/-
  SwarmGate.Analyze — the `swarmgate check` driver.

  Untrusted code (exploration, witness search, ranking synthesis, counterexample extraction) proposes
  certificates. Every "verified" verdict that is reported is the output of one of the *verified* checkers
  (`checkProp`, `checkIFC`, `checkNoStuck`, `checkCompletion`, `checkBounded`, `checkDecentralised`),
  each of which has a soundness theorem connecting it to all runs of the gate.
-/
import SwarmGate.Json
import SwarmGate.Noninterference

namespace SwarmGate
open Lean

/-! ### Labelled exploration with parent pointers (for counterexamples; untrusted) -/

structure ExploreResult (α : Type) where
  nodes : Array α
  parent : Array (Option (Nat × Json))
  complete : Bool

def exploreL {α : Type} [BEq α] [Hashable α] [Inhabited α] (init : List α) (succL : α → List (Json × α)) (fuel : Nat) :
    ExploreResult α := Id.run do
  let mut idx : Std.HashMap α Nat := {}
  let mut nodes : Array α := #[]
  let mut parent : Array (Option (Nat × Json)) := #[]
  for a in init do
    if !idx.contains a then
      idx := idx.insert a nodes.size; nodes := nodes.push a; parent := parent.push none
  let mut i := 0
  let mut complete := true
  while i < nodes.size do
    if nodes.size > fuel then
      complete := false
      break
    let c := nodes[i]!
    for (lab, c') in succL c do
      if !idx.contains c' then
        idx := idx.insert c' nodes.size; nodes := nodes.push c'; parent := parent.push (some (i, lab))
    i := i + 1
  return { nodes, parent, complete }

/-- Event labels on the path from an initial node to node `i`. -/
partial def pathTo {α : Type} (r : ExploreResult α) (i : Nat) : List Json :=
  match r.parent[i]? with
  | some (some (j, lab)) => pathTo r j ++ [lab]
  | _ => []

def Trans.labelJson (P : Protocol) (roles : Array String) (t : Trans) : Json :=
  let _ := P
  Json.mkObj [("src", roles[t.src]?.getD (toString t.src)), ("dst", roles[t.dst]?.getD (toString t.dst)),
    ("label", t.label)]

/-! ### Candidate witness payloads (untrusted search) -/

partial def predConsts : Pred → List Value
  | .and p q | .or p q => predConsts p ++ predConsts q
  | .not p => predConsts p
  | .intLe _ k | .intGe _ k => [.int k, .int (k - 1), .int (k + 1)]
  | .strIn _ cs => cs.map .str
  | .eqStr _ s => [.str s]
  | .eqBool _ b => [.bool b]
  | _ => []

mutual
partial def candidates (t : Ty) (consts : List Value) : List Value :=
  let base := match t with
    | .unit => [.unit]
    | .bool => [.bool false, .bool true]
    | .int => [.int 0, .int 1, .int (-1)]
    | .str => [.str "", .str "x"]
    | .enum cs => cs.map .str
    | .list t' => [.list [], .list ((candidates t' consts).take 1)]
    | .record fs => (fieldCands fs consts).take 64 |>.map .record
  (consts ++ base).filter (hasTy t)
partial def fieldCands (fs : Fields) (consts : List Value) : List (List (String × Value)) :=
  match fs with
  | .nil => [[]]
  | .cons n t r =>
    let vs := (candidates t consts).take 4
    (fieldCands r consts).flatMap (fun rest => vs.map (fun v => (n, v) :: rest))
end

/-- Record-path-aware constants: wrap constants into records along refinement paths. -/
def findWitness (t : Trans) : Option Value :=
  let consts := predConsts t.pred
  (candidates t.ty consts).find? (fun v => t.matches (t.evOf v))

def mkWitnesses (P : Protocol) (V : List Nat) : Witnesses :=
  V.flatMap (fun s => ((P.out s).zipIdx).filterMap (fun (t, i) => (findWitness t).map (fun v => ((s, i), v))))

/-! ### Rankings (untrusted synthesis) -/

/-- Distance-to-final over witnessed transitions (backward BFS by fixpoint iteration). -/
def distRanking (P : Protocol) (W : Witnesses) (V : List Nat) : Ranking := Id.run do
  let mut d : Std.HashMap Nat Nat := {}
  for s in V do
    if P.isFinal s then d := d.insert s 0
  let mut changed := true
  let mut rounds := 0
  while changed && rounds ≤ V.length + 1 do
    changed := false
    rounds := rounds + 1
    for s in V do
      if !d.contains s then
        let mut best : Option Nat := none
        for i in List.range (P.out s).length do
          if witOk P W s i then
            if let some t := (P.out s)[i]? then
              if let some k := d.get? t.next then
                best := some (match best with | some b => min b (k + 1) | none => k + 1)
        if let some b := best then
          d := d.insert s b; changed := true
  return V.filterMap (fun s => (d.get? s).map (fun k => (s, k)))

/-- Longest-path ranking if the reachable control-flow graph is acyclic. -/
def longestRanking (P : Protocol) (V : List Nat) : Option Ranking := Id.run do
  -- iterate h(s) = 1 + max h(next); converges in ≤ |V| rounds iff acyclic
  let mut h : Std.HashMap Nat Nat := {}
  for s in V do h := h.insert s 0
  for _ in [0:V.length + 2] do
    let mut changed := false
    for s in V do
      let cur := h.getD s 0
      let nxt := (P.out s).foldl (fun m t => max m (h.getD t.next 0 + 1)) 0
      if nxt > cur then
        h := h.insert s nxt; changed := true
    if !changed then
      return some (V.map (fun s => (s, h.getD s 0)))
  return none

/-! ### The report -/

structure Spec where
  name : String
  roles : Array String
  P : Protocol
  cfg : Config
  props : List (String × F)
  ifc : Option IFCPolicy
  locals : Option Deployment

def Spec.ofJson (j : Json) : Except String Spec := do
  let P ← Protocol.ofJson j
  let roles ← jstrs (← jget j "roles")
  let props ← (← jarr (jgetD j "properties" (.arr #[]))).mapM (fun pj => do
    pure (← jstr (jgetD pj "name" (.str "property")), ← F.ofJson (← jget pj "formula")))
  let ifc ← match jgetD j "ifc" .null with
    | .null => pure none
    | ij => some <$> IFCPolicy.ofJson ij
  let locals ← match jgetD j "locals" .null with
    | .null => pure none
    | lj => some <$> (← jarr lj).mapM Local.ofJson
  pure { name := ← jstr (jgetD j "name" (.str "protocol")), roles := roles.toArray, P,
         cfg := { budget := ← jnat (jgetD j "budget" (.num 1000)), maxStrikes := ← jnat (jgetD j "maxStrikes" (.num 3)) },
         props, ifc, locals }

def wellFormed (P : Protocol) (V : List Nat) : List String :=
  let n := P.trans.size
  let bad := V.flatMap (fun s => (P.out s).filterMap (fun t =>
    if t.src ≥ P.nRoles ∨ t.dst ≥ P.nRoles then some s!"state {s}: role index out of range"
    else if t.src = t.dst then some s!"state {s}: self-message {t.label}"
    else if t.next ≥ n then some s!"state {s}: next state {t.next} out of range"
    else none))
  let nondet := V.filterMap (fun s => if detB P s then none else some s!"state {s}: nondeterministic choice (W1)")
  bad ++ nondet

def fuel : Nat := 500000

/-- Untrusted certificate search for `admit`. -/
def buildAdmitCert (Pi : MetaPolicy) (P : Protocol) : AdmitCert := Id.run do
  let cg := exploreL [P.start] (fun s => (P.out s).map (fun t => (Json.null, t.next))) fuel
  let V := cg.nodes.toList
  let tr := exploreL [(P.start, taintInit Pi.ifc)]
    (fun c => (P.out c.1).map (fun t => (Json.null, (t.next, taintUpd Pi.ifc c.2 t)))) fuel
  let propCerts := Pi.props.map (fun φ =>
    (φ, (exploreL [(P.start, (none : MonSt))]
      (fun c => (P.out c.1).map (fun t => (Json.null, (t.next, propUpd φ c.2 t)))) fuel).nodes.toList))
  return { V, taintV := tr.nodes.toList, propCerts, ρ := (longestRanking P V).getD [] }

/-- Admission report. The `admitted` field is exactly the verified `admit`; everything else is diagnostics
(counterexamples) for the protocol author, e.g. an LLM in a counterexample-guided repair loop. -/
def admitReport (Pi : MetaPolicy) (roles : Array String) (propNames : List String) (P : Protocol) :
    Json := Id.run do
  let lab := Trans.labelJson P roles
  let cg := exploreL [P.start] (fun s => (P.out s).map (fun t => (lab t, t.next))) fuel
  let V := cg.nodes.toList
  -- catalog
  let catOk := checkCatalog Pi.catalog P V
  let catCex := if catOk then Json.null else
    match (List.range cg.nodes.size).find? (fun i => !(catInv Pi.catalog P cg.nodes[i]!)) with
    | some i =>
      let s := cg.nodes[i]!
      let bad := (P.out s).find? (fun t => !(Pi.catalog.any (coveredBy t)))
      Json.mkObj [("path", toJson (pathTo cg i)),
        ("notInCatalog", match bad with
          | some t => Json.mkObj [("src", Json.str (roles[t.src]?.getD "?")), ("dst", Json.str (roles[t.dst]?.getD "?")),
              ("label", Json.str t.label), ("ty", Json.str (reprStr t.ty)), ("pred", Json.str (reprStr t.pred))]
          | none => .null)]
    | none => .null
  -- IFC
  let pol := Pi.ifc
  let tr := exploreL [(P.start, taintInit pol)]
    (fun c => (P.out c.1).map (fun t => (lab t, (t.next, taintUpd pol c.2 t)))) fuel
  let taintV := tr.nodes.toList
  let ifcOk := checkIFC P pol taintV
  let ifcCex := if ifcOk then Json.null else
    match (List.range tr.nodes.size).find? (fun i => !(taintInv P pol tr.nodes[i]!)) with
    | some i =>
      let c := tr.nodes[i]!
      let bad := (P.out c.1).find? (fun t => pol.isSensitive t.abs && c.2.testBit t.src)
      let tainted := (List.range P.nRoles).filter (fun k => c.2.testBit k) |>.map (fun k => roles[k]?.getD "?")
      Json.mkObj [("path", toJson (pathTo tr i)), ("then", (bad.map lab).getD .null),
        ("taintedRoles", toJson tainted)]
    | none => .null
  -- properties
  let mut propCerts : List (F × List (Nat × MonSt)) := []
  let mut propsJ : Array Json := #[]
  for (φ, nm) in Pi.props.zip propNames do
    let r := exploreL [(P.start, (none : MonSt))]
      (fun c => (P.out c.1).map (fun t => (lab t, (t.next, propUpd φ c.2 t)))) fuel
    let ok := checkProp P φ r.nodes.toList
    propCerts := propCerts ++ [(φ, r.nodes.toList)]
    let cex := if ok then Json.null else
      match (List.range r.nodes.size).find? (fun i => !(propInv φ r.nodes[i]!)) with
      | some i => toJson (pathTo r i)
      | none => Json.str "certificate rejected"
    propsJ := propsJ.push (Json.mkObj [("name", nm), ("ok", ok), ("counterexample", cex)])
  -- bound
  let ρ := (longestRanking P V).getD []
  let cert : AdmitCert := { V, taintV, propCerts, ρ }
  let bOk := boundOk Pi P cert
  let boundJ := Json.mkObj [("ok", bOk), ("maxLen", toJson Pi.maxLen),
    ("protocolMax", match longestRanking P V with
      | some r => toJson (rk r P.start) | none => Json.str "unbounded (a loop without `max`)")]
  let wf := wellFormed P V
  let W := mkWitnesses P V
  let admitted := admit Pi P cert
  return Json.mkObj [("admitted", admitted), ("theorem", "SwarmGate.admitted_secure"),
    ("states", V.length),
    ("roles", Json.mkObj [("ok", P.nRoles == Pi.nRoles)]),
    ("catalog", Json.mkObj [("ok", catOk), ("counterexample", catCex)]),
    ("ifc", Json.mkObj [("ok", ifcOk), ("counterexample", ifcCex)]),
    ("properties", Json.arr propsJ), ("bound", boundJ),
    ("wellFormed", Json.mkObj [("ok", wf.isEmpty), ("issues", toJson wf)]),
    ("noStuck", certifiesFast (cfgTS P) (liveInv P W) V),
    ("completion", certifiesFast (cfgTS P) (complInv P W (distRanking P W V)) V)]

/-- Weighted longest path ρ(s) = max_t (cost(s,t) + ρ(next)); `none` if it does not converge (attacker-paid
cycle). Untrusted; validated by the verified `checkInfluence`. -/
def influenceRanking (S : System) (V : List Nat) : Option Ranking := Id.run do
  let mut h : Std.HashMap Nat Nat := {}
  for s in V do h := h.insert s 0
  for _ in [0:V.length + 2] do
    let mut changed := false
    for s in V do
      let cur := h.getD s 0
      let nxt := (S.P.out s).foldl (fun m t => max m (h.getD t.next 0 + cost S s t)) 0
      if nxt > cur then
        h := h.insert s nxt; changed := true
    if !changed then
      return some (V.map (fun s => (s, h.getD s 0)))
  return none

/-- Theorem T9b report: the attacker set A is the static taint closure (all roles that can ever read
high-capacity attacker-derived content) plus any explicitly compromised roles. -/
def influenceReport (sp : Spec) (extra : List Nat) : Json := Id.run do
  let P := sp.P
  let pol := sp.ifc.getD { untrusted := [], maxBits := 8, sensitive := [] }
  let cg := exploreL [P.start] (fun s => (P.out s).map (fun t => (Json.null, t.next))) fuel
  let V := cg.nodes.toList
  let t0 := extra.foldl (fun m r => m ||| (1 <<< r)) (taintInit pol)
  let tr := exploreL [(P.start, t0)] (fun c => (P.out c.1).map (fun t => (Json.null, (t.next, taintUpd pol c.2 t)))) fuel
  let A := tr.nodes.foldl (fun m c => m ||| c.2) t0
  let S : System := { P, turn := fun _ => none, inA := fun r => A.testBit r, clean := fun _ _ => none }
  let roles := (List.range P.nRoles).filter (fun r => A.testBit r) |>.map (fun r => sp.roles[r]?.getD "?")
  match influenceRanking S V with
  | none => return Json.mkObj [("attackerRoles", toJson roles), ("verified", false), ("bits", Json.null),
      ("reason", "attacker choices inside an unbounded loop")]
  | some ρ =>
    let ok := checkInfluence S ρ V
    let reason := if ok then "ok" else
      "an attacker-controlled role sends an unbounded-capacity message to a clean role (e.g. free text to an endorser)"
    return Json.mkObj [("attackerRoles", toJson roles), ("verified", ok),
      ("bits", if ok then toJson (rk ρ P.start) else Json.null), ("reason", reason),
      ("theorem", "SwarmGate.influence_monitor")]

def checkReport (sp : Spec) : Json := Id.run do
  let P := sp.P
  let roles := sp.roles
  let lab := Trans.labelJson P roles
  -- control-flow graph
  let cg := exploreL [P.start] (fun s => (P.out s).map (fun t => (lab t, t.next))) fuel
  let V := cg.nodes.toList
  let wf := wellFormed P V
  let mut out : List (String × Json) := [("name", sp.name), ("states", V.length),
    ("wellFormed", Json.mkObj [("ok", wf.isEmpty), ("issues", toJson wf)])]
  -- T4: temporal properties
  let mut props : Array Json := #[]
  for (nm, φ) in sp.props do
    let r := exploreL [(P.start, (none : MonSt))]
      (fun c => (P.out c.1).map (fun t => (lab t, (t.next, propUpd φ c.2 t)))) fuel
    let ok := certifiesFast (propTS P φ) (propInv φ) r.nodes.toList
    let cex := if ok then Json.null else
      match (List.range r.nodes.size).find? (fun i => !(propInv φ r.nodes[i]!)) with
      | some i => toJson (pathTo r i)
      | none => Json.str (if r.complete then "certificate rejected" else "state space too large")
    props := props.push (Json.mkObj [("name", nm), ("verified", ok), ("configurations", r.nodes.size),
      ("theorem", "SwarmGate.property_transfer"), ("counterexample", cex)])
  out := out ++ [("properties", Json.arr props)]
  -- T5: IFC
  if let some pol := sp.ifc then
    let r := exploreL [(P.start, taintInit pol)]
      (fun c => (P.out c.1).map (fun t => (lab t, (t.next, taintUpd pol c.2 t)))) fuel
    let ok := certifiesFast (taintTS P pol) (taintInv P pol) r.nodes.toList
    let cex := if ok then Json.null else
      match (List.range r.nodes.size).find? (fun i => !(taintInv P pol r.nodes[i]!)) with
      | some i =>
        let c := r.nodes[i]!
        let bad := (P.out c.1).find? (fun t => pol.isSensitive t.abs && c.2.testBit t.src)
        let tainted := (List.range P.nRoles).filter (fun k => c.2.testBit k) |>.map (fun k => roles[k]?.getD "?")
        Json.mkObj [("path", toJson (pathTo r i)), ("then", (bad.map lab).getD .null),
          ("taintedRoles", toJson tainted)]
      | none => Json.str (if r.complete then "certificate rejected" else "state space too large")
    out := out ++ [("ifc", Json.mkObj [("verified", ok), ("configurations", r.nodes.size),
      ("theorem", "SwarmGate.ifc_transfer"), ("counterexample", cex)])]
  -- T7a/b/c: liveness
  let W := mkWitnesses P V
  let noStuck := certifiesFast (cfgTS P) (liveInv P W) V
  let stuckAt := V.filter (fun s => !liveInv P W s)
  let ρ := distRanking P W V
  let compl := certifiesFast (cfgTS P) (complInv P W ρ) V
  let noCompl := V.filter (fun s => !complInv P W ρ s)
  let bnd := longestRanking P V
  let bounded := match bnd with | some ρ' => certifiesFast (cfgTS P) (boundInv P ρ') V | none => false
  let bound := match bnd with | some ρ' => toJson (rk ρ' P.start) | none => Json.null
  out := out ++ [("noStuck", Json.mkObj [("verified", noStuck), ("stuckStates", toJson stuckAt),
      ("theorem", "SwarmGate.no_stuck")]),
    ("completion", Json.mkObj [("verified", compl), ("cannotComplete", toJson noCompl),
      ("theorem", "SwarmGate.completion_possible")]),
    ("bounded", Json.mkObj [("verified", bounded), ("maxMessages", bound),
      ("theorem", "SwarmGate.bounded_length")])]
  -- T6a: decentralised deployment
  if let some D := sp.locals then
    let r := exploreL [(P.start, D.init)] (fun x => (jointMoves D x.2).map (fun jm =>
        (Json.mkObj [("src", Json.str (roles[jm.1]?.getD "?")), ("dst", Json.str (roles[jm.2.2.1]?.getD "?")), ("label", Json.str jm.2.1.label)],
         (((globalFor P x.1 jm).map (·.next)).getD 0, (x.2.set jm.1 jm.2.1.next).set jm.2.2.1 jm.2.2.2.next)))) fuel
    let ok := D.length == P.nRoles && certifiesFast (decTS P D) (decInv P D) r.nodes.toList
    let cex := if ok then Json.null else
      match (List.range r.nodes.size).find? (fun i => !(decInv P D r.nodes[i]!)) with
      | some i =>
        let x := r.nodes[i]!
        let bad := (jointMoves D x.2).find? (fun jm => !(globalFor P x.1 jm).isSome)
        Json.mkObj [("path", toJson (pathTo r i)),
          ("thenUnjustified", match bad with
            | some jm => Json.mkObj [("src", Json.str (roles[jm.1]?.getD "?")),
                ("dst", Json.str (roles[jm.2.2.1]?.getD "?")), ("label", Json.str jm.2.1.label)]
            | none => .null)]
      | none => Json.str (if r.complete then "certificate rejected" else "state space too large")
    out := out ++ [("decentralised", Json.mkObj [("verified", ok), ("configurations", r.nodes.size),
      ("theorem", "SwarmGate.decentralised_sound"), ("counterexample", cex)])]
  return Json.mkObj out

end SwarmGate
