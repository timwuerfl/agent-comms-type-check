/-
  SwarmGate.Json — (de)serialisation glue for the `swarmgate` binary.

  This file is part of the trusted computing base only insofar as it must read the protocol and events
  faithfully; it contains no decision logic. The Python front-end and the Lean binary share one JSON schema
  (docs/FORMAT.md). Round-trip tests in `python/tests` exercise it.
-/
import Lean.Data.Json
import SwarmGate.Admission

namespace SwarmGate
open Lean

abbrev P' := Except String

def jget (j : Json) (k : String) : P' Json := j.getObjVal? k
def jgetD (j : Json) (k : String) (d : Json) : Json := (j.getObjVal? k).toOption.getD d
def jnat (j : Json) : P' Nat := j.getNat?
def jint (j : Json) : P' Int := j.getInt?
def jstr (j : Json) : P' String := j.getStr?
def jarr (j : Json) : P' (List Json) := (·.toList) <$> j.getArr?
def jstrs (j : Json) : P' (List String) := do (← jarr j).mapM jstr
def jnats (j : Json) : P' (List Nat) := do (← jarr j).mapM jnat
def joptNat (j : Json) : P' (Option Nat) := match j with | .null => pure none | j => some <$> jnat j
def joptStr (j : Json) : P' (Option String) := match j with | .null => pure none | j => some <$> jstr j

/-- JSON → payload value: null↦unit, objects↦records, arrays↦lists, integral numbers↦int. -/
partial def Value.ofJson : Json → P' Value
  | .null => pure .unit
  | .bool b => pure (.bool b)
  | .num n => if n.exponent == 0 then pure (.int n.mantissa) else throw "non-integral number in payload"
  | .str s => pure (.str s)
  | .arr a => (.list ·.toList) <$> a.mapM Value.ofJson
  | .obj kvs => (.record ·) <$> kvs.toList.mapM (fun (k, v) => do pure (k, ← Value.ofJson v))

partial def Value.toJson : Value → Json
  | .unit => .null
  | .bool b => .bool b
  | .int i => .num ⟨i, 0⟩
  | .str s => .str s
  | .list vs => .arr (vs.map Value.toJson).toArray
  | .record fs => Json.mkObj (fs.map (fun (k, v) => (k, Value.toJson v)))

partial def Ty.ofJson : Json → P' Ty
  | .str "unit" => pure .unit
  | .str "bool" => pure .bool
  | .str "int" => pure .int
  | .str "str" => pure .str
  | j => do
    if let .ok cs := jget j "enum" then return .enum (← jstrs cs)
    if let .ok t := jget j "list" then return .list (← Ty.ofJson t)
    if let .ok fs := jget j "record" then
      let fl ← jarr fs
      let pairs ← fl.mapM (fun p => do
        let a ← jarr p
        match a with
        | [n, t] => pure (← jstr n, ← Ty.ofJson t)
        | _ => throw "record field must be [name, type]")
      return .record (pairs.foldr (fun (n, t) acc => Fields.cons n t acc) Fields.nil)
    throw s!"bad type: {j.compress}"

partial def Pred.ofJson : Json → P' Pred
  | .bool true => pure .tt
  | .bool false => pure .ff
  | j => do
    let two (k : String) : P' (Option (Json × Json)) := do
      match jget j k with
      | .ok a => match ← jarr a with
        | [x, y] => pure (some (x, y))
        | _ => throw s!"{k} expects two arguments"
      | .error _ => pure none
    if let some (a, b) ← two "and" then return .and (← Pred.ofJson a) (← Pred.ofJson b)
    if let some (a, b) ← two "or" then return .or (← Pred.ofJson a) (← Pred.ofJson b)
    if let .ok a := jget j "not" then return .not (← Pred.ofJson a)
    if let some (p, k) ← two "intLe" then return .intLe (← jstrs p) (← jint k)
    if let some (p, k) ← two "intGe" then return .intGe (← jstrs p) (← jint k)
    if let some (p, k) ← two "lenLe" then return .lenLe (← jstrs p) (← jnat k)
    if let some (p, k) ← two "strIn" then return .strIn (← jstrs p) (← jstrs k)
    if let some (p, k) ← two "strNotContains" then return .strNotContains (← jstrs p) (← jstr k)
    if let some (p, k) ← two "eqStr" then return .eqStr (← jstrs p) (← jstr k)
    if let some (p, k) ← two "eqBool" then
      match k with
      | .bool b => return .eqBool (← jstrs p) b
      | _ => throw "eqBool expects a boolean"
    throw s!"bad refinement: {j.compress}"

def Trans.ofJson (j : Json) : P' Trans := do
  pure { src := ← jnat (← jget j "src"), dst := ← jnat (← jget j "dst"), label := ← jstr (← jget j "label"),
         ty := ← Ty.ofJson (jgetD j "ty" (.str "unit")), pred := ← Pred.ofJson (jgetD j "pred" (.bool true)),
         next := ← jnat (← jget j "next") }

def Protocol.ofJson (j : Json) : P' Protocol := do
  let roles ← jstrs (← jget j "roles")
  let states ← jarr (← jget j "states")
  let trans ← states.mapM (fun st => do (← jarr st).mapM Trans.ofJson)
  pure { nRoles := roles.length, trans := trans.toArray, start := ← jnat (jgetD j "start" (.num 0)),
         final := ← jnats (jgetD j "final" (.arr #[])) }

partial def F.ofJson : Json → P' F
  | .bool true => pure .tt
  | .bool false => pure .ff
  | j => do
    let two (k : String) : P' (Option (Json × Json)) := do
      match jget j k with
      | .ok a => match ← jarr a with
        | [x, y] => pure (some (x, y))
        | _ => throw s!"{k} expects two arguments"
      | .error _ => pure none
    if let .ok a := jget j "atom" then
      return .atom (← joptNat (jgetD a "src" .null)) (← joptNat (jgetD a "dst" .null))
        (← joptStr (jgetD a "label" .null))
    if let .ok a := jget j "not" then return .not (← F.ofJson a)
    if let some (a, b) ← two "and" then return .and (← F.ofJson a) (← F.ofJson b)
    if let some (a, b) ← two "or" then return .or (← F.ofJson a) (← F.ofJson b)
    if let some (a, b) ← two "imp" then return F.imp (← F.ofJson a) (← F.ofJson b)
    if let some (a, b) ← two "since" then return .since (← F.ofJson a) (← F.ofJson b)
    if let .ok a := jget j "prev" then return .prev (← F.ofJson a)
    if let .ok a := jget j "once" then return F.once (← F.ofJson a)
    if let .ok a := jget j "hist" then return F.hist (← F.ofJson a)
    throw s!"bad formula: {j.compress}"

def Pat.ofJson (j : Json) : P' Pat := do
  pure { src := ← joptNat (jgetD j "src" .null), dst := ← joptNat (jgetD j "dst" .null),
         label := ← joptStr (jgetD j "label" .null) }

def IFCPolicy.ofJson (j : Json) : P' IFCPolicy := do
  pure { untrusted := ← jnats (jgetD j "untrusted" (.arr #[])),
         maxBits := ← jnat (jgetD j "maxBits" (.num 8)),
         sensitive := ← (← jarr (jgetD j "sensitive" (.arr #[]))).mapM Pat.ofJson,
         endorsers := ← jnats (jgetD j "endorsers" (.arr #[])) }

def LTrans.ofJson (j : Json) : P' LTrans := do
  let dir ← match ← jstr (← jget j "dir") with
    | "send" => pure Dir.send
    | "recv" => pure Dir.recv
    | d => throw s!"bad dir {d}"
  pure { dir, peer := ← jnat (← jget j "peer"), label := ← jstr (← jget j "label"),
         ty := ← Ty.ofJson (jgetD j "ty" (.str "unit")), pred := ← Pred.ofJson (jgetD j "pred" (.bool true)),
         next := ← jnat (← jget j "next") }

def Local.ofJson (j : Json) : P' Local := do
  let states ← jarr (← jget j "states")
  let trans ← states.mapM (fun st => do (← jarr st).mapM LTrans.ofJson)
  pure { trans := trans.toArray, start := ← jnat (jgetD j "start" (.num 0)) }

def Event.ofJson (j : Json) : P' Event := do
  pure { src := ← jnat (← jget j "src"), dst := ← jnat (← jget j "dst"), label := ← jstr (← jget j "label"),
         payload := ← Value.ofJson (jgetD j "payload" .null) }

def AEv.toJson (a : AEv) : Json := Json.mkObj [("src", a.src), ("dst", a.dst), ("label", a.label)]

def Reason.toString : Reason → String
  | .spoof => "spoof" | .notEnabled => "notEnabled" | .budget => "budget"
  | .quarantined => "quarantined" | .halted => "halted"

def Verdict.toJson : Verdict → Json
  | .deliver _ => Json.mkObj [("verdict", "deliver")]
  | .reject b r => Json.mkObj [("verdict", "reject"), ("blamed", b), ("reason", r.toString)]
  | .killed => Json.mkObj [("verdict", "killed")]

def CatEntry.ofJson (j : Json) : P' CatEntry := do
  pure { src := ← jnat (← jget j "src"), dst := ← jnat (← jget j "dst"), label := ← jstr (← jget j "label"),
         ty := ← Ty.ofJson (jgetD j "ty" (.str "unit")), pred := ← Pred.ofJson (jgetD j "pred" (.bool true)) }

/-- Meta-policy JSON (as produced by `swarmgate.interface.Interface.to_json`). -/
def MetaPolicy.ofJson (j : Json) : P' (MetaPolicy × Array String × List String) := do
  let roles ← jstrs (← jget j "roles")
  let cat ← (← jarr (jgetD j "catalog" (.arr #[]))).mapM CatEntry.ofJson
  let ifc ← IFCPolicy.ofJson (jgetD j "ifc" (Json.mkObj []))
  let props ← (← jarr (jgetD j "properties" (.arr #[]))).mapM (fun pj => do
    pure (← jstr (jgetD pj "name" (.str "property")), ← F.ofJson (← jget pj "formula")))
  let maxLen ← joptNat (jgetD j "maxLen" .null)
  pure ({ nRoles := roles.length, catalog := cat, ifc, props := props.map (·.2), maxLen },
        roles.toArray, props.map (·.1))

end SwarmGate
