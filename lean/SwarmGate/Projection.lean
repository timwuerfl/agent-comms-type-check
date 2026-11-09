/-
  SwarmGate.Projection — decentralised enforcement by per-role sidecars (THEORY.md §6, Theorem T6).

  When no single router can be trusted (agents of different organisations talking over A2A), each
  organisation runs a sidecar that enforces only its own role's *local* protocol, obtained by projection.
  A message `p → q` is delivered iff p's sidecar accepts it as a send and q's sidecar accepts it as a
  receive. Projection itself is computed by unverified code; the certificate checked here proves that the
  sidecars together never admit a trace outside the global protocol.
-/
import SwarmGate.Liveness
import SwarmGate.Taint

namespace SwarmGate

inductive Dir where
  | send
  | recv
  deriving DecidableEq, Repr, Inhabited

/-- A local transition: `!peer label(ty){pred}` or `?peer label(ty){pred}`. -/
structure LTrans where
  dir : Dir
  peer : Nat
  label : String
  ty : Ty
  pred : Pred
  next : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A local protocol (one per role). -/
structure Local where
  trans : Array (List LTrans)
  start : Nat
  deriving Repr, Inhabited

def Local.out (L : Local) (s : Nat) : List LTrans := L.trans[s]?.getD []

def LTrans.matchesSend (lt : LTrans) (e : Event) : Bool :=
  decide (lt.dir = .send) && lt.peer == e.dst && lt.label == e.label && hasTy lt.ty e.payload &&
    lt.pred.eval e.payload

def LTrans.matchesRecv (lt : LTrans) (e : Event) : Bool :=
  decide (lt.dir = .recv) && lt.peer == e.src && lt.label == e.label && hasTy lt.ty e.payload &&
    lt.pred.eval e.payload

/-- One sidecar step. -/
def lstep (L : Local) (s : Nat) (e : Event) (asSender : Bool) : Option Nat :=
  ((L.out s).find? (fun lt => if asSender then lt.matchesSend e else lt.matchesRecv e)).map (·.next)

abbrev Deployment := List Local

def localState (c : List Nat) (r : Nat) : Nat := c[r]?.getD 0

/-- Joint delivery by sender and receiver sidecars (mediated rendezvous). -/
def dstep (D : Deployment) (c : List Nat) (e : Event) : Option (List Nat) :=
  if e.src = e.dst then none else
  if e.src < D.length ∧ e.dst < D.length ∧ e.src < c.length ∧ e.dst < c.length then
    match D[e.src]?, D[e.dst]? with
    | some Lp, some Lq =>
      match lstep Lp (localState c e.src) e true, lstep Lq (localState c e.dst) e false with
      | some sp, some sq => some ((c.set e.src sp).set e.dst sq)
      | _, _ => none
    | _, _ => none
  else none

def drun (D : Deployment) : List Nat → List Event → Option (List Nat)
  | c, [] => some c
  | c, e :: es => match dstep D c e with
    | some c' => drun D c' es
    | none => none

def Deployment.init (D : Deployment) : List Nat := D.map (·.start)

/-! ### The certificate -/

/-- All joint (send, receive) moves the sidecars could perform in configuration `c`. -/
def jointMoves (D : Deployment) (c : List Nat) : List (Nat × LTrans × Nat × LTrans) :=
  (List.range D.length).flatMap fun p =>
    ((D[p]?.map (fun L => L.out (localState c p))).getD []).flatMap fun lt =>
      if lt.dir = .send then
        ((D[lt.peer]?.map (fun L => L.out (localState c lt.peer))).getD []).filterMap fun lr =>
          if lr.dir = .recv ∧ lr.peer = p ∧ lr.label = lt.label then some (p, lt, lt.peer, lr) else none
      else []

/-- The global transition that justifies a joint move: same endpoints, label and guard as the send. -/
def justifies (p : Nat) (lt : LTrans) (q : Nat) (gt : Trans) : Bool :=
  decide (gt.src = p) && decide (gt.dst = q) && decide (gt.label = lt.label) &&
    decide (gt.ty = lt.ty) && decide (gt.pred = lt.pred)

def globalFor (P : Protocol) (g : Nat) (jm : Nat × LTrans × Nat × LTrans) : Option Trans :=
  (P.out g).find? (fun gt => justifies jm.1 jm.2.1 jm.2.2.1 gt)

def decTS (P : Protocol) (D : Deployment) : TS (Nat × List Nat) where
  init := [(P.start, D.init)]
  succ := fun x => (jointMoves D x.2).map fun jm =>
    (((globalFor P x.1 jm).map (·.next)).getD 0, (x.2.set jm.1 jm.2.1.next).set jm.2.2.1 jm.2.2.2.next)

/-- Invariant: the global state is deterministic and every joint move is justified by a global step. -/
def decInv (P : Protocol) (D : Deployment) (x : Nat × List Nat) : Bool :=
  detB P x.1 && x.2.length == D.length && (jointMoves D x.2).all (fun jm => (globalFor P x.1 jm).isSome)

def checkDecentralised (P : Protocol) (D : Deployment) (V : List (Nat × List Nat)) : Bool :=
  D.length == P.nRoles && certifies (decTS P D) (decInv P D) V

/-! ### Soundness -/

theorem lstep_some {L : Local} {s : Nat} {e : Event} {b : Bool} {s' : Nat} (h : lstep L s e b = some s') :
    ∃ lt ∈ L.out s, (if b then lt.matchesSend e else lt.matchesRecv e) = true ∧ lt.next = s' := by
  unfold lstep at h
  cases hf : (L.out s).find? (fun lt => if b then lt.matchesSend e else lt.matchesRecv e) with
  | none => simp [hf] at h
  | some lt =>
    simp [hf] at h
    exact ⟨lt, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

theorem mem_jointMoves (D : Deployment) (c : List Nat) (p q : Nat) (Lp Lq : Local) (lt lr : LTrans)
    (hp : p < D.length) (hLp : D[p]? = some Lp) (hLq : D[q]? = some Lq)
    (hlt : lt ∈ Lp.out (localState c p)) (hlr : lr ∈ Lq.out (localState c q))
    (hs : lt.dir = .send) (hq : lt.peer = q) (hr : lr.dir = .recv) (hrp : lr.peer = p)
    (hl : lr.label = lt.label) : (p, lt, q, lr) ∈ jointMoves D c := by
  subst hq
  simp only [jointMoves, List.mem_flatMap, List.mem_range]
  refine ⟨p, hp, lt, by simp [hLp, hlt], ?_⟩
  simp only [hs, if_true, List.mem_filterMap]
  exact ⟨lr, by simp [hLq, hlr], by simp [hr, hrp, hl]⟩

theorem globalFor_matches (P : Protocol) (g : Nat) (p q : Nat) (lt lr : LTrans) (e : Event) (gt : Trans)
    (hg : globalFor P g (p, lt, q, lr) = some gt) (hsend : lt.matchesSend e = true)
    (hsrc : e.src = p) (hdst : e.dst = q) : gt ∈ P.out g ∧ gt.matches e = true := by
  unfold globalFor at hg
  have hmem := List.mem_of_find?_eq_some hg
  have hj : justifies p lt q gt = true := by simpa using List.find?_some hg
  refine ⟨hmem, ?_⟩
  simp only [justifies, Bool.and_eq_true, decide_eq_true_eq] at hj
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hj
  simp only [LTrans.matchesSend, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsend
  obtain ⟨⟨⟨⟨_, hpe⟩, hle⟩, hty⟩, hpr⟩ := hsend
  simp [Trans.matches, h1, h2, h3, h4, h5, hsrc, hdst, hle, hty, hpr]

/-- One joint delivery is matched by one global step, preserving reachability in the product. -/
theorem dstep_sound (P : Protocol) (D : Deployment) (V : List (Nat × List Nat))
    (hc : certifies (decTS P D) (decInv P D) V) (g : Nat) (c c' : List Nat) (e : Event)
    (hr : Reach (decTS P D) (g, c)) (hd : dstep D c e = some c') :
    ∃ g', step P g e = some g' ∧ Reach (decTS P D) (g', c') := by
  have hinv := certifies_sound hc hr
  simp only [decInv, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hinv
  obtain ⟨⟨hdet, _⟩, hall⟩ := hinv
  unfold dstep at hd
  by_cases hne : e.src = e.dst
  · simp [hne] at hd
  · simp only [hne, if_false] at hd
    by_cases hb : e.src < D.length ∧ e.dst < D.length ∧ e.src < c.length ∧ e.dst < c.length
    · simp only [hb, and_self, if_true] at hd
      cases hLp : D[e.src]? with
      | none => simp [hLp] at hd
      | some Lp =>
        cases hLq : D[e.dst]? with
        | none => simp [hLp, hLq] at hd
        | some Lq =>
          simp only [hLp, hLq] at hd
          cases hsp : lstep Lp (localState c e.src) e true with
          | none => simp [hsp] at hd
          | some sp =>
            cases hsq : lstep Lq (localState c e.dst) e false with
            | none => simp [hsp, hsq] at hd
            | some sq =>
              simp only [hsp, hsq, Option.some.injEq] at hd
              obtain ⟨lt, hlt, hms, hlnext⟩ := lstep_some hsp
              obtain ⟨lr, hlr, hmr, hrnext⟩ := lstep_some hsq
              simp only [if_true] at hms
              simp only [Bool.false_eq_true, if_false] at hmr
              have hms' := hms
              simp only [LTrans.matchesSend, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hms'
              simp only [LTrans.matchesRecv, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hmr
              obtain ⟨⟨⟨⟨hsd, hpe⟩, hle⟩, _⟩, _⟩ := hms'
              obtain ⟨⟨⟨⟨hrd, hrp⟩, hrl⟩, _⟩, _⟩ := hmr
              have hjm := mem_jointMoves D c e.src e.dst Lp Lq lt lr hb.1 hLp hLq hlt hlr hsd hpe hrd hrp
                (by rw [hrl, hle])
              have hsome := hall _ hjm
              obtain ⟨gt, hgt⟩ := Option.isSome_iff_exists.mp hsome
              obtain ⟨hgmem, hgm⟩ := globalFor_matches P g e.src e.dst lt lr e gt hgt hms rfl rfl
              refine ⟨gt.next, step_of_matches P g e gt (detB_sound P g hdet) hgmem hgm, ?_⟩
              apply Reach.step hr
              simp only [decTS, List.mem_map]
              refine ⟨(e.src, lt, e.dst, lr), hjm, ?_⟩
              simp only [hgt, Option.map_some, Option.getD_some, hlnext, hrnext]
              rw [← hd]
    · simp [hb] at hd

theorem drun_sound (P : Protocol) (D : Deployment) (V : List (Nat × List Nat))
    (hc : certifies (decTS P D) (decInv P D) V) : ∀ (t : List Event) (g : Nat) (c c' : List Nat),
    Reach (decTS P D) (g, c) → drun D c t = some c' → ∃ g', run P g t = some g'
  | [], g, _, _, _, _ => ⟨g, by simp [run]⟩
  | e :: es, g, c, c', hr, hd => by
    unfold drun at hd
    cases hs : dstep D c e with
    | none => simp [hs] at hd
    | some c₁ =>
      simp [hs] at hd
      obtain ⟨g₁, hg₁, hr₁⟩ := dstep_sound P D V hc g c c₁ e hr hs
      obtain ⟨g', hg'⟩ := drun_sound P D V hc es g₁ c₁ c' hr₁ hd
      exact ⟨g', by simp [run, hg₁, hg']⟩

/-- **Theorem T6a (Decentralised soundness).** If the certificate checks, every trace that the sidecars
jointly deliver — whatever the agents submit — is a trace of the global protocol. Consequently T4
(properties), T5 (IFC) and T7c (bounded length) hold for decentralised deployments without any trusted
central router. -/
theorem decentralised_sound (P : Protocol) (D : Deployment) (V : List (Nat × List Nat))
    (hc : checkDecentralised P D V = true) (t : List Event) (c' : List Nat)
    (hd : drun D D.init t = some c') : Pref P t := by
  simp only [checkDecentralised, Bool.and_eq_true] at hc
  obtain ⟨g', hg'⟩ := drun_sound P D V hc.2 t P.start D.init c' (.init (by simp [decTS])) hd
  unfold Pref; rw [hg']; rfl

/-- Example corollary: decentralised deployments inherit every verified temporal property. -/
theorem decentralised_property (P : Protocol) (D : Deployment) (V : List (Nat × List Nat))
    (hc : checkDecentralised P D V = true) (root : F) (W : List (Nat × MonSt))
    (hp : checkProp P root W = true) (t : List Event) (c' : List Nat)
    (hd : drun D D.init t = some c') :
    ∀ t₁ e u, t = t₁ ++ e :: u → satT root ((t₁ ++ [e]).map Event.abs) = true :=
  property_of_pref P root W hp t (decentralised_sound P D V hc t c' hd)

/-- Example corollary: decentralised deployments inherit the verified IFC policy. -/
theorem decentralised_ifc (P : Protocol) (D : Deployment) (V : List (Nat × List Nat))
    (hc : checkDecentralised P D V = true) (pol : IFCPolicy) (W : List (Nat × Nat))
    (hp : checkIFC P pol W = true) (t : List Event) (c' : List Nat)
    (hd : drun D D.init t = some c') :
    ∀ t₁ e u, t = t₁ ++ e :: u → pol.isSensitive e.abs = true →
      (taintOf P pol t₁).testBit e.src = false :=
  ifc_of_pref P pol W hp t (decentralised_sound P D V hc t c' hd)

end SwarmGate
