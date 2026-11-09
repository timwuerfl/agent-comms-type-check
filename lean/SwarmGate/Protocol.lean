/-
  SwarmGate.Protocol — protocols as guarded deterministic automata over typed interaction events
  (THEORY.md §2–§3).
-/
import SwarmGate.Basic

namespace SwarmGate

/-- A concrete interaction event `src → dst : label(payload)`. Roles are indices. -/
structure Event where
  src : Nat
  dst : Nat
  label : String
  payload : Value
  deriving Repr, Inhabited

/-- An abstract event: what the protocol's control structure can observe. -/
structure AEv where
  src : Nat
  dst : Nat
  label : String
  deriving Repr, Inhabited, DecidableEq

def Event.abs (e : Event) : AEv := ⟨e.src, e.dst, e.label⟩

/-- A guarded transition `src → dst : label(ty){pred}. next`. -/
structure Trans where
  src : Nat
  dst : Nat
  label : String
  ty : Ty
  pred : Pred
  next : Nat
  deriving Repr, Inhabited, DecidableEq

def Trans.abs (t : Trans) : AEv := ⟨t.src, t.dst, t.label⟩

/-- `τ` matches `e`: same endpoints and label, payload well-typed and satisfying the refinement. -/
def Trans.matches (t : Trans) (e : Event) : Bool :=
  t.src == e.src && t.dst == e.dst && t.label == e.label && hasTy t.ty e.payload && t.pred.eval e.payload

/-- A protocol: outgoing transitions per state, a start state and final states. -/
structure Protocol where
  nRoles : Nat
  trans : Array (List Trans)
  start : Nat
  final : List Nat
  deriving Repr, Inhabited

/-- Outgoing transitions of state `s` (empty for out-of-range states). -/
def Protocol.out (P : Protocol) (s : Nat) : List Trans := P.trans[s]?.getD []

def Protocol.isFinal (P : Protocol) (s : Nat) : Bool := P.final.contains s

/-- The executable one-step semantics used by the monitor. -/
def step (P : Protocol) (s : Nat) (e : Event) : Option Nat :=
  ((P.out s).find? (fun t => t.matches e)).map (·.next)

/-- Folding `step` over a trace. -/
def run (P : Protocol) : Nat → List Event → Option Nat
  | s, [] => some s
  | s, e :: es => match step P s e with
    | some s' => run P s' es
    | none => none

/-- The prefix language: traces the protocol can perform from its start state. -/
def Pref (P : Protocol) (t : List Event) : Prop := (run P P.start t).isSome

/-! ### Relational specification and adequacy (Lemma 3.1) -/

/-- Declarative semantics: each event is matched by *some* outgoing transition. -/
inductive Path (P : Protocol) : Nat → List Event → Nat → Prop
  | nil (s : Nat) : Path P s [] s
  | cons {s s' s'' : Nat} {e : Event} {es : List Event} (t : Trans) :
      t ∈ P.out s → t.matches e = true → t.next = s' → Path P s' es s'' → Path P s (e :: es) s''

/-- Determinism (W1): in each state, distinct transitions have distinct abstract events. -/
def Protocol.detAt (P : Protocol) (s : Nat) : Prop :=
  ∀ t₁ ∈ P.out s, ∀ t₂ ∈ P.out s, t₁.abs = t₂.abs → t₁ = t₂

theorem step_some_iff (P : Protocol) (s : Nat) (e : Event) (s' : Nat) :
    step P s e = some s' → ∃ t ∈ P.out s, t.matches e = true ∧ t.next = s' := by
  unfold step
  intro h
  cases hf : (P.out s).find? (fun t => t.matches e) with
  | none => simp [hf] at h
  | some t =>
    simp [hf] at h
    exact ⟨t, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

theorem Trans.abs_of_matches {t : Trans} {e : Event} (h : t.matches e = true) : t.abs = e.abs := by
  simp [Trans.matches] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩ := h
  simp [Trans.abs, Event.abs, h1, h2, h3]

/-- Lemma 3.1 (soundness of the executable semantics w.r.t. the relational one). -/
theorem run_sound (P : Protocol) : ∀ (s : Nat) (t : List Event) (s' : Nat),
    run P s t = some s' → Path P s t s'
  | s, [], s', h => by simp [run] at h; subst h; exact .nil s
  | s, e :: es, s', h => by
    unfold run at h
    cases hs : step P s e with
    | none => simp [hs] at h
    | some s₁ =>
      simp [hs] at h
      obtain ⟨t, ht, hm, hn⟩ := step_some_iff P s e s₁ hs
      exact .cons t ht hm hn (run_sound P s₁ es s' h)

/-- Under determinism a matching transition is the one `step` takes. -/
theorem step_of_matches (P : Protocol) (s : Nat) (e : Event) (t : Trans)
    (hdet : P.detAt s) (ht : t ∈ P.out s) (hm : t.matches e = true) : step P s e = some t.next := by
  unfold step
  cases hf : (P.out s).find? (fun t => t.matches e) with
  | none =>
    have := List.find?_eq_none.mp hf t ht
    simp [hm] at this
  | some t' =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 : t'.matches e = true := by simpa using List.find?_some hf
    have : t' = t := hdet t' h1 t ht (by rw [Trans.abs_of_matches h2, Trans.abs_of_matches hm])
    simp [this]

/-- Lemma 3.1 (completeness under determinism W1). -/
theorem run_complete (P : Protocol) (hdet : ∀ s, P.detAt s) : ∀ (s : Nat) (t : List Event) (s' : Nat),
    Path P s t s' → run P s t = some s'
  | _, _, _, .nil s => by simp [run]
  | s, e :: es, s'', .cons (s' := s₁) t ht hm hn hp => by
    unfold run
    rw [step_of_matches P s e t (hdet s) ht hm, hn]
    exact run_complete P hdet s₁ es s'' hp

/-! ### Basic lemmas about `run` -/

theorem run_append (P : Protocol) : ∀ (s : Nat) (t u : List Event),
    run P s (t ++ u) = (run P s t).bind (fun s' => run P s' u)
  | s, [], u => by simp [run]
  | s, e :: es, u => by
    simp only [List.cons_append, run]
    cases step P s e with
    | none => simp
    | some s' => simp [run_append P s' es u]

theorem run_snoc (P : Protocol) (s : Nat) (t : List Event) (e : Event) :
    run P s (t ++ [e]) = (run P s t).bind (fun s' => step P s' e) := by
  rw [run_append]
  cases run P s t with
  | none => simp
  | some s' => simp [run]; cases step P s' e <;> simp

/-- The prefix language is prefix-closed: it is a safety property. -/
theorem run_prefix (P : Protocol) (s : Nat) (t u : List Event) :
    (run P s (t ++ u)).isSome → (run P s t).isSome := by
  rw [run_append]
  cases run P s t <;> simp

theorem Pref_prefix_closed (P : Protocol) (t u : List Event) : Pref P (t ++ u) → Pref P t :=
  run_prefix P P.start t u

end SwarmGate
