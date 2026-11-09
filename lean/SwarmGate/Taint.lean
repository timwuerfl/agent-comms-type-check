/-
  SwarmGate.Taint — context taint and protocol-level information-flow control (THEORY.md §5.3, T5).

  An LLM cannot separate data from instructions inside its context window. Hence taint is *sticky per
  agent*: once a role has received a high-capacity message from a tainted role, everything it says
  afterwards is tainted. Low-capacity messages (booleans, enums, bounded integers, records thereof)
  cannot carry free-form instructions and do not propagate taint; they only leak a bounded number of bits.
-/
import SwarmGate.Observe
import SwarmGate.PTLTL

namespace SwarmGate

/-- A pattern on abstract events (like a PTLTL atom). -/
structure Pat where
  src : Option Nat
  dst : Option Nat
  label : Option String
  deriving Repr, Inhabited, DecidableEq

def Pat.hits (p : Pat) (a : AEv) : Bool := atomHolds p.src p.dst p.label a

structure IFCPolicy where
  /-- untrusted sources: web/mail/file readers, external agents, … -/
  untrusted : List Nat
  /-- messages whose type carries at most this many bits do not propagate taint -/
  maxBits : Nat
  /-- privileged actions that must never be performed by a tainted role -/
  sensitive : List Pat
  /-- endorsers: non-LLM roles (humans, deterministic validators) that cannot be prompt-injected and
      therefore never become tainted -/
  endorsers : List Nat := []
  deriving Repr, Inhabited

def IFCPolicy.isSensitive (pol : IFCPolicy) (a : AEv) : Bool := pol.sensitive.any (·.hits a)

/-- Taint sets as bitmasks. -/
def taintInit (pol : IFCPolicy) : Nat := pol.untrusted.foldl (fun m r => m ||| (1 <<< r)) 0

def taintUpd (pol : IFCPolicy) (T : Nat) (t : Trans) : Nat :=
  if T.testBit t.src && !t.ty.lowcap pol.maxBits && !pol.endorsers.contains t.dst then T ||| (1 <<< t.dst)
  else T

/-- The taint the gate tracks along a concrete run. -/
def taintOf (P : Protocol) (pol : IFCPolicy) (t : List Event) : Nat :=
  obsRun P (taintUpd pol) P.start (taintInit pol) t

def taintTS (P : Protocol) (pol : IFCPolicy) : TS (Nat × Nat) := obsTS P (taintInit pol) (taintUpd pol)

/-- Invariant: no sensitive transition enabled here can be taken by a tainted sender. -/
def taintInv (P : Protocol) (pol : IFCPolicy) (c : Nat × Nat) : Bool :=
  (P.out c.1).all (fun t => !pol.isSensitive t.abs || !c.2.testBit t.src)

def checkIFC (P : Protocol) (pol : IFCPolicy) (V : List (Nat × Nat)) : Bool :=
  certifies (taintTS P pol) (taintInv P pol) V

/-- IFC transfer for any protocol trace. -/
theorem ifc_of_pref (P : Protocol) (pol : IFCPolicy) (V : List (Nat × Nat))
    (hc : checkIFC P pol V = true) (D : List Event) (hD0 : Pref P D) :
    ∀ t e u, D = t ++ e :: u →
      pol.isSensitive e.abs = true → (taintOf P pol t).testBit e.src = false := by
  intro t e u hD hs
  have hpref := hD0
  rw [hD] at hpref
  obtain ⟨s₁, tr, _, htr, hm, _, hreach, _⟩ := prefix_decomp P (taintInit pol) (taintUpd pol) t e u hpref
  have hinv := certifies_sound hc hreach
  simp only [taintInv, List.all_eq_true] at hinv
  have := hinv tr htr
  have habs := Trans.abs_of_matches hm
  rw [habs] at this
  simp [hs] at this
  have hsrc : tr.src = e.src := by
    have := congrArg AEv.src habs; simpa [Trans.abs, Event.abs] using this
  rw [← hsrc]; simpa [taintOf] using this

/-- **Theorem T5 (IFC transfer).** If the checker accepts, then on every run of the gate — whatever the
agents submit — every delivered sensitive event was sent by a role that had not been exposed to
high-capacity content derived from an untrusted source. -/
theorem ifc_transfer (P : Protocol) (pol : IFCPolicy) (V : List (Nat × Nat))
    (hc : checkIFC P pol V = true) (cfg : Config) (as : List Input) :
    ∀ t e u, delivered (monRun cfg P (MState.init P) as).2 = t ++ e :: u →
      pol.isSensitive e.abs = true → (taintOf P pol t).testBit e.src = false :=
  ifc_of_pref P pol V hc _ (enforcement_pref cfg P as)

/-! ### Reading of the guarantee

Equivalently: an attacker who fully controls every untrusted role *and* every agent that has read
attacker-influenced text can still cause sensitive actions only through roles that saw nothing but
low-capacity messages from tainted parties. This is the protocol-level formulation of the
plan-then-execute / dual-LLM / quarantined-reader design patterns, and the check proves that a
given protocol actually implements the pattern.
-/

end SwarmGate
