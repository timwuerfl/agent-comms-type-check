/-
  SwarmGate.Cert — translation validation via invariant certificates (THEORY.md §5.1).

  Every protocol-level analysis (temporal properties, taint, decentralisation, liveness) is an instance
  of one lemma: a finite candidate set that contains the initial configurations, satisfies the
  invariant and is closed under successors, covers every reachable configuration. The candidate set is
  produced by *unverified* fast code; only this small checker is trusted.
-/
import Std.Data.HashSet
namespace SwarmGate

/-- A transition system given by initial configurations and a successor function. -/
structure TS (α : Type) where
  init : List α
  succ : α → List α

inductive Reach {α : Type} (ts : TS α) : α → Prop
  | init {a : α} : a ∈ ts.init → Reach ts a
  | step {a b : α} : Reach ts a → b ∈ ts.succ a → Reach ts b

/-- The certificate checker. -/
def certifies {α : Type} [DecidableEq α] (ts : TS α) (inv : α → Bool) (V : List α) : Bool :=
  ts.init.all (fun a => decide (a ∈ V)) &&
  V.all inv &&
  V.all (fun c => (ts.succ c).all (fun c' => decide (c' ∈ V)))

/-- Lemma 5.1: a valid certificate covers every reachable configuration. -/
theorem certifies_covers {α : Type} [DecidableEq α] {ts : TS α} {inv : α → Bool} {V : List α}
    (h : certifies ts inv V = true) {c : α} (hc : Reach ts c) : c ∈ V := by
  simp only [certifies, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hi, _⟩, hs⟩ := h
  induction hc with
  | init ha => exact hi _ ha
  | step _ hb ih => exact hs _ ih _ hb

/-- Lemma 5.1: a valid certificate proves the invariant on every reachable configuration. -/
theorem certifies_sound {α : Type} [DecidableEq α] {ts : TS α} {inv : α → Bool} {V : List α}
    (h : certifies ts inv V = true) {c : α} (hc : Reach ts c) : inv c = true := by
  have hm := certifies_covers h hc
  simp only [certifies, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.2 c hm

/-! ### A fast checker, proven equal to the reference checker -/

/-- Same check with hash-set membership: O(|V|·b) instead of O(|V|²·b). -/
def certifiesFast {α : Type} [DecidableEq α] [Hashable α] (ts : TS α) (inv : α → Bool) (V : List α) : Bool :=
  let H := Std.HashSet.ofList V
  ts.init.all (fun a => H.contains a) && V.all inv && V.all (fun c => (ts.succ c).all (fun c' => H.contains c'))

theorem certifiesFast_eq {α : Type} [DecidableEq α] [Hashable α] [LawfulHashable α]
    (ts : TS α) (inv : α → Bool) (V : List α) : certifiesFast ts inv V = certifies ts inv V := by
  simp only [certifiesFast, certifies, Std.HashSet.contains_ofList]
  congr 1 <;> simp

/-! ### Unverified explorer producing candidate certificates -/

/-- Breadth-first exploration with fuel. Its output is *not* trusted; it is validated by `certifies`. -/
def explore {α : Type} [DecidableEq α] [Hashable α] (ts : TS α) (fuel : Nat) : List α := Id.run do
  let mut seen : Std.HashSet α := {}
  let mut out : Array α := #[]
  let mut work : Array α := #[]
  for a in ts.init do
    if !seen.contains a then
      seen := seen.insert a; out := out.push a; work := work.push a
  let mut i := 0
  for _ in [0:fuel] do
    if h : i < work.size then
      let c := work[i]
      i := i + 1
      for c' in ts.succ c do
        if !seen.contains c' then
          seen := seen.insert c'; out := out.push c'; work := work.push c'
    else break
  return out.toList

end SwarmGate
