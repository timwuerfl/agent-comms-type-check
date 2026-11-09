/-
  SwarmGate.Observe — protocol × observer products.

  An *observer* is any state machine driven by the protocol's transitions (a temporal-logic monitor, a
  taint tracker, …). We show that along every protocol run the pair (protocol state, observer state) is
  reachable in the finite product transition system. Certificates over that product therefore speak
  about every run the gate can deliver.
-/
import SwarmGate.Cert
import SwarmGate.Monitor

namespace SwarmGate

variable {σ : Type}

/-- The product of a protocol with an observer driven by transitions. -/
def obsTS (P : Protocol) (x₀ : σ) (upd : σ → Trans → σ) : TS (Nat × σ) where
  init := [(P.start, x₀)]
  succ := fun c => (P.out c.1).map (fun t => (t.next, upd c.2 t))

/-- The observer state along a concrete trace (using the transition the gate matched). -/
def obsRun (P : Protocol) (upd : σ → Trans → σ) : Nat → σ → List Event → σ
  | _, x, [] => x
  | s, x, e :: es => match (P.out s).find? (fun t => t.matches e) with
    | some t => obsRun P upd t.next (upd x t) es
    | none => x

theorem obs_reach (P : Protocol) (x₀ : σ) (upd : σ → Trans → σ) : ∀ (s : Nat) (x : σ) (t : List Event)
    (s' : Nat), run P s t = some s' → Reach (obsTS P x₀ upd) (s, x) →
    Reach (obsTS P x₀ upd) (s', obsRun P upd s x t)
  | s, x, [], s', h, hr => by simp [run] at h; subst h; simpa [obsRun] using hr
  | s, x, e :: es, s', h, hr => by
    unfold run at h
    unfold obsRun
    unfold step at h
    cases hf : (P.out s).find? (fun t => t.matches e) with
    | none => simp [hf] at h
    | some tr =>
      simp [hf] at h
      apply obs_reach P x₀ upd tr.next (upd x tr) es s' h
      apply Reach.step hr
      simp [obsTS]
      exact ⟨tr, List.mem_of_find?_eq_some hf, rfl, rfl⟩

theorem obsRun_append (P : Protocol) (upd : σ → Trans → σ) : ∀ (s : Nat) (x : σ) (t u : List Event)
    (s₁ : Nat), run P s t = some s₁ →
    obsRun P upd s x (t ++ u) = obsRun P upd s₁ (obsRun P upd s x t) u
  | s, x, [], u, s₁, h => by simp [run] at h; subst h; simp [obsRun]
  | s, x, e :: es, u, s₁, h => by
    unfold run step at h
    cases hf : (P.out s).find? (fun t => t.matches e) with
    | none => simp [hf] at h
    | some tr =>
      simp [hf] at h
      simp only [List.cons_append, obsRun, hf]
      exact obsRun_append P upd tr.next (upd x tr) es u s₁ h

/-- Decomposition of a delivered prefix `t ++ [e]`: the configuration before `e` is reachable, and `e` is
matched by an outgoing transition of the state reached after `t`. -/
theorem prefix_decomp (P : Protocol) (x₀ : σ) (upd : σ → Trans → σ) (t : List Event) (e : Event)
    (u : List Event) (h : (run P P.start (t ++ e :: u)).isSome) :
    ∃ s₁ tr, run P P.start t = some s₁ ∧ tr ∈ P.out s₁ ∧ tr.matches e = true ∧
      (P.out s₁).find? (fun t => t.matches e) = some tr ∧
      Reach (obsTS P x₀ upd) (s₁, obsRun P upd P.start x₀ t) ∧
      obsRun P upd P.start x₀ (t ++ [e]) = upd (obsRun P upd P.start x₀ t) tr := by
  have h1 : (run P P.start (t ++ [e])).isSome := by
    have := run_prefix P P.start (t ++ [e]) u; simp at this; exact this h
  have h2 := run_prefix P P.start t [e] h1
  obtain ⟨s₁, hs₁⟩ := Option.isSome_iff_exists.mp h2
  rw [run_snoc, hs₁] at h1
  simp at h1
  unfold step at h1
  cases hf : (P.out s₁).find? (fun t => t.matches e) with
  | none => simp [hf] at h1
  | some tr =>
    refine ⟨s₁, tr, hs₁, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, hf, ?_, ?_⟩
    · exact obs_reach P x₀ upd P.start x₀ t s₁ hs₁ (.init (by simp [obsTS]))
    · rw [obsRun_append P upd P.start x₀ t [e] s₁ hs₁]; simp [obsRun, hf]

end SwarmGate
