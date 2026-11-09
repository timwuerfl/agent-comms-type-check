/-
  SwarmGate.Liveness — the gate never dead-ends honest agents, sessions can always complete, and runaway
  loops are impossible for bounded protocols (THEORY.md §7, Theorem T7).
-/
import SwarmGate.Observe

namespace SwarmGate

/-- The control-flow graph of a protocol. -/
def cfgTS (P : Protocol) : TS Nat where
  init := [P.start]
  succ := fun s => (P.out s).map (·.next)

theorem run_reach (P : Protocol) : ∀ (s : Nat) (t : List Event) (s' : Nat),
    run P s t = some s' → Reach (cfgTS P) s → Reach (cfgTS P) s'
  | s, [], s', h, hr => by simp [run] at h; subst h; exact hr
  | s, e :: es, s', h, hr => by
    unfold run at h
    cases hs : step P s e with
    | none => simp [hs] at h
    | some s₁ =>
      simp [hs] at h
      obtain ⟨t, ht, _, hn⟩ := step_some_iff P s e s₁ hs
      exact run_reach P s₁ es s' h (Reach.step hr (by simp [cfgTS]; exact ⟨t, ht, hn⟩))

theorem monitor_state_reach (cfg : Config) (P : Protocol) (as : List Input) :
    Reach (cfgTS P) (monRun cfg P (MState.init P) as).1.s := by
  have h := enforcement cfg P (MState.init P) as
  exact run_reach P _ _ _ h (.init (by simp [cfgTS, MState.init]))

/-- Witness payloads: `((state, transition index), value)`. Produced by unverified code. -/
abbrev Witnesses := List ((Nat × Nat) × Value)

def Trans.evOf (t : Trans) (v : Value) : Event := ⟨t.src, t.dst, t.label, v⟩

/-- Transition `i` of state `s` has a witness payload in `W` that it accepts. -/
def witOk (P : Protocol) (W : Witnesses) (s i : Nat) : Bool :=
  match (P.out s)[i]?, W.lookup (s, i) with
  | some t, some v => t.matches (t.evOf v)
  | _, _ => false

/-! ### T7a — no stuck state -/

def liveInv (P : Protocol) (W : Witnesses) (s : Nat) : Bool :=
  P.isFinal s || (List.range (P.out s).length).any (fun i => witOk P W s i)

def checkNoStuck (P : Protocol) (W : Witnesses) (V : List Nat) : Bool :=
  certifies (cfgTS P) (liveInv P W) V

theorem witOk_step (P : Protocol) (W : Witnesses) (s i : Nat) (h : witOk P W s i = true) :
    ∃ e, (step P s e).isSome := by
  unfold witOk at h
  cases ht : (P.out s)[i]? with
  | none => simp [ht] at h
  | some t =>
    cases hv : W.lookup (s, i) with
    | none => simp [ht, hv] at h
    | some v =>
      simp [ht, hv] at h
      refine ⟨t.evOf v, ?_⟩
      unfold step
      have hmem : t ∈ P.out s := List.mem_of_getElem? ht
      cases hf : (P.out s).find? (fun t' => t'.matches (t.evOf v)) with
      | none => have := List.find?_eq_none.mp hf t hmem; simp [h] at this
      | some _ => simp

/-- **Theorem T7a (No stuck sessions).** In every state the gate can reach — whatever the agents did —
the session is either complete or some authentic, in-budget submission would be delivered. Honest agents
therefore always have a legal move, and the gate never dead-ends a session on its own. -/
theorem no_stuck (P : Protocol) (W : Witnesses) (V : List Nat) (hc : checkNoStuck P W V = true)
    (cfg : Config) (as : List Input) :
    let m := (monRun cfg P (MState.init P) as).1
    P.isFinal m.s = true ∨ ∃ e, (step P m.s e).isSome := by
  intro m
  have hinv := certifies_sound hc (monitor_state_reach cfg P as)
  simp only [liveInv, Bool.or_eq_true, List.any_eq_true, List.mem_range] at hinv
  rcases hinv with h | ⟨i, _, hi⟩
  · exact Or.inl h
  · exact Or.inr (witOk_step P W _ i hi)

/-- The next submission in a non-stuck state is actually delivered if it is authentic and in budget. -/
theorem no_stuck_deliver (cfg : Config) (P : Protocol) (m : MState) (e : Event)
    (he : (step P m.s e).isSome) (hh : m.halted = false) (hq : isQuar cfg m e.src = false)
    (hb : m.count < cfg.budget) : ∃ m', monStep cfg P m (.send e.src e) = (m', .deliver e) := by
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp he
  exact ⟨_, monStep_honest cfg P m e s' hh hq hb hs'⟩

/-! ### Determinism (W1) as a decidable check -/

def detB (P : Protocol) (s : Nat) : Bool :=
  (P.out s).all (fun t₁ => (P.out s).all (fun t₂ => !(decide (t₁.abs = t₂.abs)) || decide (t₁ = t₂)))

theorem detB_sound (P : Protocol) (s : Nat) (h : detB P s = true) : P.detAt s := by
  intro t₁ h₁ t₂ h₂ ha
  simp only [detB, List.all_eq_true] at h
  have := h t₁ h₁ t₂ h₂
  simp [ha] at this; exact this

/-! ### T7b — completion is always possible -/

abbrev Ranking := List (Nat × Nat)
def rk (ρ : Ranking) (s : Nat) : Nat := (ρ.lookup s).getD 0

/-- A witnessed transition from `s` to a state of strictly smaller rank. -/
def progressOk (P : Protocol) (W : Witnesses) (ρ : Ranking) (s i : Nat) : Bool :=
  witOk P W s i && match (P.out s)[i]? with
    | some t => decide (rk ρ t.next < rk ρ s)
    | none => false

def complInv (P : Protocol) (W : Witnesses) (ρ : Ranking) (s : Nat) : Bool :=
  detB P s && (P.isFinal s || (List.range (P.out s).length).any (fun i => progressOk P W ρ s i))

def checkCompletion (P : Protocol) (W : Witnesses) (ρ : Ranking) (V : List Nat) : Bool :=
  certifies (cfgTS P) (complInv P W ρ) V

theorem completion_aux (P : Protocol) (W : Witnesses) (ρ : Ranking) (V : List Nat)
    (hc : checkCompletion P W ρ V = true) :
    ∀ n s, Reach (cfgTS P) s → rk ρ s ≤ n → ∃ u f, run P s u = some f ∧ P.isFinal f = true := by
  intro n
  induction n with
  | zero =>
    intro s hr hn
    have hinv := certifies_sound hc hr
    simp only [complInv, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.mem_range] at hinv
    rcases hinv.2 with h | ⟨i, _, hi⟩
    · exact ⟨[], s, by simp [run], h⟩
    · simp only [progressOk, Bool.and_eq_true] at hi
      cases ht : (P.out s)[i]? with
      | none => simp [ht] at hi
      | some t => simp [ht] at hi; omega
  | succ n ih =>
    intro s hr hn
    have hinv := certifies_sound hc hr
    simp only [complInv, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.mem_range] at hinv
    obtain ⟨hdet, hrest⟩ := hinv
    rcases hrest with h | ⟨i, _, hi⟩
    · exact ⟨[], s, by simp [run], h⟩
    · simp only [progressOk, Bool.and_eq_true] at hi
      obtain ⟨hw, hrk⟩ := hi
      cases ht : (P.out s)[i]? with
      | none => simp [ht] at hrk
      | some t =>
        simp [ht] at hrk
        unfold witOk at hw
        cases hv : W.lookup (s, i) with
        | none => simp [ht, hv] at hw
        | some v =>
          simp [ht, hv] at hw
          have hmem : t ∈ P.out s := List.mem_of_getElem? ht
          have hstep := step_of_matches P s (t.evOf v) t (detB_sound P s hdet) hmem hw
          have hr' : Reach (cfgTS P) t.next := Reach.step hr (by simp [cfgTS]; exact ⟨t, hmem, rfl⟩)
          obtain ⟨u, f, hu, hf⟩ := ih t.next hr' (by omega)
          exact ⟨t.evOf v :: u, f, by simp [run, hstep, hu], hf⟩

/-- **Theorem T7b (Completion possible).** From every state the gate can reach, some sequence of legal
moves completes the session. -/
theorem completion_possible (P : Protocol) (W : Witnesses) (ρ : Ranking) (V : List Nat)
    (hc : checkCompletion P W ρ V = true) (cfg : Config) (as : List Input) :
    ∃ u f, run P (monRun cfg P (MState.init P) as).1.s u = some f ∧ P.isFinal f = true :=
  completion_aux P W ρ V hc _ _ (monitor_state_reach cfg P as) (Nat.le_refl _)

/-! ### T7c — bounded length (no runaway loops) -/

def boundInv (P : Protocol) (ρ : Ranking) (s : Nat) : Bool :=
  (P.out s).all (fun t => decide (rk ρ t.next < rk ρ s))

def checkBounded (P : Protocol) (ρ : Ranking) (V : List Nat) : Bool :=
  certifies (cfgTS P) (boundInv P ρ) V

theorem bounded_aux (P : Protocol) (ρ : Ranking) (V : List Nat) (hc : checkBounded P ρ V = true) :
    ∀ (t : List Event) (s s' : Nat), Reach (cfgTS P) s → run P s t = some s' → t.length ≤ rk ρ s
  | [], _, _, _, _ => by simp
  | e :: es, s, s', hr, h => by
    unfold run at h
    cases hs : step P s e with
    | none => simp [hs] at h
    | some s₁ =>
      simp [hs] at h
      obtain ⟨t, ht, _, hn⟩ := step_some_iff P s e s₁ hs
      have hr' : Reach (cfgTS P) s₁ := Reach.step hr (by simp [cfgTS]; exact ⟨t, ht, hn⟩)
      have ih := bounded_aux P ρ V hc es s₁ s' hr' h
      have hinv := certifies_sound hc hr
      simp only [boundInv, List.all_eq_true, decide_eq_true_eq] at hinv
      have := hinv t ht
      rw [hn] at this
      simp; omega

/-- **Theorem T7c (No runaway sessions).** For a bounded protocol, every session delivers at most
`rk ρ start` messages, whatever the agents submit — independent of the runtime budget. -/
theorem bounded_length (P : Protocol) (ρ : Ranking) (V : List Nat) (hc : checkBounded P ρ V = true)
    (cfg : Config) (as : List Input) :
    (delivered (monRun cfg P (MState.init P) as).2).length ≤ rk ρ P.start := by
  have h := enforcement cfg P (MState.init P) as
  exact bounded_aux P ρ V hc _ P.start _ (.init (by simp [cfgTS])) h

end SwarmGate
