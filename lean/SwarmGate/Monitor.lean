/-
  SwarmGate.Monitor — the reference monitor and the enforcement game (THEORY.md §4).

  The monitor completely mediates communication. Every guarantee in this file quantifies over *all*
  inputs, i.e. over every possible behaviour of every agent, including a single adversary controlling all
  agents at once and adapting to every verdict.
-/
import SwarmGate.Protocol

namespace SwarmGate

/-- Why an attempt was rejected. -/
inductive Reason where
  | spoof        -- authenticated sender ≠ claimed source role
  | notEnabled   -- the event is not a legal protocol move now (wrong recipient/label/order/type/refinement)
  | budget       -- the session's message budget is exhausted
  | quarantined  -- the sender has been quarantined after repeated violations
  | halted       -- the operator pulled the kill switch
  deriving Repr, DecidableEq, Inhabited

/-- Monitor inputs: an attempt by authenticated principal `σ`, or the (trusted) operator's kill switch. -/
inductive Input where
  | send (σ : Nat) (e : Event)
  | kill
  deriving Repr, Inhabited

inductive Verdict where
  | deliver (e : Event)
  | reject (blamed : Nat) (r : Reason)
  | killed
  deriving Repr, Inhabited

structure Config where
  budget : Nat
  /-- quarantine a principal after this many violations (0 = never quarantine) -/
  maxStrikes : Nat
  deriving Repr, Inhabited

structure MState where
  s : Nat
  count : Nat
  strikes : List (Nat × Nat)
  halted : Bool
  deriving Repr, Inhabited

def MState.init (P : Protocol) : MState := ⟨P.start, 0, [], false⟩

def strikesOf (L : List (Nat × Nat)) (σ : Nat) : Nat := (L.lookup σ).getD 0
def addStrike (L : List (Nat × Nat)) (σ : Nat) : List (Nat × Nat) := (σ, strikesOf L σ + 1) :: L

def isQuar (cfg : Config) (m : MState) (σ : Nat) : Bool :=
  cfg.maxStrikes != 0 && decide (cfg.maxStrikes ≤ strikesOf m.strikes σ)

/-- **The gate.** One monitor step. This exact function is compiled into the deployed binary. -/
def monStep (cfg : Config) (P : Protocol) (m : MState) : Input → MState × Verdict
  | .kill => ({ m with halted := true }, .killed)
  | .send σ e =>
    if m.halted then (m, .reject σ .halted)
    else if isQuar cfg m σ then (m, .reject σ .quarantined)
    else if σ ≠ e.src then ({ m with strikes := addStrike m.strikes σ }, .reject σ .spoof)
    else if cfg.budget ≤ m.count then (m, .reject σ .budget)
    else match step P m.s e with
      | some s' => ({ m with s := s', count := m.count + 1 }, .deliver e)
      | none => ({ m with strikes := addStrike m.strikes σ }, .reject σ .notEnabled)

def monRun (cfg : Config) (P : Protocol) : MState → List Input → MState × List Verdict
  | m, [] => (m, [])
  | m, a :: as =>
    let r := monStep cfg P m a
    let rest := monRun cfg P r.1 as
    (rest.1, r.2 :: rest.2)

def Verdict.delivered? : Verdict → Option Event
  | .deliver e => some e
  | _ => none

/-- The events actually delivered to recipients. -/
def delivered (vs : List Verdict) : List Event := vs.filterMap Verdict.delivered?

/-! ### Elementary step lemmas -/

theorem monStep_cases (cfg : Config) (P : Protocol) (m : MState) (a : Input) :
    (∃ e s', (monStep cfg P m a).2 = .deliver e ∧ step P m.s e = some s' ∧
        (monStep cfg P m a).1 = { m with s := s', count := m.count + 1 }) ∨
    ((monStep cfg P m a).2.delivered? = none ∧ (monStep cfg P m a).1.s = m.s ∧
        (monStep cfg P m a).1.count = m.count) := by
  cases a with
  | kill => right; simp [monStep, Verdict.delivered?]
  | send σ e =>
    unfold monStep
    by_cases h1 : m.halted = true
    · right; simp [h1, Verdict.delivered?]
    · by_cases h2 : isQuar cfg m σ = true
      · right; simp [h1, h2, Verdict.delivered?]
      · by_cases h3 : σ ≠ e.src
        · right; simp [h1, h2, h3, Verdict.delivered?]
        · by_cases h4 : cfg.budget ≤ m.count
          · right; simp [h1, h2, h3, h4, Verdict.delivered?]
          · cases hs : step P m.s e with
            | none => right; simp [h1, h2, h3, h4, hs, Verdict.delivered?]
            | some s' => left; exact ⟨e, s', by simp [h1, h2, h3, h4, hs]⟩

/-! ### T1 — Enforcement (soundness) -/

/-- **Theorem T1 (Enforcement).** Whatever the agents submit, the delivered sequence is a run of the
protocol from the monitor's initial state, ending exactly in the monitor's final protocol state. -/
theorem enforcement (cfg : Config) (P : Protocol) : ∀ (m : MState) (as : List Input),
    run P m.s (delivered (monRun cfg P m as).2) = some (monRun cfg P m as).1.s
  | m, [] => by simp [monRun, delivered, run]
  | m, a :: as => by
    have ih := enforcement cfg P (monStep cfg P m a).1 as
    rcases monStep_cases cfg P m a with ⟨e, s', hv, hs, hm⟩ | ⟨hv, hs, _⟩
    · simp only [monRun, delivered, List.filterMap_cons, hv, Verdict.delivered?]
      simp only [delivered] at ih
      rw [run, hs]; rw [hm] at ih; simpa [hm] using ih
    · simp only [monRun, delivered, List.filterMap_cons, hv]
      simp only [delivered] at ih
      rw [hs] at ih; exact ih

/-- Corollary: every delivered trace of a fresh session lies in the protocol's prefix language. -/
theorem enforcement_pref (cfg : Config) (P : Protocol) (as : List Input) :
    Pref P (delivered (monRun cfg P (MState.init P) as).2) := by
  unfold Pref
  have h := enforcement cfg P (MState.init P) as
  have h0 : (MState.init P).s = P.start := rfl
  rw [h0] at h; rw [h]; rfl

/-! ### Adaptive adversaries -/

/-- An adaptive adversary sees every past verdict and chooses the next input. It may control all agents. -/
def Strategy := List Verdict → Input

def play (cfg : Config) (P : Protocol) (A : Strategy) : Nat → MState → List Verdict → MState × List Verdict
  | 0, m, hist => (m, hist)
  | n + 1, m, hist =>
    let r := monStep cfg P m (A hist)
    play cfg P A n r.1 (hist ++ [r.2])

/-- Lemma 4.0: every interaction with an adaptive adversary is an interaction with some input list. -/
theorem play_is_run (cfg : Config) (P : Protocol) (A : Strategy) : ∀ (n : Nat) (m : MState)
    (hist : List Verdict), ∃ as, play cfg P A n m hist =
      ((monRun cfg P m as).1, hist ++ (monRun cfg P m as).2)
  | 0, m, hist => ⟨[], by simp [play, monRun]⟩
  | n + 1, m, hist => by
    obtain ⟨as, h⟩ := play_is_run cfg P A n (monStep cfg P m (A hist)).1 (hist ++ [(monStep cfg P m (A hist)).2])
    refine ⟨A hist :: as, ?_⟩
    simp only [play]; rw [h]; simp [monRun]

/-- **Theorem T1 for adaptive adversaries.** -/
theorem enforcement_adaptive (cfg : Config) (P : Protocol) (A : Strategy) (n : Nat) :
    Pref P (delivered (play cfg P A n (MState.init P) []).2) := by
  obtain ⟨as, h⟩ := play_is_run cfg P A n (MState.init P) []
  rw [h]; simpa using enforcement_pref cfg P as

/-! ### T2 — Transparency -/

def conformantInputs (es : List Event) : List Input := es.map (fun e => .send e.src e)

theorem monStep_honest (cfg : Config) (P : Protocol) (m : MState) (e : Event) (s' : Nat)
    (hh : m.halted = false) (hq : isQuar cfg m e.src = false) (hb : m.count < cfg.budget)
    (hs : step P m.s e = some s') :
    monStep cfg P m (.send e.src e) = ({ m with s := s', count := m.count + 1 }, .deliver e) := by
  have : ¬ cfg.budget ≤ m.count := by omega
  simp [monStep, hh, hq, this, hs]

/-- **Theorem T2 (Transparency).** Conformant traffic within budget is delivered unchanged. -/
theorem transparency (cfg : Config) (P : Protocol) : ∀ (m : MState) (es : List Event) (s' : Nat),
    run P m.s es = some s' → m.halted = false → m.count + es.length ≤ cfg.budget →
    (∀ e ∈ es, isQuar cfg m e.src = false) →
    monRun cfg P m (conformantInputs es) =
      ({ m with s := s', count := m.count + es.length }, es.map Verdict.deliver)
  | m, [], s', hr, _, _, _ => by simp [run] at hr; subst hr; simp [monRun, conformantInputs]
  | m, e :: es, s', hr, hh, hb, hq => by
    unfold run at hr
    cases hs : step P m.s e with
    | none => simp [hs] at hr
    | some s₁ =>
      simp [hs] at hr
      have h1 := monStep_honest cfg P m e s₁ hh (hq e (by simp)) (by simp at hb; omega) hs
      have ih := transparency cfg P { m with s := s₁, count := m.count + 1 } es s' hr hh
        (by simp at hb ⊢; omega) (by intro e' he'; simpa [isQuar] using hq e' (by simp [he']))
      simp only [conformantInputs, List.map_cons, monRun, h1] at ih ⊢
      rw [ih]; simp; omega

/-- Every conformant trace is delivered in full from a fresh session (budget permitting). -/
theorem transparency_init (cfg : Config) (P : Protocol) (es : List Event)
    (hp : Pref P es) (hb : es.length ≤ cfg.budget) :
    delivered (monRun cfg P (MState.init P) (conformantInputs es)).2 = es := by
  unfold Pref at hp
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hp
  rw [transparency cfg P (MState.init P) es s' (by simpa [MState.init] using hs') rfl
    (by simpa [MState.init] using hb) (by intro e _; simp [isQuar, MState.init, strikesOf])]
  have hc : (Verdict.delivered? ∘ Verdict.deliver) = some := by funext e; rfl
  simp [delivered, List.filterMap_map, hc]

/-! ### T3 — Blame -/

/-- **Theorem T3a (Blame soundness).** A rejection always blames the authenticated submitter, and a
`spoof`/`notEnabled` verdict is issued only when the attempt really was not an authentic enabled move. -/
theorem blame_sound (cfg : Config) (P : Protocol) (m : MState) (σ : Nat) (e : Event) (b : Nat) (r : Reason)
    (h : (monStep cfg P m (.send σ e)).2 = .reject b r) :
    b = σ ∧ (r = .spoof → σ ≠ e.src) ∧ (r = .notEnabled → σ = e.src ∧ step P m.s e = none) ∧
      (r = .budget → cfg.budget ≤ m.count) ∧ (r = .halted → m.halted = true) ∧
      (r = .quarantined → isQuar cfg m σ = true) := by
  unfold monStep at h
  by_cases h1 : m.halted = true
  · simp [h1] at h; obtain ⟨rfl, rfl⟩ := h; simp [h1]
  · by_cases h2 : isQuar cfg m σ = true
    · simp [h1, h2] at h; obtain ⟨rfl, rfl⟩ := h; simp [h2]
    · by_cases h3 : σ ≠ e.src
      · simp [h1, h2, h3] at h; obtain ⟨rfl, rfl⟩ := h; simpa using h3
      · by_cases h4 : cfg.budget ≤ m.count
        · simp [h1, h2, h3, h4] at h; obtain ⟨rfl, rfl⟩ := h; simp [h4]
        · cases hs : step P m.s e with
          | none =>
            simp [h1, h2, h3, h4, hs] at h; obtain ⟨rfl, rfl⟩ := h
            simp at h3; simp [h3]
          | some s' => simp [h1, h2, h3, h4, hs] at h

/-- Principal `h` is honest along a run: whenever it submits, it submits an authentic, enabled event. -/
def Honest (cfg : Config) (P : Protocol) (h : Nat) : MState → List Input → Prop
  | _, [] => True
  | m, a :: as => (∀ e, a = .send h e → e.src = h ∧ (step P m.s e).isSome) ∧
      Honest cfg P h (monStep cfg P m a).1 as

theorem strikesOf_addStrike_ne (L : List (Nat × Nat)) (σ h : Nat) (hne : σ ≠ h) :
    strikesOf (addStrike L σ) h = strikesOf L h := by
  simp [strikesOf, addStrike, List.lookup, show (h == σ) = false by simpa [beq_iff_eq] using Ne.symm hne]

/-- One step never changes the strike count of a principal that does not misbehave in that step. -/
theorem monStep_strikes_other (cfg : Config) (P : Protocol) (m : MState) (a : Input) (h : Nat)
    (ha : ∀ e, a = .send h e → e.src = h ∧ (step P m.s e).isSome) :
    strikesOf (monStep cfg P m a).1.strikes h = strikesOf m.strikes h := by
  cases a with
  | kill => simp [monStep]
  | send σ e =>
    unfold monStep
    by_cases hσ : σ = h
    · subst hσ
      obtain ⟨hsrc, hen⟩ := ha e rfl
      obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hen
      by_cases h1 : m.halted = true <;> by_cases h2 : isQuar cfg m σ = true <;>
        by_cases h4 : cfg.budget ≤ m.count <;> simp [h1, h2, h4, hsrc, hs']
    · by_cases h1 : m.halted = true <;> by_cases h2 : isQuar cfg m σ = true <;>
        by_cases h3 : σ ≠ e.src <;> by_cases h4 : cfg.budget ≤ m.count <;>
        simp [h1, h2, h3, h4] <;> (try cases step P m.s e) <;>
        simp [strikesOf_addStrike_ne _ _ _ hσ]

theorem monStep_halted_mono (cfg : Config) (P : Protocol) (m : MState) (a : Input) :
    m.halted = true → (monStep cfg P m a).1.halted = true := by
  intro hm; cases a with
  | kill => simp [monStep]
  | send σ e => unfold monStep; simp [hm]

/-- **Theorem T3b (Honest principals are never blamed).** Whatever every other principal does, an honest
principal that starts unquarantined is never rejected for a violation and never quarantined; it can only
be stopped by the budget or the operator's kill switch. -/
theorem honest_never_blamed (cfg : Config) (P : Protocol) (h : Nat) : ∀ (m : MState) (as : List Input),
    Honest cfg P h m as → isQuar cfg m h = false →
    ∀ v ∈ (monRun cfg P m as).2, ∀ r, v = .reject h r → r = .budget ∨ r = .halted
  | m, [], _, _ => by simp [monRun]
  | m, a :: as, ⟨ha, hrest⟩, hq => by
    intro v hv r hvr
    simp only [monRun, List.mem_cons] at hv
    rcases hv with hv | hv
    · -- the verdict for the current input
      subst hv
      cases a with
      | kill => simp [monStep] at hvr
      | send σ e =>
        have hb := blame_sound cfg P m σ e h r hvr
        obtain ⟨rfl, hsp, hne, -, -, hqu⟩ := hb
        obtain ⟨hsrc, hen⟩ := ha e rfl
        cases r with
        | spoof => exact absurd hsrc.symm (hsp rfl)
        | notEnabled => have := (hne rfl).2; simp [this] at hen
        | quarantined => rw [hq] at hqu; simp at hqu
        | budget => simp
        | halted => simp
    · have hq' : isQuar cfg (monStep cfg P m a).1 h = false := by
        have := monStep_strikes_other cfg P m a h ha
        simp only [isQuar] at hq ⊢; rw [this]; exact hq
      exact honest_never_blamed cfg P h _ as hrest hq' v hv r hvr

/-! ### T3′ — Containment: kill switch, quarantine, budget -/

theorem kill_contains (cfg : Config) (P : Protocol) : ∀ (m : MState) (as : List Input),
    m.halted = true → delivered (monRun cfg P m as).2 = []
  | m, [], _ => by simp [monRun, delivered]
  | m, a :: as, hm => by
    have ih := kill_contains cfg P (monStep cfg P m a).1 as (monStep_halted_mono cfg P m a hm)
    have hv : (monStep cfg P m a).2.delivered? = none := by
      cases a with
      | kill => simp [monStep, Verdict.delivered?]
      | send σ e => simp [monStep, hm, Verdict.delivered?]
    simp only [monRun, delivered, List.filterMap_cons, hv]
    exact ih

theorem strikesOf_addStrike_ge (L : List (Nat × Nat)) (σ h : Nat) :
    strikesOf L h ≤ strikesOf (addStrike L σ) h := by
  by_cases hσ : σ = h
  · subst hσ; simp [strikesOf, addStrike]
  · rw [strikesOf_addStrike_ne _ _ _ hσ]; exact Nat.le_refl _

theorem monStep_strikes_mono (cfg : Config) (P : Protocol) (m : MState) (a : Input) (h : Nat) :
    strikesOf m.strikes h ≤ strikesOf (monStep cfg P m a).1.strikes h := by
  cases a with
  | kill => simp [monStep]
  | send σ e =>
    unfold monStep
    by_cases h1 : m.halted = true <;> by_cases h2 : isQuar cfg m σ = true <;>
      by_cases h3 : σ ≠ e.src <;> by_cases h4 : cfg.budget ≤ m.count <;>
      simp [h1, h2, h3, h4] <;> (try cases step P m.s e) <;> simp [strikesOf_addStrike_ge]

theorem isQuar_mono (cfg : Config) (P : Protocol) (m : MState) (a : Input) (σ : Nat) :
    isQuar cfg m σ = true → isQuar cfg (monStep cfg P m a).1 σ = true := by
  simp only [isQuar, Bool.and_eq_true, decide_eq_true_eq]
  intro ⟨h1, h2⟩; exact ⟨h1, Nat.le_trans h2 (monStep_strikes_mono cfg P m a σ)⟩

/-- **Theorem T3′ (Quarantine).** Once a principal is quarantined, no event attributed to it is ever
delivered again — neither submitted by itself nor by anyone impersonating it. -/
theorem quarantine_contains (cfg : Config) (P : Protocol) (σ : Nat) : ∀ (m : MState) (as : List Input),
    isQuar cfg m σ = true → ∀ e ∈ delivered (monRun cfg P m as).2, e.src ≠ σ
  | m, [], _ => by simp [monRun, delivered]
  | m, a :: as, hq => by
    intro e he
    simp only [monRun, delivered, List.filterMap_cons] at he
    have ih := quarantine_contains cfg P σ (monStep cfg P m a).1 as (isQuar_mono cfg P m a σ hq)
    cases hv : (monStep cfg P m a).2.delivered? with
    | none => simp [hv] at he; exact ih e (by simp only [delivered, List.mem_filterMap]; exact he)
    | some e' =>
      simp [hv] at he
      rcases he with rfl | he
      · cases a with
        | kill => simp [monStep, Verdict.delivered?] at hv
        | send σ' e'' =>
          unfold monStep at hv
          by_cases h1 : m.halted = true
          · simp [h1, Verdict.delivered?] at hv
          · by_cases h2 : isQuar cfg m σ' = true
            · simp [h1, h2, Verdict.delivered?] at hv
            · by_cases h3 : σ' ≠ e''.src
              · simp [h1, h2, h3, Verdict.delivered?] at hv
              · by_cases h4 : cfg.budget ≤ m.count
                · simp [h1, h2, h3, h4, Verdict.delivered?] at hv
                · cases hs : step P m.s e'' with
                  | none => simp [h1, h2, h3, h4, hs, Verdict.delivered?] at hv
                  | some s' =>
                    simp [h1, h2, h3, h4, hs, Verdict.delivered?] at hv
                    subst hv; simp at h3; subst h3
                    intro heq; subst heq; exact h2 hq
      · exact ih e (by simp only [delivered, List.mem_filterMap]; exact he)

theorem count_run (cfg : Config) (P : Protocol) : ∀ (m : MState) (as : List Input),
    (monRun cfg P m as).1.count = m.count + (delivered (monRun cfg P m as).2).length
  | m, [] => by simp [monRun, delivered]
  | m, a :: as => by
    have ih := count_run cfg P (monStep cfg P m a).1 as
    rcases monStep_cases cfg P m a with ⟨e, s', hv, _, hm⟩ | ⟨hv, _, hc⟩
    · simp only [monRun, delivered, List.filterMap_cons, hv, Verdict.delivered?] at ih ⊢
      rw [ih, hm]; simp; omega
    · simp only [monRun, delivered, List.filterMap_cons, hv] at ih ⊢
      rw [ih, hc]

theorem count_le_budget (cfg : Config) (P : Protocol) : ∀ (m : MState) (as : List Input),
    m.count ≤ cfg.budget → (monRun cfg P m as).1.count ≤ cfg.budget
  | m, [], h => by simpa [monRun] using h
  | m, a :: as, h => by
    apply count_le_budget cfg P _ as
    rcases monStep_cases cfg P m a with ⟨e, s', hv, hs, hm⟩ | ⟨_, _, hc⟩
    · rw [hm]; simp
      cases a with
      | kill => simp [monStep] at hv
      | send σ e' =>
        unfold monStep at hv
        by_cases h1 : m.halted = true <;> by_cases h2 : isQuar cfg m σ = true <;>
          by_cases h3 : σ ≠ e'.src <;> by_cases h4 : cfg.budget ≤ m.count <;>
          simp [h1, h2, h3, h4] at hv <;> omega
    · rw [hc]; exact h

/-- **Theorem T3′ (Budget).** A session never delivers more than its budget of messages. -/
theorem budget_bound (cfg : Config) (P : Protocol) (as : List Input) :
    (delivered (monRun cfg P (MState.init P) as).2).length ≤ cfg.budget := by
  have h1 := count_run cfg P (MState.init P) as
  have h2 := count_le_budget cfg P (MState.init P) as (by simp [MState.init])
  have h0 : (MState.init P).count = 0 := rfl
  rw [h0] at h1; omega

end SwarmGate
