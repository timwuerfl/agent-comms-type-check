/-
  SwarmGate.Noninterference — noninterference for *arbitrary* agents (THEORY.md §5.4, Theorems T9, T9b).

  LLM agents cannot be modelled. We therefore model every clean (uncompromised) role as an *arbitrary*
  deterministic function of what it has seen (its view), and the adversary as an arbitrary function of the
  *whole* trace that controls a set `A` of roles (e.g. the untrusted web tool plus every agent that read
  attacker text). The result: clean behaviour depends on the adversary only through a declassified
  channel `δ` consisting of A's control choices (who/what/which label) and the payloads A sends to clean
  roles. Payloads exchanged among A-roles (say, a whole attacker-written web page) are invisible.
-/
import SwarmGate.Liveness

namespace SwarmGate

/-! ### The system model -/

/-- The view of role `r`: the events it sent or received, in order. -/
def view (r : Nat) (t : List Event) : List Event := t.filter (fun e => e.src == r || e.dst == r)

/-- A mediated multi-agent system. -/
structure System where
  P : Protocol
  /-- whose turn it is in protocol state `s` (payload-independent scheduling) -/
  turn : Nat → Option Nat
  /-- attacker-controlled roles -/
  inA : Nat → Bool
  /-- the strategy of each role `r` (used only when `inA r = false`), applied to `view r t`.
      Arbitrary: an LLM with its random seed fixed is such a function. -/
  clean : Nat → List Event → Option Event

/-- The adversary: full information (it sees the entire trace, including all payloads). -/
abbrev Adversary := List Event → Option Event

/-- What role `r` proposes after trace `t`. -/
def System.propose (S : System) (adv : Adversary) (r : Nat) (t : List Event) : Option Event :=
  if S.inA r then adv t else S.clean r (view r t)

/-- One turn: the role whose turn it is proposes an event; it is delivered iff it is authentic
(`src` = that role) and the protocol step succeeds; otherwise the run halts (`none`). -/
def sysStep (S : System) (adv : Adversary) (s : Nat) (t : List Event) : Option (Nat × List Event) :=
  match S.turn s with
  | none => none
  | some r =>
    match S.propose adv r t with
    | none => none
    | some e => if e.src = r then (step S.P s e).map (fun s' => (s', t ++ [e])) else none

/-- Execution with fuel; stops at the first halt. Returns the final protocol state and trace. -/
def exec (S : System) (adv : Adversary) : Nat → Nat → List Event → Nat × List Event
  | 0, s, t => (s, t)
  | n + 1, s, t => match sysStep S adv s t with
    | none => (s, t)
    | some (s', t') => exec S adv n s' t'

/-! ### The declassified channel δ -/

/-- What clean roles may legitimately learn about one event: for an A-sent event its destination, label
and — only if the destination is clean — its payload; nothing for events sent by clean roles (those are
determined by the clean roles themselves). -/
inductive Obs where
  | att (dst : Nat) (label : String) (payload : Option Value)
  | cl

def obs (S : System) (e : Event) : Obs :=
  if S.inA e.src then .att e.dst e.label (if S.inA e.dst then none else some e.payload) else .cl

def delta (S : System) (t : List Event) : List Obs := t.map (obs S)

/-! ### Agreement: equal except for the payloads of A→A events -/

def EvAgree (S : System) (e₁ e₂ : Event) : Prop :=
  e₁.src = e₂.src ∧ e₁.dst = e₂.dst ∧ e₁.label = e₂.label ∧
    ((S.inA e₁.src = true ∧ S.inA e₁.dst = true) ∨ e₁.payload = e₂.payload)

inductive Agree (S : System) : List Event → List Event → Prop
  | nil : Agree S [] []
  | cons {e₁ e₂ : Event} {t₁ t₂ : List Event} : EvAgree S e₁ e₂ → Agree S t₁ t₂ →
      Agree S (e₁ :: t₁) (e₂ :: t₂)

theorem EvAgree.refl (S : System) (e : Event) : EvAgree S e e := ⟨rfl, rfl, rfl, Or.inr rfl⟩

theorem Agree.length_eq {S : System} {t₁ t₂ : List Event} (h : Agree S t₁ t₂) :
    t₁.length = t₂.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Agree.snoc {S : System} {t₁ t₂ : List Event} {e₁ e₂ : Event} (h : Agree S t₁ t₂)
    (he : EvAgree S e₁ e₂) : Agree S (t₁ ++ [e₁]) (t₂ ++ [e₂]) := by
  induction h with
  | nil => exact .cons he .nil
  | cons h' _ ih => exact .cons h' ih

theorem Event.ext' {e₁ e₂ : Event} (h1 : e₁.src = e₂.src) (h2 : e₁.dst = e₂.dst)
    (h3 : e₁.label = e₂.label) (h4 : e₁.payload = e₂.payload) : e₁ = e₂ := by
  cases e₁; cases e₂; simp_all

/-- Fact (1): agreeing traces look identical to every clean role (an event in a clean role's view is never
A→A). -/
theorem view_agree {S : System} {t₁ t₂ : List Event} (h : Agree S t₁ t₂) (r : Nat)
    (hr : S.inA r = false) : view r t₁ = view r t₂ := by
  induction h with
  | nil => rfl
  | @cons e₁ e₂ _ _ he _ ih =>
    obtain ⟨h1, h2, h3, h4⟩ := he
    by_cases hv : (e₁.src == r || e₁.dst == r) = true
    · have hv' : (e₂.src == r || e₂.dst == r) = true := by rw [← h1, ← h2]; exact hv
      have hp : e₁.payload = e₂.payload := by
        rcases h4 with ⟨ha, hb⟩ | hp
        · simp only [Bool.or_eq_true, beq_iff_eq] at hv
          rcases hv with rfl | rfl <;> simp_all
        · exact hp
      simp only [view, List.filter_cons, hv, hv', if_true]
      rw [Event.ext' h1 h2 h3 hp]
      exact congrArg _ ih
    · have hv' : ¬ (e₂.src == r || e₂.dst == r) = true := by rw [← h1, ← h2]; exact hv
      simp only [view, List.filter_cons, hv, hv']
      exact ih

/-! ### Step lemmas -/

theorem sysStep_some {S : System} {adv : Adversary} {s : Nat} {t : List Event} {s' : Nat}
    {t' : List Event} (h : sysStep S adv s t = some (s', t')) :
    ∃ r e, S.turn s = some r ∧ S.propose adv r t = some e ∧ e.src = r ∧ step S.P s e = some s' ∧
      t' = t ++ [e] := by
  unfold sysStep at h
  cases hr : S.turn s with
  | none => simp [hr] at h
  | some r =>
    cases hp : S.propose adv r t with
    | none => simp [hr, hp] at h
    | some e =>
      simp only [hr, hp] at h
      by_cases he : e.src = r
      · simp only [he, if_true] at h
        cases hs : step S.P s e with
        | none => simp [hs] at h
        | some s₁ =>
          simp [hs] at h
          exact ⟨r, e, rfl, hp, he, by rw [hs, h.1], h.2.symm⟩
      · simp [he] at h

/-- Fact (2): under determinism the successor state depends only on the abstract event. -/
theorem step_abs_det {P : Protocol} {s s₁ s₂ : Nat} {e₁ e₂ : Event} (hdet : P.detAt s)
    (h₁ : step P s e₁ = some s₁) (h₂ : step P s e₂ = some s₂) (ha : e₁.abs = e₂.abs) : s₁ = s₂ := by
  obtain ⟨t₁, ht₁, hm₁, hn₁⟩ := step_some_iff P s e₁ s₁ h₁
  obtain ⟨t₂, ht₂, hm₂, hn₂⟩ := step_some_iff P s e₂ s₂ h₂
  have : t₁ = t₂ := hdet t₁ ht₁ t₂ ht₂ (by rw [Trans.abs_of_matches hm₁, Trans.abs_of_matches hm₂, ha])
  rw [← hn₁, ← hn₂, this]

/-- Execution only extends the trace. -/
theorem exec_extends (S : System) (adv : Adversary) :
    ∀ (n s : Nat) (t : List Event), ∃ u, (exec S adv n s t).2 = t ++ u
  | 0, s, t => ⟨[], by simp [exec]⟩
  | n + 1, s, t => by
    unfold exec
    cases h : sysStep S adv s t with
    | none => exact ⟨[], by simp⟩
    | some p =>
      obtain ⟨s', t'⟩ := p
      obtain ⟨_, e, _, _, _, _, ht⟩ := sysStep_some h
      obtain ⟨u, hu⟩ := exec_extends S adv n s' t'
      exact ⟨e :: u, by subst ht; simp [hu]⟩

/-- Every execution is a protocol run (the gate's enforcement, T1, at the system level). -/
theorem exec_run (S : System) (adv : Adversary) : ∀ (n s₀ s : Nat) (t : List Event),
    run S.P s₀ t = some s → run S.P s₀ (exec S adv n s t).2 = some (exec S adv n s t).1
  | 0, s₀, s, t, h => by simpa [exec] using h
  | n + 1, s₀, s, t, h => by
    unfold exec
    cases hs : sysStep S adv s t with
    | none => simpa using h
    | some p =>
      obtain ⟨s', t'⟩ := p
      obtain ⟨_, e, _, _, _, hst, ht⟩ := sysStep_some hs
      apply exec_run S adv n s₀ s' t'
      rw [ht, run_snoc, h]; simpa using hst

/-- Fact (3), one step: if both runs take a step from agreeing traces in the same state and the
declassified channel agrees on the extended traces, they reach the same state and still agree. -/
theorem sysStep_agree (S : System) (adv₁ adv₂ : Adversary) (hdet : ∀ s, S.P.detAt s)
    {s s₁ s₂ : Nat} {t₁ t₂ t₁' t₂' : List Event} (hA : Agree S t₁ t₂)
    (h₁ : sysStep S adv₁ s t₁ = some (s₁, t₁')) (h₂ : sysStep S adv₂ s t₂ = some (s₂, t₂'))
    (hδ : delta S t₁' = delta S t₂') : s₁ = s₂ ∧ Agree S t₁' t₂' := by
  obtain ⟨r₁, e₁, hr₁, hp₁, hsrc₁, hst₁, ht₁⟩ := sysStep_some h₁
  obtain ⟨r₂, e₂, hr₂, hp₂, hsrc₂, hst₂, ht₂⟩ := sysStep_some h₂
  have hr : r₁ = r₂ := by rw [hr₁] at hr₂; exact Option.some.inj hr₂
  subst hr ht₁ ht₂
  have hev : EvAgree S e₁ e₂ := by
    cases hA' : S.inA r₁ with
    | false =>
      -- a clean role's proposal is a function of its view
      have hv := view_agree hA r₁ hA'
      simp only [System.propose, hA', Bool.false_eq_true, if_false] at hp₁ hp₂
      rw [hv, hp₂] at hp₁
      rw [Option.some.inj hp₁]; exact EvAgree.refl S e₁
    | true =>
      -- the adversary's proposals are pinned by δ
      have hlen : (delta S t₁).length = (delta S t₂).length := by
        simp [delta, hA.length_eq]
      simp only [delta, List.map_append, List.map_cons, List.map_nil] at hδ
      have ho : obs S e₁ = obs S e₂ := by
        have := (List.append_inj hδ (by simpa [delta] using hlen)).2
        simpa using this
      have hs1 : S.inA e₁.src = true := by rw [hsrc₁]; exact hA'
      have hs2 : S.inA e₂.src = true := by rw [hsrc₂]; exact hA'
      simp only [obs, hs1, hs2, if_true] at ho
      injection ho with hd hl hp
      refine ⟨by rw [hsrc₁, hsrc₂], hd, hl, ?_⟩
      cases hd1 : S.inA e₁.dst with
      | true => exact Or.inl ⟨hs1, rfl⟩
      | false =>
        have hd2 : S.inA e₂.dst = false := by rw [← hd]; exact hd1
        simp only [hd1, hd2, Bool.false_eq_true, if_false] at hp
        exact Or.inr (Option.some.inj hp)
  have ⟨ha, hb, hc, _⟩ := hev
  refine ⟨step_abs_det (hdet s) hst₁ hst₂ (by simp [Event.abs, ha, hb, hc]), hA.snoc hev⟩

/-- The invariant behind T9, for arbitrary starting configurations. -/
theorem noninterference_aux (S : System) (adv₁ adv₂ : Adversary) (hdet : ∀ s, S.P.detAt s) :
    ∀ (n s : Nat) (t₁ t₂ : List Event), Agree S t₁ t₂ →
      delta S (exec S adv₁ n s t₁).2 = delta S (exec S adv₂ n s t₂).2 →
      (exec S adv₁ n s t₁).1 = (exec S adv₂ n s t₂).1 ∧
        Agree S (exec S adv₁ n s t₁).2 (exec S adv₂ n s t₂).2
  | 0, s, t₁, t₂, hA, _ => by simpa [exec] using hA
  | n + 1, s, t₁, t₂, hA, hδ => by
    have hlen := hA.length_eq
    unfold exec at hδ ⊢
    cases h₁ : sysStep S adv₁ s t₁ with
    | none =>
      cases h₂ : sysStep S adv₂ s t₂ with
      | none => exact ⟨rfl, hA⟩
      | some p₂ =>
        -- run 1 halted, run 2 continued: the δ-traces have different lengths
        exfalso
        obtain ⟨s₂, t₂'⟩ := p₂
        rw [h₁, h₂] at hδ
        obtain ⟨_, e₂, _, _, _, _, ht₂⟩ := sysStep_some h₂
        obtain ⟨u, hu⟩ := exec_extends S adv₂ n s₂ t₂'
        subst ht₂; rw [hu] at hδ
        have := congrArg List.length hδ
        simp [delta] at this; omega
    | some p₁ =>
      obtain ⟨s₁, t₁'⟩ := p₁
      cases h₂ : sysStep S adv₂ s t₂ with
      | none =>
        exfalso
        rw [h₁, h₂] at hδ
        obtain ⟨_, e₁, _, _, _, _, ht₁⟩ := sysStep_some h₁
        obtain ⟨u, hu⟩ := exec_extends S adv₁ n s₁ t₁'
        subst ht₁; rw [hu] at hδ
        have := congrArg List.length hδ
        simp [delta] at this; omega
      | some p₂ =>
        obtain ⟨s₂, t₂'⟩ := p₂
        rw [h₁, h₂] at hδ
        simp only
        obtain ⟨_, e₁, _, _, _, _, ht₁⟩ := sysStep_some h₁
        obtain ⟨_, e₂, _, _, _, _, ht₂⟩ := sysStep_some h₂
        obtain ⟨u₁, hu₁⟩ := exec_extends S adv₁ n s₁ t₁'
        obtain ⟨u₂, hu₂⟩ := exec_extends S adv₂ n s₂ t₂'
        have hδ' : delta S t₁' = delta S t₂' := by
          rw [hu₁, hu₂] at hδ
          simp only [delta, List.map_append] at hδ
          exact (List.append_inj hδ (by simp [ht₁, ht₂, hlen])).1
        obtain ⟨hs, hA'⟩ := sysStep_agree S adv₁ adv₂ hdet hA h₁ h₂ hδ'
        subst hs
        exact noninterference_aux S adv₁ adv₂ hdet n s₁ t₁' t₂' hA' hδ

/-- **Theorem T9 (Noninterference for arbitrary agents), invariant form.** If two adversaries induce the
same declassified channel, the two runs end in the same protocol state and their traces agree on every
event except the payloads of A→A events (in particular they have the same length). -/
theorem noninterference_inv (S : System) (adv₁ adv₂ : Adversary) (n : Nat)
    (hdet : ∀ s, S.P.detAt s)
    (hδ : delta S (exec S adv₁ n S.P.start []).2 = delta S (exec S adv₂ n S.P.start []).2) :
    (exec S adv₁ n S.P.start []).1 = (exec S adv₂ n S.P.start []).1 ∧
      Agree S (exec S adv₁ n S.P.start []).2 (exec S adv₂ n S.P.start []).2 ∧
      (exec S adv₁ n S.P.start []).2.length = (exec S adv₂ n S.P.start []).2.length := by
  obtain ⟨h1, h2⟩ := noninterference_aux S adv₁ adv₂ hdet n S.P.start [] [] .nil hδ
  exact ⟨h1, h2, h2.length_eq⟩

/-- **Theorem T9 (Noninterference for arbitrary agents).** Clean roles are arbitrary deterministic
functions of their views; the adversary controls the roles in `A`, sees the whole trace and may be any
function. If two adversaries produce the same declassified channel `δ` (A's control choices and the
payloads A sends to clean roles), every clean role sees exactly the same thing in both runs — hence, as
its behaviour is a function of its view, behaves identically.

Equivalently, the view of every clean role is a *function of δ*: the pairwise statement says precisely
that `δ(run adv) ↦ view r (run adv)` is well defined over the set of all adversaries, so no explicit
function is needed. Payloads that A-roles send to each other (e.g. a full attacker-written web page read
by a quarantined reader) have no influence at all on clean roles. -/
theorem noninterference (S : System) (adv₁ adv₂ : Adversary) (n : Nat)
    (hdet : ∀ s, S.P.detAt s)
    (hδ : delta S (exec S adv₁ n S.P.start []).2 = delta S (exec S adv₂ n S.P.start []).2) :
    ∀ r, S.inA r = false →
      view r (exec S adv₁ n S.P.start []).2 = view r (exec S adv₂ n S.P.start []).2 :=
  fun r hr => view_agree (noninterference_inv S adv₁ adv₂ n hdet hδ).2.1 r hr

/-- T9 with determinism discharged by the decidable check `detB` (as produced by the analyser). -/
theorem noninterference_detB (S : System) (adv₁ adv₂ : Adversary) (n : Nat)
    (hdet : ∀ s, detB S.P s = true)
    (hδ : delta S (exec S adv₁ n S.P.start []).2 = delta S (exec S adv₂ n S.P.start []).2) :
    ∀ r, S.inA r = false →
      view r (exec S adv₁ n S.P.start []).2 = view r (exec S adv₂ n S.P.start []).2 :=
  noninterference S adv₁ adv₂ n (fun s => detB_sound S.P s (hdet s)) hδ

/-! ### T9b — the attacker's decision budget (quantitative) -/

/-- `⌈log₂ k⌉` -/
def clog2 (k : Nat) : Nat := if k ≤ 1 then 0 else Nat.log2 (k - 1) + 1

/-- Bits the attacker can choose when transition `t` is taken in state `s`: which of the `k` A-sent
transitions to take *or whether to stop* (`k + 1` options, ≤ `clog2 (k+1)` bits), plus, when talking to a
clean role, the payload (≤ `capBits` bits). Clean transitions cost nothing. -/
def cost (S : System) (s : Nat) (t : Trans) : Nat :=
  if S.inA t.src then clog2 (((S.P.out s).filter (fun t' => S.inA t'.src)).length + 1)
                      + (if S.inA t.dst then 0 else t.ty.capBits.getD 0)
  else 0

/-- The ranking pays for every attacker choice, and A→clean messages have finite capacity. -/
def influenceInv (S : System) (ρ : Ranking) (s : Nat) : Bool :=
  (S.P.out s).all (fun t => decide (rk ρ t.next + cost S s t ≤ rk ρ s)) &&
  (S.P.out s).all (fun t => !(S.inA t.src && !S.inA t.dst) || t.ty.capBits.isSome)

def checkInfluence (S : System) (ρ : Ranking) (V : List Nat) : Bool :=
  certifies (cfgTS S.P) (influenceInv S ρ) V

/-- The total attacker choice bits along a protocol run (using the transitions the gate matched). -/
def runCost (S : System) : Nat → List Event → Nat
  | _, [] => 0
  | s, e :: es => match (S.P.out s).find? (fun t => t.matches e) with
    | some t => cost S s t + runCost S t.next es
    | none => 0

theorem influence_aux (S : System) (ρ : Ranking) (V : List Nat) (hc : checkInfluence S ρ V = true) :
    ∀ (t : List Event) (s s' : Nat), Reach (cfgTS S.P) s → run S.P s t = some s' →
      runCost S s t ≤ rk ρ s
  | [], _, _, _, _ => by simp [runCost]
  | e :: es, s, s', hr, h => by
    unfold run step at h
    unfold runCost
    cases hf : (S.P.out s).find? (fun t => t.matches e) with
    | none => simp [hf] at h
    | some tr =>
      simp only [hf, Option.map_some] at h
      have hmem := List.mem_of_find?_eq_some hf
      have hr' : Reach (cfgTS S.P) tr.next := Reach.step hr (by simp [cfgTS]; exact ⟨tr, hmem, rfl⟩)
      have ih := influence_aux S ρ V hc es tr.next s' hr' h
      have hinv := certifies_sound hc hr
      simp only [influenceInv, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hinv
      have := hinv.1 tr hmem
      simp only; omega

/-- **Theorem T9b (Attacker decision budget).** If `checkInfluence S ρ V` succeeds, then along every
protocol run the attacker makes choices worth at most `B = rk ρ start` bits.

Information-theoretic reading. At each attacker turn the attacker picks one of the `k_s` A-sent
transitions or stops (≤ `clog2 (k_s + 1)` bits — stopping is observable, so it must be paid for), and,
when talking to a clean role, a payload of a finite type (≤ `capBits` bits; free text is excluded by the
second conjunct of `influenceInv`). Clean moves are determined by the clean roles' views. By T9 clean
behaviour is a function of `δ`, and `δ` is determined by this sequence of choices; summing over the run,
`δ` ranges over at most `2^B` values, i.e. clean behaviour depends on at most `B` attacker-chosen bits.
(The counting step is not mechanised; it relies on `capBits` being a sound capacity bound, which holds for
scalar types and enums but not for record values whose *field order* is attacker-chosen, unless the
transport canonicalises records.) -/
theorem influence_bound (S : System) (ρ : Ranking) (V : List Nat) (hc : checkInfluence S ρ V = true)
    (t : List Event) (s' : Nat) (h : run S.P S.P.start t = some s') :
    runCost S S.P.start t ≤ rk ρ S.P.start :=
  influence_aux S ρ V hc t S.P.start s' (.init (by simp [cfgTS])) h

/-- T9b for the deployed gate: whatever the agents submit, the delivered trace carries at most
`rk ρ start` attacker-chosen bits. -/
theorem influence_monitor (S : System) (ρ : Ranking) (V : List Nat) (hc : checkInfluence S ρ V = true)
    (cfg : Config) (as : List Input) :
    runCost S S.P.start (delivered (monRun cfg S.P (MState.init S.P) as).2) ≤ rk ρ S.P.start :=
  influence_bound S ρ V hc _ _ (enforcement cfg S.P (MState.init S.P) as)

/-- T9b for the system model of T9: every execution carries at most `rk ρ start` attacker-chosen bits. -/
theorem influence_exec (S : System) (ρ : Ranking) (V : List Nat) (hc : checkInfluence S ρ V = true)
    (adv : Adversary) (n : Nat) :
    runCost S S.P.start (exec S adv n S.P.start []).2 ≤ rk ρ S.P.start :=
  influence_bound S ρ V hc _ _ (exec_run S adv n S.P.start S.P.start [] (by simp [run]))

end SwarmGate
