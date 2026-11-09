/-
  SwarmGate.Admission — untrusted protocol authors (Theorem T8).

  In v1 the protocol was trusted. Here it need not be: a protocol may be written by an LLM for the task at
  hand. The deployer fixes a *meta-policy* — the catalog of message kinds the tools and agents understand,
  the IFC policy, required temporal properties and a length bound — and a protocol is used only if the
  verified admission check accepts it. Then every enforced run of that protocol, against every adversary,
  stays inside the catalog (capability confinement), satisfies the IFC policy, every required property and
  the length bound. The trusted computing base is the meta-policy plus this checker; the protocol author,
  the agents and the certificate generator are all untrusted.
-/
import SwarmGate.Projection

namespace SwarmGate

/-- A message kind the deployer allows: `src → dst : label(ty){pred}`. -/
structure CatEntry where
  src : Nat
  dst : Nat
  label : String
  ty : Ty
  pred : Pred
  deriving Repr, Inhabited, DecidableEq

def CatEntry.matches (c : CatEntry) (e : Event) : Bool :=
  c.src == e.src && c.dst == e.dst && c.label == e.label && hasTy c.ty e.payload && c.pred.eval e.payload

/-- Syntactic refinement implication `p ⇒ q` (a protocol may only *strengthen* catalog refinements). -/
def predImplies (p q : Pred) : Bool :=
  decide (p = q) || decide (q = .tt) ||
    (match p with
     | .and a b => decide (a = q) || decide (b = q)
     | _ => false)

theorem predImplies_sound {p q : Pred} (h : predImplies p q = true) (v : Value)
    (hp : p.eval v = true) : q.eval v = true := by
  unfold predImplies at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (rfl | rfl) | h
  · exact hp
  · simp [Pred.eval]
  · cases p with
    | and a b =>
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [Pred.eval, Bool.and_eq_true] at hp
      rcases h with rfl | rfl
      · exact hp.1
      · exact hp.2
    | _ => simp at h

/-- Transition `t` is an instance of catalog entry `c`. -/
def coveredBy (t : Trans) (c : CatEntry) : Bool :=
  decide (c.src = t.src) && decide (c.dst = t.dst) && decide (c.label = t.label) &&
    decide (c.ty = t.ty) && predImplies t.pred c.pred

def catInv (cat : List CatEntry) (P : Protocol) (s : Nat) : Bool :=
  (P.out s).all (fun t => cat.any (coveredBy t))

def checkCatalog (cat : List CatEntry) (P : Protocol) (V : List Nat) : Bool :=
  certifies (cfgTS P) (catInv cat P) V

theorem coveredBy_matches {t : Trans} {c : CatEntry} {e : Event} (hc : coveredBy t c = true)
    (hm : t.matches e = true) : c.matches e = true := by
  simp only [coveredBy, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  simp only [Trans.matches, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨⟨⟨m1, m2⟩, m3⟩, m4⟩, m5⟩ := hm
  simp only [CatEntry.matches, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨by rw [h1, m1], by rw [h2, m2]⟩, by rw [h3, m3]⟩, by rw [h4]; exact m4⟩, ?_⟩
  exact predImplies_sound h5 _ m5

/-- **Capability confinement** for any protocol trace. -/
theorem catalog_of_pref (cat : List CatEntry) (P : Protocol) (V : List Nat)
    (hc : checkCatalog cat P V = true) (D : List Event) (hD : Pref P D) :
    ∀ e ∈ D, ∃ c ∈ cat, c.matches e = true := by
  intro e he
  obtain ⟨t, u, rfl⟩ := List.append_of_mem he
  obtain ⟨s₁, tr, hs₁, htr, hm, _, _, _⟩ :=
    prefix_decomp P () (fun _ _ => ()) t e u hD
  have hr : Reach (cfgTS P) s₁ := run_reach P P.start t s₁ hs₁ (.init (by simp [cfgTS]))
  have hinv := certifies_sound hc hr
  simp only [catInv, List.all_eq_true, List.any_eq_true] at hinv
  obtain ⟨c, hcm, hcov⟩ := hinv tr htr
  exact ⟨c, hcm, coveredBy_matches hcov hm⟩

/-! ### Meta-policies and admission -/

structure MetaPolicy where
  nRoles : Nat
  catalog : List CatEntry
  ifc : IFCPolicy
  props : List F
  maxLen : Option Nat
  deriving Repr, Inhabited

/-- Certificates produced by untrusted search. -/
structure AdmitCert where
  V : List Nat
  taintV : List (Nat × Nat)
  propCerts : List (F × List (Nat × MonSt))
  ρ : Ranking
  deriving Repr, Inhabited

def boundOk (Pi : MetaPolicy) (P : Protocol) (c : AdmitCert) : Bool :=
  match Pi.maxLen with
  | none => true
  | some L => checkBounded P c.ρ c.V && decide (rk c.ρ P.start ≤ L)

/-- Determinism (W1) on every state of the protocol. -/
def detAll (P : Protocol) : Bool := (List.range P.trans.size).all (fun s => detB P s)

theorem detAll_sound (P : Protocol) (h : detAll P = true) : ∀ s, P.detAt s := by
  intro s
  by_cases hs : s < P.trans.size
  · simp only [detAll, List.all_eq_true, List.mem_range] at h
    exact detB_sound P s (h s hs)
  · intro t₁ h₁
    have hn : P.trans[s]? = none := by simp; omega
    simp [Protocol.out, hn] at h₁

/-- **The admission check.** -/
def admit (Pi : MetaPolicy) (P : Protocol) (c : AdmitCert) : Bool :=
  P.nRoles == Pi.nRoles && checkCatalog Pi.catalog P c.V && checkIFC P Pi.ifc c.taintV &&
    Pi.props.all (fun φ => c.propCerts.any (fun pw => decide (pw.1 = φ) && checkProp P pw.1 pw.2)) &&
    boundOk Pi P c && detAll P

/-- **Theorem T8 (Admission).** If an (arbitrary, e.g. LLM-written) protocol is admitted against the
deployer's meta-policy, then on every run of the gate — whatever the agents submit —
(1) every delivered message is an instance of a catalog entry (capability confinement),
(2) no tainted role performs a sensitive action (IFC),
(3) every required temporal property holds after every delivered event, and
(4) the session delivers at most `maxLen` messages. -/
theorem admitted_secure (Pi : MetaPolicy) (P : Protocol) (c : AdmitCert) (hA : admit Pi P c = true)
    (cfg : Config) (as : List Input) :
    let D := delivered (monRun cfg P (MState.init P) as).2
    (∀ e ∈ D, ∃ k ∈ Pi.catalog, k.matches e = true) ∧
    (∀ t e u, D = t ++ e :: u → Pi.ifc.isSensitive e.abs = true →
        (taintOf P Pi.ifc t).testBit e.src = false) ∧
    (∀ φ ∈ Pi.props, ∀ t e u, D = t ++ e :: u → satT φ ((t ++ [e]).map Event.abs) = true) ∧
    (∀ L, Pi.maxLen = some L → D.length ≤ L) := by
  intro D
  have hpref : Pref P D := enforcement_pref cfg P as
  simp only [admit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq] at hA
  obtain ⟨⟨⟨⟨⟨_, hcat⟩, hifc⟩, hprops⟩, hbound⟩, _⟩ := hA
  refine ⟨catalog_of_pref _ P c.V hcat D hpref, ifc_of_pref P Pi.ifc c.taintV hifc D hpref, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨pw, _, heq, hck⟩ := hprops φ hφ
    rw [heq] at hck
    exact property_of_pref P φ pw.2 hck D hpref
  · intro L hL
    simp only [boundOk, hL, Bool.and_eq_true, decide_eq_true_eq] at hbound
    exact Nat.le_trans (bounded_length P c.ρ c.V hbound.1 cfg as) hbound.2

/-- Admitted protocols are deterministic (W1), so Theorem T9 applies to them without further hypotheses. -/
theorem admitted_deterministic (Pi : MetaPolicy) (P : Protocol) (c : AdmitCert)
    (hA : admit Pi P c = true) : ∀ s, P.detAt s := by
  simp only [admit, Bool.and_eq_true] at hA
  exact detAll_sound P hA.2

end SwarmGate
