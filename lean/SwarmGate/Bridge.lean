/-
  SwarmGate.Bridge — connecting the noninterference model (T9) to the deployed gate and to admission.
-/
import SwarmGate.Admission
import SwarmGate.Noninterference

namespace SwarmGate

/-- Every run of the T9 system model is a run the gate actually delivers: submitting the model's events as
authentic attempts makes the gate deliver exactly that trace (budget permitting). So T9 speaks about traces
the deployed monitor produces, not about an idealised execution. -/
theorem exec_deliverable (S : System) (adv : Adversary) (n : Nat) (cfg : Config)
    (hb : (exec S adv n S.P.start []).2.length ≤ cfg.budget) :
    delivered (monRun cfg S.P (MState.init S.P) (conformantInputs (exec S adv n S.P.start []).2)).2
      = (exec S adv n S.P.start []).2 := by
  apply transparency_init cfg S.P _ _ hb
  unfold Pref
  have h := exec_run S adv n S.P.start S.P.start [] (by simp [run])
  rw [h]; rfl

/-- **T9 for admitted protocols.** For every protocol admitted against any meta-policy — in particular every
LLM-written protocol we deploy — clean agents' views depend on the adversary only through δ. -/
theorem admitted_noninterference (Pi : MetaPolicy) (c : AdmitCert) (S : System)
    (hA : admit Pi S.P c = true) (adv₁ adv₂ : Adversary) (n : Nat)
    (hδ : delta S (exec S adv₁ n S.P.start []).2 = delta S (exec S adv₂ n S.P.start []).2) :
    ∀ r, S.inA r = false →
      view r (exec S adv₁ n S.P.start []).2 = view r (exec S adv₂ n S.P.start []).2 :=
  noninterference S adv₁ adv₂ n (admitted_deterministic Pi S.P c hA) hδ

end SwarmGate
