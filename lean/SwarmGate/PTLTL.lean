/-
  SwarmGate.PTLTL — past-time temporal properties of protocols and their transfer to every enforced run
  (THEORY.md §5.2, Theorem T4).
-/
import SwarmGate.Observe

namespace SwarmGate

/-- Past-time LTL over abstract events. `atom s d l` matches events with the given (optional) fields. -/
inductive F where
  | tt
  | atom (src : Option Nat) (dst : Option Nat) (label : Option String)
  | not (φ : F)
  | and (φ ψ : F)
  | or (φ ψ : F)
  | prev (φ : F)
  | since (φ ψ : F)
  deriving DecidableEq, Repr, Inhabited, Hashable

def F.ff : F := .not .tt
def F.once (φ : F) : F := .since .tt φ
def F.hist (φ : F) : F := .not (.once (.not φ))
def F.imp (φ ψ : F) : F := .or (.not φ) ψ

def atomHolds (s d : Option Nat) (l : Option String) (e : AEv) : Bool :=
  s.all (· == e.src) && d.all (· == e.dst) && l.all (· == e.label)

/-- Semantics at the latest event `e` of a non-empty trace whose earlier events are `past` (latest first). -/
def sat : F → AEv → List AEv → Bool
  | .tt, _, _ => true
  | .atom s d l, e, _ => atomHolds s d l e
  | .not φ, e, p => !sat φ e p
  | .and φ ψ, e, p => sat φ e p && sat ψ e p
  | .or φ ψ, e, p => sat φ e p || sat ψ e p
  | .prev _, _, [] => false
  | .prev φ, _, e' :: p => sat φ e' p
  | .since _ ψ, e, [] => sat ψ e []
  | .since φ ψ, e, e' :: p => sat ψ e (e' :: p) || (sat φ e (e' :: p) && sat (.since φ ψ) e' p)
termination_by f _ p => (p.length, sizeOf f)

/-- `ψ` holds at the end of the chronological trace `t` (vacuously true on the empty trace). -/
def satT (φ : F) (t : List AEv) : Bool :=
  match t.reverse with
  | [] => true
  | e :: p => sat φ e p

/-! ### Incremental monitor (one bit per subformula, Havelund–Roşu) -/

def subs : F → List F
  | .tt => [.tt]
  | .atom s d l => [.atom s d l]
  | .not φ => .not φ :: subs φ
  | .and φ ψ => .and φ ψ :: (subs φ ++ subs ψ)
  | .or φ ψ => .or φ ψ :: (subs φ ++ subs ψ)
  | .prev φ => .prev φ :: subs φ
  | .since φ ψ => .since φ ψ :: (subs φ ++ subs ψ)

theorem mem_subs_self (φ : F) : φ ∈ subs φ := by cases φ <;> simp [subs]

theorem subs_trans : ∀ (φ χ ψ : F), χ ∈ subs φ → ψ ∈ subs χ → ψ ∈ subs φ := by
  intro φ
  induction φ with
  | tt => intro χ ψ h1 h2; simp [subs] at h1; subst h1; exact h2
  | atom s d l => intro χ ψ h1 h2; simp [subs] at h1; subst h1; exact h2
  | not a iha =>
    intro χ ψ h1 h2; simp [subs] at h1
    rcases h1 with rfl | h1
    · exact h2
    · simp [subs]; exact Or.inr (iha χ ψ h1 h2)
  | prev a iha =>
    intro χ ψ h1 h2; simp [subs] at h1
    rcases h1 with rfl | h1
    · exact h2
    · simp [subs]; exact Or.inr (iha χ ψ h1 h2)
  | and a b iha ihb =>
    intro χ ψ h1 h2; simp [subs] at h1
    rcases h1 with rfl | h1 | h1
    · exact h2
    · simp [subs]; exact Or.inr (Or.inl (iha χ ψ h1 h2))
    · simp [subs]; exact Or.inr (Or.inr (ihb χ ψ h1 h2))
  | or a b iha ihb =>
    intro χ ψ h1 h2; simp [subs] at h1
    rcases h1 with rfl | h1 | h1
    · exact h2
    · simp [subs]; exact Or.inr (Or.inl (iha χ ψ h1 h2))
    · simp [subs]; exact Or.inr (Or.inr (ihb χ ψ h1 h2))
  | since a b iha ihb =>
    intro χ ψ h1 h2; simp [subs] at h1
    rcases h1 with rfl | h1 | h1
    · exact h2
    · simp [subs]; exact Or.inr (Or.inl (iha χ ψ h1 h2))
    · simp [subs]; exact Or.inr (Or.inr (ihb χ ψ h1 h2))

abbrev MonSt := Option (List (F × Bool))

def lk (L : List (F × Bool)) (χ : F) : Bool := (L.lookup χ).getD false

/-- Value of a subformula at the new event, given the stored values at the previous position. -/
def now : F → AEv → MonSt → Bool
  | .tt, _, _ => true
  | .atom s d l, e, _ => atomHolds s d l e
  | .not φ, e, pv => !now φ e pv
  | .and φ ψ, e, pv => now φ e pv && now ψ e pv
  | .or φ ψ, e, pv => now φ e pv || now ψ e pv
  | .prev _, _, none => false
  | .prev φ, _, some L => lk L φ
  | .since _ ψ, e, none => now ψ e none
  | .since φ ψ, e, some L => now ψ e (some L) || (now φ e (some L) && lk L (.since φ ψ))

def updM (root : F) (pv : MonSt) (e : AEv) : MonSt := some ((subs root).map (fun χ => (χ, now χ e pv)))

/-- The monitor state correctly summarises the past. -/
def Good (root : F) : MonSt → List AEv → Prop
  | none, [] => True
  | some L, e' :: p' => ∀ χ ∈ subs root, lk L χ = sat χ e' p'
  | _, _ => False

theorem lookup_map_self (L : List F) (g : F → Bool) (χ : F) (h : χ ∈ L) :
    (L.map (fun c => (c, g c))).lookup χ = some (g χ) := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    simp only [List.map_cons, List.lookup]
    by_cases hc : χ = a
    · subst hc; simp
    · have : (χ == a) = false := by simpa using hc
      simp only [this]
      exact ih (by simp at h; rcases h with h | h; exact absurd h hc; exact h)

/-- Lemma 5.2 (incremental monitor correctness). -/
theorem now_correct (root : F) (pv : MonSt) (past : List AEv) (e : AEv) (hg : Good root pv past) :
    ∀ χ, χ ∈ subs root → now χ e pv = sat χ e past := by
  intro χ
  induction χ with
  | tt => intro _; cases pv <;> simp [now, sat]
  | atom s d l => intro _; cases pv <;> simp [now, sat]
  | not a ih =>
    intro h
    have ha := ih (subs_trans _ _ _ h (by simp [subs, mem_subs_self]))
    cases pv <;> simp [now, sat, ha] <;> simp [now] at ha <;> simp [ha]
  | and a b iha ihb =>
    intro h
    have ha := iha (subs_trans _ _ _ h (by simp [subs, mem_subs_self]))
    have hb := ihb (subs_trans _ _ _ h (by simp [subs, mem_subs_self]))
    cases pv <;> simp only [now, sat] at ha hb ⊢ <;> rw [ha, hb]
  | or a b iha ihb =>
    intro h
    have ha := iha (subs_trans _ _ _ h (by simp [subs, mem_subs_self]))
    have hb := ihb (subs_trans _ _ _ h (by simp [subs, mem_subs_self]))
    cases pv <;> simp only [now, sat] at ha hb ⊢ <;> rw [ha, hb]
  | prev a _ =>
    intro h
    have hsub : a ∈ subs root := subs_trans _ _ _ h (by simp [subs, mem_subs_self])
    cases pv with
    | none => cases past with
      | nil => simp [now, sat]
      | cons _ _ => simp [Good] at hg
    | some L => cases past with
      | nil => simp [Good] at hg
      | cons e' p' => simp only [now, sat]; exact hg a hsub
  | since a b iha ihb =>
    intro h
    have ha := iha (subs_trans _ _ _ h (by simp [subs, mem_subs_self]))
    have hb := ihb (subs_trans _ _ _ h (by simp [subs, mem_subs_self]))
    cases pv with
    | none => cases past with
      | nil => simp only [now, sat]; exact hb
      | cons _ _ => simp [Good] at hg
    | some L => cases past with
      | nil => simp [Good] at hg
      | cons e' p' =>
        simp only [now, sat]
        rw [ha, hb, hg (.since a b) h]

theorem updM_good (root : F) (pv : MonSt) (past : List AEv) (e : AEv) (hg : Good root pv past) :
    Good root (updM root pv e) (e :: past) := by
  intro χ hχ
  simp only [lk]
  rw [lookup_map_self _ _ _ hχ]
  simp only [Option.getD_some]
  exact now_correct root pv past e hg χ hχ

/-! ### The product with the protocol and the transfer theorem -/

def propUpd (root : F) (x : MonSt) (t : Trans) : MonSt := updM root x t.abs

def propTS (P : Protocol) (root : F) : TS (Nat × MonSt) := obsTS P none (propUpd root)

def propInv (root : F) (c : Nat × MonSt) : Bool :=
  match c.2 with
  | none => true
  | some L => lk L root

/-- The verified property checker: validates a candidate certificate. -/
def checkProp (P : Protocol) (root : F) (V : List (Nat × MonSt)) : Bool :=
  certifies (propTS P root) (propInv root) V

theorem obsRun_good (P : Protocol) (root : F) : ∀ (s : Nat) (x : MonSt) (past : List AEv) (t : List Event),
    (run P s t).isSome → Good root x past →
    Good root (obsRun P (propUpd root) s x t) ((t.map Event.abs).reverse ++ past)
  | s, x, past, [], _, hg => by simpa [obsRun] using hg
  | s, x, past, e :: es, h, hg => by
    unfold run step at h
    unfold obsRun
    cases hf : (P.out s).find? (fun t => t.matches e) with
    | none => simp [hf] at h
    | some tr =>
      simp [hf] at h
      have hm : tr.matches e = true := by simpa using List.find?_some hf
      have habs := Trans.abs_of_matches hm
      have := obsRun_good P root tr.next (propUpd root x tr) (e.abs :: past) es
        (by cases hr : run P tr.next es <;> simp_all)
        (by simp only [propUpd]; rw [habs]; exact updM_good root x past e.abs hg)
      simpa using this

/-- Property transfer for any protocol trace (used by both the central gate and decentralised sidecars). -/
theorem property_of_pref (P : Protocol) (root : F) (V : List (Nat × MonSt))
    (hc : checkProp P root V = true) (D : List Event) (hD0 : Pref P D) :
    ∀ t e u, D = t ++ e :: u → satT root ((t ++ [e]).map Event.abs) = true := by
  intro t e u hD
  have hpref := hD0
  rw [hD] at hpref
  obtain ⟨s₁, tr, hs₁, htr, hm, hf, hreach, hobs⟩ :=
    prefix_decomp P none (propUpd root) t e u hpref
  -- the configuration after `t ++ [e]` is reachable
  have hreach' : Reach (propTS P root) (tr.next, obsRun P (propUpd root) P.start none (t ++ [e])) := by
    rw [hobs]
    exact Reach.step hreach (by simp [propTS, obsTS]; exact ⟨tr, htr, rfl, rfl⟩)
  have hinv := certifies_sound hc hreach'
  -- and the observer state is a correct summary of the (non-empty) trace
  have hg := obsRun_good P root P.start none [] (t ++ [e])
    (by have := run_prefix P P.start (t ++ [e]) u; simp at this; exact this hpref) (by simp [Good])
  simp only [List.append_nil] at hg
  simp only [satT]
  revert hinv hg
  generalize obsRun P (propUpd root) P.start none (t ++ [e]) = x
  intro hinv hg
  simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append] at hg ⊢
  cases x with
  | none => simp [Good] at hg
  | some L =>
    simp only [Good] at hg
    rw [← hg root (mem_subs_self root)]
    simpa [propInv] using hinv

/-- **Theorem T4 (Property transfer).** If the checker accepts a certificate for `ψ`, then on every run
of the gate — whatever the agents submit — `ψ` holds after every delivered event. -/
theorem property_transfer (P : Protocol) (root : F) (V : List (Nat × MonSt))
    (hc : checkProp P root V = true) (cfg : Config) (as : List Input) :
    ∀ t e u, delivered (monRun cfg P (MState.init P) as).2 = t ++ e :: u →
      satT root ((t ++ [e]).map Event.abs) = true :=
  property_of_pref P root V hc _ (enforcement_pref cfg P as)

end SwarmGate
