import IxCCGrounding.Direct.Check
import IxCCGrounding.Subst

/-!
# Profiles and equality up to what the denotation does not read (`IxCCGrounding.Direct.Eq`)

**Part A, profiles.** A binder datum reads an assignment only through which of its parameters are
zero, so its value at a profile is its value at every assignment that profile stands for
(`holds_of_pwAt`); SrcEval's levels give the kernel assignment their own profile
(`profAt_of_lvAt`); a decision required at every profile of a set holds at any assignment one of
them stands for (`AtProf`).

**Part C, `eqUpTo` is sound** in every environment, with no law: what it equates denote alike by
`Denotes`'s rules (levels through `Level.eval`, which `Level.simplify` and the max-plus form
preserve; a binder's datum through its regime; a literal through its constructor form).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

/-! ## Part A. Profiles -/

/-- A datum with its parameters among `lps` reads an assignment only through which of them are
zero. -/
theorem holds_congr_zero {lps : List Nat} {pw : PropWhen} (hd : pw.paramsDefined lps = true)
    {φ ψ : LevelParam → Nat} (h : ∀ p ∈ lps, (φ p = 0 ↔ ψ p = 0)) :
    pw.holds φ = pw.holds ψ := by
  cases pw with
  | never => simp
  | ifAllZero ps =>
    simp only [PropWhen.paramsDefined_ifAllZero, List.all_eq_true] at hd
    simp only [PropWhen.holds_ifAllZero]
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, beq_iff_eq]
    have hm : ∀ p ∈ ps, p ∈ lps := fun p hp => by simpa [List.contains_iff_mem] using hd p hp
    exact ⟨fun H p hp => (h p (hm p hp)).mp (H p hp), fun H p hp => (h p (hm p hp)).mpr (H p hp)⟩

/-- `φ` and the profile's own assignment are zero at the same parameters. -/
theorem φOf_zero {φ : LevelParam → Nat} :
    ∀ {lps : List Nat} {prof : IxCC.Src.Profile}, ProfAt φ lps prof →
      ∀ p ∈ lps, (φ p = 0 ↔ φOf lps prof p = 0)
  | [], _, _, p, hp => by simp at hp
  | q :: qs, prof, hφ, p, hp => by
    simp only [φOf]
    by_cases hq : q = p
    · subst hq
      have h0 := hφ 0 q rfl
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [h0]
      cases prof with
      | nil => simp
      | cons b bs => cases b <;> simp
    · have hne : (q == p) = false := by simpa using hq
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have hp' : p ∈ qs := by
        rcases List.mem_cons.mp hp with h | h
        · exact absurd h.symm hq
        · exact h
      refine φOf_zero (fun i r hr => ?_) p hp'
      have := hφ (i + 1) r (by simpa using hr)
      cases prof with
      | nil => simpa using this
      | cons b bs => simpa using this

/-- **A datum at the profile is the datum at `φ`.** -/
theorem holds_of_pwAt {φ : LevelParam → Nat} {lps : List Nat} {prof : IxCC.Src.Profile}
    {pw : PropWhen} {b : Bool} (hφ : ProfAt φ lps prof) (h : pwAt lps prof pw = some b) :
    pw.holds φ = b := by
  unfold pwAt at h
  split at h
  · rename_i hd
    cases h
    exact holds_congr_zero hd (φOf_zero hφ)
  · cases h

/-- **SrcEval's levels give the kernel assignment their profile.** -/
theorem profAt_of_lvAt {φ : LevelParam → Nat} {lps : List Nat} {ls : IxCC.Src.Levels}
    (hlv : LvAt φ lps ls) (hlen : ls.length = lps.length) :
    ProfAt φ lps (IxCC.Src.profileOf ls) := by
  intro i p hp
  have hi : i < ls.length := by
    rw [hlen]; exact (List.getElem?_eq_some_iff.mp hp).1
  rw [hlv i p hp]
  simp [IxCC.Src.profileOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- `φ` is one of the assignments the profiles of `x` stand for. -/
def AtProf (φ : LevelParam → Nat) (x : DCtx) : Prop := ∃ prof ∈ x.profs, ProfAt φ x.lps prof

theorem pwFalse_holds {φ : LevelParam → Nat} {x : DCtx} (hφ : AtProf φ x) {pw : PropWhen}
    (h : x.pwFalse pw = true) : pw.holds φ = false := by
  obtain ⟨prof, hm, hp⟩ := hφ
  have := List.all_eq_true.mp h prof hm
  exact holds_of_pwAt hp (by simpa using this)

theorem regime_of_pwFalse {φ : LevelParam → Nat} {x : DCtx} (hφ : AtProf φ x) {pw : PropWhen}
    (h : x.pwFalse pw = true) : regime φ pw ≠ 0 := by
  simp [regime, pwFalse_holds hφ h]

theorem pwEq_holds {φ : LevelParam → Nat} {x : DCtx} (hφ : AtProf φ x) {p q : PropWhen}
    (h : x.pwEq p q = true) : p.holds φ = q.holds φ := by
  unfold DCtx.pwEq at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [beq_iff_eq.mp h]
  · obtain ⟨prof, hm, hp⟩ := hφ
    have := List.all_eq_true.mp h prof hm
    split at this
    · rename_i a b ha hb
      rw [holds_of_pwAt hp ha, holds_of_pwAt hp hb, beq_iff_eq.mp this]
    · cases this

theorem regime_of_pwEq {φ : LevelParam → Nat} {x : DCtx} (hφ : AtProf φ x) {p q : PropWhen}
    (h : x.pwEq p q = true) : regime φ p = regime φ q := by
  simp [regime, pwEq_holds hφ h]

theorem zeroAt_holds {φ : LevelParam → Nat} {x : DCtx} (hφ : AtProf φ x) {pw : PropWhen}
    {v : Level} (h : x.zeroAt pw v = true) : pw.holds φ = (Level.eval φ v == 0) := by
  obtain ⟨prof, hm, hp⟩ := hφ
  have := List.all_eq_true.mp h prof hm
  split at this
  · rename_i a b ha hb
    rw [holds_of_pwAt hp ha, beq_iff_eq.mp this, ← holds_of_pwAt hp hb, holds_zeronessOf]
  · cases this

/-! ## Levels -/

/-- The value of a max-plus form at `φ`. -/
def mpEval (φ : LevelParam → Nat) (r : Nat × List (Nat × Nat)) : Nat :=
  r.2.foldr (fun pk m => max (φ pk.1 + pk.2) m) r.1

theorem mpEval_init (φ : LevelParam → Nat) : ∀ (c : Nat) (ts : List (Nat × Nat)),
    mpEval φ (c, ts) = max c (mpEval φ (0, ts))
  | c, [] => by simp [mpEval]
  | c, (p, k) :: ts => by
    have := mpEval_init φ c ts
    simp only [mpEval, List.foldr_cons] at this ⊢
    omega

theorem mpEval_succ (φ : LevelParam → Nat) : ∀ (c : Nat) (ts : List (Nat × Nat)),
    mpEval φ (c + 1, ts.map fun pk => (pk.1, pk.2 + 1)) = mpEval φ (c, ts) + 1
  | c, [] => by simp [mpEval]
  | c, (p, k) :: ts => by
    have := mpEval_succ φ c ts
    simp only [mpEval, List.map_cons, List.foldr_cons] at this ⊢
    omega

theorem mpEval_append (φ : LevelParam → Nat) (c1 c2 : Nat) : ∀ (t1 t2 : List (Nat × Nat)),
    mpEval φ (max c1 c2, t1 ++ t2) = max (mpEval φ (c1, t1)) (mpEval φ (c2, t2))
  | [], t2 => by
    have h1 := mpEval_init φ (max c1 c2) t2
    have h2 := mpEval_init φ c2 t2
    simp only [List.nil_append, mpEval, List.foldr_nil] at h1 h2 ⊢
    omega
  | (p, k) :: t1, t2 => by
    have := mpEval_append φ c1 c2 t1 t2
    simp only [mpEval, List.cons_append, List.foldr_cons] at this ⊢
    omega

/-- A max-plus form computes its level's value. -/
theorem maxPlus_eval (φ : LevelParam → Nat) :
    ∀ (l : Level) (r : Nat × List (Nat × Nat)), maxPlus l = some r → Level.eval φ l = mpEval φ r
  | .zero, r, h => by simp [maxPlus] at h; subst h; rfl
  | .param p, r, h => by simp [maxPlus] at h; subst h; simp [mpEval, Level.eval]
  | .succ l, r, h => by
    simp only [maxPlus, Option.map_eq_some_iff] at h
    obtain ⟨⟨c, ts⟩, hl, rfl⟩ := h
    rw [Level.eval, maxPlus_eval φ l _ hl, mpEval_succ]
  | .max a b, r, h => by
    simp only [maxPlus] at h
    split at h
    · rename_i c1 t1 c2 t2 ha hb
      cases h
      rw [Level.eval, maxPlus_eval φ a _ ha, maxPlus_eval φ b _ hb, mpEval_append]
    · cases h
  | .imax _ _, r, h => by simp [maxPlus] at h

theorem mpEval_ge_term (φ : LevelParam → Nat) : ∀ (d : Nat) (us : List (Nat × Nat)) (q l : Nat),
    (q, l) ∈ us → φ q + l ≤ mpEval φ (d, us)
  | _, [], _, _, h => by simp at h
  | d, (q', l') :: us, q, l, h => by
    have ih := mpEval_ge_term φ d us q l
    simp only [mpEval, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with h | h
    · cases h; omega
    · have := ih h; omega

theorem mpEval_ge_offsets (φ : LevelParam → Nat) : ∀ (d : Nat) (us : List (Nat × Nat)),
    us.foldr (fun pk m => max pk.2 m) d ≤ mpEval φ (d, us)
  | _, [] => by simp [mpEval]
  | d, (q, l) :: us => by
    have := mpEval_ge_offsets φ d us
    simp only [mpEval, List.foldr_cons] at this ⊢
    omega

/-- **One max-plus form at most another, decided, is so at every assignment.** -/
theorem maxPlusLe_sound (φ : LevelParam → Nat) {A B : Nat × List (Nat × Nat)}
    (h : maxPlusLe A B = true) : mpEval φ A ≤ mpEval φ B := by
  obtain ⟨c, ts⟩ := A
  obtain ⟨d, us⟩ := B
  simp only [maxPlusLe, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    beq_iff_eq] at h
  obtain ⟨hc, hts⟩ := h
  have hcE : c ≤ mpEval φ (d, us) := Nat.le_trans hc (mpEval_ge_offsets φ d us)
  have key : ∀ ts' : List (Nat × Nat), (∀ x ∈ ts', ∃ y ∈ us, y.1 = x.1 ∧ x.2 ≤ y.2) →
      mpEval φ (c, ts') ≤ mpEval φ (d, us) := by
    intro ts' h'
    induction ts' with
    | nil => simpa [mpEval] using hcE
    | cons x ts' ih =>
      obtain ⟨⟨q, l⟩, hy, hq, hk⟩ := h' x (List.mem_cons_self ..)
      have h1 := mpEval_ge_term φ d us q l hy
      have h2 := ih fun z hz => h' z (List.mem_cons_of_mem _ hz)
      simp only [mpEval, List.foldr_cons] at h1 h2 ⊢
      simp only at hq hk
      subst hq
      omega
  exact key ts fun x hx => by
    obtain ⟨y, hy, h1, h2⟩ := hts x hx
    exact ⟨y, hy, h1, h2⟩

/-- **`imax a a` collapsed to `a` keeps the value**: `Level.eval`'s `imax` is `0` at a zero right
side and the maximum otherwise, so at equal sides it is the side. -/
theorem eval_imaxCollapse (φ : LevelParam → Nat) :
    ∀ l : Level, Level.eval φ (imaxCollapse l) = Level.eval φ l
  | .zero => rfl
  | .param _ => rfl
  | .succ l => by simp only [imaxCollapse, Level.eval, eval_imaxCollapse φ l]
  | .max a b => by simp only [imaxCollapse, Level.eval, eval_imaxCollapse φ a, eval_imaxCollapse φ b]
  | .imax a b => by
    have ha := eval_imaxCollapse φ a
    have hb := eval_imaxCollapse φ b
    unfold imaxCollapse
    split
    · rename_i h
      have hab : Level.eval φ a = Level.eval φ b := by rw [← ha, ← hb, beq_iff_eq.mp h]
      show Level.eval φ (imaxCollapse a) =
        (if Level.eval φ b = 0 then 0 else Max.max (Level.eval φ a) (Level.eval φ b))
      rw [ha, ← hab]
      by_cases h0 : Level.eval φ a = 0 <;> simp [h0]
    · simp only [Level.eval, ha, hb]

theorem eval_lvlNorm (φ : LevelParam → Nat) (u : Level) : Level.eval φ (lvlNorm u) = Level.eval φ u := by
  rw [lvlNorm, eval_imaxCollapse, Level.eval_simplify]

/-- **`lvlEq` is sound**: the two levels evaluate alike at every assignment. -/
theorem lvlEq_sound {u v : Level} (h : lvlEq u v = true) (φ : LevelParam → Nat) :
    Level.eval φ u = Level.eval φ v := by
  unfold lvlEq at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [beq_iff_eq.mp h]
  · simp only [Bool.and_eq_true] at h
    obtain ⟨_, h⟩ := h
    rw [← eval_lvlNorm φ u, ← eval_lvlNorm φ v]
    rcases Bool.or_eq_true_iff.mp h with h | h
    · rw [beq_iff_eq.mp h]
    · split at h
      · rename_i a b ha hb
        simp only [Bool.and_eq_true] at h
        rw [maxPlus_eval φ _ _ ha, maxPlus_eval φ _ _ hb]
        exact Nat.le_antisymm (maxPlusLe_sound φ h.1) (maxPlusLe_sound φ h.2)
      · cases h

theorem lvlsEq_sound (φ : LevelParam → Nat) :
    ∀ {us vs : List Level}, lvlsEq us vs = true → Level.EvalEqList φ us vs
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => by
    simp only [lvlsEq, Bool.and_eq_true] at h
    exact ⟨lvlEq_sound h.1 φ, lvlsEq_sound φ h.2⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [lvlsEq] at h

/-! ## Part C. Equality up to what the denotation does not read -/

section Den

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}
  {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat}

theorem den_natLit {ρ : BVarIdx → V} {n : Nat} {Y : V} :
    Denotes cval env φ ρ (.lit (.natVal n)) Y ↔ Denotes cval env φ ρ (natLitToConstructor n) Y :=
  ⟨fun h => by cases h with | natLit h => exact h, fun h => .natLit h⟩

/-- A literal and a term `litEqE` equates denote alike. -/
theorem litEqE_sound : ∀ (e : KExpr) (a : Nat), litEqE a e = true →
    ∀ ρ Y Y', Denotes cval env φ ρ (.lit (.natVal a)) Y → Denotes cval env φ ρ e Y' → Y = Y' := by
  intro e
  induction e with
  | lit l =>
    intro a h ρ Y Y' hY hY'
    cases l with
    | natVal b =>
      simp only [litEqE, beq_iff_eq] at h
      subst h
      exact Denotes_functional hY hY'
    | strVal s =>
      cases a <;> simp [litEqE] at h
  | app g b _ ihb =>
    intro a h ρ Y Y' hY hY'
    cases a with
    | zero => simp [litEqE] at h
    | succ a =>
      simp only [litEqE, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hb⟩ := h
      have hY1 := den_natLit.mp hY
      simp only [natLitToConstructor] at hY1
      obtain ⟨S, A, hS, hA, rfl⟩ := den_app.mp hY1
      obtain ⟨S', B, hS', hB, rfl⟩ := den_app.mp hY'
      rw [Denotes_functional hS hS', ihb a hb ρ A B hA hB]
  | _ =>
    intro a h ρ Y Y' hY hY'
    cases a with
    | zero =>
      simp only [litEqE, beq_iff_eq] at h
      rw [h] at hY'
      exact Denotes_functional (den_natLit.mp hY) hY'
    | succ a => simp [litEqE] at h

/-- **`eqUpTo` is sound in every environment**: what it equates denote alike. -/
theorem eqUpTo_sound {x : DCtx} (hφ : AtProf φ x) :
    ∀ (T A : KExpr), eqUpTo x T A = true → ∀ ρ Y Y', Denotes cval env φ ρ T Y →
      Denotes cval env φ ρ A Y' → Y = Y' := by
  intro T
  induction T with
  | bvar i =>
    intro A h ρ Y Y' hY hY'
    rcases A with _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _⟩ | _ <;> simp only [eqUpTo] at h <;>
      first
      | exact Denotes_functional hY ((beq_iff_eq.mp h) ▸ hY')
      | exact (litEqE_sound _ _ h ρ Y' Y hY' hY).symm
  | fvar _ _ _ => intro A h ρ Y Y' hY; cases hY
  | letE _ _ _ _ _ _ _ => intro A h ρ Y Y' hY; cases hY
  | sort u =>
    intro A h ρ Y Y' hY hY'
    rcases A with _ | _ | v | _ | _ | _ | _ | _ | ⟨_ | _⟩ | _ <;> simp only [eqUpTo] at h <;>
      first
      | exact Denotes_functional hY ((beq_iff_eq.mp h) ▸ hY')
      | exact (litEqE_sound _ _ h ρ Y' Y hY' hY).symm
      | (rw [den_sort] at hY hY'; rw [hY, hY', lvlEq_sound h φ])
  | const k us =>
    intro A h ρ Y Y' hY hY'
    rcases A with _ | _ | _ | ⟨k', vs⟩ | _ | _ | _ | _ | ⟨_ | _⟩ | _ <;> simp only [eqUpTo] at h <;>
      first
      | exact Denotes_functional hY ((beq_iff_eq.mp h) ▸ hY')
      | exact (litEqE_sound _ _ h ρ Y' Y hY' hY).symm
      | skip
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hl⟩ := h
    cases hY with
    | const hf _ =>
      cases hY' with
      | const hf' _ =>
        rw [hf] at hf'
        cases hf'
        rw [Level.substFn_congr (lvlsEq_sound φ hl)]
  | app f a ihf iha =>
    intro A h ρ Y Y' hY hY'
    rcases A with _ | _ | _ | _ | ⟨g, b⟩ | _ | _ | _ | ⟨_ | _⟩ | _ <;> simp only [eqUpTo] at h <;>
      first
      | exact Denotes_functional hY ((beq_iff_eq.mp h) ▸ hY')
      | exact (litEqE_sound _ _ h ρ Y' Y hY' hY).symm
      | skip
    simp only [Bool.and_eq_true] at h
    obtain ⟨F, X, hF, hX, rfl⟩ := den_app.mp hY
    obtain ⟨F', X', hF', hX', rfl⟩ := den_app.mp hY'
    rw [ihf _ h.1 ρ F F' hF hF', iha _ h.2 ρ X X' hX hX']
  | lam d b m ihd ihb =>
    intro A h ρ Y Y' hY hY'
    rcases A with _ | _ | _ | _ | _ | ⟨d', b', m'⟩ | _ | _ | ⟨_ | _⟩ | _ <;> simp only [eqUpTo] at h <;>
      first
      | exact Denotes_functional hY ((beq_iff_eq.mp h) ▸ hY')
      | exact (litEqE_sound _ _ h ρ Y' Y hY' hY).symm
      | skip
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hm, hd⟩, hb⟩ := h
    obtain ⟨Ad, F, hAd, hF, _, rfl⟩ := den_lam.mp hY
    obtain ⟨Ad', F', hAd', hF', _, rfl⟩ := den_lam.mp hY'
    obtain rfl := ihd _ hd ρ Ad Ad' hAd hAd'
    rw [regime_of_pwEq hφ hm]
    exact lamR_congr fun z hz => ihb _ hb (push z ρ) _ _ (hF z hz) (hF' z hz)
  | forallE d b m ihd ihb =>
    intro A h ρ Y Y' hY hY'
    rcases A with _ | _ | _ | _ | _ | _ | ⟨d', b', m'⟩ | _ | ⟨_ | _⟩ | _ <;> simp only [eqUpTo] at h <;>
      first
      | exact Denotes_functional hY ((beq_iff_eq.mp h) ▸ hY')
      | exact (litEqE_sound _ _ h ρ Y' Y hY' hY).symm
      | skip
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hm, hd⟩, hb⟩ := h
    obtain ⟨Ad, Bf, hAd, hBf, _, rfl⟩ := den_pi.mp hY
    obtain ⟨Ad', Bf', hAd', hBf', _, rfl⟩ := den_pi.mp hY'
    obtain rfl := ihd _ hd ρ Ad Ad' hAd hAd'
    rw [regime_of_pwEq hφ hm]
    exact piR_congr fun z hz => ihb _ hb (push z ρ) _ _ (hBf z hz) (hBf' z hz)
  | lit l =>
    intro A h ρ Y Y' hY hY'
    cases l with
    | natVal a =>
      simp only [eqUpTo] at h
      exact litEqE_sound _ _ h ρ Y Y' hY hY'
    | strVal s =>
      rcases A with _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _⟩ | _ <;> simp only [eqUpTo] at h <;>
        first
        | exact Denotes_functional hY ((beq_iff_eq.mp h) ▸ hY')
        | exact (litEqE_sound _ _ h ρ Y' Y hY' hY).symm
  | proj s i e ih =>
    intro A h ρ Y Y' hY hY'
    rcases A with _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _⟩ | ⟨s', i', e'⟩ <;> simp only [eqUpTo] at h <;>
      first
      | exact Denotes_functional hY ((beq_iff_eq.mp h) ▸ hY')
      | exact (litEqE_sound _ _ h ρ Y' Y hY' hY).symm
      | skip
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, he⟩ := h
    cases hY with
    | proj_table ht hP =>
      cases hY' with
      | proj_table ht' hP' => rw [ht] at ht'; cases ht'; rw [ih _ he ρ _ _ hP hP']
      | proj_fst ht' _ => rw [ht] at ht'; cases ht'
      | proj_snd ht' _ => rw [ht] at ht'; cases ht'
    | proj_fst ht hP =>
      cases hY' with
      | proj_table ht' _ => rw [ht] at ht'; cases ht'
      | proj_fst _ hP' => rw [ih _ he ρ _ _ hP hP']
    | proj_snd ht hP =>
      cases hY' with
      | proj_table ht' _ => rw [ht] at ht'; cases ht'
      | proj_snd _ hP' => rw [ih _ he ρ _ _ hP hP']

end Den

end IxCC.Grounding
