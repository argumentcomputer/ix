import IxCCGrounding.Apply
import IxCCGrounding.Lits

/-!
# `Nat.le` at literal instances (`IxCCGrounding.WordLe`, step W)

The word case instantiates the stored bridge `∀ x (h : Nat.le (Nat.succ (x % S)) S), UIntN.ofNat x =
tower (x % S) h` at a literal `x` and must supply `h`: a member of `Nat.le (k + 1) S` for `k < S`. No law
says a proposition is inhabited, so it comes from `mem` of `Nat.le`'s two constructors, stored as the
kernel stores them (`NatLeBasis`, decided by the check): `refl : ∀ {n}, Nat.le n n` gives the instance
`a ≤ a`, and `step : ∀ {n m}, Nat.le n m → Nat.le n (Nat.succ m)` the next one (`natLe_mem`, by
induction on the distance). `mem` of `Nat.le : Nat → Nat → Prop` makes every member of an instance
the proof point (`natLe_pt`), so the member is `pt` (`pt_mem_natLe`). No law beyond `Model.mem`.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

/-- `Nat.le a b` as a kernel term over the key `kLe`. -/
def leApp (kLe : KKey) (a b : KExpr) : KExpr := .app (.app (.const kLe []) a) b

/-- **`Nat.le` and its two constructors as the word case reads them** (decided by the check): `Nat.le`
an inductive of type `Nat → Nat → Prop` with no level parameter; `refl` of type `∀ n, Nat.le n n`;
`step` of type `∀ n m, Nat.le n m → Nat.le n (Nat.succ m)` (binder data as stored, any). -/
structure NatLeBasis (env : KEnv) (kLe kR kS : KKey) : Prop where
  le : ∃ (cv : ConstantVal .anon) (caps : IndCaps .anon) (m1 m2 : BinderMeta),
    env.find? kLe = some (.indInfo cv caps) ∧ cv.levelParams = [] ∧
    cv.type = .forallE natK (.forallE natK (.sort .zero) m2) m1
  refl : ∃ (cv : ConstantVal .anon) (m : BinderMeta), env.find? kR = some (.ctorInfo cv 1 0) ∧
    cv.type = .forallE natK (leApp kLe (.bvar 0) (.bvar 0)) m
  step : ∃ (cv : ConstantVal .anon) (m1 m2 m3 : BinderMeta), env.find? kS = some (.ctorInfo cv 1 2) ∧
    cv.type = .forallE natK (.forallE natK (.forallE (leApp kLe (.bvar 1) (.bvar 0))
      (leApp kLe (.bvar 2) (.app (.const natSuccName []) (.bvar 1))) m3) m2) m1

section Le

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

theorem den_le_const (M : Model V env) {kLe kR kS : KKey} (hB : NatLeBasis env kLe kR kS)
    {φ : LevelParam → Nat} (ρ : BVarIdx → V) :
    Denotes M.cval env φ ρ (.const kLe []) (M.cval kLe φ) := by
  obtain ⟨cv, caps, -, -, hf, hl, -⟩ := hB.le
  exact (den_const0 (ci := .indInfo cv caps) hf hl).mpr rfl

/-- **Every member of an instance of `Nat.le` at two members of `Nat` is the proof point** (`mem` of
`Nat.le`, whose type ends in `Prop`). -/
theorem natLe_pt (M : Model V env) (hN : NatBasis env) {kLe kR kS : KKey}
    (hB : NatLeBasis env kLe kR kS) {φ : LevelParam → Nat} {x y z : V}
    (hx : x ∈ˢ M.cval natName φ) (hy : y ∈ˢ M.cval natName φ)
    (hz : z ∈ˢ app (app (M.cval kLe φ) x) y) : z = pt := by
  have hF := natFacts M hN φ
  obtain ⟨cv, caps, m1, m2, hf, -, ht⟩ := hB.le
  obtain ⟨T, hT, hm⟩ := mem_key M hf φ (fun _ => empty)
  simp only [ConstantInfo.toConstantVal, ht] at hT
  obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hT ((hF.natD _ _).mpr rfl) hm hx
  obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 ((hF.natD _ _).mpr rfl) hm1 hy
  rw [den_sort.mp hB2] at hm2
  simp only [Level.eval] at hm2
  rw [univ_zero] at hm2
  exact eq_pt_of_mem_univZero hm2 hz

/-- **`Nat.le a (a + d)` is inhabited**, by `refl` and `d` uses of `step`. -/
theorem natLe_mem (M : Model V env) (hN : NatBasis env) {kLe kR kS : KKey}
    (hB : NatLeBasis env kLe kR kS) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (a : Nat) :
    ∀ d, ∃ y, y ∈ˢ app (app (M.cval kLe φ) (litSet M φ a)) (litSet M φ (a + d)) := by
  have hF := natFacts M hN φ
  have hLe : ∀ ρ' : BVarIdx → V, Denotes M.cval env φ ρ' (.const kLe []) (M.cval kLe φ) :=
    fun ρ' => den_le_const M hB ρ'
  intro d
  induction d with
  | zero =>
    obtain ⟨cvR, mR, hfR, htR⟩ := hB.refl
    obtain ⟨T, hT, hm⟩ := mem_key M hfR φ ρ
    simp only [ConstantInfo.toConstantVal, htR, leApp] at hT
    obtain ⟨B, hB', hmB⟩ := app_mem_den_pi hT ((hF.natD ρ _).mpr rfl) hm (lit_mem M hF a)
    have hD : Denotes M.cval env φ (push (litSet M φ a) ρ)
        (.app (.app (.const kLe []) (.bvar 0)) (.bvar 0))
        (app (app (M.cval kLe φ) (litSet M φ a)) (litSet M φ a)) :=
      .app (.app (hLe _) (.bvar (i := 0))) (.bvar (i := 0))
    rw [Denotes_functional hB' hD] at hmB
    exact ⟨_, hmB⟩
  | succ d ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨cvS, m1, m2, m3, hfS, htS⟩ := hB.step
    obtain ⟨T, hT, hm⟩ := mem_key M hfS φ ρ
    simp only [ConstantInfo.toConstantVal, htS, leApp] at hT
    obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hT ((hF.natD ρ _).mpr rfl) hm (lit_mem M hF a)
    obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 ((hF.natD _ _).mpr rfl) hm1 (lit_mem M hF (a + d))
    have hD3 : Denotes M.cval env φ (push (litSet M φ (a + d)) (push (litSet M φ a) ρ))
        (.app (.app (.const kLe []) (.bvar 1)) (.bvar 0))
        (app (app (M.cval kLe φ) (litSet M φ a)) (litSet M φ (a + d))) :=
      .app (.app (hLe _) (.bvar (i := 1))) (.bvar (i := 0))
    obtain ⟨B3, hB3, hm3⟩ := app_mem_den_pi hB2 hD3 hm2 hy
    have hD4 : Denotes M.cval env φ (push y (push (litSet M φ (a + d)) (push (litSet M φ a) ρ)))
        (.app (.app (.const kLe []) (.bvar 2)) (.app (.const natSuccName []) (.bvar 1)))
        (app (app (M.cval kLe φ) (litSet M φ a)) (litSet M φ (a + (d + 1)))) :=
      .app (.app (hLe _) (.bvar (i := 2))) (.app ((hF.succD _ _).mpr rfl) (.bvar (i := 1)))
    rw [Denotes_functional hB3 hD4] at hm3
    exact ⟨_, hm3⟩

/-- **`pt` lies in `Nat.le a b` for `a ≤ b`** (the bridge's binder at a true instance). -/
theorem pt_mem_natLe (M : Model V env) (hN : NatBasis env) {kLe kR kS : KKey}
    (hB : NatLeBasis env kLe kR kS) (φ : LevelParam → Nat) {a b : Nat} (hab : a ≤ b) :
    (pt : V) ∈ˢ app (app (M.cval kLe φ) (litSet M φ a)) (litSet M φ b) := by
  have hF := natFacts M hN φ
  obtain ⟨y, hy⟩ := natLe_mem M hN hB φ (fun _ => empty) a (b - a)
  rw [Nat.add_sub_cancel' hab] at hy
  rwa [natLe_pt M hN hB (lit_mem M hF a) (lit_mem M hF b) hy] at hy

end Le

end IxCC.Grounding
