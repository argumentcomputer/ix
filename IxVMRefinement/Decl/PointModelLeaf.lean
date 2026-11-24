import IxVMRefinement.Decl.PointModelTele
import IxCK.Kernel.Model.JudgeRules
import IxCK.Kernel.Model.Harvest
import IxCK.Kernel.Model.IndCons
import IxCK.Kernel.Model.IndCaps
import IxCK.Kernel.Model.Swap
import IxCK.Kernel.Model.CtxOkKit
import IxCK.Kernel.Semantics.IndBlockFacts
import IxCK.Kernel.Rules.Transport

/-! # The one-point interpretation of an inductive block, at the model tier

A block of inductive types none of whose recursors is stored can be modeled with every type a
one-point type: the former `T : ∀ xs, Sort l` reads as `λ xs, PUnit.{l}` and a constructor
`c : ∀ ys, T as` as `λ ys, PUnit.unit.{v}`. `Ix.Kernel.Model` asks of such an inductive, stored
at the empty capability record, only that its constants inhabit their types, so no positivity
or universe condition is needed.

The members are stored as inductives and constructors, and the rules tier has no rule that
unfolds an inductive. The equation `T as = PUnit` is therefore taken from a second environment
that is never installed, the **shadow**: the same constants under the same keys, with each
former of the block stored as the definition `λ xs, PUnit.{l}` instead. One annotated valuation
models both (`Twin.denoteMeta_eq`: a reading consults the environment only through the stored
level parameters, the literal guards and the projection tables). Typing derivations are read at
the real environment, the conversion `∀ ys, PUnit.{v} ≡ ∀ ys, T as` (δ at `T`, β at binders
whose datum is `never`) at the shadow, and its soundness there gives the membership of the
constructor's leaf at the real one (`Leaf.convert`).

`pointRun_modelT` is the result: a run of member checks (`PointRun`) keeps the fold's model
invariant `EnvModelT`. No constant is stored beyond the block's own.
-/

namespace IxVM.Refinement.Decl.Point

open Ix.Kernel
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Term Ix.Kernel.Verify Ix.Kernel.SetTheory
open Ix.Kernel.Model
open Ix.Kernel.Rules (Red DefEq Infer Grade)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The `PUnit` pin -/

/-- **The kernel's `PUnit` pin is stored**, as the derivations read it: `PUnit.{l} : Sort l`
and `PUnit.unit.{l} : PUnit.{l}` at every level, grade and depth. -/
structure PUnitPin (env : Env .anon) : Prop where
  punit : ∀ (l : Level) (g : Grade) (d : Nat), Infer env g d (.const punitName [l]) (.sort l)
  unit : ∀ (l : Level) (g : Grade) (d : Nat),
    Infer env g d (.const punitUnitName [l]) (.const punitName [l])
  stored : (env.find? punitName).isSome = true ∧ (env.find? punitUnitName).isSome = true

theorem isSome_of_envExt {env env' : Env .anon} (hx : EnvExt env env') {n : Key .anon}
    (h : (env.find? n).isSome = true) : (env'.find? n).isSome = true := by
  cases hf : env.find? n with
  | none => rw [hf] at h; exact nomatch h
  | some c => rw [hx.find hf]; rfl

theorem PUnitPin.mono {env env' : Env .anon} (h : PUnitPin env) (hx : EnvExt env env') :
    PUnitPin env' where
  punit := fun l g d => Infer.weaken hx (h.punit l g d)
  unit := fun l g d => Infer.weaken hx (h.unit l g d)
  stored := ⟨isSome_of_envExt hx h.stored.1, isSome_of_envExt hx h.stored.2⟩

/-- The pin, from the two stored constants: a type former at one level parameter of type
`Sort` at it, and a constant of that type at the same parameter. -/
theorem PUnitPin.of_stored {env : Env .anon} {ciP ciU : ConstantInfo .anon} {p q : LevelParam}
    (hP : env.find? punitName = some ciP) (hPt : ciP.isTowerEntry = false)
    (hPl : ciP.toConstantVal.levelParams = [p])
    (hPty : ciP.toConstantVal.type = .sort (.param p))
    (hU : env.find? punitUnitName = some ciU) (hUt : ciU.isTowerEntry = false)
    (hUl : ciU.toConstantVal.levelParams = [q])
    (hUty : ciU.toConstantVal.type = .const punitName [.param q]) : PUnitPin env where
  punit := fun l g d => by
    have h := Infer.const (env := env) (g := g) (d := d) (us := [l]) hP hPt
      (by rw [hPl]; rfl)
    rw [hPl, hPty] at h
    simpa [Expr.instantiateLevelParams, Level.subst, Level.subst.go] using h
  unit := fun l g d => by
    have h := Infer.const (env := env) (g := g) (d := d) (us := [l]) hU hUt
      (by rw [hUl]; rfl)
    rw [hUl, hUty] at h
    simpa [Expr.instantiateLevelParams, Level.subst, Level.subst.go] using h
  stored := ⟨by rw [hP]; rfl, by rw [hU]; rfl⟩

/-! ## Leaves -/

/-- **A leaf for a constant of type `type'`**: a valuation entry that is closed, reads only the
level parameters `lps`, is graded and bit-valid, and inhabits the reading of `type'`, which is
graded. What `declStep_preserves_of_cons` asks of a fresh constant's leaf. -/
structure Leaf {env : Env .anon} (m : EnvModel V env) (lps : List LevelParam)
    (type' : Expr .anon) (A : (LevelParam → Nat) → AnnotTerm) : Prop where
  closed : ∀ (ψ : LevelParam → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ
  params : ∀ ψ₁ ψ₂ : LevelParam → Nat, (∀ p ∈ lps, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂
  ok : ∀ (ψ : LevelParam → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ)
  valid : ∀ (ψ : LevelParam → Nat) (ρ : Nat → V), AnnotValid V ρ (A ψ)
  vclosed : ∀ ψ : LevelParam → Nat, Term.Closed ((A ψ).erase)
  key : ∀ ψ : LevelParam → Nat, ∃ ta : AnnotTerm,
    denoteMeta m.acval env ψ 0 type' = some ta ∧
    (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
    ∀ ρ : Nat → V, interp V ρ (A ψ) ∈ˢ interp V ρ ta

/-- **The reading of a typed closed term is a leaf at its inferred type**, which keeps the
term's frame. -/
theorem leaf_of_infer {env : Env .anon} (mp : EnvModelM V μ env) {lps : List LevelParam}
    {value' vtype : Expr .anon}
    (hvf' : value'.hasFvar = false) (hbv' : value'.looseBVarsBounded 0 = true)
    (hvp : value'.allLevelParamsDefined lps = true)
    (hvrun : Infer env .full 0 value' vtype) :
    ∃ A : (LevelParam → Nat) → AnnotTerm,
      (∀ ψ, denoteMeta mp.base2.acval env ψ 0 value' = some (A ψ)) ∧
      Leaf mp.base2 lps vtype A ∧
      Expr.WScoped 0 vtype ∧ vtype.looseBVarsBounded 0 = true ∧ vtype.fvarLeaves = [] := by
  have hJ : JudgeSound rulesJ mp.base2 := judgeSound_rulesJ_of mp
  have hrun : (rulesJ (md := .anon)).infer env 0 value' vtype := hvrun
  have hwv : Expr.WScoped 0 value' := Expr.WScoped.of_not_hasFvar hvf'
  have hnlv : value'.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf'
  have hLv : Expr.LeavesBounded value' := fun l hl => by
    rw [hnlv] at hl
    exact absurd hl (List.not_mem_nil)
  have hAex : ∀ ψ : LevelParam → Nat,
      ∃ va, denoteMeta mp.base2.acval env ψ 0 value' = some va :=
    fun ψ => hJ.accepted ψ hrun hwv hbv' hLv
  let A : (LevelParam → Nat) → AnnotTerm :=
    fun ψ => (denoteMeta mp.base2.acval env ψ 0 value').getD default
  have hA : ∀ ψ : LevelParam → Nat,
      denoteMeta mp.base2.acval env ψ 0 value' = some (A ψ) := by
    intro ψ
    obtain ⟨va, hva⟩ := hAex ψ
    show _ = some ((denoteMeta mp.base2.acval env ψ 0 value').getD default)
    simp [hva]
  have hrows : ∀ ψ : LevelParam → Nat, ∃ vta,
      denoteMeta mp.base2.acval env ψ 0 vtype = some vta ∧
      ((∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ (A ψ)) ∧
        (∀ ρ : Nat → V, Sat V [] ρ → WellDenotedV V ρ vta) ∧
        ∀ ρ : Nat → V, Sat V [] ρ → interp V ρ (A ψ) ∈ˢ interp V ρ vta) := by
    intro ψ
    obtain ⟨vta, hvta⟩ := hJ.reads ψ hrun hwv hbv' hLv (CtxOk.nil hnlv) (hA ψ)
    exact ⟨vta, hvta, hJ.infer ψ hrun hwv hbv' hLv (CtxOk.nil hnlv) (hA ψ) hvta⟩
  have hframe := hJ.frame (fun _ => 0) hrun hwv hbv' hLv (CtxOk.nil hnlv) (hA _)
  have hnlvt : vtype.fvarLeaves = [] := by
    cases hh : vtype.fvarLeaves with
    | nil => rfl
    | cons l ls =>
      have := hframe.2.2 l (by rw [hh]; exact List.mem_cons_self ..)
      rw [hnlv] at this
      exact absurd this (List.not_mem_nil)
  refine ⟨A, hA, ?_, hframe.1, hframe.2.1, hnlvt⟩
  exact
    { closed := fun ψ k =>
        denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed hvf' hbv' (hA ψ) 1 k
      params := fun ψ₁ ψ₂ hψ => by
        have := denoteMeta_params_ext mp.base2 hψ 0 value' hvp
        rw [hA ψ₁, hA ψ₂] at this
        exact Option.some.inj this
      ok := fun ψ ρ => by
        obtain ⟨vta, hvta, hrE, -, -⟩ := hrows ψ
        exact (hrE ρ (Sat_nil V ρ)).1
      valid := fun ψ ρ => by
        obtain ⟨vta, hvta, hrE, -, -⟩ := hrows ψ
        exact (hrE ρ (Sat_nil V ρ)).2
      vclosed := fun ψ =>
        denote_closed mp.base2.cval_closed hvf' hbv'
          (denoteMeta_erase mp.base2.acval_erase 0 value' (hA ψ))
      key := fun ψ => by
        obtain ⟨vta, hvta, -, hrT, hrM⟩ := hrows ψ
        exact ⟨vta, hvta, fun ρ => hrT ρ (Sat_nil V ρ), fun ρ => hrM ρ (Sat_nil V ρ)⟩ }

/-- A typed closed type reads, and its reading is graded. -/
theorem type_row {env : Env .anon} (mp : EnvModelM V μ env) {type' stype : Expr .anon}
    (htf' : type'.hasFvar = false) (hbt' : type'.looseBVarsBounded 0 = true)
    (hst : Infer env .full 0 type' stype) (ψ : LevelParam → Nat) :
    ∃ ta, denoteMeta mp.base2.acval env ψ 0 type' = some ta ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ ta := by
  have hJ : JudgeSound rulesJ mp.base2 := judgeSound_rulesJ_of mp
  have hrun : (rulesJ (md := .anon)).infer env 0 type' stype := hst
  have hwt : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hnlt : type'.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hLt : Expr.LeavesBounded type' := fun l hl => by
    rw [hnlt] at hl
    exact absurd hl (List.not_mem_nil)
  obtain ⟨ta, hta⟩ := hJ.accepted ψ hrun hwt hbt' hLt
  obtain ⟨sta, hsta⟩ := hJ.reads ψ hrun hwt hbt' hLt (CtxOk.nil hnlt) hta
  exact ⟨ta, hta, fun ρ =>
    (hJ.infer ψ hrun hwt hbt' hLt (CtxOk.nil hnlt) hta hsta).1 ρ (Sat_nil V ρ)⟩

/-- **A conversion of closed terms equates their readings**, where both are graded. -/
theorem interp_eq_of_defEq {env : Env .anon} (mp : EnvModelM V μ env) {a b : Expr .anon}
    (hde : DefEq env 0 a b)
    (hwa : Expr.WScoped 0 a) (hba : a.looseBVarsBounded 0 = true) (hla : a.fvarLeaves = [])
    (hfb : b.hasFvar = false) (hbb : b.looseBVarsBounded 0 = true)
    {ψ : LevelParam → Nat} {aa ba : AnnotTerm}
    (haa : denoteMeta mp.base2.acval env ψ 0 a = some aa)
    (hbr : denoteMeta mp.base2.acval env ψ 0 b = some ba)
    (hoka : ∀ ρ : Nat → V, WellDenotedV V ρ aa) (hokb : ∀ ρ : Nat → V, WellDenotedV V ρ ba)
    (ρ : Nat → V) : interp V ρ aa = interp V ρ ba := by
  have hJ : JudgeSound rulesJ mp.base2 := judgeSound_rulesJ_of mp
  have hrun : (rulesJ (md := .anon)).defeq env 0 a b := hde
  have hLa : Expr.LeavesBounded a := fun l hl => by
    rw [hla] at hl
    exact absurd hl (List.not_mem_nil)
  have hlb : b.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hfb
  have hLb : Expr.LeavesBounded b := fun l hl => by
    rw [hlb] at hl
    exact absurd hl (List.not_mem_nil)
  exact hJ.defeq ψ hrun hwa hba hLa (Expr.WScoped.of_not_hasFvar hfb) hbb hLb
    (CtxOk.nil hla) (CtxOk.nil hlb) haa hbr (fun ρ _ => hoka ρ) (fun ρ _ => hokb ρ) ρ
    (Sat_nil V ρ)

/-! ## Twin environments -/

/-- **A shadowed former**: stored at the real environment as an inductive at the empty
capability record, and at the shadow as the `PUnit`-valued definition over its type, a
telescope into a sort whose binders all carry `never`. Its key is an input key. -/
def ShadowAt (envT envD : Env .anon) (n : Key .anon) : Prop :=
  (∃ a, n = .id a) ∧ ∃ (cv : ConstantVal .anon) (l : Level) (hint : ReducibilityHint),
    envT.find? n = some (.indInfo cv {}) ∧
    envD.find? n = some (.defnInfo cv (lamTele (.const punitName [l]) cv.type) hint) ∧
    cv.type.resultSort = some l ∧ PwAll PropWhen.never cv.type

/-- **Twin environments**: the shadow stores what the real environment stores, except at the
shadowed formers. -/
def Twin (envT envD : Env .anon) : Prop :=
  ∀ n : Key .anon, envT.find? n = envD.find? n ∨ ShadowAt envT envD n

theorem Twin.refl (env : Env .anon) : Twin env env := fun _ => Or.inl rfl

section TwinFacts

variable {envT envD : Env .anon}

theorem ShadowAt.cons {cT cD : ConstantInfo .anon} {n : Key .anon}
    (hT : cT.name ≠ n) (hD : cD.name ≠ n) (h : ShadowAt envT envD n) :
    ShadowAt ⟨cT :: envT.consts⟩ ⟨cD :: envD.consts⟩ n := by
  obtain ⟨hid, cv, l, hint, h1, h2, h3, h4⟩ := h
  exact ⟨hid, cv, l, hint, by rw [EnvExt.find?_cons_ne hT]; exact h1,
    by rw [EnvExt.find?_cons_ne hD]; exact h2, h3, h4⟩

theorem ShadowAt.self {cv : ConstantVal .anon} {l : Level} {hint : ReducibilityHint}
    (hid : ∃ a, cv.name = .id a) (hr : cv.type.resultSort = some l)
    (hp : PwAll PropWhen.never cv.type) :
    ShadowAt ⟨.indInfo cv {} :: envT.consts⟩
      ⟨.defnInfo cv (lamTele (.const punitName [l]) cv.type) hint :: envD.consts⟩ cv.name :=
  ⟨hid, cv, l, hint, Env.find?_cons_self (.indInfo cv {}) envT,
    Env.find?_cons_self (.defnInfo cv (lamTele (.const punitName [l]) cv.type) hint) envD,
    hr, hp⟩

theorem Twin.cons_same (h : Twin envT envD) (c : ConstantInfo .anon) :
    Twin ⟨c :: envT.consts⟩ ⟨c :: envD.consts⟩ := by
  intro n
  by_cases hn : c.name = n
  · subst hn
    exact Or.inl ((Env.find?_cons_self c envT).trans (Env.find?_cons_self c envD).symm)
  · rcases h n with h | h
    · exact Or.inl (by rw [EnvExt.find?_cons_ne hn, EnvExt.find?_cons_ne hn, h])
    · exact Or.inr (h.cons hn hn)

theorem Twin.cons_shadow (h : Twin envT envD) {cv : ConstantVal .anon} {l : Level}
    {hint : ReducibilityHint} (hid : ∃ a, cv.name = .id a)
    (hr : cv.type.resultSort = some l) (hp : PwAll PropWhen.never cv.type) :
    Twin ⟨.indInfo cv {} :: envT.consts⟩
      ⟨.defnInfo cv (lamTele (.const punitName [l]) cv.type) hint :: envD.consts⟩ := by
  intro n
  by_cases hn : cv.name = n
  · subst hn
    exact Or.inr (ShadowAt.self hid hr hp)
  · rcases h n with h | h
    · exact Or.inl (by
        rw [EnvExt.find?_cons_ne (c := .indInfo cv {}) hn,
          EnvExt.find?_cons_ne
            (c := .defnInfo cv (lamTele (.const punitName [l]) cv.type) hint) hn, h])
    · exact Or.inr (h.cons hn hn)

theorem Twin.find_eq (h : Twin envT envD) {n : Key .anon} (hn : ∀ a, n ≠ .id a) :
    envT.find? n = envD.find? n := by
  rcases h n with h | ⟨⟨a, ha⟩, -⟩
  · exact h
  · exact absurd ha (hn a)

theorem Twin.levels (h : Twin envT envD) (n : Key .anon) :
    (envT.find? n).map (fun ci => ci.toConstantVal.levelParams) =
      (envD.find? n).map (fun ci => ci.toConstantVal.levelParams) := by
  rcases h n with h | ⟨-, cv, l, hint, hT, hD, -, -⟩
  · rw [h]
  · rw [hT, hD]
    rfl

theorem Twin.isSome (h : Twin envT envD) (n : Key .anon) :
    (envT.find? n).isSome = (envD.find? n).isSome := by
  rcases h n with h | ⟨-, cv, l, hint, hT, hD, -, -⟩
  · rw [h]
  · rw [hT, hD]
    rfl

theorem Twin.fresh (h : Twin envT envD) {n : Key .anon} (hf : envT.find? n = none) :
    envD.find? n = none := by
  rcases h n with h | ⟨-, cv, l, hint, hT, -, -, -⟩
  · rw [← h]
    exact hf
  · rw [hT] at hf
    exact nomatch hf

theorem Twin.natLit (h : Twin envT envD) : natLitSupported envT = natLitSupported envD := by
  unfold natLitSupported
  rw [h.find_eq (n := natName) (fun a => roleKey_ne_id _ a),
    h.find_eq (n := natZeroName) (fun a => roleKey_ne_id _ a),
    h.find_eq (n := natSuccName) (fun a => roleKey_ne_id _ a)]

theorem Twin.strLit (h : Twin envT envD) : strLitSupported envT = strLitSupported envD := by
  unfold strLitSupported
  rw [h.natLit, h.find_eq (n := stringName) (fun a => roleKey_ne_id _ a),
    h.find_eq (n := stringOfListName) (fun a => roleKey_ne_id _ a),
    h.find_eq (n := listName) (fun a => roleKey_ne_id _ a),
    h.find_eq (n := listNilName) (fun a => roleKey_ne_id _ a),
    h.find_eq (n := listConsName) (fun a => roleKey_ne_id _ a),
    h.find_eq (n := charName) (fun a => roleKey_ne_id _ a),
    h.find_eq (n := charOfNatName) (fun a => roleKey_ne_id _ a)]

theorem Twin.proj (h : Twin envT envD) (sn : Key .anon) (i : Nat) :
    envT.findProj? sn i = envD.findProj? sn i := by
  unfold Env.findProj?
  rw [h.find_eq (n := projTableName sn) (fun a => auxKey_ne_id sn .projTable a)]

/-- **A reading is the same at twin environments.** -/
theorem Twin.denoteMeta_eq (h : Twin envT envD)
    (acval : Key .anon → (LevelParam → Nat) → AnnotTerm) (ψ : LevelParam → Nat) (d : Nat)
    (e : Expr .anon) : denoteMeta acval envT ψ d e = denoteMeta acval envD ψ d e :=
  denoteMeta_env_ext h.levels h.natLit h.strLit h.proj d e

theorem Twin.constsResolve (h : Twin envT envD) {e : Expr .anon}
    (he : e.constsResolve envT = true) : e.constsResolve envD = true :=
  Expr.constsResolve_le (fun n hn => by rw [← h.isSome n]; exact hn) he

/-- A leaf at the real model is one at the shadow model. -/
theorem Leaf.twin {mT : EnvModel V envT} {mD : EnvModel V envD}
    (hac : mD.acval = mT.acval) (htw : Twin envT envD) {lps : List LevelParam}
    {type' : Expr .anon} {A : (LevelParam → Nat) → AnnotTerm} (h : Leaf mT lps type' A) :
    Leaf mD lps type' A where
  closed := h.closed
  params := h.params
  ok := h.ok
  valid := h.valid
  vclosed := h.vclosed
  key := fun ψ => by
    obtain ⟨ta, hta, hok, hmem⟩ := h.key ψ
    exact ⟨ta, by rw [hac, ← htw.denoteMeta_eq]; exact hta, hok, hmem⟩

/-- **A leaf moves along a conversion derived at the shadow.** -/
theorem Leaf.convert (mT : EnvModelM V μ envT) (mD : EnvModelM V μ envD)
    (hac : mD.base2.acval = mT.base2.acval) (htw : Twin envT envD)
    {lps : List LevelParam} {vtype type' : Expr .anon} {A : (LevelParam → Nat) → AnnotTerm}
    (hleaf : Leaf mT.base2 lps vtype A)
    (hwv : Expr.WScoped 0 vtype) (hbv : vtype.looseBVarsBounded 0 = true)
    (hlv : vtype.fvarLeaves = [])
    (htf' : type'.hasFvar = false) (hbt' : type'.looseBVarsBounded 0 = true)
    (hrow : ∀ ψ, ∃ ta, denoteMeta mT.base2.acval envT ψ 0 type' = some ta ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ ta)
    (hde : DefEq envD 0 vtype type') : Leaf mT.base2 lps type' A where
  closed := hleaf.closed
  params := hleaf.params
  ok := hleaf.ok
  valid := hleaf.valid
  vclosed := hleaf.vclosed
  key := fun ψ => by
    obtain ⟨vta, hvta, hokv, hmem⟩ := hleaf.key ψ
    obtain ⟨ta, hta, hokt⟩ := hrow ψ
    have hvtaD : denoteMeta mD.base2.acval envD ψ 0 vtype = some vta := by
      rw [hac, ← htw.denoteMeta_eq]; exact hvta
    have htaD : denoteMeta mD.base2.acval envD ψ 0 type' = some ta := by
      rw [hac, ← htw.denoteMeta_eq]; exact hta
    refine ⟨ta, hta, hokt, fun ρ => ?_⟩
    rw [← interp_eq_of_defEq mD hde hwv hbv hlv htf' hbt' hvtaD htaD hokv hokt ρ]
    exact hmem ρ

end TwinFacts

/-! ## The two conses -/

/-- An input key is no `Nat` operation's. -/
theorem not_natOp_of_id {n : Key .anon} (h : ∃ a, n = .id a) :
    n ∉ natOpNames ∧ n ∉ natDivModNames := by
  obtain ⟨a, rfl⟩ := h
  constructor
  · intro hm
    simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h <;> exact nomatch h
  · intro hm
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h <;> exact nomatch h

/-- **A block member, stored with a given leaf**: an inductive at the empty capability record
or a constructor, at a fresh unreserved key, extends the model. -/
theorem consMember {env : Env .anon} (mp : EnvModelM V μ env) {c₀ : ConstantInfo .anon}
    {cvA : ConstantVal .anon}
    (hkind : c₀ = .indInfo cvA {} ∨ ∃ nP nF, c₀ = .ctorInfo cvA nP nF)
    (hfresh : env.find? cvA.name = none)
    (hnres : reservedBasisNames.contains cvA.name = false)
    (hpshape : cvA.name.isProjFnShape = false)
    (hty : cvA.type.hasFvar = false ∧
      cvA.type.allLevelParamsDefined cvA.levelParams = true ∧
      cvA.type.constsResolve env = true ∧ cvA.type.looseBVarsBounded 0 = true)
    (hE : EtaFamiliesClosed env)
    {A : (LevelParam → Nat) → AnnotTerm} (hleaf : Leaf mp.base2 cvA.levelParams cvA.type A) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvA.name A ∧ ModelExt mp mp' := by
  obtain ⟨h1, h2, h3, h4⟩ := hty
  have hcv : c₀.toConstantVal = cvA := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> rfl
  have hname : c₀.name = cvA.name := congrArg ConstantVal.name hcv
  have hnotdefn : ∀ cv v hint, c₀ ≠ .defnInfo cv v hint := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> intro _ _ _ h <;> exact nomatch h
  have hnotrec : ∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> intro _ _ _ _ h <;> exact nomatch h
  have hnotproj : ∀ tbl, c₀ ≠ .projInfo tbl := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> intro _ h <;> exact nomatch h
  have hnotthm : ∀ (cv : ConstantVal .anon) (v : Expr .anon), c₀ ≠ .thmInfo cv v := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩ <;> intro _ _ h <;> exact nomatch h
  have hcaps0 : ∀ cv caps, c₀ = .indInfo cv caps → caps = {} := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩
    · intro cv caps h
      exact (ConstantInfo.indInfo.inj h).2.symm
    · intro cv caps h
      exact nomatch h
  have hknd : (∃ cv caps, c₀ = .indInfo cv caps) ∨ ∃ cv nP nF, c₀ = .ctorInfo cv nP nF := by
    rcases hkind with rfl | ⟨nP, nF, rfl⟩
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr ⟨_, _, _, rfl⟩
  have hfresh0 : env.find? c₀.name = none := by rw [hname]; exact hfresh
  have hnres0 : reservedBasisNames.contains c₀.name = false := by rw [hname]; exact hnres
  have hpshape0 : c₀.name.isProjFnShape = false := by rw [hname]; exact hpshape
  have hicw : IndCapsWF c₀ := by
    intro cv caps heq
    rw [hcaps0 cv caps heq]
    exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  have hwf : EnvWF ⟨c₀ :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf (structConstWF (by rw [hcv]; exact h1) (by rw [hcv]; exact h2)
      (Expr.constsResolve_mono (by rw [hcv]; exact h3)) (by rw [hcv]; exact h4)
      (fun cv v hint heq => absurd heq (hnotdefn cv v hint))
      (fun cv mI rP rules heq => absurd heq (hnotrec cv mI rP rules))
      (fun tbl heq => absurd heq (hnotproj tbl)) hicw)
  have hcb : ConstsBound env cvA.type := constsBound_of_constsResolve _ h3
  have hcross : ∀ (ψ : LevelParam → Nat) {ta : AnnotTerm},
      denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta →
      denoteMeta (acvalWith mp.base2.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ 0
        c₀.toConstantVal.type = some ta := by
    intro ψ ta h
    rw [hcv]
    exact denoteMeta_cons_fresh_mono hfresh0 hnotproj ψ 0 cvA.type hcb h
  have hh : ConsHead env c₀ A :=
    ConsHead.ofFresh hwf hleaf.vclosed hnres0 hnotproj
      (fun cvR mI rP rules heq => absurd heq (hnotrec cvR mI rP rules))
  obtain ⟨mp', hac⟩ := declStep_preserves_of_ind_member_cons mp (c₀ := c₀) (A := A)
    hfresh0 hnres0 hknd hh hleaf.closed
    (fun ψ₁ ψ₂ hps => hleaf.params ψ₁ ψ₂ (by rw [← hcv]; exact hps))
    hleaf.ok hleaf.valid
    (fun ψ => by
      obtain ⟨ta, hta, -, -⟩ := hleaf.key ψ
      exact ⟨ta, hcross ψ hta⟩)
    (fun ψ ta hta ρ => by
      obtain ⟨ta₀, hta₀, hok, -⟩ := hleaf.key ψ
      obtain rfl : ta₀ = ta := Option.some.inj ((hcross ψ hta₀).symm.trans hta)
      exact hok ρ)
    (fun ψ ta hta ρ => by
      obtain ⟨ta₀, hta₀, -, hmem⟩ := hleaf.key ψ
      obtain rfl : ta₀ = ta := Option.some.inj ((hcross ψ hta₀).symm.trans hta)
      exact hmem ρ)
    (fun m₂ hac => capsOk_cons_member mp (blockNames := [cvA.name]) hfresh0 hnotproj hcv hname
      hpshape0 (by simp)
      (fun caps heq => by
        have hc : caps = {} := hcaps0 cvA caps heq
        subst hc
        exact ⟨etaPins_empty, fun h => (nomatch h), fun h => (nomatch h)⟩)
      (fun T cvT caps hf hcape hres _ => hE T cvT caps hf hcape hres)
      (fun n cvS capsS hnb hf => by
        have hn : n = cvA.name := by simpa using hnb
        rw [hn, hfresh] at hf
        exact nomatch hf)
      (fun T cvT caps hfT hcape hresT hp h0 hbT hbC hfamT m₃ hac₃ φ' => by
        have hTn : T = cvA.name := by simpa using hbT
        rw [hTn, ← hname, Env.find?_cons_self] at hfT
        have hc := Option.some.inj hfT
        rw [hcaps0 cvT caps hc] at hcape
        exact nomatch hcape)
      (fun cvT caps hceq hcapu hresT hpT m₃ hac₃ φ' => by
        rw [hcaps0 cvT caps hceq] at hcapu
        exact nomatch hcapu)
      m₂ hac)
  exact ⟨mp', by rw [hac, hname],
    (ModelExt.refl (mp₁ := mp)).plain hac hfresh0 hnotproj hnotthm⟩

/-- **A definition, stored with a given leaf that its value reads to**, at a fresh key that is
neither reserved nor a `Nat` operation's, extends the model. -/
theorem consDefn {env : Env .anon} (mp : EnvModelM V μ env) {cvA : ConstantVal .anon}
    {value' : Expr .anon} {hint : ReducibilityHint}
    (hfresh : env.find? cvA.name = none)
    (hnres : reservedBasisNames.contains cvA.name = false)
    (hnop : cvA.name ∉ natOpNames) (hndm : cvA.name ∉ natDivModNames)
    (hty : cvA.type.hasFvar = false ∧
      cvA.type.allLevelParamsDefined cvA.levelParams = true ∧
      cvA.type.constsResolve env = true ∧ cvA.type.looseBVarsBounded 0 = true)
    (hval : value'.hasFvar = false ∧
      value'.allLevelParamsDefined cvA.levelParams = true ∧
      value'.constsResolve env = true ∧ value'.looseBVarsBounded 0 = true)
    {A : (LevelParam → Nat) → AnnotTerm} (hleaf : Leaf mp.base2 cvA.levelParams cvA.type A)
    (hreads : ∀ ψ, denoteMeta mp.base2.acval env ψ 0 value' = some (A ψ)) :
    ∃ mp' : EnvModelM V μ ⟨.defnInfo cvA value' hint :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvA.name A ∧ ModelExt mp mp' := by
  obtain ⟨htf', htp, htr, hbt'⟩ := hty
  obtain ⟨hvf', hvp, hvr, hbv'⟩ := hval
  have hcbT : ConstsBound env cvA.type := constsBound_of_constsResolve _ htr
  have hcbV : ConstsBound env value' := constsBound_of_constsResolve _ hvr
  have hcomp : ∀ (ψ : LevelParam → Nat) (e : Expr .anon), ConstsBound env e →
      ∀ {ea : AnnotTerm}, denoteMeta mp.base2.acval env ψ 0 e = some ea →
      denoteMeta (acvalWith mp.base2.acval cvA.name A)
          ⟨.defnInfo cvA value' hint :: env.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteMeta_cons_fresh_mono (acval := mp.base2.acval)
        (c₀ := .defnInfo cvA value' hint) (A := A) hfresh (fun _ h => nomatch h) ψ 0 e hcb h
  have key : ∃ mp' : EnvModelM V μ ⟨.defnInfo cvA value' hint :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval
        (ConstantInfo.defnInfo cvA value' hint).name A := by
    refine declStep_preserves_of_cons mp (c₀ := .defnInfo cvA value' hint) (A := A) hfresh
      (ConsHead.ofFresh
        (EnvWF.cons mp.base2.wf ⟨htf', htp, Expr.constsResolve_mono htr, hbt',
          (fun _ _ _ heq => by
            obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj heq
            exact ⟨hvf', hvp, Expr.constsResolve_mono hvr, hbv'⟩),
          (fun _ _ _ _ heq => nomatch heq),
          (fun _ heq => nomatch heq),
          (fun _ _ heq => nomatch heq)⟩)
        hleaf.vclosed hnres (fun _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
      hleaf.closed hleaf.params hleaf.ok hleaf.valid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro ψ
      obtain ⟨ta, hta, -, -⟩ := hleaf.key ψ
      exact ⟨ta, hcomp ψ cvA.type hcbT hta⟩
    · intro ψ ta hta ρ
      replace hta : denoteMeta (acvalWith mp.base2.acval cvA.name A)
          ⟨.defnInfo cvA value' hint :: env.consts⟩ ψ 0 cvA.type = some ta := hta
      obtain ⟨ta₀, hta₀, hok, -⟩ := hleaf.key ψ
      obtain rfl : ta₀ = ta :=
        Option.some.inj ((hcomp ψ cvA.type hcbT hta₀).symm.trans hta)
      exact hok ρ
    · intro ψ ta hta ρ
      replace hta : denoteMeta (acvalWith mp.base2.acval cvA.name A)
          ⟨.defnInfo cvA value' hint :: env.consts⟩ ψ 0 cvA.type = some ta := hta
      obtain ⟨ta₀, hta₀, -, hmem⟩ := hleaf.key ψ
      obtain rfl : ta₀ = ta :=
        Option.some.inj ((hcomp ψ cvA.type hcbT hta₀).symm.trans hta)
      exact hmem ρ
    · intro ψ cv2 value2 hmem
      obtain ⟨hint2, hdt⟩ := hmem
      injection hdt with e1 e2 e3
      rw [e2]
      exact hcomp ψ value' hcbV (hreads ψ)
    · exact fun φ => natHeads_cons_fresh mp (c₀ := .defnInfo cvA value' hint) (A := A) hfresh
        ⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩ _ rfl φ
    · exact fun φ => natOps_cons_fresh mp (mp.nat_ops φ) (c₀ := .defnInfo cvA value' hint)
        (A := A) hfresh (hntc := ConsCrossEnv.ofNtc (fun _ h => nomatch h)) (Or.inr hnop) _ rfl
    · exact fun φ => divMod_cons_fresh (mp.div_mod φ) (c₀ := .defnInfo cvA value' hint)
        (A := A) hfresh (Or.inr hndm) _ rfl
    · exact eqLaw_cons_valueKind mp.eq_law (c₀ := .defnInfo cvA value' hint) (A := A)
        (fun _ _ h => nomatch h) _ rfl
    · exact capsOk_cons_fresh mp mp.caps_ok (c₀ := .defnInfo cvA value' hint) (A := A) hfresh
        (ConsCrossEnv.ofNtc (fun _ h => nomatch h)) (fun _ _ h => nomatch h)
        (fun _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) _ rfl
    · exact fun φ => recRules_cons_fresh mp (c₀ := .defnInfo cvA value' hint) (A := A) hfresh
        (ConsCrossEnv.ofNtc (fun _ h => nomatch h)) (fun _ _ _ _ h => nomatch h) _ rfl φ
    · exact fun φ => towerOk_cons_fresh mp (c₀ := .defnInfo cvA value' hint) (A := A) hfresh
        (ConsCrossEnv.ofNtc (fun _ h => nomatch h)) (fun _ h => nomatch h) _ rfl φ
  obtain ⟨mp', hac⟩ := key
  exact ⟨mp', hac,
    (ModelExt.refl (mp₁ := mp)).plain hac hfresh (fun _ h => nomatch h) (fun _ _ h => nomatch h)⟩

/-! ## The two chains -/

/-- **What the two chains keep**: the environments are twins modeled by one valuation; every
former of the block stored so far is shadowed; the stored η families are closed on both sides;
and the `PUnit` pin is stored. -/
structure Chain (formers : List (Key .anon)) {envT envD : Env .anon}
    (mT : EnvModelM V μ envT) (mD : EnvModelM V μ envD) : Prop where
  twin : Twin envT envD
  acval : mD.base2.acval = mT.base2.acval
  shadowed : ∀ T ∈ formers, ∀ cvT caps, envT.find? T = some (.indInfo cvT caps) →
    ShadowAt envT envD T
  closedT : EtaFamiliesClosed envT
  closedD : EtaFamiliesClosed envD
  pin : PUnitPin envT

/-- An input key is no projection table's. -/
theorem id_ne_projTableName {n : Key .anon} (h : ∃ a, n = .id a) (T : Key .anon) :
    n ≠ projTableName T := by
  obtain ⟨a, rfl⟩ := h
  exact fun e => auxKey_ne_id T .projTable a e.symm

/-- **A former joins the chains**: an inductive at the empty capability record on the real
side, the `PUnit`-valued definition on the shadow side, one leaf for both. -/
theorem chain_former {formers : List (Key .anon)} {envT envD : Env .anon}
    (mT : EnvModelM V μ envT) (mD : EnvModelM V μ envD) (hch : Chain formers mT mD)
    {cv : ConstantVal .anon} {type' : Expr .anon} {l : Level}
    (hcv : ConstantValRunJ rulesJ envT cv type') (hid : ∃ a, cv.name = .id a)
    (hr : type'.resultSort = some l) :
    ∃ (envD' : Env .anon)
      (mT' : EnvModelM V μ ⟨.indInfo ⟨cv.name, cv.levelParams, type'⟩ {} :: envT.consts⟩)
      (mD' : EnvModelM V μ envD'), Chain formers mT' mD' ∧ ModelExt mT mT' := by
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr, stype, u, hst, hens⟩ := hcv
  have hst' : Infer envT .full 0 type' stype := hst
  have hens' : Red envT 0 stype (.sort u) := hens
  obtain ⟨htf', hbt'⟩ := (judgeFrames_rulesJ envT).annot_syntax hann hitf hlbt
  have hfresh : envT.find? cv.name = none := Option.isNone_iff_eq_none.mp hfind
  have hsh : Shape type' := shape_of_resultSort type' l hr
  have hz : Level.zeronessOf u = PropWhen.never :=
    sort_of_resultSort _ type' 0 stype u rfl hr hst' hens'
  have hpw : PwAll PropWhen.never type' := by
    have := pwAll_of_infer _ type' 0 stype u rfl hsh hst' hens'
    rwa [hz] at this
  -- the value `λ xs, PUnit.{l}` has the former's type
  have hval : Infer envT .full 0 (lamTele (.const punitName [l]) type') type' := by
    have h := infer_lamTele (env := envT) (w := .const punitName [l]) (W := .sort l)
      (v' := .succ l) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => trivial) (fun _ => rfl) rfl
      (fun d => hch.pin.punit l .full d) (fun d => Infer.sort)
      _ type' 0 stype u rfl hsh (Expr.WScoped.of_not_hasFvar htf').fvarsBelow hbt' hst' hens'
      hz
    rwa [piTele_sort_self type' l hr] at h
  have hlpl : l.allParamsDefined cv.levelParams = true := resultSort_defined type' l hr htp
  have hvf' : (lamTele (.const punitName [l]) type').hasFvar = false :=
    lamTele_hasFvar rfl type' htf'
  have hvb' : (lamTele (.const punitName [l]) type').looseBVarsBounded 0 = true :=
    lamTele_looseBVarsBounded (fun _ => rfl) type' 0 hbt'
  have hvp : (lamTele (.const punitName [l]) type').allLevelParamsDefined cv.levelParams
      = true :=
    lamTele_allLevelParamsDefined (by simp [Expr.allLevelParamsDefined, hlpl]) type' htp
  have hvr : (lamTele (.const punitName [l]) type').constsResolve envT = true :=
    lamTele_constsResolve (by simpa [Expr.constsResolve] using hch.pin.stored.1) type' htr
  obtain ⟨A, hA, hleaf, -, -, -⟩ := leaf_of_infer mT hvf' hvb' hvp hval
  -- the real side
  obtain ⟨mT', hacT, hextT⟩ := consMember mT
    (c₀ := .indInfo ⟨cv.name, cv.levelParams, type'⟩ {})
    (cvA := ⟨cv.name, cv.levelParams, type'⟩) (Or.inl rfl) hfresh hnres hpshape
    ⟨htf', htp, htr, hbt'⟩ hch.closedT hleaf
  -- the shadow side
  have hfreshD : envD.find? cv.name = none := hch.twin.fresh hfresh
  have hnop := not_natOp_of_id hid
  obtain ⟨mD', hacD, -⟩ := consDefn mD (cvA := ⟨cv.name, cv.levelParams, type'⟩)
    (value' := lamTele (.const punitName [l]) type') (hint := .abbrev) hfreshD hnres
    hnop.1 hnop.2 ⟨htf', htp, hch.twin.constsResolve htr, hbt'⟩
    ⟨hvf', hvp, hch.twin.constsResolve hvr, hvb'⟩ (hleaf.twin hch.acval hch.twin)
    (fun ψ => by rw [hch.acval, ← hch.twin.denoteMeta_eq]; exact hA ψ)
  refine ⟨_, mT', mD', ?_, hextT⟩
  exact
    { twin := hch.twin.cons_shadow (cv := ⟨cv.name, cv.levelParams, type'⟩) hid hr hpw
      acval := by rw [hacT, hacD, hch.acval]
      shadowed := fun T hT cvT caps hf => by
        by_cases hn : cv.name = T
        · subst hn
          exact ShadowAt.self (cv := ⟨cv.name, cv.levelParams, type'⟩) hid hr hpw
        · rw [EnvExt.find?_cons_ne (c := .indInfo ⟨cv.name, cv.levelParams, type'⟩ {}) hn] at hf
          exact (hch.shadowed T hT cvT caps hf).cons hn hn
      closedT := EtaFamiliesClosed.cons_nonind hch.closedT hfresh (fun cv' caps heq he => by
        obtain ⟨-, hc⟩ := ConstantInfo.indInfo.inj heq
        rw [← hc] at he
        exact nomatch he)
      closedD := EtaFamiliesClosed.cons_nonind hch.closedD hfreshD
        (fun _ _ heq => nomatch heq)
      pin := hch.pin.mono (EnvExt.cons hfresh (fun _ => id_ne_projTableName hid _)) }

/-- **A constructor joins the chains**, stored as itself on both sides, with the leaf
`λ ys, PUnit.unit.{v}`: typed at the real environment against `∀ ys, PUnit.{v}`, which
converts to the constructor's type at the shadow. -/
theorem chain_ctor {formers : List (Key .anon)} {envT envD : Env .anon}
    (mT : EnvModelM V μ envT) (mD : EnvModelM V μ envD) (hch : Chain formers mT mD)
    {cv : ConstantVal .anon} {type' : Expr .anon} {nP nF : Nat} {T : Key .anon}
    {us : List Level} {cvT : ConstantVal .anon} {caps : IndCaps .anon}
    (hcv : ConstantValRunJ rulesJ envT cv type') (hid : ∃ a, cv.name = .id a)
    (hT : T ∈ formers) (hfT : envT.find? T = some (.indInfo cvT caps))
    (hends : EndsHead T us cvT.type.piArity type') :
    ∃ (envD' : Env .anon)
      (mT' : EnvModelM V μ
        ⟨.ctorInfo ⟨cv.name, cv.levelParams, type'⟩ nP nF :: envT.consts⟩)
      (mD' : EnvModelM V μ envD'), Chain formers mT' mD' ∧ ModelExt mT mT' := by
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr, stype, u, hst, hens⟩ := hcv
  have hst' : Infer envT .full 0 type' stype := hst
  have hens' : Red envT 0 stype (.sort u) := hens
  obtain ⟨htf', hbt'⟩ := (judgeFrames_rulesJ envT).annot_syntax hann hitf hlbt
  have hfresh : envT.find? cv.name = none := Option.isNone_iff_eq_none.mp hfind
  -- the former and its shadow
  obtain ⟨-, cv₀, l, hint, hT₀, hD₀, hr, hp⟩ := hch.shadowed T hT cvT caps hfT
  have hcvT : cv₀ = cvT :=
    (ConstantInfo.indInfo.inj (Option.some.inj (hT₀.symm.trans hfT))).1
  rw [hcvT] at hT₀ hD₀ hr hp
  -- the sort of the constructor's type
  obtain ⟨hus, hz⟩ := sort_of_endsHead (us := us) hT₀ hr _ type' 0 stype u rfl hends hst' hens'
  have hus' : us.length = cvT.levelParams.length := hus
  have hz' : Level.zeronessOf u =
      Level.zeronessOf (Level.subst cvT.levelParams us l) := hz
  -- the value `λ ys, PUnit.unit.{v}` has the type `∀ ys, PUnit.{v}`
  have hval : Infer envT .full 0
      (lamTele (.const punitUnitName [Level.subst cvT.levelParams us l]) type')
      (piTele (.const punitName [Level.subst cvT.levelParams us l]) type') :=
    infer_lamTele (env := envT)
      (w := .const punitUnitName [Level.subst cvT.levelParams us l])
      (W := .const punitName [Level.subst cvT.levelParams us l])
      (v' := Level.subst cvT.levelParams us l)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => trivial) (fun _ => rfl) rfl
      (fun d => hch.pin.unit _ .full d) (fun d => hch.pin.punit _ .io d)
      _ type' 0 stype u rfl (EndsHead.shape type' hends)
      (Expr.WScoped.of_not_hasFvar htf').fvarsBelow hbt' hst' hens' hz'
  have hwfT : ConstWF envT (.indInfo cvT {}) := mT.base2.wf _ (Env.find?_mem hT₀)
  have hlT : l.allParamsDefined cvT.levelParams = true :=
    resultSort_defined cvT.type l hr hwfT.2.1
  have husd : ∀ u' ∈ us, u'.allParamsDefined cv.levelParams = true :=
    EndsHead.levels_defined _ type' rfl hends htp
  have hvT : (Level.subst cvT.levelParams us l).allParamsDefined cv.levelParams = true :=
    Level.allParamsDefined_subst hus' husd hlT
  have hvf' : (lamTele (.const punitUnitName [Level.subst cvT.levelParams us l])
      type').hasFvar = false := lamTele_hasFvar rfl type' htf'
  have hvb' : (lamTele (.const punitUnitName [Level.subst cvT.levelParams us l])
      type').looseBVarsBounded 0 = true := lamTele_looseBVarsBounded (fun _ => rfl) type' 0 hbt'
  have hvp : (lamTele (.const punitUnitName [Level.subst cvT.levelParams us l])
      type').allLevelParamsDefined cv.levelParams = true :=
    lamTele_allLevelParamsDefined (by simp [Expr.allLevelParamsDefined, hvT]) type' htp
  obtain ⟨A, hA, hleafV, hwv, hbv, hlv⟩ := leaf_of_infer mT hvf' hvb' hvp hval
  -- the conversion, at the shadow
  have hbase : ∀ (d : Nat) (e : Expr .anon), e.getAppFn = .const T us →
      e.getAppArgs.length = cvT.type.piArity →
      DefEq envD d (.const punitName [Level.subst cvT.levelParams us l]) e :=
    fun d e h1 h2 =>
      DefEq.symm (DefEq.redL (red_shadow_apply hD₀ hr hp hus' h1 h2) DefEq.refl)
  have hde : DefEq envD 0
      (piTele (.const punitName [Level.subst cvT.levelParams us l]) type') type' :=
    defEq_piTele (fun _ _ => rfl) hbase _ type' 0 rfl hends
  have hleaf : Leaf mT.base2 cv.levelParams type' A :=
    Leaf.convert mT mD hch.acval hch.twin hleafV hwv hbv hlv htf' hbt'
      (fun ψ => type_row mT htf' hbt' hst' ψ) hde
  -- both sides store the constructor
  have hfreshD : envD.find? cv.name = none := hch.twin.fresh hfresh
  obtain ⟨mT', hacT, hextT⟩ := consMember mT
    (c₀ := .ctorInfo ⟨cv.name, cv.levelParams, type'⟩ nP nF)
    (cvA := ⟨cv.name, cv.levelParams, type'⟩) (Or.inr ⟨nP, nF, rfl⟩) hfresh hnres hpshape
    ⟨htf', htp, htr, hbt'⟩ hch.closedT hleaf
  obtain ⟨mD', hacD, -⟩ := consMember mD
    (c₀ := .ctorInfo ⟨cv.name, cv.levelParams, type'⟩ nP nF)
    (cvA := ⟨cv.name, cv.levelParams, type'⟩) (Or.inr ⟨nP, nF, rfl⟩) hfreshD hnres hpshape
    ⟨htf', htp, hch.twin.constsResolve htr, hbt'⟩ hch.closedD
    (hleaf.twin hch.acval hch.twin)
  refine ⟨_, mT', mD', ?_, hextT⟩
  exact
    { twin := hch.twin.cons_same _
      acval := by rw [hacT, hacD, hch.acval]
      shadowed := fun T' hT' cvT' caps' hf => by
        by_cases hn : cv.name = T'
        · subst hn
          exact nomatch (Option.some.inj ((Env.find?_cons_self
            (.ctorInfo ⟨cv.name, cv.levelParams, type'⟩ nP nF) envT).symm.trans hf))
        · rw [EnvExt.find?_cons_ne
            (c := .ctorInfo ⟨cv.name, cv.levelParams, type'⟩ nP nF) hn] at hf
          exact (hch.shadowed T' hT' cvT' caps' hf).cons hn hn
      closedT := EtaFamiliesClosed.cons_nonind hch.closedT hfresh
        (fun _ _ heq => nomatch heq)
      closedD := EtaFamiliesClosed.cons_nonind hch.closedD hfreshD
        (fun _ _ heq => nomatch heq)
      pin := hch.pin.mono (EnvExt.cons hfresh (fun _ => id_ne_projTableName hid _)) }

/-! ## The block -/

/-- **One member's check and its stored form.** The front door at the environment so far
(`ConstantValRunJ` over derivations), an input key, and by kind:

* a type former is stored at the empty capability record, and its annotated type is a
  syntactic telescope into a sort;
* a constructor is stored with its declared counts, and its annotated type is a syntactic
  telescope ending in a former of the block, stored, applied to as many arguments as that
  former's type has binders.

No other kind is a member. Nothing is asked about positivity, universes or parameters. -/
def PointMember (formers : List (Key .anon)) (env : Env .anon)
    (ci ciA : ConstantInfo .anon) : Prop :=
  ∃ type' : Expr .anon,
    ConstantValRunJ rulesJ env ci.toConstantVal type' ∧
    (∃ a, ci.name = .id a) ∧
    match ci with
    | .indInfo cv _ =>
      ciA = .indInfo ⟨cv.name, cv.levelParams, type'⟩ {} ∧
        ∃ l, type'.resultSort = some l
    | .ctorInfo cv nP nF =>
      ciA = .ctorInfo ⟨cv.name, cv.levelParams, type'⟩ nP nF ∧
        ∃ (T : Key .anon) (us : List Level) (cvT : ConstantVal .anon) (caps : IndCaps .anon),
          T ∈ formers ∧ env.find? T = some (.indInfo cvT caps) ∧
          EndsHead T us cvT.type.piArity type'
    | _ => False

/-- **The members, in order**, each checked at the environment the earlier ones built. -/
def PointRun (formers : List (Key .anon)) :
    Env .anon → List (ConstantInfo .anon) → Env .anon → Prop
  | env, [], env₂ => env₂ = env
  | env, ci :: rest, env₂ =>
    ∃ ciA, PointMember formers env ci ciA ∧ PointRun formers ⟨ciA :: env.consts⟩ rest env₂

/-- The chains through a run of members. -/
theorem pointRun_chain (formers : List (Key .anon)) :
    ∀ (members : List (ConstantInfo .anon)) {envT envD env₂ : Env .anon}
      (mT : EnvModelM V μ envT) (mD : EnvModelM V μ envD),
      Chain formers mT mD → PointRun formers envT members env₂ →
      ∃ mT₂ : EnvModelM V μ env₂, ModelExt mT mT₂ ∧ EtaFamiliesClosed env₂
  | [], envT, envD, env₂, mT, mD, hch, hrun => by
    obtain rfl : env₂ = envT := hrun
    exact ⟨mT, .refl, hch.closedT⟩
  | ci :: rest, envT, envD, env₂, mT, mD, hch, hrun => by
    obtain ⟨ciA, ⟨type', hcv, hid, hkind⟩, hrest⟩ := hrun
    cases ci with
    | indInfo cv caps₀ =>
      obtain ⟨rfl, l, hr⟩ := hkind
      obtain ⟨envD', mT', mD', hch', hext⟩ := chain_former mT mD hch hcv hid hr
      obtain ⟨mT₂, hext₂, hE₂⟩ := pointRun_chain formers rest mT' mD' hch' hrest
      exact ⟨mT₂, hext.trans hext₂, hE₂⟩
    | ctorInfo cv nP nF =>
      obtain ⟨rfl, T, us, cvT, caps, hT, hfT, hends⟩ := hkind
      obtain ⟨envD', mT', mD', hch', hext⟩ :=
        chain_ctor (nP := nP) (nF := nF) mT mD hch hcv hid hT hfT hends
      obtain ⟨mT₂, hext₂, hE₂⟩ := pointRun_chain formers rest mT' mD' hch' hrest
      exact ⟨mT₂, hext.trans hext₂, hE₂⟩
    | axiomInfo _ => exact False.elim hkind
    | defnInfo _ _ _ => exact False.elim hkind
    | thmInfo _ _ => exact False.elim hkind
    | recInfo _ _ _ _ => exact False.elim hkind
    | projInfo _ => exact False.elim hkind

/-- **A one-point block keeps the fold's model invariant.** At an environment that stores the
`PUnit` pin and none of the block's formers, a run of member checks extends a model whose
stored theorem values read, to one of the environment the run built. -/
theorem pointRun_modelT {formers : List (Key .anon)} {members : List (ConstantInfo .anon)}
    {env env₂ : Env .anon} (hrun : PointRun formers env members env₂)
    (hfresh : ∀ T ∈ formers, env.find? T = none) (hpin : PUnitPin env)
    (h : EnvModelT V μ env) : EnvModelT V μ env₂ := by
  obtain ⟨⟨mp, hT⟩, hE⟩ := h
  have hch : Chain formers mp mp :=
    { twin := Twin.refl env
      acval := rfl
      shadowed := fun T hT cvT caps hf => by
        rw [hfresh T hT] at hf
        exact nomatch hf
      closedT := hE
      closedD := hE
      pin := hpin }
  obtain ⟨mp₂, hext, hE₂⟩ := pointRun_chain formers members mp mp hch hrun
  exact ⟨⟨mp₂, hT.of_ext hext⟩, hE₂⟩

end IxVM.Refinement.Decl.Point
