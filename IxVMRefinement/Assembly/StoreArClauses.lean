import IxVMRefinement.Assembly.LevelClauses
import IxC.Kernel.Model.StoreArNative

/-! # The arity clause beside the model invariant

`Ix.Kernel.Model.StoreArR` (every stored term applies every stored constant at its own number of
level parameters and resolves; a stored comparison of `Nat` finds the `Bool` values pinned) is
the carried form of `StoreAr`. With `ThmLevels` it makes `LvClauses`, the one environment clause
the recursor step's level transport reads beside the prefix invariant:

* at the environment of the pins: `storeArR_basisEnv` (decided over the nineteen pins),
  `lvClauses_basisEnv`;
* along a value step: `keepsValuesJ_storeArR`, `keepsValuesKeyed_storeArR`,
  `keepsValuesJ_lvClauses`, `keepsValuesKeyed_lvClauses`;
* along a native block's install: `NativeNoRecFacts.storeArR`, `NativeNoRecFacts.lvClauses`;
* the declaration front's check at any permutation of the positions from the prefix invariant
  and `LvClauses`: `constantValCheckJ_of_prefix_lv`.
-/

universe u

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel (ConstantInfo ConstantVal ThmLevels StoreAr Expr RecRule)
open Ix.Kernel.Model (StoreArR ConstArR ArRes)
open IxVM.Refinement.TableInhabit (basisEnv)

/-! ## The environment of the pins, decided -/

/-- `ArRes`, decided. -/
def arResB (env : Ix.Kernel.Env .anon) (e : Expr .anon) : Bool :=
  Expr.arOk env e && e.constsResolve env

theorem arRes_of_arResB {env : Ix.Kernel.Env .anon} {e : Expr .anon}
    (h : arResB env e = true) : ArRes env e := by
  simp only [arResB, Bool.and_eq_true] at h
  exact ⟨h.1, h.2⟩

/-- A rule's right-hand side is arity-correct and resolves, and the rule is not nested. -/
def ruleArB (env : Ix.Kernel.Env .anon) (rl : RecRule .anon) : Bool :=
  arResB env rl.rhs &&
    (match rl.fire with
     | .nested _ _ => false
     | _ => true)

/-- `ConstArR`, decided where a projection table and a nested rule do not occur. -/
def constArRB (env : Ix.Kernel.Env .anon) : ConstantInfo .anon → Bool
  | .axiomInfo cv => arResB env cv.type
  | .defnInfo cv v _ => arResB env cv.type && arResB env v
  | .thmInfo cv v => arResB env cv.type && arResB env v
  | .indInfo cv _ => arResB env cv.type
  | .ctorInfo cv _ _ => arResB env cv.type
  | .recInfo cv _ _ rules => arResB env cv.type && rules.all (ruleArB env)
  | .projInfo _ => false

theorem constArR_of_constArRB {env : Ix.Kernel.Env .anon} {c : ConstantInfo .anon}
    (h : constArRB env c = true) : ConstArR env c := by
  cases c with
  | axiomInfo cv =>
    simp only [constArRB] at h
    exact Ix.Kernel.Model.ConstArR.of_axiom (arRes_of_arResB h)
  | defnInfo cv v hint =>
    simp only [constArRB, Bool.and_eq_true] at h
    exact Ix.Kernel.Model.ConstArR.of_defn (arRes_of_arResB h.1) (arRes_of_arResB h.2)
  | thmInfo cv v =>
    simp only [constArRB, Bool.and_eq_true] at h
    exact Ix.Kernel.Model.ConstArR.of_thm (arRes_of_arResB h.1) (arRes_of_arResB h.2)
  | indInfo cv caps =>
    simp only [constArRB] at h
    exact Ix.Kernel.Model.ConstArR.of_ind (arRes_of_arResB h)
  | ctorInfo cv nP nF =>
    simp only [constArRB] at h
    exact Ix.Kernel.Model.ConstArR.of_ctor (arRes_of_arResB h)
  | recInfo cv mI rP rules =>
    simp only [constArRB, Bool.and_eq_true, List.all_eq_true] at h
    exact {
      type := arRes_of_arResB h.1
      defn := fun _ _ _ he => nomatch he
      thm := fun _ _ he => nomatch he
      rhs := fun cv' mI' rP' rules' he rl hrl => by
        cases he
        have hr := h.2 rl hrl
        simp only [ruleArB, Bool.and_eq_true] at hr
        refine ⟨arRes_of_arResB hr.1, fun lvls pins hfire => ?_⟩
        have h2 := hr.2
        rw [hfire] at h2
        simp at h2
      proj := fun _ he => nomatch he }
  | projInfo tbl => simp [constArRB] at h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Every pin's stored terms are arity-correct and resolve (decided). -/
theorem basisEnv_constArRB : basisEnv.consts.all (constArRB basisEnv) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- No comparison of `Nat` is among the pins (decided). -/
theorem basisEnv_noCmp :
    ((basisEnv.find? (Ix.Kernel.natBeqName : Ix.Kernel.Key .anon)).isNone &&
      (basisEnv.find? (Ix.Kernel.natBleName : Ix.Kernel.Key .anon)).isNone) = true := by
  decide +kernel

/-- **`StoreArR` holds at the environment of the pins.** -/
theorem storeArR_basisEnv : StoreArR basisEnv where
  const := fun {_ ci} hf =>
    constArR_of_constArRB (List.all_eq_true.mp basisEnv_constArRB ci (basisEnv_find_mem hf).1)
  bool := fun {c} hst hcb => by
    exfalso
    have hn := basisEnv_noCmp
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hn
    unfold Ix.Kernel.natOpStored at hst
    rcases hcb with rfl | rfl
    · rw [hn.1] at hst
      simp at hst
    · rw [hn.2] at hst
      simp at hst

/-! ## Value steps -/

/-- **A value step keeps `StoreArR`.** -/
theorem keepsValuesJ_storeArR : KeepsValuesJ (StoreArR (md := .anon)) :=
  fun _ _ _ h hfresh hval _ hd =>
    Ix.Kernel.Model.storeArR_declRunJ_value h hfresh hval hd rfl

/-- **A value step at the key of a 32-byte address keeps `StoreArR`** (the skeleton's form). -/
theorem keepsValuesKeyed_storeArR (t : Ix.Kernel.RoleTable) :
    KeepsValuesKeyed t (StoreArR (md := .anon)) :=
  keepsValuesJ_storeArR.keyed t

/-! ## A native block's install -/

/-- **A native block's install keeps `StoreArR`** (`Ix.Kernel.Model.storeArR_nativeNoRec`). -/
theorem NativeNoRecFacts.storeArR {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : Ix.Kernel.Semantics.NativeFam .anon} (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hA : StoreArR env) : StoreArR env₂ :=
  Ix.Kernel.Model.storeArR_nativeNoRec hA h.runJ

/-! ## The carried clause -/

/-- **The level clauses the fold carries beside the invariant**: a stored theorem's value
mentions only its own level parameters (`ThmLevels`), and the stored terms are arity-correct and
resolve (`StoreArR`). -/
abbrev LvClauses (env : Ix.Kernel.Env .anon) : Prop :=
  ThmLevels env ∧ StoreArR env

/-- The clauses give `StoreAr`. -/
theorem LvClauses.storeAr {env : Ix.Kernel.Env .anon} (h : LvClauses env) : StoreAr env :=
  h.2.toStoreAr

/-- **`LvClauses` holds at the environment of the pins.** -/
theorem lvClauses_basisEnv : LvClauses basisEnv :=
  ⟨thmLevels_basisEnv, storeArR_basisEnv⟩

/-- **A value step keeps `LvClauses`.** -/
theorem keepsValuesJ_lvClauses : KeepsValuesJ LvClauses :=
  keepsValuesJ_thmLevels.and keepsValuesJ_storeArR

/-- **A value step at the key of a 32-byte address keeps `LvClauses`.** -/
theorem keepsValuesKeyed_lvClauses (t : Ix.Kernel.RoleTable) : KeepsValuesKeyed t LvClauses :=
  keepsValuesJ_lvClauses.keyed t

/-- **A native block's install keeps `LvClauses`.** -/
theorem NativeNoRecFacts.lvClauses {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : Ix.Kernel.Semantics.NativeFam .anon} (hpin : Ix.Kernel.basisPinHit blk = none)
    (h : NativeNoRecFacts env env₂ blk nP p₀ fam) (hX : LvClauses env) : LvClauses env₂ :=
  ⟨h.thmLevels hpin hX.1, h.storeArR hX.2⟩

/-! ## The final form -/

/-- **The declaration front's check at the declared level parameters, from the prefix
invariant and the carried level clauses**: `Decl.constantValCheckJ_of_scoped` with no
`PosSortLift` premise, for any permutation of the positions (the large eliminator's
`k :: List.range k` included). -/
theorem constantValCheckJ_of_prefix_lv {E : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {lim : Option Nat} {c : ScopedCtx}
    {Γ : Nat → KExpr} {cv cv' : ConstantVal .anon}
    {nl ty rc types r₁ r₂ : SourceValue F} {h h₁ h₂ h₃ : Heap F} {cs₁ cs₂ : List (Call F)}
    (hP : Decl.PrefixInv.{u} E t lim c.env) (hX : LvClauses c.env)
    (hvs : IxVM.Consistency.ValStored cv' cv)
    (hv : Decl.ValRepExact c.κ h nl ty cv')
    (hlbd : cv.type.looseBVarsBounded 0 = true)
    (hfv : cv.type.hasFvar = false)
    (hfresh : c.env.find? cv.name = none)
    (hbasis : Ix.Kernel.reservedBasisNames.contains cv.name = false)
    (hshape : cv.name.isProjFnShape = false)
    (ev_ws : ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h r₁ h₁ cs₁)
    (ext : Heap.Extends h h₂)
    (hrc : RCRep c.t c.lim h₂ rc) (hty : TypesRep c.κ Γ h₂ 0 types)
    (hef : CoreEnvFacts c.toCtx) (hlf : ScopedLoadFacts c) (hgood : CoreGood c cs₂)
    (ev_sort : ObsFn W "KernelInfer::k_ensure_sort" [rc, ty, types] h₂ r₂ h₃ cs₂) :
    Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ c.env cv cv' ∧
      ∃ sty₀ u₀ ℓ,
        Ix.Kernel.Rules.Infer c.env .full 0 (posOf cv'.levelParams cv'.type) sty₀ ∧
        Ix.Kernel.Rules.Red c.env 0 sty₀ (.sort u₀) ∧
        RepKLevel h₃ ℓ r₂ ∧ LvEq u₀ ℓ :=
  constantValCheckJ_of_prefix_perm hP ⟨hX.1, hX.storeAr⟩ hvs hv hlbd hfv hfresh hbasis hshape
    ev_ws ext hrc hty hef hlf hgood ev_sort

end IxVM.Refinement.Typing
