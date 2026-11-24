import IxVMRefinement.Decl.NativeCommon
import IxCK.Kernel.Model.LevelRen
import IxCK.Kernel.Model.ThmLevels

/-! # Typing and conversion at the declared level parameters, from the positional run

The circuit checks a declaration's type with its level parameters renamed to positions
(`posOf`). Every declaration the reader produces has the positions themselves as parameters,
except a large eliminator (`k :: List.range k`, the motive universe first). The rules' transport
along a renaming of level parameters (`Ix.Kernel.Rules.infer_lr`, `IxCK/Kernel/Model/LevelRen.lean`)
undoes `posOf` for any permutation of the positions:

* `PosSortLift.of_perm`: the sort certificate at the declared parameters, from the positional
  one, in an environment satisfying the store invariant, `ThmLevels` and `StoreAr`;
* `posDefEq_lift`: a conversion at the declared parameters from the positional one, for
  arity-correct terms;
* `constantValCheckJ_of_scoped_perm`: the declaration front's check, with these store facts
  in place of a `PosSortLift` premise.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel (Expr Level LevelParam ConstantVal Env LvStore StoreAr ThmLevels)
open Ix.Kernel.Rules (Infer Red DefEq LvRen)
open Ix.Kernel.Semantics (ConstantValCheckJ)
open Ix.Kernel.Model (rulesJ)

/-- **The renaming that undoes `posOf ps`.** -/
theorem lvRen_posInv {env : Env .anon} (hS : Ix.Kernel.Open.StoreInv env) (hT : ThmLevels env)
    (hA : StoreAr env) (ps : List LevelParam) :
    LvRen env (List.range ps.length) (ps.map Level.param) :=
  ⟨Level.IsRen.map_param ps, LvStore.of hS hT, hA⟩

/-- **The sort certificate at the declared level parameters** (a large eliminator's included),
from the positional one. Replaces the `PosSortLift` hypotheses of the earlier routes. -/
theorem PosSortLift.of_perm {env : Env .anon} {cv' : ConstantVal .anon}
    (hS : Ix.Kernel.Open.StoreInv env) (hT : ThmLevels env) (hA : StoreAr env)
    (hfv : cv'.type.hasFvar = false)
    (hp : cv'.levelParams.Perm (List.range cv'.levelParams.length)) : PosSortLift env cv' := by
  intro sty₀ u₀ hinf hred
  have h := lvRen_posInv hS hT hA cv'.levelParams
  have hfv' : (posOf cv'.levelParams cv'.type).hasFvar = false := by
    unfold posOf
    rw [Ix.Kernel.Expr.hasFvar_instantiateLevelParams]
    exact hfv
  obtain ⟨har, hinf'⟩ := Ix.Kernel.Rules.Infer.lvRen_closed h hinf hfv'
  have hred' := (Ix.Kernel.Rules.Red.lvRen h hred har).2
  rw [posOf_perm_inv hp] at hinf'
  exact ⟨_, _, hinf', hred'⟩

/-- `PosSortLift.of_perm` read by a package `rulesJ` maps into. -/
theorem PosSortLiftFor.of_perm {J : Ix.Kernel.Semantics.Judgements .anon}
    (M : JudgementsMap rulesJ J) {env : Env .anon} {cv' : ConstantVal .anon}
    (hS : Ix.Kernel.Open.StoreInv env) (hT : ThmLevels env) (hA : StoreAr env)
    (hfv : cv'.type.hasFvar = false)
    (hp : cv'.levelParams.Perm (List.range cv'.levelParams.length)) :
    PosSortLiftFor J env cv' := by
  intro sty₀ u₀ hinf hred
  obtain ⟨sty, u, h1, h2⟩ := PosSortLift.of_perm hS hT hA hfv hp sty₀ u₀ hinf hred
  exact ⟨sty, u, M.infer h1, M.sort h2⟩

/-- **A conversion at the declared level parameters**, from the positional one, for terms that
apply every stored constant at its own number of level parameters. -/
theorem posDefEq_lift {env : Env .anon} (hS : Ix.Kernel.Open.StoreInv env) (hT : ThmLevels env)
    (hA : StoreAr env) {ps : List LevelParam} (hp : ps.Perm (List.range ps.length)) {d : Nat}
    {a b : Expr .anon} (ha : Ix.Kernel.Expr.arOk env a = true)
    (hb : Ix.Kernel.Expr.arOk env b = true)
    (hd : DefEq env d (posOf ps a) (posOf ps b)) : DefEq env d a b := by
  have h := lvRen_posInv hS hT hA ps
  have ha' : Ix.Kernel.Expr.arOk env (posOf ps a) = true := by
    unfold posOf; rw [Ix.Kernel.LevelRen.arOk_inst]; exact ha
  have hb' : Ix.Kernel.Expr.arOk env (posOf ps b) = true := by
    unfold posOf; rw [Ix.Kernel.LevelRen.arOk_inst]; exact hb
  have hd' := Ix.Kernel.Rules.DefEq.lvRen h hd ha' hb'
  rw [posOf_perm_inv hp, posOf_perm_inv hp] at hd'
  exact hd'

/-- **The declaration front's check at the declared level parameters**, for any permutation
of the positions: `constantValCheckJ_of_scoped` with the store facts in place of `PosSortLift`. -/
theorem constantValCheckJ_of_scoped_perm {c : ScopedCtx}
    {Γ : Nat → KExpr} {cv cv' : ConstantVal .anon}
    {nl ty rc types r₁ r₂ : SourceValue F} {h h₁ h₂ h₃ : Heap F} {cs₁ cs₂ : List (Call F)}
    (hvs : IxVM.Consistency.ValStored cv' cv)
    (hv : ValRepExact c.κ h nl ty cv')
    (hlbd : cv.type.looseBVarsBounded 0 = true)
    (hfv : cv.type.hasFvar = false)
    (hfresh : c.env.find? cv.name = none)
    (hbasis : Ix.Kernel.reservedBasisNames.contains cv.name = false)
    (hshape : cv.name.isProjFnShape = false)
    (hstore : Ix.Kernel.Open.StoreInv c.env)
    (hthm : ThmLevels c.env) (har : StoreAr c.env)
    (ev_ws : ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h r₁ h₁ cs₁)
    (ext : Heap.Extends h h₂)
    (hrc : RCRep c.t c.lim h₂ rc) (hty : TypesRep c.κ Γ h₂ 0 types)
    (hef : CoreEnvFacts c.toCtx) (hlf : ScopedLoadFacts c) (hgood : CoreGood c cs₂)
    (ev_sort : ObsFn W "KernelInfer::k_ensure_sort" [rc, ty, types] h₂ r₂ h₃ cs₂) :
    ConstantValCheckJ rulesJ c.env cv cv' ∧
      ∃ sty₀ u₀ ℓ,
        Infer c.env .full 0 (posOf cv'.levelParams cv'.type) sty₀ ∧
        Red c.env 0 sty₀ (.sort u₀) ∧
        RepKLevel h₃ ℓ r₂ ∧ LvEq u₀ ℓ :=
  constantValCheckJ_of_scoped hvs hv hlbd hfv hfresh hbasis hshape hstore
    (PosSortLift.of_perm hstore hthm har (annotates_hasFvar_false hvs.2.2 hfv) hv.2.2.1)
    ev_ws ext hrc hty hef hlf hgood ev_sort

end IxVM.Refinement.Decl
