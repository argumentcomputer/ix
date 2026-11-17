import IxVMRefinement.Assembly.NativeBlockRegister
import IxVMRefinement.Assembly.NativeBlockFacts
import IxVMRefinement.Assembly.TypingBasisInv
import IxVMRefinement.Decl.LevelRenLift
import IxVMRefinement.Decl.PrefixInv

/-! # The level clauses beside the model invariant

`ThmLevels` (a stored theorem's value mentions only the theorem's level parameters) is an
environment-only clause the fold carries beside the invariant, as the registry and the key
clauses are: it holds at the environment of the pins (`thmLevels_basisEnv`), a value step keeps
it (`keepsValuesJ_thmLevels`, `keepsValuesKeyed_thmLevels`), a native block's install keeps it
(`NativeNoRecFacts.thmLevels`, and `Ix.Kernel.Model.thmLevels_declRunJ` for every declaration
step over derivations), and the late recursor's step keeps it (`Ix.Kernel.Model.thmLevels_late`).

`constantValCheckJ_of_prefix_perm` is the declaration front's check at any permutation of the
positions, from the prefix invariant and the two level clauses (`ThmLevels`, `StoreAr`).
-/

universe u

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel (ConstantInfo ConstantVal ThmLevels StoreAr)
open IxVM.Refinement.TableInhabit (basisEnv)

/-- Whether a stored constant is a theorem. -/
def isThmInfo : ConstantInfo .anon → Bool
  | .thmInfo _ _ => true
  | _ => false

/-- The environment of the pins stores no theorem. -/
theorem basisEnv_noThm : basisEnv.consts.all (fun c => !isThmInfo c) = true := by
  decide

/-- **`ThmLevels` holds at the environment of the pins.** -/
theorem thmLevels_basisEnv : ThmLevels basisEnv := by
  intro n cv v hf
  have hm := (basisEnv_find_mem hf).1
  have h := List.all_eq_true.mp basisEnv_noThm _ hm
  simp [isThmInfo] at h

/-- **A value step keeps `ThmLevels`.** -/
theorem keepsValuesJ_thmLevels : KeepsValuesJ (ThmLevels (md := .anon)) :=
  fun _ _ _ h _ _ _ hd => Ix.Kernel.Model.thmLevels_declRunJ h hd

/-- **A value step at the key of a 32-byte address keeps `ThmLevels`** (the skeleton's form). -/
theorem keepsValuesKeyed_thmLevels (t : Ix.Kernel.RoleTable) :
    KeepsValuesKeyed t (ThmLevels (md := .anon)) :=
  keepsValuesJ_thmLevels.keyed t

/-- **A native block's install keeps `ThmLevels`.** -/
theorem NativeNoRecFacts.thmLevels {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : Ix.Kernel.Semantics.NativeFam .anon} (hpin : Ix.Kernel.basisPinHit blk = none)
    (h : NativeNoRecFacts env env₂ blk nP p₀ fam) (hT : ThmLevels env) : ThmLevels env₂ :=
  Ix.Kernel.Model.thmLevels_declRunJ hT (h.declRunJ hpin)

/-- **The late recursor's step keeps `ThmLevels`** (`Ix.Kernel.Model.thmLevels_late` at the
rules' package). -/
theorem thmLevels_lateRec {env env₂ : Ix.Kernel.Env .anon}
    {fam : Ix.Kernel.Semantics.NativeFam .anon} {cvR : ConstantVal .anon} {mI rP : Nat}
    {rules : List (Ix.Kernel.RecRule .anon)} (hT : ThmLevels env)
    (hrun : Ix.Kernel.Semantics.DeclNativeRecLateRunJ Ix.Kernel.Model.rulesJ env fam cvR mI rP
      rules env₂) : ThmLevels env₂ :=
  Ix.Kernel.Model.thmLevels_late hT hrun

/-- **The declaration front's check at the declared level parameters, from the prefix
invariant and the two level clauses**: `Decl.constantValCheckJ_of_scoped` with no `PosSortLift`
premise, for any permutation of the positions (the large eliminator's `k :: List.range k`
included). -/
theorem constantValCheckJ_of_prefix_perm {E : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {lim : Option Nat} {c : ScopedCtx}
    {Γ : Nat → KExpr} {cv cv' : ConstantVal .anon}
    {nl ty rc types r₁ r₂ : SourceValue F} {h h₁ h₂ h₃ : Heap F} {cs₁ cs₂ : List (Call F)}
    (hP : Decl.PrefixInv.{u} E t lim c.env) (hX : ThmLevels c.env ∧ StoreAr c.env)
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
  Decl.constantValCheckJ_of_scoped_perm hvs hv hlbd hfv hfresh hbasis hshape hP.store.store
    hX.1 hX.2 ev_ws ext hrc hty hef hlf hgood ev_sort

end IxVM.Refinement.Typing
