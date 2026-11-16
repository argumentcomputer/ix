import IxVMRefinement.Decl.NativePrelude
import IxVMRefinement.Decl.NativeStage

/-! # Native former shape observations at actual capability stages -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (Expr ConstantVal)

/-- The actual former guard supplies either its raw telescope or a nonzero index count.
This is precisely the arity information needed to stage the actual native capabilities. -/
theorem former_decl_ok_shape {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {params indices : Nat} {type : KExpr}
    {typePtr count blockArg index sortLevel result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (bound : params + indices < 18446744069414584321)
    (represented : TmExact κ 0 Γ h 0 type typePtr)
    (observed : ObsFn W "KernelCheck::former_decl_ok"
      [typePtr, .field (params : F), .field (indices : F), count, blockArg, index, sortLevel]
      h result h' calls) :
    (∃ binders level, type.stripPis (params + indices) = some (binders, .sort level) ∧
      binders.length = params + indices) ∨ indices ≠ 0 := by
  match Obs.«KernelCheck::former_decl_ok».obs observed with
  | .n1 (v17 := sum) (op38 := added) (ev15 := telescope) .. =>
    rw [evalBinOp_add_nat params indices added] at telescope
    obtain ⟨_, binders, level, shape, length⟩ :=
      former_is_tele_one_bounded_spec (params + indices) bound represented telescope
    exact .inl ⟨binders, level, shape, length⟩
  | .other (ev78 := zeroTest) (heq93 := resultEq) .. =>
    subst resultEq
    obtain ⟨isZero, _⟩ := Lib.is_zero_spec zeroTest
    right
    intro zero
    subst indices
    simp at isZero

/-- The observed guard discharges the stage arity premise while retaining the supplied
native shape and recursion verdict. The base invariants and checked type properties are preserved. -/
theorem coreEnvFacts_consNativeCapsAt_of_guard {c : Ctx} {cv : ConstantVal .anon}
    {shape : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    {typePtr count blockArg index sortLevel result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (facts : CoreEnvFacts c) (fresh : c.env.find? cv.name = none)
    (keyShape : cv.name.isProjFnShape = false)
    (typeShape : cv.type.hasFvar = false ∧ cv.type.allLevelParamsDefined cv.levelParams = true ∧
      cv.type.constsResolve c.env = true ∧ cv.type.looseBVarsBounded 0 = true)
    (bound : shape.nP + shape.nIdx < 18446744069414584321)
    (represented : TmExact c.κ 0 (fun _ => default) h 0 cv.type typePtr)
    (observed : ObsFn W "KernelCheck::former_decl_ok"
      [typePtr, .field (shape.nP : F), .field (shape.nIdx : F), count, blockArg, index, sortLevel]
      h result h' calls) :
    CoreEnvFacts { c with env := ⟨.indInfo cv (Ix.Kernel.nativeCapsAt shape isRec) :: c.env.consts⟩ } := by
  rcases former_decl_ok_shape bound represented observed with ⟨binders, level, telescope, _⟩ | indexed
  · exact coreEnvFacts_consNativeCapsAt facts fresh keyShape typeShape telescope
  · exact coreEnvFacts_consNativeCapsAt_indexed facts fresh keyShape typeShape indexed

end IxVM.Refinement.Decl
