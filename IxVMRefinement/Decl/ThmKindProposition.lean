import IxVMRefinement.Decl.ThmKindStep
import IxVMRefinement.Decl.ReferenceProposition

/-! # A theorem row from prefix checking and final proposition evidence

A genuine frame identifies the final proposition check with the original annotated type.
The checked value is then transported through the local theorem-kind simulation. The frame
and its raw expression support remain explicit structural obligations.
-/

namespace IxVM.Refinement.Decl.ThmKind

open Ix.Kernel Ix.Kernel.Semantics
open IxVM.Refinement.Assembly

/-- Final admission's proposition evidence yields the row for the actual prefix annotation. -/
theorem value_typed_from_final {P : KeyScope .anon} {before final after : Env .anon}
    (frame : EnvFrame P before final) (simulation : ThmSimAt before after)
    {fuel : Nat} {cv : ConstantVal .anon} {rawValue type value : Expr .anon}
    (good : cv.type.Good P)
    (first : ConstantValRun .verified fuel before cv type)
    (checked : ValueFrontRun .verified fuel before cv rawValue type value)
    (proposition : ∃ propFuel type' st u,
      (fueledOps .verified propFuel).annotate final 0 cv.type = .ok type' ∧
      (fueledOps .verified propFuel).inferType final 0 type' = .ok st ∧
      (fueledOps .verified propFuel).ensureSort final 0 st = .ok u ∧ u.isZero = true) :
    ThmValueTyped after { cv with type } value := by
  obtain ⟨_, _, _, _, _, _, annotated, _, _, st, u, inferred, sorted⟩ := first
  obtain ⟨propFuel, type', propSt, propU, propAnnotation, propInference, propSort, zero⟩ := proposition
  have prefixZero := proposition_at_prefix frame good annotated inferred sorted
    propAnnotation propInference propSort zero
  exact value_typed_of_runs simulation checked inferred sorted prefixZero

end IxVM.Refinement.Decl.ThmKind
