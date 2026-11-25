import IxVMRefinement.Binding.MemberLoadPins
import IxVM.Obs.KernelRoleSpec

/-! # The inductives and constructors selected at the two standard-axiom families -/

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM (F)

set_option maxRecDepth 100000

private theorem one_ctor {role : Ix.Kernel.Role} (which : role = .iff ∨ role = .nonempty)
    {h h' result calls} (ev : ObsFn W "KernelRoleSpec::role_ctor_count" [.field (roleNum role)]
      h result h' calls) : result = .field 1 := by
  match Obs.«KernelRoleSpec::role_ctor_count».obs ev with
  | .n0 (hv14 := tag) .. =>
    rcases which with rfl | rfl <;> exact absurd (Value.field.inj tag) (by decide)
  | .n8 (he23 := out) .. | .n11 (he31 := out) .. | .n23 (he39 := out) ..
  | .n26 (he47 := out) .. => exact out
  | .other (hne42 := noIff) (hne50 := noNonempty) .. =>
    rcases which with rfl | rfl
    · exact False.elim (noIff rfl)
    · exact False.elim (noNonempty rfl)

/-- At either family role the checked value is an inductive with one constructor. -/
theorem validateMember_induct {role : Ix.Kernel.Role} (which : role = .iff ∨ role = .nonempty)
    {rc tbl addr ci : SourceValue F} {h h' result calls}
    (path : Obs.«KernelRoles::validate_member».Path rc tbl (.field (roleNum role)) addr ci
      h result h' calls) :
    ∃ nl ty np ni unsafeFlag block idx, ci = .construct kciEnum "Induct"
      [nl, ty, np, ni, .field 1, unsafeFlag, block, idx] := by
  have table : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.role_member_kind.body)
      (roleNum role) = some 0 := by rcases which with rfl | rfl <;> decide +kernel
  match path with
  | .n0 (hv128 := shape) (ev208 := count) (heq217 := pin) .. =>
    rw [pin.trans (one_ctor which count)] at shape
    exact ⟨_, _, _, _, _, _, _, shape⟩
  | .n1 (ev101 := kind) .. | .n2 (ev101 := kind) .. | .n3 (ev101 := kind) ..
  | .n4 (ev101 := kind) .. | .n5 (ev101 := kind) .. | .n6 (ev101 := kind) ..
  | .n7 (ev101 := kind) .. => exact absurd (Value.field.inj (memberKind_of_table table kind)) (by decide)

/-- The family and the parameter and field counts of the two constructors. -/
inductive StdCtorPin : Ix.Kernel.Role → Ix.Kernel.Role → Nat → Prop where
  | iff : StdCtorPin .iffIntro .iff 2
  | nonempty : StdCtorPin .nonemptyIntro .nonempty 1

private theorem ctor_spec {role family : Ix.Kernel.Role} {n : Nat} (pin : StdCtorPin role family n)
    {h h' result calls} (ev : ObsFn W "KernelRoleSpec::role_ctor_of" [.field (roleNum role)]
      h result h' calls) :
    result = .tuple [.field (roleNum family), .field 0, .field (n : F), .field (n : F)] := by
  match Obs.«KernelRoleSpec::role_ctor_of».obs ev with
  | .n2 (hv14 := tag) .. | .n9 (hv52 := tag) .. | .n12 (hv90 := tag) .. =>
    cases pin <;> exact absurd (Value.field.inj tag) (by decide)
  | .n24 (hv128 := tag) (he135 := out) .. =>
    cases pin with
    | iff => exact out
    | nonempty => exact absurd (Value.field.inj tag) (by decide)
  | .n27 (hne162 := notIff) (he173 := out) .. =>
    cases pin with
    | iff => exact False.elim (notIff rfl)
    | nonempty => exact out
  | .other (hne162 := notIff) (hne200 := notNonempty) .. =>
    cases pin with
    | iff => exact False.elim (notIff rfl)
    | nonempty => exact False.elim (notNonempty rfl)

/-- At either constructor the loaded value has the required parameter and field
counts. Its index is zero and the validator obtains the address of its parent
inductive from the same role table. -/
theorem validateMember_ctor {role family : Ix.Kernel.Role} {n : Nat} (pin : StdCtorPin role family n)
    {rc tbl addr ci : SourceValue F} {h h' result calls}
    (path : Obs.«KernelRoles::validate_member».Path rc tbl (.field (roleNum role)) addr ci
      h result h' calls) :
    ∃ nl ty block idx unsafeFlag address pre post cs,
      ci = .construct kciEnum "Ctor"
        [nl, ty, block, idx, .field 0, .field (n : F), .field (n : F), unsafeFlag] ∧
      ObsFn W "KernelRoles::role_bound_addr" [tbl, .field (roleNum family)] pre address post cs := by
  have table : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.role_member_kind.body)
      (roleNum role) = some 1 := by cases pin <;> decide +kernel
  match path with
  | .n1 (hv261 := shape) (ev319 := spec) (ev389 := lookup) (heq563 := checkIdx)
      (heq591 := checkP) (heq619 := checkF) .. =>
    have ans := Value.tuple.inj (ctor_spec pin spec)
    simp only [List.cons.injEq, and_true] at ans
    rw [checkIdx.trans ans.2.1, checkP.trans ans.2.2.1, checkF.trans ans.2.2.2] at shape
    rw [ans.1] at lookup
    exact ⟨_, _, _, _, _, _, _, _, _, shape, lookup⟩
  | .n0 (ev101 := kind) .. | .n2 (ev101 := kind) .. | .n3 (ev101 := kind) ..
  | .n4 (ev101 := kind) .. | .n5 (ev101 := kind) .. | .n6 (ev101 := kind) ..
  | .n7 (ev101 := kind) .. => exact absurd (Value.field.inj (memberKind_of_table table kind)) (by decide)

end IxVM.Refinement.Binding
