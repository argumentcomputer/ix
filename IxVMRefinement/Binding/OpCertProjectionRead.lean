import IxVMRefinement.Binding.SubstConstProj
import IxVMRefinement.Obs.KernelRoles4

/-! # The projection check in an operation's proof-evidence entry -/

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core

/-- A successful proof-evidence entry loads the named theorem, substitutes in its value, and
checks the substituted pointer at depth zero. At each heap extending the substitution output,
the operation's address is absent from the projection heads of that specific input value. -/
theorem validate_op_proof_noProj {e rest rc tbl role a v es k r thm : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {b : Bytes.Address}
    (path : Obs.«KernelRoles::validate_op_equations».Seg1 e rest rc tbl role a v es k h r h' cs)
    (proof : e = .construct "KernelRoles::RoleEvidence" "Proof" [thm])
    (ra : Bytes.RepAddressRef addrTy h b a) :
    ∃ (beforeGet loaded substituted checked : Heap F) (ci ty pval out unit : SourceValue F)
      (getCalls substCalls scopeCalls : List (Call F)),
      ObsFn W "Ingress::get_ci" [thm] beforeGet ci loaded getCalls ∧
      loadValue loaded ci = .ok (.construct kciEnum "Thm" [.field 0, ty, pval]) ∧
      ObsFn W "KernelSubst::subst_const" [pval, a, v] loaded out substituted substCalls ∧
      ObsFn W "KernelCheck::validate_expr_well_scoped" [out, .field 0, .field 0]
        substituted unit checked scopeCalls ∧
      (⟨"KernelSubst::subst_const", [pval, a, v], loaded⟩ : Call F) ∈ cs ∧
      ∀ H, Heap.Extends substituted H → ¬ ProjIn H pval b := by
  match path with
  | .n0_Defeq (hv83 := defeq) .. =>
    rw [proof] at defeq
    exact absurd (Value.construct.inj defeq).2.1 (by decide)
  | .n0_Proof (heq379 := bad) .. | .other_Defeq (heq431 := bad) ..
  | .other_Proof_Defn_other (heq1257 := bad) .. | .other_Proof_other (heq1904 := bad) .. =>
    exact (zero_ne_one (Value.field.inj bad)).elim
  | .other_Proof_Defn_Theorem (ev56 := mode) (hv442 := evidence) (ev462 := getRecord)
      (ev631 := get) (ld625 := ld) (heq688 := levels) (ev702 := sub) (ev740 := scope)
      (hc1225 := calls) .. =>
    rw [proof] at evidence
    injection evidence with _ _ args
    have same := (List.cons.inj args).1
    rw [← same] at get
    rw [levels] at ld
    refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, get, ld, sub, scope, ?_, ?_⟩
    · rw [calls]
      simp
    · intro H ext
      have ext0 := mode.heap_extends.trans (getRecord.heap_extends.trans get.heap_extends)
      exact subst_const_path_noProj (Obs.«KernelSubst::subst_const».obs sub) ext
        (Bytes.repAddressRef_heapMono₂ addrTy (ext0.trans (sub.heap_extends.trans ext)) ra)

end IxVM.Refinement.Binding
