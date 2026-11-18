import IxVMRefinement.Assembly.TypingRecLateStored

/-! # The recursor arm of `check_const`, in full

`check_const_rec_route` exports the scope check and the member check of the `Rec` arm. The late
step also reads two more of the arm's facts:

* the record declares one motive (the native route asserts `n_mot = 1` before the member check;
  the modeled route runs the family check at the value's block field, which `hfr` refuses, as
  it is at a standalone recursor record: `Claim.familyCheckRefused_of_recr`);
* the type is checked as a sort (`k_ensure_sort(rc, ty, [])`, in the empty context allocated
  after the scope check), the run from which the recursor's declared type is checked at the
  prefix (`ConstantValCheckJ`).

`check_const_rec_arm` gives both with the runs of `check_const_rec_route`, the heaps in order:
the check's heap, the scope check's, the sort check's (after the empty context), the member
check's.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency

/-- **The `Rec` arm of `check_const`, in full**: one motive; the scope check of the type at a
heap after the check's; the sort check of the type in the empty context allocated after the
scope check, its calls among the check's; the member check at a heap after the sort check's,
its calls among the check's. -/
theorem check_const_rec_arm
    {rc levels type parameters indices motives minors rules k unsafeFlag block position addr
      result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::check_const"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], addr] h result h' calls)
    (hfr : Claim.FamilyCheckRefused rc block h calls) :
    motives = .field 1 ∧
    ∃ (scopeBefore scopeAfter sortAfter memberHeap : Heap F)
      (scopeResult sortResult : SourceValue F)
      (scopeCalls sortCalls memberCalls : List (Call F)),
      Heap.Extends h scopeBefore ∧
      ObsFn Obs.W "KernelCheck::validate_expr_well_scoped" [type, .field 0, levels]
        scopeBefore scopeResult scopeAfter scopeCalls ∧
      (⟨"KernelCheck::validate_expr_well_scoped", [type, .field 0, levels], scopeBefore⟩ :
        Call F) ∈ calls ∧
      ObsFn Obs.W "KernelInfer::k_ensure_sort"
        [rc, type, .ptr (.enum Core.kexprListEnum) scopeAfter.length]
        (scopeAfter ++ [.construct Core.kexprListEnum "Nil" []]) sortResult sortAfter sortCalls ∧
      (⟨"KernelInfer::k_ensure_sort",
        [rc, type, .ptr (.enum Core.kexprListEnum) scopeAfter.length],
        scopeAfter ++ [.construct Core.kexprListEnum "Nil" []]⟩ : Call F) ∈ calls ∧
      (∀ cl ∈ sortCalls, cl ∈ calls) ∧
      Heap.Extends sortAfter memberHeap ∧
      ObsFn Obs.W "KernelCheck::check_recursor_member"
        [rc, .construct "KernelTypes::KConstantInfo" "Rec"
          [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
            position], addr] memberHeap result h' memberCalls ∧
      (∀ cl ∈ memberCalls, cl ∈ calls) := by
  match Obs.«KernelCheck::check_const».obs observed with
  | .Axiom_n1 (hv37 := shape) ..
  | .Axiom_other_n0 (hv37 := shape) ..
  | .Axiom_other_other (hv37 := shape) ..
  | .Defn (hv269 := shape) ..
  | .Thm (hv526 := shape) ..
  | .Opaque (hv825 := shape) ..
  | .Quot (hv1076 := shape) ..
  | .Induct_n0 (hv1240 := shape) ..
  | .Induct_other_n0 (hv1240 := shape) ..
  | .Induct_other_other (hv1240 := shape) ..
  | .Ctor_n0_n0 (hv1989 := shape) ..
  | .Ctor_n0_other (hv1989 := shape) ..
  | .Ctor_other_n0 (hv1989 := shape) ..
  | .Ctor_other_other (hv1989 := shape) .. =>
    injection shape with _ tag _
    exact absurd tag (by decide)
  | .Rec_other (m2789 := m2789) (m2857 := m2857) (ev14 := ev14) (hv2727 := shape)
      (ev2801 := ev2801) (hm2865 := hm2865) (ev2838 := ev2838) (ev2882 := ev2882)
      (ev2912 := ev2912) (ev2942 := ev2942) (ev2964 := ev2964) (ev2986 := ev2986)
      (ev3157 := evf) (hc3182 := hcs) .. =>
    -- the modeled route runs the family check at the value's block field, which is refused
    injection shape with _ _ entries
    simp only [List.cons.injEq] at entries
    obtain ⟨-, -, -, -, -, -, -, -, -, hblock, -⟩ := entries
    subst hblock
    have enil : Heap.Extends m2789 m2857 := by rw [hm2865]; exact Heap.Extends.snoc m2789 _
    exact (hfr _ _ _ _ _ (ev14.heap_extends.trans (ev2801.heap_extends.trans (enil.trans
      (ev2838.heap_extends.trans (ev2882.heap_extends.trans (ev2912.heap_extends.trans
      (ev2942.heap_extends.trans (ev2964.heap_extends.trans ev2986.heap_extends))))))))
      (fun cl hcl => by rw [hcs]; simp [hcl]) evf).elim
  | .Rec_n0 (m2 := scopeBefore) (m2789 := scopeAfter) (m2857 := sortBefore)
      (m2826 := sortAfter) (v2825 := sortResult) (cs2836 := sortCalls)
      (m2870 := safeAfter) (m2900 := rulesAfter) (m2930 := kindsAfter)
      (m2952 := familyAfter) (m2974 := memberHeap)
      (ev14 := unsafeRun) (hv2727 := shape) (ev2801 := scopeRun) (hm2865 := nilSort)
      (ev2838 := sortRun) (ev2882 := safeRun) (ev2912 := rulesRun) (ev2942 := kindsRun)
      (ev2964 := familyRun) (ev2986 := modeledRun) (heq3062 := oneMotive)
      (ev3068 := memberRun) (hc3093 := allCalls) .. =>
    injection shape with _ _ entries
    simp only [List.cons.injEq, and_true] at entries
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := entries
    subst nilSort
    have hext : Heap.Extends sortAfter memberHeap :=
      safeRun.heap_extends.trans (rulesRun.heap_extends.trans
        (kindsRun.heap_extends.trans (familyRun.heap_extends.trans modeledRun.heap_extends)))
    refine ⟨oneMotive, scopeBefore, scopeAfter, sortAfter, memberHeap, _, sortResult, _,
      sortCalls, _, unsafeRun.heap_extends, scopeRun, ?_, sortRun, ?_, ?_, hext, memberRun, ?_⟩
    · rw [allCalls]; simp
    · rw [allCalls]; simp
    · intro call member
      rw [allCalls]
      simp [member]
    · intro call member
      rw [allCalls]
      simp [member]

end IxVM.Refinement.Typing
