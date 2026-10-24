import IxSharingVerify.FamilyLocalWriting

/-! A complete semantic writing within the full-endpoint residual bound.
The exact residual flow cancels internal child costs; local costs are
bounded by actual valid writings from FamilyLocalWriting. Attainment then
provides an EncodingWF witness, without assuming the requested bound.

EncodingWF asserts valid writings using the available stored term IDs,
an inline body for each table term, and one valid writing per ordered root.
It does not assert UInt64 representability, table order/capacity, serialized
bytes, or successful execution of a materializer. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (Desc)

theorem fullStored_nodup (cfg : Config) (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true) :
    (fullStored ex width).toList.Nodup := by
  rw [initial_full_stored cfg ex width wf checked]
  apply (Exact.mergeSorted_perm _ _).nodup_iff.mpr
  apply nodup_app (initial_cs_nodup width ex)
  · rw [stage_unc]
    exact uunc_nodup _ _ _ _
  · intro t stored uncertain
    have cs := (initial_cs_mem width ex t).mp stored
    rw [stage_unc, mem_uunc] at uncertain
    rw [cs.2] at uncertain
    cases uncertain.2

theorem mul_sum_map (c : Nat) (f : Nat → Nat) (xs : List Nat) :
    c * (xs.map f).sum = (xs.map fun x => c * f x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Nat.mul_add, ih]

theorem child_cost_sum {dag : Dag} (wf : DagWF dag) {y : Nat} (bound : y < dag.size)
    (value : Nat → Nat) :
    ((List.range dag.size).map fun t => edgeAll (Prep.ofDag dag) y t * value t).sum =
      ((dag.node y).children.toList.map value).sum := by
  have children : ∀ t ∈ (dag.node y).children.toList, t < dag.size := by
    intro t present
    have below := wf.child_lt bound (Array.mem_toList_iff.mp present)
    omega
  rw [sum_eq_count_range children value]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  rw [edgeAll_eq_child_count wf bound]

/-- Weighted incoming costs are precisely root costs plus child costs
from ordinary expansions, retaining all root and edge multiplicities. -/
theorem residual_flow_cost (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size) (value : Nat → Nat) :
    ((List.range ex.dag.size).map fun t => (residualIncoming ex width)[t]! * value t).sum =
      (ex.roots.toList.map value).sum +
        ((List.range ex.dag.size).map fun y => residualExpansions ex width y *
          ((ex.dag.node y).children.toList.map value).sum).sum := by
  have rows : (List.range ex.dag.size).map (fun t => (residualIncoming ex width)[t]! * value t) =
      (List.range ex.dag.size).map (fun t => ex.roots.toList.count t * value t +
        ((List.range ex.dag.size).map fun y =>
          residualExpansions ex width y * (edgeAll (Prep.ofDag ex.dag) y t * value t)).sum) := by
    apply List.map_congr_left
    intro t present
    rw [residualIncoming_eq ex width wf roots (List.mem_range.mp present), Nat.add_mul,
      ← sum_mul_right']
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro y _
    rw [Nat.mul_comm (edgeAll (Prep.ofDag ex.dag) y t), Nat.mul_assoc]
  rw [rows, sum_map_add', ← sum_eq_count_range roots value,
    sum_comm_range (List.range ex.dag.size) ex.dag.size]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro y present
  rw [← mul_sum_map, child_cost_sum wf (List.mem_range.mp present)]

/-- One node's table-body and incoming costs are paid by its expansion
and boundary charges. Each case uses a real semantic writing inequality. -/
theorem residual_semantic_row (cfg : Config) (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    {t : Nat} (bound : t < ex.dag.size) :
    let avail := fun x => decide (x ∈ (fullStored ex width).toList)
    (fullStored ex width).toList.count t * uInl (Prep.ofDag ex.dag) width avail t +
        (residualIncoming ex width)[t]! * uCost (Prep.ofDag ex.dag) width avail t ≤
      residualExpansions ex width t * (residualLocalPayload ex t +
        ((ex.dag.node t).children.toList.map (uCost (Prep.ofDag ex.dag) width avail)).sum) +
        (residualIncoming ex width)[t]! * residualBoundaryUnit ex width t := by
  dsimp only
  let avail := fun x => decide (x ∈ (fullStored ex width).toList)
  have hp := prepWF_ofDag wf
  have localCost := uInl_le_local hp width avail bound
  have row := hp.uCost_eq width avail t bound
  have nodup := fullStored_nodup cfg ex width wf checked
  by_cases present : t ∈ (fullStored ex width).toList
  · have stored : (fullStored ex width).contains t = true :=
      Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp present)
    have available : avail t = true := by simp only [avail, present, decide_true]
    have value : uCost (Prep.ofDag ex.dag) width avail t ≤ width := by
      rw [row]
      unfold costOf
      rw [available]
      exact Nat.min_le_right _ _
    have incoming := Nat.mul_le_mul_left (residualIncoming ex width)[t]! value
    rw [nodup.count, ite_eq_left present]
    simp only [residualExpansions, residualWeight, residualBoundaryUnit, stored, ite_true,
      Nat.one_mul, residualLocalPayload]
    exact Nat.add_le_add localCost incoming
  · have stored : (fullStored ex width).contains t = false := by
      apply Bool.eq_false_iff.mpr
      intro yes
      exact present (Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp yes))
    have unavailable : avail t = false := by simp only [avail, present, decide_false]
    have value : uCost (Prep.ofDag ex.dag) width avail t = uInl (Prep.ofDag ex.dag) width avail t := by
      rw [row]
      simp only [costOf, unavailable, Bool.false_eq_true, ite_false, uInl]
    rw [List.count_eq_zero_of_not_mem present]
    simp only [Nat.zero_mul, Nat.zero_add, residualExpansions, residualWeight,
      residualBoundaryUnit, stored, Bool.false_eq_true, ite_false]
    by_cases repeated : 2 ≤ (graphFacts ex.dag ex.roots).deg[t]!
    · rw [ite_eq_left repeated, ite_eq_left repeated]
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [value]
      exact Nat.mul_le_mul_left _ (hp.uInl_le_empty width avail bound)
    · rw [ite_eq_right repeated, ite_eq_right repeated]
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [value]
      exact Nat.mul_le_mul_left _ localCost

/-- Cancelling internal edge costs proves the actual uniform semantic
length of the full endpoint is bounded by the residual charge. -/
theorem fullStored_ulen_le_residual (cfg : Config) (ex : Expanded) (width : Nat)
    (wf : DagWF ex.dag) (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true) :
    ulen ex.dag width ex.roots (fullStored ex width).toList ≤ residualCharge ex width := by
  let avail := fun x => decide (x ∈ (fullStored ex width).toList)
  let value := uCost (Prep.ofDag ex.dag) width avail
  have inTable : ∀ t ∈ (fullStored ex width).toList, t < ex.dag.size :=
    fun t present => ((initial_full_stored_mem cfg ex width wf checked t).mp present).1
  have rows := sum_le_sum_of_le (List.range ex.dag.size)
    (fun t present => residual_semantic_row cfg ex width wf checked (List.mem_range.mp present))
  rw [sum_map_add', sum_map_add'] at rows
  have body := sum_eq_count_range inTable (uInl (Prep.ofDag ex.dag) width avail)
  have flow := residual_flow_cost ex width wf roots value
  have expanded : ((List.range ex.dag.size).map fun t =>
      residualExpansions ex width t * (residualLocalPayload ex t +
        ((ex.dag.node t).children.toList.map value).sum)).sum =
      ((List.range ex.dag.size).map fun t => residualExpansions ex width t * residualLocalPayload ex t).sum +
      ((List.range ex.dag.size).map fun t =>
        residualExpansions ex width t * ((ex.dag.node t).children.toList.map value).sum).sum := by
    rw [← sum_map_add']
    apply congrArg List.sum
    apply List.map_congr_left
    intro t _
    exact Nat.mul_add _ _ _
  dsimp only [value, avail] at body flow expanded
  unfold ulen uniformCost residualCharge
  rw [Array.length_toList]
  omega

/-- An actual complete writing attains that bounded semantic minimum.
EncodingWF guarantees inline stored bodies and valid ordered root writings
using only available stored IDs; it is not a wire-format theorem. -/
theorem fullStored_encoding_bound (cfg : Config) (ex : Expanded) (width : Nat)
    (wf : DagWF ex.dag) (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true) :
    let p := Prep.ofDag ex.dag
    let table := (fullStored ex width).toList
    let avail := fun x => decide (x ∈ table)
    ∃ entry rootsW, EncodingWF p avail table entry ex.roots.toList rootsW ∧
      encodingCost p width table entry rootsW = ulen ex.dag width ex.roots table ∧
      encodingCost p width table entry rootsW ≤ residualCharge ex width ∧
      encodingCost p width table entry rootsW ≤ tag0Size (fullStored ex width).size +
        ((List.range ex.dag.size).map fun t =>
          (ex.dag.node t).head.ownBytes + 9 + (ex.dag.node t).sideExtra).sum +
        2 * width * (ex.roots.size +
          ((List.range ex.dag.size).map fun t => (ex.dag.node t).children.size).sum) := by
  dsimp only
  have inTable : ∀ t ∈ (fullStored ex width).toList, t < ex.dag.size :=
    fun t present => ((initial_full_stored_mem cfg ex width wf checked t).mp present).1
  obtain ⟨entry, rootsW, valid, cost⟩ := (prepWF_ofDag wf).uniformCost_attained width
    (fun x => decide (x ∈ (fullStored ex width).toList)) (fullStored ex width).toList
    ex.roots.toList inTable roots
  have bounded := fullStored_ulen_le_residual cfg ex width wf roots checked
  have explicitBound := residualCharge_le cfg ex width wf roots reachable checked
  refine ⟨entry, rootsW, valid, cost, ?_, ?_⟩
  · rw [cost]
    exact bounded
  · rw [cost]
    exact Nat.le_trans bounded explicitBound

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.fullStored_nodup [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.mul_sum_map [propext]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.child_cost_sum [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.residual_flow_cost [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.residual_semantic_row [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.fullStored_ulen_le_residual [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.fullStored_encoding_bound [propext, Classical.choice, Quot.sound]
