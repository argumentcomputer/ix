import IxSharingVerify.FamilyFullWitness

/-! Residual-forest accounting for the actual full family endpoint.
Stored terms expand once for their entry bodies. An omitted term with
compact degree at least two is treated as an atomic unshared body; the
previous checkpoint bounds its semantic cost. Remaining omitted terms
expand according to their incoming root/edge occurrences.

This proof-only accounting has not yet been related to a concrete WTree
forest or materializer output. In particular, the local telescope allowance
below is a charge to be justified by the later grafting proof, not an
assertion that a wire encoding exists. -/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (Desc)

/-- Full endpoints get one stored body; repeated omitted bodies are atomic;
only omitted low-degree nodes propagate their actual incoming multiplicity. -/
def residualWeight (ex : Expanded) (width t incoming : Nat) : Nat :=
  if (fullStored ex width).contains t then 1
  else if 2 ≤ (graphFacts ex.dag ex.roots).deg[t]! then 0 else incoming

def residualIncoming (ex : Expanded) (width : Nat) : Array Nat :=
  (propagateCounts ex.dag ex.roots (residualWeight ex width)).1

def residualExpansions (ex : Expanded) (width t : Nat) : Nat :=
  residualWeight ex width t (residualIncoming ex width)[t]!

theorem residualIncoming_eq (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size) {t : Nat} (bound : t < ex.dag.size) :
    (residualIncoming ex width)[t]! = ex.roots.toList.count t +
      ((List.range ex.dag.size).map fun y =>
        edgeAll (Prep.ofDag ex.dag) y t * residualExpansions ex width y).sum :=
  (propagateCounts_spec wf ex.roots roots (residualWeight ex width) bound).1

theorem degree_eq_edges {dag : Dag} (wf : DagWF dag) (roots : Array Nat)
    (inBounds : ∀ r ∈ roots.toList, r < dag.size) (t : Nat) :
    (graphFacts dag roots).deg[t]! = roots.toList.count t +
      ((List.range dag.size).map fun y => edgeAll (Prep.ofDag dag) y t).sum := by
  simpa only [graphFacts, Bool.false_eq_true, ite_false, edgeAll]
    using edgeCounts_spec wf roots inBounds false t

/-- No ordinary node is charged twice across the residual stored-body/root
forest. The low-degree case follows from its actual root-plus-edge degree,
not from an assumption about the unfolded occurrence count. -/
theorem residualExpansions_le_one (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size) :
    ∀ t, t < ex.dag.size → residualExpansions ex width t ≤ 1 := by
  have key : ∀ m t, ex.dag.size - t = m → t < ex.dag.size →
      residualExpansions ex width t ≤ 1 := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro t distance bound
      by_cases stored : (fullStored ex width).contains t = true
      · simp only [residualExpansions, residualWeight, stored, ite_true]
        exact Nat.le_refl 1
      by_cases repeated : 2 ≤ (graphFacts ex.dag ex.roots).deg[t]!
      · simp only [residualExpansions, residualWeight, stored, Bool.false_eq_true, ite_false,
          repeated, ite_true, Nat.zero_le]
      have incoming : (residualIncoming ex width)[t]! ≤ (graphFacts ex.dag ex.roots).deg[t]! := by
        rw [residualIncoming_eq ex width wf roots bound, degree_eq_edges wf ex.roots roots]
        apply Nat.add_le_add_left
        apply sum_le_sum_of_le
        intro y present
        have yBound := List.mem_range.mp present
        by_cases later : t < y
        · have once := ih (ex.dag.size - y) (by omega) y rfl yBound
          simpa only [Nat.mul_one] using Nat.mul_le_mul_left (edgeAll (Prep.ofDag ex.dag) y t) once
        · rw [edgeAll_zero_of_le (prepWF_ofDag wf) (by omega)]
          simp
      simp only [residualExpansions, residualWeight, stored, Bool.false_eq_true, ite_false,
        repeated] at ⊢
      omega
  exact fun t bound => key _ t rfl bound

theorem residualIncoming_le_degree (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size) {t : Nat} (bound : t < ex.dag.size) :
    (residualIncoming ex width)[t]! ≤ (graphFacts ex.dag ex.roots).deg[t]! := by
  rw [residualIncoming_eq ex width wf roots bound, degree_eq_edges wf ex.roots roots]
  apply Nat.add_le_add_left
  apply sum_le_sum_of_le
  intro y present
  have once := residualExpansions_le_one ex width wf roots y (List.mem_range.mp present)
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (edgeAll (Prep.ofDag ex.dag) y t) once

/-- `edgeAll` retains repeated child edges, exactly as the structural child
array does. It is not a count of distinct parents. -/
theorem edgeAll_eq_child_count {dag : Dag} (wf : DagWF dag) {y : Nat} (bound : y < dag.size)
    (t : Nat) : edgeAll (Prep.ofDag dag) y t = (dag.node y).children.toList.count t := by
  have arity := wf.children_size bound
  rw [children_toList arity]
  have count := count_map_filter (dag.node y).child (fun _ => true)
    (List.range (dag.node y).head.arity) t
  rw [List.filter_eq_self.mpr (by intros; rfl)] at count
  simp only [Bool.true_and] at count
  rw [count]
  unfold edgeAll edgeMult
  simp only [ofDag_dag]
  exact (filter_length_split (fun i => (dag.node y).child i == t)
    (fun i => continuationEdge (dag.node y) i (dag.node t)) _).symm

theorem edgeAll_sum {dag : Dag} (wf : DagWF dag) {y : Nat} (bound : y < dag.size) :
    ((List.range dag.size).map fun t => edgeAll (Prep.ofDag dag) y t).sum =
      (dag.node y).children.size := by
  have children : ∀ t ∈ (dag.node y).children.toList, t < dag.size := by
    intro t present
    have below := wf.child_lt bound (Array.mem_toList_iff.mp present)
    omega
  have count := sum_eq_count_range children (fun _ => 1)
  have same : ((List.range dag.size).map fun t => edgeAll (Prep.ofDag dag) y t) =
      (List.range dag.size).map fun t => (dag.node y).children.toList.count t := by
    apply List.map_congr_left
    intro t _
    exact edgeAll_eq_child_count wf bound t
  rw [same]
  simpa [List.map_const', List.sum_replicate_nat] using count.symm

/-- Sum of actual compact degrees: every root occurrence and every child
edge appears once, including duplicates in either supplied array. -/
theorem degree_sum {dag : Dag} (wf : DagWF dag) (roots : Array Nat)
    (inBounds : ∀ r ∈ roots.toList, r < dag.size) :
    ((List.range dag.size).map fun t => (graphFacts dag roots).deg[t]!).sum =
      roots.size + ((List.range dag.size).map fun y => (dag.node y).children.size).sum := by
  have counts := sum_eq_count_range inBounds (fun _ => 1)
  have rootSum : ((List.range dag.size).map roots.toList.count).sum = roots.size := by
    simpa [List.map_const', List.sum_replicate_nat] using counts.symm
  have degrees : (List.range dag.size).map (fun t => (graphFacts dag roots).deg[t]!) =
      (List.range dag.size).map (fun t => roots.toList.count t +
        ((List.range dag.size).map fun y => edgeAll (Prep.ofDag dag) y t).sum) := by
    apply List.map_congr_left
    intro t _
    exact degree_eq_edges wf roots inBounds t
  rw [degrees, sum_map_add', rootSum,
    sum_comm_range (List.range dag.size) dag.size (fun t y => edgeAll (Prep.ofDag dag) y t)]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro y present
  exact edgeAll_sum wf (List.mem_range.mp present)

theorem residualIncoming_sum_le (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size) :
    ((List.range ex.dag.size).map fun t => (residualIncoming ex width)[t]!).sum ≤
      ex.roots.size + ((List.range ex.dag.size).map fun y => (ex.dag.node y).children.size).sum := by
  rw [← degree_sum wf ex.roots roots]
  exact sum_le_sum_of_le _ fun t present =>
    residualIncoming_le_degree ex width wf roots (List.mem_range.mp present)

/-- Include the complete local scalar/vector payload from `ownBytes` and
the binder side payload. Nine extra bytes per expanded node are reserved
for the later telescope-grafting proof; no field-count bound is inferred. -/
def residualLocalPayload (ex : Expanded) (t : Nat) : Nat :=
  (ex.dag.node t).head.ownBytes + 9 + (ex.dag.node t).sideExtra

/-- Stored references cost w. Omitted repeated bodies use their proved
unshared semantic cost. Low-degree nodes are expanded instead. -/
def residualBoundaryUnit (ex : Expanded) (width t : Nat) : Nat :=
  if (fullStored ex width).contains t then width
  else if 2 ≤ (graphFacts ex.dag ex.roots).deg[t]! then
    uInl (Prep.ofDag ex.dag) width (fun _ => false) t
  else 0

theorem residualBoundaryUnit_le (cfg : Config) (ex : Expanded) (width : Nat)
    (wf : DagWF ex.dag) (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    {t : Nat} (bound : t < ex.dag.size) : residualBoundaryUnit ex width t ≤ 2 * width := by
  by_cases stored : (fullStored ex width).contains t = true
  · simp only [residualBoundaryUnit, stored, ite_true]
    omega
  by_cases repeated : 2 ≤ (graphFacts ex.dag ex.roots).deg[t]!
  · have omitted : t ∉ (fullStored ex width).toList := by
      intro present
      exact stored (Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp present))
    have small := initial_omitted_repeated_small cfg ex width wf roots reachable checked
      bound omitted repeated
    simp only [residualBoundaryUnit, stored, Bool.false_eq_true, ite_false, repeated, ite_true]
    omega
  · simp only [residualBoundaryUnit, stored, Bool.false_eq_true, ite_false, repeated, Nat.zero_le]

/-- Accounting only: a table header, ordinary-node payloads and all atomic
boundary costs. Equality/inequality with a concrete writing remains open. -/
def residualCharge (ex : Expanded) (width : Nat) : Nat :=
  tag0Size (fullStored ex width).size +
    ((List.range ex.dag.size).map fun t =>
      residualExpansions ex width t * residualLocalPayload ex t).sum +
    ((List.range ex.dag.size).map fun t =>
      (residualIncoming ex width)[t]! * residualBoundaryUnit ex width t).sum

/-- Every complete local payload is charged at most once; the remaining
charge is at most 2*w per root occurrence or child edge, with multiplicity.
This is a residual-accounting bound, not yet a serialized-output witness. -/
theorem residualCharge_le (cfg : Config) (ex : Expanded) (width : Nat)
    (wf : DagWF ex.dag) (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true) :
    residualCharge ex width ≤ tag0Size (fullStored ex width).size +
      ((List.range ex.dag.size).map fun t => residualLocalPayload ex t).sum +
      2 * width * (ex.roots.size +
        ((List.range ex.dag.size).map fun t => (ex.dag.node t).children.size).sum) := by
  have payload : ((List.range ex.dag.size).map fun t =>
      residualExpansions ex width t * residualLocalPayload ex t).sum ≤
      ((List.range ex.dag.size).map fun t => residualLocalPayload ex t).sum := by
    apply sum_le_sum_of_le
    intro t present
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (residualLocalPayload ex t)
      (residualExpansions_le_one ex width wf roots t (List.mem_range.mp present))
  have boundary : ((List.range ex.dag.size).map fun t =>
      (residualIncoming ex width)[t]! * residualBoundaryUnit ex width t).sum ≤
      ((List.range ex.dag.size).map fun t => (residualIncoming ex width)[t]! * (2 * width)).sum := by
    apply sum_le_sum_of_le
    intro t present
    exact Nat.mul_le_mul_left _
      (residualBoundaryUnit_le cfg ex width wf roots reachable checked (List.mem_range.mp present))
  rw [sum_mul_right'] at boundary
  have boundaryBound : ((List.range ex.dag.size).map fun t =>
      (residualIncoming ex width)[t]! * residualBoundaryUnit ex width t).sum ≤
      2 * width * (ex.roots.size +
        ((List.range ex.dag.size).map fun t => (ex.dag.node t).children.size).sum) := by
    calc
      _ ≤ _ := boundary
      _ ≤ _ := Nat.mul_le_mul_right (2 * width) (residualIncoming_sum_le ex width wf roots)
      _ = _ := Nat.mul_comm _ _
  unfold residualCharge
  exact Nat.add_le_add (Nat.add_le_add_left payload _) boundaryBound

end Ix.Sharing.Family

#guard_kernel_axioms Ix.Sharing.Family.residualIncoming_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.degree_eq_edges [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.residualExpansions_le_one [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.residualIncoming_le_degree [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.edgeAll_eq_child_count [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.edgeAll_sum [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.degree_sum [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.residualIncoming_sum_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.residualBoundaryUnit_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.residualCharge_le [propext, Classical.choice, Quot.sound]
