import IxSharingVerify.FamilyCost

/-! The initial family cost decomposition does not need the telescope
subadditivity bound used by the old global-optimality exchange. These
additive lemmas retain root bounds, reachability and the checked component
partition, without changing any runtime guard or existing exact theorem.

The family remains the actual initial-stage product: CS is fixed and each
uncertain component contributes one of its declared family sets. No claim
of global optimality, output representability or unconditional success is
made here. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (Desc)

/-- The initial threshold is positive directly from the stage rule; its
proof does not package a global optimum or a telescope bound. -/
theorem initial_theta_pos (width : Nat) (ex : Expanded) :
    1 ≤ (stg width ex).theta := by
  rcases (stage_cls_theta width ex).2 with threshold | ⟨threshold, _⟩
  · rw [threshold]
    unfold uthetaMax
    omega
  · rw [threshold]
    omega

/-- Initial CS membership is exactly the initial classification filter. -/
theorem initial_cs_mem (width : Nat) (ex : Expanded) (t : Nat) :
    t ∈ (stg width ex).cs.toList ↔
      t < ex.dag.size ∧ (ucls ex.dag ex.roots width (stg width ex).theta)[t]! = .certainStored := by
  rw [stage_cs, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨bound, stored⟩
    exact ⟨bound, uclass_eq_of_beq stored⟩
  · rintro ⟨bound, stored⟩
    exact ⟨bound, by rw [stored]; exact uclass_beq_self _⟩

/-- Filtering structural IDs cannot duplicate a certain-stored member. -/
theorem initial_cs_nodup (width : Nat) (ex : Expanded) :
    (stg width ex).cs.toList.Nodup := by
  rw [stage_cs]
  exact List.nodup_range.sublist List.filter_sublist

/-- Each checked component adds its exact semantic cost change, without
`SpinesFit`. This is the same prefix identity as `ulen_compParts`, using
only the initial threshold/CS facts above and `ulen_split_component`.

Reachability is retained in the public interface for compatibility with the
actual family domain; this decomposition itself does not consume it. -/
theorem ulen_compParts_spineFree {width : Nat} {ex : Expanded} (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (_reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : componentsChecked ex.dag (stg width ex).cls (stg width ex).opaq
      (stg width ex).comps (componentLabels ex.dag.size (stg width ex).comps) = true)
    (selected : List Nat) :
    ∀ j, j ≤ (stg width ex).comps.size →
      ulen ex.dag width ex.roots
          ((stg width ex).cs.toList ++ compParts (stg width ex).comps selected j) +
          tag0Size (stg width ex).cs.toList.length +
          ((List.range j).map fun i => scost (compCx width ex i) ex.dag []).sum =
        ulen ex.dag width ex.roots (stg width ex).cs.toList +
          tag0Size ((stg width ex).cs.toList ++ compParts (stg width ex).comps selected j).length +
          ((List.range j).map fun i =>
            scost (compCx width ex i) ex.dag
              (partOf selected (stg width ex).comps[i]!.toList)).sum := by
  obtain ⟨members, _, _, separate⟩ := componentsChecked_spec wf checked
  rw [(stage_cls_theta width ex).1] at members separate
  let label : Nat → Nat := fun t =>
    ((componentLabels ex.dag.size (stg width ex).comps)[t]!).getD 0
  intro j
  induction j with
  | zero => intro _; simp [compParts]
  | succ j ih =>
    intro bound
    have previous := ih (by omega)
    have inside : j < (stg width ex).comps.size := by omega
    have context := compCx_sctx wf checked inside
    have thisPart : ∀ t ∈ partOf selected (stg width ex).comps[j]!.toList,
        t ∈ (compCx width ex j).members.toList ∧ t < ex.dag.size ∧
          (ucls ex.dag ex.roots width (stg width ex).theta)[t]! = .uncertain ∧ label t = j := by
      intro t present
      have own := (partOf_sub t present).1
      obtain ⟨inDag, uncertain, labelled⟩ := members j inside t own
      exact ⟨own, inDag, uncertain, by simp only [label]; rw [labelled]; rfl⟩
    have earlier : ∀ t ∈ compParts (stg width ex).comps selected j,
        t < ex.dag.size ∧
          (ucls ex.dag ex.roots width (stg width ex).theta)[t]! = .uncertain ∧ label t ≠ j := by
      intro t present
      obtain ⟨i, before, own, _⟩ := mem_compParts.mp present
      obtain ⟨inDag, uncertain, labelled⟩ := members i (by omega) t own
      exact ⟨inDag, uncertain, by simp only [label]; rw [labelled]; simp; omega⟩
    have splitCost := ulen_split_component wf ex.roots roots width (stg width ex).theta
      (initial_theta_pos width ex) (opaq := (compCx width ex j).up.opaq)
      (fun u => stage_opaq width ex u) (initial_cs_nodup width ex)
      (fun t present => (initial_cs_mem width ex t).mp present)
      (compCx width ex j).members label j
      (fun a b inDag uncertainA uncertainB desc => by
        simp only [label]
        rw [separate a b inDag uncertainA uncertainB desc])
      (V := partOf selected (stg width ex).comps[j]!.toList)
      (R := compParts (stg width ex).comps selected j) thisPart earlier
    rw [← context.cost_eq, ← context.cost_eq] at splitCost
    have perm :
        ((stg width ex).cs.toList ++ compParts (stg width ex).comps selected (j + 1)).Perm
          ((stg width ex).cs.toList ++ partOf selected (stg width ex).comps[j]!.toList ++
            compParts (stg width ex).comps selected j) := by
      rw [compParts_succ]
      simp only [List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    rw [ulen_perm perm, perm.length_eq, List.range_succ, List.map_append, List.map_append,
      List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    simp only [List.length_append] at splitCost previous ⊢
    omega

/-- The actual family objective is a uniform semantic length on the same
root/reachability/partition domain, without a telescope-size premise.
Only membership in the declared product is required; no global minimum,
desired cost equality, or finisher-success assumption is substituted. -/
theorem initial_product_cost_spineFree {cfg : Config} {ex : Expanded} {width : Nat}
    {sets : List (Array Nat)} (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    (member : ProductMember cfg (initialFactors ex (stg width ex)) sets) :
    (ulen ex.dag width ex.roots ((stg width ex).cs.toList ++ selectedTerms sets) : _root_.Int) =
      (csBase ex (Prep.ofDag ex.dag) (stg width ex) : _root_.Int) +
        productObjective (stg width ex).cs.size (initialFactors ex (stg width ex)) sets := by
  have parts := initial_compParts_perm wf checked member
  have decomposition := ulen_compParts_spineFree wf roots reachable checked (selectedTerms sets)
    (stg width ex).comps.size (Nat.le_refl _)
  have base := csBase_eq (w := width) wf roots
  rw [ulen_perm (parts.append_left (stg width ex).cs.toList), List.length_append,
    parts.length_eq, selectedTerms_length, Array.length_toList] at decomposition
  rw [Array.length_toList] at base
  have deltas := initial_deltaSum wf checked member
  rw [sum_map_sub_int] at deltas
  unfold productObjective
  omega

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_theta_pos [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_cs_mem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_cs_nodup [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.ulen_compParts_spineFree [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.initial_product_cost_spineFree [propext, Classical.choice, Quot.sound]
