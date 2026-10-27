import IxSharingVerify.BuildSuccess
import IxSharingVerify.ReexpandSuccess
import IxSharingVerify.PinnedOrderSpec
import IxSharingVerify.FamilyBudget
import IxSharingVerify.FamilySuccess
import IxSharingVerify.FamilyComponents
import IxSharingVerify.FamilyFinish
import IxC.Kernel.Audit.Axioms

/-!
# The uniform phase never refuses

`uniformFinishF` checks its stored set, materializes it in the pinned order,
compares the materialized length with the model and re-expands the result.
For a strictly increasing stored set of in-degree-2 terms of a canonical DAG
whose model is the uniform length of the set, every check passes under
large enough budgets (`uniformFinishF_ok`): `build` never refuses, the
materialized total is the uniform length, the pinned order lists stored
descendants first, and the re-expansion identifies the table and roots.

`familyUniform_ok` assembles the family phase: the component check, the
component loop, the knapsack, the model guards and the finisher.
-/

namespace Ix.Sharing.Verify.Totality

open Ix.Sharing.Exact
open Ix.Sharing.Family
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (DagArity Desc Below bind_eq_ok termOf materializeDependent_parts
  materializeDependent_backward materializeDependent_correct forall₂_getElem)
open Ix.Sharing.Verify.CanonicalMeaning (ExpandedOK reexpand_ids dagModel_termOf)
open Ix.Sharing.Verify.Budget (LimitsLe Limits.join materializeDependent_mono reexpand_mono
  familyComponents_mono uniformKnapsack_mono uniformFinishF_mono)

theorem dagArity_of {dag : Dag} (hwf : DagWF dag) : DagArity dag := by
  intro t
  by_cases ht : t < dag.size
  · have := hwf.arity t ht
    rw [← dag_node_eq ht] at this
    exact this
  · simp only [Dag.node, Array.getElem?_eq_none (Nat.le_of_not_lt ht), Option.getD_none]
    rfl

theorem length_le_of_nodup {l : List Nat} {n : Nat} (nodup : l.Nodup) (bound : ∀ x ∈ l, x < n) :
    l.length ≤ n := by
  simpa using List.Nodup.length_le_of_subset nodup (l₂ := List.range n)
    (fun x hx => List.mem_range.mpr (bound x hx))

/-- The predicted total of `materializeDependent`. -/
def dependentTotal (p : Prep) (table roots : Array Nat) (width : Array (Option Nat)) : Nat :=
  tag0Size table.size +
    table.foldl (fun acc t => acc + p.inlineCost (p.evalAll width)
      (indexOfPairs p.dag.size table.toList.zipIdx) width t) 0 +
    roots.foldl (fun acc r => acc + (p.evalAll width).cost[r]!) 0

/-- The widths of a stored set at one width. -/
def storedWidth (n w : Nat) (stored : Array Nat) : Array (Option Nat) :=
  stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none)

section Dependent

variable {dag : Dag} (hwf : DagWF dag) {w : Nat} {stored table roots : Array Nat}
  (hin : ∀ t ∈ stored.toList, t < dag.size) (hperm : table.toList.Perm stored.toList)
  (hroots : ∀ r ∈ roots.toList, r < dag.size)

include hin in
theorem storedWidth_spec (u : Nat) :
    widthOf (storedWidth dag.size w stored) u =
      if (fun t => decide (t ∈ stored.toList)) u then some ((fun _ => w) u) else none := by
  unfold storedWidth
  rw [← Array.foldl_toList]
  exact widthOfStored dag.size w stored.toList hin u

include hin hperm in
theorem storedIndex_spec (u : Nat) :
    ((indexOfPairs (Prep.ofDag dag).dag.size table.toList.zipIdx)[u]?.getD none).isSome =
      (fun t => decide (t ∈ stored.toList)) u := by
  rw [ofDag_dag, indexOfTable_isSome _ table (fun t ht => hin t (hperm.subset ht)) u]
  simp only [decide_eq_decide]
  exact hperm.mem_iff

include hwf hin hperm hroots in
/-- `materializeDependent` of a stored set in a permuted order succeeds once
its predicted total fits. -/
theorem materializeDependent_ok (capacity : table.size < wordBound) (limits : Limits)
    (room : dependentTotal (Prep.ofDag dag) table roots (storedWidth dag.size w stored) ≤
      limits.maxMaterialize) :
    ∃ es rs work, (Prep.ofDag dag).materializeDependent table roots
      (storedWidth dag.size w stored) limits =
        .ok (es, rs, dependentTotal (Prep.ofDag dag) table roots (storedWidth dag.size w stored), work) := by
  have hp := prepWF_ofDag hwf
  have hev := hp.evalAll_ok (ofDag_empty_size dag) (wd := fun _ => w)
    (avail := fun t => decide (t ∈ stored.toList)) (storedWidth dag.size w stored)
    (storedWidth_spec hin)
  have build := hp.build_ok _ hev _ (storedWidth dag.size w stored)
    (storedWidth_spec hin) (storedIndex_spec hin hperm)
  obtain ⟨es, hes⟩ := array_mapM_ok _ table (fun t ht =>
    build ((Prep.ofDag dag).dag.size + 1) true t (hin t (hperm.subset ht)) (by have := hin t (hperm.subset ht); simp only [ofDag_dag]; omega))
  obtain ⟨rs, hrs⟩ := array_mapM_ok _ roots (fun r hr =>
    build ((Prep.ofDag dag).dag.size + 1) false r (hroots r hr) (by have := hroots r hr; simp only [ofDag_dag]; omega))
  refine ⟨es, rs, ?_⟩
  unfold Prep.materializeDependent
  rw [ite_eq_right (show ¬ table.size ≥ wordBound by omega)]
  dsimp only
  split
  · rename_i tooBig
    exact absurd room (Nat.not_le.mpr tooBig)
  · rw [hes, hrs]
    exact ⟨_, rfl⟩

include hwf hin hperm in
/-- The predicted total is the uniform length of the stored set. -/
theorem dependentTotal_eq :
    dependentTotal (Prep.ofDag dag) table roots (storedWidth dag.size w stored) =
      ulen dag w roots stored.toList := by
  have hp := prepWF_ofDag hwf
  have hempty := ofDag_empty_size dag
  let p := Prep.ofDag dag
  have hin' : ∀ t ∈ table.toList, t < p.dag.size := fun t ht => hin t (hperm.subset ht)
  unfold dependentTotal ulen uniformCost
  rw [array_foldl_add_sum, array_foldl_add_sum]
  have hlen : table.size = stored.toList.length := by
    rw [← Array.length_toList]; exact hperm.length_eq
  have hentries : (table.toList.map (p.inlineCost (p.evalAll (storedWidth dag.size w stored))
      (indexOfPairs p.dag.size table.toList.zipIdx) (storedWidth dag.size w stored))).sum =
      (stored.toList.map (uInl p w (fun t => decide (t ∈ stored.toList)))).sum := by
    rw [List.map_congr_left (fun t ht => hp.inlineCost_eq hempty _ _
      (storedWidth_spec hin) (storedIndex_spec hin hperm) t (hin' t ht))]
    exact List.Perm.sum_nat (hperm.map _)
  have hrootsSum : (roots.toList.map fun r => (p.evalAll (storedWidth dag.size w stored)).cost[r]!).sum =
      (roots.toList.map (uCost p w (fun t => decide (t ∈ stored.toList)))).sum := by
    rw [List.map_congr_left (fun r _ => hp.evalAll_cost hempty _ (storedWidth_spec hin) r)]
  simp only [p] at hentries hrootsSum hlen
  rw [hlen, hentries, hrootsSum]

end Dependent

/-- **The uniform finisher never refuses** a strictly increasing stored set
of in-degree-2 terms whose model is its uniform length. -/
theorem uniformFinishF_ok {w : Nat} {ex : Expanded} (ok : ExpandedOK ex) (deg : Array Nat)
    (c : UniformChoice) (hin : ∀ t ∈ c.stored.toList, t < ex.dag.size)
    (sorted : c.stored.toList.Pairwise (· < ·)) (degrees : ∀ t ∈ c.stored.toList, 2 ≤ deg[t]!)
    (model : c.model = ulen ex.dag w ex.roots c.stored.toList)
    (capacity : ex.dag.size < wordBound) :
    ∃ limits out, uniformFinishF w limits ex (Prep.ofDag ex.dag) deg c = .ok out := by
  have hwf := ok.wf
  let order := pinnedOrder ex.dag c.facts.deg c.stored
  have hperm : order.toList.Perm c.stored.toList := pinnedOrder_perm _ _ _
  have nodup : c.stored.toList.Nodup := sorted.imp Nat.ne_of_lt
  have orderSize : order.size < wordBound := by
    have h1 := length_le_of_nodup nodup hin
    have h2 := hperm.length_eq
    simp only [Array.length_toList] at h1 h2
    omega
  let total := dependentTotal (Prep.ofDag ex.dag) order ex.roots (storedWidth ex.dag.size w c.stored)
  let first : Limits := { maxMaterialize := total }
  obtain ⟨es, rs, work, materialized⟩ := materializeDependent_ok hwf hin hperm ok.roots orderSize first
    (Nat.le_refl _)
  have totalEq : total = c.model := by
    rw [model]
    exact dependentTotal_eq (roots := ex.roots) hwf hin hperm
  -- the materialized parts
  obtain ⟨esSize, backward, rootsBelow⟩ := materializeDependent_backward _ order ex.roots _ first
    (dagArity_of hwf) (fun k j hk hj below => Ix.Sharing.Verify.Pinned.pinnedOrder_backward hwf
      c.facts.deg c.stored hin nodup k j hk hj below) materialized
  obtain ⟨entries, rootRows⟩ := materializeDependent_correct _ order ex.roots _ first materialized
    (termOf ex.dag.nodes) (dagModel_termOf hwf)
  have rsSize : rs.size = ex.roots.size := by
    have := (forall₂_getElem rootRows).1
    simpa using this.symm
  obtain ⟨second, visits, reexpanded⟩ := reexpand_ids hwf ok.injective
    (fun t ht => hin t (hperm.subset ht)) ok.roots esSize rsSize backward rootsBelow entries rootRows
    (by omega)
  let limits := Limits.join first second
  have mat : (Prep.ofDag ex.dag).materializeDependent (pinnedOrder ex.dag c.facts.deg c.stored)
      ex.roots (c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none))
      limits = .ok (es, rs, dependentTotal (Prep.ofDag ex.dag) (pinnedOrder ex.dag c.facts.deg c.stored)
        ex.roots (c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)),
        work) :=
    materializeDependent_mono (LimitsLe.join_left first second) _ _ _ _ materialized
  have re : reexpand limits ex.dag es rs = .ok (pinnedOrder ex.dag c.facts.deg c.stored, ex.roots, visits) :=
    reexpand_mono (LimitsLe.join_right first second) reexpanded
  refine ⟨limits, ?_⟩
  unfold uniformFinishF
  dsimp only
  have bounded : (c.stored.all (· < ex.dag.size)) = true := by
    rw [Array.all_eq_true']
    intro t member
    exact decide_eq_true (hin t (Array.mem_toList_iff.mpr member))
  have checkModel : (dependentTotal (Prep.ofDag ex.dag) (pinnedOrder ex.dag c.facts.deg c.stored)
      ex.roots (c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none))
      == c.model) = true := beq_iff_eq.mpr totalEq
  rw [ite_eq_left bounded, ite_eq_left (inClassCheckD_ok sorted degrees)]
  rw [Budget.bind_ok_eq mat]
  dsimp only
  rw [ite_eq_left checkModel]
  rw [Budget.bind_ok_eq re]
  dsimp only
  rw [ite_eq_left (beq_self_eq_true _), ite_eq_left (beq_self_eq_true _)]
  exact ⟨_, rfl⟩


/-! ## The family phase -/

/-- The stored set of a least family selection: strictly increasing terms of
in-degree at least 2. -/
theorem selected_stored {cfg : Config} {ex : Expanded} {width : Nat} (wf : DagWF ex.dag)
    (checked : componentsChecked ex.dag (stg width ex).cls (stg width ex).opaq (stg width ex).comps
      (componentLabels ex.dag.size (stg width ex).comps) = true)
    {delta : _root_.Int} {set : Array Nat}
    (selected : LeastProductOutput cfg (stg width ex).cs.size (initialFactors ex (stg width ex)) delta set) :
    (∀ t ∈ (mergeSorted (stg width ex).cs set).toList,
      t < ex.dag.size ∧ 2 ≤ (graphFacts ex.dag ex.roots).deg[t]!) ∧
    (mergeSorted (stg width ex).cs set).toList.Pairwise (· < ·) := by
  obtain ⟨sets, minimum, -, setEq, -, -⟩ := selected
  obtain ⟨partition, distinct, -, -⟩ := componentsChecked_spec wf checked
  have clsEq := (stage_cls_theta width ex).1
  obtain ⟨lengthEq, rows⟩ := forall₂_getElem minimum.1
  have factorsLength : (initialFactors ex (stg width ex)).length = (stg width ex).comps.size := by
    simp [initialFactors]
  -- each selected set lies in its component, without repeats
  have inComp : ∀ i (hi : i < sets.length), i < (stg width ex).comps.size ∧
      sets[i].toList.Nodup ∧ ∀ t ∈ sets[i].toList, t ∈ (stg width ex).comps[i]!.toList := by
    intro i hi
    have hc : i < (stg width ex).comps.size := by omega
    have row := rows i (by omega) hi
    simp only [initialFactors, List.getElem_map, Array.getElem_toList] at row
    have membersNodup : (stg width ex).comps[i].toList.Nodup := by
      simpa [getElem!_pos (stg width ex).comps i hc] using distinct i hc
    refine ⟨hc, (family_sorted cfg _ _ membersNodup _ row).imp Nat.ne_of_lt, fun t ht => ?_⟩
    rw [getElem!_pos (stg width ex).comps i hc]
    exact family_members cfg _ _ _ row t ht
  have selectedFacts : ∀ t ∈ selectedTerms sets, ∃ i, ∃ hi : i < sets.length,
      t ∈ sets[i].toList := by
    intro t ht
    simp only [selectedTerms, List.mem_flatten, List.mem_map] at ht
    obtain ⟨_, ⟨s, hs, rfl⟩, ts⟩ := ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    exact ⟨i, hi, ts⟩
  have uncertainOf : ∀ t ∈ selectedTerms sets, t < ex.dag.size ∧
      (stg width ex).cls[t]! = .uncertain ∧ ∃ i, (componentLabels ex.dag.size (stg width ex).comps)[t]! = some i ∧
        ∀ (j : Nat) (hj : j < sets.length), t ∈ sets[j].toList → j = i := by
    intro t ht
    obtain ⟨i, hi, ts⟩ := selectedFacts t ht
    obtain ⟨hc, _, sub⟩ := inComp i hi
    obtain ⟨bound, unc, label⟩ := partition i hc t (sub t ts)
    refine ⟨bound, unc, i, label, fun j hj tj => ?_⟩
    obtain ⟨hcj, _, subj⟩ := inComp j hj
    have labelj := (partition j hcj t (subj t tj)).2.2
    rw [label] at labelj
    exact (Option.some.inj labelj).symm
  have perm := cs_merge_perm (stg width ex).cs sets
  rw [← setEq] at perm
  constructor
  · intro t ht
    rcases List.mem_append.mp (perm.subset ht) with h | h
    · obtain ⟨bound, cs⟩ := (initial_cs_mem width ex t).mp h
      exact ⟨bound, deg_of_ucls bound (Or.inl cs)⟩
    · obtain ⟨bound, unc, _⟩ := uncertainOf t h
      rw [clsEq] at unc
      exact ⟨bound, deg_of_ucls bound (Or.inr unc)⟩
  · have selectedNodup : (selectedTerms sets).Nodup := by
      unfold selectedTerms
      show List.Pairwise (· ≠ ·) _
      rw [List.pairwise_flatten]
      refine ⟨?_, ?_⟩
      · intro l hl
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
        exact (inComp i hi).2.1
      · rw [List.pairwise_iff_getElem]
        intro i j hi hj lt t ti y tj same
        subst same
        simp only [List.getElem_map, List.length_map] at ti tj hi hj
        have inSel : t ∈ selectedTerms sets := by
          simp only [selectedTerms, List.mem_flatten, List.mem_map]
          exact ⟨_, ⟨sets[i], List.getElem_mem hi, rfl⟩, ti⟩
        obtain ⟨_, _, k, _, unique⟩ := uncertainOf t inSel
        have := (unique i hi ti).trans (unique j hj tj).symm
        omega
    have nodup : ((stg width ex).cs.toList ++ selectedTerms sets).Nodup := by
      rw [List.nodup_append]
      refine ⟨initial_cs_nodup width ex, selectedNodup, fun a ha b hb same => ?_⟩
      subst same
      obtain ⟨_, cs⟩ := (initial_cs_mem width ex a).mp ha
      obtain ⟨_, unc, _⟩ := uncertainOf a hb
      rw [clsEq, cs] at unc
      cases unc
    have sortedLe := mergeSorted_sorted (stg width ex).cs set
    exact (sortedLe.and (perm.nodup_iff.mpr nodup)).imp fun ⟨le, ne⟩ => Nat.lt_of_le_of_ne le ne

/-- `familyUniform` from its parts. -/
theorem familyUniform_of_parts {cfg : Config} {limits : Limits} {ex : Expanded} {width : Nat}
    {results : Array CompResult} {states work : Nat} {delta : _root_.Int} {set : Array Nat}
    {lowerBracket : Bool} {out : UniformSharingResult}
    (produced : familyComponents cfg limits ex (stg width ex) width (parentsOf ex.dag) =
      .ok (results, states, work))
    (chosen : uniformKnapsack limits (stg width ex).cs.size results = .ok (delta, set, lowerBracket))
    (bounded : (familyModel ex width delta set).toNat ≤ limits.maxOutputBytes)
    (finish : uniformFinishF width limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots).deg
      (familyChoice ex width states work delta set lowerBracket) = .ok out) :
    familyUniform cfg limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots) (parentsOf ex.dag)
      width = .ok out := by
  unfold familyUniform
  rw [← uniformStage_eq_F]
  dsimp only
  rw [Budget.bind_ok_eq produced]
  dsimp only
  rw [Budget.bind_ok_eq chosen]
  dsimp only
  split
  · rename_i tooLong
    exact absurd tooLong (Nat.not_lt.mpr bounded)
  · exact finish

/-- **The family phase never refuses** on a canonical DAG whose size fits
a 64-bit index. -/
theorem familyUniform_ok (cfg : Config) {ex : Expanded} (ok : ExpandedOK ex) (width : Nat)
    (capacity : ex.dag.size < wordBound) :
    ∃ limits out, familyUniform cfg limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) width = .ok out := by
  have wf := ok.wf
  have checked := stage_componentsChecked width ex wf
  have hcp := Ix.Sharing.Family.childrenPrecede_of_cp wf.precede
  have membersNodup := (checked_components_capacity wf checked).1
  let first : Limits :=
    { maxStates := familyCallTotal cfg (stg width ex).comps.toList
      maxCostEvals := familyWorkTotal cfg ex (stg width ex) (stg width ex).comps.toList }
  obtain ⟨⟨results, states, work⟩, produced⟩ := familyComponents_ok cfg first ex (stg width ex) width
    hcp membersNodup (Nat.le_refl _) (Nat.le_refl _)
  let second : Limits := { maxKnapsackCells := knapsackCells (stg width ex).cs.size results }
  obtain ⟨⟨delta, set, lowerBracket⟩, chosen⟩ := uniformKnapsack_ok second _ results (Nat.le_refl _)
  let joined := Limits.join first second
  have produced' := familyComponents_mono (LimitsLe.join_left first second) cfg ex _ width hcp produced
  have chosen' := uniformKnapsack_mono (LimitsLe.join_right first second) chosen
  have selected := familyComponents_least cfg joined ex width wf checked produced' chosen'
  have modelEq := (selected_model_nonnegative wf ok.roots ok.reachable checked selected).2
  obtain ⟨storedFacts, sorted⟩ := selected_stored wf checked selected
  let third : Limits := { maxOutputBytes := (familyModel ex width delta set).toNat }
  obtain ⟨fourth, out, finish⟩ := uniformFinishF_ok (w := width) ok (graphFacts ex.dag ex.roots).deg
    (familyChoice ex width states work delta set lowerBracket)
    (fun t ht => (storedFacts t ht).1) sorted (fun t ht => (storedFacts t ht).2) modelEq capacity
  let all := Limits.join (Limits.join joined third) fourth
  have toAll : LimitsLe joined all :=
    LimitsLe.trans (LimitsLe.join_left joined third) (LimitsLe.join_left _ fourth)
  refine ⟨all, out, familyUniform_of_parts
    (familyComponents_mono toAll cfg ex _ width hcp produced')
    (uniformKnapsack_mono toAll chosen') ?_
    (uniformFinishF_mono (LimitsLe.join_right _ fourth) _ _ _ _ _ finish)⟩
  exact Nat.le_trans (Nat.le_refl _)
    ((LimitsLe.trans (LimitsLe.join_right joined third) (LimitsLe.join_left _ fourth)).outputBytes)

end Ix.Sharing.Verify.Totality

#guard_kernel_axioms Ix.Sharing.Verify.Totality.materializeDependent_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.dependentTotal_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.uniformFinishF_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.selected_stored [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.familyUniform_ok [propext, Classical.choice, Quot.sound]
