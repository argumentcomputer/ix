import IxSharingVerify.FamilyMinimum
import Ix.Sharing.FamilyNormalize

/-! Successful family production supplies the ordered family rows.
The cached-loop theorem is reused, including restoration of both buffers.
This is not the semantic-length or finisher correspondence theorem. -/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (bind_eq_ok)

theorem retainedResult_fields {slack : Nat} {trace : ComponentTrace} {result : CompResult}
    (run : retainedResult slack trace = .ok result) :
    result.members = trace.members ∧ result.bySize = CTable.trim trace.rows slack ∧
      CTable.best result.bySize = some result.bestDelta ∧
      bestSetOf result.bySize result.bestDelta = some result.bestSet ∧
      result.bySize[result.bestSet.size]! = some (result.bestDelta, result.bestSet) := by
  unfold retainedResult at run
  dsimp only at run
  split at run
  · rename_i delta best
    split at run
    · rename_i set chosen
      split at run
      · rename_i indexed
        simp only [pure, Except.pure, Except.ok.injEq] at run
        cases run
        exact ⟨rfl, rfl, best, chosen, by simpa only [beq_iff_eq] using indexed⟩
      · cases run
    · cases run
  · cases run

/-- Metering and row retention surround exactly the existing cached step.
This decomposition works for arbitrary incoming buffers and parent tables. -/
theorem familyStep_cached (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (parents : Array (Array Nat)) (results : Array CompResult)
    (states work : Nat) (posA posC members : Array Nat) {out : FamilyState}
    (run : familyStep cfg limits ex sg width parents ((results, states, work), posA, posC) members = .ok out) :
    ∃ trace result states' work', retainedResult sg.slack trace = .ok result ∧
      cachedStep cfg ex sg width parents (#[], posA, posC) (members, results.size) =
        (#[trace], out.2.1, out.2.2) ∧ out.1 = (results.push result, states', work') := by
  unfold familyStep at run
  dsimp only at run
  obtain ⟨states', _, run⟩ := bind_eq_ok run
  generalize context : mkSCtxL ex sg.f sg.up sg.cand sg.b0 sg.vis0 sg.rootCount
    sg.slack sg.theta sg.baseEv sg.widthCs sg.allTrue sg.unc parents posC members = prepared at run
  obtain ⟨cx, posC'⟩ := prepared
  dsimp only at run
  obtain ⟨work', _, run⟩ := bind_eq_ok run
  unfold cachedEvaluation at run
  split at run <;> rename_i localOK
  all_goals
    obtain ⟨result, retained, run⟩ := bind_eq_ok run
    simp only [pure, Except.pure, Except.ok.injEq] at run
    cases run
    refine ⟨_, result, states', work', retained, ?_, rfl⟩
    simp [cachedStep, cachedComponent, cachedEvaluation, context, localOK]

theorem familyStep_reference (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (hcp : childrenPrecede ex.dag.nodes = true) (results : Array CompResult)
    (states work : Nat) (members : Array Nat) {out : FamilyState}
    (run : familyStep cfg limits ex sg width (parentsOf ex.dag)
      ((results, states, work), Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0)
      members = .ok out) :
    ∃ result states' work', retainedResult sg.slack (component cfg ex sg width results.size members) = .ok result ∧
      out = ((results.push result, states', work'),
        Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0) := by
  obtain ⟨trace, result, states', work', retained, cached, head⟩ :=
    familyStep_cached cfg limits ex sg width _ results states work _ _ members run
  have reference := cachedStep_eq cfg ex sg width hcp #[] members results.size
  rw [cached] at reference
  simp only [Array.push_empty, Prod.mk.injEq] at reference
  have same : trace = component cfg ex sg width results.size members := by
    simpa using congrArg Array.toList reference.1
  refine ⟨result, states', work', by rwa [← same], Prod.ext head ?_⟩
  exact Prod.ext reference.2.1 reference.2.2

def componentFactor (ex : Expanded) (sg : UStage) (members : Array Nat) : Factor :=
  let cx := componentContext ex sg members
  { members := members.toList, cost := componentDelta cx (cx.phiE (fun _ => false) #[]).1 }

theorem retainedResult_row {cfg : Config} {ex : Expanded} {sg : UStage} {width index : Nat}
    {members : Array Nat} {result : CompResult}
    (run : retainedResult sg.slack (component cfg ex sg width index members) = .ok result) :
    ResultRow cfg sg.slack (componentFactor ex sg members) result := by
  have fields := retainedResult_fields run
  exact ⟨fields.2.1, fields.2.2.1, fields.2.2.2.1⟩

/-- Every successful prefix appends exactly one retained row per component,
in input order. The shared buffers are zero again at the fold boundary. -/
theorem familyFold_rows (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (hcp : childrenPrecede ex.dag.nodes = true) (members : List (Array Nat))
    (results : Array CompResult) (states work : Nat) {out : FamilyState}
    (run : members.foldlM (familyStep cfg limits ex sg width (parentsOf ex.dag))
      ((results, states, work), Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0) = .ok out) :
    ∃ added, out.1.1 = results ++ added ∧
      FamilyResults cfg sg.slack (members.map (componentFactor ex sg)) added.toList ∧
      out.2 = (Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0) := by
  induction members generalizing results states work with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at run
    cases run
    exact ⟨#[], by simp, List.Forall₂.nil, rfl⟩
  | cons m ms ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle, step, rest⟩ := bind_eq_ok run
    obtain ⟨result, states', work', retained, rfl⟩ :=
      familyStep_reference cfg limits ex sg width hcp results states work m step
    obtain ⟨added, eq, rows, cleared⟩ := ih (results.push result) states' work' rest
    refine ⟨#[result] ++ added, ?_, ?_, cleared⟩
    · rw [eq]
      simp only [Array.push_eq_append, Array.append_assoc]
    · simpa [FamilyResults]
        using List.Forall₂.cons (retainedResult_row retained) rows

theorem familyComponents_rows {cfg : Config} {limits : Limits} {ex : Expanded} {sg : UStage} {width : Nat}
    (hcp : childrenPrecede ex.dag.nodes = true) {results : Array CompResult} {states work : Nat}
    (run : familyComponents cfg limits ex sg width (parentsOf ex.dag) = .ok (results, states, work)) :
    FamilyResults cfg sg.slack (initialFactors ex sg) results.toList := by
  unfold familyComponents at run
  change ((sg.comps.foldlM (familyStep cfg limits ex sg width (parentsOf ex.dag))
    ((#[], 0, 0), Array.replicate sg.up.prep.dag.size 0, Array.replicate ex.dag.size 0)) >>= fun out =>
      pure out.1) = .ok (results, states, work) at run
  obtain ⟨out, folded, finished⟩ := bind_eq_ok run
  rw [← Array.foldlM_toList] at folded
  obtain ⟨added, eq, rows, _⟩ := familyFold_rows cfg limits ex sg width hcp sg.comps.toList #[] 0 0 folded
  simp only [pure, Except.pure, Except.ok.injEq] at finished
  have same : results = added := by
    have head := congrArg Prod.fst finished
    exact head.symm.trans (by simpa using eq)
  rw [same]
  exact rows

/-- Successful production neither omits nor duplicates a component row. -/
theorem familyComponents_count {cfg : Config} {limits : Limits} {ex : Expanded} {sg : UStage} {width : Nat}
    (hcp : childrenPrecede ex.dag.nodes = true) {results : Array CompResult} {states work : Nat}
    (run : familyComponents cfg limits ex sg width (parentsOf ex.dag) = .ok (results, states, work)) :
    results.size = sg.comps.size := by
  have lengths := (Ix.Sharing.Verify.SharingExact.forall₂_getElem (familyComponents_rows hcp run)).1
  simpa only [initialFactors, List.length_map, Array.length_toList] using lengths.symm

theorem dagWF_childrenPrecede {dag : Dag} (wf : DagWF dag) : childrenPrecede dag.nodes = true := by
  unfold childrenPrecede
  rw [Array.all_eq_true]
  intro i hi
  have bound : i < dag.nodes.size := by simpa using hi
  simp only [Array.getElem_zipIdx, Nat.zero_add]
  apply Array.all_eq_true.mpr
  intro j hj
  have child := wf.precede i bound (dag.nodes[i].children[j]) (by
    rw [getElem!_pos dag.nodes i bound]
    exact Array.getElem_mem hj)
  simpa using child

/-- The actual producer supplies all row hypotheses of the minimum theorem.
Only successful production/selection and the existing structural checks remain. -/
theorem familyComponents_least (cfg : Config) (limits : Limits) (ex : Expanded) (width : Nat)
    (wf : DagWF ex.dag)
    (checked : let sg := uniformStage width ex (Prep.ofDag ex.dag)
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    {results : Array CompResult} {states work : Nat}
    (produced : let sg := uniformStage width ex (Prep.ofDag ex.dag)
      familyComponents cfg limits ex sg width (parentsOf ex.dag) = .ok (results, states, work))
    {delta : _root_.Int} {set : Array Nat} {lowerBracket : Bool}
    (selected : let sg := uniformStage width ex (Prep.ofDag ex.dag)
      uniformKnapsack limits sg.cs.size results = .ok (delta, set, lowerBracket)) :
    let sg := uniformStage width ex (Prep.ofDag ex.dag)
    LeastProductOutput cfg sg.cs.size (initialFactors ex sg) delta set :=
  initial_knapsack_least cfg ex width wf checked results
    (familyComponents_rows (dagWF_childrenPrecede wf) produced) selected

/-- A successful `familyUniform` run really consumed the produced
family rows and their least selection. This extracts its internal witness;
it does not identify the semantic length or output of `uniformFinishF`. -/
theorem familyUniform_selection (cfg : Config) (limits : Limits) (ex : Expanded) (width : Nat)
    (wf : DagWF ex.dag) {out : UniformSharingResult}
    (run : familyUniform cfg limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) width = .ok out) :
    let sg := uniformStage width ex (Prep.ofDag ex.dag)
    ∃ results states work delta set lowerBracket,
      familyComponents cfg limits ex sg width (parentsOf ex.dag) = .ok (results, states, work) ∧
      uniformKnapsack limits sg.cs.size results = .ok (delta, set, lowerBracket) ∧
      LeastProductOutput cfg sg.cs.size (initialFactors ex sg) delta set := by
  unfold familyUniform at run
  rw [← uniformStage_eq_F] at run
  dsimp only at run
  split at run
  · rename_i checked
    obtain ⟨⟨results, states, work⟩, produced, rest⟩ := bind_eq_ok run
    obtain ⟨⟨delta, set, lowerBracket⟩, selected, _⟩ := bind_eq_ok rest
    refine ⟨results, states, work, delta, set, lowerBracket, produced, selected, ?_⟩
    exact familyComponents_least cfg limits ex width wf (by simpa using checked) produced selected
  · cases run

end Ix.Sharing.Family

#guard_kernel_axioms Ix.Sharing.Family.retainedResult_fields [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyStep_cached [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyStep_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyFold_rows [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyComponents_rows [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyComponents_count [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyComponents_least [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyUniform_selection [propext, Classical.choice, Quot.sound]
