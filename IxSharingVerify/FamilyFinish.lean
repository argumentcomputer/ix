import IxSharingVerify.FamilyCost

/-! A successful experimental uniform result retains the actual family
selection, semantic model, pinned table and checked roots. Tiered allocation,
rematerialization and whole-constant serialization are separate. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (Desc bind_eq_ok)

def familyModel (ex : Expanded) (width : Nat) (delta : _root_.Int) (set : Array Nat) : _root_.Int :=
  (csBase ex (Prep.ofDag ex.dag) (stg width ex) : _root_.Int) + delta +
    (tag0Size ((stg width ex).cs.size + set.size) : _root_.Int)

/-- The exact record constructed by `familyUniform`, exposed only for proofs. -/
def familyChoice (ex : Expanded) (width : Nat) (states work : Nat)
    (delta : _root_.Int) (set : Array Nat) (lowerBracket : Bool) : UniformChoice :=
  { facts := graphFacts ex.dag ex.roots, certainStored := (stg width ex).cs,
    certainExcluded := (stg width ex).ce, uncertain := (stg width ex).unc,
    lowDegree := (stg width ex).low, components := (stg width ex).comps,
    stored := mergeSorted (stg width ex).cs set, model := (familyModel ex width delta set).toNat,
    states, costEvals := work, lowerBracket }

/-- Extract the actual component/knapsack runs and the exact choice passed
to the fast finisher, including the executed model and budget guards. -/
theorem familyUniform_finish {cfg : Config} {limits : Limits} {ex : Expanded} {width : Nat}
    {out : UniformSharingResult}
    (run : familyUniform cfg limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) width = .ok out) :
    ∃ results states work delta set lowerBracket,
      componentsChecked ex.dag (stg width ex).cls (stg width ex).opaq (stg width ex).comps
        (componentLabels ex.dag.size (stg width ex).comps) = true ∧
      familyComponents cfg limits ex (stg width ex) width (parentsOf ex.dag) = .ok (results, states, work) ∧
      uniformKnapsack limits (stg width ex).cs.size results = .ok (delta, set, lowerBracket) ∧
      0 ≤ familyModel ex width delta set ∧ (familyModel ex width delta set).toNat ≤ limits.maxOutputBytes ∧
      uniformFinishF width limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots).deg
        (familyChoice ex width states work delta set lowerBracket) = .ok out := by
  unfold familyUniform at run
  rw [← uniformStage_eq_F] at run
  dsimp only at run
  split at run
  · rename_i checked
    obtain ⟨⟨results, states, work⟩, produced, run⟩ := bind_eq_ok run
    obtain ⟨⟨delta, set, lowerBracket⟩, chosen, run⟩ := bind_eq_ok run
    dsimp only at run
    split at run
    · cases run
    · rename_i nonnegative
      split at run
      · cases run
      · rename_i bounded
        exact ⟨results, states, work, delta, set, lowerBracket, checked, produced, chosen,
          by simpa [familyModel] using Int.le_of_not_gt nonnegative,
          by simpa [familyModel] using Nat.le_of_not_gt bounded, run⟩
  · cases run

/-- Successful re-expansion identifies both the returned table and roots.
This exposes existing finisher guards without changing their statements. -/
theorem uniformFinish_reexpanded {width : Nat} {limits : Limits} {ex : Expanded} {prep : Prep}
    {choice : UniformChoice} {out : UniformSharingResult}
    (run : uniformFinish width limits ex prep choice = .ok out) :
    ∃ visits, reexpand limits ex.dag out.result.sharing out.result.roots =
      .ok (out.result.tableTerms, ex.roots, visits) := by
  unfold uniformFinish at run
  dsimp only at run
  split at run
  · split at run
    · obtain ⟨⟨entries, roots, predicted, work⟩, _, run⟩ := bind_eq_ok run
      dsimp only at run
      split at run
      · obtain ⟨⟨entryIds, rootIds, visits⟩, expanded, run⟩ := bind_eq_ok run
        dsimp only at run
        split at run
        · rename_i table
          split at run
          · rename_i rootsSame
            cases run
            have tableEq : entryIds = pinnedOrder ex.dag choice.facts.deg choice.stored := by simpa using table
            have rootsEq : rootIds = ex.roots := by simpa using rootsSame
            exact ⟨visits, by simpa only [tableEq, rootsEq] using expanded⟩
          · cases run
        · cases run
      · cases run
    · cases run
  · cases run

/-- Returned uniform data and the successful materialization/re-expansion
witnesses. Model bytes denote uniform semantic cost, not yet serialization. -/
structure UniformFinished (width : Nat) (limits : Limits) (ex : Expanded) (out : UniformSharingResult) : Prop where
  inBounds : ∀ t ∈ out.stored.toList, t < ex.dag.size
  inClass : InClass ex.dag ex.roots out.stored.toList
  table : out.result.tableTerms = pinnedOrder ex.dag (graphFacts ex.dag ex.roots).deg out.stored
  permutation : out.result.tableTerms.toList.Perm out.stored.toList
  model : out.result.modelBytes = ulen ex.dag width ex.roots out.stored.toList
  materialized : ∃ work, (Prep.ofDag ex.dag).materializeDependent out.result.tableTerms ex.roots
    (out.stored.foldl (fun acc t => acc.set! t (some width)) (Array.replicate ex.dag.size none))
    limits = .ok (out.result.sharing, out.result.roots, out.result.modelBytes, work)
  reexpanded : ∃ visits, reexpand limits ex.dag out.result.sharing out.result.roots =
    .ok (out.result.tableTerms, ex.roots, visits)
  measured : out.result.variableBytes = tag0Size out.result.sharing.size +
    exprsSize out.result.sharing + exprsSize out.result.roots

/-- Package the existing finisher specification for any choice whose
reported model is known to equal the semantic uniform cost. -/
theorem uniformFinish_finished {width : Nat} {limits : Limits} {ex : Expanded}
    {choice : UniformChoice} {out : UniformSharingResult}
    (facts : choice.facts = graphFacts ex.dag ex.roots)
    (model : choice.model = ulen ex.dag width ex.roots choice.stored.toList)
    (run : uniformFinish width limits ex (Prep.ofDag ex.dag) choice = .ok out) :
    UniformFinished width limits ex out := by
  obtain ⟨bounds, checked, stored, table, modelBytes, work, materialized, measured⟩ := uniformFinish_spec run
  have permutation : out.result.tableTerms.toList.Perm out.stored.toList := by
    rw [table, stored]; exact pinnedOrder_perm _ _ _
  refine ⟨?_, ?_, ?_, permutation, ?_, ?_, uniformFinish_reexpanded run, measured⟩
  · rw [stored]; exact bounds
  · rw [stored]; exact inClass_of_check bounds checked
  · rw [table, stored, facts]
  · rw [modelBytes, stored]; exact model
  · exact ⟨work, by simpa only [table, stored, modelBytes] using materialized⟩

/-- Successful materialization preserves the number of roots and produces
one body per pinned table entry, within its existing wire-count bound. -/
theorem UniformFinished.sizes {width : Nat} {limits : Limits} {ex : Expanded} {out : UniformSharingResult}
    (finished : UniformFinished width limits ex out) :
    out.result.tableTerms.size < UInt64.size ∧
      out.result.sharing.size = out.result.tableTerms.size ∧ out.result.roots.size = ex.roots.size := by
  obtain ⟨work, materialized⟩ := finished.materialized
  obtain ⟨bound, entries, roots⟩ := Ix.Sharing.Verify.SharingExact.materializeDependent_parts
    _ _ _ _ _ materialized
  have entriesLength := (Ix.Sharing.Verify.SharingExact.forall₂_getElem entries).1
  have rootsLength := (Ix.Sharing.Verify.SharingExact.forall₂_getElem roots).1
  exact ⟨bound, by simpa using entriesLength.symm, by simpa using rootsLength.symm⟩

/-- Actual successful family selection reaches the returned stored array,
model, pinned table and checked roots. The semantic domain assumptions are
explicit; neither production success nor byte/model equality is presumed. -/
theorem familyUniform_finished {cfg : Config} {limits : Limits} {ex : Expanded} {width : Nat}
    (wf : DagWF ex.dag) (spines : SpinesFit (Prep.ofDag ex.dag))
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    {out : UniformSharingResult}
    (run : familyUniform cfg limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) width = .ok out) :
    ∃ delta set, LeastProductOutput cfg (stg width ex).cs.size (initialFactors ex (stg width ex)) delta set ∧
      out.stored = mergeSorted (stg width ex).cs set ∧ UniformFinished width limits ex out := by
  obtain ⟨results, states, work, delta, set, lowerBracket, checked, produced, chosen, _, _, finish⟩ :=
    familyUniform_finish run
  have selected := familyComponents_least cfg limits ex width wf checked produced chosen
  have cost := (selected_model_nonnegative wf spines roots reachable checked selected).2
  have standard : uniformFinish width limits ex (Prep.ofDag ex.dag)
      (familyChoice ex width states work delta set lowerBracket) = .ok out := by
    rw [uniformFinish_eq_F]
    exact finish
  have stored := (uniformFinish_spec standard).2.2.1
  exact ⟨delta, set, selected, stored, uniformFinish_finished rfl cost standard⟩

/-- The reported model of the returned uniform result is minimal over the
same finite initial family product, with the initial CS fixed. -/
theorem familyUniform_model_minimum {cfg : Config} {limits : Limits} {ex : Expanded} {width : Nat}
    (wf : DagWF ex.dag) (spines : SpinesFit (Prep.ofDag ex.dag))
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    {out : UniformSharingResult}
    (run : familyUniform cfg limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) width = .ok out) :
    ∀ other, ProductMember cfg (initialFactors ex (stg width ex)) other →
      out.result.modelBytes ≤ ulen ex.dag width ex.roots
        (mergeSorted (stg width ex).cs (other.foldl mergeSorted #[])).toList := by
  obtain ⟨results, states, work, delta, set, lowerBracket, checked, produced, chosen, _, _, _⟩ :=
    familyUniform_finish run
  obtain ⟨delta', set', selected, stored, finished⟩ := familyUniform_finished wf spines roots reachable run
  obtain ⟨sets, minimum, _, setEq, _, _⟩ := selected
  intro other member
  rw [finished.model, stored, setEq]
  exact initial_minimum_cost wf spines roots reachable checked minimum other member

/-- Named returned-field projection for later pipeline composition. It
does not import an exact-search success premise or assert final serialization. -/
theorem familyUniform_result_fields {cfg : Config} {limits : Limits} {ex : Expanded} {width : Nat}
    (wf : DagWF ex.dag) (spines : SpinesFit (Prep.ofDag ex.dag))
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    {out : UniformSharingResult}
    (run : familyUniform cfg limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) width = .ok out) :
    out.result.tableTerms.toList.Perm out.stored.toList ∧
      out.result.modelBytes = ulen ex.dag width ex.roots out.stored.toList ∧
      out.result.roots.size = ex.roots.size ∧
      ∃ visits, reexpand limits ex.dag out.result.sharing out.result.roots =
        .ok (out.result.tableTerms, ex.roots, visits) := by
  obtain ⟨_, _, _, _, finished⟩ := familyUniform_finished wf spines roots reachable run
  exact ⟨finished.permutation, finished.model, finished.sizes.2.2, finished.reexpanded⟩

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyUniform_finish [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.uniformFinish_reexpanded [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.uniformFinish_finished [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.UniformFinished.sizes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyUniform_finished [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyUniform_model_minimum [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.familyUniform_result_fields [propext, Classical.choice, Quot.sound]
