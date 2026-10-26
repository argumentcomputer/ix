import IxSharingVerify.FamilyFinish
import IxSharingVerify.TieredWire

/-! Checked successful tiered family output. The phase-3 inequality below
uses the executed rematerialization guard; it does not prove that the guard
can never refuse a valid input. Totality and whole-constant encoding follow
separately. No exact-search phase-1 success premise is used. -/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.Tiered
open Ix.Sharing.Verify.SharingExact (Desc bind_eq_ok SharesIn DagModel substShares
  materializeTable_parts materializeTable_backward forall₂_getElem)

/-- The actual three phases, with cached rematerialization rewritten to
the existing reference function by its proved equality. -/
theorem familyAtWidth_parts {cfg : Config} {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {width candidates : Nat} {out : TieredSharingResult}
    (run : familyAtWidth cfg layout limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) candidates width = .ok out) :
    ∃ uniform allocation materialized,
      familyUniform cfg limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
        (parentsOf ex.dag) width = .ok uniform ∧
      allocate layout limits ex.dag (graphFacts ex.dag ex.roots).deg uniform.result.tableTerms
        uniform.result.sharing uniform.result.roots = .ok allocation ∧
      rematerialize layout limits ex allocation.order
        (layoutBytes layout uniform.result.sharing uniform.result.roots) = .ok materialized ∧
      out = tieredResultF layout width uniform allocation materialized candidates
        (layoutBytes layout uniform.result.sharing uniform.result.roots) := by
  unfold familyAtWidth at run
  obtain ⟨uniform, first, run⟩ := bind_eq_ok run
  obtain ⟨allocation, second, run⟩ := bind_eq_ok run
  obtain ⟨materialized, third, run⟩ := bind_eq_ok run
  rw [← rematerialize_eq_P] at third
  exact ⟨uniform, allocation, materialized, first, second, third, (Except.ok.inj run).symm⟩

theorem familyAtWidth_width {cfg : Config} {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {width candidates : Nat} {out : TieredSharingResult}
    (run : familyAtWidth cfg layout limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) candidates width = .ok out) : out.stats.w = width := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := familyAtWidth_parts run
  rfl

/-- Format and backward Shares follow from the actual successful phase-3
checks and materializer, independently of phase-1 search optimality. -/
theorem rematerialize_format {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {order : Array Nat} {phase1 : Nat} {m : Rematerialized}
    (run : rematerialize layout limits ex order phase1 = .ok m) : FormatOK m.entries m.roots := by
  obtain ⟨work, materialized, _, _, wire⟩ := rematerialize_parts run
  obtain ⟨bound, _, _⟩ := materializeTable_parts _ _ _ _ _ materialized
  obtain ⟨size, entriesBack, rootsBack⟩ := materializeTable_backward _ _ _ _ _ (by omega) materialized
  rw [Array.all_eq_true'] at wire
  have wf : ∀ e ∈ (m.entries ++ m.roots).toList, e.wireWF :=
    fun e he => wireWF_of_check (wire e (Array.mem_toList_iff.mp he))
  refine ⟨fun e he => wf e (by simp [he]), fun e he => wf e (by simp [he]),
    by omega, entriesBack, ?_⟩
  intro e he
  rw [size]
  exact rootsBack e he

/-- Observable guarantees of a successful tiered family candidate. The
semantic statements are relative to any model of the input DAG. -/
structure TieredOutput (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (out : TieredSharingResult) : Prop where
  format : FormatOK out.result.sharing out.result.roots
  table : out.result.tableTerms.toList.Perm out.phase1.stored.toList
  model : out.result.modelBytes = layoutBytes layout out.result.sharing out.result.roots
  measured : out.result.variableBytes = out.result.modelBytes
  phase3_le : out.result.modelBytes ≤ layoutBytes layout out.phase1.result.sharing out.phase1.result.roots
  sizes : out.result.sharing.size = out.result.tableTerms.size ∧ out.result.roots.size = ex.roots.size
  meaning : ∀ (E : Nat → Ixon.Expr), DagModel ex.dag E →
    (∀ k (hk : k < out.result.sharing.size),
      substShares (fun i => E out.result.tableTerms[i]!) out.result.sharing[k] = E out.result.tableTerms[k]!) ∧
    List.Forall₂ (fun r e => substShares (fun i => E out.result.tableTerms[i]!) e = E r)
      ex.roots.toList out.result.roots.toList
  reexpanded : ∃ visits, reexpand limits ex.dag out.result.sharing out.result.roots =
    .ok (out.result.tableTerms, ex.roots, visits)

theorem tieredResult_checked {layout : ShareLayout} {limits : Limits} {ex : Expanded} {width candidates : Nat}
    (wf : DagWF ex.dag) (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    {uniform : UniformSharingResult} {allocation : Allocation} {m : Rematerialized}
    (finished : UniformFinished width limits ex uniform)
    (allocated : allocate layout limits ex.dag (graphFacts ex.dag ex.roots).deg uniform.result.tableTerms
      uniform.result.sharing uniform.result.roots = .ok allocation)
    (materialized : rematerialize layout limits ex allocation.order
      (layoutBytes layout uniform.result.sharing uniform.result.roots) = .ok m) :
    TieredOutput layout limits ex (tieredResultF layout width uniform allocation m candidates
      (layoutBytes layout uniform.result.sharing uniform.result.roots)) := by
  obtain ⟨size, _, rootParts, bytes, bound, _, _, meaning, expanded⟩ := rematerialize_spec wf roots materialized
  have rootLength := (forall₂_getElem rootParts).1
  have measure := (rematerialize_measured materialized).2
  have permutation := (allocate_spec allocated).2.2.1
  exact ⟨rematerialize_format materialized, permutation.trans finished.permutation,
    bytes, measure.symm, bound, ⟨size, by change m.roots.size = ex.roots.size; simpa using rootLength.symm⟩,
    meaning, expanded⟩

/-- The real family phase-1 witness is retained beside the final checked
tiered output; phase 3 is not asserted to be a global byte minimum. -/
theorem familyAtWidth_checked {cfg : Config} {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {width candidates : Nat} (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    {out : TieredSharingResult}
    (run : familyAtWidth cfg layout limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) candidates width = .ok out) :
    (∃ delta set, LeastProductOutput cfg (stg width ex).cs.size (initialFactors ex (stg width ex)) delta set ∧
      out.phase1.stored = mergeSorted (stg width ex).cs set ∧ UniformFinished width limits ex out.phase1) ∧
      TieredOutput layout limits ex out := by
  obtain ⟨uniform, allocation, materialized, first, second, third, rfl⟩ := familyAtWidth_parts run
  obtain ⟨delta, set, selected, stored, finished⟩ := familyUniform_finished wf roots reachable first
  exact ⟨⟨delta, set, selected, stored, finished⟩, tieredResult_checked wf roots finished second third⟩

/-- The actual expanded wrapper returns a successful width-1/2/3 candidate,
changing only its recorded candidate lengths and expansion statistics. -/
theorem familyExpanded_selected {cfg : Config} {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {out : TieredSharingResult} (run : familyExpanded cfg layout limits ex = .ok out) :
    ∃ width candidate lengths, width ∈ [1, 2, 3] ∧
      familyAtWidth cfg layout limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
        (parentsOf ex.dag) (tieredCandidateCount ex.dag.size (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots))
        width = .ok candidate ∧
      out = withExpansionStats ex { candidate with stats := { candidate.stats with candidateLengths := lengths } } := by
  unfold familyExpanded at run
  obtain ⟨_, _, run⟩ := bind_eq_ok run
  obtain ⟨picked, selected, returned⟩ := bind_eq_ok run
  rw [tieredCandidates_eq] at selected
  obtain ⟨c1, first, selected⟩ := bind_eq_ok selected
  obtain ⟨c2, second, selected⟩ := bind_eq_ok selected
  obtain ⟨c3, third, selected⟩ := bind_eq_ok selected
  have pickEq := (Except.ok.inj selected).symm
  have outEq := (Except.ok.inj returned).symm
  let best := #[c2, c3].foldl (fun b c => if tieredBetter c b then c else b) c1
  let lengths := #[c1, c2, c3].map (fun c => (c.stats.w, c.stats.phase3LayoutBytes))
  have origin := (select_three c1 c2 c3 (familyAtWidth_width first)
    (familyAtWidth_width second) (familyAtWidth_width third)).1
  have same : out = withExpansionStats ex { best with stats := { best.stats with candidateLengths := lengths } } := by
    rw [outEq, pickEq]
    rfl
  rcases origin with eq | eq | eq
  · exact ⟨1, c1, _, by simp, first, by simpa only [best, eq] using same⟩
  · exact ⟨2, c2, _, by simp, second, by simpa only [best, eq] using same⟩
  · exact ⟨3, c3, _, by simp, third, by simpa only [best, eq] using same⟩

theorem TieredOutput.recordStats {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {candidate : TieredSharingResult} (checked : TieredOutput layout limits ex candidate)
    (lengths : Array (Nat × Nat)) :
    TieredOutput layout limits ex
      (withExpansionStats ex { candidate with stats := { candidate.stats with candidateLengths := lengths } }) :=
  { format := checked.format, table := checked.table, model := checked.model,
    measured := checked.measured, phase3_le := checked.phase3_le, sizes := checked.sizes,
    meaning := checked.meaning, reexpanded := checked.reexpanded }

/-- Transport the actual successful selected width, its uniform family
witness and all tiered output facts through statistics-only recording.
Domain-guard discharge and unconditional success remain separate. -/
theorem familyExpanded_checked {cfg : Config} {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    {out : TieredSharingResult} (run : familyExpanded cfg layout limits ex = .ok out) :
    (∃ width, width ∈ [1, 2, 3] ∧ ∃ delta set,
      LeastProductOutput cfg (stg width ex).cs.size (initialFactors ex (stg width ex)) delta set ∧
      out.phase1.stored = mergeSorted (stg width ex).cs set ∧ UniformFinished width limits ex out.phase1) ∧
      TieredOutput layout limits ex out := by
  obtain ⟨width, candidate, lengths, admitted, candidateRun, rfl⟩ := familyExpanded_selected run
  obtain ⟨⟨delta, set, least, stored, finished⟩, checked⟩ :=
    familyAtWidth_checked wf roots reachable candidateRun
  refine ⟨⟨width, admitted, delta, set, least, stored, ?_⟩, checked.recordStats lengths⟩
  exact {
    inBounds := finished.inBounds, inClass := finished.inClass
    table := finished.table, permutation := finished.permutation, model := finished.model
    materialized := finished.materialized, reexpanded := finished.reexpanded, measured := finished.measured }

/-- A compact exported format/semantics/length view of the successful
expanded entry; no claim is made about whole-constant serialization. -/
theorem familyExpanded_output {cfg : Config} {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    {out : TieredSharingResult} (run : familyExpanded cfg layout limits ex = .ok out) :
    FormatOK out.result.sharing out.result.roots ∧
      out.result.variableBytes = layoutBytes layout out.result.sharing out.result.roots ∧
      out.result.modelBytes ≤ layoutBytes layout out.phase1.result.sharing out.phase1.result.roots ∧
      ∃ visits, reexpand limits ex.dag out.result.sharing out.result.roots =
        .ok (out.result.tableTerms, ex.roots, visits) := by
  have checked := (familyExpanded_checked wf roots reachable run).2
  exact ⟨checked.format, checked.measured.trans checked.model, checked.phase3_le, checked.reexpanded⟩

end Ix.Sharing.Family

#guard_kernel_axioms Ix.Sharing.Family.familyAtWidth_parts [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.rematerialize_format [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.tieredResult_checked [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyAtWidth_checked [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyExpanded_selected [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyExpanded_checked [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyExpanded_output [propext, Classical.choice, Quot.sound]
