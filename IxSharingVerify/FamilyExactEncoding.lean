import IxSharingVerify.FamilyExactCompatibility

/-! Actual old/new uniform finishers and tiered candidates have identical
encodings under the initial exact-family gate. Performance statistics are
projected out; successful runs and the old default-search flag stay explicit.
Complete constant serialization is a separate wrapper bridge. -/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.Tiered
open Ix.Sharing.Verify.SharingExact (bind_eq_ok)

theorem uniformChoose_facts {width : Nat} {limits : Limits} {ex : Expanded} {prep : Prep}
    {choice : UniformChoice} (run : uniformChoose width limits ex prep = .ok choice) :
    choice.facts = graphFacts ex.dag ex.roots := by
  unfold uniformChoose at run
  dsimp only at run
  split at run
  · obtain ⟨⟨_, _, _⟩, _, run⟩ := bind_eq_ok run
    obtain ⟨⟨_, _, _⟩, _, run⟩ := bind_eq_ok run
    dsimp only at run
    split at run
    · cases run
    · split at run
      · cases run
      · cases run; rfl
  · cases run

/-- Same stored IDs give the same pinned order and actual materialization;
the choice's counters and lower-bracket flag do not enter this comparison. -/
theorem familyUniform_exact_encoding {cfg : Config} {limits : Limits} {ex : Expanded} {width : Nat}
    {old fresh : UniformSharingResult}
    (defaultSearch : limits.uniformSubsetSearch = false) (gate : ExactInitial cfg ex width)
    (oldRun : optimizeUniformExpanded width limits ex = .ok old)
    (freshRun : familyUniform cfg limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) width = .ok fresh) :
    fresh.result.sharing = old.result.sharing ∧ fresh.result.roots = old.result.roots ∧
      fresh.result.tableTerms = old.result.tableTerms ∧ fresh.stored = old.stored := by
  have same := (familyUniform_exact_match defaultSearch gate oldRun freshRun).1
  obtain ⟨_, wf, roots, marks, spines, choice, chosen, finish⟩ := optimizeUniform_parts oldRun
  obtain ⟨_, _, _, _, finished⟩ := familyUniform_finished wf spines roots (reach_of_marks wf roots marks) freshRun
  obtain ⟨_, _, stored, table, _, oldWork, oldMat, _⟩ := uniformFinish_spec finish
  have facts := uniformChoose_facts chosen
  have tableSame : fresh.result.tableTerms = old.result.tableTerms := by
    rw [finished.table, table, facts, same, stored]
  obtain ⟨freshWork, freshMat⟩ := finished.materialized
  rw [tableSame, same, stored, table] at freshMat
  rw [freshMat] at oldMat
  have outputs := Except.ok.inj oldMat
  exact ⟨congrArg (fun p => p.1) outputs, congrArg (fun p => p.2.1) outputs, tableSame, same⟩

/-- Encoding and precisely the decision fields read by `tieredBetter`. -/
def selectionOf (out : TieredSharingResult) :=
  (encodingOf out, out.phase1.stored, out.stats.w, out.stats.phase3LayoutBytes)

theorem tieredPick_selection {a b c x y z : TieredSharingResult}
    (first : selectionOf a = selectionOf x) (second : selectionOf b = selectionOf y)
    (third : selectionOf c = selectionOf z) :
    selectionOf (tieredPick a b c) = selectionOf (tieredPick x y z) := by
  have better {left right left' right' : TieredSharingResult}
      (hl : selectionOf left = selectionOf left') (hr : selectionOf right = selectionOf right') :
      tieredBetter left right = tieredBetter left' right' := by
    have sl := congrArg (fun p => p.2.1) hl
    have sr := congrArg (fun p => p.2.1) hr
    have wl := congrArg (fun p => p.2.2.1) hl
    have wr := congrArg (fun p => p.2.2.1) hr
    have bl := congrArg (fun p => p.2.2.2) hl
    have br := congrArg (fun p => p.2.2.2) hr
    unfold tieredBetter
    rw [show left.phase1.stored = left'.phase1.stored from sl,
      show right.phase1.stored = right'.phase1.stored from sr,
      show left.stats.w = left'.stats.w from wl, show right.stats.w = right'.stats.w from wr,
      show left.stats.phase3LayoutBytes = left'.stats.phase3LayoutBytes from bl,
      show right.stats.phase3LayoutBytes = right'.stats.phase3LayoutBytes from br]
  have step {left right left' right' : TieredSharingResult}
      (hl : selectionOf left = selectionOf left') (hr : selectionOf right = selectionOf right') :
      selectionOf (if tieredBetter right left then right else left) =
        selectionOf (if tieredBetter right' left' then right' else left') := by
    rw [better hr hl]; split <;> assumption
  have result := step (step first second) third
  simpa [tieredPick, selectionOf, encodingOf] using result

/-- Actual allocation and rematerialization are the same functions of the
equal uniform encoding, so all selection-relevant fields agree. -/
theorem familyAtWidth_exact_selection {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {ex : Expanded} {width candidates : Nat} {old fresh : TieredSharingResult}
    (defaultSearch : limits.uniformSubsetSearch = false) (gate : ExactInitial cfg ex width)
    (oldRun : tieredAtWidth layout limits ex width = .ok old)
    (freshRun : familyAtWidth cfg layout limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) candidates width = .ok fresh) : selectionOf fresh = selectionOf old := by
  obtain ⟨oldU, oldA, oldM, oldUniform, oldAllocate, oldMaterialize, rfl⟩ := tieredAtWidth_parts oldRun
  obtain ⟨freshU, freshA, freshM, freshUniform, freshAllocate, freshMaterialize, rfl⟩ := familyAtWidth_parts freshRun
  obtain ⟨sharing, roots, table, stored⟩ := familyUniform_exact_encoding defaultSearch gate oldUniform freshUniform
  rw [table, sharing, roots, oldAllocate] at freshAllocate
  cases Except.ok.inj freshAllocate
  rw [sharing, roots, oldMaterialize] at freshMaterialize
  cases Except.ok.inj freshMaterialize
  simp only [selectionOf, encodingOf, tieredResult_eq_F, tieredResultF]
  rw [stored]

/-- At all three applicable widths, compare ACTUAL successful candidates.
The old zero-counter core and the family entry differ only in statistics;
the existing transport theorem supplies the corresponding family run. -/
theorem familyExpanded_exact_encoding {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {ex : Expanded} {old fresh : TieredSharingResult}
    (defaultSearch : limits.uniformSubsetSearch = false) (gates : ExactAllWidths cfg ex)
    (oldRun : canonicalTieredExpanded layout limits ex = .ok old)
    (freshRun : familyExpanded cfg layout limits ex = .ok fresh) : encodingOf fresh = encodingOf old := by
  obtain ⟨core, oldCore, rfl, _, _, _, _, _⟩ := canonicalTiered_core oldRun
  let zero : Expanded := { ex with visits := 0, internedNodes := 0 }
  have newCore := familyExpanded_transport_success (cfg := cfg) (layout := layout) (limits := limits)
    (first := ex) (second := zero) (out := fresh) rfl rfl freshRun
  unfold canonicalTieredCore at oldCore
  obtain ⟨o1, old1, oldCore⟩ := bind_eq_ok oldCore
  obtain ⟨o2, old2, oldCore⟩ := bind_eq_ok oldCore
  obtain ⟨o3, old3, oldCore⟩ := bind_eq_ok oldCore
  unfold familyExpanded at newCore
  obtain ⟨_, _, newCore⟩ := bind_eq_ok newCore
  obtain ⟨_, _, newCore⟩ := bind_eq_ok newCore
  obtain ⟨picked, pickedRun, returned⟩ := bind_eq_ok newCore
  rw [tieredCandidates_eq] at pickedRun
  obtain ⟨n1, new1, pickedRun⟩ := bind_eq_ok pickedRun
  obtain ⟨n2, new2, pickedRun⟩ := bind_eq_ok pickedRun
  obtain ⟨n3, new3, pickedRun⟩ := bind_eq_ok pickedRun
  have first := familyAtWidth_exact_selection defaultSearch (show ExactInitial cfg zero 1 from gates 1 (by simp)) old1 new1
  have second := familyAtWidth_exact_selection defaultSearch (show ExactInitial cfg zero 2 from gates 2 (by simp)) old2 new2
  have third := familyAtWidth_exact_selection defaultSearch (show ExactInitial cfg zero 3 from gates 3 (by simp)) old3 new3
  have same := congrArg (fun p => p.1) (tieredPick_selection first second third)
  have oldEncoded : encodingOf (tieredPick o1 o2 o3) = encodingOf core := congrArg encodingOf (Except.ok.inj oldCore)
  have newEncoded : encodingOf (tieredPick n1 n2 n3) = encodingOf fresh := by
    have chosen := Except.ok.inj pickedRun
    have out := congrArg encodingOf (Except.ok.inj returned)
    change encodingOf picked = encodingOf fresh at out
    rw [← chosen] at out
    exact out
  exact newEncoded.symm.trans (same.trans oldEncoded)

end Ix.Sharing.Family

#guard_kernel_axioms Ix.Sharing.Family.uniformChoose_facts [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyUniform_exact_encoding [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.tieredPick_selection [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyAtWidth_exact_selection [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyExpanded_exact_encoding [propext, Classical.choice, Quot.sound]
