import IxSharingVerify.FamilyExactEncoding

/-! Conditional T4 for the actual production/default old normalization API.
Both real wrappers must succeed at the same layout/limits, and every initial
component of their common expansion must be exact at widths 1, 2 and 3.
The conclusion compares complete constants/bytes, never performance statistics.
This is not unconditional success, global byte optimality or a production cutover. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.SharingExact (bind_eq_ok)

/-- The size gate is attached to the actual shared-input expansion. Wrapper
success supplies that expansion, so no additional success premise is needed. -/
def ExactInput (cfg : Config) (limits : Limits) (input : Ixon.Constant) : Prop :=
  ∀ expanded, expand limits input.sharing (constantInfoRoots input.info) true = .ok expanded →
    ExactAllWidths cfg expanded

theorem exactInput_of_expand {cfg : Config} {limits : Limits} {input : Ixon.Constant} {expanded : Expanded}
    (run : expand limits input.sharing (constantInfoRoots input.info) true = .ok expanded)
    (gates : ExactAllWidths cfg expanded) : ExactInput cfg limits input := by
  intro actual success
  rw [run] at success
  cases Except.ok.inj success
  exact gates

/-- Extract the existing API's actual shared expansion, tiered run and
root write-back, without replacing it by a declarative reference optimizer. -/
theorem normalizeConstantSharingTiered_parts {layout : ShareLayout} {limits : Limits}
    {input output : Ixon.Constant} (run : Exact.Reference.normalizeConstantSharingTiered layout input limits = .ok output) :
    ∃ expanded result info,
      expand limits input.sharing (constantInfoRoots input.info) true = .ok expanded ∧
      canonicalTieredExpanded layout limits expanded = .ok result ∧
      withRoots input.info result.result.roots = .ok info ∧
      output = { input with info, sharing := result.result.sharing } := by
  unfold Exact.Reference.normalizeConstantSharingTiered at run
  obtain ⟨result, normalized, run⟩ := bind_eq_ok run
  unfold Exact.Reference.canonicalSharingTieredTable at normalized
  obtain ⟨expanded, expandedRun, tiered⟩ := bind_eq_ok normalized
  obtain ⟨info, written, run⟩ := bind_eq_ok run
  exact ⟨expanded, result, info, expandedRun, tiered, written, (Except.ok.inj run).symm⟩

/-- Complete output-constant compatibility, including unchanged payload
fields, refs and univs. The old default-search flag and both API successes
remain explicit; arbitrary previous sharing is handled by their real expansion. -/
theorem normalizeFamily_exact_constant {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input old fresh : Ixon.Constant} {result : TieredSharingResult}
    (defaultSearch : limits.uniformSubsetSearch = false) (gates : ExactInput cfg limits input)
    (oldRun : Exact.Reference.normalizeConstantSharingTiered layout input limits = .ok old)
    (freshRun : normalizeFamily cfg layout input limits = .ok (fresh, result)) : fresh = old := by
  obtain ⟨oldEx, oldResult, oldInfo, oldExpand, oldTiered, oldWritten, oldOutput⟩ :=
    normalizeConstantSharingTiered_parts oldRun
  obtain ⟨freshEx, freshInfo, freshExpand, freshTiered, freshWritten, freshOutput⟩ := normalizeFamily_parts freshRun
  rw [freshExpand] at oldExpand
  cases Except.ok.inj oldExpand
  have encoding := familyExpanded_exact_encoding defaultSearch (gates _ freshExpand) oldTiered freshTiered
  have sharing : result.result.sharing = oldResult.result.sharing := congrArg (·.1) encoding
  have roots : result.result.roots = oldResult.result.roots := congrArg (fun e => e.2.1) encoding
  rw [roots, oldWritten] at freshWritten
  cases Except.ok.inj freshWritten
  rw [freshOutput, oldOutput, sharing]

/-- Full serialized-constant equality follows by congruence of the actual
serializer. This compares complete bytes, not merely variable-length fields. -/
theorem normalizeFamily_exact_bytes {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input old fresh : Ixon.Constant} {result : TieredSharingResult}
    (defaultSearch : limits.uniformSubsetSearch = false) (gates : ExactInput cfg limits input)
    (oldRun : Exact.Reference.normalizeConstantSharingTiered layout input limits = .ok old)
    (freshRun : normalizeFamily cfg layout input limits = .ok (fresh, result)) :
    Ixon.serConstant fresh = Ixon.serConstant old :=
  congrArg Ixon.serConstant (normalizeFamily_exact_constant defaultSearch gates oldRun freshRun)

/-- The public K16 wrapper is the constant projection of the same family
pipeline, including all errors. The compiled twin is justified separately. -/
theorem normalizeConstantSharingTiered_eq_family (layout : ShareLayout) (input : Ixon.Constant)
    (limits : Limits) :
    normalizeConstantSharingTiered layout input limits =
      (normalizeFamily canonicalFamilyConfig layout input limits).map Prod.fst := by
  unfold normalizeConstantSharingTiered canonicalSharingTieredTable normalizeFamily
  rw [familyReferenceExpanded_eq_cached]
  cases expanded : expand limits input.sharing (constantInfoRoots input.info) true with
  | error error => rfl
  | ok ex =>
    dsimp only [bind, Except.bind]
    cases normalized : familyExpanded canonicalFamilyConfig layout limits ex with
    | error error => rfl
    | ok result =>
      dsimp only [bind, Except.bind]
      cases withRoots input.info result.result.roots <;> rfl

/-- Conditional compatibility of the actual public production and old
reference wrappers. Arbitrary same-budget old-success implies new-success
is false; both successful runs remain explicit. -/
theorem normalizeConstantSharingTiered_reference_eq {layout : ShareLayout} {limits : Limits}
    {input old fresh : Ixon.Constant}
    (defaultSearch : limits.uniformSubsetSearch = false) (gates : ExactInput canonicalFamilyConfig limits input)
    (oldRun : Exact.Reference.normalizeConstantSharingTiered layout input limits = .ok old)
    (freshRun : normalizeConstantSharingTiered layout input limits = .ok fresh) : fresh = old := by
  rw [normalizeConstantSharingTiered_eq_family] at freshRun
  cases actual : normalizeFamily canonicalFamilyConfig layout input limits with
  | error error => rw [actual] at freshRun; cases freshRun
  | ok pair =>
    obtain ⟨output, result⟩ := pair
    rw [actual] at freshRun
    have same : output = fresh := Except.ok.inj freshRun
    rw [← same]
    exact normalizeFamily_exact_constant defaultSearch gates oldRun actual

theorem normalizeConstantSharingTiered_reference_bytes {layout : ShareLayout} {limits : Limits}
    {input old fresh : Ixon.Constant}
    (defaultSearch : limits.uniformSubsetSearch = false) (gates : ExactInput canonicalFamilyConfig limits input)
    (oldRun : Exact.Reference.normalizeConstantSharingTiered layout input limits = .ok old)
    (freshRun : normalizeConstantSharingTiered layout input limits = .ok fresh) :
    Ixon.serConstant fresh = Ixon.serConstant old :=
  congrArg Ixon.serConstant (normalizeConstantSharingTiered_reference_eq defaultSearch gates oldRun freshRun)

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.exactInput_of_expand [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeConstantSharingTiered_parts [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_exact_constant [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_exact_bytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeConstantSharingTiered_eq_family [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeConstantSharingTiered_reference_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeConstantSharingTiered_reference_bytes [propext, Classical.choice, Quot.sound]
