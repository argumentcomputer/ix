import Ix.Kernel.Audit.Axioms
import Ix.Sharing.Verify
import Ix.Sharing.Verify.Builder

/-!
# Trust manifest for the sharing proofs

These roots cover the TagN codec, the sharing construction (the exact core,
the uniform optimizer, the tiered phases, the output format), the compiler's
sharing builder, and every `@[csimp]` theorem by which compiled code runs a
fast body in place of a sharing specification (`Audit.CompiledCode` fails the
build if one is missing). Each root's transitive axiom set must be exactly the
listed one (`Ix.Kernel.Audit.checkAxioms`, the certified kernel's exact
traversal of checked types and bodies), and only Lean's `propext`,
`Classical.choice` and `Quot.sound` may be listed, so a root that reaches
`sorryAx` or any other axiom fails this module.
-/

namespace Ix.Sharing.Verify.Audit.Statements

open Lean Elab Command

/-- One audited theorem root and its exact axiom set. -/
structure RootAllowance where
  root : Lean.Name
  standardAxioms : Array Lean.Name := #[]

private def permittedStandardAxioms : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def standard : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def noChoice : Array Lean.Name := #[``propext, ``Quot.sound]

private def propextOnly : Array Lean.Name := #[``propext]

private def quotOnly : Array Lean.Name := #[``Quot.sound]

/-- The theorem roots and their exact axiom sets. `Audit.CompiledCode` also
requires every `@[csimp]` theorem on the compiler's import path to be one of
them. -/
def roots : Array RootAllowance := #[
  -- The compiler's sharing builder (`Ix.Sharing.Verify.Builder`). The
  -- theorems about `BlockResult.mk'` (`BlockResult.mk'_codec_roundtrip`,
  -- `BlockResult.constantInfo_codec_roundtrip`,
  -- `finishConstantInfoWithSharing_run_codecWF`) are not roots: `mk'` hashes
  -- the block, and the Blake3 package's `HasherOps.hash` carries a
  -- `native_decide` axiom, which this manifest does not admit.
  { root := ``Ix.Sharing.Verify.buildConstantWithSharing_wireWF,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.constantInfoRootExprs_toList,
    standardAxioms := #[``propext] },
  { root := ``Ixon.Verify.TagN.runGetExact_getTagN_eq,
    standardAxioms := standard },
  { root := ``Ixon.Verify.TagN.putTagN_inj,
    standardAxioms := noChoice },
  { root := ``Ixon.Verify.TagN.getTagN_rejects_code,
    standardAxioms := standard },
  { root := ``Ixon.Verify.TagN.getTagN_rejects_overflow,
    standardAxioms := noChoice },
  -- The TagN bijection (a read succeeds exactly on the written bytes) and the
  -- length decomposition of a serialized Constant that the docs cite.
  { root := ``Ixon.Verify.TagN.runGetExact_getTagN_iff,
    standardAxioms := standard },
  { root := ``Ixon.Verify.TagN.runGetExact_getTagN_inj,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.SharingExact.serConstant_size_decomposition,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.SharingExact.materializeWith_correct,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.SharingExact.materializeTable_correct,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.SharingExact.materializeDependent_correct,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.SharingExact.canonicalize_det,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.optimizeUniform_modelBytes,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.optimizeUniform_variableBytes,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.PrepWF.uniformCost_le,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.UniformModel.PrepWF.uniformCost_attained,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.uniformCost_insert_le,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.uniformCost_insert_le_counts,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.stored_in_minimum,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.excluded_of_minimum,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.classify_sound,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.threshold_one_sound,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.tag0Size_succ_le,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.UniformModel.tag4Size_add_le,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.UniformModel.tag4Size_not_subadditive_at_end,
    standardAxioms := #[] },
  { root := ``Ix.Sharing.Verify.UniformModel.PrepWF.uCost_local,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.PrepWF.uCost_modular,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.uniformCost_modular,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.components_modular,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.certainStored_opaque,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.lower_bound_sound,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.componentsChecked_spec,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.optimizeUniform_reach,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.reachLabelsOn_allows,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.mem_upClosure,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.sepCheck_spec,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.evalFold_rows,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.UniformModel.entry_inl,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.phiE_spec,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.optimizeUniform_minimum,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.uniformChoose_model_le,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.Env.search_spec,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.Env.component_table,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.uniformKnapsack_le,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.compEnv_wf,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.ulen_compParts,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.group_rep,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.group_modular,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.forced_mem,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.revisible_le,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.ulen_split_component,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.minimum_exists,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.optimizeUniform_least,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.uniformChoose_tie,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.uniformKnapsack_tie,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.knapFold_tie,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.conv_tie,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.lexLt_iff,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.UniformModel.precL_union,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.UniformModel.bestSetOf_spec,
    standardAxioms := standard },
  -- Compiled component search (`@[csimp]`): the loop of `searchComponents`
  -- runs the area- and closure-local search.
  -- `standard` since Lean 4.34.0 (was `noChoice`): `searchComponentRef`
  -- inserts into a `Std.HashMap`, whose `emptyWithCapacity` proof reaches
  -- `Classical.choice` through `Nat.isPowerOfTwo_nextPowerOfTwo`.
  { root := ``Ix.Sharing.Exact.searchComponents_eq_via,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.searchComponentsWith_eq_fast,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.canonicalTieredCore_select,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.tieredAtWidth_parts,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.tierClosures_spec,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.tierDfs_spec,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.firstTier_spec,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.allocate_spec,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.tierWeights_spec,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.tierDeps_spec,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.PrepWF.gValid_cost,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.UniformModel.PrepWF.gExists_opt,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.PrepWF.gBuild_size,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.gCost_local,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.UniformModel.evalUp_ok,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.Tiered.materializeTable_spec,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.materializeTable_min,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.rematerialize_spec,
    standardAxioms := standard },
  -- Phase-3 compiled-code replacements (`@[csimp]`): compiled code runs the
  -- right-hand side wherever the specification on the left is called.
  { root := ``Ix.Sharing.Exact.materializeTable_eq_fast,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.build_eq_fast,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Exact.inlineCost_eq_fast,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Exact.reexpand_eq_fast,
    standardAxioms := standard },
  -- For the wire layout the length the tiered construction reports is the
  -- serialized length of its output.
  { root := ``Ix.Sharing.Verify.Tiered.canonicalSharingTiered_serialized,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.canonicalSharingTieredTable_serialized,
    standardAxioms := standard },
  -- Phase 3 materializes the table from one evaluation of the whole
  -- dictionary when the order allows it (`rematerialize` changed; equal to
  -- `materializeTable` on every input, errors and limits included).
  { root := ``Ix.Sharing.Verify.Tiered.materializeTableOnePass_eq,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.canonicalTiered_core,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.canonicalTiered_det,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.canonicalTiered_reexpand,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.canonicalSharingTieredTable_idem,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.wireCounts_spec,
    standardAxioms := propextOnly },
  { root := ``Ix.Sharing.Verify.Tiered.canonicalTiered_format,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.canonicalSharingTiered_format,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.canonicalSharingTieredTable_format,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.PrepWF.gBuild_tree,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.UniformModel.WTree.gcost_eq,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.Tiered.phase3_le_phase1,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.allocate_optimal,
    standardAxioms := standard },
  -- Compiled tiered construction (`@[csimp]`, `Ix.Sharing.Exact.TierFast`,
  -- `Ix.Sharing.Exact.PinnedDeps`, `Ix.Sharing.Exact.PinnedFast`,
  -- `Ix.Sharing.Exact.KnapsackFast` and
  -- `Ix.Sharing.Exact.TieredFast`).
  { root := ``Ix.Sharing.Exact.firstTier_eq_fast,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.pinnedDeps_eq_fast,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.pinnedOrder_eq_fast,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.uniformKnapsack_eq_fast,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.allocate_eq_C,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.tieredAtWidth_eq_C,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.canonicalTieredCore_eq_C,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.optimizeUniformExpanded_eq_C,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.canonicalTieredExpanded_eq_C,
    standardAxioms := standard },
  -- Compiled-code replacements (`@[csimp]`): compiled code runs the
  -- right-hand side wherever the specification on the left is called.
  { root := ``Ix.Sharing.Exact.tagNByteWidth_eq_fast,
    standardAxioms := quotOnly },
  { root := ``Ix.Sharing.Exact.propagateCounts_eq_fast,
    standardAxioms := noChoice },
  -- `standard` since Lean 4.34.0 (was `noChoice`): `SCtx` holds a
  -- `Std.HashMap`, whose well-formedness proof reaches `Classical.choice`
  -- through `Nat.isPowerOfTwo_nextPowerOfTwo`.
  { root := ``Ix.Sharing.Exact.SCtx.phiE_eq_fast,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.csBase_eq_fast,
    standardAxioms := noChoice }
]

/-- Check every root: no duplicates, only Lean's standard axioms listed, and
the root's transitive axiom set exactly the listed one. Every root is checked
and every mismatch reported. -/
def check (allowances : Array RootAllowance) : CommandElabM Unit := do
  let mut seen : Lean.NameSet := {}
  let mut failures : Array MessageData := #[]
  for allowance in allowances do
    if seen.contains allowance.root then
      throwError m!"duplicate axiom-audit root: {allowance.root}"
    seen := seen.insert allowance.root
    for axiomName in allowance.standardAxioms do
      unless permittedStandardAxioms.contains axiomName do
        throwError m!"{allowance.root}: {axiomName} is not a permitted standard Lean axiom"
    try Ix.Kernel.Audit.checkAxioms allowance.root allowance.standardAxioms
    catch ex => failures := failures.push ex.toMessageData
  unless failures.isEmpty do
    throwError m!"sharing proof trust audit: {failures.size} of {allowances.size} roots \
      failed\n{MessageData.joinSep failures.toList "\n"}"
  logInfo m!"sharing proof trust audit passed for {allowances.size} theorem roots"

run_cmd check roots

end Ix.Sharing.Verify.Audit.Statements
