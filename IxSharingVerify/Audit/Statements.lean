import IxC.Kernel.Audit.Axioms
import IxSharingVerify
import IxSharingVerify.Builder
import IxSharingVerify.ConstantNeverFails
import IxSharingVerify.FamilyCached
import IxSharingVerify.FamilyFast
import IxSharingVerify.FamilyNormalize
import IxSharingVerify.FamilyNormalizeSpec
import IxSharingVerify.FamilyWritingBound
import IxSharingVerify.UniformCappedSize
import Ix.LeanIngress.Expr
import Ix.Sharing.FamilyContext

/-!
# Trust manifest for the sharing proofs

These roots cover the TagN codec, the sharing construction (the exact core,
the uniform optimizer, the tiered phases, the output format, the production
rule, its totality and its output-size bound), the compiler's sharing builder,
and every `@[csimp]` theorem by which compiled code
runs a fast body in place of a sharing specification (`Audit.CompiledCode` fails the
build if one is missing). Each root's transitive axiom set must be exactly the
listed one (`Ix.Kernel.Audit.checkAxioms`, the certified kernel's exact
traversal of checked types and bodies), and only Lean's `propext`,
`Classical.choice` and `Quot.sound` may be listed, so a root that reaches
`sorryAx` or any other axiom fails this module.
-/

#guard_module_axioms Ix.Sharing.FamilyParallel
#guard_module_axioms Ix.Sharing.FamilyContext

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
  -- sharing-k16-greedy-v1: preserved exact references, proved compiled
  -- family twins, actual family leastness and compiler-facing contracts.
  { root := ``Ix.Sharing.Verify.CanonicalMeaning.Reference.canonicalSharingTiered_meaning, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.Reference.canonicalSharingTiered_format, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.Reference.canonicalSharingTieredTable_format, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.Reference.canonicalSharingTiered_serialized, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Tiered.Reference.canonicalSharingTieredTable_serialized, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.component_eq_fast, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.components_eq_cached, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyReferenceExpanded_eq_cached, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyAreaPhi_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyTraceArea_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyAreaEvaluation_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyStepArea_eq_reference, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyFoldArea_eq_reference, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyComponentsArea_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyUniformArea_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyAtWidthArea_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyExpanded_eq_area, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.normalizeFamily_eq_area, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.Parallel.exactTable_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.Parallel.tableWithDepth_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.Parallel.table_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.Parallel.table_eq_function, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.foldChoices_eq_fast, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Family.LightContext.trace_eq_parallel, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.LightContext.trace_walk_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.LightContext.step_eq_area, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.LightContext.expanded_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.LightContext.normalize_eq_area, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyExpandedArea_eq_lightContext, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.normalizeFamilyArea_eq_lightContext, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyReferenceExpanded_eq_lightContext, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyExpanded_eq_lightContext, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.normalizeFamily_eq_lightContext, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.exact_family_iff, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.exact_table_row_least, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.table_tie_coverage, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.initial_knapsack_least, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyUniform_selection, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.initial_minimum_cost, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyUniform_finished, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyUniform_model_minimum, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyExpanded_checked, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.normalizeFamily_meaning, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.normalizeFamily_wire, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CanonicalProduction.canonicalSharingTiered_parts, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CanonicalProduction.canonicalSharingTieredTable_parts, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CanonicalProduction.canonicalSharingTiered_family_least, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CanonicalProduction.canonicalSharingTiered_output, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.normalizeConstantSharingTiered_eq_family, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.normalizeConstantSharingTiered_reference_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.normalizeConstantSharingTiered_reference_bytes, standardAxioms := standard },
  -- The production rule never fails: under some budget every refusal is
  -- unreachable on its domain, larger budgets keep a successful run and its
  -- result, and the output expands again.
  { root := ``Ix.Sharing.Verify.Totality.canonicalSharingTiered_ok, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.canonicalSharingTieredTable_ok, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.normalizeConstantSharingTiered_ok, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.familyExpanded_ok, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.canonicalSharingTiered_output_expands, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.canonicalSharingTieredTable_output_expands,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Budget.canonicalSharingTiered_mono, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Budget.canonicalSharingTiered_budget_independent,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Budget.normalizeConstantSharingTiered_budget_independent,
    standardAxioms := standard },
  -- The first-tier search of the slot allocation visits at most `(m + 1)^9`
  -- states on a table of `m` entries.
  { root := ``Ix.Sharing.Verify.Tiered.allocate_within, standardAxioms := standard },
  -- The output is at most nine times the full endpoint's charge.
  { root := ``Ix.Sharing.Family.selected_ulen_le_modelBound, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyExpanded_output_le, standardAxioms := standard },
  -- A budget polynomial in the input size admits every Share-free input of
  -- the domain, and every larger budget returns the same output.
  { root := ``Ix.Sharing.Verify.Totality.familyCallTotal_le, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.familyWorkTotal_le, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.familyExpanded_within, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.canonicalSharingTiered_limitsFor, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.canonicalSharingTiered_above, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.canonicalSharingTieredTable_limitsFor, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.canonicalSharingTieredTable_above, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Totality.normalizeConstantSharingTiered_limitsFor,
    standardAxioms := standard },
  -- Re-checks of the compiled family twins beside their definitions in
  -- `Ix.Sharing` (`FamilyCached`, `FamilyFast`, `FamilyNormalize`, `FamilyNormalizeSpec`).
  { root := ``Ix.Sharing.Family.cachedStep_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.componentsCachedWith_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.localPhi_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.phiE_work, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.cachedComponent_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyStep_eq_reference, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyFold_eq_reference, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyComponents_eq_reference, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyUniform_eq_reference, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.familyAtWidth_eq_reference, standardAxioms := standard },
  -- Groundwork for an output-size bound (`FamilyFullWitness`, `FamilyResidual`,
  -- `FamilyLocalWriting`, `FamilyWritingBound`) and the arithmetic contract of
  -- Rust's capped classification cost (`UniformCappedSize`).
  { root := ``Ix.Sharing.Family.fullChoices_member, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.fullChoices_selected_mem, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Family.initial_full_member, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.initial_full_selected_mem, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.initial_full_merge, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.initial_full_stored, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.initial_full_stored_mem, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.occurrences_positive, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.degree_le_occurrences, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.excluded_size_lt_two, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.initial_omitted_repeated_excluded, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.initial_omitted_repeated_small, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.initial_omitted_cases, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.residualIncoming_eq, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.degree_eq_edges, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.residualExpansions_le_one, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.residualIncoming_le_degree, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.edgeAll_eq_child_count, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.edgeAll_sum, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.degree_sum, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.residualIncoming_sum_le, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.residualBoundaryUnit_le, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.residualCharge_le, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.tag4Size_le_nine, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Family.telescope_graft, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Family.telescope_one_node, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Family.telescope_child_costs, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Family.inline_local_writing, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.uInl_le_local, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.fullStored_nodup, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.mul_sum_map, standardAxioms := propextOnly },
  { root := ``Ix.Sharing.Family.child_cost_sum, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.residual_flow_cost, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.residual_semantic_row, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.fullStored_ulen_le_residual, standardAxioms := standard },
  { root := ``Ix.Sharing.Family.fullStored_encoding_bound, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CappedSize.excluded_div, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CappedSize.excluded_fast, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CappedSize.excluded_size_lt_two, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CappedSize.cap_size, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CappedSize.cap_occ, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CappedSize.classification_capped, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CappedSize.cap_add_u128_safe, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.CappedSize.cap_add, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.CappedSize.cap_fold, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.CappedSize.cap_empty_telescope, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.CappedSize.empty_no_cuts, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.CappedSize.empty_telescope_natural, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.CappedSize.certainExcludedTest_contract, standardAxioms := #[] },
  -- The meaning of the canonical construction: the pointer cache, ingestion
  -- of the table and the roots, and canonical numbering preserve what each
  -- input expression denotes.
  { root := ``Ix.Sharing.Verify.CanonicalMeaning.canonicalize_correct, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CanonicalMeaning.expand_correct, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CanonicalMeaning.expand_unshared, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CanonicalMeaning.expand_root_terms, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.CanonicalMeaning.canonicalSharingTiered_meaning, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Ingestion.ingestTable_run, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Ingestion.canonicalize_ingested, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Ingestion.ingestTable_correct, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Ingestion.ingestTable_initial, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Ingestion.ingestTable_unshared, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Ingestion.reexpand_correct, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Ingestion.termOf_retains, standardAxioms := noChoice },
  { root := ``Ix.Sharing.Verify.Ingestion.internNode_good, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Ingestion.ingestExpr_checked, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.Ingestion.ingestExpr_initial, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.ExprCache.sound_empty, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.ExprCache.sound_insert, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.ExprCache.lookup_entry, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.ExprCache.lookup_sound, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.ExprCache.lookup_insert, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.ExprCache.collision_miss, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.ExprCache.Sound.mono, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.ExprCache.ingestExpr_hit, standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.ExprCache.ingestExpr_hit_meaning, standardAxioms := standard },
  -- The compiler's sharing builder (`Ix.Sharing.Verify.Builder`) and the
  -- stored-byte wrapper `BlockResult.mk'`, which hashes the block with
  -- `Address.admissionHash` (pure BLAKE3 in the logic; no hash
  -- reaches a `native_decide` axiom). These assert no hash-injectivity or
  -- FFI-agreement law.
  { root := ``Ix.Sharing.Verify.BlockResult.mk'_codec_roundtrip,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.BlockResult.mk'_codecWF,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.BlockResult.constantInfo_codec_roundtrip,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.finishConstantInfoWithSharing_run_codecWF,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.buildConstantWithSharing_wireWF,
    standardAxioms := standard },
  -- The same endpoint from the payload's header fields alone: the roots that
  -- sharing rewrites need no wire-validity premise.
  { root := ``Ix.Sharing.Verify.buildConstantWithSharing_wireWF_headers,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Verify.constantInfoRootExprs_toList,
    standardAxioms := #[``propext] },
  { root := ``Ixon.Verify.TagN.runGetExact_getTagN_eq,
    standardAxioms := standard },
  { root := ``Ixon.Verify.TagN.putTagN_inj,
    standardAxioms := noChoice },
  -- Compiled host code (`Ix.Ixon` and its importers) writes TagN integers
  -- with the inlined copy `putTagNI` (`@[csimp]`, by `rfl`).
  { root := ``Ixon.putTagN_eq_I,
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
  -- The compiled tiered copies (`*_eq_C` below) run that loop as
  -- `searchComponentsArea`, the search on each component's area with the
  -- truncated evaluation, equal to `searchComponentsWith` on a stage's tables.
  { root := ``Ix.Sharing.Exact.AreaProof.searchComponentsArea_eq,
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
  { root := ``Ix.Sharing.Verify.Tiered.Reference.canonicalSharingTieredTable_idem,
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
  -- The compiler's preseed table walks (`Ix.CompileM.TableWorklist`):
  -- compiled code runs the total worklists, proved equal to the structural
  -- walks (`@[csimp]`), in place of the former `implemented_by` code.
  { root := ``Ix.CompileM.collectExprTables_eq_worklist,
    standardAxioms := standard },
  { root := ``Ix.CompileM.preseedExprTables_eq_worklist,
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
    standardAxioms := noChoice },
  -- The compiler's exact cache keys (`Ix.Compile.ExactKey`): compiled
  -- code compares expressions, levels and names pointer-first with a memo,
  -- proved equal to `decide (a = b)` over the raw terms (`@[csimp]`).
  { root := ``Ix.Compile.ExactKey.exprEq_eq_impl,
    standardAxioms := standard },
  { root := ``Ix.Compile.ExactKey.levelEq_eq_impl,
    standardAxioms := standard },
  { root := ``Ix.Compile.ExactKey.nameEq_eq_impl,
    standardAxioms := noChoice },
  -- The Source ingress's term conversion (`Ix.LeanIngress.Expr`), which the
  -- compile drivers now run through their Source service (AuxGen M1):
  -- compiled code runs the shared-memo conversion, proved equal to the
  -- structural one (`@[csimp]`).
  { root := ``Ix.LeanIngress.ingressExprs_eq_shared,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.areaFold_eq_direct,
    standardAxioms := noChoice },
  { root := ``Ix.Sharing.Exact.memberFlags_eq_direct,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.phiA_eq_direct,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.placeBucket_eq_fast,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.reboundA_eq_direct,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.revisibleA_eq_direct,
    standardAxioms := standard },
  { root := ``Ix.Sharing.Exact.TBase.ofPrep_eq_direct,
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
