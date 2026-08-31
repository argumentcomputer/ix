import Ix.Tc.Verify.Audit.Basic
import Ix.Compile.Verify.Statements

/-!
# Trust manifest for the compiler statement frontier

These roots cover the first expression-level square, concrete catalog
integrity, and the production compiler's finite-table transitions.  The
explicit `KernelSourceWitness` assumption is data supplied to later theorems,
not a global axiom, and no compiler theorem may inherit checker acceptance as
a premise.
-/

namespace Ix.Compile.Verify.Audit.Statements

open Ix.Tc.Verify.Audit

private def standard : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def noChoice : Array Lean.Name := #[``propext, ``Quot.sound]

private def blake3Native : Array Lean.Name := #[
  nativeAxiom `Blake3
    `Blake3.HasherOps.hash._native.native_decide.ax_1
]

private def nameNative : Array Lean.Name := #[
  nativeAxiom `Ix.Environment
    `Ix.Name.mkStr._native.native_decide.ax_1
]

private def singletonDriverNative : Array Lean.Name :=
  blake3Native ++ nameNative

private def roots : Array RootAllowance := #[
  { root := ``Ix.Compile.Verify.IxonExprRel.eraseModes_iff,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.compileUnivRef_value,
    standardAxioms := noChoice },
  { root := ``Ix.Compile.Verify.compileExprRef_leanFragment,
    standardAxioms := noChoice },
  { root := ``Ix.Compile.Verify.compileExprRef_wireWF,
    standardAxioms := noChoice },
  { root := ``Ix.Compile.Verify.compileExprRef_eraseModes,
    standardAxioms := noChoice },
  { root := ``Ix.Compile.Verify.compileExprRef_value,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.Catalog.factorization },
  { root := ``Ix.Compile.Verify.deUniv_serUniv,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.deUniv_serUniv_small,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.deUniv_serUniv_sortOne,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.deExpr_serExpr_single,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.deExpr_serExpr,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.deConstant_serConstant_core_empty,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.deConstant_serConstant_core,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.deConstant_serConstant_nonrecursive,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.deConstant_serConstant_standalone,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.constantWireWF_iff_codec,
    standardAxioms := #[``propext] },
  { root := ``Ix.Compile.Verify.deConstant_serConstant,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.ExprTableWF.mono },
  { root := ``Ix.Compile.Verify.Catalog.empty_wf,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.Catalog.ofEnv_finite,
    standardAxioms := noChoice },
  { root := ``Ix.Compile.Verify.BlockState.internRef_wf,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.BlockState.internUniv_wf,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.internRef_run_wf,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.internUniv_run_wf,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.UnivCacheWF.insert,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.compileUniv_run_cached,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.compileUniv_run_refines,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.compileAndInternUnivCanon_run_refines,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.compileAndInternUnivCanon_array_refines,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileUniv_run_value,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.canonPreseedUnivs_run_refines,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.collectExprTablesStructural_run_ready,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.collectExprTablesStructural_run_ready_covers,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.collectPreseedExprs_singleton_run_ready_covers,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.collectPreseedExprs_pair_run_ready_covers,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.singletonPreseedCovers_of_ready,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.singletonPreseedCapacity_of_ready,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.internPreseedRefs_run_wf,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.internPreseedRefs_run_total,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.internPreseedRefs_run_indexed,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.internPreseedRefs_run_resolutionFrame,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.internPreseedUnivs_run_wf,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.internPreseedUnivs_run_total,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.internPreseedUnivs_run_indexed,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.internPreseedUnivs_run_resolutionFrame,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.univSortKey_injective_wire,
    standardAxioms := standard },
  { root :=
      ``Ix.Compile.Verify.PreseedCollectionCovers.compileExprRef_of_indexed,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.BlockWireTablesWF.of_preseed,
    standardAxioms := noChoice },
  { root := ``Ix.Compile.Verify.preseedExprTables_singleton_run_ready,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.preseedExprTables_singleton_run_ready_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.preseedExprTables_singleton_run_ready_frozenRef,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.preseedExprTables_of_collect_run_ready_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.preseedExprTables_pair_run_ready_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.preseedExprTables_pair_run_ready_frozenRefs,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.preseedExprTables_roots_run_ready_frozenRefs,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.collectPreseedExprs_inputs_run_ready_covers,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.preseedExprTables_inputs_run_ready_frozenRefs,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.heterogeneousPreseedSeenSafe_of_uniform,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.preseedExprTables_inputs_run_uniform_ready_frozenRefs,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.preseedExprTables_run_univsFinal,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.serializeIxSyntax_run_refines,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.KVMapSupported.all,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileKVMap_run_refines,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.metaCompileSupport_finite,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.BlockState_compileName_strict,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.serializeIxSyntax_run_strictStores,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileDataValue_run_strictStores,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileKVMap_run_strictStores,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.StructuralExprCacheWF.insert,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.OrdinaryExprCacheWF.insert,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.compileExpr_run_surgeryFree,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExprNoSurgeryFuel_structural_refines,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_structural_refines,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_structural_value,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_sort_value,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_constEmpty_recur_value,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_constEmpty_ref_value,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_lit_value,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExprNoSurgeryFuel_ordinary_refines,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_ordinary_refines,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_ordinary_codec_roundtrip,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.deConstant_serUnsharedAxiomConstant,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.deConstant_serUnsharedDefinitionConstant,
    standardAxioms := standard },
  { root :=
      ``Ix.Compile.Verify.compileExpr_run_ordinary_axiomConstant_roundtrip,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.compileExpr_run_ordinary_definitionConstant_roundtrip,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.BlockResult.mk'_codec_roundtrip,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.buildConstantWithSharing_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.BlockResult.constantInfo_codec_roundtrip,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.constantInfoRootExprs_toList,
    standardAxioms := #[``propext] },
  { root :=
      ``Ix.Compile.Verify.finishConstantInfoWithSharing_run_codecWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileAxiom_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.finishQuotientCompilation_run,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileQuotient_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileRecursorRules_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.finishRecursorCompilation_run,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileRecursor_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileConstructor_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.compileInductiveConstructors_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.finishInductiveCompilation_run,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileInductive_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileInductiveData_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileMutConsts_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.buildCompiledMutualBlock_codecWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.compileMutualBlock_run_of_preseed_ordinary_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root := ``Ix.Compile.Verify.compileMutualBlock_run_ready_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root :=
      ``Ix.Compile.Verify.compileMutualBlock_run_member_uniform_ready_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root := ``Ix.Compile.Verify.collectMutConsts_run_of_lookups,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.compareLevelReady_of_ref,
    standardAxioms := noChoice },
  { root := ``Ix.Compile.Verify.PreseedReady.compareReady,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.compareExpr_run_ready,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.compareConst_run_ready,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.sortConsts_run_classesWF,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.sortConsts_run_ready,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.sortConstsIsolated_run_of_sort,
    standardAxioms := standard },
  { root :=
      ``Ix.Compile.Verify.compileConstant_run_mutual_of_lookup_sorted_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root := ``Ix.Compile.Verify.finishInductiveFamilyBlock_run_codecWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.lookupInductiveConstructors_run_of_lookup,
    standardAxioms := standard, nativeAxioms := nameNative },
  { root := ``Ix.Compile.Verify.compileDefinition_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.finishDefinitionDataCompilation_run,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileDefinitionData_run_ordinary_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.compileDefinitionDataInfo_run_ready_codecWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.axiomCompileStartState_frozen,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.compileConstantInfo_axiom_run_ordinary_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root :=
      ``Ix.Compile.Verify.compileConstantInfo_axiom_default_run_ready_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root :=
      ``Ix.Compile.Verify.compileConstantInfo_definition_default_run_ready_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root :=
      ``Ix.Compile.Verify.compileConstantInfo_theorem_default_run_ready_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root :=
      ``Ix.Compile.Verify.compileConstantInfo_opaque_default_run_ready_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root :=
      ``Ix.Compile.Verify.compileConstantInfo_quotient_default_run_ready_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root :=
      ``Ix.Compile.Verify.compileConstantInfo_recursor_default_run_ready_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root :=
      ``Ix.Compile.Verify.compileConstantInfo_inductive_default_run_ready_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root :=
      ``Ix.Compile.Verify.compileConstantInfo_constructor_default_run_ready_codecWF,
    standardAxioms := standard, nativeAxioms := singletonDriverNative },
  { root := ``Ix.Compile.Verify.rewriteWithSharing_wireWF,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.applySharing_wireWF,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.compileExpr_run_ordinary_axiomBlock_noSharing_roundtrip,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.compileExpr_run_ordinary_definitionBlock_noSharing_roundtrip,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.compileExpr_run_ordinary_axiomBlock_roundtrip,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.compileExpr_run_ordinary_definitionBlock_roundtrip,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_ordinary_value,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root :=
      ``Ix.Compile.Verify.compileExprNoSurgeryFuel_ordinary_arena_refines,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_ordinary_arena_refines,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Compile.Verify.compileExpr_run_ordinary_arena_value,
    standardAxioms := standard, nativeAxioms := blake3Native }
]

run_cmd Ix.Tc.Verify.Audit.check roots

end Ix.Compile.Verify.Audit.Statements
