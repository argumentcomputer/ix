/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Infer
import Ix.Kernel.Verify.Consistency.Constant
import Ix.Kernel.Verify.Consistency.Environment
import Ix.Kernel.Verify.Consistency.RecursiveCache
import Ix.Kernel.Verify.Consistency.RecursiveState
import Ix.Kernel.Verify.Consistency.SourceAgreement
import Ix.Kernel.Verify.Consistency.SourceCache
import Ix.Kernel.Verify.Consistency.Dependencies
import Ix.Kernel.Verify.Consistency.CheapBeta
import Ix.Kernel.Verify.Consistency.SynthesisCache
import Ix.Kernel.Verify.Consistency.SynthesisCacheExecution
import Ix.Kernel.Verify.Consistency.LetCache
import Ix.Kernel.Verify.Consistency.BetaSourceInference
import Ix.Kernel.Verify.Consistency.BetaExposureConstruction
import Ix.Kernel.Verify.Consistency.BetaHistoryInference
import Ix.Kernel.Verify.Audit.Basic

/-! Exact full-dependency boundaries for the direct model-refinement roots.
No root permits proof holes, implementation bridge axioms, or pending
metatheory axioms. Native assumptions are enumerated only where a production
smart constructor or dispatcher still contains a generated native proof. -/

namespace Ix.Kernel.Consistency.Audit

open Kernel.Verify.Audit

private def standard : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
private def levelNative : Lean.Name :=
  nativeAxiom `Ix.Kernel.Level `Ix.Kernel.KUniv.mkSucc._native.native_decide.ax_1
private def expressionNative : Lean.Name :=
  nativeAxiom `Ix.Kernel.Expr `Ix.Kernel.KExpr.mkVar._native.native_decide.ax_1
private def nameNative : Lean.Name :=
  nativeAxiom `Ix.Environment `Ix.Name.mkStr._native.native_decide.ax_1

/-- The public driver reaches these additional generated output-length
proofs through the full production method table, including inactive branches.
No new native proof is introduced by the fragment verification. -/
private def productionNative : Array Lean.Name := #[
  expressionNative, levelNative,
  nameNative,
  nativeAxiom `Ix.Kernel.Inductive `Ix.Kernel.RecM.canonicalAuxOrder._native.native_decide.ax_9
]

private def atomicRoots : Array Lean.Name := #[
  ``infer_uncached_success_state, ``infer_uncached_success, ``AtomicInferenceSupport.typing,
  ``AtomicInferenceSupport.reads, ``AtomicInferenceSupport.output,
  ``AtomicInferenceSupport.scopeAndReferences, ``AtomicInference.sound,
  ``inferUncached_fvar_sound, ``infer_fvar_sound,
  ``FVarInferenceSupport.output, ``FVarInferenceSupport.sound,
  ``InferenceCacheHit.run, ``infer_sort_cached_sound,
  ``infer_sort_cache_agreement, ``infer_sort_cache_frame, ``BinderInference.sortOfAgreement,
  ``ForallInferenceTrace.output, ``LambdaInferenceTrace.output, ``BinderInference.sound,
  ``inferUncached_monomorphic_const_scoped, ``ApplicationInferenceTrace.output,
  ``BinderInference.soundWithSynthesis, ``BinderInference.synthesis,
  ``BinderInference.hereditary, ``SynthesisInference.soundWithHereditary,
  ``CheckedType.sound, ``TypeFormation.sound,
  ``SynthesisInference.sound, ``SynthesisInference.closed_sound, ``SynthesisInference.ofSort,
  ``SynthesisTypeCheck.sound, ``SynthesisInference.ofTypeCheck,
  ``BinderInference.lambda_type, ``SynthesisInference.lambda_type,
  ``SynthesisInference.beta_sound, ``SynthesisInference.beta_step,
  ``RecM.whnfCoreWithFlagsStep_betaOne,
  ``DefinitionBodySupport.sound, ``DefinitionBodyTrace.scopes, ``DefinitionBodyTrace.binderSupport,
  ``DefinitionBodyTrace.checkedType, ``DefinitionBodyTrace.synthesisTypeCheck,
  ``DefinitionBodyTrace.synthesisSupport, ``AxiomTypeTrace.synthesisTypeCheck,
  ``DefinitionCheckSupport.sound, ``DefinitionBodyTrace.betaDeclaredSupport,
  ``AtomicDefinitionRun.ofHash, ``SynthesisSortCheck.soundWithHereditary, ``SynthesisSortCheck.sound
]

private def formationRoots : Array Lean.Name := #[
  ``Theory.Model.piSet_fibre_subset, ``Theory.Model.IsTGUniverse.piSet_fibre_mem,
  ``Theory.Model.zeroCondition_conditionLevel, ``Theory.Model.zeroCondition_applicationLevel,
  ``Theory.Model.applicationLevel_zero, ``Theory.Model.applicationLevel_ge,
  ``Theory.Model.TypingClaim.applicationType, ``Theory.Model.AExpr.LevelEquivalent.termTyping,
  ``InterfaceExtends.realizes, ``InterfaceExtends.typing,
  ``context_valid_tail, ``typing_weaken, ``typing_instL_closed,
  ``ContextFormation.empty, ``ContextFormation.push,
  ``Theory.Model.wellDenoted_of_inst, ``Theory.Model.wellDenoted_inst_iff,
  ``Theory.Model.TypingClaim.inst, ``Theory.Model.CheckingClaim.inst,
  ``Theory.Model.ConversionClaim.inst,
  ``HereditaryTyping, ``HereditaryTyping.typing, ``HereditaryTyping.lambdaType,
  ``HereditaryTyping.lambdaPrefix, ``HereditaryTyping.lambdaSpine,
  ``HereditaryTyping.weakenAt, ``HereditaryTyping.extend, ``HereditaryTyping.liftValue,
  ``HereditaryTyping.substituteAt
]

private def letRoots : Array Lean.Name := #[
  ``LetInferenceTrace.abstracted, ``LetInferenceTrace.substituted, ``LetInferenceTrace.reduced,
  ``LetInferenceTrace.after, ``LetInferenceTrace.output_state, ``LetInferenceTrace.SubstitutionSupport,
  ``LetInferenceTrace.substituted_reading, ``LetTypeReduction.reading, ``LetTypeReduction.trace,
  ``LetInferenceCheck.source_reading, ``LetInferenceCheck.substituted_type_origin,
  ``LetInferenceCheck.betaTyping, ``LetInferenceCheck.sound, ``LetInferenceCheck.closed_sound,
  ``LetInferenceCheck.beta_steps_sound, ``DefinitionBodyTrace.letSupport,
  ``InferenceCacheHistory.openLet, ``LetInferenceCheck.CacheData, ``LetInferenceCheck.cacheTrace,
  ``LetInferenceCheck.cache_maps, ``LetInferenceCheck.cacheHistory,
  ``LetTypeReduction.rigid, ``LetTypeReduction.sound, ``LetInferenceTrace.opened_reading,
  ``LetInferenceCheck.asSynthesis, ``LetInferenceCheck.CacheData.asSynthesis,
  ``LetInferenceCheck.cacheExecution, ``LetInferenceCheck.synthesisCacheHistory
]

/-- Structural source reconstruction precedes the semantic induction.
Its support and reader cannot assume the resulting hereditary invariant. -/
private def recursiveLetShapeRoots : Array Lean.Name := #[
  ``SynthesisInference.letE, ``SynthesisCheckedOrigin.binderType,
  ``SynthesisInference.outputReading, ``SynthesisBetaTyping.forallE
]

/-- Executed sort exposure, its recursive source resources, and its cache
history must be constructed before the semantic hereditary invariant. -/
private def sortExposureRoots : Array Lean.Name := #[
  ``BetaSortExposure.run, ``BetaSortExposure.coherent, ``BetaSortExposure.context,
  ``BetaSortExposure.betaTrace, ``BetaSortExposure.checkedTrace, ``BetaSortExposure.inference_frame,
  ``BetaSortExposure.policy, ``BetaSortExposure.inference_maps, ``SortInferenceTrace.direct,
  ``SortInferenceTrace.success, ``SortInferenceTrace.inferenceFrame, ``SortInferenceTrace.frame,
  ``SortInferenceTrace.exposure_state, ``SortInferenceTrace.exposure_frame, ``SortInferenceTrace.exposure_policy,
  ``SortInferenceTrace.exposure_maps, ``ForallSortInferenceTrace.domainFrame, ``ForallSortInferenceTrace.opened_reading,
  ``ForallSortInferenceTrace.success, ``ForallSortInferenceTrace.ofSuccess, ``ForallSortInferenceTrace.ofInference,
  ``ForallSortInferenceTrace.output_state, ``LambdaSortInferenceTrace.domainFrame, ``LambdaSortInferenceTrace.opened_reading,
  ``LambdaSortInferenceTrace.success, ``LambdaSortInferenceTrace.ofSuccess, ``LambdaSortInferenceTrace.ofInference,
  ``LambdaSortInferenceTrace.output_state, ``LetSortInferenceTrace.domainFrame, ``LetSortInferenceTrace.valueFrame,
  ``LetSortInferenceTrace.openingFrame, ``LetSortInferenceTrace.domainContext, ``LetSortInferenceTrace.openingContext,
  ``LetSortInferenceTrace.opened_reading, ``LetSortInferenceTrace.restores, ``LetSortInferenceTrace.success,
  ``LetSortInferenceTrace.ofSuccess, ``LetSortInferenceTrace.ofInference, ``LetSortInferenceTrace.output_state,
  ``LetSortInferenceTrace.substituted_reading, ``SynthesisInference.forallSort, ``SynthesisInference.lamSort,
  ``SynthesisInference.letSort, ``SynthesisContext.pushSort, ``SynthesisSortCheck.checked,
  ``SynthesisSortCheck.direct, ``SynthesisSortCheck.ofRetainedType, ``SynthesisSortCheck.betaTyping,
  ``SynthesisSortCheck.CacheData, ``SynthesisSortCheck.cacheExecution, ``InferenceCacheTrace.forallSort,
  ``InferenceCacheTrace.lamSort, ``InferenceCacheTrace.letSort
]

private def instantiationRoots : Array Lean.Name := #[
  ``instUnivSpec_readExpr?, ``instUnivSpec_readExpr?_withScope,
  ``instantiateUnivParams_readExpr?, ``instantiateUnivParams_readAnnotated,
  ``instantiateUnivParams_readAnnotated_scoped,
  ``instUnivSpec_scoped_eq, ``instantiateUnivParamsSpec_scoped_eq,
  ``instantiateUnivParams_scoped_eq, ``instantiateUnivParams_readScopedAnnotated,
  ``instantiateUnivParamsSpec_readScopedAnnotated,
  ``inferUncached_const_refinement, ``infer_const_refinement,
  ``inferUncached_const_sound, ``infer_const_sound,
  ``inferUncached_const_instantiation, ``ScopedConstantInferenceSupport.closed,
  ``inferUncached_const_scoped_refinement, ``inferUncached_const_scoped_sound,
  ``inferUncached_const_predicted_type, ``infer_const_scoped_annotated,
  ``infer_const_cache_write, ``CachedConstantInferenceSupport.refinement,
  ``CachedConstantInferenceSupport.sound,
  ``instantiateUnivParams_cache_frame, ``infer_const_cache_frame,
  ``infer_const_cache_agreement, ``CachedConstantInferenceSupport.transport,
  ``CachedConstantInferenceSupport.openBinder, ``CachedConstantInferenceSupport.sound_after_frame
]

private def cacheFrameRoots : Array Lean.Name := #[
  ``InferenceCacheFrame.of_eq, ``InferenceCacheFrame.refl, ``InferenceCacheFrame.trans,
  ``InferenceCacheAgreement.frame,
  ``cacheInferResult_eq, ``PreservesInferenceCache.pure, ``PreservesInferenceCache.bind,
  ``PreservesInferenceCache.runIntern, ``InferenceCacheFrame.localContext,
  ``InferenceCacheAgreement.policy, ``withInferOnly_eq,
  ``PreservesInferenceCache.withInferOnly, ``getConst_loaded,
  ``IngressCacheExtension.refl, ``IngressCacheExtension.intern, ``IngressCacheExtension.trans,
  ``EntriesCompatible.ofFresh, ``EntriesCompatible.ofLookups,
  ``insertMutsEntriesState_intern,
  ``ingress_runIntern_cache, ``LazyLookupFrame.refl, ``LazyLookupFrame.cache, ``LazyLookupFrame.policy
]

private def cacheMapRoots : Array Lean.Name := #[
  ``InferenceCacheAgreement.write, ``PreservesInferenceCache.write_other,
  ``InferenceCacheAgreement.clearReductionCaches,
  ``IngressCacheExtension.insert, ``insertStandaloneEntries_singleton,
  ``insertMutsEntriesState_cache, ``guardReserved_state, ``insertMutsEntries_cache
]

private def cacheKeyRoots : Array Lean.Name := #[
  ``inferKey_closed, ``inferKey_policy, ``inferKey_environment, ``inferKey_address,
  ``InferenceCacheHit.key_closed, ``observeInferenceCache,
  ``InferenceCacheAgreement.selected, ``InferenceCacheHit.transport,
  ``PreservesInferenceCache.inferKey, ``PreservesInferenceCache.openBinder,
  ``withLctxScope_eq, ``PreservesInferenceCache.withLctxScope
]

private def recursiveCacheRoots : Array Lean.Name := #[
  ``ApplicationInferenceTrace.output_state, ``ForallInferenceTrace.output_state,
  ``LambdaInferenceTrace.output_state, ``isDefEq_hash_state, ``isDefEq_hash_frame,
  ``InferenceCacheTrace.writes, ``InferenceCacheTrace.sortOfKey,
  ``InferenceCacheTrace.fvarOfKey, ``InferenceCacheTrace.constOfKey, ``InferenceCacheTrace.lazyConstOfKey,
  ``InferenceCacheTrace.frame, ``InferenceCacheTrace.agreement,
  ``infer_lazyConst_cache_frame, ``CachedConstantInferenceSupport.afterLazyInference,
  ``InferenceCacheTrace.verifiedConstOfKey,
  ``infer_verifiedConst_cache_frame, ``CachedConstantInferenceSupport.afterVerifiedInference,
  ``InferenceCacheTrace.coherentConstOfKey, ``infer_verifiedConst_coherent,
  ``infer_coherentConst_cache_frame, ``CachedConstantInferenceSupport.afterCoherentInference,
  ``InferenceCacheHit.afterInference, ``CachedConstantInferenceSupport.afterInference,
  ``CachedConstantInferenceSupport.sound_after_inference, ``BinderInference.sortAfterInference
]

private def synthesisCacheRoots : Array Lean.Name := #[
  ``infer_full_success_cache, ``InferenceCacheHit.fromFullRun, ``infer_full_replay_closed,
  ``SynthesisInference.reuseFull, ``SynthesisInference.reuseFullClosed, ``SynthesisInference.reuseFullAcross,
  ``BetaPublicWhnfPlan.inference_frame, ``BetaPublicWhnfPlan.policy,
  ``BetaPiExposure.inference_frame, ``BetaPiExposure.policy
]

private def cacheHistoryRoots : Array Lean.Name := #[
  ``InferenceCacheTrace.populated_outside, ``InferenceCacheTrace.populated_frame,
  ``BetaPublicWhnfPlan.inference_maps, ``BetaPiExposure.inference_maps,
  ``InferenceCacheEvent.ofRun, ``InferenceCacheEvent.fullStep, ``InferenceCacheEvent.onlyStep,
  ``InferenceCacheEvent.applyFull, ``InferenceCacheEvent.applyOnly,
  ``InferenceCacheEvent.applyFull_nil, ``InferenceCacheEvent.applyOnly_nil,
  ``InferenceCacheEvent.applyFull_append, ``InferenceCacheEvent.applyOnly_append,
  ``InferenceCacheEvent.applyFull_origin, ``InferenceCacheEvent.applyOnly_origin,
  ``InferenceCacheTrace.events, ``InferenceCacheTrace.childEvents, ``InferenceCacheTrace.cache_maps,
  ``InferenceCacheHistory.ofMaps, ``InferenceCacheHistory.afterInference,
  ``InferenceCacheHistory.policy, ``InferenceCacheHistory.truncate, ``InferenceCacheHistory.afterInferKey,
  ``InferenceCacheHistory.openBinder, ``InferenceCacheHistory.getConst, ``InferenceCacheHistory.clear,
  ``InferenceCacheHistory.full_origin, ``InferenceCacheHistory.only_origin,
  ``InferenceCacheHistory.KeyData, ``InferenceCacheHistory.KeyData.same, ``InferenceCacheHistory.selected_origin,
  ``SynthesisEventCheck.ofSource, ``SynthesisEventCheck.extend, ``SynthesisEventCheck.retained,
  ``SynthesisEventCheck.result_reading, ``SynthesisEventCheck.cached,
  ``SynthesisEventChecks, ``SynthesisEventChecks.nil, ``SynthesisEventChecks.append,
  ``SynthesisEventChecks.singleton, ``SynthesisEventChecks.extend,
  ``SynthesisCacheHistory.ofMaps, ``SynthesisCacheHistory.extend, ``SynthesisCacheHistory.afterInference,
  ``SynthesisCacheHistory.policy, ``SynthesisCacheHistory.truncate, ``SynthesisCacheHistory.openBinder,
  ``SynthesisCacheHistory.getConst, ``SynthesisCacheHistory.clear,
  ``SynthesisCacheHistory.select, ``SynthesisCacheHistory.observe,
  ``SynthesisCacheSupplement.ofLeaf, ``SynthesisCacheSupplement.sortOfKey,
  ``SynthesisCacheSupplement.fvarOfKey, ``SynthesisCacheSupplement.verifiedConstOfKey,
  ``SynthesisCacheSupplement.complete, ``SynthesisInference.CacheData,
  ``SynthesisInference.cacheExecution, ``SynthesisCacheHistory.afterSynthesis
]

private def cacheTransportRoots : Array RootAllowance := #[
  { root := ``liftedSpineView, standardAxioms := #[``propext] },
  { root := ``liftedForallView },
  { root := ``liftedLambdaView },
  { root := ``liftedApplicationView },
  { root := ``liftedVariableSpineView, standardAxioms := #[``propext] },
  { root := ``liftN_sort_inv },
  { root := ``InterfaceExtends.conversion, standardAxioms := standard },
  { root := ``InterfaceExtends.argumentSpine, standardAxioms := standard },
  { root := ``InterfaceExtends.lambdaSpine, standardAxioms := standard },
  { root := ``ContextInsertion.argumentSpine, standardAxioms := standard },
  { root := ``ContextInsertion.lambdaSpine, standardAxioms := standard }
] ++ #[
  ``SynthesisRetainedCheck.forallBody,
  ``SynthesisRetainedCheck.variableSpineOrigin,
  ``SynthesisRetainedCheck.lambdaBodyVariableSpine,
  ``SynthesisRetainedCheck.lambdaPrefix,
  ``SynthesisRetainedCheck.origin,
  ``SynthesisRetainedCheck.typeOrigin,
  ``SynthesisRetainedCheck.spineOrigin,
  ``SynthesisRetainedCheck.soundWithSpine,
  ``SynthesisRetainedCheck.soundWithHereditary,
  ``SynthesisRetainedCheck.betaNextOrigin,
  ``SynthesisRetainedCheck.betaTyping,
  ``SynthesisVariableSpineOrigin.weakenAt,
  ``SynthesisVariableSpineOrigin.rebase,
  ``SynthesisArgumentSpineOrigin.weakenAt,
  ``SynthesisArgumentSpineOrigin.rebase,
  ``SynthesisSpineOrigin.extend,
  ``SynthesisSpineOrigin.weakenAt,
  ``SynthesisSpineOrigin.rebase,
  ``SynthesisReductionOrigin.weakenAt,
  ``SynthesisBetaTyping.extend,
  ``SynthesisBetaTyping.rebase,
  ``CachedSynthesisCheck.ofFull,
  ``CachedSynthesisCheck.ofClosedFull,
  ``CachedSynthesisCheck.frame,
  ``CachedSynthesisCheck.extend,
  ``CachedSynthesisCheck.weaken,
  ``CachedSynthesisCheck.afterOpenBinder,
  ``CachedSynthesisCheck.afterInference,
  ``CachedSynthesisCheck.hit,
  ``CachedSynthesisCheck.support,
  ``CachedSynthesisCheck.run,
  ``CachedSynthesisCheck.sound
].map (fun root => { root, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] })

private def lazyCacheRoots : Array Lean.Name := #[
  ``ingressAnonStandalone_cache, ``ingressAnonAddrShallow_cache, ``lazyIngressAddr_cache,
  ``tryGetConst_standalone_cache, ``getConst_standalone_cache,
  ``CachedConstantInferenceSupport.afterGetConst, ``CachedConstantInferenceSupport.afterFailedGetConst,
  ``BlockEntriesCompatible.ofFresh, ``BlockEntriesCompatible.ofLookups,
  ``prepareAnonBlock_cache, ``ingressAnonBlockWithTrace_cache, ``ingressAnonBlock_cache,
  ``ingressAnonAddrShallow_verified_cache, ``StandaloneLazySupport.toVerified,
  ``lazyIngressAddr_verified_cache, ``tryGetConst_verified_cache, ``getConst_verified_cache,
  ``CachedConstantInferenceSupport.afterVerifiedGetConst,
  ``CachedConstantInferenceSupport.afterFailedVerifiedGetConst,
  ``convertExpr_coherent, ``convertAnonStandalone_coherent, ``convertAnonBlock_coherent,
  ``prepareAnonBlock_coherent, ``ingressAnonBlock_coherent, ``ingressAnonAddrShallow_coherent,
  ``lazyIngressAddr_coherent, ``tryGetConst_coherent, ``getConst_coherent,
  ``UniverseInstantiationSupport.afterVerifiedGetConst
]

private def sourceOwnershipRoots : Array Lean.Name := #[
  ``SourceOwnership.ofOwner, ``LoadedBlockInvariant.empty,
  ``LoadedBlockInvariant.ofMaps, ``LoadedBlockInvariant.intern,
  ``sourceOwnershipRows_mem, ``SourceOwnership.ofCheck
]

private def ownedLoaderRoots : Array Lean.Name := #[
  ``convertAnonBlock_projection_keys, ``LoadedBlockInvariant.compatible,
  ``LoadedBlockInvariant.materialization, ``ingressAnonBlock_blocks,
  ``ingressAnonAddrShallow_blocks, ``OwnedLazySupport.toVerified,
  ``lazyIngressAddr_blocks, ``tryGetConst_blocks, ``getConst_owned,
  ``OwnedLazySupport.afterGetConst, ``OwnedLazySupport.afterFailedGetConst,
  ``OwnedLazySupport.afterInferKey, ``InferenceCacheTrace.ownedConstOfKey,
  ``OwnedLazySupport.afterConstInference, ``CachedConstantInferenceSupport.afterOwnedInference
]

private def recursiveStateRoots : Array Lean.Name := #[
  ``InferenceStateInvariant.owned, ``InferenceStateInvariant.ofOwned,
  ``InferenceStateInvariant.ofMaps, ``InferenceStateInvariant.afterInferKey,
  ``InferenceStateInvariant.getConst, ``InferenceStateInvariant.openBinder,
  ``OwnedInferenceTrace.writes, ``OwnedInferenceTrace.preserves,
  ``OwnedInferenceTrace.toCacheTrace, ``OwnedInferenceTrace.toCacheTrace_writes,
  ``OwnedInferenceTrace.frame, ``OwnedInferenceTrace.sortOfKey,
  ``OwnedInferenceTrace.fvarOfKey, ``OwnedInferenceTrace.constOfKey,
  ``InferenceStateInvariant.afterConstInference,
  ``CachedConstantInferenceSupport.afterOwnedRecursiveInference,
  ``BinderInference.sortAfterOwnedInference
]

private def conversionUniverseRoots : Array Lean.Name := #[
  ``conversionRecipe_univStep, ``conversionRecipe_univLoop, ``conversionRecipe_univTree,
  ``conversionRecipe_univIdx, ``conversionRecipe_univArgs
]

private def sourceAgreementRoots : Array Lean.Name := #[
  ``conversionRecipe_exprStep, ``conversionRecipe_exprLoop, ``conversionRecipe_expr,
  ``conversionRecipe_defn, ``conversionRecipe_recursor, ``conversionRecipe_standalone,
  ``convertAnonStandalone_prediction, ``predictStandalone?_verified, ``predictStandalone?_some,
  ``StandaloneSourceAgreement.empty, ``StandaloneSourceAgreement.ofMap,
  ``SourceOwnership.projection_unpredicted, ``ingressAnonBlock_sourceAgreement,
  ``ingressAnonStandalone_sourceAgreement, ``ingressAnonAddrShallow_sourceAgreement,
  ``SourceStateInvariant.ofMaps, ``SourceStateInvariant.afterInferKey,
  ``lazyIngressAddr_sourceAgreement, ``tryGetConst_sourceAgreement, ``getConst_sourceAgreement,
  ``SourceStateInvariant.getConst, ``StandaloneModelBinding.getConst,
  ``ScopedConstantInferenceSupport.ofSource, ``ConstantInferenceSupport.ofSource,
  ``infer_const_source_sound, ``SourceStateInvariant.openBinder,
  ``OwnedInferenceTrace.SourceData, ``OwnedInferenceTrace.preservesSource,
  ``OwnedInferenceTrace.frameSource
]

private def sourceCacheRoots : Array Lean.Name := #[
  ``SourceCacheRequest.term, ``SourceCacheRequest.result, ``SourceCacheRequest.key,
  ``SourceCacheRequest.closed, ``SourceCacheRequest.Loaded, ``SourceCacheRequest.Loaded.frame,
  ``SourceCacheRequest.Loaded.ofMap, ``SourceCacheEntry.frame, ``SourceCacheAgreement,
  ``SourceCacheAgreement.ofMaps, ``SourceCacheAgreement.afterInferKey,
  ``SourceCacheAgreement.openBinder, ``SourceCacheAgreement.getConst, ``SourceCacheAgreement.write,
  ``SourceCacheKeyData, ``SourceCacheKeyData.same, ``OwnedInferenceTrace.CacheData,
  ``OwnedInferenceTrace.preservesCache, ``OwnedInferenceTrace.preservesSourceCache,
  ``SourceCacheInvariant.getConst, ``SourceCacheInvariant.policy, ``SourceCacheInvariant.truncate,
  ``SourceCacheInvariant.openBinder, ``SourceCacheInvariant.clearReductionCaches,
  ``StandaloneModelBinding.cacheRequest, ``CachedConstantInferenceSupport.ofSourceCache,
  ``BinderInference.constFromSourceCache, ``BinderInference.sortFromSourceCache
]

private def sourceCacheInitialRoots : Array Lean.Name := #[
  ``SourceCacheAgreement.empty, ``SourceCacheInvariant.ofCheckedSource,
  ``SourceCacheHistory.invariant, ``infer_const_history_sound,
  ``InferenceCacheHistory.initial, ``SynthesisCacheHistory.initial
]

private def productionRoots : Array Lean.Name := #[
  ``axiom_type_trace, ``AxiomObservation.synthesisTypeCheck, ``StandalonePrefix.definitionTypeCheck,
  ``StandalonePrefix.member_success, ``definition_body_trace,
  ``AtomicDefinitionRun.sound, ``AtomicDefinitionRun.no_self_alias,
  ``WorkPosition.check_success, ``AtomicDefinitionPlan.extends,
  ``AtomicDefinitionPlan.sound, ``AtomicDefinitionPlan.represents,
  ``checkEnvAnon_atomic_preserves_model, ``checkEnvAnon_atomic_represents_source,
  ``checkEnvAnon_atomic_no_false
]

private def scopedRoots : Array Lean.Name := #[
  ``localIndex?_mem, ``localIndex?_getElem, ``localIndex?_fresh,
  ``readScopedExpr?_closed, ``readScopedExpr?_weaken_closed, ``readScopedExpr?_eraseMeta,
  ``beq_readScopedExpr?, ``internExpr_readScopedExpr?, ``readScopedExpr?_push,
  ``LocalContextReading.empty, ``readScopedExpr?_scope, ``readScopedExpr?_annotated_scope
]

private def contextRoots : Array Lean.Name := #[
  ``localContext_find?_push_same, ``localContext_find?_push_ne,
  ``LocalContextReading.push, ``ScopedModelTyping.closed
]

private def binderWalkerRoots : Array Lean.Name := #[
  ``inferKey_lctx, ``UncachedInference.localContext,
  ``readScopedExpr?_instantiateRevSpec, ``readScopedExpr?_abstractFVarsSpec,
  ``openBinder_eq, ``openBinder_sound,
  ``abstractFVars_singleton_spec, ``abstractFVars_readScopedExpr?,
  ``readScopedExpr?_liftSpec, ``readScopedExpr?_substSpec, ``subst_readScopedExpr?,
  ``KExpr.simulSubstSpec_singleton_eq, ``simulSubst_singleton_readScopedExpr?,
  ``ApplicationSubstitutionData.coherent, ``LambdaClosingData.coherent
]

/-- Production roots must not acquire a checker-soundness assumption
or invoke the independent certificate validator to establish acceptance. -/
private def forbiddenProduction : Array Lean.Name := #[
  `Ix.Kernel.CheckSuccessSound,
  `Ix.Kernel.SupportedCheckFragment,
  `Ix.Theory.Certified.checkProofCertified,
  `Ix.Certified.acceptsSerializedStore
]

/-- Typed lambda-prefix reduction and its concrete walker/plan boundaries. -/
private def betaRoots : Array RootAllowance := #[
  { root := ``Theory.Model.AExpr.appN_nil },
  { root := ``Theory.Model.AExpr.appN_cons },
  { root := ``Theory.Model.LambdaPrefix.inst },
  { root := ``Theory.Model.LambdaPrefix.truncate, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.LambdaPeel.length_bound, standardAxioms := #[``propext] },
  { root := ``Theory.Model.LambdaPeel.inst },
  { root := ``Theory.Model.LambdaPeel.snoc, standardAxioms := #[``propext] },
  { root := ``Theory.Model.LambdaPeel.betaPrefix, standardAxioms := #[``propext] },
  { root := ``Theory.Model.ArgumentSpine.append, standardAxioms := standard },
  { root := ``Theory.Model.ArgumentSpine.typing, standardAxioms := standard },
  { root := ``Theory.Model.ConversionClaim.appN, standardAxioms := standard },
  { root := ``Theory.Model.LambdaPrefix.beta_sound, standardAxioms := standard },
  { root := ``Theory.Model.AExpr.inst_liftN_top, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.instRevAt_zero },
  { root := ``Theory.Model.AExpr.erase_instRevAt, standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.instRevAt_sort },
  { root := ``Theory.Model.AExpr.instRevAt_const },
  { root := ``Theory.Model.AExpr.instRevAt_natLit },
  { root := ``Theory.Model.AExpr.instRevAt_app, standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.instRevAt_lam, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.instRevAt_forallE, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.instRevAt_proj, standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.instRevAt_liftN, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.instRevAt_bvar_below, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.instRevAt_bvar_above, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.instRevAt_bvar_selected, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``BinderInference.lambdaPrefix, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.lambdaPrefix, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisHead.appN_head },
  { root := ``SynthesisInference.lambda_spine, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.beta_spine_sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.beta_peel_sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.beta_many_step, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``readScopedExpr?_simulSubstSpec, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``simulSubst_readScopedExpr?, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``argumentsReading_get, standardAxioms := #[``propext] },
  { root := ``argumentsReading_reverse_get, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``readScopedExpr?_appN, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``readScopedExpr?_collectSpine, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``betaPeel_readScopedExpr?, standardAxioms := #[``propext] },
  { root := ``internAppChain_readScopedExpr?, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``finishAppResult_readScopedExpr?, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``DefinitionBodyTrace.betaDeclaredSpineSupport, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``RecM.appSpineView_go, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``RecM.appSpineView_collectSpine, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``RecM.finishAppResult_eq_foldlM, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``RecM.finishAppResult_eq_internAppChain, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``RecM.whnfCoreWithFlagsStep_betaMany, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``RecM.BetaPeel.fuel, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``RecM.BetaPeel.of_consume, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``RecM.BetaPeel.remaining_eq_drop, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``RecM.BetaPeel.consumed_append_remaining, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``RecM.BetaPeel.prepend },
  { root := ``RecM.BetaPeel.of_peelLamsN, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``WalkerRequest.Bounds.cheapBeta_simul, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``cheapBetaPlan?_simul, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``SynthesisInference.cheapBeta_plan_sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] }
]

private def typeOriginRoots : Array RootAllowance := #[
  { root := ``LambdaBodyTrace.output_state, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``LambdaBodyTrace.output, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``readScopedExpr?_lambda_spine, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``CheapBetaSupport.reading, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``TypeReductionTransport.weakenPrefix, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``TypeReductionTransport.instantiatePrefix, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``TypeReductionTransport.sound, standardAxioms := standard },
  { root := ``BinderInference.lambdaSpineTyping, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.soundWithSpine, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisContext.sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``Theory.Model.AExpr.instL_liftN, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.instL_inst, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.liftN_liftN_comm, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.liftN_inst, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.liftN_inst_zero, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.lambdaDepth_liftN, standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.lambdaDepth_instL, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.liftN_appN },
  { root := ``Theory.Model.AExpr.instL_appN, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.liftN_betaPrefix, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.instL_betaPrefix, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.appN_ne_forallE },
  { root := ``Theory.Model.LambdaPrefix.lambdaDepth_zero, standardAxioms := #[``propext] },
  { root := ``Theory.Model.LambdaSpineTyping.non_application, standardAxioms := standard },
  { root := ``Theory.Model.LambdaSpineTyping.lam, standardAxioms := standard },
  { root := ``Theory.Model.LambdaSpineTyping.app, standardAxioms := standard },
  { root := ``Theory.Model.LambdaSpineTyping.betaPrefix, standardAxioms := standard }
]

private def substitutedOriginRoots : Array RootAllowance := #[
  { root := ``Theory.Model.AExpr.liftN_liftN_merge, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.inst_liftN, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.inst_liftN_within, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.inst_inst, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.inst_inst_zero, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.lambdaDepth_le_inst, standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.inst_appN },
  { root := ``Theory.Model.AExpr.inst_betaPrefix, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.Context.Valid.tail, standardAxioms := standard },
  { root := ``Theory.Model.Context.Valid.head, standardAxioms := standard },
  { root := ``Theory.Model.ContextSubstitution.base_valid, standardAxioms := standard },
  { root := ``Theory.Model.ContextSubstitution.source_valid, standardAxioms := standard },
  { root := ``Theory.Model.TypingClaim.instAt, standardAxioms := standard },
  { root := ``Theory.Model.CheckingClaim.instAt, standardAxioms := standard },
  { root := ``Theory.Model.ConversionClaim.instAt, standardAxioms := standard },
  { root := ``context_valid_instL, standardAxioms := standard },
  { root := ``typing_instL_context, standardAxioms := standard },
  { root := ``context_valid_prefix, standardAxioms := standard },
  { root := ``typing_append_context, standardAxioms := standard },
  { root := ``context_push_instL, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``SynthesisTypeTransport.sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisTypingOrigin.sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisTypeTransport.substitutePrefixAt, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``ApplicationInferenceTrace.substituteTypeOriginAt, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``ApplicationInferenceTrace.substituteTypeOrigin, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BinderInference.forallBodyCheck, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.forallBodyCheck, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisTypeCheck.forallBody, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] }
]

private def exposedOriginRoots : Array RootAllowance := #[
  { root := ``Theory.Model.AExpr.liftN_zero, standardAxioms := #[``propext] },
  { root := ``Theory.Model.LambdaPrefix.liftN },
  { root := ``Theory.Model.LambdaPrefix.instL, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.ArgumentSpine.instAt, standardAxioms := standard },
  { root := ``Theory.Model.ContextSubstitution.removed_type, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.ContextSubstitution.instantiate_removed_type, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.ContextSubstitution.lookup_other, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.ContextSubstitution.lift_typing, standardAxioms := standard },
  { root := ``SynthesisArgumentSpineOrigin.weaken, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisArgumentSpineOrigin.instantiate, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisArgumentSpineOrigin.appendContext, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisArgumentSpineOrigin.extend, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisArgumentSpineOrigin.substituteAt, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisVariableSpineOrigin.appendContext, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisVariableSpineOrigin.instantiate, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisVariableSpineOrigin.extend, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisVariableSpineOrigin.substituteAt, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``ApplicationInferenceTrace.exposedTypeOriginAt, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``ApplicationInferenceTrace.substituteReductionOriginAt, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BinderInference.variableSpineOrigin, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.variableSpineOrigin, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisForallBodyCheck.variableSpine, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisCheckedOrigin.sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisArgumentSpineOrigin.sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisReductionOrigin.sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisScopedTypeCheck.sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisScopedTypeCheck.forallBody, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisScopedTypeCheck.variableSpine, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisTypeCheck.scoped, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``Theory.Model.AExpr.inst_variable_appN, standardAxioms := #[``propext] },
  { root := ``Theory.Model.ContextSubstitution.lift_spine, standardAxioms := standard },
  { root := ``Theory.Model.LambdaSpineTyping.substituteHead, standardAxioms := standard },
  { root := ``SynthesisCheckedOrigin.soundWithSpine, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``ApplicationInferenceTrace.exposedApplicationOriginAt, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] }
]

private def repeatedBetaRoots : Array RootAllowance := #[
  { root := ``Theory.Model.AExpr.inst_liftN_self, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.TypingClaim.lambdaBody, standardAxioms := standard },
  { root := ``Theory.Model.TypingClaim.termConv, standardAxioms := standard },
  { root := ``BinderInference.lambdaBodyVariableSpine, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.lambdaBodyVariableSpine, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.betaResultOrigin, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.betaNextOrigin, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.beta_twice_sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``beta_many_step_readScopedExpr?, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisReductionOrigin.beta_many_step, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``DefinitionBodyTrace.betaDeclaredTwiceSupport, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] }
]

private def betaTraceRoots : Array RootAllowance := #[
  { root := ``SynthesisTypingOrigin.applySpine, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTrace.applySpine, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTrace.beta, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BinderInference.spineOrigin, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.spineOrigin, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisSpineOrigin.betaTrace, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.betaSpineTrace, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTrace.sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaStep.run, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaStep.sourceReading, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaStep.reading, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaWhnfTrace.toBetaTrace, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaWhnfTrace.run, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaWhnfTrace.reading, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaWhnfTrace.uncached_sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``DefinitionBodyTrace.betaDeclaredTraceSupport, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``DefinitionBodyTrace.betaDeclaredWhnfSupport, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] }
]

private def hereditaryBetaRoots : Array RootAllowance := #[
  { root := ``ContextInsertion.lookup, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``ContextInsertion.source_valid, standardAxioms := standard },
  { root := ``ContextInsertion.typing, standardAxioms := standard },
  { root := ``ContextInsertion.conversion, standardAxioms := standard },
  { root := ``SynthesisBetaTrace.rigid, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaSyntax.steps_betaPrefix, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``SynthesisBetaTyping.origin, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.lambdaView, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.ForallView, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.forallView, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.ForallView.sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.ForallView.variableSpine, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.spineOrigin, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.variableSpineOrigin, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.lambdaBodyVariableSpine, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.weakenAt, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.substituteAt, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.lambdaPrefix, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.betaStep, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.betaSteps, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisBetaTyping.betaPrefix, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaSubstitutionContext.relation },
  { root := ``BetaSubstitutionContext.liftValue, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BinderInference.betaTyping, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.betaTyping, standardAxioms := standard,
    nativeAxioms := #[expressionNative, levelNative], forbiddenDependencies := #[``HereditaryTyping] },
  { root := ``SynthesisInference.beta_steps_sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaStepPlan.run, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaStepPlan.sourceReading, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``BetaStepPlan.reading, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``BetaStepPlan.counts, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``BetaStepPlan.betaTyping, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaWhnfTrace.annotate, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.beta_whnf_sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``DefinitionBodyTrace.betaDeclaredStepsSupport, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``DefinitionBodyTrace.betaDeclaredWhnfPathSupport, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] }
]

private def piExposureRoots : Array RootAllowance := #[
  { root := ``Theory.Model.AExpr.HeadRigid.map },
  { root := ``Theory.Model.ContextSubstitution.lift_conversion, standardAxioms := standard },
  { root := ``Theory.Model.LambdaSpineTyping.convert, standardAxioms := standard },
  { root := ``BetaWhnfTrace.run, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaWhnfTrace.reading, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaWhnfTrace.frame, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaWhnfTrace.first, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaStepPlan.not_transient, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``betaWhnfKey_run, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``betaWhnfKey_environment, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``betaWhnfKey_context, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``betaWhnfKey_native, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``betaWhnfKey_fuel, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``betaWhnfPrefix_run, standardAxioms := standard },
  { root := ``betaWhnfPrefix_fields, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``betaWhnfCharge_run, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``betaWhnfCharge_fields, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``BetaWhnfTerminal.noDelta_tail, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaWhnfTerminal.full_step, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaWhnfTerminal.noDelta_uncached, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaWhnfTerminal.full_uncached, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaPublicWhnf.coreKey_fields, standardAxioms := standard, nativeAxioms := #[expressionNative] },
  { root := ``BetaPublicWhnfPlan.run, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaPublicWhnfPlan.reading, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaPublicWhnfPlan.context, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaPublicWhnfPlan.cache_hit, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaPiExposure.run, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaPiExposure.reading, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaPiExposure.context, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``ApplicationWhnfInferenceTrace.output_state, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``ApplicationWhnfInferenceTrace.output, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``ApplicationWhnfInferenceTrace.exposure_state, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``ApplicationWhnfInferenceTrace.exposure_context, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``ApplicationWhnfInferenceTrace.ofBeta, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaPublicWhnfPlan.betaTrace, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaPiExposure.betaTrace, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``BetaPiExposure.checkedTrace, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] },
  { root := ``SynthesisInference.beta_public_whnf_sound, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative] }
]

/-- Cache producers and replay must precede semantic hereditary typing.
The operational layer records raw executions and derives published hits. -/
private def mixedCacheFrameRoots : Array Lean.Name := #[
  ``BetaCacheExecution.writeNoDelta_intern,
  ``BetaCacheExecution.writeFull_intern
]

private def mixedCacheKeyRoots : Array Lean.Name := #[
  ``BetaCacheFrame.refl,
  ``BetaCacheFrame.trans,
  ``BetaCacheFrame.instrument,
  ``BetaCacheFrame.charge,
  ``BetaCacheExecution.writeNoDelta_frame,
  ``BetaCacheExecution.writeFull_frame,
  ``betaWhnfKey_congr,
  ``betaWhnfKey_replay,
  ``betaWhnfKey_prefix,
  ``betaWhnfKey_charge,
  ``BetaCacheFrame.key,
  ``BetaCacheExecution.writeNoDelta_key,
  ``BetaCacheExecution.writeFull_key
]

private def mixedCacheExecutionRoots : Array Lean.Name := #[
  ``BetaCoreExecution.after,
  ``BetaCoreExecution.first,
  ``BetaCoreExecution.terminal,
  ``BetaCoreExecution.run,
  ``BetaCoreExecution.reading,
  ``BetaCoreExecution.frame,
  ``BetaCoreExecution.stable_key,
  ``BetaCoreExecution.published,
  ``BetaCoreExecution.replay,
  ``BetaCoreExecution.replay_run,
  ``BetaCoreExecution.betaTrace,
  ``BetaNoDeltaExecution.after,
  ``BetaNoDeltaExecution.first,
  ``BetaNoDeltaExecution.terminal,
  ``BetaNoDeltaExecution.run,
  ``BetaNoDeltaExecution.reading,
  ``BetaNoDeltaExecution.frame,
  ``BetaNoDeltaExecution.stable_key,
  ``BetaNoDeltaExecution.published,
  ``BetaNoDeltaExecution.replay,
  ``BetaNoDeltaExecution.replay_run,
  ``BetaNoDeltaExecution.betaTrace,
  ``BetaPublicExecution.after,
  ``BetaPublicExecution.first,
  ``BetaPublicExecution.terminal,
  ``BetaPublicExecution.run,
  ``BetaPublicExecution.reading,
  ``BetaPublicExecution.frame,
  ``BetaPublicExecution.stable_key,
  ``BetaPublicExecution.published,
  ``BetaPublicExecution.replay,
  ``BetaPublicExecution.replay_run,
  ``BetaPublicExecution.betaTrace,
  ``BetaPublicWhnfPlan.execution,
  ``BetaPublicWhnfPlan.execution_after,
  ``RecM.whnfNoDeltaImplNonLeaf_fullMiss_conditional,
  ``RecM.whnfWithNatSuccModeNonLeaf_miss_conditional
]

/-- Source reconstruction and success inversion must not depend on the
semantic invariant that the original inference soundness theorem derives. -/
private def betaSourceExprRoots : Array Lean.Name := #[
  ``BetaStepSource.selected_not_transient,
  ``BetaStepSource.peeled,
  ``BetaStepSource.substituted,
  ``BetaStepSource.output,
  ``BetaStepSource.after,
  ``BetaStepSource.Resources,
  ``BetaStepSource.construct,
  ``BetaStepSource.construct_result,
  ``BetaStepSource.construct_after
]

private def betaSourceExecutionRoots : Array Lean.Name := #[
  ``BetaWhnfSource.Resources,
  ``BetaWhnfSource.Resources.first,
  ``BetaStepSource.construct_run,
  ``BetaWhnfTerminal.core_step,
  ``BetaWhnfSource.Witness,
  ``BetaWhnfSource.construct,
  ``BetaCoreExecution.exists_of_miss_success,
  ``BetaWhnfSource.CoreResources,
  ``BetaWhnfSource.NoDeltaResources,
  ``BetaWhnfSource.PublicResources,
  ``BetaCoreExecution.exists_of_success,
  ``BetaNoDeltaExecution.exists_of_success,
  ``BetaPublicExecution.exists_of_success,
  ``BetaSortExposure.exists_of_success,
  ``BetaPiExposure.exists_of_success,
  ``RecM.whnfCoreWithFlagsNonLeaf_fullMiss_success,
  ``RecM.whnfNoDeltaImplNonLeaf_fullMiss_core_success,
  ``RecM.whnfWithNatSuccModeNonLeaf_miss_noDelta_success,
  ``RecM.ensureSortWhnf_success,
  ``RecM.ensureForallWhnf_success
]

private def letWhnfSyntaxRoots : Array Lean.Name := #[
  ``StructuralWhnfEntry,
  ``LetStepSource.selected,
  ``LetStepSource.parts,
  ``LetStepSource.selected_entry,
  ``BetaStepSource.selected_entry,
  ``BetaWhnfSource.selected,
  ``BetaWhnfSource.selected_entry
]

private def letWhnfExprRoots : Array Lean.Name := #[
  ``StructuralWhnfEntry.not_transient,
  ``LetStepPlan,
  ``LetStepPlan.output,
  ``LetStepPlan.result,
  ``LetStepPlan.after,
  ``LetStepPlan.entry,
  ``LetStepPlan.reading,
  ``LetStepSource.output,
  ``LetStepSource.after,
  ``LetStepSource.Resources,
  ``LetStepSource.construct,
  ``LetStepSource.construct_result,
  ``LetStepSource.construct_after,
  ``BetaStepPlan.entry
]

private def letWhnfExecutionRoots : Array Lean.Name := #[
  ``StructuralWhnfEntry.core,
  ``StructuralWhnfEntry.noDelta,
  ``StructuralWhnfEntry.full,
  ``StructuralWhnfEntry.sort,
  ``StructuralWhnfEntry.forallE,
  ``LetStepPlan.run
]

/-- Recursive head calls retain their own method depth, full/cheap cache
effects, and source-derived beta continuation. No head annotation or raw
execution proof may depend on the semantic hereditary invariant. -/
private def headWhnfSyntaxRoots : Array Lean.Name := #[
  ``AppSpineSource.parts,
  ``BetaPrefixSource.selected,
  ``BetaHeadStepSource.selected,
  ``BetaHeadStepSource.selected_app,
  ``BetaHeadStepSource.selected_head,
  ``BetaHeadStepSource.selected_entry
]

private def headWhnfFrameRoots : Array Lean.Name := #[
  ``AppSpineSource.reading,
  ``AppSpineSource.nonempty,
  ``BetaCoreCache.lookup,
  ``BetaCoreCache.write,
  ``BetaCoreCache.intern
]

private def headWhnfExprRoots : Array Lean.Name := #[
  ``BetaPrefixPlan,
  ``BetaPrefixPlan.rawLambda,
  ``BetaPrefixPlan.modelLambda,
  ``BetaPrefixPlan.modelInput,
  ``BetaPrefixPlan.output,
  ``BetaPrefixPlan.result,
  ``BetaPrefixPlan.after,
  ``BetaPrefixPlan.modelResult,
  ``BetaPrefixPlan.counts,
  ``BetaPrefixPlan.reading,
  ``BetaPrefixSource.peeled,
  ``BetaPrefixSource.substituted,
  ``BetaPrefixSource.output,
  ``BetaPrefixSource.after,
  ``BetaPrefixSource.Resources,
  ``BetaPrefixSource.consumed_nonempty,
  ``BetaPrefixSource.Witness,
  ``BetaPrefixSource.construct,
  ``BetaPrefixSource.Witness.result,
  ``BetaPrefixSource.Witness.after,
  ``BetaHeadStepPlan,
  ``BetaHeadStepPlan.rawLambda,
  ``BetaHeadStepPlan.modelLambda,
  ``BetaHeadStepPlan.result,
  ``BetaHeadStepPlan.after,
  ``BetaHeadStepPlan.modelResult,
  ``BetaHeadStepPlan.entry,
  ``BetaHeadStepPlan.sourceReading,
  ``BetaHeadStepPlan.reading,
  ``BetaHeadStepSource.Witness,
  ``BetaHeadStepSource.construct,
  ``BetaCoreCache.frame,
  ``betaWhnfKey_key,
  ``BetaCacheFrame.intern,
  ``BetaCacheFrame.core,
  ``BetaCacheFrame.cheap
]

private def headWhnfExecutionRoots : Array Lean.Name := #[
  ``BetaPrefixPlan.run,
  ``BetaHeadStepPlan.run,
  ``BetaHeadStepSource.head_of_success,
  ``BetaCoreCache.hit,
  ``BetaCoreCache.miss,
  ``BetaCoreCache.miss_success,
  ``SynthesisBetaTyping.mapFunction,
  ``SynthesisBetaTyping.mapHead,
  ``BetaHeadReduction,
  ``BetaHeadReduction.entry,
  ``BetaHeadReduction.run,
  ``BetaHeadReduction.reading,
  ``BetaHeadReduction.frame,
  ``BetaPrefixPlan.betaTyping,
  ``BetaHeadReduction.annotate,
  ``SynthesisBetaWhnfTrace.toRawTrace
]

/-- Replay reconstructs annotations from the current source reading. Neither
the raw producer nor its reconstruction may assume semantic typing. -/
private def betaReannotationExprRoots : Array Lean.Name := #[
  ``BetaPrefixPlan.sourceResources,
  ``BetaPrefixPlan.sourceOutput,
  ``BetaStepPlan.selected,
  ``BetaStepPlan.sourceResources,
  ``BetaStepPlan.sourceOutput,
  ``BetaStepPlan.sourceAfter,
  ``BetaHeadStepPlan.sourceSpine,
  ``BetaHeadStepPlan.sourceResources,
  ``BetaHeadStepPlan.sourceOutput,
  ``BetaHeadStepPlan.sourceAfter,
  ``BetaHeadStepSource.constructOfEntry
]

private def betaReannotationExecutionRoots : Array Lean.Name := #[
  ``BetaWhnfTrace.reannotate,
  ``BetaHeadReduction.reannotate,
  ``BetaHeadCacheOrigin,
  ``BetaHeadReduction.origin,
  ``BetaHeadReduction.published,
  ``BetaHeadReduction.replay,
  ``BetaHeadReduction.replay_run,
  ``BetaHeadCacheOrigin.replay,
  ``BetaWhnfSource.HeadOrigins,
  ``BetaWhnfSource.HeadOrigins.absent,
  ``BetaWhnfSource.HeadOrigins.ofCall,
  ``BetaWhnfSource.HeadOrigins.replay,
  ``BetaCoreExecution.reannotate,
  ``BetaNoDeltaExecution.reannotate,
  ``BetaPublicExecution.reannotate,
  ``BetaHeadReduction.exists_of_success,
  ``BetaWhnfSource.HeadOrigins.of_success,
  ``BetaWhnfSource.CoreResources.ofExecution,
  ``BetaWhnfSource.NoDeltaResources.ofExecution,
  ``BetaWhnfSource.PublicResources.ofExecution
]

/-- Complete WHNF histories retain raw producing calls. Current typing is
derived only after finite source-key selection and fresh annotation. -/
private def whnfHistoryFrameRoots : Array Lean.Name := #[
  ``WhnfCachePartition.cache, ``WhnfCachePartition.intern,
  ``WhnfCachePartition.instrument, ``WhnfCachePartition.charge,
  ``WhnfCachePartition.writeCore, ``WhnfCachePartition.writeNoDelta,
  ``WhnfCachePartition.writeFull, ``WhnfCachePartition.lookupCore
]

private def whnfHistoryExprRoots : Array Lean.Name := #[
  ``betaWhnfKey_address, ``WhnfCachePartition.key
]

private def whnfHistoryExecutionRoots : Array Lean.Name := #[
  ``BetaCoreExecution.cachedHead, ``BetaCoreExecution.headReduction,
  ``BetaCacheEventOrigin, ``BetaCacheEventOrigin.address, ``BetaCacheEvent,
  ``BetaCacheEvent.head, ``BetaCacheEvent.noDelta, ``BetaCacheEvent.full,
  ``BetaCacheEvent.step, ``BetaCacheEvent.apply, ``BetaCacheEvent.apply_nil,
  ``BetaCacheEvent.apply_append, ``BetaCacheEvent.apply_origin,
  ``BetaWhnfTrace.cacheEvents, ``BetaHeadReduction.cacheEvents,
  ``BetaWhnfTrace.cache_maps, ``BetaHeadReduction.cache_maps,
  ``BetaCoreExecution.cacheEvents, ``BetaCoreExecution.cache_maps,
  ``BetaNoDeltaExecution.cacheEvents, ``BetaNoDeltaExecution.cache_maps,
  ``BetaPublicExecution.cacheEvents, ``BetaPublicExecution.cache_maps,
  ``BetaCacheHistory, ``BetaCacheHistory.ofMaps, ``BetaCacheHistory.append,
  ``BetaCacheHistory.intern, ``BetaCacheHistory.key, ``BetaCacheHistory.instrument,
  ``BetaCacheHistory.charge, ``BetaCacheHistory.policy, ``BetaCacheHistory.truncate,
  ``BetaCacheHistory.openBinder, ``BetaCacheHistory.openLet, ``BetaCacheHistory.withLctxScope,
  ``BetaCacheHistory.clear, ``BetaCacheHistory.afterTrace, ``BetaCacheHistory.afterHead,
  ``BetaCacheHistory.afterCore, ``BetaCacheHistory.afterNoDelta, ``BetaCacheHistory.afterPublic,
  ``BetaCacheHistory.origin, ``BetaCacheHistory.KeyData, ``BetaCacheHistory.KeyData.same,
  ``BetaCacheHistory.selected_origin, ``BetaCacheHistory.selected,
  ``BetaWhnfTrace.boundedCacheHistory, ``BetaCacheEventOrigin.terminal,
  ``BetaCacheEventOrigin.headOrigin, ``BetaCacheEventOrigin.noDeltaOrigin, ``BetaCacheEventOrigin.fullOrigin,
  ``BetaCacheHistory.headOrigins, ``BetaCacheHistory.coreResources,
  ``BetaCacheHistory.noDeltaResources, ``BetaCacheHistory.publicResources,
  ``BetaCoreExecution.exists_of_history, ``BetaNoDeltaExecution.exists_of_history,
  ``BetaPublicExecution.exists_of_history, ``BetaPiExposure.cacheHistory, ``BetaSortExposure.cacheHistory
]

/-- Complete WHNF histories and intern coherence survive the supported
inference recursion. Exposure inputs derive their readings from the executed
source checks; no semantic typing invariant is assumed. -/
private def inferenceHistoryFrameRoots : Array Lean.Name := #[
  ``LazyLookupFrame.whnf_maps, ``BetaHistoryReading
]

private def inferenceHistoryExprRoots : Array Lean.Name := #[
  ``UncachedInference.keyedCoherent
]

private def inferenceHistoryExecutionRoots : Array Lean.Name := #[
  ``BetaCacheHistory.afterInferKey, ``BetaCacheHistory.getConst, ``BetaCacheHistory.hashConversion,
  ``BetaCacheHistory.afterMiss, ``BetaHistoryReading.afterPublic, ``BetaHistoryReading.afterPi,
  ``BetaHistoryReading.afterSort, ``InferenceCacheTrace.WhnfData, ``InferenceCacheTrace.whnfHistory,
  ``infer_miss_coherent, ``InferenceCacheTrace.const_coherent, ``InferenceCacheTrace.fvar_coherent,
  ``BinderInference.outputCoherent, ``SynthesisInference.outputCoherent,
  ``SynthesisSortCheck.historyReading, ``SynthesisSortCheck.afterCoherent
]

private def localScopeFrameRoots : Array Lean.Name := #[
  ``LocalContext.Equiv.refl, ``LocalContext.Equiv.symm, ``LocalContext.Equiv.trans,
  ``LocalContext.Equiv.size, ``LocalContext.Equiv.find?, ``LocalContext.Equiv.wf,
  ``LocalContext.Extension.trans, ``LocalContext.Extension.size_le,
  ``PreservesLocalExtension.pure, ``PreservesLocalExtension.throw,
  ``PreservesLocalExtension.bind, ``PreservesLocalExtension.runIntern,
  ``PreservesLocalExtension.withInferOnly
]

private def localStateFrameRoots : Array Lean.Name := #[
  ``TcM.InternOnly.pure,
  ``TcM.InternOnly.throw,
  ``TcM.InternOnly.bind,
  ``TcM.InternOnly.runIntern,
  ``TcM.InternOnly.ofExcept,
  ``TcM.InternOnly.map,
  ``LocalContext.IdsBelow.mono,
  ``LocalContext.IdsBelow.equiv,
  ``LocalContext.IdsBelow.fresh,
  ``LocalStateFrame.refl,
  ``LocalStateFrame.trans,
  ``LocalStateFrame.invariant,
  ``LocalStateExtension.refl,
  ``LocalStateExtension.trans,
  ``LocalStateExtension.of_frame,
  ``FramesLocalState.preserves,
  ``FramesLocalState.pure,
  ``FramesLocalState.throw,
  ``FramesLocalState.runIntern,
  ``FramesLocalState.of_internOnly,
  ``FramesLocalState.bind,
  ``PreservesLocalState.bind,
  ``FramesLocalState.get,
  ``FramesLocalState.modify,
  ``FramesLocalState.intern,
  ``FramesLocalState.withInferOnly,
  ``FramesLocalState.cacheInferResult,
  ``FramesLocalState.isEagerReduce,
  ``FramesLocalState.prims,
  ``FramesLocalState.lazyIngressAddr,
  ``FramesLocalState.tryGetConst,
  ``FramesLocalState.getConst
]

private def localStateMapRoots : Array Lean.Name := #[
  ``LocalContext.IdsBelow.empty,
  ``LocalContext.IdsBelow.push
]

private def localStateWalkerRoots : Array Lean.Name := #[
  ``LocalStateExtension.restore,
  ``PreservesLocalState.withLctxScope,
  ``PreservesLocalState.openLet,
  ``PreservesLocalState.openBinder,
  ``FramesLocalState.ctxAddrForLbr,
  ``FramesLocalState.inferKey,
  ``FramesLocalState.lookupVar
]

private def localStateOperationalRoots : Array Lean.Name := #[
  ``TcM.InternOnly.instantiateUnivParams,
  ``FramesLocalState.instantiateUnivParams,
  ``FramesLocalState.ensureSortWhnf,
  ``FramesLocalState.ensureSortDirect,
  ``FramesLocalState.ensureForallWhnf,
  ``FramesLocalState.ensureForallDirect,
  ``inferUncached_framesLocalState,
  ``FramesLocalState.inferWith,
  ``infer_framesLocalState,
  ``FramesLocalState.peelProjForall, ``FramesLocalState.instantiateProjParamStep,
  ``FramesLocalState.instantiateProjParams, ``FramesLocalState.inductiveAppBinderStep,
  ``FramesLocalState.inductiveAppBinders, ``FramesLocalState.inductiveAppResultIsProp,
  ``FramesLocalState.inductiveAppIsProp, ``FramesLocalState.inferProjFieldStep,
  ``FramesLocalState.inferProjFieldsLoopStep, ``FramesLocalState.inferProjFields,
  ``FramesLocalState.inferProj, ``infer_framesLocalState_of_whnf
]

private def ingressFrameRoots : Array Lean.Name := #[
  ``KEnv.IngressFrame.refl,
  ``KEnv.IngressFrame.trans,
  ``KEnv.IngressFrame.counter,
  ``KEnv.IngressFrame.insert,
  ``KEnv.IngressFrame.insertBlock,
  ``KEnv.IngressFrame.foldl,
  ``KEnv.IngressFrame.insertEntriesState,
  ``KEnv.IngressFrame.insertMutsEntriesState,
  ``IngressM.FramesState.pure,
  ``IngressM.FramesState.throw,
  ``IngressM.FramesState.get,
  ``IngressM.FramesState.modifyGet,
  ``IngressM.FramesState.liftExcept,
  ``IngressM.FramesState.bind,
  ``IngressM.FramesState.internE,
  ``IngressM.FramesState.internU,
  ``IngressM.FramesState.forInList,
  ``IngressM.FramesState.forInArray,
  ``IngressM.FramesState.forInList',
  ``ConvM.FramesState.pure,
  ``ConvM.FramesState.throw,
  ``ConvM.FramesState.get,
  ``ConvM.FramesState.modify,
  ``ConvM.FramesState.bind,
  ``ConvM.FramesState.lift,
  ``ConvM.FramesState.forInList,
  ``ConvM.FramesState.forInArray
]

private def ingressMapRoots : Array Lean.Name := #[
  ``IngressM.FramesState.forInRange,
  ``IngressM.FramesState.forInRange',
  ``IngressM.FramesState.guardReserved,
  ``IngressM.FramesState.insertStandaloneEntries,
  ``IngressM.FramesState.insertMutsEntries,
  ``ConvM.FramesState.forInRange
]

private def ingressLevelRoots : Array Lean.Name := #[
  ``IngressM.FramesState.ingressUnivTree,
  ``ConvM.FramesState.ingressUnivIdx,
  ``ConvM.FramesState.ingressUnivArgs
]

private def ingressOperationalRoots : Array Lean.Name := #[
  ``IngressM.FramesState.ingressDefnAnon,
  ``IngressM.FramesState.ingressRecursorAnon,
  ``IngressM.FramesState.ingressAnonInductive,
  ``IngressM.FramesState.ingressAnonStandalone,
  ``IngressM.FramesState.prepareAnonBlock,
  ``IngressM.FramesState.ingressAnonBlockWithTrace,
  ``IngressM.FramesState.ingressAnonBlock,
  ``IngressM.FramesState.ingressAnonAddrShallow,
  ``ConvM.FramesState.ingressExpr,
  ``LoaderCounterMonotone.ingressAnonAddrShallow
]

private def recursiveStateFrameRoots : Array Lean.Name := #[
  ``FramesLocalState.ofWF,
  ``FramesLocalState.tryCatch,
  ``FramesLocalState.tryFinally,
  ``FramesLocalState.map,
  ``FramesLocalState.modifyGet,
  ``FramesLocalState.tick,
  ``FramesLocalState.stepTrace,
  ``FramesLocalState.bumpStats,
  ``FramesLocalState.isLetVar,
  ``FramesLocalState.tryGetBlock,
  ``FramesLocalState.runBounded,
  ``FramesLocalState.forInList,
  ``FramesLocalState.forInArray,
  ``FramesLocalState.withCheapRecursionDepth,
  ``FramesLocalState.whnfRec,
  ``FramesLocalState.whnfModeRec,
  ``FramesLocalState.whnfCoreFlagsRec,
  ``FramesLocalState.inferOnlyRec,
  ``FramesLocalState.tryOptional,
  ``FramesLocalState.pureRec,
  ``FramesLocalState.throwRec,
  ``FramesLocalState.throwExceptRec,
  ``FramesLocalState.getRec,
  ``FramesLocalState.liftRec,
  ``FramesLocalState.liftSelf,
  ``FramesLocalState.mapRec,
  ``FramesLocalState.bindRead,
  ``FramesLocalState.tryProbe,
  ``FramesLocalState.bindRec,
  ``FramesLocalState.bindTcM,
  ``FramesLocalState.tryFinallyRec,
  ``FramesLocalState.tryCatchRec,
  ``FramesLocalState.tryCatchExceptRec,
  ``FramesLocalState.modifyRec,
  ``FramesLocalState.forInListTcM,
  ``FramesLocalState.isNatBinArithAddr,
  ``FramesLocalState.isNatBinPredAddr,
  ``FramesLocalState.boolLitValue,
  ``FramesLocalState.isNatStuckRecursorAddr,
  ``FramesLocalState.saveDepth,
  ``FramesLocalState.enterDispatch,
  ``FramesLocalState.exitDispatch,
  ``FramesLocalState.callIsDefEq,
  ``FramesLocalState.isNatLiteralRecursorApp,
  ``FramesLocalState.natRecLiteralParts,
  ``FramesLocalState.isStuckNatPredicateProbe,
  ``FramesLocalState.discoverBlockInductives,
  ``FramesLocalState.cacheIsRec,
  ``FramesLocalState.eraseCachedIsRec,
  ``FramesLocalState.isNatSuccSpine,
  ``FramesLocalState.recordNatSuccStuck,
  ``FramesLocalState.whnfNatReducerArg,
  ``FramesLocalState.inferDecidableProp,
  ``FramesLocalState.whnfWithNatSuccModeMissCharge,
  ``FramesLocalState.isDefEqCall,
  ``FramesLocalState.inferOnlyCall,
  ``FramesLocalState.withEquiv,
  ``FramesLocalState.allDefEqSpineArgsList,
  ``FramesLocalState.isNatLike,
  ``FramesLocalState.isNatZero,
  ``FramesLocalState.isBoolTrue,
  ``FramesLocalState.boolTrueReductionAllowed,
  ``FramesLocalState.isDelta,
  ``FramesLocalState.classifyDeltaHead,
  ``FramesLocalState.isRegular,
  ``FramesLocalState.defRankId,
  ``FramesLocalState.rankDeltaHead,
  ``FramesLocalState.allDefEqSpineArgs,
  ``FramesLocalState.tryDefEqWhnfApp,
  ``FramesLocalState.tryDefEqApp
]

private def recursiveStateMapRoots : Array Lean.Name := #[
  ``FramesLocalState.forInRange,
  ``FramesLocalState.pushLocal,
  ``FramesLocalState.pushLet,
  ``FramesLocalState.popLocal,
  ``FramesLocalState.restoreDepthGo,
  ``FramesLocalState.restoreDepth,
  ``FramesLocalState.peelMajorForalls,
  ``FramesLocalState.scanMajorInductiveStep,
  ``FramesLocalState.scanMajorInductive,
  ``FramesLocalState.getMajorInductiveId,
  ``FramesLocalState.computeIsRecParamStepAfterWhnf,
  ``FramesLocalState.computeIsRecParamStep,
  ``FramesLocalState.computeIsRecFieldStepAfterWhnf,
  ``FramesLocalState.computeIsRecFieldStep,
  ``FramesLocalState.computeIsRecCtor,
  ``FramesLocalState.computeIsRec,
  ``FramesLocalState.computedIsRecClassify,
  ``FramesLocalState.computedIsRecMiss,
  ``FramesLocalState.computedIsRec,
  ``FramesLocalState.isStructLike,
  ``FramesLocalState.whnfWithNatSuccModePrefix,
  ``FramesLocalState.trySameHeadSpine,
  ``FramesLocalState.trySameHeadSpineSpeculative,
  ``FramesLocalState.isUnitLikeInductive
]

private def recursiveStateExprRoots : Array Lean.Name := #[
  ``FramesLocalState.lookupLetVal,
  ``FramesLocalState.whnfKey,
  ``FramesLocalState.mkNatSucc,
  ``FramesLocalState.mkNatAdd,
  ``FramesLocalState.natToConstructor,
  ``FramesLocalState.evalNatOffsetLiteralFuel,
  ``FramesLocalState.natOffsetFuel,
  ``FramesLocalState.finishAppResult,
  ``FramesLocalState.strLitListToConstructor,
  ``FramesLocalState.natOffset,
  ``FramesLocalState.natOffsetOrZero,
  ``FramesLocalState.evalNatOffsetLiteral,
  ``FramesLocalState.natOffsetDecompose,
  ``FramesLocalState.natOffsetRebuild,
  ``FramesLocalState.strLitToConstructor,
  ``FramesLocalState.internIntLit,
  ``FramesLocalState.applyIotaArg,
  ``FramesLocalState.applyIotaArgs,
  ``FramesLocalState.isTransientNatLiteralWork,
  ``FramesLocalState.cleanupNatOffsetMajor,
  ``FramesLocalState.projectDecidableFinValMinor,
  ``FramesLocalState.tryReduceFinValDecidableRec,
  ``FramesLocalState.tryReduceProjectionDefinition,
  ``FramesLocalState.bitvecOfNatArgs,
  ``FramesLocalState.charOfNatExpr,
  ``FramesLocalState.tryReduceStringLiteral,
  ``FramesLocalState.tryReduceString,
  ``FramesLocalState.tryProjReduceTail,
  ``FramesLocalState.tryProjPrepare,
  ``FramesLocalState.tryProjReduce,
  ``FramesLocalState.tryProjAppReduce,
  ``FramesLocalState.tryProjAppReduceFinished,
  ``FramesLocalState.finishStructEtaFields,
  ``FramesLocalState.finishStructEtaResult,
  ``FramesLocalState.verifyKSynthCandidate,
  ``FramesLocalState.selectKSynthCandidate,
  ``FramesLocalState.tryReduceNatSuccPeelMiss,
  ``FramesLocalState.tryReduceNatSuccPeelAfterKey,
  ``FramesLocalState.tryReduceNatSuccPeel,
  ``FramesLocalState.tryReduceNatSuccAfterWhnf,
  ``FramesLocalState.isNatSuccIhStep,
  ``FramesLocalState.tryReduceNatSuccLinearRec,
  ``FramesLocalState.tryReduceNatSuccIterStep,
  ``FramesLocalState.tryReduceNatSuccIter,
  ``FramesLocalState.tryReduceNatPredicate,
  ``FramesLocalState.tryReduceNatWithSuccMode,
  ``FramesLocalState.tryReduceNat,
  ``FramesLocalState.tryNatOffsetStuck,
  ``FramesLocalState.buildNatDecidableTrue,
  ``FramesLocalState.buildNatDecidableFalse,
  ``FramesLocalState.tryNormalizeIntDecidable,
  ``FramesLocalState.tryQuotReduce,
  ``FramesLocalState.tryEvalNatValueForPredFuel,
  ``FramesLocalState.tryEvalNatValueForPred,
  ``FramesLocalState.tryReduceBitvecToNat,
  ``FramesLocalState.bitvecToNatExpr,
  ``FramesLocalState.tryReduceBitvecUlt,
  ``FramesLocalState.tryReduceBitvecLtProp,
  ``FramesLocalState.tryReduceBitvec,
  ``openLetWithFV_eq,
  ``PreservesLocalState.openLetWithFV,
  ``FramesLocalState.defEqCtxKey,
  ``FramesLocalState.quickBinder,
  ``FramesLocalState.tryDefEqWhnfLet,
  ``FramesLocalState.tryEtaStructFields,
  ``FramesLocalState.natSuccOf,
  ``FramesLocalState.quickDefEq,
  ``FramesLocalState.finishDefEqLazyDeltaStep,
  ``FramesLocalState.trySameHeadSpineCached,
  ``FramesLocalState.tryDefEqWhnfStructural,
  ``FramesLocalState.isDefEqNatAfterLiteral,
  ``FramesLocalState.isDefEqNat,
  ``FramesLocalState.tryDefEqWhnfNat,
  ``FramesLocalState.tryDefEqOffsetAfterCandidates,
  ``FramesLocalState.tryDefEqOffsetAfterZeroMiss,
  ``FramesLocalState.tryDefEqOffsetAfterLiteral,
  ``FramesLocalState.tryDefEqOffset,
  ``FramesLocalState.tryStringLitExpansion,
  ``FramesLocalState.tryDefEqWhnfStringAfterGuard,
  ``FramesLocalState.tryDefEqWhnfString,
  ``FramesLocalState.compareEtaExpansion,
  ``FramesLocalState.finishLazyDeltaReductionStep
]

private def recursiveStateOperationalRoots : Array Lean.Name := #[
  ``FramesLocalState.unfoldConstValue,
  ``FramesLocalState.tryDeltaUnfold,
  ``FramesLocalState.tryReduceNativeMarker,
  ``FramesLocalState.applyIotaRule,
  ``FramesLocalState.tryApplyIotaCtor,
  ``FramesLocalState.finishStructEtaAfterSort,
  ``FramesLocalState.tryStructEtaAfterInductive,
  ``FramesLocalState.tryStructEtaIota,
  ``FramesLocalState.synthCtorWhenK,
  ``FramesLocalState.tryIotaCtorOrStructEta,
  ``FramesLocalState.tryIotaAfterCleanup,
  ``FramesLocalState.tryIotaAfterMajorWhnf,
  ``FramesLocalState.tryIotaWithFlags,
  ``FramesLocalState.deltaUnfoldOne,
  ``FramesLocalState.tryReduceDecidable,
  ``FramesLocalState.tryReduceNative,
  ``FramesLocalState.whnfCoreWithFlagsStep,
  ``FramesLocalState.whnfCoreWithFlagsUncached,
  ``FramesLocalState.whnfCoreWithFlagsNonLeaf,
  ``FramesLocalState.whnfCoreWithFlags,
  ``FramesLocalState.whnfCore,
  ``FramesLocalState.whnfCoreForDefEq,
  ``FramesLocalState.whnfNoDeltaReducersStep,
  ``FramesLocalState.whnfNoDeltaImplStep,
  ``FramesLocalState.whnfNoDeltaImplUncached,
  ``FramesLocalState.whnfNoDeltaImplNonLeaf,
  ``FramesLocalState.whnfNoDeltaImpl,
  ``FramesLocalState.whnfNoDelta,
  ``FramesLocalState.whnfNoDeltaForDefEq,
  ``FramesLocalState.whnfWithNatSuccModeStep,
  ``FramesLocalState.whnfWithNatSuccModeUncached,
  ``FramesLocalState.whnfWithNatSuccModeNonLeaf,
  ``FramesLocalState.whnfWithNatSuccMode,
  ``FramesLocalState.whnf,
  ``FramesLocalState.etaExpansionBaseLoop,
  ``FramesLocalState.whnfIsBoolTrue,
  ``FramesLocalState.defEqLazyDeltaStepAfterSameHeadMiss,
  ``FramesLocalState.defEqLazyDeltaStepWithLeftDelta,
  ``FramesLocalState.defEqLazyDeltaStepWithRightDelta,
  ``FramesLocalState.defEqLazyDeltaStepWithEqualRank,
  ``FramesLocalState.defEqLazyDeltaStepAfterProjectionMiss,
  ``FramesLocalState.classifyPropTypeUncached,
  ``FramesLocalState.isPropType,
  ``FramesLocalState.tryProofIrrel,
  ``FramesLocalState.isDefEqWhnfAfterUnit,
  ``FramesLocalState.tryDefEqUnit,
  ``FramesLocalState.isDefEqWhnfAfterStructEta,
  ``FramesLocalState.tryEtaExpansionAfterGuard,
  ``FramesLocalState.tryEtaExpansion,
  ``FramesLocalState.tryDefEqWhnfEtaAfterGuard,
  ``FramesLocalState.tryDefEqWhnfEta,
  ``FramesLocalState.normalizeEtaStructSource,
  ``FramesLocalState.etaExpansionBase,
  ``FramesLocalState.tryEtaStructAfterTypes,
  ``FramesLocalState.tryEtaStructAfterConstructor,
  ``FramesLocalState.tryEtaStructAfterNormalization,
  ``FramesLocalState.tryEtaStruct,
  ``FramesLocalState.tryDefEqWhnfStructEta,
  ``FramesLocalState.isDefEqWhnfAfterString,
  ``FramesLocalState.isDefEqWhnfAfterEta,
  ``FramesLocalState.isDefEqWhnfAfterNat,
  ``FramesLocalState.isDefEqWhnfAfterStructural,
  ``FramesLocalState.isDefEqWhnf,
  ``FramesLocalState.etaExpansionBaseAfterValue,
  ``FramesLocalState.etaExpansionBaseAfterProjection,
  ``FramesLocalState.lazyDeltaReductionStepWithLeftDelta,
  ``FramesLocalState.lazyDeltaReductionStepWithRightDelta,
  ``FramesLocalState.lazyDeltaReductionStepAfterSameHeadMiss,
  ``FramesLocalState.lazyDeltaReductionStepWithEqualRank,
  ``FramesLocalState.lazyDeltaReductionStepWithBothDelta,
  ``FramesLocalState.tryUnfoldProjApp,
  ``FramesLocalState.defEqLazyDeltaStepAfterDeltaClassification,
  ``FramesLocalState.defEqLazyDeltaStepAfterAcceleratorMiss,
  ``FramesLocalState.defEqLazyDeltaStepAfterNatMiss,
  ``FramesLocalState.defEqLazyDeltaStepAfterOffsetMiss,
  ``FramesLocalState.defEqLazyDeltaStep,
  ``FramesLocalState.runDefEqLazyDelta,
  ``FramesLocalState.lazyDeltaReductionStepAfterActive,
  ``FramesLocalState.lazyDeltaReductionStepAfterClassification,
  ``FramesLocalState.lazyDeltaReductionStep,
  ``FramesLocalState.lazyDeltaProjReduction,
  ``FramesLocalState.tryStructuralCongruence,
  ``FramesLocalState.isDefEqAfterLazyDeltaStopped,
  ``FramesLocalState.isDefEqInnerAfterProofIrrelevance,
  ``FramesLocalState.isDefEqInnerAfterNoDeltaPass,
  ``FramesLocalState.isDefEqInnerAfterCorePass,
  ``FramesLocalState.isDefEqInnerAfterStringExpansion,
  ``FramesLocalState.isDefEqInnerAfterBoolTrue,
  ``FramesLocalState.isDefEqInnerAfterFirstBoolGuardMiss,
  ``FramesLocalState.isDefEqInnerAfterQuick,
  ``FramesLocalState.isDefEqInner,
  ``FramesLocalState.isDefEqAfterRootCacheMiss,
  ``FramesLocalState.isDefEqAfterDirectCacheMiss,
  ``FramesLocalState.isDefEq,
  ``MethodsLocalState.methodsN,
  ``FramesLocalState.runRec,
  ``TcM.whnf_framesLocalState,
  ``TcM.whnfCore_framesLocalState,
  ``TcM.whnfNoDelta_framesLocalState,
  ``TcM.infer_framesLocalState,
  ``TcM.isDefEq_framesLocalState,
  ``TcM.ensureSort_framesLocalState,
  ``TcM.ensureForall_framesLocalState
]

private def localRestorationRoots : Array Lean.Name := #[
  ``LocalContext.Equiv.truncate, ``LocalContext.truncate_push,
  ``LocalContext.truncate_push_le, ``LocalContext.Extension.restore,
  ``withLctxScope_restores, ``withLctxScope_error_restores,
  ``openLet_extends, ``openBinder_extends,
  ``PreservesLocalExtension.inferKey, ``PreservesLocalExtension.withLctxScope,
  ``inferKey_total
]

private def modelLocalStateRoots : Array Lean.Name := #[
  ``infer_methodsN_framesLocalState, ``isDefEq_methodsN_framesLocalState,
  ``infer_localReading, ``LetInferenceTrace.domainFrame,
  ``LetInferenceTrace.valueFrame, ``LetInferenceTrace.openingFrame,
  ``LetInferenceTrace.domainContext, ``LetInferenceTrace.openingContext,
  ``LetInferenceTrace.restores, ``LetInferenceCheck.keyedValid,
  ``LetInferenceCheck.absent,
  ``ApplicationInferenceTrace.functionFrame, ``ApplicationInferenceTrace.contextPreserved,
  ``ApplicationInferenceTrace.argumentFrame, ``ApplicationInferenceTrace.comparedFrame,
  ``ApplicationWhnfInferenceTrace.functionFrame, ``ApplicationWhnfInferenceTrace.contextPreserved,
  ``ApplicationWhnfInferenceTrace.exposedFrame, ``ApplicationWhnfInferenceTrace.argumentFrame,
  ``ApplicationWhnfInferenceTrace.comparedFrame,
  ``ForallInferenceTrace.domainFrame, ``ForallInferenceTrace.domainValid,
  ``ForallInferenceTrace.contextPreserved, ``ForallInferenceTrace.absent,
  ``LambdaBodyTrace.domainFrame, ``LambdaBodyTrace.domainValid,
  ``LambdaBodyTrace.contextPreserved, ``LambdaBodyTrace.absent,
  ``LambdaInferenceTrace.domainValid, ``LambdaInferenceTrace.contextPreserved,
  ``LambdaInferenceTrace.absent
]

def roots : Array RootAllowance := #[
  { root := ``InterfaceExtends.refl, forbiddenDependencies := forbiddenProduction },
  { root := ``InterfaceExtends.trans, forbiddenDependencies := forbiddenProduction },
  { root := ``DefinitionDependencies.Ordered.closed, standardAxioms := #[``propext, ``Quot.sound],
    forbiddenDependencies := forbiddenProduction },
  { root := ``DefinitionDependencies.Ordered.ranked, standardAxioms := standard,
    forbiddenDependencies := forbiddenProduction },
  { root := ``DefinitionDependencies.Ordered.wellFounded, standardAxioms := standard,
    forbiddenDependencies := forbiddenProduction },
  { root := ``DefinitionDependencies.WalkInvariant.initial, standardAxioms := standard,
    forbiddenDependencies := forbiddenProduction },
  { root := ``DefinitionDependencies.step_certificate, standardAxioms := standard,
    forbiddenDependencies := forbiddenProduction },
  { root := ``DefinitionDependencies.loop_certificate, standardAxioms := standard,
    forbiddenDependencies := forbiddenProduction },
  { root := ``DefinitionDependencies.order_certificate, standardAxioms := standard,
    forbiddenDependencies := forbiddenProduction },
  { root := ``DefinitionDependencies.order_sound, standardAxioms := standard,
    forbiddenDependencies := forbiddenProduction },
  { root := ``DefinitionReferences.definitionRefs_complete, standardAxioms := standard,
    forbiddenDependencies := forbiddenProduction },
  { root := ``readScopedExpr?_referencesIn, standardAxioms := standard,
    forbiddenDependencies := forbiddenProduction },
  { root := ``DefinitionBodyTrace.dependencyOrder, standardAxioms := standard,
    nativeAxioms := #[expressionNative, levelNative], forbiddenDependencies := forbiddenProduction },
  { root := ``DefinitionBodyTrace.referencesIn, standardAxioms := standard,
    nativeAxioms := #[expressionNative, levelNative], forbiddenDependencies := forbiddenProduction },
  { root := ``ConversionRecipe.run_predict, standardAxioms := standard,
    forbiddenDependencies := forbiddenProduction },
  { root := ``Ix.Kernel.ConversionRecipe.run_bind, standardAxioms := #[``propext, ``Quot.sound],
    forbiddenDependencies := forbiddenProduction },
  { root := ``getConst_result_loaded, standardAxioms := #[``propext, ``Quot.sound],
    forbiddenDependencies := forbiddenProduction },
  { root := ``SourceStateInvariant.ofCheckedSource, standardAxioms := standard,
    nativeAxioms := #[expressionNative, levelNative, nameNative],
    forbiddenDependencies := forbiddenProduction },
  { root := ``convertUnivTree_coherent, standardAxioms := standard,
    nativeAxioms := #[levelNative], forbiddenDependencies := forbiddenProduction },
  { root := ``newLazyAnon_intern_coherent, standardAxioms := standard,
    nativeAxioms := #[expressionNative, levelNative, nameNative],
    forbiddenDependencies := forbiddenProduction },
  { root := ``OwnedLazySupport.newLazyAnon, standardAxioms := standard,
    nativeAxioms := #[expressionNative, levelNative, nameNative],
    forbiddenDependencies := forbiddenProduction },
  { root := ``OwnedLazySupport.ofCheckedSource, standardAxioms := standard,
    nativeAxioms := #[expressionNative, levelNative, nameNative],
    forbiddenDependencies := forbiddenProduction },
  { root := ``InferenceStateInvariant.ofCheckedSource, standardAxioms := standard,
    nativeAxioms := #[expressionNative, levelNative, nameNative],
    forbiddenDependencies := forbiddenProduction },
  { root := ``readLevel_eq, standardAxioms := #[``propext] },
  { root := ``readLevel_eval, standardAxioms := #[``propext] },
  { root := ``readLevel_wf, standardAxioms := #[``propext] },
  { root := ``readLevel_eraseMeta, standardAxioms := #[``propext] },
  { root := ``readLevel_mkSucc, standardAxioms := #[``propext, ``Classical.choice],
    nativeAxioms := #[levelNative] },
  { root := ``readLevel_mkIMax, standardAxioms := standard,
    nativeAxioms := #[levelNative] },
  { root := ``univEq_sound, standardAxioms := standard },
  { root := ``univGeq_sound, standardAxioms := standard },
  { root := ``readExpr?_mkSort, standardAxioms := standard,
    nativeAxioms := #[expressionNative] },
  { root := ``readExpr?_eraseMeta, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``readScopedExpr?_lam_parts },
  { root := ``readScopedExpr?_app_parts },
  { root := ``readScopedExpr?_all_parts },
  { root := ``readScopedExpr?_let_parts, forbiddenDependencies := forbiddenProduction },
  { root := ``Theory.Model.AExpr.erase_surjective, forbiddenDependencies := forbiddenProduction },
  { root := ``Theory.VExpr.ClosedN.liftN, standardAxioms := #[``propext, ``Quot.sound],
    forbiddenDependencies := forbiddenProduction },
  { root := ``Theory.VExpr.ClosedN.inst, standardAxioms := #[``propext, ``Quot.sound],
    forbiddenDependencies := forbiddenProduction },
  { root := ``Theory.VExpr.liftN_inst_zero, standardAxioms := #[``propext, ``Quot.sound],
    forbiddenDependencies := forbiddenProduction },
  { root := ``Theory.VExpr.inst_inst_zero, standardAxioms := #[``propext, ``Quot.sound],
    forbiddenDependencies := forbiddenProduction },
  { root := ``Theory.VExpr.instRevAt_inst_zero, standardAxioms := #[``propext, ``Quot.sound],
    forbiddenDependencies := forbiddenProduction },
  { root := ``readScopedExpr?_mkLet, standardAxioms := #[``propext, ``Classical.choice],
    nativeAxioms := #[expressionNative], forbiddenDependencies := forbiddenProduction },
  { root := ``cheapBetaPlan?_head_lambda, standardAxioms := standard,
    nativeAxioms := #[expressionNative], forbiddenDependencies := forbiddenProduction },
  { root := ``openLet_eq, standardAxioms := standard,
    nativeAxioms := #[expressionNative], forbiddenDependencies := forbiddenProduction },
  { root := ``openLet_inference_state, standardAxioms := standard,
    nativeAxioms := #[expressionNative], forbiddenDependencies := forbiddenProduction },
  { root := ``openLet_sound, standardAxioms := standard,
    nativeAxioms := #[expressionNative], forbiddenDependencies := forbiddenProduction },
  { root := ``UncachedInference.keyedLocalState, standardAxioms := standard,
    nativeAxioms := #[expressionNative], forbiddenDependencies := forbiddenProduction },
  { root := ``beq_readExpr?, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``internExpr_readExpr?, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``ModelTyping.sort, standardAxioms := standard,
    nativeAxioms := #[expressionNative, levelNative] },
  { root := ``ModelTyping.of_beq, standardAxioms := standard },
  { root := ``ModelTyping.internExpr, standardAxioms := standard },
  { root := ``ModelTyping.internType, standardAxioms := standard },
  { root := ``ModelTyping.no_false, standardAxioms := standard },
  { root := ``sort_conversion, standardAxioms := standard },
  { root := ``inferUncached_sort_sound, standardAxioms := standard,
    nativeAxioms := #[expressionNative, levelNative] },
  { root := ``Theory.VExpr.LevelWF.liftN, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.VExpr.LevelWF.inst, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.VExpr.LevelEquivalent.refl, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.VExpr.LevelEquivalent.liftN, standardAxioms := #[``propext] },
  { root := ``Theory.VExpr.LevelEquivalent.inst, standardAxioms := #[``propext] },
  { root := ``Theory.VExpr.instL_liftN, standardAxioms := #[``propext] },
  { root := ``Theory.VExpr.instL_inst, standardAxioms := #[``propext] },
  { root := ``Theory.VExpr.LevelWF.instL_nil, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.eq_of_erase_annotations, standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.Scope.instL, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.references_instL, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Theory.Model.AExpr.reannotate_levels, standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.LevelEquivalent.annotations, standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.LevelEquivalent.erase, standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.LevelEquivalent.scope, standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.LevelEquivalent.references, standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.LevelEquivalent.of_erase_annotations,
    standardAxioms := #[``propext] },
  { root := ``Theory.Model.AExpr.LevelEquivalent.interp, standardAxioms := standard },
  { root := ``Theory.Model.AExpr.LevelEquivalent.wellDenoted, standardAxioms := standard },
  { root := ``Theory.Model.AExpr.LevelEquivalent.typing, standardAxioms := standard },
  { root := ``Theory.Model.TypingClaim.checking, standardAxioms := standard },
  { root := ``Theory.Model.TypingClaim.appChecking, standardAxioms := standard },
  { root := ``Theory.Model.CheckingClaim.typing, standardAxioms := standard },
  { root := ``Theory.Model.CheckingClaim.typingSort, standardAxioms := standard },
  { root := ``Theory.Model.CheckingClaim.lam, standardAxioms := standard },
  { root := ``ConditionsScoped, standardAxioms := #[``propext],
    forbiddenDependencies := forbiddenProduction },
  { root := ``ConditionsScoped.scope, standardAxioms := #[``propext],
    forbiddenDependencies := forbiddenProduction }
] ++ sourceCacheInitialRoots.map (fun root => {
  root, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative, nameNative],
  forbiddenDependencies := forbiddenProduction
}) ++ conversionUniverseRoots.map (fun root => {
  root, standardAxioms := standard, nativeAxioms := #[levelNative],
  forbiddenDependencies := forbiddenProduction
}) ++ (scopedRoots ++ cacheFrameRoots).map (fun root => {
  root, standardAxioms := #[``propext, ``Quot.sound], forbiddenDependencies := forbiddenProduction
}) ++ (contextRoots ++ cacheMapRoots ++ sourceOwnershipRoots ++ formationRoots).map (fun root => {
  root, standardAxioms := standard, forbiddenDependencies := forbiddenProduction
}) ++ (binderWalkerRoots ++ cacheKeyRoots).map (fun root => {
  root, standardAxioms := standard, nativeAxioms := #[expressionNative],
  forbiddenDependencies := forbiddenProduction
}) ++ (atomicRoots ++ letRoots ++ instantiationRoots ++ recursiveCacheRoots ++ synthesisCacheRoots ++ cacheHistoryRoots ++ lazyCacheRoots ++
    ownedLoaderRoots ++ recursiveStateRoots ++ sourceAgreementRoots ++ sourceCacheRoots).map (fun root => {
  root, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative],
  forbiddenDependencies := forbiddenProduction
}) ++ productionRoots.map (fun root => {
  root, standardAxioms := standard, nativeAxioms := productionNative,
  forbiddenDependencies := forbiddenProduction
}) ++ (betaRoots ++ typeOriginRoots ++ substitutedOriginRoots ++ exposedOriginRoots ++
    repeatedBetaRoots ++ betaTraceRoots ++ hereditaryBetaRoots ++ piExposureRoots ++ cacheTransportRoots).map (fun allowance => {
    allowance with forbiddenDependencies := allowance.forbiddenDependencies ++ forbiddenProduction })
  ++ (#[``BetaStepSource.selected, ``BetaStepSource.selected_app] ++ letWhnfSyntaxRoots ++ headWhnfSyntaxRoots).map (fun root => {
    root, standardAxioms := #[``propext],
    forbiddenDependencies := forbiddenProduction ++ #[``HereditaryTyping] })
  ++ #[``WhnfCachePartition, ``WhnfCachePartition.ofFlags].map (fun root => {
    root, forbiddenDependencies := forbiddenProduction ++ #[``HereditaryTyping] })
  ++ (mixedCacheFrameRoots ++ headWhnfFrameRoots ++ whnfHistoryFrameRoots ++ inferenceHistoryFrameRoots ++
      #[``betaWhnfCharge_success]).map (fun root => {
    root, standardAxioms := #[``propext, ``Quot.sound],
    forbiddenDependencies := forbiddenProduction ++ #[``HereditaryTyping] })
  ++ (mixedCacheKeyRoots ++ betaSourceExprRoots ++ letWhnfExprRoots ++ headWhnfExprRoots ++
      betaReannotationExprRoots ++ whnfHistoryExprRoots ++ inferenceHistoryExprRoots).map (fun root => {
    root, standardAxioms := standard, nativeAxioms := #[expressionNative],
    forbiddenDependencies := forbiddenProduction ++ #[``HereditaryTyping] })
  ++ #[``SynthesisInference.beta_core_execution_sound, ``SynthesisInference.beta_noDelta_execution_sound,
      ``SynthesisInference.beta_public_execution_sound,
      ``SynthesisInference.beta_whnf_of_success, ``SynthesisInference.beta_core_of_success,
      ``SynthesisInference.beta_noDelta_of_success, ``SynthesisInference.beta_public_of_success,
      ``SynthesisInference.beta_public_of_history].map (fun root => {
    root, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative],
    forbiddenDependencies := forbiddenProduction })
  ++ (recursiveLetShapeRoots ++ sortExposureRoots ++ mixedCacheExecutionRoots ++ betaSourceExecutionRoots ++
      letWhnfExecutionRoots ++ headWhnfExecutionRoots ++ betaReannotationExecutionRoots ++ whnfHistoryExecutionRoots ++
      inferenceHistoryExecutionRoots).map (fun root => {
    root, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative],
    forbiddenDependencies := forbiddenProduction ++ #[``HereditaryTyping] })
  ++ (localScopeFrameRoots ++ localStateFrameRoots ++ recursiveStateFrameRoots ++ ingressFrameRoots ++
      #[``LocalContextReading.congr, ``FramesLocalState.ok, ``FramesLocalState.error,
        ``IngressM.FramesState.runIntern, ``LocalStateInvariant.freshReading]).map (fun root => {
    root, standardAxioms := #[``propext, ``Quot.sound], forbiddenDependencies := forbiddenProduction })
  ++ (localStateMapRoots ++ recursiveStateMapRoots ++ ingressMapRoots ++
      #[``LocalContext.Equiv.push]).map (fun root => {
    root, standardAxioms := standard, forbiddenDependencies := forbiddenProduction })
  ++ (localStateWalkerRoots ++ recursiveStateExprRoots ++ localRestorationRoots).map (fun root => {
    root, standardAxioms := standard, nativeAxioms := #[expressionNative],
    forbiddenDependencies := forbiddenProduction })
  ++ ingressLevelRoots.map (fun root => {
    root, standardAxioms := standard, nativeAxioms := #[levelNative],
    forbiddenDependencies := forbiddenProduction })
  ++ (localStateOperationalRoots ++ recursiveStateOperationalRoots ++ ingressOperationalRoots ++
      modelLocalStateRoots ++ #[``infer_localContext]).map (fun root => {
    root, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative],
    forbiddenDependencies := forbiddenProduction })
  ++ #[
    { root := ``BetaCacheHistory.initial, standardAxioms := standard,
      nativeAxioms := #[expressionNative, levelNative, nameNative],
      forbiddenDependencies := forbiddenProduction ++ #[``HereditaryTyping] },
    { root := ``BetaCoreCache.published, standardAxioms := standard,
      forbiddenDependencies := forbiddenProduction ++ #[``HereditaryTyping] },
    { root := ``LocalStateInvariant.newLazyAnon, standardAxioms := standard,
      nativeAxioms := #[expressionNative, levelNative, nameNative],
      forbiddenDependencies := forbiddenProduction },
    { root := ``localIndex?_of_mem, standardAxioms := #[``propext],
      forbiddenDependencies := forbiddenProduction }
  ]
  ++ #[{ root := ``extend_atomic_definition, standardAxioms := standard }]

run_cmd Kernel.Verify.Audit.check roots

end Ix.Kernel.Consistency.Audit
