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
  ``AtomicDefinitionRun.ofHash
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
  ``Theory.Model.ConversionClaim.inst
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
  ``SourceCacheHistory.invariant, ``infer_const_history_sound
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
}) ++ (atomicRoots ++ instantiationRoots ++ recursiveCacheRoots ++ lazyCacheRoots ++
    ownedLoaderRoots ++ recursiveStateRoots ++ sourceAgreementRoots ++ sourceCacheRoots).map (fun root => {
  root, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative],
  forbiddenDependencies := forbiddenProduction
}) ++ productionRoots.map (fun root => {
  root, standardAxioms := standard, nativeAxioms := productionNative,
  forbiddenDependencies := forbiddenProduction
}) ++ (betaRoots ++ typeOriginRoots).map (fun allowance => {
    allowance with forbiddenDependencies := forbiddenProduction })
  ++ #[{ root := ``extend_atomic_definition, standardAxioms := standard }]

run_cmd Kernel.Verify.Audit.check roots

end Ix.Kernel.Consistency.Audit
