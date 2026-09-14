/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Infer
import Ix.Kernel.Verify.Consistency.Constant
import Ix.Kernel.Verify.Consistency.Environment
import Ix.Kernel.Verify.Consistency.RecursiveCache
import Ix.Kernel.Verify.Consistency.CacheLifecycle
import Ix.Kernel.Verify.Consistency.StringExpansion
import Ix.Kernel.Verify.Consistency.DefinitionOrder
import Ix.Kernel.Verify.Consistency.LocalOpening
import Ix.Kernel.Verify.Consistency.LocalSubstitution
import Ix.Kernel.Verify.Consistency.LetInference
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

/-- The public driver reaches these additional generated output-length
proofs through the full production method table, including inactive branches.
No new native proof is introduced by the fragment verification. -/
private def productionNative : Array Lean.Name := #[
  expressionNative, levelNative,
  nativeAxiom `Ix.Environment `Ix.Name.mkStr._native.native_decide.ax_1,
  nativeAxiom `Ix.Kernel.Inductive `Ix.Kernel.RecM.canonicalAuxOrder._native.native_decide.ax_9
]

private def atomicRoots : Array Lean.Name := #[
  ``infer_uncached_success_state, ``infer_uncached_success, ``AtomicInferenceSupport.typing,
  ``AtomicInferenceSupport.reads, ``AtomicInferenceSupport.output,
  ``AtomicInferenceSupport.scopeAndReferences, ``AtomicInference.sound,
  ``inferUncached_fvar_sound, ``infer_fvar_sound,
  ``inferUncached_fvar_local_sound, ``whnfCoreWithFlagsStep_fvar_local_sound,
  ``FVarInferenceSupport.output, ``FVarInferenceSupport.sound,
  ``InferenceCacheHit.run, ``infer_sort_cached_sound,
  ``infer_sort_cache_agreement, ``infer_sort_cache_frame, ``BinderInference.sortOfAgreement,
  ``ForallInferenceTrace.output, ``LambdaInferenceTrace.output, ``BinderInference.sound,
  ``inferUncached_monomorphic_const_scoped, ``ApplicationInferenceTrace.output,
  ``LetInferenceTrace.of_success, ``LetInferenceTrace.beforeBeta_typing,
  ``BinderInference.soundWithSynthesis, ``BinderInference.synthesis,
  ``DefinitionBodySupport.sound
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
  ``InferenceCacheFrame.refl, ``InferenceCacheFrame.trans, ``InferenceCacheAgreement.frame,
  ``cacheInferResult_eq, ``PreservesInferenceCache.pure, ``PreservesInferenceCache.bind,
  ``PreservesInferenceCache.runIntern, ``InferenceCacheFrame.localContext,
  ``InferenceCacheAgreement.policy, ``withInferOnly_eq,
  ``PreservesInferenceCache.withInferOnly, ``getConst_loaded
]

private def cacheMapRoots : Array Lean.Name := #[
  ``InferenceCacheAgreement.write, ``PreservesInferenceCache.write_other,
  ``InferenceCacheAgreement.clearReductionCaches
]

private def cacheKeyRoots : Array Lean.Name := #[
  ``inferKey_closed, ``inferKey_policy, ``InferenceCacheHit.key_closed, ``observeInferenceCache,
  ``InferenceCacheAgreement.selected, ``InferenceCacheHit.transport,
  ``PreservesInferenceCache.inferKey, ``PreservesInferenceCache.openBinder,
  ``withLctxScope_eq, ``PreservesInferenceCache.withLctxScope
]

private def cacheInvariantFrameRoots : Array Lean.Name := #[
  ``InferenceCacheInvariant.frame, ``InferenceCacheInvariant.mono,
  ``InferenceCacheInvariant.runIntern, ``InferenceCacheInvariant.restoreCheckCachesOnError,
  ``InferenceCacheInvariant.isolateCheckErrors, ``PreservesInferenceInvariant.pure,
  ``PreservesInferenceInvariant.bind, ``PreservesInferenceInvariant.runIntern,
  ``PreservesInferenceInvariant.withInferOnly
]

private def cacheInvariantMapRoots : Array Lean.Name := #[
  ``InferenceCacheInvariant.empty, ``InferenceCacheInvariant.write,
  ``InferenceCacheInvariant.clearReductionCaches, ``InferenceCacheInvariant.reset,
  ``InferenceCacheInvariant.finishAnonCheckItem
]

private def cacheInvariantKeyRoots : Array Lean.Name := #[
  ``InferenceCacheInvariant.inferKey, ``InferenceCacheInvariant.selected,
  ``InferenceCacheInvariant.openBinder, ``PreservesInferenceInvariant.withLctxScope,
  ``inferKey_total
]

private def cacheInvariantDriverRoots : Array Lean.Name := #[
  ``InferenceCacheInvariant.checkConst_error, ``InferenceCacheInvariant.runAnonCheckItem,
  ``InferenceCacheInvariant.runAnonCheckList,
  ``InferenceCacheInvariant.initialized_runAnonCheckList
]

private def recursiveCacheRoots : Array Lean.Name := #[
  ``ApplicationInferenceTrace.output_state, ``ForallInferenceTrace.output_state,
  ``LambdaInferenceTrace.output_state, ``isDefEq_hash_state, ``isDefEq_hash_frame,
  ``InferenceCacheTrace.writes, ``InferenceCacheTrace.sortOfKey,
  ``InferenceCacheTrace.fvarOfKey, ``InferenceCacheTrace.constOfKey,
  ``InferenceCacheTrace.frame, ``InferenceCacheTrace.agreement,
  ``InferenceCacheHit.afterInference, ``CachedConstantInferenceSupport.afterInference,
  ``CachedConstantInferenceSupport.sound_after_inference, ``BinderInference.sortAfterInference
]

private def productionRoots : Array Lean.Name := #[
  ``StandalonePrefix.member_success, ``definition_body_trace,
  ``DefinitionOrder.member_no_self, ``DefinitionOrder.block_guard,
  ``DefinitionOrder.block_rank, ``DefinitionOrder.block_wellFounded,
  ``DefinitionOrder.block_no_cycle,
  ``AtomicDefinitionRun.sound, ``AtomicDefinitionRun.no_self_alias,
  ``WorkPosition.check_success, ``AtomicDefinitionPlan.extends,
  ``AtomicDefinitionPlan.sound, ``AtomicDefinitionPlan.represents,
  ``checkEnvAnon_atomic_preserves_model, ``checkEnvAnon_atomic_represents_source,
  ``checkEnvAnon_atomic_no_false
]

private def localIndexRoots : Array Lean.Name := #[
  ``localIndex?_mem, ``localIndex?_getElem, ``localIndex?_fresh
]

private def scopedRoots : Array Lean.Name := #[
  ``readScopedExpr?_closed, ``readScopedExpr?_weaken_closed, ``readScopedExpr?_eraseMeta,
  ``beq_readScopedExpr?, ``internExpr_readScopedExpr?, ``readScopedExpr?_push,
  ``LocalContextReading.empty
]

private def stringListRoots : Array Lean.Name := #[
  ``StringPrimitiveRefs.listExpr_liftN, ``StringPrimitiveRefs.listExpr_inst,
  ``StringPrimitiveRefs.listExpr_instL, ``StringPrimitiveRefs.listExpr_closed
]

/-- `String.toList` carries standard-library choice and quotient dependencies.
The full dependency audit includes this executable definition in reader types. -/
private def stringRoots : Array Lean.Name := #[
  ``StringPrimitiveRefs.expr_liftN, ``StringPrimitiveRefs.expr_inst,
  ``StringPrimitiveRefs.expr_instL, ``StringPrimitiveRefs.expr_closed,
  ``StringPrimitiveRefs.expr_levelWF, ``readString?_parts, ``readString?_liftN,
  ``readString?_inst, ``readString?_instL, ``readString?_closed, ``readString?_levelWF,
  ``StringPrimitiveRefs.resolve?_fields
]

private def internFrameRoots : Array Lean.Name := #[
  ``ExpressionInternInvariant.mono, ``ExpressionInternInvariant.result_eq, ``intern_eq
]

private def internMapRoots : Array Lean.Name := #[
  ``ExpressionInternInvariant.empty, ``ExpressionInternInvariant.internExpr,
  ``ExpressionInternInvariant.internUniv, ``ExpressionInternInvariant.internExprList
]

private def stringExpansionRoots : Array Lean.Name := #[
  ``StringExpansion.list_run, ``StringExpansion.candidates_length, ``StringExpansion.run,
  ``StringExpansion.run_finite, ``StringExpansion.listResult_read
]

private def letSubstitutionRoots : Array Lean.Name := #[
  ``Theory.VExpr.liftN_combine, ``Theory.VExpr.liftN_comm,
  ``Theory.VExpr.liftN_instVar_lo, ``Theory.VExpr.liftN_inst_lo,
  ``Theory.VExpr.liftN_instVar_hi, ``Theory.VExpr.liftN_inst_hi_at,
  ``Theory.VExpr.liftN_inst_hi, ``Theory.VExpr.inst_liftN,
  ``Theory.VExpr.inst_instVar_hi, ``Theory.VExpr.inst_inst_hi,
  ``Theory.VExpr.inst0_inst_hi
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
  ``LocalContextValues.empty, ``openLet_eq,
  ``LocalContextValues.openLet, ``LocalContextValues.openBinder,
  ``readLocalExpr?_instantiateLetSpec, ``readLocalExpr?_instantiateBinderSpec,
  ``openLet_local_sound, ``openBinder_local_sound,
  ``readLocalExpr?_liftSpec, ``readLocalExpr?_substSpec, ``subst_readLocalExpr?,
  ``readLocalExpr?_abstractFVarsSpec, ``abstractFVars_readLocalExpr?,
  ``KExpr.abstractFVarsSpec_size, ``closeLetType_readLocalExpr?
]

private def localValueRoots : Array Lean.Name := #[
  ``Theory.Model.Context.Valid.pop, ``Theory.Model.TypingClaim.weaken,
  ``readLocalExpr?_scoped, ``readLocalExpr?_eraseMeta, ``internExpr_readLocalExpr?,
  ``readLocalExpr?_extend, ``readLocalExpr?_lift, ``localContext_find?_push_ne_eq,
  ``LocalContextValues.index_none, ``LocalContextValues.pushLet,
  ``LocalContextValues.pushBinder, ``LocalModelTyping.closed,
  ``readLocalExpr?_readable, ``readLocalExpr?_instantiateLocal,
  ``readLocalExpr?_letResidual
]

/-- Production roots must not acquire a checker-soundness assumption
or invoke the independent certificate validator to establish acceptance. -/
private def forbiddenProduction : Array Lean.Name := #[
  `Ix.Kernel.CheckSuccessSound,
  `Ix.Kernel.SupportedCheckFragment,
  `Ix.Theory.Certified.checkProofCertified,
  `Ix.Certified.acceptsSerializedStore
]

def roots : Array RootAllowance := #[
  { root := ``LocalValues.Below.empty, standardAxioms := #[],
    forbiddenDependencies := forbiddenProduction },
  { root := ``LocalValues.Below.absent, standardAxioms := #[],
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
  { root := ``readExpr?_eraseMeta, standardAxioms := standard },
  { root := ``readScopedExpr?_lam_parts, standardAxioms := standard },
  { root := ``readScopedExpr?_app_parts, standardAxioms := standard },
  { root := ``readScopedExpr?_all_parts, standardAxioms := standard },
  { root := ``readScopedExpr?_let_parts, standardAxioms := standard },
  { root := ``readScopedExpr?_mkLet, standardAxioms := standard,
    nativeAxioms := #[expressionNative] },
  { root := ``Theory.liftVar_lt },
  { root := ``Theory.liftVar_le },
  { root := ``Theory.VExpr.liftN_zero, standardAxioms := #[``propext] },
  { root := ``beq_readExpr?, standardAxioms := standard },
  { root := ``internExpr_readExpr?, standardAxioms := standard },
  { root := ``StringPrimitiveRefs.listExpr_levelWF, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``StringExpansion.listCandidates_length,
    standardAxioms := #[``propext, ``Classical.choice], nativeAxioms := #[expressionNative],
    forbiddenDependencies := forbiddenProduction },
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
  { root := ``Theory.Model.CheckingClaim.lam, standardAxioms := standard }
] ++ (stringListRoots ++ #[``LocalValues.pushLet_extends,
    ``LocalValues.pushBinder_lifts, ``LocalValues.Below.pushLet]).map (fun root => {
  root, standardAxioms := #[``propext], forbiddenDependencies := forbiddenProduction
}) ++ (localIndexRoots ++ cacheFrameRoots ++ letSubstitutionRoots ++ cacheInvariantFrameRoots ++
    internFrameRoots ++ #[``DefinitionOrder.ready_independent,
      ``DefinitionOrder.order?_sound, ``DefinitionOrder.member_of_read,
      ``LocalValues.Below.pushBinder]).map (fun root => {
  root, standardAxioms := #[``propext, ``Quot.sound], forbiddenDependencies := forbiddenProduction
}) ++ (contextRoots ++ localValueRoots ++ cacheMapRoots ++ cacheInvariantMapRoots ++ scopedRoots ++ stringRoots ++
    internMapRoots ++ #[``DefinitionOrder.order?_rank,
      ``DefinitionOrder.acyclic_rank]).map (fun root => {
  root, standardAxioms := standard, forbiddenDependencies := forbiddenProduction
}) ++ (binderWalkerRoots ++ cacheKeyRoots ++ cacheInvariantKeyRoots ++ stringExpansionRoots).map (fun root => {
  root, standardAxioms := standard, nativeAxioms := #[expressionNative],
  forbiddenDependencies := forbiddenProduction
}) ++ (atomicRoots ++ instantiationRoots ++ recursiveCacheRoots ++
    #[``InferenceCacheInvariant.infer]).map (fun root => {
  root, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative],
  forbiddenDependencies := forbiddenProduction
}) ++ (productionRoots ++ cacheInvariantDriverRoots).map (fun root => {
  root, standardAxioms := standard, nativeAxioms := productionNative,
  forbiddenDependencies := forbiddenProduction
}) ++ #[``InferenceCacheInvariant.newLazyAnon,
    ``InferenceCacheInvariant.initialAnonCheckLoopState].map (fun root => {
  root, standardAxioms := standard,
  nativeAxioms := #[expressionNative, levelNative,
    nativeAxiom `Ix.Environment `Ix.Name.mkStr._native.native_decide.ax_1],
  forbiddenDependencies := forbiddenProduction
}) ++ #[``StringExpansion.result_read, ``StringExpansion.read_of_run].map (fun root => {
  root, standardAxioms := standard,
  nativeAxioms := #[expressionNative,
    nativeAxiom `Ix.Environment `Ix.Name.mkStr._native.native_decide.ax_1],
  forbiddenDependencies := forbiddenProduction
}) ++ #[{ root := ``extend_atomic_definition, standardAxioms := standard }]

run_cmd Kernel.Verify.Audit.check roots

end Ix.Kernel.Consistency.Audit
