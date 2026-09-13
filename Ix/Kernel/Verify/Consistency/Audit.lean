/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Infer
import Ix.Kernel.Verify.Consistency.Constant
import Ix.Kernel.Verify.Consistency.Environment
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
  ``FVarInferenceSupport.output, ``FVarInferenceSupport.sound,
  ``InferenceCacheHit.run, ``infer_sort_cached_sound,
  ``infer_sort_cache_agreement, ``infer_sort_cache_frame, ``BinderInference.sortOfAgreement,
  ``ForallInferenceTrace.output, ``LambdaInferenceTrace.output, ``BinderInference.sound,
  ``inferUncached_monomorphic_const_scoped, ``ApplicationInferenceTrace.output,
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
  ``inferKey_closed, ``InferenceCacheHit.key_closed, ``observeInferenceCache,
  ``InferenceCacheAgreement.selected, ``InferenceCacheHit.transport,
  ``PreservesInferenceCache.inferKey, ``PreservesInferenceCache.openBinder,
  ``withLctxScope_eq, ``PreservesInferenceCache.withLctxScope
]

private def productionRoots : Array Lean.Name := #[
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
  ``LocalContextReading.empty
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
  ``readScopedExpr?_liftSpec, ``readScopedExpr?_substSpec, ``subst_readScopedExpr?
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
  { root := ``Theory.Model.CheckingClaim.lam, standardAxioms := standard }
] ++ (scopedRoots ++ cacheFrameRoots).map (fun root => {
  root, standardAxioms := #[``propext, ``Quot.sound], forbiddenDependencies := forbiddenProduction
}) ++ (contextRoots ++ cacheMapRoots).map (fun root => {
  root, standardAxioms := standard, forbiddenDependencies := forbiddenProduction
}) ++ (binderWalkerRoots ++ cacheKeyRoots).map (fun root => {
  root, standardAxioms := standard, nativeAxioms := #[expressionNative],
  forbiddenDependencies := forbiddenProduction
}) ++ (atomicRoots ++ instantiationRoots).map (fun root => {
  root, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative],
  forbiddenDependencies := forbiddenProduction
}) ++ productionRoots.map (fun root => {
  root, standardAxioms := standard, nativeAxioms := productionNative,
  forbiddenDependencies := forbiddenProduction
}) ++ #[{ root := ``extend_atomic_definition, standardAxioms := standard }]

run_cmd Kernel.Verify.Audit.check roots

end Ix.Kernel.Consistency.Audit
