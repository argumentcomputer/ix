/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Infer
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
  ``infer_uncached_success, ``AtomicInferenceSupport.typing,
  ``AtomicInferenceSupport.reads, ``AtomicInferenceSupport.output,
  ``AtomicInferenceSupport.scopeAndReferences, ``AtomicInference.sound
]

private def productionRoots : Array Lean.Name := #[
  ``StandalonePrefix.member_success, ``definition_body_trace,
  ``AtomicDefinitionRun.sound, ``AtomicDefinitionRun.no_self_alias,
  ``WorkPosition.check_success, ``AtomicDefinitionPlan.extends,
  ``AtomicDefinitionPlan.sound, ``AtomicDefinitionPlan.represents,
  ``checkEnvAnon_atomic_preserves_model, ``checkEnvAnon_atomic_represents_source,
  ``checkEnvAnon_atomic_no_false
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
  { root := ``univEq_sound, standardAxioms := standard },
  { root := ``univGeq_sound, standardAxioms := standard },
  { root := ``readExpr?_mkSort, standardAxioms := standard,
    nativeAxioms := #[expressionNative] },
  { root := ``readExpr?_eraseMeta, standardAxioms := #[``propext, ``Quot.sound] },
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
    nativeAxioms := #[expressionNative, levelNative] }
] ++ atomicRoots.map (fun root => {
  root, standardAxioms := standard, nativeAxioms := #[expressionNative, levelNative],
  forbiddenDependencies := forbiddenProduction
}) ++ productionRoots.map (fun root => {
  root, standardAxioms := standard, nativeAxioms := productionNative,
  forbiddenDependencies := forbiddenProduction
}) ++ #[{ root := ``extend_atomic_definition, standardAxioms := standard }]

run_cmd Kernel.Verify.Audit.check roots

end Ix.Kernel.Consistency.Audit
