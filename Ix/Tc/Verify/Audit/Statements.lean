import Ix.Tc.Verify.Audit.Basic
import Ix.Tc.Verify.Audit.Completed
import Ix.Tc.Verify.Statements

/-!
# Trust manifest for the public checker statement frontier

All seven roots are concrete results over the bounded production recursion
schedule and checker.  The three recursive-method adapters have no `sorryAx`
dependency; the standalone and atomic-block checker roots retain only the two
named Lean4Lean typing lemmas through their singleton-definition branch.  The
E3-S root executes the exact Boolean serial workset and composes those same
transparent K3/E0 resources with E1 and certificate-backed E2 evidence. This
module permits no local statement placeholder and forbids both the legacy
whole-environment route and the unusable all-depth recursive closure.
-/

namespace Ix.Tc.Verify.Audit.Statements

open Ix.Tc.Verify.Audit

private def standard : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def forallEInv : Lean.Name :=
  ``Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified
private def sortInv : Lean.Name := ``Lean4Lean.VEnv.IsDefEqU.sort_inv
private def checkerDebt : Array Lean.Name := #[forallEInv, sortInv]

private def legacyWholeEnv : Array Lean.Name := #[
  ``Ix.Tc.AddKInduct,
  ``Ix.Tc.AddKInduct.to_addInduct,
  ``Ix.Tc.TrKEnv',
  ``Ix.Tc.TrKEnv
]

private def legacyAllDepthKnot : Array Lean.Name := #[
  ``Ix.Tc.RecursiveMethodClosureContext,
  ``Ix.Tc.RecursiveMethodClosureContext.closedAt,
  ``Ix.Tc.RecursiveMethodClosureContext.methodsN,
  ``Ix.Tc.RecursiveMethodClosureContext.fullInferenceContext,
  ``Ix.Tc.RecursiveMethodClosureContext.next_fullInferenceWFAt,
  ``Ix.Tc.RecursiveMethodClosureContext.methodsN_fullInferenceWFAt,
  ``Ix.Tc.RecursiveMethodClosureContext.publicInfer_full_wf
]

private def forbidden : Array Lean.Name :=
  legacyWholeEnv ++ legacyAllDepthKnot

/- K2S public recursive roots may retain the legacy declarations in the
library, but must not manufacture a global suffix model or pass through the
old proposition-classifier/run-context path. -/
private def legacyGlobalSuffix : Array Lean.Name := #[
  ``Ix.Tc.KernelSuffixModel,
  ``Ix.Tc.ScopedKernelSuffixModel.toKernelSuffixModel,
  ``Ix.Tc.PropositionClassifierContext,
  ``Ix.Tc.RecursiveMethodRunContext,
  ``Ix.Tc.TcM.whnf.wf_legacy,
  ``Ix.Tc.TcM.infer.wf_legacy,
  ``Ix.Tc.TcM.isDefEq.wf_legacy,
  ``Ix.Tc.TcM.checkConst.wf_legacy
]

private def scopedForbidden : Array Lean.Name :=
  forbidden ++ legacyGlobalSuffix

private def runNative : Array Lean.Name := #[
  nativeAxiom `Blake3
    `Blake3.HasherOps.hash._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Expr
    `Ix.Tc.KExpr.mkVar._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Level
    `Ix.Tc.KUniv.mkSucc._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Monad
    `Ix.Tc.TcM.ctxAddrForLbrUncached._native.native_decide.ax_3
]

private def checkConstNative : Array Lean.Name := #[
  nativeAxiom `Blake3
    `Blake3.HasherOps.hash._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Expr
    `Ix.Tc.KExpr.mkVar._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Level
    `Ix.Tc.KUniv.mkSucc._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Monad
    `Ix.Tc.TcM.ctxAddrForLbrUncached._native.native_decide.ax_3,
  nativeAxiom `Ix.Environment
    `Ix.Name.mkStr._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Inductive
    `Ix.Tc.RecM.canonicalAuxOrder._native.native_decide.ax_9
]

private def roots : Array RootAllowance := #[
  { root := ``Ix.Tc.TcM.whnf.wf,
    standardAxioms := standard, nativeAxioms := runNative,
    forbiddenDependencies := scopedForbidden },
  { root := ``Ix.Tc.TcM.infer.wf,
    standardAxioms := standard, nativeAxioms := runNative,
    forbiddenDependencies := scopedForbidden },
  { root := ``Ix.Tc.TcM.isDefEq.wf,
    standardAxioms := standard, nativeAxioms := runNative,
    forbiddenDependencies := scopedForbidden },
  { root := ``Ix.Tc.TcM.checkConst.wf,
    standardAxioms := standard,
    nativeAxioms := checkConstNative,
    sorryOrigins := checkerDebt,
    forbiddenDependencies := scopedForbidden },
  { root := ``Ix.Tc.TcM.checkConst.blockDisposition,
    standardAxioms := standard,
    nativeAxioms := checkConstNative,
    sorryOrigins := checkerDebt,
    forbiddenDependencies := scopedForbidden },
  { root := ``Ix.Tc.BooleanEnumerationFixture.subjectWF,
    standardAxioms := standard,
    nativeAxioms := Ix.Tc.Verify.Audit.Completed.booleanDriverNative,
    sorryOrigins := checkerDebt,
    forbiddenDependencies := scopedForbidden },
  { root := ``Ix.Tc.BooleanSerialized.subjectWF,
    standardAxioms := standard,
    nativeAxioms := Ix.Tc.Verify.Audit.Completed.serializedBooleanNative,
    sorryOrigins := checkerDebt,
    forbiddenDependencies := scopedForbidden }
]

run_cmd Ix.Tc.Verify.Audit.check roots

end Ix.Tc.Verify.Audit.Statements
