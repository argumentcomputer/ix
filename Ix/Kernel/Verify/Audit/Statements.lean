import Ix.Kernel.Verify.Audit.Basic
import Ix.Kernel.Verify.Audit.Completed
import Ix.Kernel.Verify.Statements

/-!
# Trust manifest for the public checker statement frontier

All seven roots are concrete results over the bounded production recursion
schedule and checker.  The three recursive-method adapters have no `sorryAx`
dependency; the standalone and atomic-block checker roots retain only the two
named Ix.Theory.Named typing lemmas through their singleton-definition branch.  The
supported-fragment root executes the exact Boolean serial workset and composes
its runtime success gates with serial composition and fixed inductive
certificate entries. This
module permits no local statement placeholder and additionally forbids the
Boolean/serialized roots from reaching oracle construction, restaging, or
world materialization.
-/

namespace Ix.Kernel.Verify.Audit.Statements

open Ix.Kernel.Verify.Audit

private def standard : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def forallEInv : Lean.Name :=
  ``Ix.Theory.Named.VEnv.IsDefEqU.forallE_inv_stratified
private def sortInv : Lean.Name := ``Ix.Theory.Named.VEnv.IsDefEqU.sort_inv
private def checkerDebt : Array Lean.Name := #[forallEInv, sortInv]

private def legacyWholeEnv : Array Lean.Name := #[
  ``Ix.Kernel.AddKInduct,
  ``Ix.Kernel.AddKInduct.to_addInduct,
  ``Ix.Kernel.TrKEnv',
  ``Ix.Kernel.TrKEnv
]

private def legacyAllDepthKnot : Array Lean.Name := #[
  ``Ix.Kernel.RecursiveMethodClosureContext,
  ``Ix.Kernel.RecursiveMethodClosureContext.closedAt,
  ``Ix.Kernel.RecursiveMethodClosureContext.methodsN,
  ``Ix.Kernel.RecursiveMethodClosureContext.fullInferenceContext,
  ``Ix.Kernel.RecursiveMethodClosureContext.next_fullInferenceWFAt,
  ``Ix.Kernel.RecursiveMethodClosureContext.methodsN_fullInferenceWFAt,
  ``Ix.Kernel.RecursiveMethodClosureContext.publicInfer_full_wf
]

private def forbidden : Array Lean.Name :=
  legacyWholeEnv ++ legacyAllDepthKnot

/- Scoped public recursive roots may retain the legacy declarations in the
library, but must not manufacture a global suffix model or pass through the
old proposition-classifier/run-context path. -/
private def legacyGlobalSuffix : Array Lean.Name := #[
  ``Ix.Kernel.KernelSuffixModel,
  ``Ix.Kernel.ScopedKernelSuffixModel.toKernelSuffixModel,
  ``Ix.Kernel.PropositionClassifierContext,
  ``Ix.Kernel.RecursiveMethodRunContext,
  ``Ix.Kernel.TcM.whnf.wf_legacy,
  ``Ix.Kernel.TcM.infer.wf_legacy,
  ``Ix.Kernel.TcM.isDefEq.wf_legacy,
  ``Ix.Kernel.TcM.checkConst.wf_legacy
]

private def scopedForbidden : Array Lean.Name :=
  forbidden ++ legacyGlobalSuffix

/- The all-block statement for the supported fragment must consume fixed semantic entries and may
not regain the retired residual-oracle/world-materialization path through an
adapter refactor. -/
private def oracleWorldMaterialization : Array Lean.Name := #[
  ``Ix.Kernel.VerifyWorld.admitOracle,
  ``Ix.Kernel.VerifyWorld.le_admitOracle,
  ``Ix.Kernel.OracleBlockCertificate.admit,
  ``Ix.Kernel.OracleBlockCertificate.admitState,
  ``Ix.Kernel.RecM.certifyOracleBackedBlock,
  ``Ix.Kernel.RecM.certifyOracleBackedAdmittedBlock,
  ``Ix.Kernel.SingletonFamilyCatalogLink.oracle,
  ``Ix.Kernel.SingletonRecursorCatalogLink.oracle,
  ``Ix.Kernel.InductiveOracle.reindex,
  ``Ix.Kernel.InductiveOracle.restageMissing
]

private def certificateBackedForbidden : Array Lean.Name :=
  scopedForbidden ++ oracleWorldMaterialization

private def runNative : Array Lean.Name := #[
  nativeAxiom `Ix.Kernel.Expr
    `Ix.Kernel.KExpr.mkVar._native.native_decide.ax_1,
  nativeAxiom `Ix.Kernel.Level
    `Ix.Kernel.KUniv.mkSucc._native.native_decide.ax_1,
]

private def checkConstNative : Array Lean.Name := #[
  nativeAxiom `Ix.Kernel.Expr
    `Ix.Kernel.KExpr.mkVar._native.native_decide.ax_1,
  nativeAxiom `Ix.Kernel.Level
    `Ix.Kernel.KUniv.mkSucc._native.native_decide.ax_1,
  nativeAxiom `Ix.Environment
    `Ix.Name.mkStr._native.native_decide.ax_1,
  nativeAxiom `Ix.Kernel.Inductive
    `Ix.Kernel.RecM.canonicalAuxOrder._native.native_decide.ax_9
]

private def roots : Array RootAllowance := #[
  { root := ``Ix.Kernel.TcM.whnf.wf,
    standardAxioms := standard, nativeAxioms := runNative,
    forbiddenDependencies := scopedForbidden },
  { root := ``Ix.Kernel.TcM.infer.wf,
    standardAxioms := standard, nativeAxioms := runNative,
    forbiddenDependencies := scopedForbidden },
  { root := ``Ix.Kernel.TcM.isDefEq.wf,
    standardAxioms := standard, nativeAxioms := runNative,
    forbiddenDependencies := scopedForbidden },
  { root := ``Ix.Kernel.TcM.checkConst.wf,
    standardAxioms := standard,
    nativeAxioms := checkConstNative,
    sorryOrigins := checkerDebt,
    forbiddenDependencies := scopedForbidden },
  { root := ``Ix.Kernel.TcM.checkConst.blockDisposition,
    standardAxioms := standard,
    nativeAxioms := checkConstNative,
    sorryOrigins := checkerDebt,
    forbiddenDependencies := scopedForbidden },
  { root := ``Ix.Kernel.BooleanEnumerationFixture.subjectWF,
    standardAxioms := standard,
    nativeAxioms := Ix.Kernel.Verify.Audit.Completed.booleanDriverNative,
    sorryOrigins := checkerDebt,
    forbiddenDependencies := certificateBackedForbidden },
  { root := ``Ix.Kernel.BooleanSerialized.subjectWF,
    standardAxioms := standard,
    nativeAxioms := Ix.Kernel.Verify.Audit.Completed.serializedBooleanNative,
    sorryOrigins := checkerDebt,
    forbiddenDependencies := certificateBackedForbidden }
]

run_cmd Ix.Kernel.Verify.Audit.check roots

end Ix.Kernel.Verify.Audit.Statements
