import Ix.Tc.Verify.Audit.Basic
import Ix.Tc.Verify.Statements

/-!
# Trust manifest for the temporary checker statement frontier

The four roots in this import context are intentionally still proved with
`sorry`. Their exact direct frontier includes each theorem itself plus the
two upstream inductive-environment assumptions now exposed by G4's concrete
`KernelTcInv`. As proofs land, the corresponding local origin must disappear
and the remaining transitive boundary must still match exactly.
-/

namespace Ix.Tc.Verify.Audit.Statements

open Ix.Tc.Verify.Audit

private def standard : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def inductiveWF : Lean.Name := ``Lean4Lean.VInductDecl.WF
private def addInduct : Lean.Name := ``Lean4Lean.VEnv.addInduct

private def runNative : Array Lean.Name := #[
  nativeAxiom `Blake3
    `Blake3.HasherOps.hash._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Expr
    `Ix.Tc.KExpr.mkVar._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Level
    `Ix.Tc.KUniv.mkSucc._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Monad
    `Ix.Tc.TcM.ctxAddrForLbr._native.native_decide.ax_5
]

private def checkConstNative : Array Lean.Name := #[
  nativeAxiom `Blake3
    `Blake3.HasherOps.hash._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Expr
    `Ix.Tc.KExpr.mkVar._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Level
    `Ix.Tc.KUniv.mkSucc._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Monad
    `Ix.Tc.TcM.ctxAddrForLbr._native.native_decide.ax_5,
  nativeAxiom `Ix.Environment
    `Ix.Name.mkStr._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Inductive
    `Ix.Tc.RecM.canonicalAuxOrder._native.native_decide.ax_17
]

private def roots : Array RootAllowance := #[
  { root := ``Ix.Tc.TcM.whnf.wf,
    standardAxioms := standard, nativeAxioms := runNative,
    sorryOrigins := #[inductiveWF, addInduct, ``Ix.Tc.TcM.whnf.wf] },
  { root := ``Ix.Tc.TcM.infer.wf,
    standardAxioms := standard, nativeAxioms := runNative,
    sorryOrigins := #[inductiveWF, addInduct, ``Ix.Tc.TcM.infer.wf] },
  { root := ``Ix.Tc.TcM.isDefEq.wf,
    standardAxioms := standard, nativeAxioms := runNative,
    sorryOrigins := #[inductiveWF, addInduct, ``Ix.Tc.TcM.isDefEq.wf] },
  { root := ``Ix.Tc.TcM.checkConst.wf,
    standardAxioms := standard,
    nativeAxioms := checkConstNative,
    sorryOrigins := #[inductiveWF, addInduct, ``Ix.Tc.TcM.checkConst.wf] }
]

run_cmd Ix.Tc.Verify.Audit.check roots

end Ix.Tc.Verify.Audit.Statements
