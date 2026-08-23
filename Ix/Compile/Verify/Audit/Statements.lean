import Ix.Tc.Verify.Audit.Basic
import Ix.Compile.Verify.Statements

/-!
# Trust manifest for the compiler statement frontier

These first expression-level roots are constructive.  The explicit
`KernelSourceWitness` assumption is data supplied to later theorems, not a
global axiom, and no compiler theorem may inherit checker acceptance as a
premise.
-/

namespace Ix.Compile.Verify.Audit.Statements

open Ix.Tc.Verify.Audit

private def standard : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def noChoice : Array Lean.Name := #[``propext, ``Quot.sound]

private def roots : Array RootAllowance := #[
  { root := ``Ix.Compile.Verify.IxonExprRel.eraseModes_iff,
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.compileUnivRef_value,
    standardAxioms := noChoice },
  { root := ``Ix.Compile.Verify.compileExprRef_leanFragment,
    standardAxioms := noChoice },
  { root := ``Ix.Compile.Verify.compileExprRef_eraseModes,
    standardAxioms := noChoice },
  { root := ``Ix.Compile.Verify.compileExprRef_value,
    standardAxioms := standard }
]

run_cmd Ix.Tc.Verify.Audit.check roots

end Ix.Compile.Verify.Audit.Statements
