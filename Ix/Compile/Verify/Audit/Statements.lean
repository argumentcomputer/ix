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
    standardAxioms := standard },
  { root := ``Ix.Compile.Verify.Catalog.factorization },
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
  { root := ``Ix.Compile.Verify.compileExpr_run_ordinary_value,
    standardAxioms := standard, nativeAxioms := blake3Native }
]

run_cmd Ix.Tc.Verify.Audit.check roots

end Ix.Compile.Verify.Audit.Statements
