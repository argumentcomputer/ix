/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Infer
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
]

run_cmd Kernel.Verify.Audit.check roots

end Ix.Kernel.Consistency.Audit
