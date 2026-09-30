/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Runtime.Expr

/-! # Runtime terms with free variables as levels (S1, phase 1)

Opening a binder substitutes a level without shifting it, closing reads
levels back as indices, and abstraction inverts opening. The `rfl` checks
require `inst1` to return an arbitrary bvar-closed replacement as it is,
including under binders, where `AExpr.inst` would lift it. -/

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Runtime

namespace Tests.Ix.Kernel.RuntimeStack

-- The replacement is used as it is under a binder: no lift.
example (replacement : RExpr β) (condition : Certified.PropWhen) :
    (RExpr.lam condition (.bvar 0) (.app (.bvar 1) (.bvar 0))).inst1 replacement =
      .lam condition replacement (.app replacement (.bvar 0)) := rfl

-- Indices above the substituted one are lowered; levels are untouched.
#guard ((RExpr.app (.bvar 2) (.app (.bvar 0) (.fvar 5)) : RExpr Nat).inst1 (.fvar 7)) =
  .app (.bvar 1) (.app (.fvar 7) (.fvar 5))

-- Opening `λ. #0 #1` at depth 2 with level 2, then closing at depth 3, is the
-- body read at depth 2 under one binder: `#0` is the new variable.
#guard (RExpr.closeAt 3 0 ((RExpr.app (.bvar 0) (.fvar 1) : RExpr Nat).inst1 (.fvar 2))) =
  (RExpr.closeAt 2 1 (RExpr.app (.bvar 0) (.fvar 1) : RExpr Nat))

-- Levels read as indices from the top of the stack, shifted by binders.
#guard (RExpr.close 3 (.lam .never (.fvar 0) (.app (.fvar 2) (.bvar 0)) : RExpr Nat)) =
  (.lam .never (.bvar 2) (.app (.bvar 1) (.bvar 0)) : AExpr Nat)

-- Abstraction binds exactly the requested level.
#guard ((RExpr.app (.fvar 3) (.lam .never (.fvar 1) (.fvar 3)) : RExpr Nat).abstract1 3) =
  .app (.bvar 0) (.lam .never (.fvar 1) (.bvar 1))

-- `openAt` turns a context term's loose indices into levels.
#guard (RExpr.openAt 3 0 (.app (.bvar 0) (.lam .never (.bvar 2) (.bvar 1)) : AExpr Nat)) =
  .app (.fvar 2) (.lam .never (.fvar 0) (.fvar 2))

#guard (RExpr.close 3 (RExpr.openAt 3 0 (.app (.bvar 0) (.lam .never (.bvar 2) (.bvar 1)) : AExpr Nat))) =
  (.app (.bvar 0) (.lam .never (.bvar 2) (.bvar 1)) : AExpr Nat)

-- The computed fields.
#guard (RExpr.lam .never (.fvar 4) (.app (.bvar 0) (.bvar 2)) : RExpr Nat).looseBound = 2
#guard (RExpr.lam .never (.fvar 4) (.app (.bvar 0) (.bvar 2)) : RExpr Nat).fvarBound = 5
#guard (RExpr.ofAExpr (.lam .never (.bvar 0) (.bvar 1)) : RExpr Nat).fvarBound = 0

-- Pointer-first equality agrees with structural equality.
#guard (RExpr.app (.fvar 1) (.bvar 0) : RExpr Nat) = .app (.fvar 1) (.bvar 0)
#guard (RExpr.app (.fvar 1) (.bvar 0) : RExpr Nat) ≠ .app (.bvar 1) (.bvar 0)

end Tests.Ix.Kernel.RuntimeStack
