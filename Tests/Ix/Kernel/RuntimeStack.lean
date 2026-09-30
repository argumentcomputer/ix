/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Runtime.Close

/-! # Runtime terms with free variables as levels (S1, phase 1)

Opening a binder substitutes a level without shifting it, closing reads
levels back as indices, and abstraction inverts opening. The `rfl` checks
require `inst1` to return an arbitrary bvar-closed replacement as it is,
including under binders, where `AExpr.inst` would lift it. Stamps stay valid
under deeper pushes and die at a pop below their depth, including when a
sibling binder of the same type is pushed in its place. -/

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

/-! ## The stack -/

def s0 : Stack Nat := .empty
def s1 : Stack Nat := s0.push (.sort .zero)
def s2 : Stack Nat := s1.push (.fvar 0)

-- Entries are read at their own depth and lifted by `Context.push`.
#guard s2.view = [.bvar 1, .sort .zero]
#guard s2.fvarType? 1 = some (.fvar 0)

#guard s2.stamp.valid s2
-- Deeper stacks extending the prefix keep the stamp.
#guard s2.stamp.valid (s2.push (.fvar 1))
#guard s2.stamp.valid ((s2.push (.fvar 1)).pop)
-- A pop below the stamp's depth invalidates it, and so does a sibling binder,
-- even of the same type: only weakening is licensed.
#guard !(s2.stamp.valid s2.pop)
#guard !(s2.stamp.valid (s2.pop.push (.fvar 0)))
-- The level below survives the sibling.
#guard s1.stamp.valid (s2.pop.push (.fvar 0))
#guard !(s1.stamp.valid (s2.pop.pop.push (.sort .zero)))
#guard s0.stamp.valid s2.pop.pop

/-! ## The commutation lemmas at work

A λ inferred at `s2`: the body opened with `fvar 2`, its type bound back with
`abstract1`, and every claim read through `close`. -/

-- `λ (x : #fvar 1). f x` with its body at depth 2 under one binder.
def body : RExpr Nat := .app (.fvar 0) (.bvar 0)
def opened : RExpr Nat := body.inst1 (.fvar s2.size)

#guard RExpr.close (s2.size + 1) opened = RExpr.closeAt s2.size 1 body
#guard (s2.push (.fvar 1)).view = s2.view.push (RExpr.close s2.size (.fvar 1))
-- The body's type at depth 3, bound as a Π body at depth 2.
#guard RExpr.closeAt 2 1 ((RExpr.app (.fvar 1) (.fvar 2) : RExpr Nat).abstract1 2) =
  RExpr.close 3 (.app (.fvar 1) (.fvar 2))
-- Beta at depth 2 is model substitution of the closed argument.
#guard RExpr.close 2 ((RExpr.app (.bvar 0) (.fvar 0) : RExpr Nat).inst1 (.fvar 1)) =
  (RExpr.closeAt 2 1 (.app (.bvar 0) (.fvar 0))).inst (RExpr.close 2 (.fvar 1))
-- A term made at depth 2 read at depth 4 is its lift by 2.
#guard RExpr.close 4 (.lam .never (.fvar 1) (.app (.fvar 0) (.bvar 0)) : RExpr Nat) =
  (RExpr.close 2 (.lam .never (.fvar 1) (.app (.fvar 0) (.bvar 0)))).liftN 2

-- The lemmas themselves, instantiated.
example : RExpr.close (s2.size + 1) opened = RExpr.closeAt s2.size 1 body :=
  RExpr.close_open
    (by simp [body, RExpr.fvarBound, s2, s1, s0, Stack.empty, Stack.size, Stack.push])
    (by simp [body, RExpr.looseBound])

example (s : Stack Nat) (A : RExpr Nat) :
    (s.push A).view = s.view.push (RExpr.close s.size A) := Stack.view_push s A

end Tests.Ix.Kernel.RuntimeStack
