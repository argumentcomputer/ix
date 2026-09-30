/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.BetaSpine

/-! # Substitution without rebuilding zero-shift replacements

The arbitrary replacement below cannot be traversed by definitional
reduction. These `rfl` checks require substitution at depth zero to return
it directly, including when it occurs repeatedly. Positive-depth checks
retain the lift needed to avoid capturing free variables. -/

open Ix.Kernel Ix.Kernel.Model

namespace Tests.Ix.Kernel.SubstitutionSharing

example (replacement : AExpr β) :
    (AExpr.bvar 0).inst replacement = replacement := rfl

example (replacement : AExpr β) :
    (AExpr.app (.bvar 0) (.bvar 0)).inst replacement =
      .app replacement replacement := rfl

-- The domain uses the identity shortcut; the body crosses a binder and
-- must lift the same replacement while preserving its newly bound variable.
example (replacement : AExpr β) (condition : Certified.PropWhen) :
    (AExpr.lam condition (.bvar 0) (.app (.bvar 1) (.bvar 0))).inst replacement =
      .lam condition replacement (.app (replacement.liftN 1) (.bvar 0)) := rfl

example (replacement : AExpr β) :
    (AExpr.letE (.bvar 0) (.bvar 0) (.app (.bvar 1) (.bvar 0))).inst replacement =
      .letE replacement replacement (.app (replacement.liftN 1) (.bvar 0)) := rfl

-- A free reference in the replacement remains free under both binders;
-- references above the removed variable decrement exactly once.
#guard ((.lam .always (.bvar 0)
    (.forallE .never (.bvar 1) (.app (.bvar 2) (.bvar 3)))) : AExpr Nat).inst
      (.app (.bvar 0) (.bvar 1)) =
  .lam .always (.app (.bvar 0) (.bvar 1))
    (.forallE .never (.app (.bvar 1) (.bvar 2))
      (.app (.app (.bvar 2) (.bvar 3)) (.bvar 2)))

end Tests.Ix.Kernel.SubstitutionSharing
