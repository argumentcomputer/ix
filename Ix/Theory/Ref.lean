/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

namespace Ix.Theory

/-- A reference to a constant contained in a content-addressed block. -/
inductive ConstRef (β : Type u) where
  /-- The `i`th top-level member of block `b`. -/
  | member (b : β) (i : Nat)
  /-- The `c`th constructor of the `i`th inductive member of block `b`. -/
  | ctor (b : β) (i c : Nat)
deriving DecidableEq, Hashable

namespace ConstRef

/-- The block containing a referenced member or constructor. -/
@[simp] def block : ConstRef β → β
  | .member b _ | .ctor b _ _ => b

end ConstRef
end Ix.Theory
