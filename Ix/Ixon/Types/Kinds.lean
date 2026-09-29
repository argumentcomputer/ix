/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
module

public section

/-! Declaration tags shared by Ixon and the host compiler. -/

/-- Distinguish different kinds of Ix definitions --/
inductive Ix.DefKind where
| defn : Ix.DefKind
| opaq : Ix.DefKind
| thm : Ix.DefKind
deriving BEq, Ord, Hashable, Repr, Nonempty, Inhabited, DecidableEq

inductive Ix.DefinitionSafety where
  | unsaf : Ix.DefinitionSafety
  | safe : Ix.DefinitionSafety
  | part : Ix.DefinitionSafety
  deriving BEq, Ord, Hashable, Repr, Nonempty, Inhabited, DecidableEq

inductive Ix.QuotKind where
  | type : Ix.QuotKind
  | ctor : Ix.QuotKind
  | lift : Ix.QuotKind
  | ind : Ix.QuotKind
  deriving BEq, Ord, Hashable, Repr, Nonempty, Inhabited, DecidableEq

end
