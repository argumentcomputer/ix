import Compilatrix.IxIR2.Validate

/-!
# Finite inputs to an independently addressed IxIR₂ snapshot

The complete program is stored under one root. Declaration keys remain exact
logical symbols, so recursive dependency graphs need no recursive hash
equation. Every declaration body, ordered block, schema, layout preimage and
policy is included in the snapshot identity. This format does not renumber
blocks, rekey declarations, or certify the origin of supplied sidecars.
-/

namespace Compilatrix.IxIR2.Wire

open Compilatrix.Ixon (Address Owned)

local instance : LawfulBEq ByteArray where
  eq_of_beq := fun equal => ByteArray.ext (eq_of_beq equal)
  rfl := by intro value; change (value.data == value.data) = true; simp

local instance : Repr ByteArray where
  reprPrec value precedence := reprPrec value.data precedence

structure Policy where
  semantics : String
  validator : String
  lowering : String
  passes : Array String
  layout : String
  credits : CreditPolicy
  allowExtern : Bool := false
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- A named provenance input. Role and root both participate in identity. -/
structure Dependency where
  role : String
  root : Address
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Exact bytes behind a layout key. Their ABI is selected by `Policy.layout`;
the artifact checker verifies the BLAKE3 key without interpreting the bytes. -/
structure Layout where
  identity : LayoutId
  preimage : ByteArray
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Schema where
  world : Owned
  constructor : CtorId
  definition : CtorSchema
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Artifact where
  policy : Policy
  dependencies : Array Dependency
  layouts : Array Layout
  schemas : Array Schema
  scalarLeaves : Array Validate.ScalarLeafFact
  program : Program
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

end Compilatrix.IxIR2.Wire
