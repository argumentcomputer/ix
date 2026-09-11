import Ix.Compiler.IxIR1.Basic

/-!
# IxIR₂: block-local ownership and reuse-credit IR

IxIR₂ makes the ownership information needed for checked reuse explicit.
Values and reuse credits live in separate block-local register files.  Block
parameters describe the complete capability environment at each control-flow
join, so the executable validator can check every block independently.

This file is deliberately syntax-only.  `Ix.Compiler.IxIR2.Validate` supplies
the bounded checker and its proof-facing acceptance predicate.
-/

namespace Ix.Compiler.IxIR2

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR0 (Literal)

abbrev BlockId := Nat
abbrev ValueId := Nat
abbrev CreditId := Nat
abbrev LayoutId := Address
abbrev CtorId := IxIR1.CtorId

/-- Block-local operands.  Registers are numbered in definition order. -/
inductive Atom where
  | reg (id : ValueId)
  | lit (literal : Literal)
  | erased
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Whether a function call transfers an argument root or merely observes it. -/
inductive ParamPassing where
  | owned
  | borrowed
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Param where
  world : Owned
  passing : ParamPassing
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- The checked call interface of one function. -/
structure Signature where
  params : Array Param
  result : Owned
  /-- May this function be entered through a shared partial application? -/
  papSafe : Bool
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- The ownership root that keeps a non-retaining view alive. -/
inductive BorrowLender where
  /-- A caller-owned root that this activation never consumes. -/
  | caller
  /-- A prior owning value in the same block. -/
  | value (id : ValueId)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Capability available for one value at a block boundary or program point. -/
inductive ValueCap where
  | scalar
  | owned (world : Owned)
  | borrowed (world : Owned) (lender : BorrowLender)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- A required credit is definitely present; an optional credit may be absent. -/
inductive CreditCap where
  | required (layout : LayoutId)
  | optional (layout : LayoutId)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Checked representation information for one constructor in one world. -/
structure CtorSchema where
  layout : LayoutId
  fields : Array Owned
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Primitive instructions.  Result values and credits are appended to their
respective register files in the order specified by the validator contract. -/
inductive Instr where
  | move (value : Atom)
  | alloc (world : Owned) (cid : CtorId) (args : Array Atom)
  | allocWith (credit : CreditId) (world : Owned) (cid : CtorId)
      (args : Array Atom)
  | discardCredit (credit : CreditId)
  | takeUnique (target : Atom) (cid : CtorId)
  | resetShared (target : Atom) (cid : CtorId)
  | retainShared (target : Atom)
  | releaseShared (target : Atom)
  | dropUnique (target : Atom)
  | freeUnique (target : Atom) (cid : CtorId)
  | fetch (target : Atom) (cid : CtorId) (field : Nat)
  | call (function : Address) (args : Array Atom)
  | callSelf (args : Array Atom)
  | papp (function : Address) (args : Array Atom)
  | apply (function : Atom) (args : Array Atom)
  | extern (function : Address) (args : Array Atom)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Complete arguments for one control-flow transfer. -/
structure Edge where
  target : BlockId
  values : Array Atom
  credits : Array CreditId
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure CtorAlt where
  cid : CtorId
  edge : Edge
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Literal peeling bundled with constructor dispatch for a dynamically
represented IxIR₁ case scrutinee.  The successor transfer implicitly prepends
the predecessor literal to the explicit edge arguments. -/
structure NatPeel where
  zero : Edge
  succ : Edge
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Terminator where
  | jump (edge : Edge)
  | switchValue (scrutinee : Atom) (constructors : Array CtorAlt)
      (natPeel : Option NatPeel)
  | branchCredit (credit : CreditId) (someEdge noneEdge : Edge)
  | ret (value : Atom)
  | tailCall (function : Address) (args : Array Atom)
  | tailCallSelf (args : Array Atom)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Block where
  valueParams : Array ValueCap
  creditParams : Array CreditCap
  instructions : Array Instr
  terminator : Terminator
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Block `0` is the entry block.  Block IDs are array indices. -/
structure Function where
  signature : Signature
  blocks : Array Block
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Decl where
  | fn (definition : Function)
  | extern (arity : Nat)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- A finite, content-addressed declaration world plus its distinguished main
function.  The validator rejects duplicate declaration addresses. -/
structure Program where
  declarations : List (Address × Decl)
  main : Function
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

end Ix.Compiler.IxIR2
