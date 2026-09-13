/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Expr

namespace Ix.Theory

/-- Whether a declaration participates in the safe kernel fragment. -/
inductive Safety where
  | safe
  | «unsafe»
  | «partial»
  deriving DecidableEq, Repr

/-- The reduction behavior of a definition-like constant. -/
inductive DefKind where
  | definition
  | theorem
  | opaque
  deriving DecidableEq, Repr

/-- The four primitive constants that make up Lean's quotient interface. -/
inductive QuotKind where
  | type
  | ctor
  | lift
  | ind
  deriving DecidableEq, Repr

/-- Trusted constructor metadata nested under its inductive family. -/
structure Ctor (β : Type u) where
  uvars : Nat
  nparams : Nat
  nfields : Nat
  type : VExpr β
  safety : Safety
  deriving DecidableEq

/-- One recursor reduction rule, positional in its constructor list. -/
structure RecRule (β : Type u) where
  nfields : Nat
  rhs : VExpr β
  deriving DecidableEq

/-- Anonymous constant data stored in a content-addressed block. -/
inductive Const (β : Type u) where
  | axiom (uvars : Nat) (type : VExpr β) (safety : Safety)
  | defn (uvars : Nat) (kind : DefKind) (type value : VExpr β)
      (safety : Safety)
  | quot (kind : QuotKind) (uvars : Nat) (type : VExpr β)
  | induct (uvars nparams nindices : Nat) (type : VExpr β)
      (ctors : List (Ctor β)) (safety : Safety)
  | recursor (uvars nparams nindices nmotives nminors : Nat) (type : VExpr β)
      (rules : List (RecRule β)) (k : Bool) (safety : Safety)
  deriving DecidableEq

/-- A content-addressed unit. Members are ordered and addressed positionally. -/
structure Block (β : Type u) where
  members : List (Const β)
  deriving DecidableEq

/-- A compact tag shared by ordinary members and nested constructors. -/
inductive ConstKind where
  | axiom
  | defn (kind : DefKind)
  | quot (kind : QuotKind)
  | induct
  | ctor
  | recursor
  deriving DecidableEq, Repr

namespace Ctor

def refs (ctor : Ctor β) : List (ConstRef β) := ctor.type.refs

/-- Syntactic closure of a constructor declaration. -/
def Closed (ctor : Ctor β) : Prop := ctor.type.Closed

/-- The constructor's declared field telescope, excluding shared parameters. -/
def fieldTypes (ctor : Ctor β) : List (VExpr β) :=
  (ctor.type.telN (ctor.nparams + ctor.nfields)).drop ctor.nparams

/-- Whether a field type refers to any member of the indicated block. -/
def recursiveInBlock [DecidableEq β] (ctor : Ctor β) (block : β) : Bool :=
  ctor.fieldTypes.any fun field =>
    field.refs.any fun ref => ref.block == block

end Ctor

namespace RecRule

def refs (rule : RecRule β) : List (ConstRef β) := rule.rhs.refs

/-- Syntactic closure of a stored recursor rule. -/
def Closed (rule : RecRule β) : Prop := rule.rhs.Closed

end RecRule

namespace Const

/-- Every trusted expression carried by a constant is term-variable closed. -/
def Closed : Const β → Prop
  | .axiom _ type _ => type.Closed
  | .defn _ _ type value _ => type.Closed ∧ value.Closed
  | .quot _ _ type => type.Closed
  | .induct _ _ _ type ctors _ =>
      type.Closed ∧ ∀ ctor ∈ ctors, ctor.Closed
  | .recursor _ _ _ _ _ type rules _ _ =>
      type.Closed ∧ ∀ rule ∈ rules, rule.Closed

/-- Number of constructors contributed to a block's flattened rule order. -/
def ctorCount : Const β → Nat
  | .induct _ _ _ _ ctors _ => ctors.length
  | _ => 0

def kind : Const β → ConstKind
  | .axiom .. => .axiom
  | .defn _ kind .. => .defn kind
  | .quot kind .. => .quot kind
  | .induct .. => .induct
  | .recursor .. => .recursor

def uvars : Const β → Nat
  | .axiom uvars .. | .defn uvars .. | .induct uvars .. |
    .recursor uvars .. => uvars
  | .quot _ uvars _ => uvars

def type : Const β → VExpr β
  | .axiom _ type _ | .defn _ _ type _ _ | .quot _ _ type |
    .induct _ _ _ type _ _ | .recursor _ _ _ _ _ type _ _ _ => type

theorem Closed.type_closed {constant : Const β}
    (closed : constant.Closed) : constant.type.Closed := by
  cases constant <;> simp_all [Closed, type]

/-- Every external reference occurring in a member's trusted expressions. -/
def refs : Const β → List (ConstRef β)
  | .axiom _ type _ => type.refs
  | .defn _ _ type value _ => type.refs ++ value.refs
  | .quot _ _ type => type.refs
  | .induct _ _ _ type ctors _ => type.refs ++ ctors.flatMap Ctor.refs
  | .recursor _ _ _ _ _ type rules _ _ => type.refs ++ rules.flatMap RecRule.refs

end Const

namespace Block

/-- Every constant stored in a block is syntactically closed. -/
def Closed (block : Block β) : Prop :=
  ∀ constant ∈ block.members, constant.Closed

theorem Closed.member {block : Block β} (closed : block.Closed)
    {index : Nat} {constant : Const β}
    (found : block.members[index]? = some constant) : constant.Closed :=
  closed constant (List.mem_iff_getElem?.2 ⟨index, found⟩)

/-- References from all member types, values, constructor types, and recursor rules. -/
def refs (block : Block β) : List (ConstRef β) :=
  block.members.flatMap Const.refs

end Block

end Ix.Theory
