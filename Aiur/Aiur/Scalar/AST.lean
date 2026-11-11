import Std

namespace Aiur.Scalar

/-- The source language currently has one type, independently of literal storage. -/
inductive Ty where
  | field
  deriving Repr, BEq, DecidableEq

inductive BinOp where
  | add | sub | mul | div
  deriving Repr, BEq, DecidableEq

/-- `α` is `Nat` in the frontend and the chosen field after specialization. -/
inductive Pattern (α : Type) where
  | literal (value : α)
  | wildcard
  deriving Repr, BEq

inductive Expr (α : Type) where
  | literal (value : α)
  | var (name : String)
  | neg (value : Expr α)
  | binary (op : BinOp) (left right : Expr α)
  | call (function : String) (args : List (Expr α))
  | matchValue (scrutinee : Expr α) (arms : List (Pattern α × Expr α))
  deriving Repr, BEq

structure Function (α : Type) where
  name : String
  params : List String
  body : Expr α
  deriving Repr, BEq

/-- All definitions share one namespace, allowing forward and mutually recursive calls. -/
structure Program (α : Type) where
  functions : List (Function α)
  deriving Repr, BEq

def Program.findFunction? (program : Program α) (name : String) : Option (Function α) :=
  program.functions.find? (·.name == name)

def Pattern.map (f : α → β) : Pattern α → Pattern β
  | .literal value => .literal (f value)
  | .wildcard => .wildcard

/-- Map literal values in both expressions and patterns, preserving program structure. -/
def Expr.map (f : α → β) : Expr α → Expr β
  | .literal value => .literal (f value)
  | .var name => .var name
  | .neg value => .neg (value.map f)
  | .binary op left right => .binary op (left.map f) (right.map f)
  | .call name args => .call name (args.map (Expr.map f))
  | .matchValue scrutinee arms =>
      .matchValue (scrutinee.map f) (arms.map fun arm => (arm.1.map f, arm.2.map f))
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      first
      | omega
      | cases arm
        simp_all only [Prod.mk.sizeOf_spec]
        omega

def Function.map (f : α → β) (function : Function α) : Function β :=
  { name := function.name, params := function.params, body := function.body.map f }

def Program.map (f : α → β) (program : Program α) : Program β :=
  { functions := program.functions.map (Function.map f) }

/-- Specialize a frontend program by casting its natural literals into a field. -/
def Program.toField (F : Type) [NatCast F] (program : Program Nat) : Program F :=
  program.map (fun n => (Nat.cast n : F))

end Aiur.Scalar
