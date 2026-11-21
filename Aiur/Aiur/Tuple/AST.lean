import Std

namespace Aiur.Tuple

/-- Tuple shape is part of the type, including empty and singleton tuples. -/
inductive Ty where
  | field
  | tuple (items : List Ty)
  deriving Repr, BEq

mutual
  def Ty.decEq : (left right : Ty) → Decidable (left = right)
    | .field, .field => .isTrue rfl
    | .tuple xs, .tuple ys =>
        match Ty.listDecEq xs ys with
        | .isTrue h => .isTrue (congrArg Ty.tuple h)
        | .isFalse h => .isFalse (fun eq => h (Ty.tuple.inj eq))
    | .field, .tuple _ => .isFalse (by intro h; cases h)
    | .tuple _, .field => .isFalse (by intro h; cases h)
  termination_by left _ => sizeOf left

  def Ty.listDecEq : (left right : List (Ty)) → Decidable (left = right)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro h; cases h)
    | _ :: _, [] => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys => match Ty.decEq x y, Ty.listDecEq xs ys with
      | .isTrue h, .isTrue hs => .isTrue (by cases h; cases hs; rfl)
      | .isFalse h, _ => .isFalse (fun eq => h (List.cons.inj eq).1)
      | _, .isFalse h => .isFalse (fun eq => h (List.cons.inj eq).2)
  termination_by left _ => sizeOf left
end

instance : DecidableEq (Ty) := Ty.decEq

inductive BinOp where
  | add | sub | mul | div
  deriving Repr, BEq, DecidableEq

/-- A structured value whose leaves are field elements (or symbolic field expressions). -/
inductive Value (α : Type) where
  | field (value : α)
  | tuple (items : List (Value α))
  deriving Repr, BEq

mutual
  def Value.decEq [DecidableEq α] : (left right : Value α) → Decidable (left = right)
    | .field x, .field y =>
        if h : x = y then .isTrue (by cases h; rfl)
        else .isFalse (fun eq => h (Value.field.inj eq))
    | .tuple xs, .tuple ys =>
        match Value.listDecEq xs ys with
        | .isTrue h => .isTrue (congrArg Value.tuple h)
        | .isFalse h => .isFalse (fun eq => h (Value.tuple.inj eq))
    | .field _, .tuple _ => .isFalse (by intro h; cases h)
    | .tuple _, .field _ => .isFalse (by intro h; cases h)
  termination_by left _ => sizeOf left

  def Value.listDecEq [DecidableEq α] : (left right : List (Value α)) → Decidable (left = right)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro h; cases h)
    | _ :: _, [] => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys => match Value.decEq x y, Value.listDecEq xs ys with
      | .isTrue h, .isTrue hs => .isTrue (by cases h; cases hs; rfl)
      | .isFalse h, _ => .isFalse (fun eq => h (List.cons.inj eq).1)
      | _, .isFalse h => .isFalse (fun eq => h (List.cons.inj eq).2)
  termination_by left _ => sizeOf left
end

instance [DecidableEq α] : DecidableEq (Value α) := Value.decEq

def Value.map (f : α → β) : Value α → Value β
  | .field x => .field (f x)
  | .tuple items => .tuple (items.map (Value.map f))
termination_by value => sizeOf value

def Value.type : Value α → Ty
  | .field _ => .field
  | .tuple items => .tuple (items.map Value.type)
termination_by value => sizeOf value

def Value.flatten : Value α → List α
  | .field x => [x]
  | .tuple items => items.flatMap Value.flatten
termination_by value => sizeOf value

instance [OfNat α n] : OfNat (Value α) n := ⟨.field (OfNat.ofNat n)⟩

/-- Patterns can test leaves, discard subtrees, or bind entire subtrees. -/
inductive Pattern (α : Type) where
  | literal (value : α)
  | wildcard
  | bind (name : String)
  | tuple (items : List (Pattern α))
  deriving Repr, BEq

mutual
  def Pattern.decEq [DecidableEq α] : (left right : Pattern α) → Decidable (left = right)
    | .literal x, .literal y =>
        if h : x = y then .isTrue (by cases h; rfl)
        else .isFalse (fun eq => h (Pattern.literal.inj eq))
    | .wildcard, .wildcard => .isTrue rfl
    | .bind x, .bind y =>
        if h : x = y then .isTrue (by cases h; rfl)
        else .isFalse (fun eq => h (Pattern.bind.inj eq))
    | .tuple xs, .tuple ys =>
        match Pattern.listDecEq xs ys with
        | .isTrue h => .isTrue (congrArg Pattern.tuple h)
        | .isFalse h => .isFalse (fun eq => h (Pattern.tuple.inj eq))
    | .literal _, .wildcard => .isFalse (by intro h; cases h)
    | .literal _, .bind _ => .isFalse (by intro h; cases h)
    | .literal _, .tuple _ => .isFalse (by intro h; cases h)
    | .wildcard, .literal _ => .isFalse (by intro h; cases h)
    | .wildcard, .bind _ => .isFalse (by intro h; cases h)
    | .wildcard, .tuple _ => .isFalse (by intro h; cases h)
    | .bind _, .literal _ => .isFalse (by intro h; cases h)
    | .bind _, .wildcard => .isFalse (by intro h; cases h)
    | .bind _, .tuple _ => .isFalse (by intro h; cases h)
    | .tuple _, .literal _ => .isFalse (by intro h; cases h)
    | .tuple _, .wildcard => .isFalse (by intro h; cases h)
    | .tuple _, .bind _ => .isFalse (by intro h; cases h)
  termination_by left _ => sizeOf left

  def Pattern.listDecEq [DecidableEq α] : (left right : List (Pattern α)) → Decidable (left = right)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro h; cases h)
    | _ :: _, [] => .isFalse (by intro h; cases h)
    | x :: xs, y :: ys => match Pattern.decEq x y, Pattern.listDecEq xs ys with
      | .isTrue h, .isTrue hs => .isTrue (by cases h; cases hs; rfl)
      | .isFalse h, _ => .isFalse (fun eq => h (List.cons.inj eq).1)
      | _, .isFalse h => .isFalse (fun eq => h (List.cons.inj eq).2)
  termination_by left _ => sizeOf left
end

instance [DecidableEq α] : DecidableEq (Pattern α) := Pattern.decEq

inductive Expr (α : Type) where
  | literal (value : α)
  | var (name : String)
  | tuple (items : List (Expr α))
  | project (value : Expr α) (index : Nat)
  | letValue (pattern : Pattern α) (value body : Expr α)
  | neg (value : Expr α)
  | binary (op : BinOp) (left right : Expr α)
  | call (function : String) (args : List (Expr α))
  | matchValue (scrutinee : Expr α) (arms : List (Pattern α × Expr α))
  deriving Repr, BEq

structure Function (α : Type) where
  name : String
  params : List (String × Ty)
  result : Ty
  body : Expr α
  deriving Repr, BEq

structure Program (α : Type) where
  functions : List (Function α)
  deriving Repr, BEq

def Program.findFunction? (program : Program α) (name : String) : Option (Function α) :=
  program.functions.find? (·.name == name)

def Pattern.map (f : α → β) : Pattern α → Pattern β
  | .literal x => .literal (f x)
  | .wildcard => .wildcard
  | .bind name => .bind name
  | .tuple items => .tuple (items.map (Pattern.map f))
termination_by pattern => sizeOf pattern

/-- Bindings and wildcards accept every value of their checked type. -/
def Pattern.irrefutable : Pattern α → Bool
  | .literal _ => false
  | .wildcard | .bind _ => true
  | .tuple items => (items.map Pattern.irrefutable).all id
termination_by pattern => sizeOf pattern

/-- Ignore binder names when checking duplicate matching conditions. -/
def Pattern.condition : Pattern α → Pattern α
  | .bind _ => .wildcard
  | .tuple items => .tuple (items.map Pattern.condition)
  | pattern => pattern
termination_by pattern => sizeOf pattern

def Expr.map (f : α → β) : Expr α → Expr β
  | .literal value => .literal (f value)
  | .var name => .var name
  | .tuple items => .tuple (items.map (Expr.map f))
  | .project value index => .project (value.map f) index
  | .letValue pattern value body => .letValue (pattern.map f) (value.map f) (body.map f)
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
      | cases arm; simp_all only [Prod.mk.sizeOf_spec]; omega

def Function.map (f : α → β) (function : Function α) : Function β :=
  { function with body := function.body.map f }

def Program.map (f : α → β) (program : Program α) : Program β :=
  { functions := program.functions.map (Function.map f) }

def Program.toField (F : Type) [NatCast F] (program : Program Nat) : Program F :=
  program.map (fun n => (Nat.cast n : F))

end Aiur.Tuple
