import Aiur.Scalar.AST
import Mathlib.Algebra.Field.Basic

namespace Aiur.Scalar.Circuit

abbrev Var := Nat
abbrev Channel := String

/-- A polynomial expression. Division and function calls are deliberately absent. -/
inductive ArithExpr (F : Type) where
  | const (value : F)
  | var (id : Var)
  | add (left right : ArithExpr F)
  | sub (left right : ArithExpr F)
  | mul (left right : ArithExpr F)
  deriving Repr, BEq

/-- The value of a polynomial under an assignment, not an execution instruction. -/
def ArithExpr.denote [Field F] (assignment : Var → F) : ArithExpr F → F
  | .const value => value
  | .var id => assignment id
  | .add left right => left.denote assignment + right.denote assignment
  | .sub left right => left.denote assignment - right.denote assignment
  | .mul left right => left.denote assignment * right.denote assignment

def ArithExpr.inBounds (numVars : Nat) : ArithExpr F → Bool
  | .const _ => true
  | .var id => id < numVars
  | .add left right | .sub left right | .mul left right =>
      left.inBounds numVars && right.inBounds numVars

/-- Every local constraint is exactly a polynomial required to be zero. -/
abbrev Constraint := ArithExpr

def Satisfies [Field F] (constraints : List (Constraint F)) (assignment : Var → F) : Prop :=
  ∀ polynomial ∈ constraints, polynomial.denote assignment = 0

/-- Constraint order has no semantic significance. -/
theorem satisfies_perm [Field F] {left right : List (Constraint F)}
    (h : left.Perm right) (assignment : Var → F) :
    Satisfies left assignment ↔ Satisfies right assignment := by
  constructor
  · intro valid polynomial member
    exact valid polynomial (h.mem_iff.mpr member)
  · intro valid polynomial member
    exact valid polynomial (h.mem_iff.mp member)

/-- A call requests a tuple of arguments together with its claimed return value. -/
structure Message (F : Type) where
  channel : Channel
  args : List F
  result : F
  deriving Repr, BEq, DecidableEq

/-- An enabled call contributes one message; its result is always a local variable. -/
structure Send (F : Type) where
  channel : Channel
  args : List (ArithExpr F)
  result : Var
  enable : ArithExpr F
  deriving Repr, BEq

def Send.message [Field F] (send : Send F) (assignment : Var → F) : Message F :=
  ⟨send.channel, send.args.map (ArithExpr.denote assignment), assignment send.result⟩

def Send.inBounds (numVars : Nat) (send : Send F) : Bool :=
  send.result < numVars && send.enable.inBounds numVars &&
    send.args.all (ArithExpr.inBounds numVars)

/--
One chip per function. Inputs occupy variables `0 .. arity - 1`.
The lists of equations and sends impose no execution order.
-/
structure Chip (F : Type) where
  name : String
  arity : Nat
  numVars : Nat
  output : Var
  constraints : List (Constraint F)
  sends : List (Send F)
  deriving Repr, BEq

def Chip.wellFormed (chip : Chip F) : Bool :=
  chip.arity ≤ chip.output && chip.output < chip.numVars &&
    chip.constraints.all (ArithExpr.inBounds chip.numVars) &&
    chip.sends.all (Send.inBounds chip.numVars)

/-- A proposed simultaneous assignment for one invocation of a chip. -/
structure Row (F : Type) where
  chip : String
  values : List F
  deriving Repr, BEq

def Row.assignment [Zero F] (row : Row F) (id : Var) : F :=
  row.values[id]?.getD 0

structure System (F : Type) where
  chips : List (Chip F)
  deriving Repr, BEq

def System.findChip? (system : System F) (name : String) : Option (Chip F) :=
  system.chips.find? (·.name == name)

inductive WitnessError where
  | duplicateChip (name : String)
  | unknownChip (name : String)
  | invalidLayout (name : String)
  | wrongRowSize (name : String) (expected actual : Nat)
  | constraintNotZero (name : String) (index : Nat)
  | unbalancedMessages
  deriving Repr, BEq, DecidableEq

/-- Validate a proposed assignment and obtain its receive and enabled sends. -/
def Chip.checkRow [Field F] [DecidableEq F] (chip : Chip F) (row : Row F) :
    Except WitnessError (Message F × List (Message F)) := do
  if !chip.wellFormed then throw (.invalidLayout chip.name)
  if row.values.length != chip.numVars then
    throw (.wrongRowSize chip.name chip.numVars row.values.length)
  for (polynomial, index) in chip.constraints.zipIdx do
    if polynomial.denote row.assignment ≠ 0 then throw (.constraintNotZero chip.name index)
  let mut sent := []
  for send in chip.sends do
    let enabled := send.enable.denote row.assignment
    if enabled = 1 then sent := sent ++ [send.message row.assignment]
  let received := Message.mk chip.name (row.values.take chip.arity) (row.assignment chip.output)
  return (received, sent)

/--
Check exact channel balance, including multiplicities, with one external request.
Rows are an unordered witness collection; no call stack or execution order is assumed.
-/
def System.check [Field F] [DecidableEq F] (system : System F)
    (entry : Message F) (rows : List (Row F)) : Except WitnessError Unit := do
  let mut seen := []
  for chip in system.chips do
    if chip.name ∈ seen then throw (.duplicateChip chip.name)
    seen := chip.name :: seen
    if !chip.wellFormed then throw (.invalidLayout chip.name)
  let mut received := []
  let mut sent := [entry]
  for row in rows do
    let some chip := system.findChip? row.chip | throw (.unknownChip row.chip)
    let (input, output) ← chip.checkRow row
    received := input :: received
    sent := output ++ sent
  if sent.Perm received then pure () else throw .unbalancedMessages

/-- The executable witness check defines acceptance of the abstract channel model. -/
def System.Accepts [Field F] [DecidableEq F] (system : System F)
    (entry : Message F) (rows : List (Row F)) : Prop :=
  system.check entry rows = .ok ()

/-- A selected inverse equation rules out a zero denominator. -/
theorem inverse_nonzero [Field F] {denominator inverse : F}
    (h : denominator * inverse - 1 = 0) : denominator ≠ 0 := by
  intro zero
  simp [zero] at h

theorem inverse_eq [Field F] {denominator inverse : F}
    (h : denominator * inverse - 1 = 0) : inverse = denominator⁻¹ := by
  have product : denominator * inverse = 1 := sub_eq_zero.mp h
  have nonzero := inverse_nonzero h
  calc
    inverse = (denominator⁻¹ * denominator) * inverse := by
      rw [inv_mul_cancel₀ nonzero, one_mul]
    _ = denominator⁻¹ * (denominator * inverse) := mul_assoc _ _ _
    _ = denominator⁻¹ := by rw [product, mul_one]

theorem selector_boolean [Field F] {selector : F}
    (h : selector * (selector - 1) = 0) : selector = 0 ∨ selector = 1 := by
  rcases mul_eq_zero.mp h with zero | one
  · exact Or.inl zero
  · exact Or.inr (sub_eq_zero.mp one)

end Aiur.Scalar.Circuit
