import Aiur.Tuple.AST
import Aiur.Scalar.Circuit.Basic

namespace Aiur.Tuple.Circuit

abbrev Var := Scalar.Circuit.Var
abbrev ArithExpr := Scalar.Circuit.ArithExpr
abbrev Constraint := Scalar.Circuit.Constraint
abbrev Satisfies [Field F] (constraints : List (Constraint F)) (assignment : Var → F) :=
  Scalar.Circuit.Satisfies constraints assignment
abbrev Row := Scalar.Circuit.Row

namespace ArithExpr
export Aiur.Scalar.Circuit.ArithExpr (const var add sub mul)
abbrev denote [Field F] (assignment : Var → F) (expr : ArithExpr F) : F :=
  Scalar.Circuit.ArithExpr.denote assignment expr
abbrev inBounds (numVars : Nat) (expr : ArithExpr F) : Bool :=
  Scalar.Circuit.ArithExpr.inBounds numVars expr
end ArithExpr

namespace Row
abbrev assignment [Zero F] (row : Row F) (id : Var) : F :=
  Scalar.Circuit.Row.assignment row id
end Row

/-- Tuple shape and every leaf are part of a call's claim. -/
structure Message (F : Type) where
  channel : String
  args : List (Value F)
  result : Value F
  deriving Repr, BEq, DecidableEq

structure Send (F : Type) where
  channel : String
  args : List (Value (ArithExpr F))
  result : Value Var
  enable : ArithExpr F
  deriving Repr, BEq

def Send.message [Field F] (send : Send F) (assignment : Var → F) : Message F :=
  ⟨send.channel, send.args.map (Value.map (ArithExpr.denote assignment)), send.result.map assignment⟩

def Send.inBounds (numVars : Nat) (send : Send F) : Bool :=
  send.result.flatten.all (· < numVars) && send.enable.inBounds numVars &&
    (send.args.flatMap Value.flatten).all (ArithExpr.inBounds numVars)

/-- Structure lives in the interface; rows and equations contain only field elements. -/
structure Chip (F : Type) where
  name : String
  inputs : List (Value Var)
  output : Value Var
  numVars : Nat
  constraints : List (Constraint F)
  sends : List (Send F)
  deriving Repr, BEq

def Chip.wellFormed (chip : Chip F) : Bool :=
  (chip.inputs.flatMap Value.flatten ++ chip.output.flatten).all (· < chip.numVars) &&
    chip.constraints.all (ArithExpr.inBounds chip.numVars) &&
    chip.sends.all (Send.inBounds chip.numVars)

def Chip.ValidRow [Field F] (chip : Chip F) (row : Row F) : Prop :=
  chip.wellFormed = true ∧ row.values.length = chip.numVars ∧
    Satisfies chip.constraints row.assignment

def Chip.receive [Field F] (chip : Chip F) (row : Row F) : Message F :=
  ⟨chip.name, chip.inputs.map (Value.map row.assignment), chip.output.map row.assignment⟩

def Chip.premises [Field F] [DecidableEq F] (chip : Chip F) (row : Row F) : List (Message F) :=
  chip.sends.filterMap fun send =>
    if send.enable.denote row.assignment = 1 then some (send.message row.assignment) else none

structure System (F : Type) where
  chips : List (Chip F)
  deriving Repr, BEq

def System.findChip? (system : System F) (name : String) : Option (Chip F) :=
  system.chips.find? (·.name == name)

abbrev WitnessError := Scalar.Circuit.WitnessError

def Chip.checkRow [Field F] [DecidableEq F] (chip : Chip F) (row : Row F) :
    Except WitnessError (Message F × List (Message F)) := do
  if !chip.wellFormed then throw (.invalidLayout chip.name)
  if row.values.length != chip.numVars then
    throw (.wrongRowSize chip.name chip.numVars row.values.length)
  for (polynomial, index) in chip.constraints.zipIdx do
    if polynomial.denote row.assignment ≠ 0 then throw (.constraintNotZero chip.name index)
  return (chip.receive row, chip.premises row)

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

def System.Accepts [Field F] [DecidableEq F] (system : System F)
    (entry : Message F) (rows : List (Row F)) : Prop := system.check entry rows = .ok ()

end Aiur.Tuple.Circuit
