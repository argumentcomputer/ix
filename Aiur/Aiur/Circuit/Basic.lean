import Aiur.AST
import Aiur.Memory
import Aiur.Wire
import Aiur.Scalar.Circuit.Basic
import Aiur.Circuit.Balance

namespace Aiur.Circuit

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
  args : List (WireValue F)
  result : WireValue F
  deriving Repr, BEq, DecidableEq

abbrev CallRelation (F : Type) := String → List (WireValue F) → WireValue F → Prop
abbrev WireEnvironment (F : Type) := List (String × WireValue F)

structure Send (F : Type) where
  channel : String
  args : List (WireValue (ArithExpr F))
  result : WireValue Var
  enable : ArithExpr F
  deriving Repr, BEq

def Send.message [Field F] (send : Send F) (assignment : Var → F) : Message F :=
  ⟨send.channel, send.args.map (WireValue.map (ArithExpr.denote assignment)), send.result.map assignment⟩

def Send.inBounds (numVars : Nat) (send : Send F) : Bool :=
  send.result.words.all (· < numVars) && send.enable.inBounds numVars &&
    (send.args.flatMap WireValue.words).all (ArithExpr.inBounds numVars)

/-- Both store and load require this same cell in the shared ROM. -/
structure MemoryLookup (F : Type) where
  address : ArithExpr F
  value : WireValue (ArithExpr F)
  enable : ArithExpr F
  deriving Repr, BEq

def MemoryLookup.inBounds (numVars : Nat) (lookup : MemoryLookup F) : Bool :=
  lookup.address.inBounds numVars && lookup.enable.inBounds numVars &&
    lookup.value.words.all (ArithExpr.inBounds numVars)

def MemoryLookup.Valid [Field F] (rom : WireROM F) (assignment : Var → F)
    (lookup : MemoryLookup F) : Prop :=
  lookup.enable.denote assignment = 1 →
    (lookup.address.denote assignment, lookup.value.map (ArithExpr.denote assignment)) ∈ rom.entries

/-- Structure lives in the interface; rows and equations contain only field elements. -/
structure Chip (F : Type) where
  name : String
  inputs : List (WireValue Var)
  /-- The provided result can reuse columns or contain expressions and constants. -/
  output : WireValue (ArithExpr F)
  numVars : Nat
  constraints : List (Constraint F)
  sends : List (Send F)
  memory : List (MemoryLookup F)
  deriving Repr, BEq

def Chip.wellFormed (chip : Chip F) : Bool :=
  (chip.inputs.flatMap WireValue.words).all (· < chip.numVars) &&
    chip.output.words.all (ArithExpr.inBounds chip.numVars) &&
    chip.constraints.all (ArithExpr.inBounds chip.numVars) &&
    chip.sends.all (Send.inBounds chip.numVars) &&
    chip.memory.all (MemoryLookup.inBounds chip.numVars)

def Chip.ValidRow [Field F] (chip : Chip F) (rom : WireROM F) (row : Row F) : Prop :=
  chip.wellFormed = true ∧ row.values.length = chip.numVars ∧
    Satisfies chip.constraints row.assignment ∧
    ∀ lookup ∈ chip.memory, lookup.Valid rom row.assignment

def Chip.receive [Field F] (chip : Chip F) (row : Row F) : Message F :=
  ⟨chip.name, chip.inputs.map (WireValue.map row.assignment),
    chip.output.map (ArithExpr.denote row.assignment)⟩

def Chip.premises [Field F] [DecidableEq F] (chip : Chip F) (row : Row F) : List (Message F) :=
  chip.sends.filterMap fun send =>
    if send.enable.denote row.assignment = 1 then some (send.message row.assignment) else none

structure System (F : Type) where
  chips : List (Chip F)
  enums : Declarations := []
  tables : List (Table F) := []
  maps : List MapDecl := []
  deriving Repr, BEq

def System.findChip? (system : System F) (name : String) : Option (Chip F) :=
  system.chips.find? (·.name == name)

def encodeMapEntry [NatCast F] [Zero F] (decls : Declarations) (name : String)
    (entry : MapEntry F) : Option (Message F) := do
  let args ← entry.args.mapM (fun value => value.toValue.encode decls)
  let result ← entry.result.toValue.encode decls
  return ⟨name, args, result⟩

/-- The finite membership relation supplied by the shared precommitted traces. -/
def System.mapClaims [NatCast F] [Zero F] (system : System F) : List (Message F) :=
  let data : Program F := {
    functions := []
    enums := system.enums
    tables := system.tables
    maps := system.maps
  }
  system.maps.flatMap fun map =>
    (data.mapEntries map).filterMap (encodeMapEntry system.enums map.name)

def System.MapClaim [NatCast F] [Zero F] (system : System F) (message : Message F) : Prop :=
  message ∈ system.mapClaims

instance [NatCast F] [Zero F] [DecidableEq F] (system : System F) (message : Message F) :
    Decidable (system.MapClaim message) := by
  unfold System.MapClaim
  apply decidable_of_iff (system.mapClaims.any (fun claim => decide (claim = message)) = true)
  constructor
  · intro found
    obtain ⟨claim, member, same⟩ := List.any_eq_true.mp found
    have same : claim = message := of_decide_eq_true same
    simpa only [same] using member
  · intro member
    exact List.any_eq_true.mpr ⟨message, member, by simp⟩

inductive WitnessError where
  | duplicateChip (chip : String)
  | invalidLayout (chip : String)
  | wrongRowSize (chip : String) (expected actual : Nat)
  | constraintNotZero (chip : String) (index : Nat)
  | unknownChip (chip : String)
  | unbalancedMessages
  | pointerEntryArgument
  | malformedEntry
  | invalidROM
  | missingCell (chip : String) (index : Nat)
  deriving Repr, BEq, DecidableEq

def Chip.checkRow [Field F] [DecidableEq F] (chip : Chip F) (rom : WireROM F) (row : Row F) :
    Except WitnessError (Message F × List (Message F)) := do
  if !chip.wellFormed then throw (.invalidLayout chip.name)
  if row.values.length != chip.numVars then
    throw (.wrongRowSize chip.name chip.numVars row.values.length)
  let _ ← chip.constraints.zipIdx.mapM fun (polynomial, index) =>
    if polynomial.denote row.assignment ≠ 0 then
      throw (.constraintNotZero chip.name index) else pure (() : Unit)
  let _ ← chip.memory.zipIdx.mapM fun (lookup, index) => do
    if lookup.enable.denote row.assignment = 1 then
      if !rom.entries.any (fun entry => decide (entry =
          (lookup.address.denote row.assignment,
            lookup.value.map (ArithExpr.denote row.assignment)))) then
        throw (.missingCell chip.name index)
    pure (() : Unit)
  return (chip.receive row, chip.premises row)

/-- Check the whole chip namespace, including chips unused by a trace. -/
def checkChips (seen : List String) : List (Chip F) → Except WitnessError Unit
  | [] => .ok ()
  | chip :: chips => do
      if chip.name ∈ seen then throw (.duplicateChip chip.name)
      if !chip.wellFormed then throw (.invalidLayout chip.name)
      checkChips (chip.name :: seen) chips

/-- Checks shared by the unit and memoized trace checkers. -/
def System.checkContext [Field F] [DecidableEq F] (system : System F)
    (rom : WireROM F) (entry : Message F) : Except WitnessError Unit := do
  let _ ← entry.args.mapM fun argument => do
    if (argument.decode system.enums).isNone then throw .malformedEntry
    if !argument.type.pointerFree system.enums then throw .pointerEntryArgument
    pure (() : Unit)
  if (entry.result.decode system.enums).isNone then throw .malformedEntry
  if ¬rom.Valid then throw .invalidROM
  checkChips [] system.chips

/-- A row provides its conclusion with an exact integer weight. Its active
premises always have weight one, including when the provide weight is zero. -/
structure WeightedRow (F : Type) where
  row : Row F
  multiplicity : Int
  deriving Repr, BEq

def System.inspectRow [Field F] [DecidableEq F] (system : System F)
    (rom : WireROM F) (row : Row F) : Except WitnessError (RuleClaims (Message F)) := do
  let some chip := system.findChip? row.chip | throw (.unknownChip row.chip)
  chip.checkRow rom row

def System.inspectRows [Field F] [DecidableEq F] (system : System F)
    (rom : WireROM F) (rows : List (Row F)) : Except WitnessError (List (RuleClaims (Message F))) :=
  rows.mapM (system.inspectRow rom)

def System.inspectWeightedRows [Field F] [DecidableEq F] (system : System F)
    (rom : WireROM F) (rows : List (WeightedRow F)) :
    Except WitnessError (List (RuleClaims (Message F) × Int)) :=
  rows.mapM fun weighted => do
    let claims ← system.inspectRow rom weighted.row
    return (claims, weighted.multiplicity)

/-- Unordered, exact integer balance; every provided and required occurrence has weight one. -/
def System.check [Field F] [DecidableEq F] (system : System F)
    (rom : WireROM F) (entry : Message F) (rows : List (Row F)) : Except WitnessError Unit := do
  system.checkContext rom entry
  let rules ← system.inspectRows rom rows
  let ledger := Balance.accumulator (fun claim => decide (system.MapClaim claim)) entry
    (rules.map fun rule => (rule, 1))
  if ledger.isZero then pure () else throw .unbalancedMessages

/-- The LogUp-style abstraction: arbitrary integer provide weights, unit requires.
This checks exact claims and integers, without a cryptographic accumulator or a field cast. -/
def System.checkMemo [Field F] [DecidableEq F] (system : System F)
    (rom : WireROM F) (entry : Message F) (rows : List (WeightedRow F)) : Except WitnessError Unit := do
  system.checkContext rom entry
  let rules ← system.inspectWeightedRows rom rows
  let ledger := Balance.accumulator (fun claim => decide (system.MapClaim claim)) entry rules
  if ledger.isZero then pure () else throw .unbalancedMessages

def System.Accepts [Field F] [DecidableEq F] (system : System F)
    (rom : WireROM F) (entry : Message F) (rows : List (Row F)) : Prop := system.check rom entry rows = .ok ()

def System.AcceptsMemo [Field F] [DecidableEq F] (system : System F)
    (rom : WireROM F) (entry : Message F) (rows : List (WeightedRow F)) : Prop :=
  system.checkMemo rom entry rows = .ok ()

end Aiur.Circuit
