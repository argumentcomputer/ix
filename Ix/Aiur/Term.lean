module
public import Std.Data.HashSet.Basic
public import Ix.Aiur.Goldilocks
public import Ix.IndexMap

public section

namespace Aiur

inductive Local
  | str : String → Local
  | idx : Nat → Local
  deriving Repr, BEq, Inhabited, Hashable

structure Global where
  toName : Lean.Name
  deriving Repr, BEq, Inhabited

instance : EquivBEq Global where
  symm {_ _} h := by rw [BEq.beq] at h ⊢; exact BEq.symm h
  trans {_ _ _} h₁ h₂ := by rw [BEq.beq] at h₁ h₂ ⊢; exact BEq.trans h₁ h₂
  rfl {_} := by rw [BEq.beq]; apply BEq.rfl

instance : Hashable Global where
  hash a := hash a.toName

instance : LawfulHashable Global where
  hash_eq a b h := LawfulHashable.hash_eq a.toName b.toName h

instance : ToString Global where
  toString g := g.toName.toString

def Global.init (limb : String) : Global :=
  ⟨.mkSimple limb⟩

def Global.pushNamespace (global : Global) (limb : String) : Global :=
  ⟨global.toName.mkStr limb⟩

def Global.popNamespace (global : Global) : Option (String × Global) :=
  match global.toName with
  | .str tail head => some (head, ⟨tail⟩)
  | _ => none

inductive Pattern
  | var : Local → Pattern
  | wildcard : Pattern
  | ref : Global → List Pattern → Pattern
  | field : G → Pattern
  | tuple : Array Pattern → Pattern
  | array : Array Pattern → Pattern
  | or : Pattern → Pattern → Pattern
  | pointer : Pattern → Pattern
  deriving Repr, BEq, Hashable, Inhabited

inductive Typ where
  | unit
  | field
  | tuple : Array Typ → Typ
  | array : Typ → Nat → Typ
  | pointer : Typ → Typ
  | ref : Global → Typ
  | function : List Typ → Typ → Typ
  deriving Repr, BEq, Hashable, Inhabited

mutual

inductive Term
  | unit
  | var : Local → Term
  -- | unsafeCast : Term → Typ → Term
  | ref : Global → Term
  | data : Data → Term
  | ret : Term → Term
  | let : Pattern → Term → Term → Term
  | match : Term → List (Pattern × Term) → Term
  | app : Global → List Term → (unconstrained : Bool) → Term
  | add : Term → Term → Term
  | sub : Term → Term → Term
  | mul : Term → Term → Term
  | eqZero : Term → Term
  | proj : Term → Nat → Term
  | get : Term → Nat → Term
  | slice : Term → Nat → Nat → Term
  | set : Term → Nat → Term → Term
  | store : Term → Term
  | load : Term → Term
  | ptrVal : Term → Term
  | ann : Typ → Term → Term
  | assertEq : Term → Term → (ret : Term) → Term
  | ioGetInfo : (key : Term) → Term
  | ioSetInfo : (key : Term) → (idx : Term) → (len : Term) → (ret : Term) → Term
  | ioRead : (idx : Term) → (len : Nat) → Term
  | ioWrite : (data : Term) → (ret : Term) → Term
  | u8BitDecomposition : Term → Term
  | u8ShiftLeft : Term → Term
  | u8ShiftRight : Term → Term
  | u8Xor : Term → Term → Term
  | u8Add : Term → Term → Term
  | u8Sub : Term → Term → Term
  | u8And : Term → Term → Term
  | u8Or : Term → Term → Term
  | u8LessThan : Term → Term → Term
  | u32LessThan : Term → Term → Term
  | debug : String → Option Term → Term → Term
  deriving Repr, BEq, Hashable, Inhabited

inductive Data
  | field : G → Data
  | tuple : Array Term → Data
  | array : Array Term → Data
  deriving Repr

end

structure Constructor where
  nameHead : String
  argTypes : List Typ
  deriving Repr, BEq, Inhabited

structure DataType where
  name : Global
  constructors : List Constructor
  deriving Repr, BEq, Inhabited

structure TypeAlias where
  name : Global
  expansion : Typ
  deriving Repr, BEq, Inhabited

structure Function where
  name : Global
  inputs : List (Local × Typ)
  output : Typ
  body : Term
  entry : Bool
  deriving Repr

structure Toplevel where
  dataTypes : Array DataType
  typeAliases : Array TypeAlias
  functions : Array Function
  deriving Repr

def Toplevel.getFuncIdx (toplevel : Toplevel) (funcName : Lean.Name) : Option Nat := do
  toplevel.functions.findIdx? fun function => function.name.toName == funcName

def Toplevel.merge (x y : Toplevel) : Except Global Toplevel := do
  let ⟨xDataTypes, xTypeAliases, xFunctions⟩ := x
  let ⟨yDataTypes, yTypeAliases, yFunctions⟩ := y
  let mut globals : Std.HashSet Global := ∅
  let mut dataTypes := .emptyWithCapacity (xDataTypes.size + yDataTypes.size)
  let mut typeAliases := .emptyWithCapacity (xTypeAliases.size + yTypeAliases.size)
  let mut functions := .emptyWithCapacity (xFunctions.size + yFunctions.size)
  for dtSet in [xDataTypes, yDataTypes] do
    for dt in dtSet do
      if globals.contains dt.name then throw dt.name
      globals := globals.insert dt.name
      dataTypes := dataTypes.push dt
  for taSet in [xTypeAliases, yTypeAliases] do
    for ta in taSet do
      if globals.contains ta.name then throw ta.name
      globals := globals.insert ta.name
      typeAliases := typeAliases.push ta
  for fSet in [xFunctions, yFunctions] do
    for f in fSet do
      if globals.contains f.name then throw f.name
      globals := globals.insert f.name
      functions := functions.push f
  pure ⟨dataTypes, typeAliases, functions⟩

inductive Declaration
  | function : Function → Declaration
  | dataType : DataType → Declaration
  | constructor : DataType → Constructor → Declaration
  deriving Repr, Inhabited

abbrev Decls := IndexMap Global Declaration

end Aiur

end
