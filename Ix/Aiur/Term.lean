import Std.Data.HashMap

namespace Aiur

inductive Local
  | str : String → Local
  | idx : Nat → Local
  deriving BEq, Hashable

structure Global where
  toName : Lean.Name
  deriving BEq, Hashable, Inhabited

def Global.init (limb : String) : Global :=
  ⟨.mkSimple limb⟩

def Global.pushNamespace (global : Global) (limb : String) : Global :=
  ⟨global.toName.mkStr limb⟩

def Global.popNamespace (global : Global) : Option (String × Global) :=
  match global.toName with
  | .str tail head => some (head, ⟨tail⟩)
  | _ => none

inductive Primitive
  | u1 : Bool → Primitive
  | u8 : UInt8 → Primitive
  | u16 : UInt16 → Primitive
  | u32 : UInt32 → Primitive
  | u64 : UInt64 → Primitive
  deriving BEq, Hashable

inductive Pattern
  | var : Local → Pattern
  | wildcard : Pattern
  | ref : Global → List Pattern → Pattern
  | primitive : Primitive → Pattern
  | tuple : List Pattern → Pattern
  | or : Pattern → Pattern → Pattern
  deriving BEq, Hashable, Inhabited

inductive PrimitiveType
  | u1 | u8 | u16 | u32 | u64
  deriving BEq, Hashable

inductive Typ where
  | primitive : PrimitiveType → Typ
  | tuple : List Typ → Typ
  | pointer : Typ → Typ
  | dataType : Global → Typ
  | function : List Typ → Typ → Typ
  deriving BEq, Hashable, Inhabited

mutual

inductive Term
  | var : Local → Term
  | ref : Global → Term
  | data : Data → Term
  | ret : Term → Term
  | let : Pattern → Term → Term → Term
  | match : Term → List (Pattern × Term) → Term
  | if : Term → Term → Term → Term
  | app : Global → List Term → Term
  | preimg : Global → Term → Term
  | xor : Term → Term → Term
  | and : Term → Term → Term
  | get : Term → Nat → Term
  | slice : Term → Nat → Nat → Term
  | store : Term → Term
  | load : Term → Term
  | pointerAsU64 : Term → Term
  | ann : Typ → Term → Term
  deriving BEq, Hashable, Inhabited

inductive Data
  | primitive : Primitive → Data
  | tuple : List Term → Data

end

structure Constructor where
  nameHead : String
  argTypes : List Typ
  deriving BEq, Inhabited

structure DataType where
  name : Global
  constructors : List Constructor
  deriving BEq, Inhabited

structure Function where
  name : Global
  inputs : List (Local × Typ)
  output : Typ
  body : Term

structure Toplevel where
  dataTypes : List DataType
  functions : List Function

inductive Declaration
  | function : Function → Declaration
  | dataType : DataType → Declaration
  | constructor : DataType → Constructor → Declaration

abbrev Decls := Std.HashMap Global Declaration

end Aiur
