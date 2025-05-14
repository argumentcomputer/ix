import Std.Data.HashMap
open Std

namespace Aiur

inductive Local
  | str : String → Local
  | idx : Nat → Local
  deriving Repr, BEq, Hashable

structure Global where
  toName : Lean.Name
  deriving Repr, BEq, Hashable, Inhabited

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

inductive Primitive
  | u1 : Bool → Primitive
  | u8 : UInt8 → Primitive
  | u16 : UInt16 → Primitive
  | u32 : UInt32 → Primitive
  | u64 : UInt64 → Primitive
  deriving Repr, BEq, Hashable

def Primitive.toU64 : Primitive → UInt64
| .u1 n => n.toUInt64
| .u8 n => n.toUInt64
| .u16 n => n.toUInt64
| .u32 n => n.toUInt64
| .u64 n => n

inductive Pattern
  | var : Local → Pattern
  | wildcard : Pattern
  | ref : Global → List Pattern → Pattern
  | primitive : Primitive → Pattern
  | tuple : Array Pattern → Pattern
  | or : Pattern → Pattern → Pattern
  deriving Repr, BEq, Hashable, Inhabited

inductive PrimitiveType
  | u1 | u8 | u16 | u32 | u64
  deriving Repr, BEq, Hashable

inductive Typ where
  | primitive : PrimitiveType → Typ
  | tuple : Array Typ → Typ
  | pointer : Typ → Typ
  | dataType : Global → Typ
  | function : List Typ → Typ → Typ
  deriving Repr, BEq, Hashable, Inhabited

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
  deriving Repr, BEq, Hashable, Inhabited

inductive Data
  | primitive : Primitive → Data
  | tuple : Array Term → Data
  deriving Repr

end

inductive ContextualType
  | evaluates : Typ → ContextualType
  | escapes : ContextualType
  deriving Repr, BEq, Inhabited

def ContextualType.unwrap : ContextualType → Typ
| .escapes => panic! "term should not escape"
| .evaluates typ => typ

def ContextualType.unwrapOr : ContextualType → Typ → Typ
| .escapes => fun typ => typ
| .evaluates typ => fun _ => typ

mutual
inductive TypedTermInner
  | var : Local → TypedTermInner
  | ref : Global → TypedTermInner
  | data : TypedData → TypedTermInner
  | ret : TypedTerm → TypedTermInner
  | let : Pattern → TypedTerm → TypedTerm → TypedTermInner
  | match : TypedTerm → List (Pattern × TypedTerm) → TypedTermInner
  | if : TypedTerm → TypedTerm → TypedTerm → TypedTermInner
  | app : Global → List TypedTerm → TypedTermInner
  | preimg : Global → TypedTerm → TypedTermInner
  | xor : TypedTerm → TypedTerm → TypedTermInner
  | and : TypedTerm → TypedTerm → TypedTermInner
  | get : TypedTerm → Nat → TypedTermInner
  | slice : TypedTerm → Nat → Nat → TypedTermInner
  | store : TypedTerm → TypedTermInner
  | load : TypedTerm → TypedTermInner
  | pointerAsU64 : TypedTerm → TypedTermInner
  deriving Repr, Inhabited

structure TypedTerm where
  typ : ContextualType
  inner : TypedTermInner
  deriving Repr, Inhabited

inductive TypedData
  | primitive : Primitive → TypedData
  | tuple : Array TypedTerm → TypedData
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

structure Function where
  name : Global
  inputs : List (Local × Typ)
  output : Typ
  body : Term
  deriving Repr

structure Toplevel where
  dataTypes : List DataType
  functions : List Function
  deriving Repr

inductive Declaration
  | function : Function → Declaration
  | dataType : DataType → Declaration
  | constructor : DataType → Constructor → Declaration
  deriving Repr, Inhabited

abbrev Decls := HashMap Global Declaration

structure TypedFunction where
  name : Global
  inputs : List (Local × Typ)
  output : Typ
  body : TypedTerm
  deriving Repr

inductive TypedDeclaration
  | function : TypedFunction → TypedDeclaration
  | dataType : DataType → TypedDeclaration
  | constructor : DataType → Constructor → TypedDeclaration
  deriving Repr, Inhabited

abbrev TypedDecls := HashMap Global TypedDeclaration

mutual

partial def Typ.size (decls : TypedDecls) (visited : HashMap Global Unit := {}) : Typ → Nat
  | Typ.primitive .. => 1
  | Typ.pointer .. => 1
  | Typ.function .. => 1
  | Typ.tuple ts => ts.foldl (init := 0) (fun acc t => acc + t.size decls visited)
  | Typ.dataType g => match decls.get! g with
    | .dataType data => data.size decls visited
    | _ => panic! "impossible case"

partial def Constructor.size (decls : TypedDecls) (visited : HashMap Global Unit := {}) (c : Constructor) : Nat :=
  c.argTypes.foldl (λ acc t => acc + t.size decls visited) 0

partial def DataType.size (dt : DataType) (decls : TypedDecls) (visited : HashMap Global Unit := {}) : Nat :=
  if visited.contains dt.name then
    panic! s!"cycle detected at datatype `{dt.name}`"
  else
    let visited := visited.insert dt.name ()
    let ctorSizes := dt.constructors.map (Constructor.size decls visited)
    let maxFields := ctorSizes.foldl max 0
    maxFields + 1
end

end Aiur
