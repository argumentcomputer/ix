import Std.Data.HashMap
open Std

namespace Aiur

inductive Local
  | str : String → Local
  | idx : Nat → Local
  deriving BEq, Hashable

structure Global where
  toName : Lean.Name
  deriving BEq, Hashable, Inhabited

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

inductive ContextualType
  | evaluates : Typ → ContextualType
  | escapes : ContextualType
  deriving BEq, Inhabited

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
  deriving Inhabited

structure TypedTerm where
  typ : ContextualType
  inner : TypedTermInner
  deriving Inhabited

inductive TypedData
  | primitive : Primitive → TypedData
  | tuple : List TypedTerm → TypedData
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
  deriving Inhabited

abbrev Decls := HashMap Global Declaration

mutual

partial def Typ.size (decls : Decls) (visited : HashMap Global Unit := {}) : Typ → Nat
  | Typ.primitive .. => 1
  | Typ.pointer .. => 1
  | Typ.function .. => 1
  | Typ.tuple ts => ts.foldl (init := 0) (fun acc t => acc + t.size decls visited)
  | Typ.dataType g => match decls.get! g with
    | .dataType data => data.size decls visited
    | _ => panic! "impossible case"

partial def Constructor.size (decls : Decls) (visited : HashMap Global Unit := {}) (c : Constructor) : Nat :=
  c.argTypes.foldl (λ acc t => acc + t.size decls visited) 0

partial def DataType.size (dt : DataType) (decls : Decls) (visited : HashMap Global Unit := {}) : Nat :=
  if visited.contains dt.name then
    panic! s!"cycle detected at datatype `{dt.name}`"
  else
    let visited := visited.insert dt.name ()
    let ctorSizes := dt.constructors.map (Constructor.size decls visited)
    let maxFields := ctorSizes.foldl max 0
    maxFields + 1
end

end Aiur
