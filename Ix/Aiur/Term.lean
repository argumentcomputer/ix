import Std.Data.HashSet.Basic
import Ix.Aiur.Goldilocks
import Ix.IndexMap

namespace Aiur

inductive Local
  | str : String → Local
  | idx : Nat → Local
  deriving Repr, BEq, Hashable

structure Global where
  toName : Lean.Name
  deriving Repr, BEq, Inhabited

instance : EquivBEq Global where
  symm {_ _} h := by rw [BEq.beq] at h ⊢; exact BEq.symm h
  trans {_ _ _} h₁ h₂ := by rw [BEq.beq] at h₁ h₂ ⊢; exact BEq.trans h₁ h₂
  refl {_} := by rw [BEq.beq]; apply BEq.refl

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
  deriving Repr, BEq, Hashable, Inhabited

inductive Typ where
  | field
  | tuple : Array Typ → Typ
  | array : Typ → Nat → Typ
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
  | app : Global → List Term → Term
  | add : Term → Term → Term
  | sub : Term → Term → Term
  | mul : Term → Term → Term
  | proj : Term → Nat → Term
  | get : Term → Nat → Term
  | slice : Term → Nat → Nat → Term
  | store : Term → Term
  | load : Term → Term
  | ptrVal : Term → Term
  | ann : Typ → Term → Term
  deriving Repr, BEq, Hashable, Inhabited

inductive Data
  | field : G → Data
  | tuple : Array Term → Data
  | array : Array Term → Data
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
  | app : Global → List TypedTerm → TypedTermInner
  | add : TypedTerm → TypedTerm → TypedTermInner
  | sub : TypedTerm → TypedTerm → TypedTermInner
  | mul : TypedTerm → TypedTerm → TypedTermInner
  | proj : TypedTerm → Nat → TypedTermInner
  | get : TypedTerm → Nat → TypedTermInner
  | slice : TypedTerm → Nat → Nat → TypedTermInner
  | store : TypedTerm → TypedTermInner
  | load : TypedTerm → TypedTermInner
  | ptrVal : TypedTerm → TypedTermInner
  deriving Repr, Inhabited

structure TypedTerm where
  typ : ContextualType
  inner : TypedTermInner
  deriving Repr, Inhabited

inductive TypedData
  | field : G → TypedData
  | tuple : Array TypedTerm → TypedData
  | array : Array TypedTerm → TypedData
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

def Toplevel.getFuncIdx (toplevel : Toplevel) (funcName : Lean.Name) : Option Nat := do
  toplevel.functions.findIdx? fun function => function.name.toName == funcName

inductive Declaration
  | function : Function → Declaration
  | dataType : DataType → Declaration
  | constructor : DataType → Constructor → Declaration
  deriving Repr, Inhabited

abbrev Decls := IndexMap Global Declaration

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

abbrev TypedDecls := IndexMap Global TypedDeclaration

mutual

open Std (HashSet)

partial def Typ.size (decls : TypedDecls) (visited : HashSet Global := {}) : Typ → Nat
  | .field .. => 1
  | .pointer .. => 1
  | .function .. => 1
  | .tuple ts => ts.foldl (init := 0) (fun acc t => acc + t.size decls visited)
  | .array t n => n * t.size decls visited
  | .dataType g => match decls.getByKey g with
    | some (.dataType data) => data.size decls visited
    | _ => panic! "impossible case"

partial def Constructor.size (decls : TypedDecls) (visited : HashSet Global := {}) (c : Constructor) : Nat :=
  c.argTypes.foldl (λ acc t => acc + t.size decls visited) 0

partial def DataType.size (dt : DataType) (decls : TypedDecls) (visited : HashSet Global := {}) : Nat :=
  if visited.contains dt.name then
    panic! s!"cycle detected at datatype `{dt.name}`"
  else
    let visited := visited.insert dt.name
    let ctorSizes := dt.constructors.map (Constructor.size decls visited)
    let maxFields := ctorSizes.foldl max 0
    maxFields + 1
end

end Aiur
