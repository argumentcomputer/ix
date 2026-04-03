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

inductive Typ where
  | unit
  | field
  | tuple : Array Typ → Typ
  | array : Typ → Nat → Typ
  | pointer : Typ → Typ
  | typeRef : Global → Typ
  | function : List Typ → Typ → Typ
  | typeVar : String → Typ
  | templateApp : Global → Array Typ → Typ
  | unif : Nat → Typ
  deriving Repr, BEq, Hashable, Inhabited

inductive Pattern
  | var : Local → Pattern
  | wildcard : Pattern
  | ref : Global → List Pattern → Pattern
  | field : G → Pattern
  | tuple : Array Pattern → Pattern
  | array : Array Pattern → Pattern
  | or : Pattern → Pattern → Pattern
  | pointer : Pattern → Pattern
  | templateRef : Global → Array Typ → String → List Pattern → Pattern
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
  | templateApp : Global → Array Typ → Option String → List Term → Bool → Term
  deriving Repr, BEq, Hashable, Inhabited

inductive Data
  | field : G → Data
  | tuple : Array Term → Data
  | array : Array Term → Data
  deriving Repr

end

mutual
inductive TypedTermInner
  | unit
  | var : Local → TypedTermInner
  -- | unsafeCast : TypedTermInner → Typ → TypedTermInner
  | ref : Global → TypedTermInner
  | data : TypedData → TypedTermInner
  | ret : TypedTerm → TypedTermInner
  | let : Pattern → TypedTerm → TypedTerm → TypedTermInner
  | match : TypedTerm → List (Pattern × TypedTerm) → TypedTermInner
  | app : Global → List TypedTerm → (unconstrained : Bool) → TypedTermInner
  | add : TypedTerm → TypedTerm → TypedTermInner
  | sub : TypedTerm → TypedTerm → TypedTermInner
  | mul : TypedTerm → TypedTerm → TypedTermInner
  | eqZero : TypedTerm → TypedTermInner
  | proj : TypedTerm → Nat → TypedTermInner
  | get : TypedTerm → Nat → TypedTermInner
  | slice : TypedTerm → Nat → Nat → TypedTermInner
  | set : TypedTerm → Nat → TypedTerm → TypedTermInner
  | store : TypedTerm → TypedTermInner
  | load : TypedTerm → TypedTermInner
  | ptrVal : TypedTerm → TypedTermInner
  | assertEq : TypedTerm → TypedTerm → TypedTerm → TypedTermInner
  | ioGetInfo : TypedTerm → TypedTermInner
  | ioSetInfo : TypedTerm → TypedTerm → TypedTerm → TypedTerm → TypedTermInner
  | ioRead : TypedTerm → Nat → TypedTermInner
  | ioWrite : TypedTerm → TypedTerm → TypedTermInner
  | u8BitDecomposition : TypedTerm → TypedTermInner
  | u8ShiftLeft : TypedTerm → TypedTermInner
  | u8ShiftRight : TypedTerm → TypedTermInner
  | u8Xor : TypedTerm → TypedTerm → TypedTermInner
  | u8Add : TypedTerm → TypedTerm → TypedTermInner
  | u8Sub : TypedTerm → TypedTerm → TypedTermInner
  | u8And : TypedTerm → TypedTerm → TypedTermInner
  | u8Or : TypedTerm → TypedTerm → TypedTermInner
  | u8LessThan : TypedTerm → TypedTerm → TypedTermInner
  | u32LessThan : TypedTerm → TypedTerm → TypedTermInner
  | debug : String → Option TypedTerm → TypedTerm → TypedTermInner
  deriving Repr, Inhabited

structure TypedTerm where
  typ : Typ
  inner : TypedTermInner
  escapes : Bool
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
  deriving Repr, Inhabited

structure DataTypeTemplate where
  name : Global
  typeParams : Array String
  constructors : List Constructor
  deriving Repr

structure FunctionTemplate where
  name : Global
  typeParams : Array String
  inputs : List (Local × Typ)
  output : Typ
  body : Term
  deriving Repr, Inhabited

structure Toplevel where
  dataTypes : Array DataType
  typeAliases : Array TypeAlias
  functions : Array Function
  dataTypeTemplates : Array DataTypeTemplate
  functionTemplates : Array FunctionTemplate
  deriving Repr

def Toplevel.getFuncIdx (toplevel : Toplevel) (funcName : Lean.Name) : Option Nat := do
  toplevel.functions.findIdx? fun function => function.name.toName == funcName

def Toplevel.merge (x y : Toplevel) : Except Global Toplevel := do
  let ⟨xDT, xTA, xF, xDTT, xFT⟩ := x
  let ⟨yDT, yTA, yF, yDTT, yFT⟩ := y
  let (globals, dataTypes) ← mergeArrays DataType.name ∅ xDT yDT
  let (globals, typeAliases) ← mergeArrays TypeAlias.name globals xTA yTA
  let (globals, functions) ← mergeArrays Function.name globals xF yF
  let (globals, dataTypeTemplates) ← mergeArrays DataTypeTemplate.name globals xDTT yDTT
  let (_, functionTemplates) ← mergeArrays FunctionTemplate.name globals xFT yFT
  pure ⟨dataTypes, typeAliases, functions, dataTypeTemplates, functionTemplates⟩
where
  mergeArrays {α : Type} (getName : α → Global) (globals : Std.HashSet Global)
      (xs ys : Array α) : Except Global (Std.HashSet Global × Array α) := do
    let mut globals := globals
    let mut result := Array.emptyWithCapacity (xs.size + ys.size)
    for set in [xs, ys] do
      for item in set do
        let n := getName item
        if globals.contains n then throw n
        globals := globals.insert n
        result := result.push item
    pure (globals, result)

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
  entry : Bool
  deriving Repr

inductive TypedDeclaration
  | function : TypedFunction → TypedDeclaration
  | dataType : DataType → TypedDeclaration
  | constructor : DataType → Constructor → TypedDeclaration
  deriving Repr, Inhabited

abbrev TypedDecls := IndexMap Global TypedDeclaration

mutual

open Std (HashSet)

partial def Typ.size (decls : TypedDecls) (visited : HashSet Global := {}) :
    Typ → Except String Nat
  | .unit => pure 0
  | .field .. => pure 1
  | .pointer .. => pure 1
  | .function .. => pure 1
  | .tuple ts => ts.foldlM (init := 0) fun acc t => do
    let tSize ← t.size decls visited
    pure $ acc + tSize
  | .array t n => do
    let tSize ← t.size decls visited
    pure $ n * tSize
  | .typeRef g => match decls.getByKey g with
    | some (.dataType data) => data.size decls visited
    | _ => throw s!"Datatype not found: `{g}`"
  | .typeVar s => throw s!"Unexpected type variable `{s}` after concretization"
  | .templateApp g _ => throw s!"Unexpected template application `{g}` after concretization"
  | .unif id => throw s!"Unexpected unification variable `?{id}`"

partial def Constructor.size (decls : TypedDecls) (visited : HashSet Global := {})
    (c : Constructor) : Except String Nat :=
  c.argTypes.foldlM (init := 0) fun acc t => do
    let tSize ← t.size decls visited
    pure $ acc + tSize

partial def DataType.size (dt : DataType) (decls : TypedDecls)
    (visited : HashSet Global := {}) : Except String Nat :=
  if visited.contains dt.name then
    throw s!"Cycle detected at datatype `{dt.name}`"
  else do
    let visited := visited.insert dt.name
    let ctorSizes ← dt.constructors.mapM (Constructor.size decls visited)
    let maxFields := ctorSizes.foldl max 0
    pure $ maxFields + 1
end

end Aiur

end
