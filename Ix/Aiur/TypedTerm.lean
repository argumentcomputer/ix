module
public import Ix.Aiur.Term

public section

namespace Aiur

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

end Aiur

end
