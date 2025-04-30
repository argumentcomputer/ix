import Std.Data.HashMap

namespace Aiur

abbrev Name := String
abbrev ValIdx := Nat
abbrev SelIdx := Nat
abbrev FuncIdx := Nat
abbrev MemIdx := Nat

inductive Prim where
  | u64 : UInt64 → Prim
  | bool : Bool → Prim
  deriving Repr, BEq

inductive Op where
  | prim : Prim → Op
  | add : ValIdx → ValIdx → Op
  | sub : ValIdx → ValIdx → Op
  | mul : ValIdx → ValIdx → Op
  | xor : ValIdx → ValIdx → Op
  | and : ValIdx → ValIdx → Op
  | lt: ValIdx → ValIdx → Op
  | store : List ValIdx → Op
  | load : MemIdx → ValIdx → Op
  | call : FuncIdx → List ValIdx → ValIdx → Op
  deriving Repr, BEq

mutual
  inductive Ctrl where
    | if : ValIdx → Block → Block → Ctrl
    | match : ValIdx → List (UInt64 × Block) -> Option Block → Ctrl
    | ret : SelIdx → List ValIdx → Ctrl
    deriving Repr, BEq

  structure Block where
    ops : List Op
    ctrl : Ctrl
    returnIdents : List SelIdx
    deriving Repr, BEq
end

structure Function where
  name : Name
  inputSize : Nat
  outputSize : Nat
  body : Block
  deriving Repr, BEq


end Aiur
