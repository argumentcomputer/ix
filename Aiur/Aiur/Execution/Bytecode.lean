import Aiur.Wire

namespace Aiur.Execution

abbrev Register := Nat

/-- Execution instructions, independent of circuit columns and constraints.
Aggregate values occupy statically known register lists. -/
inductive Instruction (F : Type) where
  | literal (dest : Register) (value : F)
  | copy (dest source : List Register)
  | neg (dest source : Register)
  | binary (dest : Register) (op : BinOp) (left right : Register)
  | guard (tests : List (Register × F)) (message : String)
  | branch (tests : List (Register × F)) (otherwise : Nat)
  | jump (target : Nat)
  | call (function : Nat) (args dest : List Register)
  | store (type : Ty) (value : List Register) (dest : Register)
  | load (type : Ty) (pointer : Register) (dest : List Register)
  | hint (type keyType : Ty) (key dest : List Register) (channel : String := "")
  | assertEq (left right : List Register) (assertion : Assertion)
  | ret (value : List Register)
  | fail (message : String)
  deriving Repr, BEq

structure Function (F : Type) where
  name : String
  params : List Ty
  result : Ty
  registers : Nat
  code : Array (Instruction F)
  deriving Repr, BEq

/-- Callable IDs enumerate functions first, then maps. Table IDs preserve
sharing of an input trace across multiple maps. -/
structure Map where
  name : String
  params : List Ty
  result : Ty
  input : Nat
  output : Nat
  deriving Repr, BEq

structure Table (F : Type) where
  name : String
  type : Ty
  rows : List (List F)
  deriving Repr, BEq

structure Bytecode (F : Type) where
  functions : List (Function F)
  enums : Declarations
  tables : List (Table F)
  maps : List Map
  /-- Host-selected public spelling and resolved callable ID. -/
  entries : List (String × Nat)
  deriving Repr, BEq

end Aiur.Execution
