import Ix.Aiur.Goldilocks

namespace Aiur

namespace Bytecode

abbrev FunIdx := Nat
abbrev ValIdx := Nat
abbrev SelIdx := Nat

inductive Op
  | const : G → Op
  | add : ValIdx → ValIdx → Op
  | sub : ValIdx → ValIdx → Op
  | mul : ValIdx → ValIdx → Op
  | eqZero : ValIdx → Op
  | call : FunIdx → Array ValIdx → (outputSize : Nat) → Op
  | store : Array ValIdx → Op
  | load : (size : Nat) → ValIdx → Op
  | assertEq : Array ValIdx → Array ValIdx → Op
  | ioGetInfo : Array ValIdx → Op
  | ioSetInfo : Array ValIdx → ValIdx → ValIdx → Op
  | ioRead : ValIdx → Nat → Op
  | ioWrite : Array ValIdx → Op
  | u8BitDecomposition : ValIdx → Op
  | u8ShiftLeft : ValIdx → Op
  | u8ShiftRight : ValIdx → Op
  | u8Xor : ValIdx → ValIdx → Op
  | u8Add : ValIdx → ValIdx → Op
  | debug : String → Option (Array ValIdx) → Op
  deriving Repr

mutual
  inductive Ctrl where
    | match : ValIdx → Array (G × Block) → Option Block → Ctrl
    | return : SelIdx → Array ValIdx → Ctrl
    deriving Inhabited, Repr

  structure Block where
    ops : Array Op
    ctrl : Ctrl
    minSelIncluded: SelIdx
    maxSelExcluded: SelIdx
    deriving Inhabited, Repr
end

/-- The circuit layout of a function -/
structure FunctionLayout where
  inputSize : Nat
  /-- Bit values that identify which path the computation took.
    Exactly one selector must be set. -/
  selectors : Nat
  /-- Represent registers that hold temporary values and can be shared by
    different circuit paths, since they never overlap. -/
  auxiliaries : Nat
  /-- Lookups can be shared across calls, stores, loads and returns from
    different paths. -/
  lookups : Nat
  deriving Inhabited, Repr

structure Function where
  body : Block
  layout: FunctionLayout
  unconstrained : Bool
  deriving Inhabited, Repr

structure Toplevel where
  functions : Array Function
  memorySizes : Array Nat
  deriving Repr

end Bytecode

end Aiur
