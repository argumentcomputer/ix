import Ix.Aiur2.Goldilocks

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
  | call : FunIdx → Array ValIdx → Op
  | store : Array ValIdx → Op
  | load : (width : Nat) → ValIdx → Op

mutual
  inductive Ctrl where
    | match : ValIdx → Array (G × Block) → Option Block → Ctrl
    | return : SelIdx → Array ValIdx → Ctrl
    deriving Inhabited

  structure Block where
    ops : Array Op
    ctrl : Ctrl
    minSelIncluded: SelIdx
    maxSelExcluded: SelIdx
    deriving Inhabited
end

/-- The circuit layout of a function -/
structure CircuitLayout where
  /-- Bit values that identify which path the computation took.
    Exactly one selector must be set. -/
  selectors : Nat
  /-- Represent registers that hold temporary values and can be shared by
    different circuit paths, since they never overlap. -/
  auxiliaries : Nat
  /-- Constraint slots that can be shared in different paths of the circuit. -/
  sharedConstraints : Nat
  deriving Inhabited

structure Function where
  inputSize : Nat
  outputSize : Nat
  body : Block
  circuitLayout: CircuitLayout

structure Toplevel where
  functions : Array Function
  memoryWidths : Array Nat

end Bytecode

end Aiur
