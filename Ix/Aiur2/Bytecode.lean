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
structure CircuitLayout where
  /-- Bit values that identify which path the computation took.
    Exactly one selector must be set. -/
  selectors : Nat
  /-- Represent registers that hold temporary values and can be shared by
    different circuit paths, since they never overlap. -/
  auxiliaries : Nat
  /-- Constraint slots that can be shared in different paths of the circuit. -/
  sharedConstraints : Nat
  deriving Inhabited, Repr

structure Function where
  inputSize : Nat
  outputSize : Nat
  body : Block
  circuitLayout: CircuitLayout
  deriving Inhabited, Repr

structure Toplevel where
  functions : Array Function
  memoryWidths : Array Nat
  deriving Repr

@[extern "c_rs_toplevel_execute_test"]
private opaque Toplevel.executeTest' :
  @& Toplevel → @& FunIdx → @& Array G → USize → Array G

def Toplevel.executeTest (toplevel : Toplevel) (funIdx : FunIdx) (args : Array G) : Array G :=
  let function := toplevel.functions[funIdx]!
  toplevel.executeTest' funIdx args function.outputSize.toUSize

end Bytecode

end Aiur
