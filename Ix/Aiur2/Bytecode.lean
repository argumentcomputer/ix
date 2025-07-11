namespace Aiur

abbrev G := Fin 0xFFFFFFFF00000001

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

  structure Block where
    ops : Array Op
    ctrl : Ctrl
    minSelIncluded: SelIdx
    maxSelExcluded: SelIdx
end

structure Function where
  inputSize : Nat
  outputSize : Nat
  body : Block

structure Toplevel where
  functions : Array Function
  memoryWidths : Array Nat

end Bytecode

end Aiur
