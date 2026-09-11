import Ix.Compiler.IxIR2.Basic

/-! The baseline instruction subset has no credit creation or consumption.
This executable certificate is independent of the ordinary ownership validator.
It lets clients transfer an entire execution between the two interpretations. -/

namespace Ix.Compiler.IxIR2.CreditFree

def instruction : Instr → Bool
  | .allocWith .. | .discardCredit .. | .takeUnique .. | .resetShared .. => false
  | _ => true

def function (definition : Function) : Bool :=
  definition.blocks.all fun block => block.instructions.all instruction

def program (source : Program) : Bool :=
  function source.main && source.declarations.all fun entry =>
    match entry.2 with
    | .fn definition => function definition
    | .extern _ => true

theorem instructionAt {definition : Function} {block : Block}
    {blockId index : Nat} (free : function definition = true)
    (blockAt : definition.blocks[blockId]? = some block)
    (bound : index < block.instructions.size) :
    instruction block.instructions[index] = true := by
  obtain ⟨blockBound, blockEq⟩ := Array.getElem?_eq_some_iff.mp blockAt
  subst block
  exact Array.all_eq_true.mp
    (Array.all_eq_true.mp free blockId blockBound) index bound

end Ix.Compiler.IxIR2.CreditFree
