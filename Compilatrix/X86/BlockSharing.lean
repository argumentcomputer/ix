import Compilatrix.X86.Basic

/-! Bottom-up block interning. Hashes select buckets; complete instruction,
operand, and terminator equality selects a block. The hash table is only an
emission aid: the consumer checks the resulting program against its plans.
No correctness theorem assumes an injective hash or a correct cache. -/
namespace Compilatrix.X86

deriving instance Hashable for GPR, IndexReg, Width, MulWidth, Scale, MemAddr,
  FrameSize, StackSlot, MoveSource, AluSource, AluOp, Condition, Compare,
  Intrinsic, Mnemonic, OpEn, Op, Arg, Instr, Reach, Terminator, Block

namespace BlockSharing

structure State where
  blocks : Array Block := #[]
  known : Std.HashMap Block BlockId := {}
  sharing : Bool := false

abbrev Emit := StateT State (Except String)

def emit (instructions : List Instr) (terminator : Terminator) : Emit BlockId := do
  let state ← get
  let block : Block := ⟨instructions.toArray, terminator⟩
  if state.sharing then
    if let some entry := state.known[block]? then return entry
  if state.blocks.size + 1 >= UInt32.size then throw "scalar target exceeds the block-address range"
  let entry := UInt32.ofNat state.blocks.size
  set { state with
    blocks := state.blocks.push block
    known := if state.sharing then state.known.insert block entry else state.known }
  return entry

end BlockSharing
end Compilatrix.X86
