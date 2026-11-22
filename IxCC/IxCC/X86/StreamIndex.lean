import IxCC.X86.StreamLayout

/-! One linear construction of canonical instruction and block positions.
The cached arrays are proved equal to the existing prefix-sum specification;
no proposed encoder offsets are trusted as the source layout. -/

namespace IxCC.X86.Stream

private def positions (sizes : List Nat) : Array Nat :=
  (sizes.scanl (· + ·) 0).toArray

private theorem positions_size (sizes : List Nat) : (positions sizes).size = sizes.length + 1 := by
  simp [positions]

private theorem positions_at (sizes : List Nat) {index : Nat} (bound : index ≤ sizes.length) :
    (positions sizes)[index]? = some (prefixSize sizes index) := by
  simp [positions, List.getElem?_scanl, bound, prefixSize, List.sum_eq_foldl_nat]

structure BlockIndex where
  positions : Array Nat
  bodyBytes : Nat
  bytes : Nat
  deriving Inhabited

def indexBlock (block : Block) : BlockIndex :=
  let positions := positions (instructionSizes block)
  let bodyBytes := positions[block.instructions.size]?.getD 0
  ⟨positions, bodyBytes, bodyBytes + terminatorSize block.terminator⟩

theorem indexBlock_position (block : Block) {index : Nat} (bound : index ≤ block.instructions.size) :
    (indexBlock block).positions[index]? = some (instructionOffset block index) := by
  exact positions_at _ (by simpa [instructionSizes] using bound)

theorem indexBlock_body (block : Block) :
    (indexBlock block).bodyBytes = instructionOffset block block.instructions.size := by
  have found := indexBlock_position block (Nat.le_refl block.instructions.size)
  simpa [indexBlock] using congrArg (fun value => value.getD 0) found

theorem indexBlock_bytes (block : Block) : (indexBlock block).bytes = blockSize block := by
  change (indexBlock block).bodyBytes + terminatorSize block.terminator = _
  rw [indexBlock_body, instructionOffset_end]
  rfl

structure Index where
  blocks : Array BlockIndex
  starts : Array Nat
  textBytes : Nat

def buildIndex (program : Program) : Index :=
  let blocks := program.blocks.map indexBlock
  let positions := positions (blocks.toList.map (·.bytes))
  ⟨blocks, positions.pop, positions[blocks.size]?.getD 0⟩

theorem buildIndex_blocks (program : Program) :
    (buildIndex program).blocks = program.blocks.map indexBlock := rfl

private theorem indexed_sizes (program : Program) :
    ((program.blocks.map indexBlock).toList.map (·.bytes)) = blockSizes program := by
  simp [Array.toList_map, List.map_map, Function.comp_def, indexBlock_bytes, blockSizes]

theorem buildIndex_start (program : Program) {index : Nat} (bound : index < program.blocks.size) :
    (buildIndex program).starts[index]? = some (blockOffset program index) := by
  have small : index ≤ (blockSizes program).length := by simpa [blockSizes] using Nat.le_of_lt bound
  simp only [buildIndex, indexed_sizes, Array.getElem?_pop, positions_size]
  simp only [blockSizes, List.length_map, Array.length_toList, Nat.add_sub_cancel] at *
  rw [if_pos bound]
  exact positions_at _ (by simpa using small)

theorem buildIndex_starts (program : Program) :
    (buildIndex program).starts = blockOffsets program := by
  apply Array.ext_getElem?
  intro index
  by_cases bound : index < program.blocks.size
  · rw [buildIndex_start program bound]
    simp [blockOffsets, bound]
  · have size : (buildIndex program).starts.size = program.blocks.size := by
      simp [buildIndex, positions_size]
    rw [Array.getElem?_eq_none (by omega)]
    simp [blockOffsets, bound]

theorem buildIndex_text (program : Program) : (buildIndex program).textBytes = textSize program := by
  have bound : program.blocks.size ≤ (blockSizes program).length := by simp [blockSizes]
  have found := positions_at (blockSizes program) bound
  simp only [buildIndex, indexed_sizes, Array.size_map]
  rw [found]
  exact blockOffset_end program

end IxCC.X86.Stream
