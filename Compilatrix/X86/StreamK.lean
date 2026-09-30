import Compilatrix.X86.StreamValidate
import Compilatrix.X86.EncodeK

/-!
# E2's stream check in kernel-evaluable style

`Stream.checkK` is the stream specification `Stream.check` evaluated in one
pass over the text. It walks the blocks and their instructions in order,
carrying the current offset and the text from that offset on (a list), so
it never indexes the text by position: each instruction is decoded from a
fifteen-byte window of the remaining text (`decodeRestK`), which is what
`decodeAt` decodes (`decodeWindowAt_eq`). The block offsets are prefix sums
computed once, and sizes come from the list encoder
(`Encode.encodeInstrK`). In the kernel, a list is read by walking it, so
`check`'s positions (a prefix sum per position, a text suffix per decode)
cost the product of the text's and the program's sizes, and `checkIndexed`
(the native twin) copies windows through `ByteArray.extract`.

`checkK_eq` proves `checkK = check`, so `Stream.encodeK`, which runs
`Encode.encodeK` and accepts its output by `checkK`, certifies the same
streams as `Stream.encode` (`encodeK_eq`).
-/

namespace Compilatrix.X86.Stream

open Compilatrix.X86

/-- An instruction's encoded length, from the list encoder. -/
def instructionSizeK (instruction : Instr) : Nat := (Encode.encodeInstrK instruction).bytes.length

/-- A block's encoded length. -/
def blockSizeK (block : Block) : Nat :=
  (block.instructions.toList.map instructionSizeK).sum + terminatorSize block.terminator

/-- `decodeAt`'s parse on a window (the `decodedList` of `DecodeWindow`). -/
def decodedListK (input : List UInt8) : Option Decode.Decoded := do
  let (operation, rest) ← Decode.one input
  let length := input.length - rest.length
  if 0 < length && length ≤ 15 then some ⟨operation, length⟩ else none

/-- `decodeAt` on the text from an offset on: none past the end, else the
parse of a fifteen-byte window. -/
def decodeRestK : List UInt8 → Option Decode.Decoded
  | [] => none
  | rest@(_ :: _) => decodedListK (rest.take 15)

/-- `decodes` on the text from an offset on. -/
def decodesK (rest : List UInt8) (operation : Decode.Operation) (length : Nat) : Bool :=
  decodeRestK rest == some ⟨operation, length⟩

/-- What the walk knows about the program: its block offsets, block count
and external targets. -/
structure WalkK where
  starts : List Nat
  blocks : Nat
  externals : ExternalTargets

/-- `targets`, at `offset`, where `rest` is the text from `offset` on. -/
def targetsK (w : WalkK) (rest : List UInt8) (offset : Nat) (operation : Imm32 → Decode.Operation)
    (length : Nat) (target : BlockId) : Bool :=
  let targetOffset := w.starts[target.toNat]?.getD 0
  decide (target.toNat < w.blocks) &&
    Encode.fitsSigned32 ((targetOffset : Int) - (offset + length)) &&
    decodesK rest (operation (displacement (offset + length) targetOffset)) length

/-- `falls`. -/
def fallsK (w : WalkK) (offset : Nat) (target : BlockId) : Bool :=
  decide (target.toNat < w.blocks) && w.starts[target.toNat]?.getD 0 == offset

/-- `instructionMatches`, where `rest` is the text from `offset` on. -/
def instructionMatchesK (w : WalkK) (rest : List UInt8) (offset : Nat) (instruction : Instr) : Bool :=
  match instruction with
  | .call target => targetsK w rest offset .call 5 target
  | .callRuntime intrinsic =>
      match w.externals intrinsic with
      | none => decodesK rest (.call 0) 5
      | some target => Encode.fitsSigned32 (target - (offset + 5)) &&
          decodesK rest (.call (externalDisplacement (offset + 5) target)) 5
  | .fused producer pargs consumer cargs =>
      let size := (Encode.encodeList producer pargs).length
      decodesK rest (.op producer pargs) size &&
        decodesK (rest.drop size) (.op consumer cargs) (Encode.encodeList consumer cargs).length
  | _ => decodesK rest (Encode.instructionOperation instruction) (instructionSizeK instruction)

/-- `terminatorMatches`, where `rest` is the text from `offset` on. -/
def terminatorMatchesK (w : WalkK) (rest : List UInt8) (offset : Nat) : Terminator → Bool
  | .jump target | .tailCall target => targetsK w rest offset .jump 5 target
  | .ret => decodesK rest .ret 1
  | .branch producer args condition yes no .rel32 =>
      let size := (Encode.encodeList producer args).length
      decodesK rest (.op producer args) size &&
        targetsK w (rest.drop size) (offset + size) (.branch condition) 6 yes &&
        targetsK w (rest.drop (size + 6)) (offset + size + 6) .jump 5 no
  | .branch producer args condition yes no .fall =>
      let size := (Encode.encodeList producer args).length
      decodesK rest (.op producer args) size &&
        targetsK w (rest.drop size) (offset + size) (.branch condition) 6 yes &&
        fallsK w (offset + size + 6) no

/-- A block's instructions, then its terminator, from `offset` on. -/
def bodyK (w : WalkK) (terminator : Terminator) : List Instr → List UInt8 → Nat → Bool
  | [], rest, offset => terminatorMatchesK w rest offset terminator
  | instruction :: instructions, rest, offset =>
    instructionMatchesK w rest offset instruction &&
      bodyK w terminator instructions (rest.drop (instructionSizeK instruction))
        (offset + instructionSizeK instruction)

/-- The blocks, in order, from `offset` on. -/
def blocksK (w : WalkK) : List Block → List UInt8 → Nat → Bool
  | [], _, _ => true
  | block :: blocks, rest, offset =>
    bodyK w block.terminator block.instructions.toList rest offset &&
      blocksK w blocks (rest.drop (blockSizeK block)) (offset + blockSizeK block)

/-- `check` in kernel-evaluable style (`checkK_eq`). -/
def checkK (program : Program) (output : Encode.Output) (externals : ExternalTargets := unresolved) : Bool :=
  let blocks := program.blocks.toList
  let sizes := blocks.map blockSizeK
  let starts := (sizes.scanl (· + ·) 0).dropLast
  let total := sizes.sum
  decide (total < UInt64.size) && output.text.size == total &&
    output.blockOffsets.toList == starts && output.relocations == expectedRelocations program &&
    blocksK ⟨starts, blocks.length, externals⟩ blocks output.text.data.toList 0

/-! ## `checkK = check` -/


theorem instructionSizeK_eq (instruction : Instr) : instructionSizeK instruction = instructionSize instruction := by
  simp only [instructionSizeK, instructionSize, ← Encode.encodeInstr_toK, Encode.Chunk.toK, ByteArray.size,
    Array.length_toList]

theorem blockSizeK_eq (block : Block) : blockSizeK block = blockSize block := by
  have sizes : instructionSizeK = instructionSize := funext instructionSizeK_eq
  simp only [blockSizeK, blockSize, instructionSizes, sizes]

/-! ## The window -/

/-- A successful parse consumed a prefix and succeeds on any suffix (as in
`DecodeWindow`, whose lemmas are private). -/
private theorem decodedListK_prefix {input : List UInt8} {decoded : Decode.Decoded}
    (accepted : decodedListK input = some decoded) :
    ∃ consumed remaining, input = consumed ++ remaining ∧ consumed.length = decoded.length ∧
      0 < decoded.length ∧ decoded.length ≤ 15 ∧
      ∀ suffix, Decode.one (consumed ++ suffix) = some (decoded.operation, suffix) := by
  rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨operation, rest⟩, parsed, accepted⟩
  change (if 0 < input.length - rest.length && input.length - rest.length ≤ 15 then
    some ⟨operation, input.length - rest.length⟩ else none) = some decoded at accepted
  split at accepted
  · rename_i bounds
    cases accepted
    obtain ⟨consumed, same, extension⟩ := Decode.one_stable.holds parsed
    have length : input.length - rest.length = consumed.length := by simp [same]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at bounds
    exact ⟨consumed, rest, same, length.symm, bounds.1, bounds.2, extension⟩
  · contradiction

private theorem decodedListK_of_prefix {consumed : List UInt8} {decoded : Decode.Decoded}
    (length : consumed.length = decoded.length) (positive : 0 < decoded.length) (short : decoded.length ≤ 15)
    (parsed : ∀ suffix, Decode.one (consumed ++ suffix) = some (decoded.operation, suffix)) (suffix : List UInt8) :
    decodedListK (consumed ++ suffix) = some decoded := by
  cases decoded
  simp [decodedListK, parsed suffix, length, positive, short]

theorem decodedListK_take (input : List UInt8) : decodedListK (input.take 15) = decodedListK input := by
  apply Option.ext
  intro decoded
  constructor
  · intro accepted
    obtain ⟨consumed, remaining, same, length, positive, short, parsed⟩ := decodedListK_prefix accepted
    have full : input = consumed ++ (remaining ++ input.drop 15) := by
      rw [← List.append_assoc, ← same, List.take_append_drop]
    rw [full]
    exact decodedListK_of_prefix length positive short parsed _
  · intro accepted
    obtain ⟨consumed, remaining, same, length, positive, short, parsed⟩ := decodedListK_prefix accepted
    have fits : consumed.length ≤ 15 := by omega
    rw [same, List.take_append, List.take_of_length_le fits]
    exact decodedListK_of_prefix length positive short parsed _

theorem decodeRestK_eq (text : ByteArray) (offset : Nat) :
    decodeRestK (text.data.toList.drop offset) = Decode.decodeAt text offset := by
  unfold Decode.decodeAt
  by_cases past : offset ≥ text.size
  · rw [ite_eq_left past, List.drop_eq_nil_of_le (by rw [← Encode.size_eq_length]; exact past)]
    rfl
  · rw [ite_eq_right past]
    cases h : text.data.toList.drop offset with
    | nil =>
      have := List.drop_eq_nil_iff.mp h
      rw [Encode.size_eq_length] at past
      omega
    | cons head tail =>
      simp only [decodeRestK]
      rw [decodedListK_take]
      rfl

theorem decodesK_eq (text : ByteArray) (offset : Nat) (operation : Decode.Operation) (length : Nat) :
    decodesK (text.data.toList.drop offset) operation length = decodes text offset operation length := by
  simp only [decodesK, decodes, decodeRestK_eq]

/-! ## Positions -/

theorem scanl_getElem? (sizes : List Nat) {index : Nat} (bound : index ≤ sizes.length) :
    (sizes.scanl (· + ·) 0)[index]? = some (prefixSize sizes index) := by
  simp [List.getElem?_scanl, bound, prefixSize, List.sum_eq_foldl_nat]

/-- The walk's knowledge is the program's positions. -/
structure WalkK.Fits (w : WalkK) (program : Program) : Prop where
  blocks : w.blocks = program.blocks.size
  starts : ∀ target, target < program.blocks.size → w.starts[target]? = some (blockOffset program target)

theorem starts_fits (program : Program) (externals : ExternalTargets) :
    WalkK.Fits ⟨((program.blocks.toList.map blockSizeK).scanl (· + ·) 0).dropLast, program.blocks.toList.length,
      externals⟩ program := by
  have sizes : program.blocks.toList.map blockSizeK = blockSizes program := by
    simp only [blockSizes]
    exact List.map_congr_left fun block _ => blockSizeK_eq block
  refine ⟨rfl, fun target bound => ?_⟩
  simp only [sizes]
  rw [List.getElem?_dropLast, ite_eq_left (by simp [blockSizes]; omega),
    scanl_getElem? _ (by simp [blockSizes]; omega)]
  rfl

theorem targetsK_eq {w : WalkK} {program : Program} (fits : w.Fits program) (text : ByteArray) (offset : Nat)
    (operation : Imm32 → Decode.Operation) (length : Nat) (target : BlockId) :
    targetsK w (text.data.toList.drop offset) offset operation length target =
      targets program text offset operation length target := by
  unfold targetsK targets
  dsimp only
  rw [fits.blocks, decodesK_eq]
  by_cases bound : target.toNat < program.blocks.size
  · rw [fits.starts _ bound]
    rfl
  · simp [bound]

theorem fallsK_eq {w : WalkK} {program : Program} (fits : w.Fits program) (offset : Nat) (target : BlockId) :
    fallsK w offset target = falls program offset target := by
  unfold fallsK falls
  rw [fits.blocks]
  by_cases bound : target.toNat < program.blocks.size
  · rw [fits.starts _ bound]
    rfl
  · simp [bound]

theorem encodeList_length (o : Op) (args : List Arg) : (Encode.encodeList o args).length = (Encode.encodeOp o args).size :=
  rfl

theorem instructionMatchesK_eq {w : WalkK} {program : Program} (fits : w.Fits program) (text : ByteArray)
    (offset : Nat) (instruction : Instr) :
    instructionMatchesK w (text.data.toList.drop offset) offset instruction =
      instructionMatches program text w.externals offset instruction := by
  cases instruction with
  | call target => exact targetsK_eq fits text offset _ 5 target
  | callRuntime intrinsic =>
    unfold instructionMatchesK instructionMatches
    simp only [decodesK_eq]
    rfl
  | fused producer pargs consumer cargs =>
    unfold instructionMatchesK instructionMatches
    simp only [List.drop_drop, decodesK_eq, encodeList_length]
  | op o args =>
    unfold instructionMatchesK instructionMatches
    simp only [decodesK_eq, instructionSizeK_eq]
  | unwind source =>
    unfold instructionMatchesK instructionMatches
    simp only [decodesK_eq, instructionSizeK_eq]

theorem terminatorMatchesK_eq {w : WalkK} {program : Program} (fits : w.Fits program) (text : ByteArray)
    (offset : Nat) (terminator : Terminator) :
    terminatorMatchesK w (text.data.toList.drop offset) offset terminator =
      terminatorMatches program text offset terminator := by
  cases terminator with
  | jump target => exact targetsK_eq fits text offset _ 5 target
  | tailCall target => exact targetsK_eq fits text offset _ 5 target
  | ret => exact decodesK_eq text offset _ 1
  | branch producer args condition yes no reach =>
    cases reach <;> unfold terminatorMatchesK terminatorMatches <;>
      simp only [List.drop_drop, ← Nat.add_assoc] <;>
      simp only [decodesK_eq, encodeList_length, targetsK_eq fits, fallsK_eq fits]

/-! ## The walk -/

theorem bodyK_eq {w : WalkK} {program : Program} (fits : w.Fits program) (text : ByteArray) (block : Block)
    (start : Nat) : ∀ (j : Nat), j ≤ block.instructions.size →
    bodyK w block.terminator (block.instructions.toList.drop j)
        (text.data.toList.drop (start + instructionOffset block j)) (start + instructionOffset block j) =
      ((List.range' j (block.instructions.size - j)).all (fun index =>
        match block.instructions[index]? with
        | none => false
        | some instruction => instructionMatches program text w.externals
            (start + instructionOffset block index) instruction) &&
      terminatorMatches program text (start + instructionOffset block block.instructions.size) block.terminator) := by
  intro j bound
  induction h : block.instructions.size - j generalizing j with
  | zero =>
    have equal : j = block.instructions.size := by omega
    subst equal
    rw [List.drop_eq_nil_of_le (by simp)]
    simp only [bodyK, List.range'_zero, List.all_nil, Bool.true_and]
    exact terminatorMatchesK_eq fits text _ block.terminator
  | succ n ih =>
    have small : j < block.instructions.size := by omega
    have found : block.instructions[j]? = some block.instructions.toList[j] := by
      rw [← Array.getElem?_toList]
      exact List.getElem?_eq_getElem (by simpa using small)
    rw [List.drop_eq_getElem_cons (by simpa using small)]
    simp only [bodyK, List.range'_succ, List.all_cons]
    rw [instructionMatchesK_eq fits, List.drop_drop, instructionSizeK_eq, Nat.add_assoc,
      ← instructionOffset_next found, ih (j + 1) (by omega) (by omega), found]
    simp only [Bool.and_assoc]

theorem bodyK_start {w : WalkK} {program : Program} (fits : w.Fits program) (text : ByteArray) (block : Block)
    (start : Nat) :
    bodyK w block.terminator block.instructions.toList (text.data.toList.drop start) start =
      ((List.range block.instructions.size).all (fun index =>
        match block.instructions[index]? with
        | none => false
        | some instruction => instructionMatches program text w.externals
            (start + instructionOffset block index) instruction) &&
      terminatorMatches program text (start + instructionOffset block block.instructions.size) block.terminator) := by
  have := bodyK_eq fits text block start 0 (Nat.zero_le _)
  simp only [List.drop_zero, instructionOffset_zero, Nat.add_zero, Nat.sub_zero] at this
  rw [this, List.range_eq_range']

theorem blocksK_eq {w : WalkK} {program : Program} (fits : w.Fits program) (output : Encode.Output) :
    ∀ (k : Nat), k ≤ program.blocks.size →
    blocksK w (program.blocks.toList.drop k) (output.text.data.toList.drop (blockOffset program k))
        (blockOffset program k) =
      (List.range' k (program.blocks.size - k)).all (blockMatches program output w.externals) := by
  intro k bound
  induction h : program.blocks.size - k generalizing k with
  | zero =>
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ n ih =>
    have small : k < program.blocks.size := by omega
    have found : program.blocks[k]? = some program.blocks.toList[k] := by
      rw [← Array.getElem?_toList]
      exact List.getElem?_eq_getElem (by simpa using small)
    rw [List.drop_eq_getElem_cons (by simpa using small)]
    simp only [blocksK, List.range'_succ, List.all_cons]
    rw [bodyK_start fits, List.drop_drop, blockSizeK_eq, ← blockOffset_next found,
      ih (k + 1) (by omega) (by omega)]
    simp only [blockMatches, found]
    rfl

theorem blockOffsets_toList (program : Program) :
    (blockOffsets program).toList = ((blockSizes program).scanl (· + ·) 0).dropLast := by
  apply List.ext_getElem?
  intro index
  have length : (List.scanl (· + ·) 0 (blockSizes program)).length - 1 = program.blocks.size := by
    simp [blockSizes]
  simp only [blockOffsets, Array.toList_map, List.getElem?_map, List.getElem?_dropLast, length]
  by_cases bound : index < program.blocks.size
  · rw [ite_eq_left bound, scanl_getElem? _ (by simp [blockSizes]; omega)]
    simp [bound]
    rfl
  · rw [ite_eq_right bound]
    simp [bound]

/-- The stream check in one pass is the stream specification. -/
theorem checkK_eq (program : Program) (output : Encode.Output) (externals : ExternalTargets := unresolved) :
    checkK program output externals = check program output externals := by
  have sizes : program.blocks.toList.map blockSizeK = blockSizes program := by
    simp only [blockSizes]
    exact List.map_congr_left fun block _ => blockSizeK_eq block
  have offsets : (output.blockOffsets.toList == ((blockSizes program).scanl (· + ·) 0).dropLast) =
      (output.blockOffsets == blockOffsets program) := by
    rw [← blockOffsets_toList, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Array.toList_inj]
  have walk := blocksK_eq (starts_fits program externals) output 0 (Nat.zero_le _)
  simp only [List.drop_zero, blockOffset_zero, Nat.sub_zero, sizes] at walk
  unfold checkK check
  simp only [sizes, offsets, walk, textSize, List.range_eq_range']
  exact walk ▸ rfl


/-- `Stream.encode` in kernel-evaluable style: the list encoder, accepted by
`checkK` (`encodeK_eq`). -/
def encodeK (checked : Checked) : Except Error (Certified checked) := do
  let output ← (Encode.encodeK checked).mapError Error.encoder
  if accepted : checkK checked.program output = true then
    return ⟨output, check_sound ((checkK_eq checked.program output).symm.trans accepted)⟩
  else throw .invalidStream

/-- The kernel-style stream is `Stream.encode`'s: the same output, accepted
exactly when `checkIndexed` accepts it (both are `check`). -/
theorem encodeK_eq (checked : Checked) : encodeK checked = encode checked := by
  unfold encodeK encode
  rw [Encode.encodeK_eq]
  cases Encode.encode checked with
  | error e => rfl
  | ok output =>
    have same : checkK checked.program output = checkIndexed checked.program output := by
      rw [checkK_eq, checkIndexed_eq]
    simp only [Except.mapError, bind, Except.bind]
    by_cases accepted : checkIndexed checked.program output = true
    · rw [dif_pos (same.trans accepted), dif_pos accepted]
    · rw [dif_neg (by rw [same]; exact accepted), dif_neg accepted]

end Compilatrix.X86.Stream
