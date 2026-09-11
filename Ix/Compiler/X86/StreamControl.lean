import Ix.Compiler.X86.StreamLinear

/-! Control transfers fetched from complete certified text. The branch
recipe takes two or three byte steps and reaches the mapped typed target. -/

namespace Ix.Compiler.X86.Stream

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

theorem targets_sound {program : Program} {text : ByteArray} {offset length : Nat}
    {operation : Imm32 → Decode.Operation} {target : BlockId}
    (accepted : targets program text offset operation length target = true) :
    target.toNat < program.blocks.size ∧
      Encode.fitsSigned32 ((blockOffset program target.toNat : Int) - (offset + length)) = true ∧
      Decode.decodeAt text offset =
        some ⟨operation (displacement (offset + length) (blockOffset program target.toNat)), length⟩ := by
  simpa only [targets, decodes, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using accepted

theorem step_decoded {text : ByteArray} {base : Word} {state : ByteEval.State}
    {offset : Nat} {decoded : Decode.Decoded}
    (address : state.rip = base + UInt64.ofNat offset) (bound : offset < UInt64.size)
    (fetched : Decode.decodeAt text offset = some decoded) :
    ByteEval.step text base state = ByteEval.execute decoded state := by
  simp [ByteEval.step, address, rip_offset _ _ bound, fetched]

theorem jump_at {program : Program} {text : ByteArray} {offset : Nat} {target : BlockId}
    (accepted : targets program text offset .jump 5 target = true)
    (base : Word) (state : ByteEval.State)
    (address : state.rip = base + UInt64.ofNat offset) (bound : offset < UInt64.size) :
    ByteEval.step text base state =
      .ok { state with rip := base + UInt64.ofNat (blockOffset program target.toNat) } := by
  obtain ⟨_, fits, fetched⟩ := targets_sound accepted
  rw [step_decoded address bound fetched]
  have resolved := Encode.relative_resolves_base base (offset + 5) (blockOffset program target.toNat) fits
  change Except.ok { state with rip := ByteEval.relative (state.rip + 5) (displacement (offset + 5) (blockOffset program target.toNat)) } = _
  have nextAddress : state.rip + 5 = base + UInt64.ofNat (offset + 5) := by
    simp [address, UInt64.ofNat_add, UInt64.add_assoc]
  rw [nextAddress]
  change Except.ok { state with rip := ByteEval.relative (base + UInt64.ofNat (offset + 5)) (Int32.ofInt ((blockOffset program target.toNat : Int) - ((offset + 5 : Nat) : Int))).toUInt32 } = _
  rw [resolved]

theorem branch_at {program : Program} {text : ByteArray} {offset : Nat}
    {comparison : Compare} {condition : Condition} {yes no : BlockId}
    (accepted : terminatorMatches program text offset (.branch comparison condition yes no) = true)
    (base : Word) (state : ByteEval.State)
    (address : state.rip = base + UInt64.ofNat offset)
    (bound : offset + (Encode.encodeCompare comparison).size + 6 < UInt64.size) :
    ByteEval.run text base (if comparison.holds condition state.core then 2 else 3) state =
      .ok { Encode.comparedState comparison state with
        rip := base + UInt64.ofNat (blockOffset program
          (if comparison.holds condition state.core then yes else no).toNat) } := by
  simp only [terminatorMatches, Bool.and_eq_true, and_assoc] at accepted
  obtain ⟨compareAccepted, yesAccepted, noAccepted⟩ := accepted
  have compareFetched : Decode.decodeAt text offset = some
      ⟨.compare comparison.width comparison.left (Encode.aluOperand comparison.width comparison.right),
        (Encode.encodeCompare comparison).size⟩ := by
    simpa [decodes, beq_iff_eq] using compareAccepted
  have first : ByteEval.step text base state = .ok (Encode.comparedState comparison state) := by
    rw [step_decoded address (by omega) compareFetched]
    rfl
  have compareAddress : (Encode.comparedState comparison state).rip =
      base + UInt64.ofNat (offset + (Encode.encodeCompare comparison).size) := by
    simp [Encode.comparedState, address, UInt64.ofNat_add, UInt64.add_assoc]
  obtain ⟨_, fits, fetched⟩ := targets_sound yesAccepted
  have second := step_decoded compareAddress (by omega) fetched
  have resolved := Encode.relative_resolves_base base (offset + (Encode.encodeCompare comparison).size + 6)
    (blockOffset program yes.toNat) fits
  have taken : ByteEval.step text base (Encode.comparedState comparison state) =
      .ok { Encode.comparedState comparison state with
        rip := if comparison.holds condition state.core then
          base + UInt64.ofNat (blockOffset program yes.toNat)
        else base + UInt64.ofNat (offset + (Encode.encodeCompare comparison).size + 6) } := by
    rw [second]
    simp only [ByteEval.execute]
    rw [Encode.comparedState_test]
    have nextAddress : (Encode.comparedState comparison state).rip + UInt64.ofNat 6 =
        base + UInt64.ofNat (offset + (Encode.encodeCompare comparison).size + 6) := by
      simp [compareAddress, UInt64.ofNat_add, UInt64.add_assoc]
    simp only [nextAddress, displacement, resolved]
    rfl
  have third := jump_at noAccepted base
    ({ Encode.comparedState comparison state with
      rip := base + UInt64.ofNat (offset + (Encode.encodeCompare comparison).size + 6) }) rfl bound
  cases take : comparison.holds condition state.core <;>
    simp only [take, Bool.false_eq_true, ↓reduceIte, ByteEval.run, first, taken,
      bind, Except.bind, third]

theorem terminator_bound {program : Program} {blockIndex : Nat} {block : Block}
    (found : program.blocks[blockIndex]? = some block) :
    blockOffset program blockIndex + instructionOffset block block.instructions.size +
      terminatorSize block.terminator ≤ textSize program := by
  simpa [instructionOffset_end, blockSize, Nat.add_assoc] using block_end_le found

theorem source_terminator {checked : Checked} (runtime : Runtime) (machine : Machine)
    (running : machine.status = .running) {block : Block}
    (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (position : machine.pc.offset.toNat = block.instructions.size) :
    step runtime checked machine = executeTerminator checked block.terminator machine := by
  simp [step, running, found, position]

theorem target_entry {program : Program} {target : BlockId}
    (bound : target.toNat < program.blocks.size) :
    pcOffset? program ⟨target, 0⟩ = some (blockOffset program target.toNat) :=
  block_entry (Array.getElem?_eq_getElem bound)

theorem hasBlock_of_bound {program : Program} {target : BlockId}
    (bound : target.toNat < program.blocks.size) : program.hasBlock target = true := by
  simpa [Program.hasBlock] using bound

theorem goto_at {checked : Checked} {target : BlockId} (machine : Machine) (base : Word)
    (bound : target.toNat < checked.program.blocks.size) (running : machine.status = .running) :
    (machine.goto checked target).core = machine.core ∧
      (machine.goto checked target).status = .running ∧
      AtPC checked.program base (machine.goto checked target).pc
        (base + UInt64.ofNat (blockOffset checked.program target.toNat)) := by
  have go : machine.goto checked target = { machine with pc := ⟨target, 0⟩ } := by
    simp [Machine.goto, hasBlock_of_bound bound]
  rw [go]
  exact ⟨rfl, running, _, target_entry bound, rfl⟩

end Ix.Compiler.X86.Stream
