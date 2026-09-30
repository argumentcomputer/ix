import Compilatrix.X86.StreamLinear

/-! Control transfers fetched from complete certified text. The branch
recipe takes two or three byte steps and reaches the mapped typed target. -/

namespace Compilatrix.X86.Stream

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
    {producer : Op} {args : List Arg} {condition : Condition} {yes no : BlockId}
    (accepted : terminatorMatches program text offset (.branch producer args condition yes no) = true)
    (linear : producer.linear = true)
    (base : Word) (state : ByteEval.State)
    (address : state.rip = base + UInt64.ofNat offset)
    (bound : offset + (Encode.encodeOp producer args).size + 6 < UInt64.size)
    {core : Core} {flags : ByteEval.Flags}
    (produced : producer.exec args state.core state.flags = .ok (core, flags)) {take : Bool}
    (tested : flags.test condition = some take) :
    ByteEval.run text base (if take then 2 else 3) state =
      .ok { core, flags, rip := base + UInt64.ofNat (blockOffset program (if take then yes else no).toNat) } := by
  simp only [terminatorMatches, Bool.and_eq_true, and_assoc] at accepted
  obtain ⟨producerAccepted, yesAccepted, noAccepted⟩ := accepted
  have producerFetched : Decode.decodeAt text offset = some
      ⟨.op producer args, (Encode.encodeOp producer args).size⟩ := by
    simpa [decodes, beq_iff_eq] using producerAccepted
  let middle : ByteEval.State :=
    { core, flags, rip := base + UInt64.ofNat (offset + (Encode.encodeOp producer args).size) }
  have first : ByteEval.step text base state = .ok middle := by
    rw [step_decoded address (by omega) producerFetched, Encode.producer_step linear _ state produced]
    simp [middle, address, UInt64.ofNat_add, UInt64.add_assoc]
  obtain ⟨_, fits, fetched⟩ := targets_sound yesAccepted
  have second := step_decoded (state := middle) rfl (by omega) fetched
  have resolved := Encode.relative_resolves_base base (offset + (Encode.encodeOp producer args).size + 6)
    (blockOffset program yes.toNat) fits
  have taken : ByteEval.step text base middle =
      .ok { middle with
        rip := if take then base + UInt64.ofNat (blockOffset program yes.toNat)
        else base + UInt64.ofNat (offset + (Encode.encodeOp producer args).size + 6) } := by
    rw [second, Encode.execute_branch]
    change (match flags.test condition with | none => _ | some take => _) = _
    rw [tested]
    have nextAddress : middle.rip + UInt64.ofNat 6 =
        base + UInt64.ofNat (offset + (Encode.encodeOp producer args).size + 6) := by
      simp [middle, UInt64.ofNat_add, UInt64.add_assoc]
    simp only [nextAddress, displacement, resolved]
  have third := jump_at noAccepted base
    ({ middle with rip := base + UInt64.ofNat (offset + (Encode.encodeOp producer args).size + 6) }) rfl bound
  cases take <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ByteEval.run, first, taken, bind, Except.bind, third, middle]

theorem falls_sound {program : Program} {offset : Nat} {target : BlockId}
    (accepted : falls program offset target = true) :
    target.toNat < program.blocks.size ∧ blockOffset program target.toNat = offset := by
  simpa only [falls, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using accepted

/-- A branch whose false edge falls through (05 §7) runs its producer and
its `jcc`, two byte steps whether or not it is taken; not taken, the next
byte is the false target's first. -/
theorem branch_fall_at {program : Program} {text : ByteArray} {offset : Nat}
    {producer : Op} {args : List Arg} {condition : Condition} {yes no : BlockId}
    (accepted : terminatorMatches program text offset (.branch producer args condition yes no .fall) = true)
    (linear : producer.linear = true)
    (base : Word) (state : ByteEval.State)
    (address : state.rip = base + UInt64.ofNat offset)
    (bound : offset + (Encode.encodeOp producer args).size + 6 < UInt64.size)
    {core : Core} {flags : ByteEval.Flags}
    (produced : producer.exec args state.core state.flags = .ok (core, flags)) {take : Bool}
    (tested : flags.test condition = some take) :
    ByteEval.run text base 2 state =
      .ok { core, flags, rip := base + UInt64.ofNat (blockOffset program (if take then yes else no).toNat) } := by
  simp only [terminatorMatches, Bool.and_eq_true, and_assoc] at accepted
  obtain ⟨producerAccepted, yesAccepted, noFalls⟩ := accepted
  have noStart := (falls_sound noFalls).2
  have producerFetched : Decode.decodeAt text offset = some
      ⟨.op producer args, (Encode.encodeOp producer args).size⟩ := by
    simpa [decodes, beq_iff_eq] using producerAccepted
  let middle : ByteEval.State :=
    { core, flags, rip := base + UInt64.ofNat (offset + (Encode.encodeOp producer args).size) }
  have first : ByteEval.step text base state = .ok middle := by
    rw [step_decoded address (by omega) producerFetched, Encode.producer_step linear _ state produced]
    simp [middle, address, UInt64.ofNat_add, UInt64.add_assoc]
  obtain ⟨_, fits, fetched⟩ := targets_sound yesAccepted
  have second := step_decoded (state := middle) rfl (by omega) fetched
  have resolved := Encode.relative_resolves_base base (offset + (Encode.encodeOp producer args).size + 6)
    (blockOffset program yes.toNat) fits
  have taken : ByteEval.step text base middle =
      .ok { middle with
        rip := if take then base + UInt64.ofNat (blockOffset program yes.toNat)
        else base + UInt64.ofNat (offset + (Encode.encodeOp producer args).size + 6) } := by
    rw [second, Encode.execute_branch]
    change (match flags.test condition with | none => _ | some take => _) = _
    rw [tested]
    have nextAddress : middle.rip + UInt64.ofNat 6 =
        base + UInt64.ofNat (offset + (Encode.encodeOp producer args).size + 6) := by
      simp [middle, UInt64.ofNat_add, UInt64.add_assoc]
    simp only [nextAddress, displacement, resolved]
  cases take <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ByteEval.run, first, taken, bind, Except.bind, middle, noStart]

/-- A branch that keeps the typed machine running ran its producer, found
its condition's flags defined, and moved to a listed target with the
producer's core. -/
theorem branch_running {checked : Checked} {machine : Machine} {producer : Op} {args : List Arg}
    {condition : Condition} {yes no : BlockId} {reach : Reach}
    (running : (executeTerminator checked (.branch producer args condition yes no reach) machine).status = .running) :
    ∃ core flags take, producer.exec args machine.core {} = .ok (core, flags) ∧
      flags.test condition = some take ∧ (if take then yes else no).toNat < checked.program.blocks.size ∧
      executeTerminator checked (.branch producer args condition yes no reach) machine =
        { machine with core, pc := ⟨if take then yes else no, 0⟩ } := by
  simp only [executeTerminator] at running ⊢
  cases hexec : producer.exec args machine.core {} with
  | error fault =>
      rw [hexec] at running
      cases fault <;> simp [Machine.afterRow, Machine.trap] at running
  | ok result =>
      obtain ⟨core, flags⟩ := result
      rw [hexec] at running
      simp only at running ⊢
      cases htest : flags.test condition with
      | none =>
          rw [htest] at running
          simp [Machine.trap] at running
      | some take =>
          rw [htest] at running
          simp only at running ⊢
          by_cases valid : checked.program.hasBlock (if take then yes else no) = true
          · refine ⟨core, flags, take, rfl, htest, by simpa [Program.hasBlock] using valid, ?_⟩
            simp [Machine.goto, valid]
          · simp [Machine.goto, valid, Machine.trap] at running

/-- A branch never halts the typed machine. -/
theorem branch_not_halted (checked : Checked) (machine : Machine) (running : machine.status = .running)
    (producer : Op) (args : List Arg) (condition : Condition) (yes no : BlockId) (reach : Reach) (result : Word) :
    (executeTerminator checked (.branch producer args condition yes no reach) machine).status ≠ .halted result := by
  simp only [executeTerminator]
  cases hexec : producer.exec args machine.core {} with
  | error fault => cases fault <;> simp [Machine.afterRow, Machine.trap]
  | ok value =>
      obtain ⟨core, flags⟩ := value
      simp only
      cases flags.test condition with
      | none => simp [Machine.trap]
      | some take =>
          simp only [Machine.goto]
          split <;> split <;> simp [Machine.trap, running]

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

end Compilatrix.X86.Stream
