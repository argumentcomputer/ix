import IxCC.X86.StreamEffects

/-! Complete-text call and return effects, with bytewise return-slot
correspondence preserved across ordinary callee instructions. -/

namespace IxCC.X86.Stream

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

structure Related (program : Program) (base : Word) (holes : Holes) (machine : Machine) (state : ByteEval.State) : Prop where
  core : CoreRelated program base holes machine.returns machine.core state.core
  running : machine.status = .running
  pc : AtPC program base machine.pc state.rip

theorem paired_linear_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    {block : Block} {instruction : Instr}
    (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (foundInstruction : block.instructions[machine.pc.offset.toNat]? = some instruction)
    (linear : Encode.linearInstruction instruction = true)
    (safe : OperationSafe holes machine.returns (Encode.instructionOperation instruction) machine.core)
    (nextRunning : (step runtime checked machine).status = .running) :
    ∃ after, ByteEval.step output.text base state = .ok after ∧
      Related checked.program base (nextHoles holes (Encode.instructionOperation instruction) machine.core)
        (step runtime checked machine) after := by
  have fetched := fetch_linear valid base state.rip machine.pc related.pc found foundInstruction linear
  have agreement := linear_step valid runtime machine related.running base state.rip state.flags
    related.pc found foundInstruction linear
  simp only [ByteEval.step, fetched] at agreement
  have pair := operation_pair checked.program base state.rip state.flags holes machine.returns
    machine.core state.core related.core (Encode.instructionOperation instruction) (instructionSize instruction)
    (instruction_linear_operation instruction linear) safe
  have sourceStep : step runtime checked machine = executeInstr runtime checked instruction machine := by
    simp [step, related.running, found, foundInstruction]
  have returns : (step runtime checked machine).returns = machine.returns := by
    rw [sourceStep, linear_returns runtime checked machine instruction linear]
  cases logicalStep : ByteEval.execute ⟨Encode.instructionOperation instruction, instructionSize instruction⟩
      ⟨machine.core, state.rip, state.flags⟩ with
  | error fault =>
      cases fault with
      | memory fault | undefinedCondition fault | divideError =>
          simp only [logicalStep, LinearResult] at agreement
          rw [agreement] at nextRunning
          contradiction
      | decode rip => simp [logicalStep, LinearResult] at agreement
  | ok logicalAfter =>
      simp only [logicalStep, LinearResult] at agreement
      cases physicalStep : ByteEval.execute ⟨Encode.instructionOperation instruction, instructionSize instruction⟩ state with
      | error fault => simp [logicalStep, physicalStep, CorePair] at pair
      | ok physicalAfter =>
          simp only [logicalStep, physicalStep, CorePair] at pair
          have sameRip := (linear_rip instruction linear state (instructionSize instruction) physicalStep).trans
            (linear_rip instruction linear ⟨machine.core, state.rip, state.flags⟩
              (instructionSize instruction) logicalStep).symm
          refine ⟨physicalAfter, by simp [ByteEval.step, fetched, physicalStep], ?_⟩
          refine ⟨?_, nextRunning, ?_⟩
          · rw [returns, agreement.1]
            exact pair
          · rw [sameRip]
            exact agreement.2.2

theorem CoreRelated.comparison {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (comparison : Compare) (condition : Condition) :
    comparison.holds condition logical = comparison.holds condition physical := by
  have source : comparison.right.eval logical = comparison.right.eval physical := by
    cases comparison.right <;> simp [AluSource.eval, related.readReg]
  rw [Compare.holds_eq, Compare.holds_eq, source, related.readReg]

/-- The return-slot mask after a terminator: a branch's producer clears the
bytes it writes, like any row; other terminators write no memory. -/
def terminatorHoles (holes : Holes) (terminator : Terminator) (core : Core) : Holes :=
  match terminator with
  | .branch producer args _ _ _ _ => nextHoles holes (.op producer args) core
  | .jump _ | .tailCall _ | .ret => holes

/-- The access condition of a non-return terminator: a branch's producer
reads only ordinary data and writes no active return slot. -/
def TerminatorSafe (holes : Holes) (frames : List ReturnFrame) (terminator : Terminator) (core : Core) : Prop :=
  match terminator with
  | .branch producer args _ _ _ _ => OperationSafe holes frames (.op producer args) core
  | .jump _ | .tailCall _ | .ret => True

/-- A flag-free producer's typed run is its run on empty flags, with the
flags merged from none. -/
theorem exec_run {o : Op} (free : (desc o).flagsIn = []) {args : List Arg} {core after : Core}
    {flags : ByteEval.Flags} (executed : o.exec args core {} = .ok (after, flags)) :
    ∃ out, o.run args core {} = .ok (after, out) ∧ flags = ({} : ByteEval.Flags).merge (desc o).flagsOut out.flags := by
  rw [Encode.exec_flagsFree free] at executed
  cases hrun : o.run args core {} with
  | error fault => simp [hrun] at executed
  | ok result =>
      simp only [hrun, Except.map, Except.ok.injEq, Prod.mk.injEq] at executed
      exact ⟨result.2, by rw [← executed.1], executed.2.symm⟩

theorem paired_control_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    {block : Block} (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (position : machine.pc.offset.toNat = block.instructions.size) (notRet : block.terminator ≠ .ret)
    (safe : TerminatorSafe holes machine.returns block.terminator machine.core)
    (nextRunning : (step runtime checked machine).status = .running) :
    ∃ count after, 0 < count ∧ count ≤ 3 ∧ ByteEval.run output.text base count state = .ok after ∧
      Related checked.program base (terminatorHoles holes block.terminator machine.core)
        (step runtime checked machine) after := by
  have sourceStep := source_terminator runtime machine related.running found position
  have address := related.pc.offset found (by omega)
  rw [position] at address
  have accepted := valid.terminator machine.pc.block.toNat block found
  have bound := terminator_bound found
  have textBound := valid.textBound
  have wf := checked_terminator_wf found
  cases term : block.terminator with
  | ret => exact False.elim (notRet term)
  | jump target | tailCall target =>
      rw [term] at accepted bound
      change targets _ _ _ .jump 5 target = true at accepted
      have targetBound := (targets_sound accepted).1
      have jumped := jump_at accepted base state address (by simp only [terminatorSize] at bound; omega)
      have goEqual : step runtime checked machine = { machine with pc := ⟨target, 0⟩ } := by
        simp [sourceStep, term, executeTerminator, Machine.goto, hasBlock_of_bound targetBound]
      refine ⟨1, { state with rip := base + UInt64.ofNat (blockOffset checked.program target.toNat) },
        by decide, by decide, by simp [ByteEval.run, jumped], ?_⟩
      rw [goEqual]
      exact ⟨related.core, related.running, _, target_entry targetBound, rfl⟩
  | branch producer args condition yes no reach =>
      rw [term] at accepted bound wf safe
      obtain ⟨_, linear, free, _, fused⟩ := Encode.wellFormed_branch wf
      rw [term] at sourceStep
      rw [sourceStep] at nextRunning
      obtain ⟨core, flags, take, typed, tested, targetBound, goEqual⟩ := branch_running nextRunning
      obtain ⟨out, ranTyped, typedFlags⟩ := exec_run free typed
      have pair := run_pair related.core producer args {} safe
      rw [ranTyped] at pair
      cases ranByte : producer.run args state.core {} with
      | error fault => simp [ranByte, RunPair] at pair
      | ok result =>
          obtain ⟨physical, byteOut⟩ := result
          simp only [ranByte, RunPair] at pair
          obtain ⟨sameOut, coresRelated⟩ := pair
          subst sameOut
          have produced : producer.exec args state.core state.flags =
              .ok (physical, state.flags.merge (desc producer).flagsOut out.flags) := by
            rw [Encode.exec_flagsFree free, ranByte]
            rfl
          have byteTest : (state.flags.merge (desc producer).flagsOut out.flags).test condition = some take := by
            rw [ByteEval.test_merge_set (fun flag member => FusedOk.set fused flag (by simpa using member))
              state.flags {} out.flags, ← typedFlags, tested]
          have landed : Related checked.program base (terminatorHoles holes (.branch producer args condition yes no reach) machine.core)
              (step runtime checked machine)
              { core := physical, flags := state.flags.merge (desc producer).flagsOut out.flags,
                rip := base + UInt64.ofNat (blockOffset checked.program (if take then yes else no).toNat) } := by
            rw [sourceStep, goEqual]
            exact ⟨coresRelated, related.running, _, target_entry targetBound, rfl⟩
          cases reach with
          | rel32 =>
              have branched := branch_at accepted linear base state address
                (by simp only [terminatorSize] at bound; omega) produced byteTest
              refine ⟨if take then 2 else 3, _, ?_, ?_, branched, landed⟩
              · split <;> decide
              · split <;> decide
          | fall =>
              have branched := branch_fall_at accepted linear base state address
                (by simp only [terminatorSize] at bound; omega) produced byteTest
              exact ⟨2, _, by decide, by decide, branched, landed⟩

/-- A fused pair that keeps the typed machine running ran its producer, then
its consumer on the producer's flags, and advanced with the consumer's
core. -/
theorem fused_running {runtime : Runtime} {checked : Checked} {machine : Machine} {producer consumer : Op}
    {pargs cargs : List Arg}
    (running : (executeInstr runtime checked (.fused producer pargs consumer cargs) machine).status = .running) :
    ∃ core flags after flagsAfter, producer.exec pargs machine.core {} = .ok (core, flags) ∧
      consumer.exec cargs core flags = .ok (after, flagsAfter) ∧
      executeInstr runtime checked (.fused producer pargs consumer cargs) machine = machine.advanceWith after := by
  simp only [executeInstr] at running ⊢
  cases hproducer : producer.exec pargs machine.core {} with
  | error fault =>
      rw [hproducer] at running
      cases fault <;> simp [Machine.afterRow, Machine.trap] at running
  | ok result =>
      obtain ⟨core, flags⟩ := result
      rw [hproducer] at running
      simp only at running ⊢
      cases hconsumer : consumer.exec cargs core flags with
      | error fault =>
          rw [hconsumer] at running
          cases fault <;> simp [Machine.afterRow, Machine.trap] at running
      | ok value =>
          obtain ⟨after, flagsAfter⟩ := value
          refine ⟨core, flags, after, flagsAfter, ?_, ?_, ?_⟩ <;>
            first | rfl | exact hproducer | exact hconsumer | (rw [hconsumer]; rfl)

theorem instructionSize_fused (producer consumer : Op) (pargs cargs : List Arg) :
    instructionSize (.fused producer pargs consumer cargs) =
      (Encode.encodeOp producer pargs).size + (Encode.encodeOp consumer cargs).size := by
  simp [instructionSize, Encode.encodeInstr, Encode.Chunk.raw]

/-- E2 for a fused pair: its two byte steps keep the machines related, and
the mask clears exactly what the consumer writes (the producer writes only
flags). -/
theorem fused_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    {block : Block} {producer consumer : Op} {pargs cargs : List Arg}
    (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (foundInstruction : block.instructions[machine.pc.offset.toNat]? = some (.fused producer pargs consumer cargs))
    (producerSafe : OperationSafe holes machine.returns (.op producer pargs) machine.core)
    (consumerSafe : OperationSafe holes machine.returns (.op consumer cargs) machine.core)
    (nextRunning : (step runtime checked machine).status = .running) :
    ∃ after, ByteEval.run output.text base 2 state = .ok after ∧
      Related checked.program base (nextHoles holes (.op consumer cargs) machine.core)
        (step runtime checked machine) after := by
  have wf := checked_instruction_wf found foundInstruction
  obtain ⟨_, linear, free, only, _, _, consumes, _, fused⟩ := Encode.wellFormed_fused wf
  have sourceStep : step runtime checked machine =
      executeInstr runtime checked (.fused producer pargs consumer cargs) machine := by
    simp [step, related.running, found, foundInstruction]
  rw [sourceStep] at nextRunning ⊢
  obtain ⟨core1, flags1, core2, flags2, typedProducer, typedConsumer, stepEq⟩ := fused_running nextRunning
  rw [stepEq]
  obtain ⟨outP, ranP, flags1Eq⟩ := exec_run free typedProducer
  have core1Eq : core1 = machine.core := run_flagsOnly only ranP
  subst core1Eq
  -- The producer on the byte machine.
  have pairP := run_pair related.core producer pargs {} producerSafe
  rw [ranP] at pairP
  cases ranBP : producer.run pargs state.core {} with
  | error fault => simp [ranBP, RunPair] at pairP
  | ok resultB =>
    obtain ⟨phys1, outB⟩ := resultB
    simp only [ranBP, RunPair] at pairP
    obtain ⟨sameOut, _⟩ := pairP
    subst sameOut
    have phys1Eq : phys1 = state.core := run_flagsOnly only ranBP
    subst phys1Eq
    -- The consumer, typed and on bytes, observes the same flags.
    have observedEq : (state.flags.merge (desc producer).flagsOut outP.flags).restrict (desc consumer).flagsIn =
        flags1.restrict (desc consumer).flagsIn := by
      rw [flags1Eq]
      exact ByteEval.restrict_merge_set (FusedOk.set fused) _ _ _
    unfold Op.exec at typedConsumer
    cases ranC : consumer.run cargs machine.core (flags1.restrict (desc consumer).flagsIn) with
    | error fault => simp [ranC] at typedConsumer
    | ok resultC =>
      obtain ⟨typedCore, outC⟩ := resultC
      simp only [ranC, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at typedConsumer
      obtain ⟨rfl, _⟩ := typedConsumer
      have pairC := run_pair related.core consumer cargs (flags1.restrict (desc consumer).flagsIn) consumerSafe
      rw [ranC] at pairC
      cases ranBC : consumer.run cargs state.core (flags1.restrict (desc consumer).flagsIn) with
      | error fault => simp [ranBC, RunPair] at pairC
      | ok resultBC =>
        obtain ⟨phys2, outBC⟩ := resultBC
        simp only [ranBC, RunPair] at pairC
        obtain ⟨sameC, related2⟩ := pairC
        subst sameC
        -- Fetch both rows from the certified text.
        have accepted := valid.instruction _ _ found _ _ foundInstruction
        simp only [instructionMatches, Bool.and_eq_true, decodes, beq_iff_eq] at accepted
        obtain ⟨producerFetched, consumerFetched⟩ := accepted
        have indexBound := (Array.getElem?_eq_some_iff.mp foundInstruction).1
        have address := related.pc.offset found (by omega)
        have mapped : pcOffset? checked.program machine.pc =
            some (blockOffset checked.program machine.pc.block.toNat + instructionOffset block machine.pc.offset.toNat) := by
          simp [pcOffset?, found, show machine.pc.offset.toNat ≤ block.instructions.size by omega]
        have small := AtPC.small valid.textBound mapped
        have nextMapped := pcOffset_next found foundInstruction
        have nextSmall := AtPC.small valid.textBound nextMapped
        rw [instructionSize_fused] at nextMapped nextSmall
        let offset := blockOffset checked.program machine.pc.block.toNat + instructionOffset block machine.pc.offset.toNat
        let middle : ByteEval.State :=
          { core := state.core
            rip := base + UInt64.ofNat (offset + (Encode.encodeOp producer pargs).size)
            flags := state.flags.merge (desc producer).flagsOut outP.flags }
        have first : ByteEval.step output.text base state = .ok middle := by
          rw [step_decoded address small producerFetched, Encode.execute_linear linear, Encode.exec_flagsFree free, ranBP]
          simp [middle, offset, address, UInt64.ofNat_add, UInt64.add_assoc]
        let final : ByteEval.State :=
          { core := phys2
            rip := base + UInt64.ofNat
              (offset + ((Encode.encodeOp producer pargs).size + (Encode.encodeOp consumer cargs).size))
            flags := (state.flags.merge (desc producer).flagsOut outP.flags).merge (desc consumer).flagsOut outC.flags }
        have second : ByteEval.step output.text base middle = .ok final := by
          rw [step_decoded (state := middle) rfl (by omega) consumerFetched,
            Encode.execute_row (Op.control_of_consumer consumes)]
          unfold Op.exec
          rw [observedEq, ranBC]
          simp [final, middle, UInt64.ofNat_add, UInt64.add_assoc]
        refine ⟨final, by simp [ByteEval.run, first, second], ?_⟩
        have next := pc_next found foundInstruction
        refine ⟨?_, ?_, ?_⟩
        · simp only [Machine.advanceWith, next.1]
          exact related2
        · simp only [Machine.advanceWith, next.1]
          exact related.running
        · simp only [Machine.advanceWith, next.1]
          exact ⟨_, nextMapped, rfl⟩

/-- E2 for `unwind`: its byte step is the `mov rsp, [m]` row, which keeps
the machines related; the typed step also drops the ghost frames above the
reloaded stack pointer, and the frames it keeps are a suffix, so their
physical return slots stay mapped. The mask is unchanged: the row writes no
memory, and the dropped frames' slots stay masked until ordinary writes
clear them. -/
theorem unwind_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    {block : Block} {source : MemAddr}
    (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (located : block.instructions[machine.pc.offset.toNat]? = some (.unwind source))
    (data : ReadableData holes (source.eval machine.core) 8)
    (nextRunning : (step runtime checked machine).status = .running) :
    ∃ after, ByteEval.step output.text base state = .ok after ∧
      Related checked.program base holes (step runtime checked machine) after := by
  have sourceStep : step runtime checked machine = executeInstr runtime checked (.unwind source) machine := by
    simp [step, related.running, found, located]
  have next := pc_next found located
  rw [sourceStep, executeInstr_unwind] at nextRunning ⊢
  revert nextRunning
  cases hread : machine.core.memory.read64? (source.eval machine.core) with
  | error fault => intro nextRunning; simp [Machine.trap] at nextRunning
  | ok sp =>
    simp only
    cases hcut : cutAt sp machine.returns with
    | none => intro nextRunning; simp [Machine.trap] at nextRunning
    | some rest =>
      intro nextRunning
      simp only [Machine.advanceWith, next.1] at nextRunning ⊢
      -- The byte machine fetches and runs the same `mov rsp, [m]` row.
      have accepted := valid.instruction _ _ found _ _ located
      simp only [instructionMatches, decodes, beq_iff_eq, Encode.instructionOperation] at accepted
      have indexBound := (Array.getElem?_eq_some_iff.mp located).1
      have address := related.pc.offset found (by omega)
      have mapped : pcOffset? checked.program machine.pc =
          some (blockOffset checked.program machine.pc.block.toNat + instructionOffset block machine.pc.offset.toNat) := by
        simp [pcOffset?, found, show machine.pc.offset.toNat ≤ block.instructions.size by omega]
      have small := AtPC.small valid.textBound mapped
      have physicalRead : state.core.memory.read64? (source.eval state.core) = .ok sp := by
        rw [← related.core.address source]
        change state.core.memory.read? .w64 (source.eval machine.core) = .ok sp
        rw [← related.core.memory.read? .w64 _ data]
        exact hread
      have linear : unwindRow.linear = true := rfl
      refine ⟨⟨state.core.setReg .rsp sp, state.rip + UInt64.ofNat (instructionSize (.unwind source)), state.flags⟩,
        ?_, ?_, nextRunning, ?_⟩
      · rw [step_decoded address small accepted, Encode.execute_linear linear, unwindRow_exec, physicalRead]
      · refine ⟨(related.core.setReg .rsp sp).registers, related.core.memory, ?_⟩
        exact related.core.frames.suffix (cutAt_suffix hcut)
      · refine ⟨_, pcOffset_next found located, ?_⟩
        simp [address, UInt64.ofNat_add, UInt64.add_assoc]

theorem call_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    {block : Block} {target : BlockId}
    (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (foundInstruction : block.instructions[machine.pc.offset.toNat]? = some (.call target))
    (aligned : SysV.callSiteAligned (machine.core.readReg .rsp) = true)
    (writable : Memory.rangeAllowed machine.core.memory.writable (machine.core.readReg .rsp - 8) 8 = true)
    (disjoint : FramesDisjoint machine.returns (machine.core.readReg .rsp - 8) 8) :
    ∃ after, ByteEval.step output.text base state = .ok after ∧
      Related checked.program base (addRange holes (machine.core.readReg .rsp - 8) 8)
        (step runtime checked machine) after := by
  have accepted := valid.instruction _ _ found _ _ foundInstruction
  change targets _ _ _ .call 5 target = true at accepted
  obtain ⟨targetBound, fits, fetched⟩ := targets_sound accepted
  have indexBound := (Array.getElem?_eq_some_iff.mp foundInstruction).1
  have address := related.pc.offset found (by omega)
  have mapped : pcOffset? checked.program machine.pc =
      some (blockOffset checked.program machine.pc.block.toNat + instructionOffset block machine.pc.offset.toNat) := by
    simp [pcOffset?, found, show machine.pc.offset.toNat ≤ block.instructions.size by omega]
  have physicalFetch := step_decoded address (AtPC.small valid.textBound mapped) fetched
  have next := pc_next found foundInstruction
  have continuation := pcOffset_next found foundInstruction
  have size : instructionSize (.call target) = 5 := rfl
  rw [size] at continuation
  let nextOffset := blockOffset checked.program machine.pc.block.toNat + instructionOffset block machine.pc.offset.toNat + 5
  have nextAddress : state.rip + 5 = base + UInt64.ofNat nextOffset := by
    simp [nextOffset, address, UInt64.ofNat_add, UInt64.add_assoc]
  have resolved := Encode.relative_resolves_base base nextOffset (blockOffset checked.program target.toNat) fits
  have sourceStep : step runtime checked machine =
      Encode.typedCallState machine target { machine.pc with offset := machine.pc.offset + 1 } := by
    simp [step, related.running, found, foundInstruction, executeInstr, aligned, hasBlock_of_bound targetBound,
      next.1, Memory.write64?, Memory.write?, Width.bytes, writable, Encode.typedCallState, Memory.write64]
  let physicalAfter : ByteEval.State := {
    core := { state.core.setReg .rsp (machine.core.readReg .rsp - 8) with
      memory := state.core.memory.write64 (machine.core.readReg .rsp - 8) (state.rip + 5) }
    rip := base + UInt64.ofNat (blockOffset checked.program target.toNat), flags := state.flags }
  have physicalStep : ByteEval.step output.text base state = .ok physicalAfter := by
    rw [physicalFetch]
    simp only [ByteEval.execute, Memory.write64?, Memory.write?, Width.bytes, ← related.core.readReg .rsp,
      ← related.core.memory.writable, writable, ↓reduceIte, Except.mapError, bind, Except.bind, pure, Except.pure]
    change Except.ok ({ core := _, rip := ByteEval.relative (state.rip + 5) (displacement nextOffset (blockOffset checked.program target.toNat)), flags := state.flags } : ByteEval.State) = _
    rw [nextAddress]
    change Except.ok ({ core := _, rip := ByteEval.relative (base + UInt64.ofNat nextOffset) (Int32.ofInt ((blockOffset checked.program target.toNat : Int) - nextOffset)).toUInt32, flags := state.flags } : ByteEval.State) = _
    rw [resolved]
    rfl
  refine ⟨physicalAfter, physicalStep, ?_⟩
  rw [sourceStep]
  refine ⟨?_, related.running, _, target_entry targetBound, rfl⟩
  refine ⟨(related.core.setReg .rsp _).registers, ?_, ?_⟩
  · exact related.core.memory.write_different _ _ _ 8
  · intro frame member
    change frame ∈ _ :: machine.returns at member
    rcases List.mem_cons.mp member with equal | member
    · subst frame
      exact ⟨nextOffset, continuation, by simpa [physicalAfter, Memory.read64_write64] using nextAddress⟩
    · exact related.core.frames.write _ _ 8 disjoint frame member

theorem ret_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    {block : Block} (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (position : machine.pc.offset.toNat = block.instructions.size) (term : block.terminator = .ret)
    (frame : ReturnFrame) (rest : List ReturnFrame) (returns : machine.returns = frame :: rest)
    (stack : machine.core.readReg .rsp = frame.returnSlot)
    (typedRead : machine.core.memory.read64? frame.returnSlot = .ok frame.continuation.encode)
    (saved : machine.core.calleeSavedMatch frame.calleeSaved = true) :
    ∃ after, ByteEval.step output.text base state = .ok after ∧
      Related checked.program base holes (step runtime checked machine) after := by
  obtain ⟨offset, continuation, slot⟩ := related.core.frames frame (by simp [returns])
  have allowed : Memory.rangeAllowed machine.core.memory.readable frame.returnSlot 8 = true := by
    by_cases allowed : Memory.rangeAllowed machine.core.memory.readable frame.returnSlot 8 = true
    · exact allowed
    · simp [Memory.read64?, Memory.read?, Width.bytes, allowed] at typedRead
  have physicalRead : state.core.memory.read64? frame.returnSlot = .ok (base + UInt64.ofNat offset) := by
    simp only [Memory.read64?, Memory.read?, ← related.core.memory.readable, Width.bytes, allowed, ↓reduceIte]
    exact congrArg Except.ok slot
  have sourceStep : step runtime checked machine =
      { machine with core := machine.core.setReg .rsp (frame.returnSlot + 8), pc := frame.continuation, returns := rest } := by
    rw [source_terminator runtime machine related.running found position, term]
    simp [executeTerminator, returns, stack, typedRead, saved]
  have fetched := valid.terminator _ _ found
  have decode : Decode.decodeAt output.text
      (blockOffset checked.program machine.pc.block.toNat + instructionOffset block block.instructions.size) =
      some ⟨.ret, 1⟩ := by
    simpa [term, terminatorMatches, decodes, beq_iff_eq] using fetched
  have address := related.pc.offset found (by omega)
  rw [position] at address
  have bound := terminator_bound found
  have textBound := valid.textBound
  rw [term] at bound
  have one := step_decoded address (by simp only [terminatorSize] at bound; omega) decode
  let after : ByteEval.State := ⟨state.core.setReg .rsp (frame.returnSlot + 8), base + UInt64.ofNat offset, state.flags⟩
  have executed : ByteEval.step output.text base state = .ok after := by
    rw [one]
    simp [Encode.execute_ret, ← related.core.readReg .rsp, stack, physicalRead, after]
  refine ⟨after, executed, ?_⟩
  rw [sourceStep]
  refine ⟨?_, related.running, offset, continuation, rfl⟩
  have core := related.core.setReg .rsp (frame.returnSlot + 8)
  refine ⟨core.registers, core.memory, ?_⟩
  intro remaining member
  exact core.frames remaining (by simp [returns, member])

end IxCC.X86.Stream
