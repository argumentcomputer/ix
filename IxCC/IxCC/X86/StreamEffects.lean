import IxCC.X86.StreamMemory

/-! Preservation of return-address memory correspondence by ordinary
decoded instructions, generic over table rows. A row's memory footprint is
derived from its memory slots and stack effect (`Op.reads`, `Op.writes`).
Access premises describe these concrete byte ranges; they do not assume
instruction effects or a simulation relation after execution. -/

namespace IxCC.X86.Stream

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

/-- Memory an operation reads: its row's memory input slots and popped word. -/
def operationReads : Decode.Operation → Core → List Access
  | .op o args, core => o.reads args core

/-- Memory an operation writes, in execution order. -/
def operationWrites : Decode.Operation → Core → List Access
  | .op o args, core => o.writes args core

def OperationSafe (holes : Holes) (frames : List ReturnFrame) (operation : Decode.Operation) (core : Core) : Prop :=
  (∀ access ∈ operationReads operation core, ReadableData holes access.address access.bytes) ∧
    ∀ access ∈ operationWrites operation core, FramesDisjoint frames access.address access.bytes

/-- Clear the ranges an instruction overwrites, in order. -/
def clearAccesses (holes : Holes) : List Access → Holes
  | [] => holes
  | access :: accesses => clearAccesses (clearRange holes access.address access.bytes) accesses

theorem clearAccesses_append (holes : Holes) (first second : List Access) :
    clearAccesses holes (first ++ second) = clearAccesses (clearAccesses holes first) second := by
  induction first generalizing holes with
  | nil => rfl
  | cons access first ih => exact ih _

def nextHoles (holes : Holes) (operation : Decode.Operation) (core : Core) : Holes :=
  clearAccesses holes (operationWrites operation core)

def linearOperation : Decode.Operation → Bool
  | .op o _ => o.linear

def CorePair (program : Program) (base : Word) (holes : Holes) (frames : List ReturnFrame) :
    Except ByteEval.Fault ByteEval.State → Except ByteEval.Fault ByteEval.State → Prop
  | .ok logical, .ok physical => CoreRelated program base holes frames logical.core physical.core
  | .error left, .error right => left = right
  | _, _ => False

theorem width_bytes_le (width : Width) : width.bytes ≤ 8 := by cases width <;> decide

/-! ## Footprints depend only on registers -/

theorem access_registers {first second : Core} (same : first.registers = second.registers)
    (width : Width) (arg : Arg) : arg.access first width = arg.access second width := by
  cases arg <;> simp [Arg.access, MemAddr.eval, Core.readReg, same]

theorem slotReads_registers {first second : Core} (same : first.registers = second.registers)
    (slots : List Slot) (args : List Arg) : slotReads first slots args = slotReads second slots args := by
  induction slots generalizing args with
  | nil => cases args <;> rfl
  | cons slot slots ih =>
      cases args with
      | nil => rfl
      | cons arg args => simp [slotReads, ih, access_registers same]

theorem slotWrites_registers {first second : Core} (same : first.registers = second.registers)
    (slots : List Slot) (args : List Arg) : slotWrites first slots args = slotWrites second slots args := by
  induction slots generalizing args with
  | nil => cases args <;> rfl
  | cons slot slots ih =>
      cases args with
      | nil => rfl
      | cons arg args => simp [slotWrites, ih, access_registers same]

theorem operationReads_registers {first second : Core} (same : first.registers = second.registers)
    (operation : Decode.Operation) : operationReads operation first = operationReads operation second := by
  cases operation with
  | op o args => simp [operationReads, Op.reads, Op.pops, slotReads_registers same, Core.readReg, same]

theorem operationWrites_registers {first second : Core} (same : first.registers = second.registers)
    (operation : Decode.Operation) : operationWrites operation first = operationWrites operation second := by
  cases operation with
  | op o args => simp [operationWrites, Op.writes, Op.pushes, slotWrites_registers same, Core.readReg, same]

/-! ## Reads -/

theorem CoreRelated.load {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (width : Width) (arg : Arg)
    (data : ∀ access ∈ arg.access logical width, ReadableData holes access.address access.bytes) :
    arg.load logical width = arg.load physical width := by
  cases arg with
  | reg register => simp [Arg.load, related.readReg]
  | mem address =>
      simp only [Arg.load, ← related.address address]
      exact related.memory.read? width _ (data ⟨address.eval logical, width.bytes⟩ (by simp [Arg.access]))
  | imm value => rfl

theorem readSlots_related {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (slots : List Slot) (args : List Arg)
    (data : ∀ access ∈ slotReads logical slots args, ReadableData holes access.address access.bytes) :
    readSlots logical slots args = readSlots physical slots args := by
  induction slots generalizing args with
  | nil => cases args <;> rfl
  | cons slot slots ih =>
      cases args with
      | nil => rfl
      | cons arg args =>
          simp only [slotReads, List.mem_append] at data
          have rest := ih args (fun access member => data access (Or.inr member))
          cases hrole : slot.role <;> simp only [readSlots, hrole, rest]
          · rw [related.load slot.width arg (fun access member => data access (Or.inl (by simpa [hrole] using member)))]
          · rw [related.load slot.width arg (fun access member => data access (Or.inl (by simpa [hrole] using member)))]
          · cases arg <;> simp [Arg.address, related.readReg, related.address]

theorem readImplicits_registers {first second : Core} (same : first.registers = second.registers)
    (implicits : List Implicit) : readImplicits first implicits = readImplicits second implicits := by
  simp [readImplicits, Core.readReg, same]

theorem inputs_related {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (o : Op) (args : List Arg)
    (data : ∀ access ∈ o.reads args logical, ReadableData holes access.address access.bytes) :
    o.inputs args logical = o.inputs args physical := by
  simp only [Op.reads, List.mem_append] at data
  unfold Op.inputs
  rw [readSlots_related related _ args (fun access member => data access (Or.inl member)),
    readImplicits_registers related.registers]
  cases hstack : (desc o).stack with
  | push | none => rfl
  | pop =>
      have popped := related.memory.read? .w64 (logical.readReg .rsp)
        (data ⟨logical.readReg .rsp, 8⟩ (Or.inr (by simp [Op.pops, hstack])))
      simp only [Memory.read64?]
      rw [popped, related.readReg .rsp]

/-! ## Writes -/

/-- Paired results of a memory-faulting core update. -/
def CoreStep (program : Program) (base : Word) (holes : Holes) (frames : List ReturnFrame) :
    Except MemoryFault Core → Except MemoryFault Core → Prop
  | .ok logical, .ok physical => CoreRelated program base holes frames logical physical
  | .error left, .error right => left = right
  | _, _ => False

theorem store_related {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {before beforePhysical logical physical : Core} (registersBefore : before.registers = beforePhysical.registers)
    (related : CoreRelated program base holes frames logical physical) (width : Width) (value : Word) (arg : Arg)
    (disjoint : ∀ access ∈ arg.access before width, FramesDisjoint frames access.address access.bytes) :
    CoreStep program base (clearAccesses holes (arg.access before width)) frames
      (arg.store before width value logical) (arg.store beforePhysical width value physical) := by
  cases arg with
  | reg register => exact related.writeReg width register value
  | imm immediate => exact related
  | mem address =>
      have sameAddress : address.eval before = address.eval beforePhysical := by
        simp [MemAddr.eval, Core.readReg, registersBefore]
      have permissions := related.memory.writable
      simp only [Arg.store, Arg.access, ← sameAddress]
      cases allowed : Memory.rangeAllowed logical.memory.writable (address.eval before) width.bytes with
      | false =>
          simp [Memory.write?, ← permissions, allowed, CoreStep]
      | true =>
          simp only [Memory.write?, ← permissions, allowed, ite_true, bind, Except.bind, pure, Except.pure,
            CoreStep, clearAccesses]
          exact related.write _ _ _ (width_bytes_le width)
            (disjoint ⟨address.eval before, width.bytes⟩ (by simp [Arg.access]))

theorem writeSlots_related {program : Program} {base : Word} {frames : List ReturnFrame}
    {before beforePhysical : Core} (registersBefore : before.registers = beforePhysical.registers)
    (slots : List Slot) (args : List Arg) (results : List Word) :
    ∀ (holes : Holes) (logical physical : Core), CoreRelated program base holes frames logical physical →
      (∀ access ∈ slotWrites before slots args, FramesDisjoint frames access.address access.bytes) →
      CoreStep program base (clearAccesses holes (slotWrites before slots args)) frames
        (writeSlots before logical slots args results) (writeSlots beforePhysical physical slots args results) := by
  induction slots generalizing args results with
  | nil => intro holes logical physical related _; cases args <;> exact related
  | cons slot slots ih =>
      intro holes logical physical related disjoint
      cases args with
      | nil => exact related
      | cons arg args =>
          simp only [slotWrites, List.mem_append] at disjoint
          cases hrole : slot.role
          case read | address =>
            simpa [writeSlots, slotWrites, hrole] using
              ih args results holes logical physical related (fun access member => disjoint access (Or.inr member))
          all_goals
            have first := store_related registersBefore related slot.width (results.headD 0) arg
              (fun access member => disjoint access (Or.inl (by simpa [hrole] using member)))
            simp only [writeSlots, slotWrites, hrole, bind, Except.bind, clearAccesses_append]
            cases hl : arg.store before slot.width (results.headD 0) logical <;>
              cases hp : arg.store beforePhysical slot.width (results.headD 0) physical <;>
              simp only [hl, hp, CoreStep] at first ⊢
            · exact first
            · rename_i middle middlePhysical
              exact ih args results.tail _ middle middlePhysical first
                (fun access member => disjoint access (Or.inr member))

theorem stage_related {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (o : Op) (out : SemOut)
    (disjoint : ∀ access ∈ o.pushes logical, FramesDisjoint frames access.address access.bytes) :
    CoreStep program base (clearAccesses holes (o.pushes logical)) frames (o.stage logical out) (o.stage physical out) := by
  unfold Op.stage Op.pushes at *
  cases hstack : (desc o).stack with
  | none => simpa [hstack, CoreStep, clearAccesses] using related
  | pop => simpa [hstack, CoreStep, clearAccesses, related.readReg] using related.setReg .rsp (physical.readReg .rsp + 8)
  | push =>
      simp only [hstack] at disjoint ⊢
      have permissions := related.memory.writable
      simp only [Memory.write64?, Memory.write?, ← related.readReg .rsp, ← permissions, Width.bytes]
      by_cases allowed : Memory.rangeAllowed logical.memory.writable (logical.readReg .rsp - 8) 8 = true
      · simp only [allowed, ite_true, bind, Except.bind, pure, Except.pure, CoreStep, clearAccesses]
        have written := related.write (logical.readReg .rsp - 8) (out.results.headD 0) 8 (by decide)
          (disjoint ⟨logical.readReg .rsp - 8, 8⟩ (by simp))
        exact written.setReg .rsp (logical.readReg .rsp - 8)
      · simp only [allowed, Bool.false_eq_true, ite_false, bind, Except.bind, CoreStep]

/-! ## Rows -/

def RunPair (program : Program) (base : Word) (holes : Holes) (frames : List ReturnFrame) :
    Except ExecFault (Core × SemOut) → Except ExecFault (Core × SemOut) → Prop
  | .ok (logical, left), .ok (physical, right) =>
      left = right ∧ CoreRelated program base holes frames logical physical
  | .error left, .error right => left = right
  | _, _ => False

/-- Generic over rows: on related cores, a row reads equal inputs, computes
the same semantic result and faults, and leaves related cores whose mask
clears exactly the bytes it wrote. -/
theorem run_pair {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (o : Op) (args : List Arg) (observed : ByteEval.Flags)
    (safe : OperationSafe holes frames (.op o args) logical) :
    RunPair program base (nextHoles holes (.op o args) logical) frames
      (o.run args logical observed) (o.run args physical observed) := by
  obtain ⟨reads, writes⟩ := safe
  simp only [operationReads] at reads
  simp only [operationWrites, Op.writes, List.mem_append] at writes
  simp only [nextHoles, operationWrites, Op.writes, clearAccesses_append]
  unfold Op.run
  rw [inputs_related related o args reads]
  cases hinputs : o.inputs args physical with
  | error fault => simp [Except.mapError, RunPair]
  | ok inputs =>
      cases hsem : (desc o).sem ⟨inputs, observed⟩ with
      | error fault => simp [Except.mapError, RunPair, hsem]
      | ok out =>
          have staged := stage_related related o out (fun access member => writes access (Or.inl member))
          cases hl : o.stage logical out <;> cases hp : o.stage physical out <;>
            simp only [hl, hp, CoreStep] at staged
          · simp [Except.mapError, RunPair, hsem, hl, hp, staged]
          · rename_i stagedLogical stagedPhysical
            have written := writeSlots_related related.registers (desc o).slots args out.results _
              stagedLogical stagedPhysical staged (fun access member => writes access (Or.inr member))
            cases hwl : writeSlots logical stagedLogical (desc o).slots args out.results <;>
              cases hwp : writeSlots physical stagedPhysical (desc o).slots args out.results <;>
              simp only [hwl, hwp, CoreStep] at written
            · simp [Except.mapError, RunPair, hsem, hl, hp, hwl, hwp, written]
            · simpa [Except.mapError, RunPair, hsem, hl, hp, hwl, hwp] using
                written.implicits (desc o).implicit out.implicit

/-! ## Flag-only rows -/

theorem writeSlots_readOnly (before : Core) :
    ∀ (core : Core) (slots : List Slot) (args : List Arg) (results : List Word),
      slots.all (fun slot => !slot.role.writes) = true → writeSlots before core slots args results = .ok core
  | core, [], args, results, _ => by cases args <;> rfl
  | core, slot :: slots, [], results, _ => rfl
  | core, slot :: slots, arg :: args, results, readOnly => by
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at readOnly
      have rest := writeSlots_readOnly before core slots args results (by simpa using readOnly.2)
      cases hrole : slot.role <;> simp_all [writeSlots, Role.writes]

theorem writeImplicits_readOnly :
    ∀ (core : Core) (implicits : List Implicit) (results : List Word),
      implicits.all (fun implicit => !implicit.role.writes) = true → writeImplicits core implicits results = core
  | core, [], results, _ => by simp
  | core, implicit :: implicits, results, readOnly => by
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at readOnly
      simp only [writeImplicits, readOnly.1, Bool.false_eq_true, ↓reduceIte]
      exact writeImplicits_readOnly core implicits results readOnly.2

theorem flagsOnly_parts {o : Op} (only : o.flagsOnly = true) :
    (desc o).slots.all (fun slot => !slot.role.writes) = true ∧
      (desc o).implicit.all (fun implicit => !implicit.role.writes) = true ∧ (desc o).stack = .none := by
  simp only [Op.flagsOnly, Bool.and_eq_true, beq_iff_eq] at only
  exact ⟨only.1.1, only.1.2, only.2⟩

/-- A row that writes only flags leaves the core unchanged. -/
theorem run_flagsOnly {o : Op} (only : o.flagsOnly = true) {args : List Arg} {core after : Core}
    {observed : ByteEval.Flags} {out : SemOut} (ran : o.run args core observed = .ok (after, out)) :
    after = core := by
  obtain ⟨slots, implicits, stack⟩ := flagsOnly_parts only
  unfold Op.run at ran
  cases hinputs : o.inputs args core with
  | error fault => simp [hinputs, Except.mapError] at ran
  | ok inputs =>
      cases hsem : (desc o).sem ⟨inputs, observed⟩ with
      | error fault => simp [hinputs, hsem, Except.mapError] at ran
      | ok result =>
          have staged : o.stage core result = .ok core := by simp [Op.stage, stack]
          simp [hinputs, hsem, staged, writeSlots_readOnly core core _ args result.results slots,
            writeImplicits_readOnly core _ result.implicit implicits, Except.mapError] at ran
          exact ran.1.symm

/-- A row that writes only flags writes no memory. -/
theorem writes_flagsOnly {o : Op} (only : o.flagsOnly = true) (args : List Arg) (core : Core) :
    o.writes args core = [] := by
  obtain ⟨slots, _, stack⟩ := flagsOnly_parts only
  have none : ∀ (slots : List Slot) (args : List Arg), slots.all (fun slot => !slot.role.writes) = true →
      slotWrites core slots args = [] := by
    intro slots
    induction slots with
    | nil => intro args _; cases args <;> rfl
    | cons slot slots ih =>
        intro args readOnly
        cases args with
        | nil => rfl
        | cons arg args =>
            simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at readOnly
            cases hrole : slot.role <;> simp_all [slotWrites, Role.writes]
  simp [Op.writes, Op.pushes, stack, none _ args slots]

theorem nextHoles_flagsOnly {o : Op} (only : o.flagsOnly = true) (holes : Holes) (args : List Arg)
    (core : Core) : nextHoles holes (.op o args) core = holes := by
  simp [nextHoles, operationWrites, writes_flagsOnly only, clearAccesses]

theorem CoreRelated.operand {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (address : MemAddr) : address.eval logical = address.eval physical := related.address address

theorem operation_pair (program : Program) (base rip : Word) (flags : ByteEval.Flags)
    (holes : Holes) (frames : List ReturnFrame) (logical physical : Core)
    (related : CoreRelated program base holes frames logical physical)
    (operation : Decode.Operation) (length : Nat) (linear : linearOperation operation = true)
    (safe : OperationSafe holes frames operation logical) :
    CorePair program base (nextHoles holes operation logical) frames
      (ByteEval.execute ⟨operation, length⟩ ⟨logical, rip, flags⟩)
      (ByteEval.execute ⟨operation, length⟩ ⟨physical, rip, flags⟩) := by
  cases operation with
  | op o args =>
      simp only [linearOperation] at linear
      have pair := run_pair related o args (flags.restrict (desc o).flagsIn) safe
      rw [Encode.execute_linear linear, Encode.execute_linear linear]
      simp only [Op.exec]
      cases hl : o.run args logical (flags.restrict (desc o).flagsIn) <;>
        cases hp : o.run args physical (flags.restrict (desc o).flagsIn) <;>
        simp only [hl, hp, RunPair] at pair
      · simp [CorePair, pair]
      · rename_i left right
        obtain ⟨sameOut, coresRelated⟩ := pair
        simp [CorePair, coresRelated]

/-! ## Footprints of the typed constructors -/

section Footprints

open Encode (instructionOperation)

/-- A comparison's `cmp` row reads and writes no memory. -/
@[simp] theorem footprint_compare (comparison : Compare) (core : Core) :
    operationReads (.op comparison.row.1 comparison.row.2) core = [] ∧
      operationWrites (.op comparison.row.1 comparison.row.2) core = [] := by
  cases comparison with
  | mk width left right =>
      cases right with
      | reg =>
          simp [Compare.row, operationReads, operationWrites, Op.reads, Op.writes, Op.pops, Op.pushes, desc,
            Table.arithDesc, Table.cmpArith, Table.Arith.role, Table.rmSlot, Table.regSlot, slotReads, slotWrites,
            Arg.access]
      | imm =>
          simp only [Compare.row, aluImmRow]
          split <;>
            simp [operationReads, operationWrites, Op.reads, Op.writes, Op.pops, Op.pushes, desc,
              Table.arithDesc, Table.cmpArith, Table.Arith.role, Table.rmSlot, Table.immSlot, slotReads, slotWrites,
              Arg.access]

/-- `unwind` reads its eight-byte source and writes no memory. -/
@[simp] theorem footprint_unwind (source : MemAddr) (core : Core) :
    operationReads (Encode.instructionOperation (.unwind source)) core = [⟨source.eval core, 8⟩] ∧
      operationWrites (Encode.instructionOperation (.unwind source)) core = [] := by
  simp [Encode.instructionOperation, operationReads, operationWrites, Op.reads, Op.writes, Op.pops, Op.pushes,
    unwindRow, desc, Table.movDesc, Table.rmSlot, Table.regSlot, slotReads, slotWrites, Arg.access, Width.bytes]

@[simp] theorem footprint_mov (width : Width) (destination : GPR) (source : MoveSource) (core : Core) :
    operationReads (instructionOperation (.mov width destination source)) core = [] ∧
      operationWrites (instructionOperation (.mov width destination source)) core = [] := by
  cases source <;> cases width <;> simp only [Instr.mov, Instr.ofRow, movImmRow] <;> (try split) <;> (try split) <;>
    simp [instructionOperation, operationReads, operationWrites, Op.reads, Op.writes, Op.pops,
      Op.pushes, desc, Table.movDesc, Table.rmSlot, Table.regSlot, Table.immSlot, slotReads, slotWrites,
      Arg.access]

@[simp] theorem footprint_alu (operation : AluOp) (width : Width) (destination : GPR) (source : AluSource)
    (core : Core) :
    operationReads (instructionOperation (.alu operation width destination source)) core = [] ∧
      operationWrites (instructionOperation (.alu operation width destination source)) core = [] := by
  cases operation <;> cases source <;> simp only [Instr.alu, Instr.ofRow, aluImmRow] <;> (try split) <;>
    simp [AluOp.mnemonic, instructionOperation, operationReads,
      operationWrites, Op.reads, Op.writes, Op.pops, Op.pushes, desc, Table.arithDesc, Table.rmSlot, Table.Arith.role,
      Table.addArith, Table.subArith, Table.andArith, Table.orArith, Table.xorArith,
      Table.regSlot, Table.immSlot, slotReads, slotWrites, Arg.access]

@[simp] theorem footprint_frame (size : FrameSize) (core : Core) :
    operationReads (instructionOperation (.allocFrame size)) core = [] ∧
      operationWrites (instructionOperation (.allocFrame size)) core = [] ∧
      operationReads (instructionOperation (.freeFrame size)) core = [] ∧
      operationWrites (instructionOperation (.freeFrame size)) core = [] := by
  simp only [Instr.allocFrame, Instr.freeFrame, Instr.ofRow, aluImmRow]
  split <;>
    simp [instructionOperation, operationReads,
      operationWrites, Op.reads, Op.writes, Op.pops, Op.pushes, desc, Table.arithDesc, Table.rmSlot, Table.Arith.role,
      Table.addArith, Table.subArith,
      Table.immSlot, slotReads, slotWrites, Arg.access]

@[simp] theorem footprint_load (width : Width) (destination : GPR) (source : MemAddr) (core : Core) :
    operationReads (instructionOperation (.load width destination source)) core =
        [⟨source.eval core, width.bytes⟩] ∧
      operationWrites (instructionOperation (.load width destination source)) core = [] := by
  cases width <;>
    simp [Instr.load, instructionOperation, operationReads, operationWrites, Op.reads, Op.writes, Op.pops,
      Op.pushes, desc, Table.movDesc, Table.movzxDesc, Table.rmSlot, Table.regSlot, slotReads, slotWrites,
      Arg.access, Width.bytes]

@[simp] theorem footprint_store (width : Width) (destination : MemAddr) (source : GPR) (core : Core) :
    operationReads (instructionOperation (.store width destination source)) core = [] ∧
      operationWrites (instructionOperation (.store width destination source)) core =
        [⟨destination.eval core, width.bytes⟩] := by
  simp [Instr.store, instructionOperation, operationReads, operationWrites, Op.reads, Op.writes, Op.pops,
    Op.pushes, desc, Table.movDesc, Table.rmSlot, Table.regSlot, slotReads, slotWrites, Arg.access]

@[simp] theorem footprint_lea (destination : GPR) (source : MemAddr) (core : Core) :
    operationReads (instructionOperation (.lea destination source)) core = [] ∧
      operationWrites (instructionOperation (.lea destination source)) core = [] := by
  simp [Instr.lea, instructionOperation, operationReads, operationWrites, Op.reads, Op.writes, Op.pops,
    Op.pushes, desc, Table.leaDesc, Table.regSlot, slotReads, slotWrites, Arg.access]

@[simp] theorem footprint_push (source : GPR) (core : Core) :
    operationReads (instructionOperation (.push source)) core = [] ∧
      operationWrites (instructionOperation (.push source)) core = [⟨core.readReg .rsp - 8, 8⟩] := by
  simp [Instr.push, instructionOperation, operationReads, operationWrites, Op.reads, Op.writes, Op.pops,
    Op.pushes, desc, Table.pushDesc, Table.regSlot, slotReads, slotWrites, Arg.access]

@[simp] theorem footprint_pop (destination : GPR) (core : Core) :
    operationReads (instructionOperation (.pop destination)) core = [⟨core.readReg .rsp, 8⟩] ∧
      operationWrites (instructionOperation (.pop destination)) core = [] := by
  simp [Instr.pop, instructionOperation, operationReads, operationWrites, Op.reads, Op.writes, Op.pops,
    Op.pushes, desc, Table.popDesc, Table.regSlot, slotReads, slotWrites, Arg.access]

@[simp] theorem footprint_spill (slot : StackSlot) (source : GPR) (core : Core) :
    operationReads (instructionOperation (.spill slot source)) core = [] ∧
      operationWrites (instructionOperation (.spill slot source)) core =
        [⟨core.readReg .rbp - slot.displacement, 8⟩] := by
  have stored := footprint_store .w64 (spillAddress slot) source core
  simp only [Encode.spillAddress_eval, Width.bytes] at stored
  exact stored

@[simp] theorem footprint_reload (destination : GPR) (slot : StackSlot) (core : Core) :
    operationReads (instructionOperation (.reload destination slot)) core =
        [⟨core.readReg .rbp - slot.displacement, 8⟩] ∧
      operationWrites (instructionOperation (.reload destination slot)) core = [] := by
  have loaded := footprint_load .w64 destination (spillAddress slot) core
  simp only [Encode.spillAddress_eval, Width.bytes] at loaded
  exact loaded

end Footprints

theorem instruction_linear_operation (instruction : Instr) (linear : Encode.linearInstruction instruction = true) :
    linearOperation (Encode.instructionOperation instruction) = true := by
  cases instruction with
  | op o args =>
      simp only [Encode.linearInstruction, Bool.and_eq_true] at linear
      exact linear.1
  | fused | call | callRuntime | unwind => simp [Encode.linearInstruction] at linear

end IxCC.X86.Stream
