import Compilatrix.X86.Eval
import Compilatrix.X86.Width

/-! The typed constructors (`mov`, `load`, `alu`, `push`, `spill`, ...) choose
table rows. Executed through the shared row executor, each has exactly the
effect its name promises: these equations are the former per-constructor
typed semantics, now theorems about the table. -/

namespace Compilatrix.X86

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

@[simp] theorem MemAddr.normalize_eval (address : MemAddr) (core : Core) :
    address.normalize.eval core = address.eval core := by
  cases address with
  | mk base index scale displacement => cases index <;> rfl

theorem truncate32_of_narrow (width : Width) (narrow : width = .w8 ∨ width = .w16) (value : Word) :
    Width.w32.truncate (width.truncate value) = width.truncate value := by
  apply UInt64.toNat_inj.mp
  rw [Encode.truncate_nat, Encode.truncate_nat]
  rcases narrow with rfl | rfl <;> simp only [Width.bits] <;> omega

theorem frame_bound (size : FrameSize) : size.bytes.toNat < 2 ^ 31 := by
  have bound := size.units16.toNat_lt_size
  simp only [FrameSize.bytes, UInt64.toNat_mul, UInt16.toNat_toUInt64]
  change (size.units16.toNat * 16) % 18446744073709551616 < 2147483648
  simp only [UInt16.size] at bound
  omega

theorem frame_imm (size : FrameSize) : (Table.fullImm .w64).norm size.bytes = size.bytes := by
  have small := frame_bound size
  simp only [Table.fullImm, ImmKind.norm, signExtend32]
  have low : size.bytes.toUInt32 < 0x80000000 := by
    rw [UInt32.lt_iff_toNat_lt, UInt64.toNat_toUInt32]
    simp only [UInt32.reduceToNat]
    omega
  simp only [low, if_true]
  apply UInt64.toNat_inj.mp
  simp only [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
  omega

open Encode in
/-- The row `aluImmRow` chooses carries an immediate with the requested
value at the operation width, provided the full-size form can hold it. -/
theorem aluImmRow_spec (mn : Mnemonic) (width : Width) (target : Arg) (value : Word)
    (full : width.truncate ((Table.fullImm width).norm value) = width.truncate value) :
    ∃ form imm, (form = .MI8 ∨ form = .MI) ∧
      aluImmRow mn width target value = ({ mn, w := width, form }, [target, .imm imm]) ∧
      width.truncate imm = width.truncate value := by
  unfold aluImmRow
  split
  · rename_i fits
    exact ⟨_, _, .inl rfl, rfl, fitsImm8_truncate fits⟩
  · exact ⟨_, _, .inr rfl, rfl, full⟩

def AluOp.arith : AluOp → Table.Arith
  | .add => Table.addArith
  | .sub => Table.subArith
  | .and => Table.andArith
  | .or => Table.orArith
  | .xor => Table.xorArith

theorem desc_alu (operation : AluOp) (width : Width) (form : OpEn) :
    desc { mn := operation.mnemonic, w := width, form } = Table.arithDesc operation.arith width form := by
  cases operation <;> rfl

theorem AluOp.arith_sem (operation : AluOp) (width : Width) :
    operation.arith.sem width = Table.aluSem operation width := by
  cases operation <;> rfl

theorem AluOp.arith_role (operation : AluOp) : operation.arith.role = .readWrite := by
  cases operation <;> rfl

section
variable (runtime : Runtime) (checked : Checked) (machine : Machine)

@[simp] theorem executeInstr_mov (width : Width) (destination : GPR) (source : MoveSource) :
    executeInstr runtime checked (.mov width destination source) machine =
      machine.advanceWith (machine.core.writeReg width destination (source.eval machine.core)) := by
  cases source with
  | reg source =>
      simp [Instr.mov, executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.movDesc, Table.rmSlot,
        Table.regSlot, Table.moveSem, readSlots, writeSlots, Arg.load, Arg.store, Except.mapError,
        MoveSource.eval]
  | imm value =>
      cases width with
      | w64 =>
          simp only [Instr.mov, Instr.ofRow, movImmRow, MoveSource.eval]
          split
          · rename_i small
            simp only [executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.movDesc,
              Table.regSlot, Table.immSlot, Table.moveSem, readSlots, writeSlots, Arg.load, Arg.store,
              Except.mapError, bind, Except.bind, pure, Except.pure, List.headD_cons]
            have low : Width.w32.truncate (ImmKind.imm32.norm value) = value := by
              rw [Encode.norm_truncate .imm32 .w32 _ (by decide) rfl, Encode.truncate32_of_small _ small]
            simp only [Core.writeReg, low]
          · split <;>
              simp only [executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.movDesc,
                Table.regSlot, Table.rmSlot, Table.immSlot, Table.moveSem, readSlots, writeSlots, Arg.load,
                Arg.store, Except.mapError, bind, Except.bind, pure, Except.pure, List.headD_cons]
      | w8 | w16 | w32 =>
          simp only [Instr.mov, Instr.ofRow, movImmRow, MoveSource.eval, executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.movDesc,
            Table.regSlot, Table.immSlot, Table.moveSem, readSlots, writeSlots, Arg.load, Arg.store,
            Except.mapError, bind, Except.bind, pure, Except.pure, List.headD_cons]
          rw [Encode.writeReg_congr _ _ _ _ _ (Encode.moveImm_truncate _ value)]

@[simp] theorem executeInstr_lea (destination : GPR) (address : MemAddr) :
    executeInstr runtime checked (.lea destination address) machine =
      machine.advanceWith (machine.core.setReg destination (address.eval machine.core)) := by
  simp [Instr.lea, executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.leaDesc, Table.regSlot,
    Table.moveSem, readSlots, writeSlots, Arg.address, Arg.store, Except.mapError, Core.writeReg]

@[simp] theorem executeInstr_alu (operation : AluOp) (width : Width) (destination : GPR) (source : AluSource) :
    executeInstr runtime checked (.alu operation width destination source) machine =
      machine.advanceWith (machine.core.writeReg width destination
        (operation.eval (machine.core.readReg destination) (source.eval machine.core))) := by
  cases source with
  | reg source =>
      simp only [Instr.alu, executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc_alu,
        Table.arithDesc, AluOp.arith_sem, AluOp.arith_role, Table.rmSlot, Table.regSlot, Table.aluSem,
        readSlots, writeSlots, Arg.load, Arg.store, Except.mapError, AluSource.eval, bind, Except.bind, pure,
        Except.pure, List.headD_cons, List.tail_cons]
  | imm value =>
      obtain ⟨form, imm, form_ok, row, low⟩ := aluImmRow_spec operation.mnemonic width (.reg destination)
        (signExtend32 value) (Encode.fullImm_truncate _ _)
      simp only [Instr.alu, Instr.ofRow, row, AluSource.eval]
      rcases form_ok with rfl | rfl <;>
      simp only [executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs,
        Op.stage, desc_alu, Table.arithDesc, AluOp.arith_sem, AluOp.arith_role, Table.rmSlot, Table.immSlot,
        Table.aluSem, readSlots, writeSlots, Arg.load, Arg.store, Except.mapError, bind,
        Except.bind, pure, Except.pure, List.headD_cons, List.tail_cons] <;>
      exact congrArg machine.advanceWith (Encode.writeReg_congr _ _ _ _ _
        (Encode.alu_congr_right _ _ _ _ _ low))

@[simp] theorem executeInstr_imul (width : MulWidth) (destination source : GPR) :
    executeInstr runtime checked (.imul width destination source) machine =
      machine.advanceWith (machine.core.writeReg width.width destination
        (machine.core.readReg destination * machine.core.readReg source)) := by
  simp [Instr.imul, executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.imulDesc, Table.rmSlot,
    Table.regSlot, Table.mulSem, readSlots, writeSlots, Arg.load, Arg.store, Except.mapError]

@[simp] theorem executeInstr_load (width : Width) (destination : GPR) (address : MemAddr) :
    executeInstr runtime checked (.load width destination address) machine =
      match machine.core.loadReg? width destination (address.eval machine.core) with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok loaded => machine.advanceWith loaded := by
  cases width <;>
    simp only [Instr.load, executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.movzxDesc,
      Table.movDesc, Table.rmSlot, Table.regSlot, Table.zeroExtendSem, Table.moveSem, readSlots, writeSlots,
      Arg.load, Arg.store, Except.mapError, Core.loadReg?, MemAddr.normalize_eval] <;>
    cases machine.core.memory.read? _ (address.eval machine.core) <;>
    simp [Core.writeReg, truncate32_of_narrow, Encode.truncate64]

@[simp] theorem executeInstr_store (width : Width) (address : MemAddr) (source : GPR) :
    executeInstr runtime checked (.store width address source) machine =
      match machine.core.storeReg? width (address.eval machine.core) source with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok stored => machine.advanceWith stored := by
  simp only [Instr.store, executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.movDesc, Table.rmSlot,
    Table.regSlot, Table.moveSem, readSlots, writeSlots, Arg.load, Arg.store, Except.mapError, Core.storeReg?,
    MemAddr.normalize_eval]
  cases hw : machine.core.memory.write? width (address.eval machine.core) (machine.core.readReg source) <;>
    simp [hw] <;> rfl

@[simp] theorem executeInstr_push (source : GPR) :
    executeInstr runtime checked (.push source) machine =
      match machine.core.memory.write64? (machine.core.readReg .rsp - 8) (machine.core.readReg source) with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok memory =>
          machine.advanceWith { machine.core.setReg .rsp (machine.core.readReg .rsp - 8) with memory } := by
  simp only [Instr.push, executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.pushDesc, Table.regSlot,
    Table.moveSem, readSlots, writeSlots, Arg.load, Except.mapError]
  cases hw : machine.core.memory.write64? (machine.core.readReg .rsp - 8) (machine.core.readReg source) <;>
    simp [hw] <;> rfl

@[simp] theorem executeInstr_pop (destination : GPR) :
    executeInstr runtime checked (.pop destination) machine =
      match machine.core.memory.read64? (machine.core.readReg .rsp) with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok value =>
          machine.advanceWith ((machine.core.setReg .rsp (machine.core.readReg .rsp + 8)).setReg destination value) := by
  simp only [Instr.pop, executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.popDesc, Table.regSlot,
    Table.moveSem, readSlots, writeSlots, Arg.store, Except.mapError]
  cases machine.core.memory.read64? (machine.core.readReg .rsp) <;> simp [Core.writeReg]

@[simp] theorem executeInstr_allocFrame (size : FrameSize) :
    executeInstr runtime checked (.allocFrame size) machine =
      machine.advanceWith (machine.core.setReg .rsp (machine.core.readReg .rsp - size.bytes)) := by
  obtain ⟨form, imm, form_ok, row, low⟩ := aluImmRow_spec .sub .w64 (.reg .rsp) size.bytes (by rw [frame_imm])
  simp only [Encode.truncate64] at low
  subst low
  simp only [Instr.allocFrame, Instr.ofRow, row]
  rcases form_ok with rfl | rfl <;>
  simp [executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc,
    Table.arithDesc, Table.subArith, Table.Arith.sem, Table.Arith.role, Table.rmSlot, Table.immSlot, Table.aluSem,
    readSlots, writeSlots, Arg.load, Arg.store, Except.mapError, AluOp.eval, Core.writeReg]

@[simp] theorem executeInstr_freeFrame (size : FrameSize) :
    executeInstr runtime checked (.freeFrame size) machine =
      machine.advanceWith (machine.core.setReg .rsp (machine.core.readReg .rsp + size.bytes)) := by
  obtain ⟨form, imm, form_ok, row, low⟩ := aluImmRow_spec .add .w64 (.reg .rsp) size.bytes (by rw [frame_imm])
  simp only [Encode.truncate64] at low
  subst low
  simp only [Instr.freeFrame, Instr.ofRow, row]
  rcases form_ok with rfl | rfl <;>
  simp [executeInstr, Machine.afterRow, Op.exec, Op.run, Op.inputs, Op.stage, desc,
    Table.arithDesc, Table.addArith, Table.Arith.sem, Table.Arith.role, Table.rmSlot, Table.immSlot, Table.aluSem,
    readSlots, writeSlots, Arg.load, Arg.store, Except.mapError, AluOp.eval, Core.writeReg]

@[simp] theorem executeInstr_spill (slot : StackSlot) (source : GPR) :
    executeInstr runtime checked (.spill slot source) machine =
      match machine.core.storeReg? .w64 (machine.core.readReg .rbp - slot.displacement) source with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok stored => machine.advanceWith stored := by
  rw [Instr.spill, executeInstr_store, Encode.spillAddress_eval]

@[simp] theorem executeInstr_reload (destination : GPR) (slot : StackSlot) :
    executeInstr runtime checked (.reload destination slot) machine =
      match machine.core.loadReg? .w64 destination (machine.core.readReg .rbp - slot.displacement) with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok loaded => machine.advanceWith loaded := by
  rw [Instr.reload, executeInstr_load, Encode.spillAddress_eval]

end

end Compilatrix.X86
