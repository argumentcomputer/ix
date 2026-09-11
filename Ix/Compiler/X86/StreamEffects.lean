import Ix.Compiler.X86.StreamMemory

/-! Preservation of return-address memory correspondence by ordinary
decoded instructions. Access premises describe concrete byte ranges; they
do not assume instruction effects or a simulation relation after execution. -/

namespace Ix.Compiler.X86.Stream

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

def operationReads (operation : Decode.Operation) (core : Core) : Option (Word × Nat) :=
  match operation with
  | .load width _ address => some (address.eval core, width.bytes)
  | .pop _ => some (core.readReg .rsp, 8)
  | _ => none

def operationWrites (operation : Decode.Operation) (core : Core) : Option (Word × Nat) :=
  match operation with
  | .store width address _ => some (address.eval core, width.bytes)
  | .push _ => some (core.readReg .rsp - 8, 8)
  | _ => none

def OperationSafe (holes : Holes) (frames : List ReturnFrame) (operation : Decode.Operation) (core : Core) : Prop :=
  (match operationReads operation core with
    | none => True | some (address, count) => ReadableData holes address count) ∧
  (match operationWrites operation core with
    | none => True | some (address, count) => FramesDisjoint frames address count)

def nextHoles (holes : Holes) (operation : Decode.Operation) (core : Core) : Holes :=
  match operationWrites operation core with
  | none => holes
  | some (address, count) => clearRange holes address count

def linearOperation : Decode.Operation → Bool
  | .call _ | .jump _ | .branch _ _ | .ret => false
  | _ => true

def CorePair (program : Program) (base : Word) (holes : Holes) (frames : List ReturnFrame) :
    Except ByteEval.Fault ByteEval.State → Except ByteEval.Fault ByteEval.State → Prop
  | .ok logical, .ok physical => CoreRelated program base holes frames logical.core physical.core
  | .error left, .error right => left = right
  | _, _ => False

theorem CoreRelated.operand {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (operand : Decode.Operand) : ByteEval.operand operand logical = ByteEval.operand operand physical := by
  cases operand <;> simp [ByteEval.operand, related.readReg]

theorem width_bytes_le (width : Width) : width.bytes ≤ 8 := by cases width <;> decide

theorem operation_pair (program : Program) (base rip : Word) (flags : ByteEval.Flags)
    (holes : Holes) (frames : List ReturnFrame) (logical physical : Core)
    (related : CoreRelated program base holes frames logical physical)
    (operation : Decode.Operation) (length : Nat) (linear : linearOperation operation = true)
    (safe : OperationSafe holes frames operation logical) :
    CorePair program base (nextHoles holes operation logical) frames
      (ByteEval.execute ⟨operation, length⟩ ⟨logical, rip, flags⟩)
      (ByteEval.execute ⟨operation, length⟩ ⟨physical, rip, flags⟩) := by
  cases operation with
  | mov width destination source =>
      simp only [ByteEval.execute, pure, Except.pure, CorePair, nextHoles, operationWrites]
      rw [← related.operand source]
      exact related.writeReg width destination _
  | lea destination source =>
      simp only [ByteEval.execute, pure, Except.pure, CorePair, nextHoles, operationWrites]
      rw [← related.address source]
      exact related.setReg destination _
  | alu operation width destination source =>
      simp only [ByteEval.execute, pure, Except.pure, CorePair, nextHoles, operationWrites]
      rw [← related.readReg destination, ← related.operand source]
      exact related.writeReg width destination _
  | imul width destination source =>
      simp only [ByteEval.execute, pure, Except.pure, CorePair, nextHoles, operationWrites]
      rw [← related.readReg destination, ← related.readReg source]
      exact related.writeReg width.width destination _
  | compare width left right =>
      exact related
  | load width destination source =>
      have readEqual := related.memory.read? width (source.eval logical) safe.1
      have address := related.address source
      cases loaded : logical.memory.read? width (source.eval logical) with
      | error fault =>
          simp [ByteEval.execute, Core.loadReg?, ← address, ← readEqual, loaded, Except.mapError, CorePair]
      | ok value =>
          simp only [ByteEval.execute, Core.loadReg?, ← address, ← readEqual, loaded, Except.mapError,
            bind, Except.bind, pure, Except.pure, CorePair, nextHoles, operationWrites]
          exact related.setReg destination (width.truncate value)
  | pop destination =>
      have readEqual := related.memory.read? .w64 (logical.readReg .rsp) safe.1
      cases loaded : logical.memory.read? .w64 (logical.readReg .rsp) with
      | error fault =>
          simp [ByteEval.execute, Memory.read64?, ← related.readReg .rsp, ← readEqual,
            loaded, Except.mapError, CorePair]
      | ok value =>
          simp only [ByteEval.execute, Memory.read64?, ← related.readReg .rsp, ← readEqual,
            loaded, Except.mapError, bind, Except.bind, pure, Except.pure,
            CorePair, nextHoles, operationWrites]
          exact (related.setReg .rsp _).setReg destination value
  | store width destination source =>
      have address := related.address destination
      have permissions := related.memory.writable
      cases allowed : Memory.rangeAllowed logical.memory.writable (destination.eval logical) width.bytes with
      | false =>
          simp [ByteEval.execute, Core.storeReg?, Memory.write?, ← address, ← permissions, allowed, Except.mapError, CorePair]
      | true =>
          simp only [ByteEval.execute, Core.storeReg?, Memory.write?, ← address, ← permissions, allowed,
            ↓reduceIte, Except.mapError, bind, Except.bind, pure, Except.pure, CorePair, nextHoles, operationWrites]
          rw [← related.readReg source]
          exact related.write _ _ _ (width_bytes_le width) safe.2
  | push source =>
      have permissions := related.memory.writable
      cases allowed : Memory.rangeAllowed logical.memory.writable (logical.readReg .rsp - 8) 8 with
      | false =>
          simp [ByteEval.execute, Memory.write64?, Memory.write?, ← related.readReg .rsp, ← permissions,
            Width.bytes, allowed, Except.mapError, CorePair]
      | true =>
          simp only [ByteEval.execute, Memory.write64?, Memory.write?, ← related.readReg .rsp, ← permissions,
            Width.bytes, allowed, ↓reduceIte, Except.mapError, bind, Except.bind, pure, Except.pure,
            CorePair, nextHoles, operationWrites]
          rw [← related.readReg source]
          exact (related.write _ _ 8 (by decide) safe.2).setReg .rsp _
  | call _ | jump _ | branch _ _ | ret => simp [linearOperation] at linear

theorem instruction_linear_operation (instruction : Instr) (linear : Encode.linearInstruction instruction = true) :
    linearOperation (Encode.instructionOperation instruction) = true := by
  cases instruction <;> simp_all [Encode.linearInstruction, Encode.instructionOperation, linearOperation]

end Ix.Compiler.X86.Stream
