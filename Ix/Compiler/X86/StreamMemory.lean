import Ix.Compiler.X86.StreamRun

/-! Bytewise memory correspondence for physical return addresses. A call
adds eight differing bytes; an ordinary write clears the bytes it overwrites.
RET retains residual differences in the released slot, so stack reuse does
not rely on an incorrect equality after popping a frame. -/

namespace Ix.Compiler.X86.Stream

abbrev Holes := Word → Prop

def inRange (address : Word) (count : Nat) (candidate : Word) : Prop :=
  ∃ index < count, candidate = address + UInt64.ofNat index

def addRange (holes : Holes) (address : Word) (count : Nat) : Holes :=
  fun candidate => holes candidate ∨ inRange address count candidate

def clearRange (holes : Holes) (address : Word) (count : Nat) : Holes :=
  fun candidate => holes candidate ∧ ¬inRange address count candidate

def ReadableData (holes : Holes) (address : Word) (count : Nat) : Prop :=
  ∀ index < count, ¬holes (address + UInt64.ofNat index)

structure MemoryRelated (holes : Holes) (logical physical : Memory) : Prop where
  readable : logical.readable = physical.readable
  writable : logical.writable = physical.writable
  bytes : ∀ address, ¬holes address → logical.bytes address = physical.bytes address

theorem MemoryRelated.refl (memory : Memory) : MemoryRelated (fun _ => False) memory memory :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem MemoryRelated.read {holes : Holes} {logical physical : Memory}
    (related : MemoryRelated holes logical physical) (width : Width) (address : Word)
    (data : ReadableData holes address width.bytes) : logical.read width address = physical.read width address :=
  Memory.readLittle_congr _ _ _ _ (fun index bound => related.bytes _ (data index bound))

theorem MemoryRelated.read? {holes : Holes} {logical physical : Memory}
    (related : MemoryRelated holes logical physical) (width : Width) (address : Word)
    (data : ReadableData holes address width.bytes) : logical.read? width address = physical.read? width address := by
  simp only [Memory.read?, related.readable, related.read width address data]

@[simp] theorem writeLittle_readable (memory : Memory) (address value : Word) (count : Nat) :
    (memory.writeLittle address value count).readable = memory.readable := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

@[simp] theorem writeLittle_writable (memory : Memory) (address value : Word) (count : Nat) :
    (memory.writeLittle address value count).writable = memory.writable := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

theorem outside_range {address candidate : Word} {count : Nat}
    (outside : ¬inRange address count candidate) :
    ∀ index < count, candidate ≠ address + UInt64.ofNat index := by
  intro index bound equal
  exact outside ⟨index, bound, equal⟩

theorem MemoryRelated.write_same {holes : Holes} {logical physical : Memory}
    (related : MemoryRelated holes logical physical) (address value : Word) (count : Nat)
    (bound : count ≤ 8) :
    MemoryRelated (clearRange holes address count)
      (logical.writeLittle address value count) (physical.writeLittle address value count) := by
  refine ⟨by simpa using related.readable, by simpa using related.writable, ?_⟩
  intro candidate visible
  by_cases inside : inRange address count candidate
  · obtain ⟨index, indexBound, rfl⟩ := inside
    rw [Memory.writeLittle_bytes _ _ _ bound indexBound, Memory.writeLittle_bytes _ _ _ bound indexBound]
  · have wasVisible : ¬holes candidate := fun hidden => visible ⟨hidden, inside⟩
    rw [Memory.writeLittle_bytes_outside _ _ _ _ _ (outside_range inside),
      Memory.writeLittle_bytes_outside _ _ _ _ _ (outside_range inside), related.bytes _ wasVisible]

theorem MemoryRelated.write_different {holes : Holes} {logical physical : Memory}
    (related : MemoryRelated holes logical physical) (address logicalValue physicalValue : Word) (count : Nat) :
    MemoryRelated (addRange holes address count)
      (logical.writeLittle address logicalValue count) (physical.writeLittle address physicalValue count) := by
  refine ⟨by simpa using related.readable, by simpa using related.writable, ?_⟩
  intro candidate visible
  have wasVisible : ¬holes candidate := fun hidden => visible (Or.inl hidden)
  have outside : ¬inRange address count candidate := fun inside => visible (Or.inr inside)
  rw [Memory.writeLittle_bytes_outside _ _ _ _ _ (outside_range outside),
    Memory.writeLittle_bytes_outside _ _ _ _ _ (outside_range outside), related.bytes _ wasVisible]

def SlotMapped (program : Program) (base : Word) (memory : Memory) (frame : ReturnFrame) : Prop :=
  ∃ offset, pcOffset? program frame.continuation = some offset ∧
    memory.read64 frame.returnSlot = base + UInt64.ofNat offset

def FramesMapped (program : Program) (base : Word) (memory : Memory) (frames : List ReturnFrame) : Prop :=
  ∀ frame ∈ frames, SlotMapped program base memory frame

/-- Ordinary writes may reuse retired return slots. Active frames still
protect their concrete eight-byte return-address ranges. -/
def FramesDisjoint (frames : List ReturnFrame) (address : Word) (count : Nat) : Prop :=
  ∀ frame ∈ frames, ∀ i < 8, ∀ j < count,
    frame.returnSlot + UInt64.ofNat i ≠ address + UInt64.ofNat j

theorem FramesMapped.write {program : Program} {base : Word} {memory : Memory} {frames : List ReturnFrame}
    (mapped : FramesMapped program base memory frames) (address value : Word) (count : Nat)
    (disjoint : FramesDisjoint frames address count) :
    FramesMapped program base (memory.writeLittle address value count) frames := by
  intro frame member
  obtain ⟨offset, pc, slot⟩ := mapped frame member
  refine ⟨offset, pc, ?_⟩
  have same : (memory.writeLittle address value count).read64 frame.returnSlot = memory.read64 frame.returnSlot := by
    apply Memory.readLittle_congr
    intro i bound
    exact Memory.writeLittle_bytes_outside _ _ _ _ _ (disjoint frame member i bound)
  rw [same, slot]

structure CoreRelated (program : Program) (base : Word) (holes : Holes) (frames : List ReturnFrame)
    (logical physical : Core) : Prop where
  registers : logical.registers = physical.registers
  memory : MemoryRelated holes logical.memory physical.memory
  frames : FramesMapped program base physical.memory frames

theorem CoreRelated.readReg {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical) (register : GPR) :
    logical.readReg register = physical.readReg register := congrFun related.registers register

theorem CoreRelated.address {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical) (address : MemAddr) :
    address.eval logical = address.eval physical := by
  simp [MemAddr.eval, related.readReg]

theorem CoreRelated.setReg {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (register : GPR) (value : Word) :
    CoreRelated program base holes frames (logical.setReg register value) (physical.setReg register value) :=
  ⟨congrArg (fun registers => registers.set register value) related.registers, related.memory, related.frames⟩

theorem CoreRelated.writeReg {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (width : Width) (register : GPR) (value : Word) :
    CoreRelated program base holes frames (logical.writeReg width register value) (physical.writeReg width register value) := by
  cases width <;> simp only [Core.writeReg, related.readReg] <;> exact related.setReg _ _

theorem CoreRelated.write {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (address value : Word) (count : Nat) (bound : count ≤ 8) (disjoint : FramesDisjoint frames address count) :
    CoreRelated program base (clearRange holes address count) frames
      { logical with memory := logical.memory.writeLittle address value count }
      { physical with memory := physical.memory.writeLittle address value count } :=
  ⟨related.registers, related.memory.write_same address value count bound, related.frames.write address value count disjoint⟩

end Ix.Compiler.X86.Stream
