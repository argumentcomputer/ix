import Compilatrix.X86.UniqueSafeControl
import Compilatrix.X86.WordRegion
import Compilatrix.X86.StreamPermissions

/-! The allocating helper uses a disjoint finite stack region: its return
slot, one alignment word, and the external caller's return slot. Heap writes
preserve all three; CALL may change only the first. -/
namespace Compilatrix.X86.Allocating
open UniqueABI UniqueExecution

structure Stack (heap : Layout) where
  region : WordRegion.Layout
  slots : region.slots = 3
  aligned : region.base % 16 = 8
  disjoint : ∀ offset < 24, heap.allowed (region.base + UInt64.ofNat offset) = false

def Stack.top {heap : Layout} (stack : Stack heap) : Word := stack.region.address 2
def Stack.slot {heap : Layout} (stack : Stack heap) : Word := stack.region.address 0
def Stack.holes {heap : Layout} (stack : Stack heap) : Stream.Holes :=
  Stream.addRange (fun _ => False) stack.slot 8
def Stack.Available {heap : Layout} (stack : Stack heap) (memory : Memory) : Prop :=
  (∀ index < 3, Memory.rangeAllowed memory.readable (stack.region.address index) 8 = true) ∧
  (∀ index < 3, Memory.rangeAllowed memory.writable (stack.region.address index) 8 = true)

theorem Stack.subtract {heap : Layout} (stack : Stack heap) :
    stack.top - 8 = stack.region.address 1 ∧ stack.top - 8 - 8 = stack.slot := by
  constructor
  · exact stack.region.subtract (slot := 2) (count := 1) (by decide)
  · change stack.region.address 2 - UInt64.ofNat (8 * 1) - 8 = stack.region.address 0
    rw [stack.region.subtract (slot := 2) (count := 1) (by decide)]
    exact stack.region.subtract (slot := 1) (count := 1) (by decide)

theorem Stack.add {heap : Layout} (stack : Stack heap) :
    stack.slot + 8 = stack.region.address 1 ∧ stack.slot + 8 + 8 = stack.top := by
  constructor
  · exact stack.region.add 0 1
  · change stack.region.address 0 + UInt64.ofNat (8 * 1) + 8 = stack.region.address 2
    rw [stack.region.add 0 1]
    exact stack.region.add 1 1

theorem Stack.callAligned {heap : Layout} (stack : Stack heap) :
    SysV.callSiteAligned (stack.top - 8) = true := by
  rw [stack.subtract.1]
  have aligned := congrArg UInt64.toNat stack.aligned
  change stack.region.base.toNat % 16 = 8 at aligned
  simp only [SysV.callSiteAligned, beq_iff_eq]
  apply UInt64.toNat_inj.mp
  change (stack.region.address 1).toNat % 16 = 0
  rw [stack.region.address_toNat (by rw [stack.slots]; decide)]
  omega

theorem Stack.outside {heap : Layout} (stack : Stack heap) {index offset : Nat}
    (indexBound : index < 3) (offsetBound : offset < 8) :
    heap.allowed (stack.region.address index + UInt64.ofNat offset) = false := by
  have sum : stack.region.address index + UInt64.ofNat offset =
      stack.region.base + UInt64.ofNat (8 * index + offset) := by
    simp [WordRegion.Layout.address, UInt64.ofNat_add, UInt64.add_assoc]
  rw [sum]
  exact stack.disjoint _ (by omega)

theorem Stack.distinct {heap : Layout} (stack : Stack heap) {left right a b : Nat}
    (leftBound : left < 3) (rightBound : right < 3) (different : left ≠ right)
    (aBound : a < 8) (bBound : b < 8) :
    stack.region.address left + UInt64.ofNat a ≠ stack.region.address right + UInt64.ofNat b := by
  intro equal
  have equal := congrArg UInt64.toNat equal
  rw [stack.region.byteAddress_toNat (by rw [stack.slots]; exact leftBound) aBound,
    stack.region.byteAddress_toNat (by rw [stack.slots]; exact rightBound) bBound] at equal
  omega

theorem Stack.returnClean {heap : Layout} (stack : Stack heap) :
    Stream.ReadableData stack.holes stack.top 8 := by
  intro offset bound hidden
  rcases hidden with impossible | ⟨other, otherBound, equal⟩
  · exact impossible
  · exact stack.distinct (by decide) (by decide) (by decide) bound otherBound equal

theorem Stack.heapAccess {heap : Layout} (stack : Stack heap) (returns : List ReturnFrame)
    (frames : ∀ frame ∈ returns, frame.returnSlot = stack.slot) : HeapAccess heap stack.holes returns := by
  constructor
  · intro slot bound offset offsetBound hidden
    rcases hidden with impossible | ⟨other, otherBound, equal⟩
    · exact impossible
    · have allowed := heap.byteAllowed bound offsetBound
      rw [equal, Stack.slot, stack.outside (by decide : 0 < 3) otherBound] at allowed
      contradiction
  · intro slot bound frame member i iBound j jBound equal
    have allowed := heap.byteAllowed bound jBound
    rw [← equal, frames frame member, Stack.slot, stack.outside (by decide : 0 < 3) iBound] at allowed
    contradiction

theorem _root_.Compilatrix.X86.UniqueABI.Realizes.writeOutside
    {layout : Layout} {outside memory : Memory} {words : Words}
    (represented : Realizes layout outside words memory) (address value : Word)
    (disjoint : ∀ offset < 8, layout.allowed (address + UInt64.ofNat offset) = false) :
    Realizes layout (outside.write64 address value) words (memory.write64 address value) := by
  refine ⟨?_, by simpa using represented.readable, by simpa using represented.writable, ?_⟩
  · intro slot bound
    rw [← represented.view slot bound]
    apply Memory.readLittle_congr
    intro offset offsetBound
    apply Memory.write64_bytes_outside
    intro other otherBound equal
    have allowed := layout.byteAllowed bound offsetBound
    rw [equal, disjoint other otherBound] at allowed
    contradiction
  · intro candidate notAllowed
    by_cases inside : Stream.inRange address 8 candidate
    · obtain ⟨offset, bound, rfl⟩ := inside
      exact (Memory.writeLittle_bytes memory address value (by decide : 8 ≤ 8) bound).trans
        (Memory.writeLittle_bytes outside address value (by decide : 8 ≤ 8) bound).symm
    · rw [Memory.write64_bytes_outside _ _ _ _ (Stream.outside_range inside),
        Memory.write64_bytes_outside _ _ _ _ (Stream.outside_range inside), represented.frame _ notAllowed]

theorem _root_.Compilatrix.X86.UniqueABI.Realizes.readOutside
    {layout : Layout} {outside before after : Memory} {beforeWords afterWords : Words}
    (first : Realizes layout outside beforeWords before) (last : Realizes layout outside afterWords after)
    (address : Word) (disjoint : ∀ offset < 8, layout.allowed (address + UInt64.ofNat offset) = false) :
    after.read64 address = before.read64 address := by
  apply Memory.readLittle_congr
  intro offset bound
  rw [last.frame _ (disjoint offset bound), first.frame _ (disjoint offset bound)]

end Compilatrix.X86.Allocating

namespace Compilatrix.X86.Stream

/-- Internal CALL/RET preserve memory permissions as well as ordinary
instructions. The rejecting intrinsic environment introduces no new effects. -/
theorem rejecting_instruction_permissions (checked : Checked) (machine : Machine) (instruction : Instr) :
    Permissions machine.core (executeInstr Runtime.rejecting checked instruction machine).core := by
  by_cases linear : Encode.linearInstruction instruction = true
  · exact linear_permissions _ _ _ _ linear
  · cases instruction <;> simp_all only [Encode.linearInstruction]
    all_goals simp only [executeInstr, Runtime.rejecting, Memory.write64?, Memory.write?, Width.bytes]
    all_goals (repeat' split) <;> simp_all [Permissions, Machine.trap, Memory.write]
    all_goals
      rename_i target nextOption next writeResult memory aligned valid atNext stored
      by_cases allowed : Memory.rangeAllowed machine.core.memory.writable (machine.core.readReg .rsp - 8) 8 = true
      · simp only [allowed, ↓reduceIte, Except.ok.injEq] at stored
        subst memory
        simp
      · simp [allowed] at stored

theorem rejecting_step_permissions (checked : Checked) (machine : Machine) :
    Permissions machine.core (step Runtime.rejecting checked machine).core := by
  cases running : machine.status with
  | halted _ | trapped _ => simp [step, running, Permissions]
  | running =>
      cases found : checked.program.blocks[machine.pc.block.toNat]? with
      | none => simp [step, running, found, Machine.trap, Permissions]
      | some block =>
          cases instruction : block.instructions[machine.pc.offset.toNat]? with
          | some code => simpa [step, running, found, instruction] using rejecting_instruction_permissions checked machine code
          | none =>
              simp only [step, running, found, instruction]
              split
              · simp [Permissions, terminator_memory]
              · simp [Permissions, Machine.trap]

theorem _root_.Compilatrix.X86.Steps.rejecting_permissions {checked : Checked} {count : Nat}
    {before after : Machine} (steps : Steps Runtime.rejecting checked count before after) :
    Permissions before.core after.core := by
  induction steps with
  | refl => exact ⟨rfl, rfl⟩
  | @cons before middle after count first _ ih =>
      have next := rejecting_step_permissions checked before
      rw [first] at next
      exact ⟨ih.1.trans next.1, ih.2.trans next.2⟩

end Compilatrix.X86.Stream
