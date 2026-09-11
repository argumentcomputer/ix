import Ix.Compiler.X86.WordRegionSafeControl

namespace Ix.Compiler.X86.WordRegion

def State.call (layout : Layout) (state : State) (slot : Nat) (block : BlockId) (offset : Nat) : State :=
  (state.setReg .rsp (layout.address slot)).setWord slot (PC.mk block (UInt32.ofNat (offset + 1))).encode

theorem call_safeStep {layout : Layout} {outside memory : Memory} {state : State} {index : Nat}
    {checked : Checked} {block target : BlockId} {offset : Nat} {returns : List ReturnFrame} {holes : Stream.Holes}
    (represented : Realizes layout outside state.words memory) (bound : index < layout.slots)
    (address : state.registers .rsp - 8 = layout.address index)
    (segment : Straight.Segment checked block offset [.call target])
    (fits : offset + 1 < UInt32.size) (valid : checked.program.hasBlock target = true)
    (aligned : SysV.callSiteAligned (state.registers .rsp) = true)
    (disjoint : Stream.FramesDisjoint returns (layout.address index) 8) :
    ∃ nextMemory, Realizes layout outside (state.call layout index block offset).words nextMemory ∧
      Stream.SafeSteps Runtime.rejecting checked 1 holes (inFrame (state.core memory) block offset returns)
        (Stream.addRange holes (layout.address index) 8)
        (inFrame ((state.call layout index block offset).core nextMemory) target 0
          (callFrame (state.core memory) block offset :: returns)) := by
  let nextMemory := memory.write64 (layout.address index) (PC.mk block (UInt32.ofNat (offset + 1))).encode
  have writable := represented.writable index bound
  have one := call_inFrame segment fits valid Runtime.rejecting (state.core memory) returns aligned
    (by simpa only [State.core, Core.readReg, address] using writable)
  have effect : callCore (state.core memory) block offset = (state.call layout index block offset).core nextMemory := by
    simp [callCore, callFrame, State.core, Core.readReg, State.call, State.setReg, State.setWord, Core.setReg, address, nextMemory]
  rw [effect] at one
  obtain ⟨code, found, reads⟩ := segment
  have head := reads 0 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero] at head
  have safe : Stream.SafeAt checked.program holes (inFrame (state.core memory) block offset returns) := by
    simp [Stream.SafeAt, inFrame, UInt32.toNat_ofNat_of_lt' (by omega : offset < UInt32.size), found, head,
      State.core, Core.readReg, address, aligned, writable, disjoint]
  have changed : Stream.holeStep checked.program (inFrame (state.core memory) block offset returns) holes =
      Stream.addRange holes (layout.address index) 8 := by
    simp [Stream.holeStep, inFrame, UInt32.toNat_ofNat_of_lt' (by omega : offset < UInt32.size), found, head,
      State.core, Core.readReg, address]
  exact ⟨nextMemory, represented.write64 bound _, by simpa only [changed] using Stream.SafeSteps.single safe one⟩

end Ix.Compiler.X86.WordRegion
