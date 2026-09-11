import Ix.Compiler.X86.ScalarFrames
import Ix.Compiler.X86.WordRegionSafeTrace

namespace Ix.Compiler.X86.Scalar
open WordRegion

theorem byte_slots_distinct {layout : Layout} {left right a b : Nat}
    (leftBound : left < layout.slots) (rightBound : right < layout.slots)
    (different : left ≠ right) (aBound : a < 8) (bBound : b < 8) :
    layout.address left + UInt64.ofNat a ≠ layout.address right + UInt64.ofNat b := by
  intro equal
  have equal := congrArg UInt64.toNat equal
  rw [layout.byteAddress_toNat leftBound aBound, layout.byteAddress_toNat rightBound bBound] at equal
  omega

def FramesAbove (layout : Layout) (top : Nat) (returns : List ReturnFrame) : Prop :=
  ∀ frame ∈ returns, ∃ index, index < layout.slots ∧ top ≤ index ∧ frame.returnSlot = layout.address index

theorem FramesAbove.disjoint {layout : Layout} {top index : Nat} {returns : List ReturnFrame}
    (frames : FramesAbove layout top returns) (bound : index < layout.slots) (below : index < top) :
    Stream.FramesDisjoint returns (layout.address index) 8 := by
  intro frame member i iBound j jBound
  obtain ⟨slot, slotBound, above, address⟩ := frames frame member
  rw [address]
  exact byte_slots_distinct slotBound bound (by omega) iBound jBound

/-- Internal calls write structural return tokens at slot 33 modulo 34.
The external caller's return slot is excluded from this set. -/
def HolesIn (layout : Layout) (rootTop : Nat) (holes : Stream.Holes) : Prop :=
  ∀ address, holes address → ∃ slot offset,
    slot < layout.slots ∧ slot < rootTop ∧ slot % frameStride = 33 ∧ offset < 8 ∧
      address = layout.address slot + UInt64.ofNat offset

theorem HolesIn.empty (layout : Layout) (rootTop : Nat) : HolesIn layout rootTop (fun _ => False) :=
  fun _ impossible => impossible.elim

theorem HolesIn.mono {layout : Layout} {rootTop : Nat} {holes smaller : Stream.Holes}
    (valid : HolesIn layout rootTop holes) (subset : ∀ address, smaller address → holes address) :
    HolesIn layout rootTop smaller := fun address hidden => valid address (subset address hidden)

theorem HolesIn.clear {layout : Layout} {rootTop : Nat} {holes : Stream.Holes}
    (valid : HolesIn layout rootTop holes) (address : Word) (count : Nat) :
    HolesIn layout rootTop (Stream.clearRange holes address count) := valid.mono (fun _ h => h.1)

theorem HolesIn.add_return {layout : Layout} {rootTop index : Nat} {holes : Stream.Holes}
    (valid : HolesIn layout rootTop holes) (bound : index < layout.slots) (below : index < rootTop)
    (partition : index % frameStride = 33) :
    HolesIn layout rootTop (Stream.addRange holes (layout.address index) 8) := by
  intro address hidden
  rcases hidden with old | ⟨offset, offsetBound, equal⟩
  · exact valid address old
  · exact ⟨index, offset, bound, below, partition, offsetBound, equal⟩

theorem HolesIn.readable {layout : Layout} {rootTop index : Nat} {holes : Stream.Holes}
    (valid : HolesIn layout rootTop holes) (bound : index < layout.slots)
    (ordinary : index % frameStride ≠ 33 ∨ rootTop ≤ index) :
    Stream.ReadableData holes (layout.address index) 8 := by
  intro offset offsetBound hidden
  obtain ⟨slot, slotOffset, slotBound, below, partition, small, equal⟩ := valid _ hidden
  have different : index ≠ slot := by
    intro same
    subst slot
    rcases ordinary with normal | high
    · exact normal partition
    · omega
  exact byte_slots_distinct bound slotBound different offsetBound small equal

theorem Frame.local_ordinary {layout : Layout} (frame : Frame layout) {index : Nat} (bound : index < maxLocals) :
    frame.localIndex index % frameStride ≠ 33 := by
  have partition := frame.partition
  have enough := frame.enough
  simp only [Frame.localIndex, maxLocals, frameStride] at *
  omega

theorem Frame.base_ordinary {layout : Layout} (frame : Frame layout) : frame.baseIndex % frameStride ≠ 33 := by
  have partition := frame.partition
  have enough := frame.enough
  simp only [Frame.baseIndex, frameStride] at *
  omega

theorem Frame.local_disjoint {layout : Layout} {returns : List ReturnFrame} (frame : Frame layout)
    (frames : FramesAbove layout frame.top returns) (index : Nat) :
    Stream.FramesDisjoint returns (layout.address (frame.localIndex index)) 8 :=
  frames.disjoint (frame.local_bound index) (by have := frame.enough; simp only [Frame.localIndex]; omega)

theorem Frame.base_disjoint {layout : Layout} {returns : List ReturnFrame} (frame : Frame layout)
    (frames : FramesAbove layout frame.top returns) : Stream.FramesDisjoint returns (layout.address frame.baseIndex) 8 :=
  frames.disjoint frame.base_bound (by have := frame.enough; simp only [Frame.baseIndex]; omega)

end Ix.Compiler.X86.Scalar
