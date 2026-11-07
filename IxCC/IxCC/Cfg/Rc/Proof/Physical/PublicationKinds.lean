import IxCC.Cfg.Rc.Proof.Physical.SlotPromotion
import IxCC.Rt.Rc.Proof.ReleaseInvariant

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Rt.Rc.Procs

theorem publishSlot_free {heap : Own.Heap} {addresses : AddressMap} {base bump limit : Word}
    {slots : List Slot} (partition : ArenaPartition heap addresses base bump limit slots)
    {chosen slot : Slot} (chosenMember : chosen ∈ slots) (reserved : chosen.kind = .reserved)
    (slotMember : slot ∈ slots) (fresh : Nat) :
    (publishSlot fresh chosen.address slot).kind = .free ↔ slot.kind = .free := by
  by_cases selected : slot.address = chosen.address
  · have same := partition_address_unique partition slotMember chosenMember selected
    subst slot
    simp [publishSlot, reserved]
  · simp [publishSlot, selected]

theorem publishSlot_pending {heap : Own.Heap} {addresses : AddressMap} {base bump limit : Word}
    {slots : List Slot} (partition : ArenaPartition heap addresses base bump limit slots)
    {chosen slot : Slot} (chosenMember : chosen ∈ slots) (reserved : chosen.kind = .reserved)
    (slotMember : slot ∈ slots) (fresh location : Nat) (suffix : List Own.RVal) (predecessor : Word) :
    (publishSlot fresh chosen.address slot).kind = .pending location suffix predecessor ↔
      slot.kind = .pending location suffix predecessor := by
  by_cases selected : slot.address = chosen.address
  · have same := partition_address_unique partition slotMember chosenMember selected
    subst slot
    simp [publishSlot, reserved]
  · simp [publishSlot, selected]

theorem publication_free_exact {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (reserved : chosen.kind = .reserved) (fresh : Nat) :
    ∀ slot ∈ publishSlots fresh chosen.address slots,
      slot.kind = .free ↔ slot.address ∈ lists slot.cls := by
  intro slot present
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp present
  rw [publishSlot_free idle.partition member reserved oldMember fresh]
  simpa using idle.free_exact old oldMember

theorem publication_free_placed {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (reserved : chosen.kind = .reserved) (fresh : Nat) :
    ∀ cls address, address ∈ lists cls →
      ∃ slot ∈ publishSlots fresh chosen.address slots,
        slot.address = address ∧ slot.cls = cls ∧ slot.kind = .free := by
  intro cls address present
  obtain ⟨old, oldMember, oldAddress, oldClass, oldKind⟩ := idle.free_placed cls address present
  refine ⟨publishSlot fresh chosen.address old, List.mem_map.mpr ⟨old, oldMember, rfl⟩, ?_, ?_, ?_⟩
  · simpa using oldAddress
  · simpa using oldClass
  · exact (publishSlot_free idle.partition member reserved oldMember fresh).mpr oldKind



end IxCC.Cfg.Rc.Native
