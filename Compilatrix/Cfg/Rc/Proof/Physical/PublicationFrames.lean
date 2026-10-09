import Compilatrix.Cfg.Rc.Proof.Physical.SlotPromotion
import Compilatrix.Cfg.Rc.Proof.Physical.PublishFrame
import Compilatrix.Rt.Rc.Proof.ReleaseInvariant

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Lir
open Compilatrix.Rt Compilatrix.Rt.Rc Compilatrix.Rt.Rc.Procs

theorem partition_intervals {heap : Own.Heap} {addresses : AddressMap}
    {base bump limit : Word} {slots : List Slot}
    (partition : ArenaPartition heap addresses base bump limit slots)
    {first second : Slot} (hm : first ∈ slots) (hn : second ∈ slots)
    (different : first.address ≠ second.address) :
    first.address.toNat + 8 * first.cls ≤ second.address.toNat ∨
      second.address.toNat + 8 * second.cls ≤ first.address.toNat := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hn
  apply partition.disjoint i j first second hi hj
  intro equal
  subst j
  have same : first = second := Option.some.inj (hi.symm.trans hj)
  exact different (congrArg Slot.address same)

theorem publication_slot_frame {heap : Own.Heap} {addresses : AddressMap}
    {base bump limit : Word} {slots : List Slot}
    (partition : ArenaPartition heap addresses base bump limit slots)
    {chosen other : Slot} (hm : chosen ∈ slots) (hn : other ∈ slots)
    (different : other.address ≠ chosen.address) {fields : Nat}
    (sizeClass : chosen.cls = smallClass fields) (words : Nat → Word) (mem : X86.Memory) :
    ObjectFrame mem (publishFields mem chosen.address words (List.range fields)) other.address (8 * other.cls) := by
  have chosenBounds := partition.valid chosen hm
  have otherBounds := partition.valid other hn
  have arena := partition.bounds
  have disjoint := partition_intervals partition hn hm different
  have fieldFit : chosen.address.toNat + 8 * (fields + 1) < 2^63 := by
    simp only [sizeClass, smallClass] at chosenBounds
    omega
  apply publishFields_objectFrame (List.range fields) chosen.address words (by omega)
    (fun i hi => fieldAddress_fit fieldFit (List.mem_range.mp hi)) (fun i hi => ?_) mem
  rw [fieldAddress_nat fieldFit (List.mem_range.mp hi)]
  simp only [sizeClass, smallClass] at disjoint
  have bound := List.mem_range.mp hi
  rcases disjoint with left | right
  · left; omega
  · right; omega

/-- Publication changes only the reserved slot's payload, so all previously
live cells retain their concrete bytes and their original address map. -/
theorem publication_old_live {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (reserved : chosen.kind = .reserved)
    {fields : Nat} (sizeClass : chosen.cls = smallClass fields) (words : Nat → Word) :
    HeapLive heap addresses (publishFields mem chosen.address words (List.range fields)) := by
  refine {cell := ?_, fields_live := idle.live.fields_live, disjoint := idle.live.disjoint}
  intro location refs mode body cell
  obtain ⟨dynamic, address, mapped, represented⟩ := idle.live.cell location refs mode body cell
  subst mode
  obtain ⟨slot, slotMember, kind⟩ := idle.partition.placed location refs body cell
  obtain ⟨otherRefs, otherBody, otherCell, otherMap, otherClass⟩ := idle.partition.live slot slotMember location kind
  have bodyEqual : otherBody = body :=
    (Own.Cell.live.inj (Option.some.inj (otherCell.symm.trans cell))).2.2
  subst otherBody
  have addressEqual : slot.address = address := Option.some.inj (otherMap.symm.trans mapped)
  subst address
  have different : slot.address ≠ chosen.address := by
    intro same
    have equal := partition_address_unique idle.partition slotMember member same
    subst slot
    rw [reserved] at kind
    cases kind
  refine ⟨rfl, slot.address, mapped, represented.frame ?_⟩
  have frame := publication_slot_frame idle.partition member slotMember different sizeClass words mem
  simpa only [otherClass, smallClass_bytes] using frame



end Compilatrix.Cfg.Rc.Native
