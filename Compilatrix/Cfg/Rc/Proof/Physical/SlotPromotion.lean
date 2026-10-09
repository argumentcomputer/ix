import Compilatrix.Cfg.Rc.Proof.Physical.HeapAppend

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Lir
open Compilatrix.Rt.Rc.Procs

def publishSlot (fresh : Nat) (address : Word) (slot : Slot) : Slot :=
  if slot.address = address then {slot with kind := .live fresh} else slot

def publishSlots (fresh : Nat) (address : Word) (slots : List Slot) : List Slot :=
  slots.map (publishSlot fresh address)

@[simp] theorem publishSlot_address (fresh : Nat) (address : Word) (slot : Slot) :
    (publishSlot fresh address slot).address = slot.address := by unfold publishSlot; split <;> rfl

@[simp] theorem publishSlot_class (fresh : Nat) (address : Word) (slot : Slot) :
    (publishSlot fresh address slot).cls = slot.cls := by unfold publishSlot; split <;> rfl

theorem publishSlots_get {fresh : Nat} {address : Word} {slots : List Slot} {i : Nat} {slot : Slot}
    (lookup : (publishSlots fresh address slots)[i]? = some slot) :
    ∃ before, slots[i]? = some before ∧ slot = publishSlot fresh address before := by
  rw [publishSlots, List.getElem?_map] at lookup
  cases previous : slots[i]? with
  | none => simp [previous] at lookup
  | some before =>
    simp only [previous, Option.map_some, Option.some.injEq] at lookup
    exact ⟨before, rfl, lookup.symm⟩

theorem partition_address_unique {heap : Own.Heap} {addresses : AddressMap}
    {base bump limit : Word} {slots : List Slot}
    (partition : ArenaPartition heap addresses base bump limit slots)
    {first second : Slot} (hm : first ∈ slots) (hn : second ∈ slots)
    (same : first.address = second.address) : first = second := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hn
  by_cases equal : i = j
  · subst j
    exact Option.some.inj (hi.symm.trans hj)
  · have separated := partition.disjoint i j first second hi hj equal
    have firstPositive := (partition.valid first hm).1
    have secondPositive := (partition.valid second hn).1
    have sameNat := congrArg UInt64.toNat same
    rcases separated with h | h <;> omega

/-- A reserved slot becomes the new abstract cell without changing any byte
interval, coverage fact, or old live placement. -/
theorem partition_publish {heap : Own.Heap} {addresses : AddressMap} {base bump limit : Word}
    {slots : List Slot} (partition : ArenaPartition heap addresses base bump limit slots)
    {chosen : Slot} (member : chosen ∈ slots) (reserved : chosen.kind = .reserved)
    (body : Own.Body) (sizeClass : chosen.cls = Rt.Rc.smallClass body.fields.length) :
    ArenaPartition (heap.alloc .rc body).2 (placeFresh addresses heap.size chosen.address)
      base bump limit (publishSlots heap.size chosen.address slots) := by
  refine {
    bounds := partition.bounds
    valid := ?_
    disjoint := ?_
    accounted := ?_
    live := ?_
    placed := ?_
    pending := ?_ }
  · intro slot present
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp present
    simpa using partition.valid old oldMember
  · intro i j first second hi hj different
    obtain ⟨oldFirst, oldI, rfl⟩ := publishSlots_get hi
    obtain ⟨oldSecond, oldJ, rfl⟩ := publishSlots_get hj
    simpa using partition.disjoint i j oldFirst oldSecond oldI oldJ different
  · intro n lower upper
    obtain ⟨slot, present, interval⟩ := partition.accounted n lower upper
    refine ⟨publishSlot heap.size chosen.address slot, List.mem_map.mpr ⟨slot, present, rfl⟩, ?_⟩
    simpa using interval
  · intro slot present location kind
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp present
    by_cases selected : old.address = chosen.address
    · have same := partition_address_unique partition oldMember member selected
      subst old
      have fresh : heap.size = location := by simpa [publishSlot] using kind
      subst location
      exact ⟨1, body, by simp [allocated_cell], by simp [placeFresh], by simpa using sizeClass⟩
    · have oldKind : old.kind = .live location := by simpa [publishSlot, selected] using kind
      obtain ⟨refs, oldBody, oldCell, oldMap, oldClass⟩ := partition.live old oldMember location oldKind
      have bound : location < heap.size := (Array.getElem?_eq_some_iff.mp oldCell).1
      refine ⟨refs, oldBody, allocated_old oldCell, ?_, ?_⟩
      · simpa [placeFresh, Nat.ne_of_lt bound] using oldMap
      · simpa using oldClass
  · intro location refs other cell
    by_cases fresh : location = heap.size
    · subst location
      refine ⟨publishSlot heap.size chosen.address chosen,
        List.mem_map.mpr ⟨chosen, member, rfl⟩, ?_⟩
      simp [publishSlot]
    · have oldCell : heap.cell? location = some (.live refs .dyn other) := by
        simpa only [allocated_cell, if_neg fresh] using cell
      obtain ⟨old, oldMember, oldKind⟩ := partition.placed location refs other oldCell
      have otherAddress : old.address ≠ chosen.address := by
        intro same
        have equal := partition_address_unique partition oldMember member same
        subst old
        rw [reserved] at oldKind
        cases oldKind
      exact ⟨publishSlot heap.size chosen.address old, List.mem_map.mpr ⟨old, oldMember, rfl⟩,
        by simpa [publishSlot, otherAddress] using oldKind⟩
  · intro slot present location suffix predecessor kind
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp present
    by_cases selected : old.address = chosen.address
    · simp [publishSlot, selected] at kind
    · have oldKind : old.kind = .pending location suffix predecessor := by
        simpa [publishSlot, selected] using kind
      have dead := partition.pending old oldMember location suffix predecessor oldKind
      have bound : location < heap.size := (Array.getElem?_eq_some_iff.mp dead).1
      simpa only [allocated_cell, if_neg (Nat.ne_of_lt bound)] using dead


end Compilatrix.Cfg.Rc.Native
