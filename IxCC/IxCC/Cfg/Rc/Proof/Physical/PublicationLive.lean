import IxCC.Cfg.Rc.Proof.Physical.PublicationFrames
import IxCC.Cfg.Rc.Proof.Physical.PublicationTokens
import IxCC.Cfg.Rc.Proof.Physical.Reserved
import IxCC.Rt.Rc.Gen.Proof.Scanned

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Gen (fieldsClass)
open IxCC.Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

theorem publication_fields_bounded {heap : Heap} {external : Nat → Nat} {body : Own.Body}
    (fields : Balance heap external body.fields) : Own.Plain.ValuesBounded heap.size body.fields := by
  intro value member
  cases value with
  | loc child =>
    obtain ⟨refs, other, cell⟩ := publication_children fields child member
    exact (Array.getElem?_eq_some_iff.mp cell).1
  | lit _ | ctor0 _ | erased => trivial

/-- Complete live-heap publication: all old cells survive the real stores,
the address map extends only at the fresh logical index, the new cell has
exact initialized fields, and its physical interval is disjoint from every
old live cell. The chosen reserved slot may be recycled physical storage. -/
theorem publication_heapLive {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (idle : Gen.ReleaseInvariant maxClass heap addresses mem
      (fun location => external location + refsIn location body.fields) none []
      context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (reserved : chosen.kind = .reserved)
    (sizeClass : chosen.cls = fieldsClass body.fields.length)
    (storage : ReservedCell mem chosen.address body) (words : Nat → Word)
    (values : ∀ j value, body.fields[j]? = some value → valueWord addresses value = some (words j)) :
    Gen.HeapLive (heap.alloc .rc body).2 (placeFresh addresses heap.size chosen.address)
      (publishFields mem chosen.address words (List.range body.fields.length)) := by
  have fields := idle_field_tokens idle
  have bounded := publication_fields_bounded fields
  have old := heapLive_placeFresh (publication_old_live idle member reserved sizeClass words) chosen.address
  have fresh := storage.publish (placeFresh addresses heap.size chosen.address) words (by
    intro j value lookup
    rw [placeFresh_old (bounded value (List.mem_of_getElem? lookup))]
    exact values j value lookup)
  apply heapLive_append old (by simp [placeFresh]) fresh (publication_children fields)
  intro location refs other address cell mapped
  have locationBound : location < heap.size := (Array.getElem?_eq_some_iff.mp cell).1
  have oldMap : addresses location = some address := by
    simpa [placeFresh, Nat.ne_of_lt locationBound] using mapped
  obtain ⟨slot, slotMember, kind⟩ := idle.partition.placed location refs other cell
  obtain ⟨oldRefs, oldBody, oldCell, slotMap, slotClass⟩ := idle.partition.live slot slotMember location kind
  have bodyEqual : oldBody = other :=
    (Own.Cell.live.inj (Option.some.inj (oldCell.symm.trans cell))).2.2
  subst oldBody
  have addressEqual : slot.address = address := Option.some.inj (slotMap.symm.trans oldMap)
  subst address
  have different : chosen.address ≠ slot.address := by
    intro same
    have equal := partition_address_unique idle.partition member slotMember same
    subst slot
    rw [reserved] at kind
    cases kind
  have disjoint := partition_intervals idle.partition member slotMember different
  have hclass : chosen.cls = Gen.classOf body.ctor := by
    rw [sizeClass, Gen.classOf_fields storage.nscalar (by rw [storage.nobj]; exact storage.fields_small),
      storage.nobj]
  rw [hclass, slotClass] at disjoint
  simpa only [Gen.cellBytesOf] using disjoint


end IxCC.Cfg.Rc.Native
