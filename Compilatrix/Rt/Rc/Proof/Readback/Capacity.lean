import Compilatrix.Rt.Rc.Proof.Readback.Fuel

set_option autoImplicit false
namespace Compilatrix.Rt.Rc.Procs.Readback
open Compilatrix.Lir (Word)
open Compilatrix.Own

theorem live_address_bounds {H : Heap} {addresses : AddressMap}
    {base bump limit : Word} {slots : List Slot}
    (partition : ArenaPartition H addresses base bump limit slots)
    {location refs : Nat} {body : Body}
    (cell : H.cell? location = some (.live refs .dyn body)) :
    ∃ address, addresses location = some address ∧
      base.toNat ≤ address.toNat ∧ address.toNat+8 ≤ limit.toNat := by
  obtain ⟨slot, member, kind⟩ := partition.placed location refs body cell
  obtain ⟨_, _, _, lower, upper⟩ := partition.valid slot member
  obtain ⟨refs', body', cell', mapping, cls⟩ := partition.live slot member location kind
  have positive := (partition.valid slot member).1
  exact ⟨slot.address, mapping, lower, by have := partition.bounds.2.1; omega⟩

def addressIndex (addresses : AddressMap) (base : Word) (location : Nat) : Nat :=
  (((addresses location).getD 0).toNat - base.toNat) / 8

theorem live_index_bound {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {base bump limit : Word} {slots : List Slot} {regionBytes : Nat}
    (heap : HeapLive H addresses mem)
    (partition : ArenaPartition H addresses base bump limit slots)
    (region : limit.toNat-base.toNat ≤ regionBytes)
    {location : Nat} (member : location ∈ liveLocations H H.size) :
    addressIndex addresses base location < regionBytes/8 := by
  have live := (List.mem_filter.mp member).2
  obtain ⟨refs, mode, body, cell⟩ := liveAt_iff.mp live
  obtain ⟨rfl, _, _, _⟩ := heap.cell location refs mode body cell
  obtain ⟨address, mapping, lower, upper⟩ := live_address_bounds partition cell
  simp only [addressIndex, mapping, Option.getD_some]
  omega

theorem live_index_injective {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {base bump limit : Word} {slots : List Slot}
    (heap : HeapLive H addresses mem)
    (partition : ArenaPartition H addresses base bump limit slots)
    {left right : Nat} (hl : left ∈ liveLocations H H.size)
    (hr : right ∈ liveLocations H H.size) (hne : left ≠ right) :
    addressIndex addresses base left ≠ addressIndex addresses base right := by
  obtain ⟨rl, ml, bl, cl⟩ := liveAt_iff.mp (List.mem_filter.mp hl).2
  obtain ⟨rr, mr, br, cr⟩ := liveAt_iff.mp (List.mem_filter.mp hr).2
  obtain ⟨rfl, _, _, _⟩ := heap.cell left rl ml bl cl
  obtain ⟨rfl, _, _, _⟩ := heap.cell right rr mr br cr
  obtain ⟨al, mapl, lowerl, _⟩ := live_address_bounds partition cl
  obtain ⟨ar, mapr, lowerr, _⟩ := live_address_bounds partition cr
  have separated := heap.disjoint left right rl rr bl br al ar cl cr mapl mapr hne
  simp only [addressIndex, mapl, mapr, Option.getD_some]
  unfold cellBytes at separated
  omega

/-- Each live logical location occupies a distinct physical word interval.
This cardinality bound ignores dead history and counts neither field aliases
nor repeated paths twice. -/
theorem liveBefore_capacity {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {base bump limit : Word} {slots : List Slot} {regionBytes : Nat}
    (heap : HeapLive H addresses mem)
    (partition : ArenaPartition H addresses base bump limit slots)
    (region : limit.toNat-base.toNat ≤ regionBytes) :
    liveBefore H H.size ≤ regionBytes/8 := by
  have distinct : ((liveLocations H H.size).map (addressIndex addresses base)).Nodup := by
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp_of_mem
      (fun hl hr hn => live_index_injective heap partition hl hr hn)
      (liveLocations_nodup H H.size)
  have subset : (liveLocations H H.size).map (addressIndex addresses base) ⊆
      List.range (regionBytes/8) := by
    intro index member
    obtain ⟨location, live, rfl⟩ := List.mem_map.mp member
    exact List.mem_range.mpr (live_index_bound heap partition region live)
  simpa [liveBefore] using distinct.length_le_of_subset subset


end Compilatrix.Rt.Rc.Procs.Readback
