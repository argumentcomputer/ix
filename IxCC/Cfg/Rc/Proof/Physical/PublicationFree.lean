import IxCC.Cfg.Rc.Proof.Physical.PublicationFrames

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Proof IxCC.Rt.Rc.Procs

theorem freeChain_words {before after : X86.Memory} {chain : List Word}
    (free : FreeChain before chain)
    (frame : ∀ address ∈ chain, ∀ word, WordAt before address word → WordAt after address word) :
    FreeChain after chain := by
  induction chain with
  | nil => trivial
  | cons address tail ih =>
    exact ⟨frame address (by simp) _ free.1,
      ih free.2 (fun a ha word hw => frame a (by simp [ha]) word hw)⟩

theorem publication_free_chains {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (reserved : chosen.kind = .reserved)
    {fields : Nat} (sizeClass : chosen.cls = smallClass fields) (words : Nat → Word) (cls : Nat) :
    FreeChain (publishFields mem chosen.address words (List.range fields)) (lists cls) := by
  apply freeChain_words (idle.free_chains cls)
  intro address present word represented
  obtain ⟨slot, slotMember, addressEq, _, freeKind⟩ := idle.free_placed cls address present
  subst address
  have different : slot.address ≠ chosen.address := by
    intro same
    have equal := partition_address_unique idle.partition slotMember member same
    subst slot
    rw [reserved] at freeKind
    cases freeKind
  have frame := publication_slot_frame idle.partition member slotMember different sizeClass words mem
  have positive := (idle.partition.valid slot slotMember).1
  have oldWord : WordAt mem (slot.address + UInt64.ofNat 0) word := by simpa using represented
  simpa using frame.word (offset := 0) (by omega) oldWord

theorem publication_head_frame {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) {fields : Nat}
    (sizeClass : chosen.cls = smallClass fields) (words : Nat → Word)
    {cls : Nat} (lower : 1 ≤ cls) (upper : cls ≤ 32) :
    ObjectFrame mem (publishFields mem chosen.address words (List.range fields))
      (freeHeadAddress context (UInt64.ofNat cls)) 8 := by
  have chosenBounds := idle.partition.valid chosen member
  have arena := idle.partition.bounds
  have fieldFit : chosen.address.toNat + 8 * (fields + 1) < 2^63 := by
    simp only [sizeClass, smallClass] at chosenBounds
    omega
  have separate := idle.head_disjoint cls lower upper chosen member
  apply publishFields_objectFrame (List.range fields) chosen.address words
    (idle.head_fit cls lower upper)
    (fun i hi => fieldAddress_fit fieldFit (List.mem_range.mp hi)) (fun i hi => ?_) mem
  rw [fieldAddress_nat fieldFit (List.mem_range.mp hi)]
  simp only [sizeClass, smallClass] at separate
  have bound := List.mem_range.mp hi
  rcases separate with left | right
  · left; omega
  · right; omega

theorem publication_free_heads {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) {fields : Nat}
    (sizeClass : chosen.cls = smallClass fields) (words : Nat → Word)
    {cls : Nat} (lower : 1 ≤ cls) (upper : cls ≤ 32) :
    WordAt (publishFields mem chosen.address words (List.range fields))
      (freeHeadAddress context (UInt64.ofNat cls)) ((lists cls).headD 0) := by
  have frame := publication_head_frame idle member sizeClass words lower upper
  have oldWord : WordAt mem
      (freeHeadAddress context (UInt64.ofNat cls) + UInt64.ofNat 0) ((lists cls).headD 0) := by
    simpa using idle.free_heads cls lower upper
  simpa using frame.word (offset := 0) (by decide) oldWord



end IxCC.Cfg.Rc.Native
