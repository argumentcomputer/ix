import IxCC.Cfg.Rc.Proof.Physical.PublicationFrames
import IxCC.Rt.Rc.Proof.ProtectedMetadata

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Proof IxCC.Rt.Rc.Procs

theorem publication_protected {heap : Own.Heap} {addresses : AddressMap}
    {original : X86.Memory} {external : Nat → Nat} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses original external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) {fields : Nat}
    (sizeClass : chosen.cls = smallClass fields) (words : Nat → Word)
    (indices : List Nat) (bounded : ∀ i ∈ indices, i < fields) (mem : X86.Memory) :
    ProtectedFrame mem (publishFields mem chosen.address words indices) context base bump := by
  induction indices generalizing mem with
  | nil => exact ProtectedFrame.refl _ _ _ _
  | cons i indices ih =>
    have first := idle.object_store_frame member mem (8 * (i + 1)) .w64 (words i) (by
      have hi := bounded i (by simp)
      simp only [sizeClass, smallClass, X86.Width.bytes]
      omega)
    exact first.trans (ih (fun j hj => bounded j (by simp [hj])) _)

/-- Concrete payload stores preserve an actual control word before the arena.
In particular this applies to the allocator's bump and limit words, with
their negative context offsets justified without modular wraparound. -/
theorem publication_control_word {heap : Own.Heap} {addresses : AddressMap}
    {mem : X86.Memory} {external : Nat → Nat} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) {fields : Nat}
    (sizeClass : chosen.cls = smallClass fields) (words : Nat → Word)
    {address value : Word} (represented : WordAt mem address value)
    (before : address.toNat + 8 ≤ base.toNat) :
    WordAt (publishFields mem chosen.address words (List.range fields)) address value := by
  have bounds := idle.partition.bounds
  have chosenBounds := idle.partition.valid chosen member
  have fit : chosen.address.toNat + 8 * (fields + 1) < 2^63 := by
    simp only [sizeClass, smallClass] at chosenBounds
    omega
  have frame := publishFields_objectFrame (List.range fields) chosen.address words
    (by omega : address.toNat + 8 ≤ 2^64)
    (fun i hi => fieldAddress_fit fit (List.mem_range.mp hi)) (fun i hi => by
      left
      rw [fieldAddress_nat fit (List.mem_range.mp hi)]
      omega) mem
  have old : WordAt mem (address + UInt64.ofNat 0) value := by simpa using represented
  simpa using frame.word (offset := 0) (by decide) old

theorem publication_context_word {heap : Own.Heap} {addresses : AddressMap}
    {mem : X86.Memory} {external : Nat → Nat} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (idle : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) {fields : Nat}
    (sizeClass : chosen.cls = smallClass fields) (words : Nat → Word)
    (offset : Nat) {value : Word}
    (represented : WordAt mem (context - UInt64.ofNat offset) value)
    (lower : 8 ≤ offset) (upper : offset ≤ context.toNat)
    (contextBefore : context.toNat ≤ base.toNat) :
    WordAt (publishFields mem chosen.address words (List.range fields))
      (context - UInt64.ofNat offset) value := by
  apply publication_control_word idle member sizeClass words represented
  have fit := idle.context_fit
  have offsetNat : (UInt64.ofNat offset).toNat = offset := toNat_ofNat_lt (by omega)
  rw [sub_toNat_of_le (by rw [offsetNat]; exact upper), offsetNat]
  omega




end IxCC.Cfg.Rc.Native
