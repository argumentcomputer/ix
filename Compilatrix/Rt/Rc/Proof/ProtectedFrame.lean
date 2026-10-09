import Compilatrix.Rt.Rc.Proof.ReleaseInvariant
import Compilatrix.Rt.Rc.Proof.FreeTable
import Compilatrix.Rt.Rc.Proof.Memory

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

/-- Actual byte and permission frame outside the occupied object area and
class-head table. In particular, this can protect allocator bump/limit words
without pretending they are part of the live-object representation. -/
structure ProtectedFrame (before after : X86.Memory) (context base bump : Word) : Prop where
  readable : after.readable = before.readable
  writable : after.writable = before.writable
  bytes_eq : ∀ address : Word,
    (address.toNat < base.toNat ∨ bump.toNat ≤ address.toNat) →
    (address.toNat < context.toNat+8 ∨ context.toNat+8*33 ≤ address.toNat) →
    after.bytes address = before.bytes address

theorem ProtectedFrame.refl (mem : X86.Memory) (context base bump : Word) :
    ProtectedFrame mem mem context base bump := ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem ProtectedFrame.trans {first middle last : X86.Memory} {context base bump : Word}
    (h : ProtectedFrame first middle context base bump)
    (h' : ProtectedFrame middle last context base bump) :
    ProtectedFrame first last context base bump :=
  ⟨h'.readable.trans h.readable, h'.writable.trans h.writable,
    fun a ho hh => (h'.bytes_eq a ho hh).trans (h.bytes_eq a ho hh)⟩

theorem protected_write (mem : X86.Memory) (context base bump store value : Word) (width : X86.Width)
    (hfit : store.toNat+width.bytes ≤ 2^64)
    (hregion : (base.toNat ≤ store.toNat ∧ store.toNat+width.bytes ≤ bump.toNat) ∨
      (context.toNat+8 ≤ store.toNat ∧ store.toNat+width.bytes ≤ context.toNat+8*33)) :
    ProtectedFrame mem (mem.write width store value) context base bump where
  readable := by simp [X86.Memory.write]
  writable := by simp [X86.Memory.write]
  bytes_eq address ho hh := by
    apply writeLittle_bytes_out (by cases width <;> decide) hfit
    rcases hregion with hr | hr <;> rcases ho with ho | ho <;> rcases hh with hh | hh <;> omega

theorem ReleaseInvariant.object_store_frame
    {heap addresses original external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses original external current frames context base bump limit slots lists)
    {slot : Slot} (hm : slot ∈ slots) (mem : X86.Memory) (offset : Nat)
    (width : X86.Width) (value : Word) (hsize : offset+width.bytes ≤ 8*slot.cls) :
    ProtectedFrame mem (mem.write width (slot.address+UInt64.ofNat offset) value) context base bump := by
  have hv := h.partition.valid slot hm
  have hb := h.partition.bounds
  have hw : 0 < width.bytes := by cases width <;> decide
  have ha : (slot.address+UInt64.ofNat offset).toNat = slot.address.toNat+offset := addr_toNat (by omega)
  apply protected_write
  · rw [ha]; omega
  · left; rw [ha]; constructor <;> omega

theorem ReleaseInvariant.head_store_frame
    {heap addresses original external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses original external current frames context base bump limit slots lists)
    (mem : X86.Memory) {cls : Nat} (hl : 1 ≤ cls) (hu : cls ≤ 32) (value : Word) :
    ProtectedFrame mem (mem.write .w64 (freeHeadAddress context (UInt64.ofNat cls)) value) context base bump := by
  apply protected_write
  · exact h.head_fit cls hl hu
  · right
    rw [freeHead_toNat h.context_fit hu]
    simp only [X86.Width.bytes]
    constructor <;> omega

/-- Preserve any concrete protected word, including allocator metadata when
its eight byte addresses lie outside both write regions. -/
theorem ProtectedFrame.word {before after : X86.Memory} {context base bump address value : Word}
    (h : ProtectedFrame before after context base bump) (hw : WordAt before address value)
    (ho : ∀ j < 8, (address+UInt64.ofNat j).toNat < base.toNat ∨ bump.toNat ≤ (address+UInt64.ofNat j).toNat)
    (hh : ∀ j < 8, (address+UInt64.ofNat j).toNat < context.toNat+8 ∨
      context.toNat+8*33 ≤ (address+UInt64.ofNat j).toNat) :
    WordAt after address value where
  bytes j hj := (h.bytes_eq _ (ho j hj) (hh j hj)).trans (hw.bytes j hj)
  readable j hj := by rw [h.readable]; exact hw.readable j hj





end Compilatrix.Rt.Rc.Procs
