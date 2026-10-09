import Compilatrix.Rt.Rc.Proof.LiveMemory

/-! Byte-level frames for every unrelated live or pending object. These
follow from concrete store disjointness and do not assume a simulation. -/
namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

structure ObjectFrame (before after : X86.Memory) (address : Word) (bytes : Nat) : Prop where
  readable : after.readable = before.readable
  writable : after.writable = before.writable
  bytes_eq : ∀ j < bytes,
    after.bytes (address+UInt64.ofNat j) = before.bytes (address+UInt64.ofNat j)

theorem ObjectFrame.trans {a b c : X86.Memory} {address : Word} {bytes : Nat}
    (hab : ObjectFrame a b address bytes) (hbc : ObjectFrame b c address bytes) :
    ObjectFrame a c address bytes where
  readable := hbc.readable.trans hab.readable
  writable := hbc.writable.trans hab.writable
  bytes_eq j hj := (hbc.bytes_eq j hj).trans (hab.bytes_eq j hj)

theorem objectFrame_write (mem : X86.Memory) (address store value : Word)
    (bytes : Nat) (width : X86.Width)
    (ha : address.toNat+bytes ≤ 2^64) (hs : store.toNat+width.bytes ≤ 2^64)
    (hsep : address.toNat+bytes ≤ store.toNat ∨ store.toNat+width.bytes ≤ address.toNat) :
    ObjectFrame mem (mem.write width store value) address bytes where
  readable := by simp [X86.Memory.write]
  writable := by simp [X86.Memory.write]
  bytes_eq j hj := by
    have haj : (address+UInt64.ofNat j).toNat = address.toNat+j := addr_toNat (by omega)
    have hw : width.bytes ≤ 8 := by cases width <;> simp [X86.Width.bytes]
    exact writeLittle_bytes_out hw hs (by rw [haj]; rcases hsep with h | h <;> omega)

theorem ObjectFrame.word {before after : X86.Memory} {address : Word} {bytes offset : Nat}
    (h : ObjectFrame before after address bytes) (hoff : offset+8 ≤ bytes)
    {value : Word} (hv : WordAt before (address+UInt64.ofNat offset) value) :
    WordAt after (address+UInt64.ofNat offset) value where
  bytes j hj := by
    have he : (address+UInt64.ofNat offset)+UInt64.ofNat j = address+UInt64.ofNat (offset+j) := by
      rw [UInt64.ofNat_add]; simp [UInt64.add_assoc]
    rw [he, h.bytes_eq (offset+j) (by omega)]
    simpa only [he] using hv.bytes j hj
  readable j hj := by rw [h.readable]; exact hv.readable j hj

theorem LiveCell.frame {addresses before after address refs body}
    (h : LiveCell addresses before address refs body)
    (hf : ObjectFrame before after address (cellBytes body.fields.length)) :
    LiveCell addresses after address refs body := by
  refine { h with readable := ?_, writable := ?_, header := ?_, count := ?_, fields := ?_ }
  · intro j hj; rw [hf.readable]; exact h.readable j hj
  · intro j hj; rw [hf.writable]; exact h.writable j hj
  · rw [← h.header]
    apply X86.Memory.readLittle_congr
    intro j hj
    apply hf.bytes_eq
    simp only [X86.Width.bytes] at hj
    simp only [cellBytes]
    omega
  · rw [← h.count]
    apply X86.Memory.readLittle_congr
    intro j hj
    rw [cell_offset4]
    apply hf.bytes_eq
    simp only [X86.Width.bytes] at hj
    simp only [cellBytes]
    omega
  · intro j value hj
    obtain ⟨word, hv, hw⟩ := h.fields j value hj
    have hjbound := (List.getElem?_eq_some_iff.mp hj).1
    exact ⟨word, hv, hf.word (by simp only [cellBytes]; omega) hw⟩




end Compilatrix.Rt.Rc.Procs
