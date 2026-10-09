import Compilatrix.Rt.Proof.Mem

/-! Memory effect of the actual narrow count store used by inc/shared-dec.
This frame property does not yet supply full Lir execution or heap Balance. -/
namespace Compilatrix.Rt.Rc.Procs
open Compilatrix.Lir
open Compilatrix.Rt.Proof

def storeCount (m : X86.Memory) (address count : Word) : X86.Memory :=
  m.write .w32 (address + 4) count

/-- Only bytes 4..7 of the designated cell may differ; permissions are exact.
In particular scan/class/tag and all payload bytes are framed. -/
structure CountFrame (before after : X86.Memory) (address : Word) : Prop where
  readable : after.readable = before.readable
  writable : after.writable = before.writable
  outside : ∀ b, b.toNat < address.toNat + 4 ∨ address.toNat + 8 ≤ b.toNat →
    after.bytes b = before.bytes b

theorem countAddress {address : Word} (hfit : address.toNat + 8 ≤ 2^64) :
    (address + 4).toNat = address.toNat + 4 := by
  rw [UInt64.toNat_add]
  simp
  omega

theorem storeCount_frame (m : X86.Memory) (address count : Word)
    (hfit : address.toNat + 8 ≤ 2^64) : CountFrame m (storeCount m address count) address where
  readable := by simp [storeCount, X86.Memory.write]
  writable := by simp [storeCount, X86.Memory.write]
  outside b hb := by
    unfold storeCount X86.Memory.write
    apply writeLittle_bytes_out (by decide)
    · rw [countAddress hfit]; simp [X86.Width.bytes]; omega
    · rw [countAddress hfit]; simp only [X86.Width.bytes]; omega

/-- Every full payload or disjoint object's word retains its exact value. -/
theorem storeCount_word {m : X86.Memory} {address count b value : Word}
    (hword : WordAt m b value) (hfit : address.toNat + 8 ≤ 2^64)
    (hb : b.toNat + 8 ≤ 2^64)
    (hdisjoint : b.toNat + 8 ≤ address.toNat + 4 ∨ address.toNat + 8 ≤ b.toNat) :
    WordAt (storeCount m address count) b value := by
  apply hword.write_disjoint
  · rw [countAddress hfit]; simp [X86.Width.bytes]; omega
  · exact hb
  · rw [countAddress hfit]; simpa [X86.Width.bytes] using hdisjoint

/-- The four stored bytes implement the requested physical count, independent
of all original bytes. Bound on count is supplied by increment/decrement's
arithmetic proof; this byte statement holds even before that bound. -/
theorem storeCount_bytes (m : X86.Memory) (address count : Word) {i : Nat}
    (hi : i < 4) :
    (storeCount m address count).bytes ((address + 4) + UInt64.ofNat i) =
      (count >>> UInt64.ofNat (8*i)).toUInt8 := by
  exact X86.Memory.writeLittle_bytes m (address + 4) count (by decide) hi

end Compilatrix.Rt.Rc.Procs
