import IxCC.Cfg.Rc.Proof.Physical.Reserved
import IxCC.Rt.Rc.Proof.CountPreserve

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Proof IxCC.Rt.Rc.Procs

theorem wordAt_read32_low {mem : X86.Memory} {address word : Word}
    (represented : WordAt mem address word) :
    mem.read .w32 address = X86.Width.w32.truncate word := by
  change mem.readLittle address 4 = _
  simp (discharger := omega) only [X86.Memory.readLittle, represented.bytes]
  simpa using pack32 word

theorem wordAt_read32_high_zero {mem : X86.Memory} {address word : Word}
    (represented : WordAt mem address word) (small : word.toNat < 2^32) :
    mem.read .w32 (address + 4) = 0 := by
  have bytes : ∀ j < 4, mem.bytes ((address+4)+UInt64.ofNat j) = 0 := by
    intro j hj
    rw [cell_offset4, represented.bytes (4+j) (by omega)]
    apply UInt8.toNat_inj.mp
    rw [byte_of_shift _ _ (by omega)]
    change word.toNat / 2^(8*(4+j)) % 256 = 0
    have options : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases options with rfl | rfl | rfl | rfl <;> omega
  simp only [X86.Memory.read, X86.Width.bytes, X86.Memory.readLittle]
  simp (discharger := omega) only [bytes]
  rfl

/-- A unique dynamic allocator header is entirely below 2^32; its physical
count is zero. This bridges the existing 64-bit allocator store to the runtime's
separate concrete low-header/count read interface. -/
theorem unique_header_reads {mem : X86.Memory} {address : Word} {fields tag : Nat}
    (small : fields < 32) (tagBound : tag ≤ maxTag)
    (represented : WordAt mem address (dynamicHeader fields (smallClass fields) tag 1)) :
    mem.read .w32 address = UInt64.ofNat (headerLow fields (smallClass fields) tag) ∧
      mem.read .w32 (address+4) = 0 := by
  have headerEq : dynamicHeader fields (smallClass fields) tag 1 =
      UInt64.ofNat (headerLow fields (smallClass fields) tag) := by
    simp [dynamicHeader, header]
  rw [headerEq] at represented
  have bound : headerLow fields (smallClass fields) tag < 2^32 := by
    simp only [headerLow, smallClass, maxTag] at *
    omega
  have wordBound : (UInt64.ofNat (headerLow fields (smallClass fields) tag)).toNat < 2^32 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    exact bound
  exact ⟨(wordAt_read32_low represented).trans (truncate32_small wordBound),
    wordAt_read32_high_zero represented wordBound⟩


end IxCC.Cfg.Rc.Native
