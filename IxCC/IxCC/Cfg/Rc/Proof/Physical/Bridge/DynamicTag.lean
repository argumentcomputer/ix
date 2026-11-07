import IxCC.Rt.Rc.Proof.LiveHeader

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Rc IxCC.Rt.Rc.Procs
open IxCC.Lir (Word)

/-- The upper half of the actual low header read is exactly the tag read.
Only the four low-header bytes occur in this identity. -/
theorem read16_of_read32 (mem : X86.Memory) (address : Word) :
    mem.read .w16 (address + 2) = mem.read .w32 address >>> 16 := by
  simp only [X86.Memory.read, X86.Width.bytes, X86.Memory.readLittle]
  simp only [Nat.mul_zero, Nat.mul_one,
    show UInt64.ofNat 0 = 0 from rfl, show UInt64.ofNat 1 = 1 from rfl,
    show UInt64.ofNat 2 = 2 from rfl, show UInt64.ofNat 3 = 3 from rfl,
    show UInt64.ofNat 8 = 8 from rfl, show UInt64.ofNat 16 = 16 from rfl,
    show UInt64.ofNat 24 = 24 from rfl, UInt64.add_zero, UInt64.add_assoc,
    show (2 + 1 : UInt64) = 3 from rfl]
  generalize mem.bytes address = b0
  generalize mem.bytes (address + 1) = b1
  generalize mem.bytes (address + 2) = b2
  generalize mem.bytes (address + 3) = b3
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j bound
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨ j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 ∨ j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨ j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 ∨ j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨ j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 58 ∨ j = 59 ∨ j = 60 ∨ j = 61 ∨ j = 62 ∨ j = 63 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
      UInt8.toBitVec_toUInt64, UInt64.toBitVec_ofNat, BitVec.shiftLeft_eq',
      BitVec.ushiftRight_eq', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge]

theorem live_tag_read {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (cell : LiveCell addresses mem address refs body) :
    mem.read? .w16 (address + 2) = .ok (UInt64.ofNat body.ctor.tag) := by
  have permission : ∀ i < X86.Width.w16.bytes,
      mem.readable (address + 2 + UInt64.ofNat i) = true := by
    intro i bound
    have bound' : i < 2 := bound
    have offset : address + 2 + UInt64.ofNat i = address + UInt64.ofNat (2+i) := by
      rw [UInt64.ofNat_add, ← UInt64.add_assoc]
      rfl
    rw [offset]
    exact cell.readable (2+i) (by simp [cellBytes]; omega)
  rw [read?_ok permission, read16_of_read32, cell.header]
  congr 1
  apply UInt64.toNat_inj.mp
  have fields := cell.fields_small
  have tag := cell.tag
  unfold maxTag at tag
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    Nat.shiftRight_eq_div_pow, headerLow, smallClass]
  change (body.fields.length + 256 * (body.fields.length+1) + 65536 * body.ctor.tag) %
    2^64 / 65536 = body.ctor.tag % 2^64
  have headerBound : body.fields.length + 256 * (body.fields.length+1) +
      65536 * body.ctor.tag < 2^64 := by omega
  have tagBound : body.ctor.tag < 2^64 := by omega
  rw [Nat.mod_eq_of_lt headerBound, Nat.mod_eq_of_lt tagBound]
  omega

theorem live_pointer_even {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (cell : LiveCell addresses mem address refs body) : address &&& 1 = 0 := by
  apply UInt64.toNat_inj.mp
  have even : address.toNat % 2 = 0 := by have := cell.aligned; omega
  simpa [UInt64.toNat_and, Nat.and_one_is_mod] using even




end IxCC.Cfg.Rc.Proof.Physical.Bridge
