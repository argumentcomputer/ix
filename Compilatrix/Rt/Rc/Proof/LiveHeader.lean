import Compilatrix.Rt.Rc.Proof.CursorLoads

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

theorem read32_byte0 (mem : X86.Memory) (address : Word) :
    (mem.read .w32 address).toUInt8 = mem.bytes address := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [X86.Memory.read, X86.Width.bytes, X86.Memory.readLittle]
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
    UInt8.toBitVec_toUInt64, UInt64.toBitVec_ofNat, BitVec.shiftLeft_eq',
    BitVec.toNat_ofNat, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h16 : j < 16 := by omega
  have h24 : j < 24 := by omega
  have h64 : j < 64 := by omega
  simp [hj, h16, h24, h64]

theorem read32_byte1 (mem : X86.Memory) (address : Word) :
    ((mem.read .w32 address) >>> 8).toUInt8 = mem.bytes (address+1) := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [X86.Memory.read, X86.Width.bytes, X86.Memory.readLittle]
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64, UInt64.toBitVec_ofNat,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  have h8 : ¬8+j < 8 := by omega
  have h16 : 8+j < 16 := by omega
  have h24 : 8+j < 24 := by omega
  have h64 : 8+j < 64 := by omega
  have hj64 : j < 64 := by omega
  simp [hj, h8, h16, h24, h64, hj64]

theorem LiveCell.scan_byte {addresses mem address refs body}
    (h : LiveCell addresses mem address refs body) :
    mem.bytes address = (UInt64.ofNat body.fields.length).toUInt8 := by
  rw [← read32_byte0, h.header]
  apply UInt8.toNat_inj.mp
  have hs := h.fields_small
  have ht := h.tag
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_ofNat', headerLow, smallClass]
  unfold maxTag at ht
  omega

theorem LiveCell.class_byte {addresses mem address refs body}
    (h : LiveCell addresses mem address refs body) :
    mem.bytes (address+1) = (UInt64.ofNat (smallClass body.fields.length)).toUInt8 := by
  rw [← read32_byte1, h.header]
  apply UInt8.toNat_inj.mp
  have hs := h.fields_small
  have ht := h.tag
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    Nat.shiftRight_eq_div_pow, headerLow, smallClass]
  change ((body.fields.length + 256 * (body.fields.length+1) + 65536 * body.ctor.tag) %
    2^64 / 256) % 256 = ((body.fields.length+1) % 2^64) % 256
  unfold maxTag at ht
  have hheader : body.fields.length + 256 * (body.fields.length+1) + 65536 * body.ctor.tag < 2^64 := by omega
  have hclass64 : body.fields.length+1 < 2^64 := by omega
  have hclass256 : body.fields.length+1 < 256 := by omega
  rw [Nat.mod_eq_of_lt hheader, Nat.mod_eq_of_lt hclass64, Nat.mod_eq_of_lt hclass256]
  have hdiv : (body.fields.length + 256 * (body.fields.length+1) + 65536 * body.ctor.tag) / 256 =
      body.fields.length+1 + 256*body.ctor.tag := by omega
  rw [hdiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hclass256]

theorem LiveCell.scan_load {addresses mem address refs body}
    (h : LiveCell addresses mem address refs body) :
    loadWord mem .w8 .zero address = some (UInt64.ofNat body.fields.length) := by
  apply byte_load_nat (by have := h.fields_small; omega) _ h.scan_byte
  have hr := h.readable 0 (by simp [cellBytes]; omega)
  simpa using hr






end Compilatrix.Rt.Rc.Procs
