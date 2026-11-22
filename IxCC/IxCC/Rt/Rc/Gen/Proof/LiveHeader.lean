import IxCC.Rt.Rc.Gen.Proof.CursorLoads
import IxCC.Rt.Rc.Proof.LiveHeader

/-! The scan and class bytes of a live cell of any layout, as its header holds them. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir

theorem LiveCell.scan_byte {addresses mem address refs body}
    (h : LiveCell addresses mem address refs body) :
    mem.bytes address = (UInt64.ofNat body.ctor.nobj).toUInt8 := by
  rw [← read32_byte0, h.header]
  apply UInt8.toNat_inj.mp
  have hs := classOf_lt h.layout
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_ofNat', headerLow]
  omega

theorem LiveCell.class_byte {addresses mem address refs body}
    (h : LiveCell addresses mem address refs body) :
    mem.bytes (address+1) = (UInt64.ofNat (classOf body.ctor)).toUInt8 := by
  rw [← read32_byte1, h.header]
  apply UInt8.toNat_inj.mp
  have hs := classOf_lt h.layout
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    Nat.shiftRight_eq_div_pow, headerLow]
  change ((body.ctor.nobj + 256 * classOf body.ctor + 65536 * body.ctor.tag) %
    2^64 / 256) % 256 = (classOf body.ctor % 2^64) % 256
  have hheader : body.ctor.nobj + 256 * classOf body.ctor + 65536 * body.ctor.tag < 2^64 := by omega
  have hclass64 : classOf body.ctor < 2^64 := by omega
  rw [Nat.mod_eq_of_lt hheader, Nat.mod_eq_of_lt hclass64, Nat.mod_eq_of_lt hs.1]
  have hdiv : (body.ctor.nobj + 256 * classOf body.ctor + 65536 * body.ctor.tag) / 256 =
      classOf body.ctor + 256*body.ctor.tag := by omega
  rw [hdiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs.1]

theorem LiveCell.scan_load {addresses mem address refs body}
    (h : LiveCell addresses mem address refs body) :
    loadWord mem .w8 .zero address = some (UInt64.ofNat body.ctor.nobj) := by
  apply byte_load_nat (classOf_lt h.layout).2.1 _ h.scan_byte
  have hr := h.readable 0 (by have := h.bytes; omega)
  simpa using hr

theorem LiveCell.class_load {addresses mem address refs body}
    (h : LiveCell addresses mem address refs body) :
    loadWord mem .w8 .zero (address+1) = some (UInt64.ofNat (classOf body.ctor)) := by
  apply byte_load_nat (classOf_lt h.layout).1 _ h.class_byte
  have hr := h.readable 1 (by have := h.bytes; omega)
  simpa using hr

end IxCC.Rt.Rc.Gen
