import Compilatrix.Rt.Rc.Proof.LiveMemory
import Compilatrix.Rt.Rc.Readback

set_option autoImplicit false
namespace Compilatrix.Rt.Rc.Procs.Readback
open Compilatrix.Lir (Word)
open Compilatrix.Rt.Proof

theorem read64_halves (mem : X86.Memory) (address : Word) :
    mem.read .w64 address =
      mem.read .w32 address ||| (mem.read .w32 (address+4)) <<< 32 := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [X86.Memory.read, X86.Width.bytes, X86.Memory.readLittle,
    UInt64.add_assoc]
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
    UInt8.toBitVec_toUInt64, UInt64.toBitVec_ofNat, BitVec.shiftLeft_eq',
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  have ranges : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨
      (24 ≤ j ∧ j < 32) ∨ (32 ≤ j ∧ j < 40) ∨
      (40 ≤ j ∧ j < 48) ∨ (48 ≤ j ∧ j < 56) ∨ 56 ≤ j := by omega
  rcases ranges with h | h | h | h | h | h | h | h <;>
    simp (config := {decide := true}) (discharger := omega)
      [hj, decide_eq_true, decide_eq_false, Nat.sub_sub]

theorem halves_word {lo hi : Word} (hlo : lo.toNat < 2^32) (hhi : hi.toNat < 2^32) :
    lo ||| hi <<< 32 = UInt64.ofNat (lo.toNat+2^32*hi.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', Nat.shiftLeft_eq]
  change lo.toNat ||| ((hi.toNat * 2^32) % 2^64) = (lo.toNat+2^32*hi.toNat) % 2^64
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.or_comm,
    Nat.mul_comm hi.toNat (2^32), ← Nat.two_pow_add_eq_or_of_lt hlo]
  omega

theorem live_header {addresses : AddressMap} {mem : X86.Memory} {address : Word}
    {refs : Nat} {body : Own.Body} (h : LiveCell addresses mem address refs body) :
    mem.read64? address = .ok (dynamicHeader body.fields.length
      (smallClass body.fields.length) body.ctor.tag refs) := by
  have hn := h.fields_small
  have ht := h.tag
  have hc := h.bounded
  unfold maxTag at ht
  unfold maxCount at hc
  have hlo : headerLow body.fields.length (smallClass body.fields.length) body.ctor.tag < 2^32 := by
    unfold headerLow smallClass
    omega
  have hhi : refs-1 < 2^32 := by omega
  have loNat : (UInt64.ofNat (headerLow body.fields.length
      (smallClass body.fields.length) body.ctor.tag)).toNat =
      headerLow body.fields.length (smallClass body.fields.length) body.ctor.tag := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hiNat : (UInt64.ofNat (refs-1)).toNat = refs-1 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  change mem.read? .w64 address = _
  rw [read?_ok (fun j hj => h.readable j (by
    change j < 8 at hj; unfold cellBytes; omega)), read64_halves, h.header, h.count]
  rw [halves_word (by rw [loNat]; exact hlo) (by rw [hiNat]; exact hhi), loNat, hiNat]
  rfl



end Compilatrix.Rt.Rc.Procs.Readback
