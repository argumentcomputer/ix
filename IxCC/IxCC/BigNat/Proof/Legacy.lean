import IxCC.BigNat.Proof.Entry
import IxCC.BigNat.Proof.NatEntry

/-! # The `SlowNat` entries are wrappers of the entries over `Nat` (`IxCC.BigNat.Proof.Legacy`)

**To be deleted with `IxCC.BigNat.Entry`.** The entries over `SlowNat` remain only because the
frozen `--bignat` side path compiles them and its native glue (`IxCC.Rt.BigNat`) is written
against their shape. Their definitions are not changed here, so that path compiles what it
compiled before.

This module records that the interface they form adds nothing to the entries over `Nat`
(`IxCC.BigNat.NatEntry`): every `SlowNat` entry is, as a function, the `Nat` entry between the
two canonical conversions `SlowNat.val` and `SlowNat.ofNat`.

* `toLimbs_eq_natToLimbs`, `fromLimbs_eq_ofNat_ofLimbs`: the two conversions the `SlowNat`
  entries are written over are the representation primitives of `IxCC.Nat.Rep`.
* `add_eq_natEntry`, ...: `Entry.add a b = SlowNat.ofNat (NatEntry.add a.val b.val)`, and so on.
  The comparisons need their operands canonical, as their own specifications do.
* `pow?`, `shiftLeft?`: where they answer, they answer the `Nat` entry; they decline exactly
  when the exponent or the count is at least `2^63` (`pow?_spec`, `shiftLeft?_spec`), a
  restriction the entries over `Nat` do not have.
* `shiftRightSlow`, `log2Slow`: under the limb-count bound their own specifications carry.

Only the root module and the fence file import it; no proof depends on it.
-/

set_option autoImplicit false

namespace IxCC.BigNat.Entry

open IxCC.BigNat

/-! ## The conversions -/

/-- A canonical `SlowNat` is the canonical image of its value. -/
theorem ofNat_val {a : SlowNat} (ha : a.Canonical) : SlowNat.ofNat a.val = a :=
  val_inj (canonical_ofNat _) ha (val_ofNat _)

/-- A canonical `SlowNat` is determined by the natural it denotes. -/
theorem eq_ofNat_of_val {r : SlowNat} {n : Nat} (hr : r.Canonical) (hv : r.val = n) :
    r = SlowNat.ofNat n :=
  val_inj hr (canonical_ofNat n) (hv.trans (val_ofNat n).symm)

/-- The limb view of a canonical `SlowNat` is `toLimbs` of its value. -/
theorem toLimbs_eq_natToLimbs {a : SlowNat} (ha : a.Canonical) :
    toLimbs a = IxCC.NatRep.toLimbs a.val := by
  have h := NatEntry.toLimbs_toNat (wf_toLimbs ha)
  rw [toNat_toLimbs] at h
  exact h.symm

/-- The demotion `fromLimbs` is `ofLimbs` followed by the canonical embedding. -/
theorem fromLimbs_eq_ofNat_ofLimbs (ls : Array UInt64) :
    fromLimbs ls = SlowNat.ofNat (IxCC.NatRep.ofLimbs ls) :=
  eq_ofNat_of_val (canonical_fromLimbs ls)
    ((val_fromLimbs ls).trans (NatEntry.ofLimbs_eq_toNat ls).symm)

/-! ## Arithmetic -/

theorem add_eq_natEntry (a b : SlowNat) :
    add a b = SlowNat.ofNat (NatEntry.add a.val b.val) :=
  eq_ofNat_of_val (canonical_add a b) ((val_add a b).trans (NatEntry.add_eq _ _).symm)

theorem sub_eq_natEntry (a b : SlowNat) :
    sub a b = SlowNat.ofNat (NatEntry.sub a.val b.val) :=
  eq_ofNat_of_val (canonical_sub a b) ((val_sub a b).trans (NatEntry.sub_eq _ _).symm)

theorem pred_eq_natEntry (a : SlowNat) : pred a = SlowNat.ofNat (NatEntry.pred a.val) :=
  eq_ofNat_of_val (canonical_pred a) ((val_pred a).trans (NatEntry.pred_eq _).symm)

theorem mul_eq_natEntry (a b : SlowNat) :
    mul a b = SlowNat.ofNat (NatEntry.mul a.val b.val) :=
  eq_ofNat_of_val (canonical_mul a b) ((val_mul a b).trans (NatEntry.mul_eq _ _).symm)

theorem div_eq_natEntry (a b : SlowNat) :
    div a b = SlowNat.ofNat (NatEntry.div a.val b.val) :=
  eq_ofNat_of_val (canonical_div a b) ((val_div a b).trans (NatEntry.div_eq _ _).symm)

theorem mod_eq_natEntry (a b : SlowNat) :
    mod a b = SlowNat.ofNat (NatEntry.mod a.val b.val) :=
  eq_ofNat_of_val (canonical_mod a b) ((val_mod a b).trans (NatEntry.mod_eq _ _).symm)

theorem divMod_eq_natEntry (a b : SlowNat) :
    divMod a b =
      (SlowNat.ofNat (NatEntry.div a.val b.val), SlowNat.ofNat (NatEntry.mod a.val b.val)) :=
  Prod.ext
    (eq_ofNat_of_val (canonical_divMod a b).1
      ((divMod_spec a b).1.trans (NatEntry.div_eq _ _).symm))
    (eq_ofNat_of_val (canonical_divMod a b).2
      ((divMod_spec a b).2.trans (NatEntry.mod_eq _ _).symm))

theorem gcd_eq_natEntry (a b : SlowNat) :
    gcd a b = SlowNat.ofNat (NatEntry.gcd a.val b.val) :=
  eq_ofNat_of_val (canonical_gcd a b) ((val_gcd a b).trans (NatEntry.gcd_eq _ _).symm)

theorem pow_eq_natEntry (base : SlowNat) (exp : Nat) :
    pow base exp = SlowNat.ofNat (NatEntry.pow base.val exp) :=
  eq_ofNat_of_val (canonical_pow base exp) ((val_pow base exp).trans (NatEntry.pow_eq _ _).symm)

/-- Where `pow?` answers, it answers the entry over `Nat`. -/
theorem pow?_eq_natEntry {base exp r : SlowNat} (h : pow? base exp = some r) :
    r = SlowNat.ofNat (NatEntry.pow base.val exp.val) := by
  have hs := pow?_spec base exp
  rw [h] at hs
  exact eq_ofNat_of_val hs.1 (hs.2.trans (NatEntry.pow_eq _ _).symm)

/-! ## Comparisons -/

theorem cmp_eq_natEntry {a b : SlowNat} (ha : a.Canonical) (hb : b.Canonical) :
    cmp a b = NatEntry.cmp a.val b.val :=
  (cmp_spec ha hb).trans (NatEntry.cmp_eq _ _).symm

theorem beq_eq_natEntry {a b : SlowNat} (ha : a.Canonical) (hb : b.Canonical) :
    beq a b = NatEntry.beq a.val b.val :=
  (beq_spec ha hb).trans (NatEntry.beq_eq _ _).symm

theorem ble_eq_natEntry {a b : SlowNat} (ha : a.Canonical) (hb : b.Canonical) :
    ble a b = NatEntry.ble a.val b.val :=
  (ble_spec ha hb).trans (NatEntry.ble_eq _ _).symm

theorem blt_eq_natEntry {a b : SlowNat} (ha : a.Canonical) (hb : b.Canonical) :
    blt a b = NatEntry.blt a.val b.val :=
  (blt_spec ha hb).trans (NatEntry.blt_eq _ _).symm

/-! ## Bitwise operations and shifts -/

theorem land_eq_natEntry (a b : SlowNat) :
    land a b = SlowNat.ofNat (NatEntry.land a.val b.val) :=
  eq_ofNat_of_val (canonical_land a b) ((val_land a b).trans (NatEntry.land_eq _ _).symm)

theorem lor_eq_natEntry (a b : SlowNat) :
    lor a b = SlowNat.ofNat (NatEntry.lor a.val b.val) :=
  eq_ofNat_of_val (canonical_lor a b) ((val_lor a b).trans (NatEntry.lor_eq _ _).symm)

theorem xor_eq_natEntry (a b : SlowNat) :
    xor a b = SlowNat.ofNat (NatEntry.xor a.val b.val) :=
  eq_ofNat_of_val (canonical_xor a b) ((val_xor a b).trans (NatEntry.xor_eq _ _).symm)

theorem shiftLeft_eq_natEntry (a : SlowNat) (s : Nat) :
    shiftLeft a s = SlowNat.ofNat (NatEntry.shiftLeft a.val s) :=
  eq_ofNat_of_val (canonical_shiftLeft a s)
    ((val_shiftLeft a s).trans (NatEntry.shiftLeft_eq _ _).symm)

/-- Where `shiftLeft?` answers, it answers the entry over `Nat`. -/
theorem shiftLeft?_eq_natEntry {a s r : SlowNat} (h : shiftLeft? a s = some r) :
    r = SlowNat.ofNat (NatEntry.shiftLeft a.val s.val) := by
  have hs := shiftLeft?_spec a s
  rw [h] at hs
  exact eq_ofNat_of_val hs.1 (hs.2.trans (NatEntry.shiftLeft_eq_mul _ _).symm)

theorem shiftRight_eq_natEntry (a : SlowNat) (s : Nat) :
    shiftRight a s = SlowNat.ofNat (NatEntry.shiftRight a.val s) :=
  eq_ofNat_of_val (canonical_shiftRight a s)
    ((val_shiftRight a s).trans (NatEntry.shiftRight_eq _ _).symm)

theorem shiftRightSlow_eq_natEntry (a s : SlowNat) (hbound : a.limbCount < 2 ^ 57) :
    shiftRightSlow a s = SlowNat.ofNat (NatEntry.shiftRight a.val s.val) :=
  eq_ofNat_of_val (canonical_shiftRightSlow a s)
    ((val_shiftRightSlow a s hbound).trans (NatEntry.shiftRight_eq_div _ _).symm)

theorem log2_eq_natEntry (a : SlowNat) : log2 a = NatEntry.log2 a.val :=
  (log2_spec a).trans (NatEntry.log2_eq _).symm

theorem log2Slow_eq_natEntry (a : SlowNat) (hbound : a.limbCount < 2 ^ 57) :
    log2Slow a = SlowNat.ofNat (NatEntry.log2 a.val) :=
  eq_ofNat_of_val (canonical_log2Slow a)
    ((val_log2Slow a hbound).trans (NatEntry.log2_eq _).symm)

/-! ## Decimal conversion -/

theorem toDecimal_eq_natEntry {a : SlowNat} (ha : a.Canonical) :
    toDecimal a = NatEntry.toDecimal a.val :=
  congrArg IxCC.BigNat.toDecimal (toLimbs_eq_natToLimbs ha)

theorem ofDecimal_eq_natEntry (s : String) :
    ofDecimal s = (NatEntry.ofDecimal s).map SlowNat.ofNat := by
  unfold ofDecimal NatEntry.ofDecimal
  cases IxCC.BigNat.ofDecimal s with
  | none => rfl
  | some ls => exact congrArg some (fromLimbs_eq_ofNat_ofLimbs ls)

end IxCC.BigNat.Entry
