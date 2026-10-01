import Compilatrix.Xv.Select.Proof.Exec
import Compilatrix.Xv.Select.Lemmas

/-!
# Word facts selection relies on

Lir computes on words (`Lir.BinOp.eval`, `Lir.Cond.holds`, `Lir.loadWord`);
the rows selection emits compute on the machine's registers and flags. This
module proves the word identities that make the two agree: nested
truncations, register merges, shifts, sign extension by `xor`/`add`,
division with a zeroed high half, narrow memory reads, and conditions that
read only an operand's low bits.
-/

namespace Compilatrix.Xv.Select.Proof

open Compilatrix.Lir (VReg Word)
open Compilatrix.X86 (Width)
open Compilatrix.Xv.Validate (mergeWrite)

/-! ## Truncation -/

theorem truncate_lt (w : Width) (z : Word) : (w.truncate z).toNat < 2 ^ w.bits := by
  rw [X86.Encode.truncate_nat]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem truncate_eq_self {w : Width} {z : Word} (h : z.toNat < 2 ^ w.bits) : w.truncate z = z := by
  apply UInt64.toNat_inj.mp
  rw [X86.Encode.truncate_nat, Nat.mod_eq_of_lt h]

theorem truncate_truncate_le {w w' : Width} (h : w.bits ≤ w'.bits) (z : Word) :
    w.truncate (w'.truncate z) = w.truncate z := by
  apply UInt64.toNat_inj.mp
  rw [X86.Encode.truncate_nat, X86.Encode.truncate_nat, X86.Encode.truncate_nat]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)

theorem truncate_truncate_ge {w w' : Width} (h : w.bits ≤ w'.bits) (z : Word) :
    w'.truncate (w.truncate z) = w.truncate z :=
  truncate_eq_self (Nat.lt_of_lt_of_le (truncate_lt w z) (Nat.pow_le_pow_right (by decide) h))

/-- A register write leaves the written value in its low bits. -/
theorem truncate_mergeWrite (w : Width) (old v : Word) : w.truncate (mergeWrite w old v) = w.truncate v := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases w <;>
    simp [mergeWrite, X86.Encode.truncate_bits, Width.bits, Width.mask, X86.Encode.truncate64] <;>
    first
    | omega
    | (intro h; simp_all)
    | skip

theorem mergeWrite_wide {w : Width} (hw : w = .w32 ∨ w = .w64) (old v : Word) :
    mergeWrite w old v = w.truncate v := by
  rcases hw with rfl | rfl <;> simp [mergeWrite, X86.Encode.truncate64]


/-! ## Shifts -/

theorem shiftCount_eq (w : Width) (s : Word) : X86.shiftCount w s = (s &&& Lir.shiftMask w).toNat := by
  cases w <;> rfl

theorem masked_lt (w : Width) (s : Word) : (s &&& Lir.shiftMask w).toNat < 64 := by
  have h : (s &&& Lir.shiftMask w).toNat ≤ (Lir.shiftMask w).toNat := by
    rw [UInt64.toNat_and]; exact Nat.and_le_right
  cases w <;> simp [Lir.shiftMask] at h ⊢ <;> omega

theorem mod64_of_lt {c : Word} (h : c.toNat < 64) : (c.toBitVec % 64#64).toNat = c.toNat := by
  simp [BitVec.toNat_umod]
  omega

/-- `shl` at width `w` (the row, then the low bits) is Lir's `shl`. -/
theorem shl_eq (w : Width) (a s : Word) :
    w.truncate (shiftResult .shl w a s) = w.truncate (a <<< (s &&& Lir.shiftMask w)) := by
  rw [shiftResult, truncate_mergeWrite, shiftCount_eq]
  have hc := masked_lt w s
  generalize s &&& Lir.shiftMask w = c at hc ⊢
  have hw := X86.Encode.width_bound w
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [X86.Encode.truncate_bits, BitVec.getLsbD_setWidth, X86.ShiftOp.apply, BitVec.getLsbD_shiftLeft,
    UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', mod64_of_lt hc, Nat.mod_eq_of_lt hc]
  by_cases h₁ : i < w.bits <;> simp [h₁, hi, Nat.mod_eq_of_lt hc]
  by_cases h₂ : i < c.toNat <;> simp [h₂, Nat.mod_eq_of_lt hc]
  omega

/-- `shr` at width `w` is Lir's `shr`. -/
theorem shr_eq (w : Width) (a s : Word) :
    w.truncate (shiftResult .shr w a s) = w.truncate (w.truncate a >>> (s &&& Lir.shiftMask w)) := by
  rw [shiftResult, truncate_mergeWrite, shiftCount_eq]
  have hc := masked_lt w s
  generalize s &&& Lir.shiftMask w = c at hc ⊢
  have hw := X86.Encode.width_bound w
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [X86.Encode.truncate_bits, BitVec.getLsbD_setWidth, X86.ShiftOp.apply, BitVec.getLsbD_ushiftRight,
    UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', mod64_of_lt hc, Nat.mod_eq_of_lt hc]
  by_cases h₁ : i < w.bits <;> simp [h₁, hi, Nat.mod_eq_of_lt hc]
  by_cases h₂ : c.toNat + i < w.bits <;> simp [h₂, Nat.mod_eq_of_lt hc]
  intro _
  omega

theorem sext_bits (w : Width) (a : Word) :
    (Lir.sext w a).toBitVec = (a.toBitVec.setWidth w.bits).signExtend 64 := by
  cases w
  · simp [Lir.sext, Width.bits]
  · simp [Lir.sext, Width.bits]
  · simp [Lir.sext, Width.bits]
  · simp [Lir.sext, Width.bits, BitVec.signExtend_eq_setWidth_of_le]

/-- `sar` at width `w` is Lir's `sar`. -/
theorem sar_eq (w : Width) (a s : Word) :
    w.truncate (shiftResult .sar w a s) = Lir.sarWord w a (s &&& Lir.shiftMask w) := by
  rw [shiftResult, truncate_mergeWrite, Lir.sarWord, shiftCount_eq]
  have hc := masked_lt w s
  generalize s &&& Lir.shiftMask w = c at hc ⊢
  have hw := X86.Encode.width_bound w
  have hw8 : 8 ≤ w.bits := by cases w <;> decide
  have hsm : (c.toBitVec.smod 64#64).toNat = c.toNat := by
    rw [BitVec.toNat_smod]
    have hmsb : c.toBitVec.msb = false := by
      simp [BitVec.msb_eq_decide]; omega
    have h64 : (64#64 : BitVec 64).msb = false := by decide
    simp [hmsb, h64, BitVec.toNat_umod]
    omega
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [X86.Encode.truncate_bits, BitVec.getLsbD_setWidth, X86.ShiftOp.apply, BitVec.getLsbD_sshiftRight,
    Int64.toBitVec_toUInt64, Int64.toBitVec_shiftRight, BitVec.getLsbD_sshiftRight', hsm,
    UInt64.toBitVec_toInt64, sext_bits, BitVec.getLsbD_signExtend, BitVec.msb_signExtend]
  by_cases h₁ : i < w.bits
  · have hi64 : i < 64 := by omega
    simp [h₁, hi64, hsm, Nat.not_le.mpr h₁, Nat.not_le.mpr hi64]
    by_cases h₂ : c.toNat + i < w.bits
    · have h₃ : c.toNat + i < 64 := by omega
      simp [h₂, h₃, hsm, Nat.not_le.mpr h₁, Nat.not_le.mpr hi64]
    · by_cases h₃ : c.toNat + i < 64 <;> simp [h₂, h₃, hsm, Nat.not_le.mpr h₁, Nat.not_le.mpr hi64]
      intro h64
      cases w <;> simp [Width.bits] at h64 ⊢
      simp [BitVec.msb_eq_getMsbD_zero]
  · simp [h₁]

theorem shiftResult_wide {w : Width} (hw : w = .w32 ∨ w = .w64) (op : X86.ShiftOp) (a s : Word) :
    w.truncate (shiftResult op w a s) = shiftResult op w a s := by
  rw [shiftResult, mergeWrite_wide hw, X86.Encode.truncate_truncate]


/-! ## Sign extension by `xor` and `add` -/

theorem xor_two_pow_of_lt {n k : Nat} (h : n < 2 ^ (k + 1)) :
    n ^^^ 2 ^ k = if n < 2 ^ k then n + 2 ^ k else n - 2 ^ k := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdm := Nat.div_add_mod (n ^^^ 2 ^ k) (2 ^ k)
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow, Nat.div_self hk, Nat.mod_self, Nat.xor_zero] at hdm
  have hn := Nat.div_add_mod n (2 ^ k)
  have hlt : n / 2 ^ k < 2 := by
    rw [Nat.div_lt_iff_lt_mul hk]; rw [Nat.pow_succ] at h; omega
  have hmod := Nat.mod_lt n hk
  rcases Nat.lt_or_ge n (2 ^ k) with hn' | hn'
  · have h0 : n / 2 ^ k = 0 := Nat.div_eq_of_lt hn'
    rw [h0] at hdm hn
    simp only [Nat.zero_xor, Nat.mul_one] at hdm
    simp only [hn', ↓reduceIte]
    omega
  · have h1 : n / 2 ^ k = 1 := by
      have : 1 ≤ n / 2 ^ k := (Nat.le_div_iff_mul_le hk).2 (by omega)
      omega
    rw [h1] at hdm hn
    simp only [show (1 : Nat) ^^^ 1 = 0 from rfl, Nat.mul_zero, Nat.zero_add] at hdm
    simp only [Nat.not_lt.mpr hn', ↓reduceIte]
    omega

/-- The value of a sign extension below 64 bits. -/
theorem sext_toNat {w : Width} (hw : w ≠ .w64) (z : Word) :
    (Lir.sext w z).toNat = if 2 ^ (w.bits - 1) ≤ z.toNat % 2 ^ w.bits then
      z.toNat % 2 ^ w.bits + (2 ^ 64 - 2 ^ w.bits) else z.toNat % 2 ^ w.bits := by
  rw [← UInt64.toNat_toBitVec (Lir.sext w z), sext_bits, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, BitVec.msb_eq_decide, BitVec.toNat_setWidth]
  have hle : w.bits ≤ 64 := X86.Encode.width_bound w
  have hpow : 2 ^ w.bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hle
  have hm : z.toNat % 2 ^ w.bits < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hpow
  simp only [UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hm]
  by_cases h : 2 ^ (w.bits - 1) ≤ z.toNat % 2 ^ w.bits <;> simp [h]

theorem sext_xor_add {w : Width} (hw : w ≠ .w64) {z : Word} (hz : z.toNat < 2 ^ w.bits) :
    (z ^^^ UInt64.ofNat (2 ^ (w.bits - 1))) + (0 - UInt64.ofNat (2 ^ (w.bits - 1))) = Lir.sext w z := by
  apply UInt64.toNat_inj.mp
  rw [sext_toNat hw, Nat.mod_eq_of_lt hz]
  cases w with
  | w64 => exact absurd rfl hw
  | w8 =>
    have hx := xor_two_pow_of_lt (k := 7) (n := z.toNat) hz
    simp only [Width.bits] at hz ⊢
    simp only [UInt64.toNat_add, UInt64.toNat_xor, UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_zero]
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.add_zero] at hx ⊢
    rw [hx]
    rcases Nat.lt_or_ge z.toNat 128 with h | h <;> simp [h, Nat.not_le.mpr h, Nat.not_lt.mpr h] <;> omega
  | w16 =>
    have hx := xor_two_pow_of_lt (k := 15) (n := z.toNat) hz
    simp only [Width.bits] at hz ⊢
    simp only [UInt64.toNat_add, UInt64.toNat_xor, UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_zero]
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.add_zero] at hx ⊢
    rw [hx]
    rcases Nat.lt_or_ge z.toNat 32768 with h | h <;> simp [h, Nat.not_le.mpr h, Nat.not_lt.mpr h] <;> omega
  | w32 =>
    have hx := xor_two_pow_of_lt (k := 31) (n := z.toNat) hz
    simp only [Width.bits] at hz ⊢
    simp only [UInt64.toNat_add, UInt64.toNat_xor, UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_zero]
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.add_zero] at hx ⊢
    rw [hx]
    rcases Nat.lt_or_ge z.toNat 2147483648 with h | h <;> simp [h, Nat.not_le.mpr h, Nat.not_lt.mpr h] <;> omega


/-! ## Division with a zeroed high half -/

theorem divQuot_eq {w : Width} (hw : w = .w32 ∨ w = .w64) (a b : Word) :
    w.truncate (UInt64.ofNat (divDividend w a 0 / (w.truncate b).toNat)) = w.truncate a / w.truncate b := by
  have hz : w.truncate (0 : Word) = 0 := by simp [Width.truncate]
  simp only [divDividend, hz, UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add]
  have hq : UInt64.ofNat ((w.truncate a).toNat / (w.truncate b).toNat) = w.truncate a / w.truncate b := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_div, UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (UInt64.toNat_lt _)
  rw [hq]
  apply truncate_eq_self
  rw [UInt64.toNat_div]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (truncate_lt w a)

theorem divRem_eq {w : Width} (hw : w = .w32 ∨ w = .w64) (a b : Word) :
    w.truncate (UInt64.ofNat (divDividend w a 0 % (w.truncate b).toNat)) = w.truncate a % w.truncate b := by
  have hz : w.truncate (0 : Word) = 0 := by simp [Width.truncate]
  simp only [divDividend, hz, UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add]
  have hq : UInt64.ofNat ((w.truncate a).toNat % (w.truncate b).toNat) = w.truncate a % w.truncate b := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (UInt64.toNat_lt _)
  rw [hq]
  apply truncate_eq_self
  rw [UInt64.toNat_mod]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (truncate_lt w a)

theorem truncate_zero (w : Width) : w.truncate (0 : Word) = 0 := by simp [Width.truncate]

/-! ## Narrow memory reads -/

theorem readLittle_bit (mem : X86.Memory) (addr : Word) :
    ∀ (n i : Nat), n ≤ 8 → (mem.readLittle addr n).toBitVec.getLsbD i =
      (decide (i < 8 * n) && (mem.bytes (addr + UInt64.ofNat (i / 8))).toBitVec.getLsbD (i % 8))
  | 0, i, _ => by simp [X86.Memory.readLittle]
  | n + 1, i, h => by
      rw [X86.Memory.readLittle, UInt64.toBitVec_or, BitVec.getLsbD_or, readLittle_bit mem addr n i (by omega)]
      simp only [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, BitVec.shiftLeft_eq']
      have hn8 : ∀ y : BitVec 64, y.toNat = 8 * n → (y % 64).toNat = 8 * n := by
        intro y hy; simp [BitVec.toNat_umod, hy]; omega
      rw [hn8 _ (by simp; omega)]
      simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
      by_cases h₁ : i < 8 * n
      · have : ¬ i < 8 * (n + 1) = False := by simp; omega
        simp [h₁, show i < 8 * (n + 1) by omega]
      · by_cases h₂ : i < 8 * (n + 1)
        · have hd : i / 8 = n := by omega
          have hmod : i - 8 * n = i % 8 := by omega
          simp [h₁, h₂, hd, hmod, show i < 64 by omega, show i % 8 < 8 from Nat.mod_lt _ (by decide)]
          omega
        · simp [h₁, h₂]
          intro _ _
          exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem rangeAllowed_le (perm : Word → Bool) (addr : Word) :
    ∀ {m n : Nat}, m ≤ n → X86.Memory.rangeAllowed perm addr n = true → X86.Memory.rangeAllowed perm addr m = true
  | m, 0, hmn, h => by rw [Nat.le_zero.mp hmn]; rfl
  | m, n + 1, hmn, h => by
      simp only [X86.Memory.rangeAllowed, Bool.and_eq_true] at h
      rcases Nat.lt_or_ge m (n + 1) with hm | hm
      · exact rangeAllowed_le perm addr (by omega) h.1
      · rw [show m = n + 1 by omega]
        simp [X86.Memory.rangeAllowed, h.1, h.2]

theorem width_bytes_bits (w : Width) : w.bits = 8 * w.bytes := by cases w <;> rfl

/-- A read of fewer bytes at the same address gets the low bits. -/
theorem read_prefix {mem : X86.Memory} {w w' : Width} {addr v : Word} (h : w'.bytes ≤ w.bytes)
    (hr : mem.read? w addr = .ok v) : mem.read? w' addr = .ok (w'.truncate v) := by
  unfold X86.Memory.read? at hr ⊢
  split at hr
  · rename_i hp
    simp only [Except.ok.injEq] at hr
    subst hr
    rw [if_pos (rangeAllowed_le _ _ h hp)]
    congr 1
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hb : w.bytes ≤ 8 := by cases w <;> decide
    have hb' : w'.bytes ≤ 8 := by cases w' <;> decide
    rw [X86.Memory.read, X86.Memory.read, readLittle_bit _ _ _ _ hb', X86.Encode.truncate_bits,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, readLittle_bit _ _ _ _ hb, width_bytes_bits]
    by_cases hi' : i < 8 * w'.bytes <;> simp [hi', hi]
    omega
  · cases hr

/-- A narrow read of a Lir load's cell gets the load's low bits (zero- or
sign-extended alike). -/
theorem loadWord_read {mem : X86.Memory} {w w' : Width} {e : Lir.Ext} {addr v : Word}
    (h : Lir.loadWord mem w e addr = some v) (hw : w'.bytes ≤ w.bytes) :
    mem.read? w' addr = .ok (w'.truncate v) := by
  unfold Lir.loadWord at h
  split at h
  · rename_i raw hraw
    simp only [Option.some.injEq] at h
    subst h
    rw [read_prefix hw hraw]
    cases e
    · rfl
    · congr 1
      apply UInt64.toBitVec_inj.mp
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [X86.Encode.truncate_bits, BitVec.getLsbD_setWidth, sext_bits, BitVec.getLsbD_signExtend]
      have := width_bytes_bits w; have := width_bytes_bits w'
      by_cases h₁ : i < w'.bits <;> simp [h₁, hi]
      have : i < w.bits := by omega
      simp [this]
  · cases h


/-! ## Conditions read low bits -/

theorem truncate_and (w : Width) (a b : Word) : w.truncate (a &&& b) = w.truncate a &&& w.truncate b := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [X86.Encode.truncate_bits]

theorem holds_congr {c : Lir.Cond} {w : Width} {a a' b b' : Word} (ha : w.truncate a = w.truncate a')
    (hb : w.truncate b = w.truncate b') : c.holds w a b = c.holds w a' b' := by
  cases c <;> simp [Lir.Cond.holds, X86.Width.signedValue, ha, hb, truncate_and]

theorem holds_trunc_right (c : Lir.Cond) (w : Width) (a b : Word) : c.holds w a (w.truncate b) = c.holds w a b :=
  holds_congr rfl (X86.Encode.truncate_truncate w b)

theorem holds_trunc_left (c : Lir.Cond) (w : Width) (a b : Word) : c.holds w (w.truncate a) b = c.holds w a b :=
  holds_congr (X86.Encode.truncate_truncate w a) rfl

/-- A swapped comparison's flags decide the condition. -/
theorem cmp_swap_test {c : Lir.Cond} {cx : X86.Condition} (h : condX86 c = some cx) (w : Width) (a b : Word) :
    (X86.ByteEval.aluFlags .sub w b a).test (swapCond cx) = some (c.holds w a b) := by
  rw [X86.ByteEval.compare_flags, swapCond_holds, condX86_holds h]

/-- `test` narrowed to the immediate's width decides the tag test. -/
theorem tz_narrow (w : Width) (a k c : Word) (hk : w.truncate k = k)
    (hc : (testWidth w k).truncate c = (testWidth w k).truncate k) :
    (Lir.Cond.holds .tz (testWidth w k) a c) = Lir.Cond.holds .tz w a k := by
  simp only [Lir.Cond.holds]
  rw [truncate_and, truncate_and, hc, ← truncate_and, ← truncate_and]
  congr 1
  unfold testWidth
  simp only [hk]
  have hand : (a &&& k).toNat ≤ k.toNat := by rw [UInt64.toNat_and]; exact Nat.and_le_right
  split
  · rename_i h8
    rw [truncate_eq_self (show (a &&& k).toNat < 2 ^ Width.w8.bits by simp only [Width.bits]; omega)]
    rw [truncate_eq_self (show (a &&& k).toNat < 2 ^ w.bits by
      have := Nat.pow_le_pow_right (n := 2) (by decide) (show 8 ≤ w.bits by cases w <;> decide)
      have : 2 ^ 8 = 256 := rfl
      omega)]
  · split
    · rename_i _ h32
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h32
      obtain ⟨h32, rfl⟩ := h32
      rw [truncate_eq_self (show (a &&& k).toNat < 2 ^ Width.w32.bits by simp only [Width.bits]; omega),
        X86.Encode.truncate64]
    · rfl

theorem tnz_narrow (w : Width) (a k c : Word) (hk : w.truncate k = k)
    (hc : (testWidth w k).truncate c = (testWidth w k).truncate k) :
    (Lir.Cond.holds .tnz (testWidth w k) a c) = Lir.Cond.holds .tnz w a k := by
  have := tz_narrow w a k c hk hc
  simp only [Lir.Cond.holds] at this ⊢
  rw [bne, bne, this]

/-! ## Immediates -/

/-- `mov r32, imm32` of a 32-bit constant leaves the constant. -/
theorem mov32_imm {k : Word} (h : k.toNat < 2 ^ 32) : Width.w32.truncate (X86.ImmKind.imm32.norm k) = k := by
  apply UInt64.toNat_inj.mp
  rw [X86.Encode.truncate_nat]
  simp only [Width.bits, X86.ImmKind.norm]
  rw [X86.Encode.signExtend32_low]
  simp only [UInt64.toNat_toUInt32]
  exact Nat.mod_eq_of_lt h

end Compilatrix.Xv.Select.Proof
