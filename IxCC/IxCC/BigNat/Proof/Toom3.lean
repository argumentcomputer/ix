import IxCC.BigNat.Toom3
import IxCC.BigNat.Proof.Linear

/-! # Layer-1 Proofs for `IxCC.BigNat.Toom3` (`IxCC.BigNat.Proof.Toom3`)

Formal correctness and canonical normal-form preservation for:
- Exact division by `3` (`inv3_64_mul_three`, `wf_divExact3`, `divExact3_spec`)
- Signed magnitude difference (`wf_signedSub`, `signedSub_spec`)
- In-place Toom-3 coefficient recombination (`wf_toom3Combine`, `toNat_toom3Combine`)
- Exact 5-point nonnegative Toom-3 interpolation (`wf_toom3Interp`, `toom3Interp_spec`)

All theorems depend strictly on `[propext, Classical.choice, Quot.sound]`.
-/

namespace IxCC.BigNat

/-! ### Exact Division by 3 (`divExact3`) -/

theorem inv3_64_toNat : inv3_64.toNat = 0xAAAAAAAA * 2 ^ 32 + 0xAAAAAAAB := by
  unfold inv3_64
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft]
  have h32m : (32 : UInt64).toNat % 64 = 32 := rfl
  have ha : (0xAAAAAAAA : UInt64).toNat = 0xAAAAAAAA := rfl
  have hb : (0xAAAAAAAB : UInt64).toNat = 0xAAAAAAAB := rfl
  rw [h32m, ha, hb, Nat.shiftLeft_eq]
  have h2_64 : 2 ^ 64 = 2 ^ 32 * 2 ^ 32 := by rw [← Nat.pow_add]
  have hltA : 0xAAAAAAAA < 2 ^ 32 := by omega
  have hltB : 0xAAAAAAAB < 2 ^ 32 := by omega
  have hmul_lt : 0xAAAAAAAA * 2 ^ 32 < 2 ^ 64 := by
    rw [h2_64]; exact Nat.mul_lt_mul_of_pos_right hltA (Nat.two_pow_pos 32)
  rw [Nat.mod_eq_of_lt hmul_lt]
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [Nat.testBit_or]
  have hdiv : (0xAAAAAAAA * 2 ^ 32 + 0xAAAAAAAB) / 2 ^ 32 = 0xAAAAAAAA := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 32),
        Nat.div_eq_of_lt hltB, Nat.zero_add]
  have hmod : (0xAAAAAAAA * 2 ^ 32 + 0xAAAAAAAB) % 2 ^ 32 = 0xAAAAAAAB := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hltB]
  by_cases hlt : bit < 32
  · have hq0 : (0xAAAAAAAA * 2 ^ 32).testBit bit = false := by
      rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
      have hge : ¬ 32 ≤ bit := by omega
      simp [hge]
    have hsum : (0xAAAAAAAA * 2 ^ 32 + 0xAAAAAAAB).testBit bit =
        ((0xAAAAAAAA * 2 ^ 32 + 0xAAAAAAAB) % 2 ^ 32).testBit bit := by
      rw [Nat.testBit_mod_two_pow]; simp [hlt]
    rw [hq0, Bool.false_or, hsum, hmod]
  · have hlo0 : (0xAAAAAAAB : Nat).testBit bit = false :=
      testBit_eq_false_of_lt_pow (Nat.lt_of_lt_of_le hltB (Nat.pow_le_pow_right (by decide) (by omega)))
    have hsub : bit = 32 + (bit - 32) := by omega
    have hsum : (0xAAAAAAAA * 2 ^ 32 + 0xAAAAAAAB).testBit bit = (0xAAAAAAAA : Nat).testBit (bit - 32) := by
      conv => lhs; rw [hsub]
      rw [← Nat.testBit_shiftRight, Nat.shiftRight_eq_div_pow, hdiv]
    have hlhs : (0xAAAAAAAA * 2 ^ 32).testBit bit = (0xAAAAAAAA : Nat).testBit (bit - 32) := by
      rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
      have hge : 32 ≤ bit := by omega
      simp [hge]
    rw [hlo0, Bool.or_false, hsum, hlhs]

theorem inv3_64_mul_three : inv3_64.toNat * 3 = 2 * 2 ^ 64 + 1 := by
  rw [inv3_64_toNat]

private theorem four_pow_mod_three (k : Nat) : 4 ^ k % 3 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

private theorem two_pow_64_mod_three : 2 ^ 64 % 3 = 1 := by
  have h : 2 ^ 64 = 4 ^ 32 := by
    have h4 : (4 : Nat) = 2 ^ 2 := rfl
    rw [h4, ← Nat.pow_mul]
  exact h ▸ four_pow_mod_three 32

private theorem two_pow_64_pow_mod_three (k : Nat) : (2 ^ 64) ^ k % 3 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih, two_pow_64_mod_three]

private theorem divExact3_step_arith (a_i carry diff pLo pHi : UInt64) (borrow : Bool)
    (hcar : carry.toNat ≤ 2)
    (hs : subBorrow64 a_i carry false = (diff, borrow))
    (hm : mulWide64 (diff * inv3_64) 3 = (pLo, pHi)) :
    let carry' := if borrow then pHi + 1 else pHi
    carry'.toNat ≤ 2 ∧
    (diff * inv3_64).toNat * 3 + carry.toNat = a_i.toNat + carry'.toNat * 2 ^ 64 := by
  have hsub := subBorrow64_spec a_i carry false
  rw [hs] at hsub
  have hf : false.toNat = 0 := rfl
  rw [hf, Nat.add_zero] at hsub
  let q := diff * inv3_64
  have hmul := mulWide64_spec q 3
  rw [hm] at hmul
  dsimp only at hsub hmul ⊢
  have h3 : (3 : UInt64).toNat = 3 := rfl
  rw [h3] at hmul
  have hdiff_lt : diff.toNat < 2 ^ 64 := uint64_toNat_lt diff
  have hpLo_lt : pLo.toNat < 2 ^ 64 := uint64_toNat_lt pLo
  have hq_lt : q.toNat < 2 ^ 64 := uint64_toNat_lt q
  -- Prove pLo = diff via (q * 3) % 2^64 = diff
  have hq_mod : (q.toNat * 3) % 2 ^ 64 = diff.toNat := by
    have hq_eq : q.toNat = (diff.toNat * inv3_64.toNat) % 2 ^ 64 := UInt64.toNat_mul diff inv3_64
    rw [hq_eq, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc, inv3_64_mul_three]
    rw [Nat.mul_add, Nat.mul_one]
    have hcomm : diff.toNat * (2 * 2 ^ 64) = (diff.toNat * 2) * 2 ^ 64 := (Nat.mul_assoc _ _ _).symm
    rw [hcomm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hdiff_lt]
  have hpLo_eq : pLo.toNat = diff.toNat := by
    have h1 : (pLo.toNat + pHi.toNat * 2 ^ 64) % 2 ^ 64 = pLo.toNat := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpLo_lt]
    rw [← h1, hmul, hq_mod]
  -- Combine: q * 3 + carry = a_i + (pHi + borrow) * 2^64
  have hcomb : q.toNat * 3 + carry.toNat = a_i.toNat + (pHi.toNat + borrow.toNat) * 2 ^ 64 := by
    rw [← hmul, hpLo_eq, Nat.add_mul]
    omega
  have hhi_lt3 : pHi.toNat + borrow.toNat < 3 := by
    have hbound : q.toNat * 3 + carry.toNat < 3 * 2 ^ 64 := by
      have h1 : q.toNat + 1 ≤ 2 ^ 64 := hq_lt
      have h2 : (q.toNat + 1) * 3 ≤ 2 ^ 64 * 3 := Nat.mul_le_mul_right 3 h1
      rw [Nat.add_mul, Nat.one_mul] at h2
      omega
    have hlt2 : (pHi.toNat + borrow.toNat) * 2 ^ 64 < 3 * 2 ^ 64 := by omega
    exact Nat.lt_of_mul_lt_mul_right hlt2
  have hcar'_toNat : (if borrow then pHi + 1 else pHi).toNat = pHi.toNat + borrow.toNat := by
    cases borrow
    · simp
    · simp only [↓reduceIte, Bool.toNat_true]
      rw [UInt64.toNat_add]
      have h1 : (1 : UInt64).toNat = 1 := rfl
      have hpHi_lt : pHi.toNat + 1 < 2 ^ 64 := by
        have : pHi.toNat + 1 < 3 := by simpa using hhi_lt3
        omega
      rw [h1, Nat.mod_eq_of_lt hpHi_lt]
  refine ⟨by rw [hcar'_toNat]; omega, ?_⟩
  rw [hcar'_toNat]
  exact hcomb

private theorem divExact3Loop_spec (a : Array UInt64) (i rem : Nat) (carry : UInt64)
    (acc : Array UInt64) (hsz : acc.size = i) (hcar : carry.toNat ≤ 2) :
    ∃ finalCarry : Nat, finalCarry ≤ 2 ∧
      toNat (divExact3Loop a i carry acc rem) * 3 + toNatPrefix a i + carry.toNat * (2 ^ 64) ^ i =
        toNat acc * 3 + toNatPrefix a (i + rem) + finalCarry * (2 ^ 64) ^ (i + rem) := by
  induction rem generalizing i carry acc with
  | zero =>
    unfold divExact3Loop
    simp only [Nat.add_zero]
    exact ⟨carry.toNat, hcar, by omega⟩
  | succ rem ih =>
    unfold divExact3Loop
    rcases hs : subBorrow64 (getLimb a i) carry false with ⟨diff, borrow⟩
    dsimp only
    rcases hm : mulWide64 (diff * inv3_64) 3 with ⟨pLo, pHi⟩
    dsimp only
    have ⟨hcar', hstep⟩ := divExact3_step_arith (getLimb a i) carry diff pLo pHi borrow hcar hs hm
    have ⟨fc, hfc_le, hih⟩ := ih (i + 1) (if borrow then pHi + 1 else pHi)
      (acc.push (diff * inv3_64)) (by simp [hsz]) hcar'
    refine ⟨fc, hfc_le, ?_⟩
    have hidx : i + 1 + rem = i + (rem + 1) := by omega
    rw [hidx, toNat_push, hsz, toNatPrefix_succ a i, Nat.add_mul, Nat.pow_succ (2 ^ 64) i] at hih
    have hmul := congrArg (· * (2 ^ 64) ^ i) hstep
    rw [Nat.add_mul, Nat.add_mul] at hmul
    have hr1 : (diff * inv3_64).toNat * (2 ^ 64) ^ i * 3 = (diff * inv3_64).toNat * 3 * (2 ^ 64) ^ i := by
      rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ i) 3, ← Nat.mul_assoc]
    have hr2 : (if borrow then pHi + 1 else pHi).toNat * ((2 ^ 64) ^ i * 2 ^ 64) =
        (if borrow then pHi + 1 else pHi).toNat * 2 ^ 64 * (2 ^ 64) ^ i := by
      rw [Nat.mul_comm ((2 ^ 64) ^ i) (2 ^ 64), ← Nat.mul_assoc]
    rw [hr1, hr2] at hih
    clear hs hm hstep hr1 hr2
    omega

theorem wf_divExact3 (a : Array UInt64) : WF (divExact3 a) := by
  unfold divExact3
  split
  · exact Or.inl rfl
  · exact wf_normalize _

theorem divExact3_spec (a : Array UInt64) (hdvd : 3 ∣ toNat a) :
    toNat (divExact3 a) * 3 = toNat a := by
  unfold divExact3
  split
  · rename_i h0
    have hz : a.size = 0 := eq_of_beq h0
    have hto : toNat a = 0 := by rw [toNat, hz]; rfl
    simp [hto]
  · rw [toNat_normalize]
    have ⟨fc, hfc_le, heq⟩ := divExact3Loop_spec a 0 a.size 0 (Array.mkEmpty a.size) (by simp) (by decide)
    simp only [toNatPrefix_zero, toNat_mkEmpty, UInt64.toNat_zero, Nat.zero_mul, Nat.add_zero,
      Nat.zero_add] at heq
    have hmod_lhs : (toNat (divExact3Loop a 0 0 (Array.mkEmpty a.size) a.size) * 3) % 3 = 0 :=
      Nat.mul_mod_left _ 3
    rcases hdvd with ⟨k, hk⟩
    have hmod_a : toNat a % 3 = 0 := by rw [hk]; exact Nat.mul_mod_right 3 k
    have hmod_rhs : (toNat a + fc * (2 ^ 64) ^ a.size) % 3 = fc % 3 := by
      rw [Nat.add_mod, hmod_a, Nat.zero_add, Nat.mod_mod, Nat.mul_mod,
          two_pow_64_pow_mod_three a.size, Nat.mul_one, Nat.mod_mod]
    have hfc_mod : fc % 3 = 0 := by
      change toNat (divExact3Loop a 0 0 (Array.mkEmpty a.size) a.size) * 3 =
          toNat a + fc * (2 ^ 64) ^ a.size at heq
      rw [← hmod_rhs, ← heq, hmod_lhs]
    have hfc0 : fc = 0 := by omega
    rw [hfc0, Nat.zero_mul, Nat.add_zero] at heq
    exact heq

/-! ### Signed Difference (`signedSub`) -/

theorem wf_signedSub (a b : Array UInt64) : WF (signedSub a b).2 := by
  unfold signedSub
  cases cmp a b with
  | lt => exact wf_subRaw b a
  | eq => exact Or.inl rfl
  | gt => exact wf_subRaw a b

theorem signedSub_spec {a b : Array UInt64} (ha : WF a) (hb : WF b) :
    let res := signedSub a b
    WF res.2 ∧
    (if res.1 then toNat a + toNat res.2 = toNat b else toNat b + toNat res.2 = toNat a) := by
  refine ⟨wf_signedSub a b, ?_⟩
  unfold signedSub
  have hcmp := cmp_spec ha hb
  cases hc : cmp a b with
  | lt =>
    rw [hc] at hcmp
    have hlt : toNat a < toNat b := by
      have h : compare (toNat a) (toNat b) = .lt := hcmp.symm
      simp only [compare, compareOfLessAndEq] at h
      split at h
      · assumption
      · split at h <;> simp at h
    simp only [↓reduceIte, toNat_subRaw]
    omega
  | eq =>
    rw [hc] at hcmp
    have heq : toNat a = toNat b := by
      have h : compare (toNat a) (toNat b) = .eq := hcmp.symm
      simp only [compare, compareOfLessAndEq] at h
      split at h
      · simp at h
      · split at h
        · assumption
        · simp at h
    simp [heq]
  | gt =>
    rw [hc] at hcmp
    have hgt : toNat b < toNat a := by
      have h : compare (toNat a) (toNat b) = .gt := hcmp.symm
      simp only [compare, compareOfLessAndEq] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i hnotlt hnoteq; omega
    simp only [Bool.false_eq_true, ↓reduceIte, toNat_subRaw]
    omega

theorem toom3EvalLoop_eq (a : Array UInt64) (k : Nat) :
    let a0 := normalize (slice a 0 k)
    let a1 := normalize (slice a k (2 * k))
    let a2 := normalize (slice a (2 * k) a.size)
    let p02 := add a0 a2
    let pm1 := signedSub p02 a1
    toom3EvalLoop a k #[] #[] #[] 3 =
      (a0, a2, add p02 a1, pm1.1, pm1.2, add (shiftLeft1 (add (shiftLeft1 a2) a1)) a0) := by
  simp [toom3EvalLoop]

/-! ### Toom-3 Recombination (`toom3Combine`) & 5-Point Interpolation (`toom3Interp`) -/

private theorem toNat_subMul1InPlace_of_le (acc b : Array UInt64) (m : UInt64)
    (hle : m.toNat * toNat b ≤ toNat acc) :
    toNat (subMul1InPlace acc b m).1 = toNat acc - m.toNat * toNat b := by
  have h := subMul1InPlace_spec acc b m
  dsimp only at h
  have hlt : toNat (subMul1InPlace acc b m).1 < (2 ^ 64) ^ (subMul1InPlace acc b m).1.size :=
    toNat_lt _
  by_cases hbw : (subMul1InPlace acc b m).2.toNat = 0
  · rw [hbw, Nat.zero_mul, Nat.add_zero] at h; omega
  · have hge : (2 ^ 64) ^ (subMul1InPlace acc b m).1.size ≤
        (subMul1InPlace acc b m).2.toNat * (2 ^ 64) ^ (subMul1InPlace acc b m).1.size :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega

private theorem wf_toom3CombineLoop (c1 c2 c3 c4 : Array UInt64) (k : Nat) (acc : Array UInt64) :
    ∀ step, WF (toom3CombineLoop c1 c2 c3 c4 k acc step)
  | 0 => wf_normalize acc
  | step + 1 => wf_toom3CombineLoop c1 c2 c3 c4 k _ step

theorem wf_toom3Combine (c0 c1 c2 c3 c4 : Array UInt64) (k outSize : Nat) :
    WF (toom3Combine c0 c1 c2 c3 c4 k outSize) :=
  wf_toom3CombineLoop c1 c2 c3 c4 k (copyIntoZeros c0 outSize) 4

theorem toNat_toom3Combine (c0 c1 c2 c3 c4 : Array UInt64) (k outSize : Nat) :
    toNat (toom3Combine c0 c1 c2 c3 c4 k outSize) =
      toNat c0 + toNat c1 * (2 ^ 64) ^ k + toNat c2 * (2 ^ 64) ^ (2 * k) +
      toNat c3 * (2 ^ 64) ^ (3 * k) + toNat c4 * (2 ^ 64) ^ (4 * k) := by
  unfold toom3Combine
  simp only [toom3CombineLoop, beq_self_eq_true, ↓reduceIte,
    show (2 == 3) = false from rfl, show (1 == 3) = false from rfl,
    show (1 == 2) = false from rfl, show (0 == 3) = false from rfl,
    show (0 == 2) = false from rfl, show (0 == 1) = false from rfl,
    Bool.false_eq_true, Nat.one_mul,
    toNat_normalize, toNat_addAtInPlace, toNat_copyIntoZeros]

private theorem subMul3Loop_eq_1 (c acc : Array UInt64) :
    subMul3Loop #[] #[] c 0 0 1 acc 1 = normalize (subAtInPlace acc c 0).1 := by
  simp [subMul3Loop]

private theorem subMul3Loop_eq_2 (b c acc : Array UInt64) :
    subMul3Loop #[] b c 0 1 1 acc 2 =
      normalize (subAtInPlace (subAtInPlace acc b 0).1 c 0).1 := by
  simp [subMul3Loop]

private theorem subMul3Loop_eq_3 (a b c acc : Array UInt64) :
    subMul3Loop a b c 1 4 16 acc 3 =
      normalize (subMul1InPlace (subMul1InPlace (subAtInPlace acc a 0).1 b 4).1 c 16).1 := by
  simp [subMul3Loop]

theorem wf_toom3Interp (r0 r1 rm1 r2 rInf : Array UInt64) (rm1Neg : Bool) (k outSize : Nat) :
    WF (toom3Interp r0 r1 rm1 r2 rInf rm1Neg k outSize) := by
  unfold toom3Interp
  exact wf_toom3Combine _ _ _ _ _ _ _

theorem toom3Interp_spec (r0 r1 rm1 r2 rInf : Array UInt64) (rm1Neg : Bool) (k outSize : Nat)
    (c0 c1 c2 c3 c4 : Nat)
    (hr0 : toNat r0 = c0)
    (hrInf : toNat rInf = c4)
    (hr1 : toNat r1 = c0 + c1 + c2 + c3 + c4)
    (hrm1 : if rm1Neg then toNat rm1 + (c0 + c2 + c4) = c1 + c3
            else toNat rm1 + (c1 + c3) = c0 + c2 + c4)
    (hr2 : toNat r2 = c0 + 2 * c1 + 4 * c2 + 8 * c3 + 16 * c4) :
    WF (toom3Interp r0 r1 rm1 r2 rInf rm1Neg k outSize) ∧
    toNat (toom3Interp r0 r1 rm1 r2 rInf rm1Neg k outSize) =
      c0 + c1 * (2 ^ 64) ^ k + c2 * (2 ^ 64) ^ (2 * k) +
      c3 * (2 ^ 64) ^ (3 * k) + c4 * (2 ^ 64) ^ (4 * k) := by
  refine ⟨wf_toom3Interp r0 r1 rm1 r2 rInf rm1Neg k outSize, ?_⟩
  unfold toom3Interp
  dsimp only
  rw [subMul3Loop_eq_2, subMul3Loop_eq_3, subMul3Loop_eq_1, subMul3Loop_eq_1]
  let hi := shiftRight1 (add r1 rm1)
  let lo := subRaw hi rm1
  let t024 := if rm1Neg then lo else hi
  let t13  := if rm1Neg then hi else lo
  have hhi : toNat hi = if rm1Neg then c1 + c3 else c0 + c2 + c4 := by
    show toNat (shiftRight1 (add r1 rm1)) = _
    rw [toNat_shiftRight1, toNat_add, hr1]
    cases rm1Neg
    · simp only [Bool.false_eq_true, ↓reduceIte] at hrm1 ⊢; omega
    · simp only [↓reduceIte] at hrm1 ⊢; omega
  have hlo : toNat lo = if rm1Neg then c0 + c2 + c4 else c1 + c3 := by
    show toNat (subRaw hi rm1) = _
    rw [toNat_subRaw, hhi]
    cases rm1Neg
    · simp only [Bool.false_eq_true, ↓reduceIte] at hrm1 ⊢; omega
    · simp only [↓reduceIte] at hrm1 ⊢; omega
  have ht024 : toNat t024 = c0 + c2 + c4 := by
    dsimp only [t024]; cases rm1Neg <;> simp [hhi, hlo]
  have ht13 : toNat t13 = c1 + c3 := by
    dsimp only [t13]; cases rm1Neg <;> simp [hhi, hlo]
  -- Step 2: c2 = t024 - r0 - rInf
  have hc2_1 : toNat (subAtInPlace t024 r0 0).1 = c2 + c4 := by
    have h := (toNat_subAtInPlace_of_le t024 r0 0 (by simp [ht024, hr0]; omega)).2
    simp only [Nat.pow_zero, Nat.mul_one, ht024, hr0] at h
    omega
  have hc2_2 : toNat (subAtInPlace (subAtInPlace t024 r0 0).1 rInf 0).1 = c2 := by
    have h := (toNat_subAtInPlace_of_le (subAtInPlace t024 r0 0).1 rInf 0
      (by simp [hc2_1, hrInf])).2
    simp only [Nat.pow_zero, Nat.mul_one, hc2_1, hrInf] at h
    omega
  let c2Arr := normalize (subAtInPlace (subAtInPlace t024 r0 0).1 rInf 0).1
  have hc2_val : toNat c2Arr = c2 := by
    show toNat (normalize _) = c2
    rw [toNat_normalize, hc2_2]
  -- Step 3: u = (r2 - r0 - 4*c2 - 16*rInf) / 2 = c1 + 4*c3
  have hu1 : toNat (subAtInPlace r2 r0 0).1 = 2 * c1 + 4 * c2 + 8 * c3 + 16 * c4 := by
    have h := (toNat_subAtInPlace_of_le r2 r0 0 (by simp [hr2, hr0]; omega)).2
    simp only [Nat.pow_zero, Nat.mul_one, hr2, hr0] at h
    omega
  have h4 : (4 : UInt64).toNat = 4 := rfl
  have h16 : (16 : UInt64).toNat = 16 := rfl
  have hu2 : toNat (subMul1InPlace (subAtInPlace r2 r0 0).1 c2Arr 4).1 = 2 * c1 + 8 * c3 + 16 * c4 := by
    have h := toNat_subMul1InPlace_of_le (subAtInPlace r2 r0 0).1 c2Arr 4
      (by rw [h4, hc2_val, hu1]; omega)
    rw [h4, hc2_val, hu1] at h
    omega
  have hu3 : toNat (subMul1InPlace (subMul1InPlace (subAtInPlace r2 r0 0).1 c2Arr 4).1 rInf 16).1 =
      2 * c1 + 8 * c3 := by
    have h := toNat_subMul1InPlace_of_le (subMul1InPlace (subAtInPlace r2 r0 0).1 c2Arr 4).1 rInf 16
      (by rw [h16, hrInf, hu2]; omega)
    rw [h16, hrInf, hu2] at h
    omega
  let u := shiftRight1 (normalize (subMul1InPlace (subMul1InPlace (subAtInPlace r2 r0 0).1 c2Arr 4).1 rInf 16).1)
  have hu_val : toNat u = c1 + 4 * c3 := by
    show toNat (shiftRight1 (normalize _)) = c1 + 4 * c3
    rw [toNat_shiftRight1, toNat_normalize, hu3]
    omega
  -- Step 4: c3 = divExact3 (u - t13)
  have hdiff3 : toNat (subAtInPlace u t13 0).1 = 3 * c3 := by
    have h := (toNat_subAtInPlace_of_le u t13 0 (by simp [hu_val, ht13]; omega)).2
    simp only [Nat.pow_zero, Nat.mul_one, hu_val, ht13] at h
    omega
  let c3Arr := divExact3 (normalize (subAtInPlace u t13 0).1)
  have hc3_val : toNat c3Arr = c3 := by
    have hdvd : 3 ∣ toNat (normalize (subAtInPlace u t13 0).1) := by
      rw [toNat_normalize, hdiff3]; exact ⟨c3, rfl⟩
    have h := divExact3_spec (normalize (subAtInPlace u t13 0).1) hdvd
    rw [toNat_normalize, hdiff3] at h
    change toNat c3Arr * 3 = 3 * c3 at h
    omega
  -- Step 5: c1 = t13 - c3
  have hc1_raw : toNat (subAtInPlace t13 c3Arr 0).1 = c1 := by
    have h := (toNat_subAtInPlace_of_le t13 c3Arr 0 (by simp [ht13, hc3_val])).2
    simp only [Nat.pow_zero, Nat.mul_one, ht13, hc3_val] at h
    omega
  -- Step 6: toom3Combine
  rw [toNat_toom3Combine, hr0, toNat_normalize, hc1_raw, hc2_val, hc3_val, hrInf]

theorem wf_karatsubaCombine (z0 z2 z1Full : Array UInt64) (m outSize : Nat) :
    WF (karatsubaCombine z0 z2 z1Full m outSize) :=
  wf_normalize _

theorem toNat_karatsubaCombine (z0 z2 z1Full : Array UInt64)
    (a0 a1 b0 b1 m outSize : Nat)
    (hz0 : toNat z0 = a0 * b0) (hz2 : toNat z2 = a1 * b1)
    (hzS : toNat z1Full = (a0 + a1) * (b0 + b1)) :
    toNat (karatsubaCombine z0 z2 z1Full m outSize) =
      (a0 + a1 * (2 ^ 64) ^ m) * (b0 + b1 * (2 ^ 64) ^ m) := by
  unfold karatsubaCombine
  dsimp only
  have hexp : (a0 + a1) * (b0 + b1) = a0 * b0 + a0 * b1 + a1 * b0 + a1 * b1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have hz1a : toNat (subAtInPlace z1Full z0 0).1 = a0 * b1 + a1 * b0 + a1 * b1 := by
    have h := (toNat_subAtInPlace_of_le z1Full z0 0 (by simp [hzS, hz0, hexp]; omega)).2
    simp only [Nat.pow_zero, Nat.mul_one, hzS, hz0] at h
    omega
  have hz1b : toNat (subAtInPlace (subAtInPlace z1Full z0 0).1 z2 0).1 = a0 * b1 + a1 * b0 := by
    have h := (toNat_subAtInPlace_of_le (subAtInPlace z1Full z0 0).1 z2 0
      (by simp [hz1a, hz2])).2
    simp only [Nat.pow_zero, Nat.mul_one, hz1a, hz2] at h
    omega
  rw [toNat_normalize, toNat_addAtInPlace, toNat_addAtInPlace, toNat_copyIntoZeros,
      toNat_normalize, hz0, hz1b, hz2]
  have hpow2 : (2 ^ 64) ^ (2 * m) = (2 ^ 64) ^ m * (2 ^ 64) ^ m := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hpow2]
  calc a0 * b0 + (a0 * b1 + a1 * b0) * (2 ^ 64) ^ m + a1 * b1 * ((2 ^ 64) ^ m * (2 ^ 64) ^ m)
      = a0 * b0 + a0 * (b1 * (2 ^ 64) ^ m) +
        (a1 * (2 ^ 64) ^ m * b0 + a1 * (2 ^ 64) ^ m * (b1 * (2 ^ 64) ^ m)) := by
        rw [Nat.add_mul]
        have t1 : a0 * b1 * (2 ^ 64) ^ m = a0 * (b1 * (2 ^ 64) ^ m) := Nat.mul_assoc _ _ _
        have t2 : a1 * b0 * (2 ^ 64) ^ m = a1 * (2 ^ 64) ^ m * b0 := by
          rw [Nat.mul_assoc, Nat.mul_comm b0 ((2 ^ 64) ^ m), ← Nat.mul_assoc]
        have t3 : a1 * b1 * ((2 ^ 64) ^ m * (2 ^ 64) ^ m) =
            a1 * (2 ^ 64) ^ m * (b1 * (2 ^ 64) ^ m) := by ac_rfl
        rw [t1, t2, t3]; omega
    _ = (a0 + a1 * (2 ^ 64) ^ m) * (b0 + b1 * (2 ^ 64) ^ m) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]

end IxCC.BigNat
