import IxCC.BigNat.Linear
import IxCC.BigNat.Proof.Basic

/-! # Layer-1 Proofs for `IxCC.BigNat.Linear` (`IxCC.BigNat.Proof.Linear`)

Formal correctness and canonical normal-form preservation for all linear-time
`BigNat` operations: `cmp`, `beq`, `ble`, `blt`, `add`, `subRaw`, `sub`, `pred`,
`land`, `lor`, `xor`, `shiftLimbs`, `shiftLeft`, `shiftRight`, and `log2`.

All theorems depend strictly on `[propext, Classical.choice, Quot.sound]`.
-/

namespace IxCC.BigNat

/-! ### Comparison (`cmp`, `beq`, `ble`, `blt`) -/

theorem cmpLoop_spec (a b : Array UInt64) (k : Nat) :
    cmpLoop a b k = compare (toNatPrefix a k) (toNatPrefix b k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold cmpLoop
    dsimp only
    rw [toNatPrefix_succ, toNatPrefix_succ]
    have hltA : toNatPrefix a k < (2 ^ 64) ^ k := toNatPrefix_lt a k
    have hltB : toNatPrefix b k < (2 ^ 64) ^ k := toNatPrefix_lt b k
    by_cases hlt : getLimb a k < getLimb b k
    · simp only [hlt, ↓reduceIte]
      have hnat : (getLimb a k).toNat < (getLimb b k).toNat := UInt64.lt_iff_toNat_lt.mp hlt
      have h1 : ((getLimb a k).toNat + 1) * (2 ^ 64) ^ k ≤ (getLimb b k).toNat * (2 ^ 64) ^ k :=
        Nat.mul_le_mul_right _ hnat
      rw [Nat.add_mul, Nat.one_mul] at h1
      have htotal : toNatPrefix a k + (getLimb a k).toNat * (2 ^ 64) ^ k <
          toNatPrefix b k + (getLimb b k).toNat * (2 ^ 64) ^ k := by omega
      simp [compare, compareOfLessAndEq, htotal]
    · simp only [hlt, ↓reduceIte]
      by_cases hgt : getLimb a k > getLimb b k
      · simp only [hgt, ↓reduceIte]
        have hnat : (getLimb b k).toNat < (getLimb a k).toNat := UInt64.lt_iff_toNat_lt.mp hgt
        have h1 : ((getLimb b k).toNat + 1) * (2 ^ 64) ^ k ≤ (getLimb a k).toNat * (2 ^ 64) ^ k :=
          Nat.mul_le_mul_right _ hnat
        rw [Nat.add_mul, Nat.one_mul] at h1
        have htotal : toNatPrefix b k + (getLimb b k).toNat * (2 ^ 64) ^ k <
            toNatPrefix a k + (getLimb a k).toNat * (2 ^ 64) ^ k := by omega
        have hnotlt : ¬ (toNatPrefix a k + (getLimb a k).toNat * (2 ^ 64) ^ k <
            toNatPrefix b k + (getLimb b k).toNat * (2 ^ 64) ^ k) := by omega
        have hne : toNatPrefix a k + (getLimb a k).toNat * (2 ^ 64) ^ k ≠
            toNatPrefix b k + (getLimb b k).toNat * (2 ^ 64) ^ k := by omega
        simp [compare, compareOfLessAndEq, hnotlt, hne]
      · simp only [hgt, ↓reduceIte]
        have heqN : (getLimb a k).toNat = (getLimb b k).toNat := by
          have h1 : ¬ (getLimb a k).toNat < (getLimb b k).toNat :=
            fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
          have h2 : ¬ (getLimb b k).toNat < (getLimb a k).toNat :=
            fun h => hgt (UInt64.lt_iff_toNat_lt.mpr h)
          omega
        rw [ih, heqN]
        simp only [compare, compareOfLessAndEq]
        by_cases h1 : toNatPrefix a k < toNatPrefix b k
        · have h1' : toNatPrefix a k + (getLimb b k).toNat * (2 ^ 64) ^ k <
              toNatPrefix b k + (getLimb b k).toNat * (2 ^ 64) ^ k := by omega
          simp [h1, h1']
        · by_cases h2 : toNatPrefix a k = toNatPrefix b k
          · simp [h2]
          · have h1' : ¬ (toNatPrefix a k + (getLimb b k).toNat * (2 ^ 64) ^ k <
                toNatPrefix b k + (getLimb b k).toNat * (2 ^ 64) ^ k) := by omega
            simp [h1, h2, h1']

theorem cmp_spec {a b : Array UInt64} (ha : WF a) (hb : WF b) :
    cmp a b = compare (toNat a) (toNat b) := by
  unfold cmp
  by_cases hlt : a.size < b.size
  · simp only [hlt, ↓reduceIte]
    have h1 : toNat a < (2 ^ 64) ^ a.size := toNat_lt a
    have h2 : (2 ^ 64) ^ (b.size - 1) ≤ toNat b := toNat_ge_top b hb (by omega)
    have h3 : (2 ^ 64) ^ a.size ≤ (2 ^ 64) ^ (b.size - 1) :=
      Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
    have hnat : toNat a < toNat b := by omega
    simp [compare, compareOfLessAndEq, hnat]
  · simp only [hlt, ↓reduceIte]
    by_cases hgt : a.size > b.size
    · simp only [hgt, ↓reduceIte]
      have h1 : toNat b < (2 ^ 64) ^ b.size := toNat_lt b
      have h2 : (2 ^ 64) ^ (a.size - 1) ≤ toNat a := toNat_ge_top a ha (by omega)
      have h3 : (2 ^ 64) ^ b.size ≤ (2 ^ 64) ^ (a.size - 1) :=
        Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
      have hnotlt : ¬ toNat a < toNat b := by omega
      have hne : toNat a ≠ toNat b := by omega
      simp [compare, compareOfLessAndEq, hnotlt, hne]
    · simp only [hgt, ↓reduceIte]
      have heq : a.size = b.size := by omega
      unfold toNat
      rw [← heq]
      exact cmpLoop_spec a b a.size

theorem beq_spec {a b : Array UInt64} (ha : WF a) (hb : WF b) :
    beq a b = (toNat a == toNat b) := by
  unfold beq
  rw [cmp_spec ha hb]
  simp only [compare, compareOfLessAndEq]
  by_cases hlt : toNat a < toNat b
  · have hne : toNat a ≠ toNat b := by omega
    simp [hlt, hne]
  · by_cases heq : toNat a = toNat b
    · simp [heq]
    · simp [hlt, heq]

theorem ble_spec {a b : Array UInt64} (ha : WF a) (hb : WF b) :
    ble a b = decide (toNat a ≤ toNat b) := by
  unfold ble
  rw [cmp_spec ha hb]
  simp only [compare, compareOfLessAndEq]
  by_cases hlt : toNat a < toNat b
  · have hle : toNat a ≤ toNat b := by omega
    simp [hlt, hle]
  · by_cases heq : toNat a = toNat b
    · simp [heq]
    · have hnotle : ¬ toNat a ≤ toNat b := by omega
      simp [hlt, heq, hnotle]

theorem blt_spec {a b : Array UInt64} (ha : WF a) (hb : WF b) :
    blt a b = decide (toNat a < toNat b) := by
  unfold blt
  rw [cmp_spec ha hb]
  simp only [compare, compareOfLessAndEq]
  by_cases hlt : toNat a < toNat b
  · simp [hlt]
  · by_cases heq : toNat a = toNat b <;> simp [hlt, heq]

/-! ### Addition (`add`) -/

theorem toNat_addLoop (a b : Array UInt64) (n i : Nat) (carry : Bool) (acc : Array UInt64)
    (hi : i ≤ n) (hsz : acc.size = i) :
    toNat (addLoop a b n i carry acc) + toNatPrefix a i + toNatPrefix b i =
      toNat acc + carry.toNat * (2 ^ 64) ^ i + toNatPrefix a n + toNatPrefix b n := by
  induction hd : n - i generalizing i carry acc with
  | zero =>
    have hin : i = n := by omega
    subst hin
    unfold addLoop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    cases carry
    · simp
    · simp only [↓reduceIte, toNat_push, hsz]
      have h1 : (1 : UInt64).toNat = 1 := rfl
      simp [h1]
  | succ d ih =>
    have hlt : i < n := by omega
    unfold addLoop
    simp only [hlt, ↓reduceDIte]
    have hspec := addCarry64_spec (getLimb a i) (getLimb b i) carry
    rcases hac : addCarry64 (getLimb a i) (getLimb b i) carry with ⟨lo, c'⟩
    rw [hac] at hspec
    dsimp only at hspec ⊢
    have hih := ih (i + 1) c' (acc.push lo) (by omega) (by simp [hsz]) (by omega)
    rw [toNat_push, hsz, toNatPrefix_succ a i, toNatPrefix_succ b i, Nat.pow_succ (2 ^ 64) i] at hih
    have hmul : (lo.toNat + c'.toNat * 2 ^ 64) * (2 ^ 64) ^ i =
        ((getLimb a i).toNat + (getLimb b i).toNat + carry.toNat) * (2 ^ 64) ^ i := by
      rw [hspec]
    have h1 : c'.toNat * ((2 ^ 64) ^ i * 2 ^ 64) = (c'.toNat * 2 ^ 64) * (2 ^ 64) ^ i := by
      rw [Nat.mul_comm ((2 ^ 64) ^ i) (2 ^ 64), ← Nat.mul_assoc]
    rw [h1] at hih
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul] at hmul
    omega

theorem wf_add (a b : Array UInt64) : WF (add a b) :=
  wf_normalize _

theorem toNat_add (a b : Array UInt64) : toNat (add a b) = toNat a + toNat b := by
  unfold add
  rw [toNat_normalize]
  let n := if a.size ≤ b.size then b.size else a.size
  have h := toNat_addLoop a b n 0 false (Array.mkEmpty (n + 1)) (Nat.zero_le _) (by simp)
  simp only [toNatPrefix_zero, toNat_mkEmpty, Bool.toNat_false, Nat.zero_mul, Nat.add_zero,
    Nat.zero_add] at h
  have hA : toNatPrefix a n = toNat a := toNatPrefix_eq_toNat_of_le a (by dsimp [n]; split <;> omega)
  have hB : toNatPrefix b n = toNat b := toNatPrefix_eq_toNat_of_le b (by dsimp [n]; split <;> omega)
  rw [hA, hB] at h
  exact h

/-! ### Truncating Subtraction (`subRaw`, `sub`) and Predecessor (`pred`) -/

theorem toNat_subLoop (a b : Array UInt64) (n i : Nat) (borrow : Bool) (acc : Array UInt64)
    (hi : i ≤ n) (hsz : acc.size = i) :
    let res := subLoop a b n i borrow acc
    res.1.size = n ∧
    toNat res.1 + toNatPrefix b n + borrow.toNat * (2 ^ 64) ^ i + toNatPrefix a i =
      toNat acc + toNatPrefix a n + res.2.toNat * (2 ^ 64) ^ n + toNatPrefix b i := by
  induction hd : n - i generalizing i borrow acc with
  | zero =>
    have hin : i = n := by omega
    subst hin
    unfold subLoop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    exact ⟨hsz, by omega⟩
  | succ d ih =>
    have hlt : i < n := by omega
    unfold subLoop
    simp only [hlt, ↓reduceDIte]
    have hspec := subBorrow64_spec (getLimb a i) (getLimb b i) borrow
    rcases hsb : subBorrow64 (getLimb a i) (getLimb b i) borrow with ⟨lo, b'⟩
    rw [hsb] at hspec
    dsimp only at hspec ⊢
    have ⟨hsz', heq⟩ := ih (i + 1) b' (acc.push lo) (by omega) (by simp [hsz]) (by omega)
    refine ⟨hsz', ?_⟩
    rw [toNat_push, hsz, toNatPrefix_succ a i, toNatPrefix_succ b i, Nat.pow_succ (2 ^ 64) i] at heq
    have hmul : (lo.toNat + (getLimb b i).toNat + borrow.toNat) * (2 ^ 64) ^ i =
        ((getLimb a i).toNat + b'.toNat * 2 ^ 64) * (2 ^ 64) ^ i := by
      rw [hspec]
    have h1 : b'.toNat * ((2 ^ 64) ^ i * 2 ^ 64) = (b'.toNat * 2 ^ 64) * (2 ^ 64) ^ i := by
      rw [Nat.mul_comm ((2 ^ 64) ^ i) (2 ^ 64), ← Nat.mul_assoc]
    rw [h1] at heq
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul] at hmul
    omega

theorem wf_subRaw (a b : Array UInt64) : WF (subRaw a b) := by
  unfold subRaw
  dsimp only
  cases (subLoop a b (if a.size ≤ b.size then b.size else a.size) 0 false
    (Array.mkEmpty (if a.size ≤ b.size then b.size else a.size))).2
  · exact wf_normalize _
  · exact Or.inl rfl

theorem toNat_subRaw (a b : Array UInt64) : toNat (subRaw a b) = toNat a - toNat b := by
  unfold subRaw
  dsimp only
  let n := if a.size ≤ b.size then b.size else a.size
  have ⟨hsz, heq⟩ := toNat_subLoop a b n 0 false (Array.mkEmpty n) (Nat.zero_le _) (by simp)
  rcases hloop : subLoop a b n 0 false (Array.mkEmpty n) with ⟨acc, borrow⟩
  rw [hloop] at hsz heq
  dsimp only at hsz heq ⊢
  simp only [toNatPrefix_zero, toNat_mkEmpty, Bool.toNat_false, Nat.zero_mul, Nat.add_zero,
    Nat.zero_add] at heq
  have hA : toNatPrefix a n = toNat a := toNatPrefix_eq_toNat_of_le a (by dsimp [n]; split <;> omega)
  have hB : toNatPrefix b n = toNat b := toNatPrefix_eq_toNat_of_le b (by dsimp [n]; split <;> omega)
  rw [hA, hB] at heq
  cases borrow
  · simp only [Bool.false_eq_true, ↓reduceIte, toNat_normalize]
    simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at heq
    omega
  · simp only [↓reduceIte, toNat_empty]
    simp only [Bool.toNat_true, Nat.one_mul] at heq
    have hlt : toNat acc < (2 ^ 64) ^ n := by rw [← hsz]; exact toNat_lt acc
    omega

theorem wf_sub (a b : Array UInt64) : WF (sub a b) := by
  unfold sub
  cases cmp a b
  · exact Or.inl rfl
  · exact Or.inl rfl
  · dsimp only
    split
    · exact Or.inl rfl
    · exact wf_normalize _

theorem toNat_sub {a b : Array UInt64} (ha : WF a) (hb : WF b) :
    toNat (sub a b) = toNat a - toNat b := by
  unfold sub
  have hcmp := cmp_spec ha hb
  cases h : cmp a b
  · rw [h] at hcmp
    simp only [compare, compareOfLessAndEq] at hcmp
    by_cases hlt : toNat a < toNat b
    · simp; omega
    · by_cases heq : toNat a = toNat b <;> simp [hlt, heq] at hcmp
  · rw [h] at hcmp
    simp only [compare, compareOfLessAndEq] at hcmp
    by_cases hlt : toNat a < toNat b
    · simp [hlt] at hcmp
    · by_cases heq : toNat a = toNat b
      · simp; omega
      · simp [hlt, heq] at hcmp
  · have hgt : toNat b < toNat a := by
      rw [h] at hcmp
      simp only [compare, compareOfLessAndEq] at hcmp
      by_cases hlt : toNat a < toNat b
      · simp [hlt] at hcmp
      · by_cases heq : toNat a = toNat b
        · simp [heq] at hcmp
        · omega
    have hszle : b.size ≤ a.size := by
      apply Classical.byContradiction; intro hlt
      have h1 : toNat a < (2 ^ 64) ^ a.size := toNat_lt a
      have h2 : (2 ^ 64) ^ (b.size - 1) ≤ toNat b := toNat_ge_top b hb (by omega)
      have h3 : (2 ^ 64) ^ a.size ≤ (2 ^ 64) ^ (b.size - 1) :=
        Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
      omega
    have ⟨hsz, heq⟩ := toNat_subLoop a b a.size 0 false (Array.mkEmpty a.size) (Nat.zero_le _) (by simp)
    rcases hloop : subLoop a b a.size 0 false (Array.mkEmpty a.size) with ⟨acc, borrow⟩
    rw [hloop] at hsz heq
    dsimp only at hsz heq ⊢
    simp only [toNatPrefix_zero, toNat_mkEmpty, Bool.toNat_false, Nat.zero_mul, Nat.add_zero,
      Nat.zero_add] at heq
    have hA : toNatPrefix a a.size = toNat a := rfl
    have hB : toNatPrefix b a.size = toNat b := toNatPrefix_eq_toNat_of_le b hszle
    rw [hA, hB] at heq
    cases borrow
    · simp only [Bool.false_eq_true, ↓reduceIte, toNat_normalize]
      simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at heq
      omega
    · simp only [Bool.toNat_true, Nat.one_mul] at heq
      have hlt : toNat acc < (2 ^ 64) ^ a.size := by rw [← hsz]; exact toNat_lt acc
      omega

theorem wf_predLoop (a : Array UInt64) (i : Nat) : WF (predLoop a i) := by
  induction hd : a.size - i generalizing a i with
  | zero =>
    unfold predLoop
    have hge : ¬ i < a.size := by omega
    simp only [hge, ↓reduceDIte]
    exact Or.inl rfl
  | succ d ih =>
    unfold predLoop
    have hlt : i < a.size := by omega
    simp only [hlt, ↓reduceDIte]
    split
    · exact ih (a.set i maxWord64) (i + 1) (by simp; omega)
    · exact wf_normalize _

theorem wf_pred (a : Array UInt64) : WF (pred a) := by
  unfold pred
  split
  · exact Or.inl rfl
  · exact wf_predLoop a 0

theorem toNat_predLoop (a : Array UInt64) (i : Nat)
    (hex : ∃ k, i ≤ k ∧ k < a.size ∧ getLimb a k ≠ 0) :
    toNat (predLoop a i) + (2 ^ 64) ^ i = toNat a := by
  induction hd : a.size - i generalizing a i with
  | zero =>
    rcases hex with ⟨k, h1, h2, _⟩
    omega
  | succ d ih =>
    have hlt : i < a.size := by omega
    unfold predLoop
    simp only [hlt, ↓reduceDIte]
    split
    · rename_i hz
      have h0 : a[i] = 0 := eq_of_beq hz
      have hset : a.set i maxWord64 = setLimb a i maxWord64 := by simp [setLimb, hlt]
      have hex' : ∃ k, i + 1 ≤ k ∧ k < (a.set i maxWord64).size ∧ getLimb (a.set i maxWord64) k ≠ 0 := by
        rcases hex with ⟨k, h1, h2, hne⟩
        have hki : k ≠ i := by
          intro heq; subst heq; rw [getLimb_lt hlt, h0] at hne; exact hne rfl
        refine ⟨k, by omega, by simp [h2], ?_⟩
        rw [hset, getLimb_setLimb a i maxWord64 hlt k]
        simp [hki, hne]
      have hih := ih (a.set i maxWord64) (i + 1) hex' (by simp; omega)
      have hto : toNat (a.set i maxWord64) = toNat a + (2 ^ 64 - 1) * (2 ^ 64) ^ i := by
        rw [hset, toNat_setLimb_of_zero a i maxWord64 hlt (by rw [getLimb_lt hlt, h0]),
            maxWord64_toNat]
      rw [hto, Nat.pow_succ (2 ^ 64) i] at hih
      have hsplit : (2 ^ 64) ^ i * 2 ^ 64 = (2 ^ 64 - 1) * (2 ^ 64) ^ i + (2 ^ 64) ^ i := by
        have hpos : 1 ≤ 2 ^ 64 := Nat.two_pow_pos 64
        calc (2 ^ 64) ^ i * 2 ^ 64 = 2 ^ 64 * (2 ^ 64) ^ i := Nat.mul_comm _ _
          _ = ((2 ^ 64 - 1) + 1) * (2 ^ 64) ^ i := by rw [Nat.sub_add_cancel hpos]
          _ = (2 ^ 64 - 1) * (2 ^ 64) ^ i + (2 ^ 64) ^ i := by rw [Nat.add_mul, Nat.one_mul]
      omega
    · rename_i hne
      rw [toNat_normalize]
      have hset : a.set i (a[i] - 1) = setLimb a i (a[i] - 1) := by simp [setLimb, hlt]
      rw [hset]
      have hto := toNat_setLimb a i (a[i] - 1) hlt
      rw [getLimb_lt hlt] at hto
      have hpos : 1 ≤ a[i].toNat := by
        have : a[i].toNat ≠ 0 := fun h0 =>
          hne (by have : a[i] = 0 := UInt64.toNat_inj.mp (by simpa using h0); simp [this])
        omega
      have hsub : (a[i] - 1).toNat = a[i].toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hpos)]
        rfl
      rw [hsub] at hto
      have hsplit : a[i].toNat * (2 ^ 64) ^ i = (a[i].toNat - 1) * (2 ^ 64) ^ i + (2 ^ 64) ^ i := by
        calc a[i].toNat * (2 ^ 64) ^ i = ((a[i].toNat - 1) + 1) * (2 ^ 64) ^ i := by
              rw [Nat.sub_add_cancel hpos]
          _ = (a[i].toNat - 1) * (2 ^ 64) ^ i + (2 ^ 64) ^ i := by rw [Nat.add_mul, Nat.one_mul]
      omega

theorem toNat_pred {a : Array UInt64} (ha : WF a) : toNat (pred a) = toNat a - 1 := by
  unfold pred
  by_cases h0 : a.size = 0
  · simp [h0, toNat]
  · have h0b : (a.size == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    have hex : ∃ k, 0 ≤ k ∧ k < a.size ∧ getLimb a k ≠ 0 := by
      rcases ha with hz | hne
      · omega
      · exact ⟨a.size - 1, Nat.zero_le _, by omega, hne⟩
    have h := toNat_predLoop a 0 hex
    simp only [Nat.pow_zero] at h
    omega

/-! ### Bitwise Operations (`land`, `lor`, `xor`) -/

private theorem getLimb_landLoop (a b : Array UInt64) (n i : Nat) (acc : Array UInt64)
    (hi : i ≤ n) (hsz : acc.size = i) (j : Nat) :
    getLimb (landLoop a b n i acc) j =
      if j < i then getLimb acc j
      else if j < n then getLimb a j &&& getLimb b j
      else 0 := by
  induction hd : n - i generalizing i acc with
  | zero =>
    have hin : i = n := by omega
    subst hin
    unfold landLoop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    split
    · rfl
    · rename_i hge; exact getLimb_ge (by omega)
  | succ d ih =>
    have hlt : i < n := by omega
    unfold landLoop
    simp only [hlt, ↓reduceDIte]
    rw [ih (i + 1) _ (by omega) (by simp [hsz]) (by omega)]
    by_cases h1 : j < i
    · have h2 : j < i + 1 := by omega
      have hne : j ≠ acc.size := by omega
      simp [h1, h2, getLimb_push, hne]
    · by_cases h2 : j = i
      · subst h2
        simp [hsz, hlt, getLimb_push]
      · have h3 : ¬ j < i + 1 := by omega
        simp [h1, h3]

private theorem getLimb_lorLoop (a b : Array UInt64) (n i : Nat) (acc : Array UInt64)
    (hi : i ≤ n) (hsz : acc.size = i) (j : Nat) :
    getLimb (lorLoop a b n i acc) j =
      if j < i then getLimb acc j
      else if j < n then getLimb a j ||| getLimb b j
      else 0 := by
  induction hd : n - i generalizing i acc with
  | zero =>
    have hin : i = n := by omega
    subst hin
    unfold lorLoop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    split
    · rfl
    · rename_i hge; exact getLimb_ge (by omega)
  | succ d ih =>
    have hlt : i < n := by omega
    unfold lorLoop
    simp only [hlt, ↓reduceDIte]
    rw [ih (i + 1) _ (by omega) (by simp [hsz]) (by omega)]
    by_cases h1 : j < i
    · have h2 : j < i + 1 := by omega
      have hne : j ≠ acc.size := by omega
      simp [h1, h2, getLimb_push, hne]
    · by_cases h2 : j = i
      · subst h2
        simp [hsz, hlt, getLimb_push]
      · have h3 : ¬ j < i + 1 := by omega
        simp [h1, h3]

private theorem getLimb_xorLoop (a b : Array UInt64) (n i : Nat) (acc : Array UInt64)
    (hi : i ≤ n) (hsz : acc.size = i) (j : Nat) :
    getLimb (xorLoop a b n i acc) j =
      if j < i then getLimb acc j
      else if j < n then getLimb a j ^^^ getLimb b j
      else 0 := by
  induction hd : n - i generalizing i acc with
  | zero =>
    have hin : i = n := by omega
    subst hin
    unfold xorLoop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    split
    · rfl
    · rename_i hge; exact getLimb_ge (by omega)
  | succ d ih =>
    have hlt : i < n := by omega
    unfold xorLoop
    simp only [hlt, ↓reduceDIte]
    rw [ih (i + 1) _ (by omega) (by simp [hsz]) (by omega)]
    by_cases h1 : j < i
    · have h2 : j < i + 1 := by omega
      have hne : j ≠ acc.size := by omega
      simp [h1, h2, getLimb_push, hne]
    · by_cases h2 : j = i
      · subst h2
        simp [hsz, hlt, getLimb_push]
      · have h3 : ¬ j < i + 1 := by omega
        simp [h1, h3]

theorem wf_land (a b : Array UInt64) : WF (land a b) := wf_normalize _

theorem toNat_land (a b : Array UInt64) : toNat (land a b) = toNat a &&& toNat b := by
  unfold land
  dsimp only
  rw [toNat_normalize]
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [testBit_toNat, Nat.testBit_and, testBit_toNat, testBit_toNat]
  let n := if a.size ≤ b.size then a.size else b.size
  rw [getLimb_landLoop a b n 0 _ (Nat.zero_le _) (by simp)]
  simp only [Nat.not_lt_zero, ↓reduceIte]
  by_cases hlt : bit / 64 < n
  · simp only [hlt, ↓reduceIte, UInt64.toNat_and, Nat.testBit_and]
  · simp only [hlt, ↓reduceIte]
    have hor : a.size ≤ bit / 64 ∨ b.size ≤ bit / 64 := by
      dsimp [n] at hlt; split at hlt <;> omega
    rcases hor with ha | hb
    · rw [getLimb_ge ha]; simp
    · rw [getLimb_ge hb]; simp

theorem wf_lor (a b : Array UInt64) : WF (lor a b) := wf_normalize _

theorem toNat_lor (a b : Array UInt64) : toNat (lor a b) = toNat a ||| toNat b := by
  unfold lor
  dsimp only
  rw [toNat_normalize]
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [testBit_toNat, Nat.testBit_or, testBit_toNat, testBit_toNat]
  let n := if a.size ≤ b.size then b.size else a.size
  rw [getLimb_lorLoop a b n 0 _ (Nat.zero_le _) (by simp)]
  simp only [Nat.not_lt_zero, ↓reduceIte]
  by_cases hlt : bit / 64 < n
  · simp only [hlt, ↓reduceIte, UInt64.toNat_or, Nat.testBit_or]
  · simp only [hlt, ↓reduceIte]
    have ha : a.size ≤ bit / 64 := by dsimp [n] at hlt; split at hlt <;> omega
    have hb : b.size ≤ bit / 64 := by dsimp [n] at hlt; split at hlt <;> omega
    rw [getLimb_ge ha, getLimb_ge hb]; simp

theorem wf_xor (a b : Array UInt64) : WF (xor a b) := wf_normalize _

theorem toNat_xor (a b : Array UInt64) : toNat (xor a b) = toNat a ^^^ toNat b := by
  unfold xor
  dsimp only
  rw [toNat_normalize]
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [testBit_toNat, Nat.testBit_xor, testBit_toNat, testBit_toNat]
  let n := if a.size ≤ b.size then b.size else a.size
  rw [getLimb_xorLoop a b n 0 _ (Nat.zero_le _) (by simp)]
  simp only [Nat.not_lt_zero, ↓reduceIte]
  by_cases hlt : bit / 64 < n
  · simp only [hlt, ↓reduceIte, UInt64.toNat_xor, Nat.testBit_xor]
  · simp only [hlt, ↓reduceIte]
    have ha : a.size ≤ bit / 64 := by dsimp [n] at hlt; split at hlt <;> omega
    have hb : b.size ≤ bit / 64 := by dsimp [n] at hlt; split at hlt <;> omega
    rw [getLimb_ge ha, getLimb_ge hb]; simp

/-! ### Shifts (`shiftLimbs`, `shiftLeft`, `shiftRight`) -/

private theorem getLimb_copyAppendLoop (a : Array UInt64) (i : Nat) (acc : Array UInt64)
    (hi : i ≤ a.size) (j : Nat) :
    getLimb (copyAppendLoop a i acc) j =
      if j < acc.size then getLimb acc j
      else if j < acc.size + (a.size - i) then getLimb a (i + (j - acc.size))
      else 0 := by
  induction hd : a.size - i generalizing i acc with
  | zero =>
    have hge : ¬ i < a.size := by omega
    unfold copyAppendLoop
    simp only [hge, ↓reduceDIte, Nat.add_zero]
    split
    · rfl
    · rename_i hj; exact getLimb_ge (by omega)
  | succ d ih =>
    have hlt : i < a.size := by omega
    unfold copyAppendLoop
    simp only [hlt, ↓reduceDIte]
    rw [ih (i + 1) (acc.push a[i]) (by omega) (by omega)]
    simp only [Array.size_push]
    by_cases h1 : j < acc.size
    · have h2 : j < acc.size + 1 := by omega
      have hne : j ≠ acc.size := by omega
      simp [h1, h2, getLimb_push, hne]
    · by_cases h2 : j = acc.size
      · subst h2
        have hlt1 : acc.size < acc.size + 1 := by omega
        have hlt2 : acc.size < acc.size + (d + 1) := by omega
        simp only [h1, hlt1, hlt2, ↓reduceIte, getLimb_push, Nat.sub_self, Nat.add_zero, getLimb_lt hlt]
      · have h3 : ¬ j < acc.size + 1 := by omega
        have h4 : (j < acc.size + 1 + d) ↔ (j < acc.size + (d + 1)) := by omega
        simp only [h1, h3, ↓reduceIte, h4]
        split
        · congr 1; omega
        · rfl

theorem toNat_copyAppendLoop_zeros (a : Array UInt64) (k cap : Nat) :
    toNat (copyAppendLoop a 0 (mkZerosLoop k (Array.mkEmpty cap))) =
      toNat a * (2 ^ 64) ^ k := by
  have hpow : (2 ^ 64) ^ k = 2 ^ (64 * k) := by rw [← Nat.pow_mul]
  rw [hpow, ← Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [testBit_toNat, Nat.testBit_shiftLeft, testBit_toNat]
  rw [getLimb_copyAppendLoop a 0 _ (Nat.zero_le _)]
  rw [size_mkZerosLoop, size_mkEmpty, Nat.zero_add, Nat.sub_zero, Nat.zero_add]
  by_cases hlt : bit < 64 * k
  · have hdiv : bit / 64 < k := by omega
    have hge : ¬ 64 * k ≤ bit := by omega
    simp only [hdiv, hge, ↓reduceIte, getLimb_mkZerosLoop, size_mkEmpty, Nat.not_lt_zero]
    simp
  · have hge : 64 * k ≤ bit := by omega
    have hdiv : ¬ bit / 64 < k := by omega
    have hdivsub : (bit - 64 * k) / 64 = bit / 64 - k := by omega
    have hmodsub : (bit - 64 * k) % 64 = bit % 64 := by omega
    simp only [hge, hdiv, ↓reduceIte, hdivsub, hmodsub, decide_true, Bool.true_and]
    by_cases hin : bit / 64 < k + a.size
    · simp [hin]
    · simp only [hin, ↓reduceIte]
      rw [getLimb_ge (by omega)]

theorem wf_shiftLimbs (a : Array UInt64) (k : Nat) : WF (shiftLimbs a k) := by
  unfold shiftLimbs
  dsimp only
  split
  · exact Or.inl rfl
  · split
    · exact wf_normalize a
    · exact wf_normalize _

theorem toNat_shiftLimbs (a : Array UInt64) (k : Nat) :
    toNat (shiftLimbs a k) = toNat a * (2 ^ 64) ^ k := by
  unfold shiftLimbs
  dsimp only
  split
  · rename_i hz
    have hsz : (normalize a).size = 0 := eq_of_beq hz
    have ha0 : toNat a = 0 := by rw [← toNat_normalize, toNat, hsz]; rfl
    simp [ha0]
  · split
    · rename_i hk0
      have hk : k = 0 := eq_of_beq hk0
      subst hk
      simp [toNat_normalize]
    · rw [toNat_normalize, toNat_copyAppendLoop_zeros, toNat_normalize]

private theorem uint64_shift_split_lemma (v carry : UInt64) (bitShift : Nat)
    (hb1 : 0 < bitShift) (hb2 : bitShift < 64) (hcar : carry.toNat < 2 ^ bitShift) :
    let b := UInt64.ofNat bitShift
    let invB := (64 : UInt64) - b
    (((v <<< b) ||| carry).toNat) + (v >>> invB).toNat * 2 ^ 64 =
      v.toNat * 2 ^ bitShift + carry.toNat := by
  dsimp only
  have hbN : (UInt64.ofNat bitShift).toNat = bitShift := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hinvN : ((64 : UInt64) - UInt64.ofNat bitShift).toNat = 64 - bitShift := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hbN]; exact Nat.le_of_lt hb2)]
    rw [hbN]; rfl
  have hsl : (v <<< UInt64.ofNat bitShift).toNat = (v.toNat * 2 ^ bitShift) % 2 ^ 64 := by
    rw [UInt64.toNat_shiftLeft, hbN, Nat.mod_eq_of_lt hb2, Nat.shiftLeft_eq]
  have hsr : (v >>> ((64 : UInt64) - UInt64.ofNat bitShift)).toNat = v.toNat / 2 ^ (64 - bitShift) := by
    rw [UInt64.toNat_shiftRight, hinvN, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  have hdiv : (v.toNat * 2 ^ bitShift) / 2 ^ 64 = v.toNat / 2 ^ (64 - bitShift) := by
    have h64 : 2 ^ 64 = 2 ^ (64 - bitShift) * 2 ^ bitShift := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hb2)]
    rw [h64, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos bitShift)]
  have hdisj : ((v <<< UInt64.ofNat bitShift) ||| carry).toNat =
      (v <<< UInt64.ofNat bitShift).toNat + carry.toNat := by
    rw [UInt64.toNat_or, hsl]
    have hdvd : 2 ^ bitShift ∣ (v.toNat * 2 ^ bitShift) % 2 ^ 64 := by
      have h64 : 2 ^ bitShift ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (Nat.le_of_lt hb2)
      exact (Nat.dvd_mod_iff h64).mpr (Nat.dvd_mul_left _ _)
    rcases hdvd with ⟨q, hq⟩
    rw [hq, Nat.mul_comm (2 ^ bitShift) q, Nat.add_comm (q * 2 ^ bitShift) carry.toNat,
        Nat.or_comm]
    apply Nat.eq_of_testBit_eq
    intro bit
    rw [Nat.testBit_or]
    have hmul_bit : (q * 2 ^ bitShift).testBit bit =
        if bit < bitShift then false else q.testBit (bit - bitShift) := by
      rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
      by_cases hlt : bit < bitShift
      · have hge : ¬ bitShift ≤ bit := by omega
        simp [hlt, hge]
      · have hge : bitShift ≤ bit := by omega
        simp [hlt, hge]
    rw [hmul_bit]
    by_cases hlt : bit < bitShift
    · simp only [hlt, ↓reduceIte, Bool.or_false, Nat.testBit_eq_decide_div_mod_eq]
      have hs : 2 ^ bitShift = 2 ^ bit * 2 ^ (bitShift - bit) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
      have hd2 : 2 ∣ 2 ^ (bitShift - bit) := by
        have : 2 ^ (bitShift - bit) = 2 * 2 ^ (bitShift - bit - 1) := by
          conv => lhs; rw [show bitShift - bit = (bitShift - bit - 1) + 1 by omega]
          rw [Nat.pow_succ, Nat.mul_comm]
        exact ⟨2 ^ (bitShift - bit - 1), this⟩
      rcases hd2 with ⟨r, hr⟩
      rw [hs, ← Nat.mul_assoc, Nat.mul_comm q (2 ^ bit), Nat.mul_assoc (2 ^ bit) q,
          Nat.mul_comm (2 ^ bit), Nat.add_mul_div_right _ _ (Nat.two_pow_pos bit),
          hr, ← Nat.mul_assoc, Nat.mul_comm q 2, Nat.mul_assoc 2 q r, Nat.add_mul_mod_self_left]
    · simp only [hlt, ↓reduceIte]
      have hge : bitShift ≤ bit := by omega
      have hcar0 : carry.toNat.testBit bit = false :=
        testBit_eq_false_of_lt_pow (Nat.lt_of_lt_of_le hcar (Nat.pow_le_pow_right (by decide) hge))
      rw [hcar0, Bool.false_or, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hbit : 2 ^ bit = 2 ^ bitShift * 2 ^ (bit - bitShift) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
      rw [hbit, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos bitShift),
          Nat.div_eq_of_lt hcar, Nat.zero_add]
  rw [hdisj, hsl, hsr, ← hdiv]
  have hdm := Nat.div_add_mod (v.toNat * 2 ^ bitShift) (2 ^ 64)
  omega

private theorem toNat_shiftLeftBitLoop (a : Array UInt64) (bitShift i : Nat)
    (hb1 : 0 < bitShift) (hb2 : bitShift < 64) (hi : i ≤ a.size)
    (carry : UInt64) (hcar : carry.toNat < 2 ^ bitShift)
    (acc : Array UInt64) (k : Nat) (hsz : acc.size = k + i) :
    let b := UInt64.ofNat bitShift
    let invB := (64 : UInt64) - b
    toNat (shiftLeftBitLoop a b invB i carry acc) + toNatPrefix a i * 2 ^ bitShift * (2 ^ 64) ^ k =
      toNat acc + carry.toNat * (2 ^ 64) ^ (k + i) + toNat a * 2 ^ bitShift * (2 ^ 64) ^ k := by
  induction hd : a.size - i generalizing i carry acc with
  | zero =>
    have hia : i = a.size := by omega
    subst hia
    unfold shiftLeftBitLoop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    have hpref : toNatPrefix a a.size = toNat a := rfl
    split
    · rename_i hc0
      have hc : carry = 0 := eq_of_beq hc0
      subst hc
      rw [hpref]; simp
    · rw [toNat_push, hsz, hpref]
  | succ d ih =>
    have hlt : i < a.size := by omega
    unfold shiftLeftBitLoop
    simp only [hlt, ↓reduceDIte]
    have hinvN : ((64 : UInt64) - UInt64.ofNat bitShift).toNat = 64 - bitShift := by
      have hbN : (UInt64.ofNat bitShift).toNat = bitShift := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hbN]; exact Nat.le_of_lt hb2)]
      rw [hbN]; rfl
    have hcar' : (a[i] >>> ((64 : UInt64) - UInt64.ofNat bitShift)).toNat < 2 ^ bitShift := by
      rw [UInt64.toNat_shiftRight, hinvN, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hb2)]
      exact uint64_toNat_lt a[i]
    have hih := ih (i + 1) (by omega) _ hcar' (acc.push ((a[i] <<< UInt64.ofNat bitShift) ||| carry))
      (by rw [Array.size_push, hsz]; omega) (by omega)
    have hsplit := uint64_shift_split_lemma a[i] carry bitShift hb1 hb2 hcar
    dsimp only at hsplit
    rw [toNat_push, hsz, toNatPrefix_succ a i, getLimb_lt hlt] at hih
    have hpow1 : (2 ^ 64) ^ (k + (i + 1)) = (2 ^ 64) ^ (k + i) * 2 ^ 64 := by
      rw [← Nat.add_assoc, Nat.pow_succ (2 ^ 64)]
    have hpow2 : (2 ^ 64) ^ i * (2 ^ 64) ^ k = (2 ^ 64) ^ (k + i) := by
      rw [← Nat.pow_add, Nat.add_comm]
    rw [hpow1] at hih
    have hstep : (((a[i] <<< UInt64.ofNat bitShift) ||| carry).toNat +
        (a[i] >>> ((64 : UInt64) - UInt64.ofNat bitShift)).toNat * 2 ^ 64) * (2 ^ 64) ^ (k + i) =
        (a[i].toNat * 2 ^ bitShift + carry.toNat) * (2 ^ 64) ^ (k + i) := by
      rw [hsplit]
    have hr1 : (a[i] >>> ((64 : UInt64) - UInt64.ofNat bitShift)).toNat * ((2 ^ 64) ^ (k + i) * 2 ^ 64) =
        ((a[i] >>> ((64 : UInt64) - UInt64.ofNat bitShift)).toNat * 2 ^ 64) * (2 ^ 64) ^ (k + i) := by
      rw [Nat.mul_comm ((2 ^ 64) ^ (k + i)) (2 ^ 64), ← Nat.mul_assoc]
    have hr2 : (toNatPrefix a i + a[i].toNat * (2 ^ 64) ^ i) * 2 ^ bitShift * (2 ^ 64) ^ k =
        toNatPrefix a i * 2 ^ bitShift * (2 ^ 64) ^ k +
        (a[i].toNat * 2 ^ bitShift) * (2 ^ 64) ^ (k + i) := by
      rw [Nat.add_mul, Nat.add_mul]
      congr 1
      calc a[i].toNat * (2 ^ 64) ^ i * 2 ^ bitShift * (2 ^ 64) ^ k
          = a[i].toNat * ((2 ^ 64) ^ i * 2 ^ bitShift) * (2 ^ 64) ^ k := by
            rw [Nat.mul_assoc a[i].toNat]
        _ = a[i].toNat * (2 ^ bitShift * (2 ^ 64) ^ i) * (2 ^ 64) ^ k := by
            rw [Nat.mul_comm ((2 ^ 64) ^ i) (2 ^ bitShift)]
        _ = a[i].toNat * 2 ^ bitShift * ((2 ^ 64) ^ i * (2 ^ 64) ^ k) := by
            rw [← Nat.mul_assoc a[i].toNat, Nat.mul_assoc (a[i].toNat * 2 ^ bitShift)]
        _ = a[i].toNat * 2 ^ bitShift * (2 ^ 64) ^ (k + i) := by rw [hpow2]
    rw [hr1, hr2] at hih
    rw [Nat.add_mul, Nat.add_mul] at hstep
    omega

theorem wf_shiftLeft (a : Array UInt64) (s : Nat) : WF (shiftLeft a s) := by
  unfold shiftLeft
  dsimp only
  split
  · exact Or.inl rfl
  · split
    · exact wf_normalize a
    · split <;> exact wf_normalize _

theorem toNat_shiftLeft (a : Array UInt64) (s : Nat) :
    toNat (shiftLeft a s) = toNat a <<< s := by
  rw [Nat.shiftLeft_eq]
  unfold shiftLeft
  dsimp only
  split
  · rename_i hz
    have hsz : (normalize a).size = 0 := eq_of_beq hz
    have ha0 : toNat a = 0 := by rw [← toNat_normalize, toNat, hsz]; rfl
    simp [ha0]
  · split
    · rename_i hs0
      have hs : s = 0 := eq_of_beq hs0
      subst hs
      simp [toNat_normalize]
    · split
      · rename_i hbit0
        have hb0 : s % 64 = 0 := eq_of_beq hbit0
        rw [toNat_normalize, toNat_copyAppendLoop_zeros, toNat_normalize]
        have hs : s = 64 * (s / 64) := by omega
        rw [← Nat.pow_mul, ← hs]
      · rename_i hbitne
        have hb1 : 0 < s % 64 := by
          have : s % 64 ≠ 0 := fun h => hbitne (by simp [h])
          omega
        have hb2 : s % 64 < 64 := Nat.mod_lt s (by decide)
        rw [toNat_normalize]
        have hcar0 : (0 : UInt64).toNat < 2 ^ (s % 64) := Nat.two_pow_pos _
        have hacc0 : toNat (mkZerosLoop (s / 64) (Array.mkEmpty (s / 64 + (normalize a).size + 1))) = 0 := by
          rw [← toNat_empty]
          apply toNat_eq_of_getLimb
          intro j
          simp [getLimb_mkZerosLoop]
        have hsz0 : (mkZerosLoop (s / 64) (Array.mkEmpty (s / 64 + (normalize a).size + 1))).size =
            s / 64 + 0 := by
          rw [size_mkZerosLoop]; simp
        have h := toNat_shiftLeftBitLoop (normalize a) (s % 64) 0 hb1 hb2 (Nat.zero_le _)
          0 hcar0 _ (s / 64) hsz0
        dsimp only at h
        rw [toNatPrefix_zero, hacc0, toNat_normalize] at h
        have h0 : (0 : UInt64).toNat = 0 := rfl
        rw [h0] at h
        simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add] at h
        rw [h, Nat.mul_assoc, ← Nat.pow_mul, ← Nat.pow_add]
        have hs : s % 64 + 64 * (s / 64) = s := by omega
        rw [hs]

theorem toNat_shiftLeft_mul (a : Array UInt64) (s : Nat) :
    toNat (shiftLeft a s) = toNat a * 2 ^ s := by
  rw [toNat_shiftLeft, Nat.shiftLeft_eq]

private theorem getLimb_shiftRightWordLoop (a : Array UInt64) (wordShift outLen i : Nat)
    (acc : Array UInt64) (hi : i ≤ outLen) (hsz : acc.size = i) (j : Nat) :
    getLimb (shiftRightWordLoop a wordShift outLen i acc) j =
      if j < i then getLimb acc j
      else if j < outLen then getLimb a (wordShift + j)
      else 0 := by
  induction hd : outLen - i generalizing i acc with
  | zero =>
    have hge : ¬ i < outLen := by omega
    unfold shiftRightWordLoop
    simp only [hge, ↓reduceDIte]
    split
    · rfl
    · rename_i hj; have hge2 : ¬ j < outLen := by omega
      simp only [hge2, ↓reduceIte]; exact getLimb_ge (by omega)
  | succ d ih =>
    have hlt : i < outLen := by omega
    unfold shiftRightWordLoop
    simp only [hlt, ↓reduceDIte]
    rw [ih (i + 1) _ (by omega) (by simp [hsz]) (by omega)]
    by_cases h1 : j < i
    · have h2 : j < i + 1 := by omega
      have hne : j ≠ acc.size := by omega
      simp [h1, h2, getLimb_push, hne]
    · by_cases h2 : j = i
      · subst h2
        simp [hsz, hlt, getLimb_push]
      · have h3 : ¬ j < i + 1 := by omega
        simp [h1, h3]

private theorem getLimb_shiftRightBitLoop (a : Array UInt64) (wordShift outLen : Nat)
    (b invB : UInt64) (i : Nat) (acc : Array UInt64)
    (hi : i ≤ outLen) (hsz : acc.size = i) (j : Nat) :
    getLimb (shiftRightBitLoop a wordShift outLen b invB i acc) j =
      if j < i then getLimb acc j
      else if j < outLen then (getLimb a (wordShift + j) >>> b) ||| (getLimb a (wordShift + j + 1) <<< invB)
      else 0 := by
  induction hd : outLen - i generalizing i acc with
  | zero =>
    have hge : ¬ i < outLen := by omega
    unfold shiftRightBitLoop
    simp only [hge, ↓reduceDIte]
    split
    · rfl
    · rename_i hj; have hge2 : ¬ j < outLen := by omega
      simp only [hge2, ↓reduceIte]; exact getLimb_ge (by omega)
  | succ d ih =>
    have hlt : i < outLen := by omega
    unfold shiftRightBitLoop
    simp only [hlt, ↓reduceDIte]
    rw [ih (i + 1) _ (by omega) (by simp [hsz]) (by omega)]
    by_cases h1 : j < i
    · have h2 : j < i + 1 := by omega
      have hne : j ≠ acc.size := by omega
      simp [h1, h2, getLimb_push, hne]
    · by_cases h2 : j = i
      · subst h2
        simp [hsz, hlt, getLimb_push]
      · have h3 : ¬ j < i + 1 := by omega
        simp [h1, h3]

theorem wf_shiftRight (a : Array UInt64) (s : Nat) : WF (shiftRight a s) := by
  unfold shiftRight
  split
  · exact wf_normalize a
  · dsimp only
    split
    · exact Or.inl rfl
    · split <;> exact wf_normalize _

theorem toNat_shiftRight (a : Array UInt64) (s : Nat) :
    toNat (shiftRight a s) = toNat a >>> s := by
  unfold shiftRight
  split
  · rename_i hs0
    have hs : s = 0 := eq_of_beq hs0
    subst hs
    simp [toNat_normalize]
  · dsimp only
    split
    · rename_i hle
      rw [toNat_empty, Nat.shiftRight_eq_div_pow]
      symm
      apply Nat.div_eq_of_lt
      have h1 : toNat a < (2 ^ 64) ^ a.size := toNat_lt a
      have h2 : (2 ^ 64) ^ a.size = 2 ^ (64 * a.size) := by rw [← Nat.pow_mul]
      have h3 : 64 * a.size ≤ s := by omega
      exact Nat.lt_of_lt_of_le (by rwa [← h2]) (Nat.pow_le_pow_right (by decide) h3)
    · rename_i hgt
      have hlt : s / 64 < a.size := by omega
      split
      · rename_i hb0
        have hbit0 : s % 64 = 0 := eq_of_beq hb0
        rw [toNat_normalize]
        apply Nat.eq_of_testBit_eq
        intro bit
        rw [testBit_toNat, Nat.testBit_shiftRight, testBit_toNat]
        rw [getLimb_shiftRightWordLoop a (s / 64) (a.size - s / 64) 0 _ (Nat.zero_le _) (by simp)]
        simp only [Nat.not_lt_zero, ↓reduceIte]
        have hdiv : (s + bit) / 64 = s / 64 + bit / 64 := by omega
        have hmod : (s + bit) % 64 = bit % 64 := by omega
        rw [hdiv, hmod]
        split
        · rfl
        · rename_i hge
          rw [getLimb_ge (by omega)]
      · rename_i hbne
        have hb1 : 0 < s % 64 := by
          have : s % 64 ≠ 0 := fun h => hbne (by simp [h])
          omega
        have hb2 : s % 64 < 64 := Nat.mod_lt s (by decide)
        rw [toNat_normalize]
        apply Nat.eq_of_testBit_eq
        intro bit
        rw [testBit_toNat, Nat.testBit_shiftRight, testBit_toNat]
        rw [getLimb_shiftRightBitLoop a (s / 64) (a.size - s / 64) _ _ 0 _ (Nat.zero_le _) (by simp)]
        simp only [Nat.not_lt_zero, ↓reduceIte]
        have hbN : (UInt64.ofNat (s % 64)).toNat = s % 64 := by
          rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        have hinvN : ((64 : UInt64) - UInt64.ofNat (s % 64)).toNat = 64 - s % 64 := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hbN]; exact Nat.le_of_lt hb2)]
          rw [hbN]; rfl
        by_cases hj : bit / 64 < a.size - s / 64
        · simp only [hj, ↓reduceIte, UInt64.toNat_or, Nat.testBit_or,
            UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, hbN, hinvN,
            Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt (show 64 - s % 64 < 64 by omega)]
          rw [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
          have hbmod : bit % 64 < 64 := Nat.mod_lt bit (by decide)
          by_cases hwrap : bit % 64 < 64 - s % 64
          · have hnotge : ¬ 64 - s % 64 ≤ bit % 64 := by omega
            have hdiv : (s + bit) / 64 = s / 64 + bit / 64 := by omega
            have hmod : (s + bit) % 64 = s % 64 + bit % 64 := by omega
            simp [hnotge, hdiv, hmod]
          · have hge : 64 - s % 64 ≤ bit % 64 := by omega
            have hdiv : (s + bit) / 64 = s / 64 + bit / 64 + 1 := by omega
            have hmod : (s + bit) % 64 = bit % 64 - (64 - s % 64) := by omega
            have hhi : (getLimb a (s / 64 + bit / 64)).toNat.testBit (s % 64 + bit % 64) = false :=
              testBit_eq_false_of_lt_pow (Nat.lt_of_lt_of_le (uint64_toNat_lt _)
                (Nat.pow_le_pow_right (by decide) (by omega)))
            simp [hbmod, hge, hdiv, hmod, hhi]
        · simp only [hj, ↓reduceIte]
          have hge : a.size ≤ (s + bit) / 64 := by omega
          rw [getLimb_ge hge]
          simp

theorem toNat_shiftRight_div (a : Array UInt64) (s : Nat) :
    toNat (shiftRight a s) = toNat a / 2 ^ s := by
  rw [toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-! ### Base-2 Logarithm (`log2`) -/

theorem log2_spec {a : Array UInt64} (ha : WF a) :
    log2 a = Nat.log2 (toNat a) := by
  unfold log2
  by_cases h0 : a.size = 0
  · simp [h0, toNat]
  · simp only [h0, ↓reduceDIte]
    have htop_ne : a[a.size - 1]'(Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos) ≠ 0 := by
      rcases ha with hz | hne
      · omega
      · rw [getLimb_lt (by omega)] at hne
        exact hne
    have ⟨hlo, hhi⟩ := clz64_spec _ htop_ne
    have hlt64 : (clz64 (a[a.size - 1]'(Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos))).toNat < 64 :=
      clz64_lt_64 _ htop_ne
    let k := (a.size - 1) * 64 + (63 - (clz64 (a[a.size - 1]'(Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos))).toNat)
    show k = Nat.log2 (toNat a)
    have hpos : toNat a ≠ 0 := by
      have := toNat_pos_of_ne_zero a ha h0
      omega
    have hlow : 2 ^ k ≤ toNat a := by
      have hge := toNat_ge_limb a (a.size - 1)
      rw [getLimb_lt (by omega)] at hge
      have hpow : (2 ^ 64) ^ (a.size - 1) = 2 ^ ((a.size - 1) * 64) := by
        rw [← Nat.pow_mul, Nat.mul_comm]
      rw [hpow] at hge
      have h1 : 2 ^ k = 2 ^ (63 - (clz64 (a[a.size - 1]'(Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos))).toNat) *
          2 ^ ((a.size - 1) * 64) := by
        rw [← Nat.pow_add, Nat.add_comm]
      rw [h1]
      exact Nat.le_trans (Nat.mul_le_mul_right _ hlo) hge
    have hhigh : toNat a < 2 ^ (k + 1) := by
      have hsz : a.size = (a.size - 1) + 1 := by omega
      have hto : toNat a = toNatPrefix a (a.size - 1) +
          (a[a.size - 1]'(Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos)).toNat *
            (2 ^ 64) ^ (a.size - 1) := by
        unfold toNat
        conv => lhs; rw [hsz]
        rw [toNatPrefix_succ, getLimb_lt (by omega)]
      have hpref : toNatPrefix a (a.size - 1) < (2 ^ 64) ^ (a.size - 1) := toNatPrefix_lt a _
      have hpow : (2 ^ 64) ^ (a.size - 1) = 2 ^ ((a.size - 1) * 64) := by
        rw [← Nat.pow_mul, Nat.mul_comm]
      have h1 : toNat a < ((a[a.size - 1]'(Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos)).toNat + 1) *
          (2 ^ 64) ^ (a.size - 1) := by
        rw [hto, Nat.add_mul, Nat.one_mul]; omega
      have h2 : (a[a.size - 1]'(Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos)).toNat + 1 ≤
          2 ^ (64 - (clz64 (a[a.size - 1]'(Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos))).toNat) := hhi
      have h3 := Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ h2)
      rw [hpow, ← Nat.pow_add] at h3
      have hexp : 64 - (clz64 (a[a.size - 1]'(Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos))).toNat +
          (a.size - 1) * 64 = k + 1 := by omega
      rw [hexp] at h3
      exact h3
    have hle : k ≤ Nat.log2 (toNat a) := (Nat.le_log2 hpos).mpr hlow
    have hlt : Nat.log2 (toNat a) < k + 1 := (Nat.log2_lt hpos).mpr hhigh
    omega

end IxCC.BigNat
