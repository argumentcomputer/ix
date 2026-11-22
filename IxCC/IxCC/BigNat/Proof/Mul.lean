import IxCC.BigNat.Mul
import IxCC.BigNat.Proof.Linear

/-! # Layer-1 Proofs for `IxCC.BigNat.Mul` (`IxCC.BigNat.Proof.Mul`)

Formal correctness and canonical normal-form preservation for:
- Schoolbook multiplication (`mulSchoolbook`)
- Dedicated 3-pass schoolbook squaring (`sqrSchoolbook`)
- Karatsuba multiplication (`mulKaratsuba`, `mul`)
- Karatsuba squaring (`sqrKaratsuba`, `sqr`)
- Left-to-right binary exponentiation (`pow`)

All theorems depend strictly on `[propext, Classical.choice, Quot.sound]`.
-/

namespace IxCC.BigNat

/-! ### Schoolbook Multiplication (`mulSchoolbook`) -/

private theorem size_mulAddRow (a_i : UInt64) (b : Array UInt64) (i j : Nat)
    (carry : UInt64) (acc : Array UInt64) :
    (mulAddRow a_i b i j carry acc).size = acc.size := by
  induction hd : b.size - j generalizing j carry acc with
  | zero =>
    unfold mulAddRow
    have hge : ¬ j < b.size := by omega
    simp [hge]
  | succ d ih =>
    unfold mulAddRow
    have hlt : j < b.size := by omega
    simp only [hlt, ↓reduceDIte]
    rw [ih (j + 1) _ _ (by omega), size_setLimb]

private theorem getLimb_mulAddRow_gt (a_i : UInt64) (b : Array UInt64) (i j : Nat)
    (carry : UInt64) (acc : Array UInt64) (k : Nat) (hk : i + b.size < k) :
    getLimb (mulAddRow a_i b i j carry acc) k = getLimb acc k := by
  induction hd : b.size - j generalizing j carry acc with
  | zero =>
    unfold mulAddRow
    have hge : ¬ j < b.size := by omega
    simp only [hge, ↓reduceDIte]
    by_cases hsz : i + b.size < acc.size
    · rw [getLimb_setLimb acc (i + b.size) carry hsz k]
      have hne : k ≠ i + b.size := by omega
      simp [hne]
    · unfold setLimb
      simp [hsz]
  | succ d ih =>
    unfold mulAddRow
    have hlt : j < b.size := by omega
    simp only [hlt, ↓reduceDIte]
    rw [ih (j + 1) _ _ (by omega)]
    by_cases hsz : i + j < acc.size
    · rw [getLimb_setLimb acc (i + j) _ hsz k]
      have hne : k ≠ i + j := by omega
      simp [hne]
    · unfold setLimb
      simp [hsz]

private theorem toNat_mulAddRow (a_i : UInt64) (b : Array UInt64) (i j : Nat)
    (carry : UInt64) (acc : Array UInt64)
    (hj : j ≤ b.size) (hsz : i + b.size < acc.size)
    (htop : getLimb acc (i + b.size) = 0) :
    toNat (mulAddRow a_i b i j carry acc) + a_i.toNat * toNatPrefix b j * (2 ^ 64) ^ i =
      toNat acc + carry.toNat * (2 ^ 64) ^ (i + j) + a_i.toNat * toNat b * (2 ^ 64) ^ i := by
  induction hd : b.size - j generalizing j carry acc with
  | zero =>
    have hjb : j = b.size := by omega
    subst hjb
    unfold mulAddRow
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    rw [toNat_setLimb_of_zero acc (i + b.size) carry hsz htop]
    unfold toNat
    omega
  | succ d ih =>
    have hlt : j < b.size := by omega
    unfold mulAddRow
    simp only [hlt, ↓reduceDIte]
    have hspec := mulAddCarry64_spec a_i b[j] (getLimb acc (i + j)) carry
    rcases hm : mulAddCarry64 a_i b[j] (getLimb acc (i + j)) carry with ⟨lo, carry'⟩
    rw [hm] at hspec
    dsimp only at hspec ⊢
    have hltacc : i + j < acc.size := by omega
    have htop' : getLimb (setLimb acc (i + j) lo) (i + b.size) = 0 := by
      rw [getLimb_setLimb acc (i + j) lo hltacc]
      split
      · omega
      · exact htop
    have hih := ih (j + 1) carry' (setLimb acc (i + j) lo) (by omega)
      (by rw [size_setLimb]; exact hsz) htop' (by omega)
    have hset := toNat_setLimb acc (i + j) lo hltacc
    rw [toNatPrefix_succ b j, getLimb_lt hlt] at hih
    have hpow1 : (2 ^ 64) ^ (i + (j + 1)) = 2 ^ 64 * (2 ^ 64) ^ (i + j) := by
      rw [← Nat.add_assoc, Nat.pow_succ (2 ^ 64), Nat.mul_comm]
    have hpow2 : (2 ^ 64) ^ j * (2 ^ 64) ^ i = (2 ^ 64) ^ (i + j) := by
      rw [← Nat.pow_add, Nat.add_comm]
    have hmul : (lo.toNat + carry'.toNat * 2 ^ 64) * (2 ^ 64) ^ (i + j) =
        (a_i.toNat * b[j].toNat + (getLimb acc (i + j)).toNat + carry.toNat) * (2 ^ 64) ^ (i + j) := by
      rw [hspec]
    have hr1 : carry'.toNat * (2 ^ 64) ^ (i + (j + 1)) =
        (carry'.toNat * 2 ^ 64) * (2 ^ 64) ^ (i + j) := by
      rw [hpow1, Nat.mul_assoc]
    have hr2 : a_i.toNat * (toNatPrefix b j + b[j].toNat * (2 ^ 64) ^ j) * (2 ^ 64) ^ i =
        a_i.toNat * toNatPrefix b j * (2 ^ 64) ^ i +
        (a_i.toNat * b[j].toNat) * (2 ^ 64) ^ (i + j) := by
      rw [Nat.mul_add, Nat.add_mul]
      congr 1
      calc a_i.toNat * (b[j].toNat * (2 ^ 64) ^ j) * (2 ^ 64) ^ i
          = (a_i.toNat * b[j].toNat) * (2 ^ 64) ^ j * (2 ^ 64) ^ i := by rw [← Nat.mul_assoc]
        _ = (a_i.toNat * b[j].toNat) * ((2 ^ 64) ^ j * (2 ^ 64) ^ i) := Nat.mul_assoc _ _ _
        _ = (a_i.toNat * b[j].toNat) * (2 ^ 64) ^ (i + j) := by rw [hpow2]
    rw [hr1, hr2] at hih
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul] at hmul
    omega

private theorem toNat_mulOuterLoop (a b : Array UInt64) (i : Nat) (acc : Array UInt64)
    (hi : i ≤ a.size) (hsz : a.size + b.size ≤ acc.size)
    (hzeros : ∀ k, i + b.size ≤ k → getLimb acc k = 0) :
    toNat (mulOuterLoop a b i acc) + toNatPrefix a i * toNat b =
      toNat acc + toNat a * toNat b := by
  induction hd : a.size - i generalizing i acc with
  | zero =>
    have hia : i = a.size := by omega
    subst hia
    unfold mulOuterLoop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    rfl
  | succ d ih =>
    have hlt : i < a.size := by omega
    unfold mulOuterLoop
    simp only [hlt, ↓reduceDIte]
    have hrow := toNat_mulAddRow a[i] b i 0 0 acc (Nat.zero_le _) (by omega)
      (hzeros (i + b.size) (Nat.le_refl _))
    simp only [toNatPrefix_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hrow
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [h0, Nat.zero_mul, Nat.add_zero] at hrow
    have hzeros' : ∀ k, (i + 1) + b.size ≤ k → getLimb (mulAddRow a[i] b i 0 0 acc) k = 0 := by
      intro k hk
      rw [getLimb_mulAddRow_gt a[i] b i 0 0 acc k (by omega)]
      exact hzeros k (by omega)
    have hih := ih (i + 1) (mulAddRow a[i] b i 0 0 acc) (by omega)
      (by rw [size_mulAddRow]; exact hsz) hzeros' (by omega)
    rw [toNatPrefix_succ a i, getLimb_lt hlt, Nat.add_mul] at hih
    have hcomm : a[i].toNat * (2 ^ 64) ^ i * toNat b = a[i].toNat * toNat b * (2 ^ 64) ^ i := by
      rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ i) (toNat b), ← Nat.mul_assoc]
    rw [hcomm] at hih
    omega

theorem wf_mulSchoolbook (a b : Array UInt64) : WF (mulSchoolbook a b) := by
  unfold mulSchoolbook
  split
  · exact Or.inl rfl
  · exact wf_normalize _

theorem toNat_mulSchoolbook (a b : Array UInt64) :
    toNat (mulSchoolbook a b) = toNat a * toNat b := by
  unfold mulSchoolbook
  split
  · rename_i hzero
    rcases Bool.or_eq_true_iff.mp hzero with ha | hb
    · have ha0 : a.size = 0 := eq_of_beq ha
      simp [toNat, ha0]
    · have hb0 : b.size = 0 := eq_of_beq hb
      simp [toNat, hb0]
  · rw [toNat_normalize]
    have h := toNat_mulOuterLoop a b 0 (mkZeros (a.size + b.size)) (Nat.zero_le _)
      (by rw [size_mkZeros]; exact Nat.le_refl _) (fun k _ => getLimb_mkZeros _ k)
    simp only [toNatPrefix_zero, Nat.zero_mul, Nat.add_zero, toNat_mkZeros, Nat.zero_add] at h
    exact h

/-! ### Dedicated 3-Pass Squaring (`sqrSchoolbook`) -/

private def diagSum (a : Array UInt64) : Nat → Nat
  | 0 => 0
  | k + 1 => diagSum a k + (getLimb a k).toNat * (getLimb a k).toNat * (2 ^ 64) ^ (2 * k)

private def sqCross (a : Array UInt64) : Nat → Nat
  | 0 => 0
  | k + 1 => sqCross a k + (getLimb a k).toNat * toNatPrefix a k * (2 ^ 64) ^ k

private theorem sq_decomp (a : Array UInt64) (n : Nat) :
    2 * sqCross a n + diagSum a n = toNatPrefix a n * toNatPrefix a n := by
  induction n with
  | zero => simp [sqCross, diagSum]
  | succ k ih =>
    simp only [sqCross, diagSum, toNatPrefix_succ]
    have hpow : (2 ^ 64) ^ k * (2 ^ 64) ^ k = (2 ^ 64) ^ (2 * k) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hsq : (toNatPrefix a k + (getLimb a k).toNat * (2 ^ 64) ^ k) *
        (toNatPrefix a k + (getLimb a k).toNat * (2 ^ 64) ^ k) =
        toNatPrefix a k * toNatPrefix a k +
        2 * ((getLimb a k).toNat * toNatPrefix a k * (2 ^ 64) ^ k) +
        (getLimb a k).toNat * (getLimb a k).toNat * (2 ^ 64) ^ (2 * k) := by
      have ht1 : toNatPrefix a k * ((getLimb a k).toNat * (2 ^ 64) ^ k) =
          (getLimb a k).toNat * toNatPrefix a k * (2 ^ 64) ^ k := by
        rw [← Nat.mul_assoc, Nat.mul_comm (toNatPrefix a k) (getLimb a k).toNat]
      have ht2 : (getLimb a k).toNat * (2 ^ 64) ^ k * toNatPrefix a k =
          (getLimb a k).toNat * toNatPrefix a k * (2 ^ 64) ^ k := by
        rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ k) (toNatPrefix a k), ← Nat.mul_assoc]
      have ht3 : (getLimb a k).toNat * (2 ^ 64) ^ k * ((getLimb a k).toNat * (2 ^ 64) ^ k) =
          (getLimb a k).toNat * (getLimb a k).toNat * (2 ^ 64) ^ (2 * k) := by
        calc (getLimb a k).toNat * (2 ^ 64) ^ k * ((getLimb a k).toNat * (2 ^ 64) ^ k)
            = ((getLimb a k).toNat * (2 ^ 64) ^ k * (getLimb a k).toNat) * (2 ^ 64) ^ k :=
              (Nat.mul_assoc _ _ _).symm
          _ = ((getLimb a k).toNat * ((2 ^ 64) ^ k * (getLimb a k).toNat)) * (2 ^ 64) ^ k := by
              rw [Nat.mul_assoc (getLimb a k).toNat]
          _ = (getLimb a k).toNat * (getLimb a k).toNat * ((2 ^ 64) ^ k * (2 ^ 64) ^ k) := by
              rw [Nat.mul_comm ((2 ^ 64) ^ k) (getLimb a k).toNat, ← Nat.mul_assoc, Nat.mul_assoc]
          _ = (getLimb a k).toNat * (getLimb a k).toNat * (2 ^ 64) ^ (2 * k) := by rw [hpow]
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, ht1, ht2, ht3]
      omega
    rw [hsq, ← ih]
    omega

private def upperLimbs (a : Array UInt64) (lo : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => upperLimbs a lo k + if lo ≤ k then (getLimb a k).toNat * (2 ^ 64) ^ k else 0

private theorem toNatPrefix_add_upperLimbs (a : Array UInt64) (lo k : Nat) (h : lo ≤ k) :
    toNatPrefix a lo + upperLimbs a lo k = toNatPrefix a k := by
  induction k with
  | zero =>
    have h0 : lo = 0 := by omega
    subst h0; rfl
  | succ k ih =>
    by_cases heq : lo = k + 1
    · subst heq
      have hzero : upperLimbs a (k + 1) (k + 1) = 0 := by
        suffices ∀ m, m ≤ k + 1 → upperLimbs a (k + 1) m = 0 from this (k + 1) (Nat.le_refl _)
        intro m hm
        induction m with
        | zero => rfl
        | succ m ihm =>
          simp only [upperLimbs, ihm (by omega)]
          have hnot : ¬ k + 1 ≤ m := by omega
          simp [hnot]
      rw [hzero, Nat.add_zero]
    · have hle : lo ≤ k := by omega
      simp only [upperLimbs, hle, ↓reduceIte, toNatPrefix_succ]
      rw [← ih hle]
      omega

private def rowCrossSum (a : Array UInt64) (n : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => rowCrossSum a n i + (getLimb a i).toNat * upperLimbs a (i + 1) n * (2 ^ 64) ^ i

private theorem rowCrossSum_step_n (a : Array UInt64) (i k : Nat) (h : i ≤ k) :
    rowCrossSum a (k + 1) i =
      rowCrossSum a k i + toNatPrefix a i * (getLimb a k).toNat * (2 ^ 64) ^ k := by
  induction i with
  | zero => simp [rowCrossSum]
  | succ i ih =>
    simp only [rowCrossSum, ih (by omega), toNatPrefix_succ]
    have hle : i + 1 ≤ k := by omega
    simp only [upperLimbs, hle, ↓reduceIte]
    have hdist : (getLimb a i).toNat * (upperLimbs a (i + 1) k + (getLimb a k).toNat * (2 ^ 64) ^ k) * (2 ^ 64) ^ i =
        (getLimb a i).toNat * upperLimbs a (i + 1) k * (2 ^ 64) ^ i +
        ((getLimb a i).toNat * (2 ^ 64) ^ i) * (getLimb a k).toNat * (2 ^ 64) ^ k := by
      rw [Nat.mul_add, Nat.add_mul]
      congr 1
      calc (getLimb a i).toNat * ((getLimb a k).toNat * (2 ^ 64) ^ k) * (2 ^ 64) ^ i
          = (getLimb a i).toNat * (getLimb a k).toNat * (2 ^ 64) ^ k * (2 ^ 64) ^ i := by
            rw [← Nat.mul_assoc]
        _ = (getLimb a i).toNat * (getLimb a k).toNat * ((2 ^ 64) ^ k * (2 ^ 64) ^ i) :=
            Nat.mul_assoc _ _ _
        _ = (getLimb a i).toNat * (2 ^ 64) ^ i * (getLimb a k).toNat * (2 ^ 64) ^ k := by
            rw [Nat.mul_comm ((2 ^ 64) ^ k) ((2 ^ 64) ^ i), ← Nat.mul_assoc,
                Nat.mul_assoc (getLimb a i).toNat, Nat.mul_comm (getLimb a k).toNat ((2 ^ 64) ^ i),
                ← Nat.mul_assoc]
    rw [hdist, Nat.add_mul, Nat.add_mul]
    omega

private theorem rowCrossSum_eq_sqCross (a : Array UInt64) (n : Nat) :
    rowCrossSum a n n = sqCross a n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [rowCrossSum, sqCross]
    have hu0 : upperLimbs a (k + 1) (k + 1) = 0 := by
      have h := toNatPrefix_add_upperLimbs a (k + 1) (k + 1) (Nat.le_refl _)
      omega
    rw [hu0, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
    rw [rowCrossSum_step_n a k k (Nat.le_refl _), ih]
    rw [Nat.mul_comm (toNatPrefix a k) (getLimb a k).toNat]

private theorem size_sqrOffRow (a : Array UInt64) (a_i : UInt64) (i j : Nat)
    (carry : UInt64) (acc : Array UInt64) :
    (sqrOffRow a a_i i j carry acc).size = acc.size := by
  induction hd : a.size - j generalizing j carry acc with
  | zero =>
    unfold sqrOffRow
    have hge : ¬ j < a.size := by omega
    simp [hge]
  | succ d ih =>
    unfold sqrOffRow
    have hlt : j < a.size := by omega
    simp only [hlt, ↓reduceDIte]
    rw [ih (j + 1) _ _ (by omega), size_setLimb]

private theorem getLimb_sqrOffRow_gt (a : Array UInt64) (a_i : UInt64) (i j : Nat)
    (carry : UInt64) (acc : Array UInt64) (k : Nat) (hk : i + a.size < k) :
    getLimb (sqrOffRow a a_i i j carry acc) k = getLimb acc k := by
  induction hd : a.size - j generalizing j carry acc with
  | zero =>
    unfold sqrOffRow
    have hge : ¬ j < a.size := by omega
    simp only [hge, ↓reduceDIte]
    by_cases hsz : i + a.size < acc.size
    · rw [getLimb_setLimb acc (i + a.size) carry hsz k]
      have hne : k ≠ i + a.size := by omega
      simp [hne]
    · unfold setLimb; simp [hsz]
  | succ d ih =>
    unfold sqrOffRow
    have hlt : j < a.size := by omega
    simp only [hlt, ↓reduceDIte]
    rw [ih (j + 1) _ _ (by omega)]
    by_cases hsz : i + j < acc.size
    · rw [getLimb_setLimb acc (i + j) _ hsz k]
      have hne : k ≠ i + j := by omega
      simp [hne]
    · unfold setLimb; simp [hsz]

private theorem toNat_sqrOffRow (a : Array UInt64) (a_i : UInt64) (i j : Nat)
    (carry : UInt64) (acc : Array UInt64)
    (hj : j ≤ a.size) (hsz : i + a.size < acc.size)
    (htop : getLimb acc (i + a.size) = 0) :
    toNat (sqrOffRow a a_i i j carry acc) + a_i.toNat * toNatPrefix a j * (2 ^ 64) ^ i =
      toNat acc + carry.toNat * (2 ^ 64) ^ (i + j) + a_i.toNat * toNat a * (2 ^ 64) ^ i := by
  induction hd : a.size - j generalizing j carry acc with
  | zero =>
    have hja : j = a.size := by omega
    subst hja
    unfold sqrOffRow
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    rw [toNat_setLimb_of_zero acc (i + a.size) carry hsz htop]
    unfold toNat
    omega
  | succ d ih =>
    have hlt : j < a.size := by omega
    unfold sqrOffRow
    simp only [hlt, ↓reduceDIte]
    have hspec := mulAddCarry64_spec a_i a[j] (getLimb acc (i + j)) carry
    rcases hm : mulAddCarry64 a_i a[j] (getLimb acc (i + j)) carry with ⟨lo, carry'⟩
    rw [hm] at hspec
    dsimp only at hspec ⊢
    have hltacc : i + j < acc.size := by omega
    have htop' : getLimb (setLimb acc (i + j) lo) (i + a.size) = 0 := by
      rw [getLimb_setLimb acc (i + j) lo hltacc]
      split
      · omega
      · exact htop
    have hih := ih (j + 1) carry' (setLimb acc (i + j) lo) (by omega)
      (by rw [size_setLimb]; exact hsz) htop' (by omega)
    have hset := toNat_setLimb acc (i + j) lo hltacc
    rw [toNatPrefix_succ a j, getLimb_lt hlt] at hih
    have hpow1 : (2 ^ 64) ^ (i + (j + 1)) = 2 ^ 64 * (2 ^ 64) ^ (i + j) := by
      rw [← Nat.add_assoc, Nat.pow_succ (2 ^ 64), Nat.mul_comm]
    have hpow2 : (2 ^ 64) ^ j * (2 ^ 64) ^ i = (2 ^ 64) ^ (i + j) := by
      rw [← Nat.pow_add, Nat.add_comm]
    have hmul : (lo.toNat + carry'.toNat * 2 ^ 64) * (2 ^ 64) ^ (i + j) =
        (a_i.toNat * a[j].toNat + (getLimb acc (i + j)).toNat + carry.toNat) * (2 ^ 64) ^ (i + j) := by
      rw [hspec]
    have hr1 : carry'.toNat * (2 ^ 64) ^ (i + (j + 1)) =
        (carry'.toNat * 2 ^ 64) * (2 ^ 64) ^ (i + j) := by
      rw [hpow1, Nat.mul_assoc]
    have hr2 : a_i.toNat * (toNatPrefix a j + a[j].toNat * (2 ^ 64) ^ j) * (2 ^ 64) ^ i =
        a_i.toNat * toNatPrefix a j * (2 ^ 64) ^ i +
        (a_i.toNat * a[j].toNat) * (2 ^ 64) ^ (i + j) := by
      rw [Nat.mul_add, Nat.add_mul]
      congr 1
      calc a_i.toNat * (a[j].toNat * (2 ^ 64) ^ j) * (2 ^ 64) ^ i
          = (a_i.toNat * a[j].toNat) * (2 ^ 64) ^ j * (2 ^ 64) ^ i := by rw [← Nat.mul_assoc]
        _ = (a_i.toNat * a[j].toNat) * ((2 ^ 64) ^ j * (2 ^ 64) ^ i) := Nat.mul_assoc _ _ _
        _ = (a_i.toNat * a[j].toNat) * (2 ^ 64) ^ (i + j) := by rw [hpow2]
    rw [hr1, hr2] at hih
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul] at hmul
    omega

private theorem size_sqrOffOuter (a : Array UInt64) (i : Nat) (acc : Array UInt64) :
    (sqrOffOuter a i acc).size = acc.size := by
  induction hd : a.size - i generalizing i acc with
  | zero =>
    unfold sqrOffOuter
    have hge : ¬ i < a.size := by omega
    simp [hge]
  | succ d ih =>
    unfold sqrOffOuter
    have hlt : i < a.size := by omega
    simp only [hlt, ↓reduceDIte]
    rw [ih (i + 1) _ (by omega), size_sqrOffRow]

private theorem toNat_sqrOffOuter (a : Array UInt64) (i : Nat) (acc : Array UInt64)
    (hi : i ≤ a.size) (hsz : 2 * a.size ≤ acc.size)
    (hzeros : ∀ k, i + a.size ≤ k → getLimb acc k = 0) :
    toNat (sqrOffOuter a i acc) + rowCrossSum a a.size i =
      toNat acc + rowCrossSum a a.size a.size := by
  induction hd : a.size - i generalizing i acc with
  | zero =>
    have hia : i = a.size := by omega
    subst hia
    unfold sqrOffOuter
    simp only [Nat.lt_irrefl, ↓reduceDIte]
  | succ d ih =>
    have hlt : i < a.size := by omega
    unfold sqrOffOuter
    simp only [hlt, ↓reduceDIte]
    have hrow := toNat_sqrOffRow a a[i] i (i + 1) 0 acc (by omega) (by omega)
      (hzeros (i + a.size) (Nat.le_refl _))
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [h0, Nat.zero_mul, Nat.add_zero] at hrow
    have hu := toNatPrefix_add_upperLimbs a (i + 1) a.size (by omega)
    have hrow' : toNat (sqrOffRow a a[i] i (i + 1) 0 acc) =
        toNat acc + a[i].toNat * upperLimbs a (i + 1) a.size * (2 ^ 64) ^ i := by
      have hmul : a[i].toNat * toNat a * (2 ^ 64) ^ i =
          a[i].toNat * toNatPrefix a (i + 1) * (2 ^ 64) ^ i +
          a[i].toNat * upperLimbs a (i + 1) a.size * (2 ^ 64) ^ i := by
        unfold toNat
        rw [← hu, Nat.mul_add, Nat.add_mul]
      omega
    have hzeros' : ∀ k, (i + 1) + a.size ≤ k → getLimb (sqrOffRow a a[i] i (i + 1) 0 acc) k = 0 := by
      intro k hk
      rw [getLimb_sqrOffRow_gt a a[i] i (i + 1) 0 acc k (by omega)]
      exact hzeros k (by omega)
    have hih := ih (i + 1) (sqrOffRow a a[i] i (i + 1) 0 acc) (by omega)
      (by rw [size_sqrOffRow]; exact hsz) hzeros' (by omega)
    simp only [rowCrossSum, getLimb_lt hlt] at hih
    omega

private theorem size_doubleInPlaceLoop (acc : Array UInt64) (i : Nat) (carry : Bool) :
    (doubleInPlaceLoop acc i carry).size = acc.size := by
  induction hd : acc.size - i generalizing acc i carry with
  | zero =>
    unfold doubleInPlaceLoop
    have hge : ¬ i < acc.size := by omega
    simp [hge]
  | succ d ih =>
    unfold doubleInPlaceLoop
    have hlt : i < acc.size := by omega
    simp only [hlt, ↓reduceDIte]
    rw [ih (acc.set i _) (i + 1) _ (by rw [Array.size_set]; omega), Array.size_set]

private theorem toNat_doubleInPlaceLoop (acc : Array UInt64) (i : Nat) (carry : Bool)
    (hi : i ≤ acc.size)
    (hbound : 2 * toNat acc + carry.toNat * (2 ^ 64) ^ i < (2 ^ 64) ^ acc.size + toNatPrefix acc i) :
    toNat (doubleInPlaceLoop acc i carry) + toNatPrefix acc i =
      2 * toNat acc + carry.toNat * (2 ^ 64) ^ i := by
  induction hd : acc.size - i generalizing acc i carry with
  | zero =>
    have hia : i = acc.size := by omega
    subst hia
    unfold doubleInPlaceLoop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    have hpref : toNatPrefix acc acc.size = toNat acc := rfl
    rw [hpref] at hbound ⊢
    cases carry
    · simp; omega
    · simp only [Bool.toNat_true, Nat.one_mul] at hbound
      omega
  | succ d ih =>
    have hlt : i < acc.size := by omega
    unfold doubleInPlaceLoop
    simp only [hlt, ↓reduceDIte]
    have hspec := addCarry64_spec acc[i] acc[i] carry
    rcases hac : addCarry64 acc[i] acc[i] carry with ⟨lo, c'⟩
    rw [hac] at hspec
    dsimp only at hspec ⊢
    have hsetEq : acc.set i lo = setLimb acc i lo := by simp [setLimb, hlt]
    have hto := toNat_setLimb acc i lo hlt
    rw [getLimb_lt hlt] at hto
    have hpref : toNatPrefix (acc.set i lo) (i + 1) = toNatPrefix acc i + lo.toNat * (2 ^ 64) ^ i := by
      rw [hsetEq, toNatPrefix_succ, getLimb_setLimb acc i lo hlt i]
      simp only [↓reduceIte]
      congr 1
      apply toNatPrefix_congr
      intro j hj
      rw [getLimb_setLimb acc i lo hlt j]
      simp [Nat.ne_of_lt hj]
    have hstep : (lo.toNat + c'.toNat * 2 ^ 64) * (2 ^ 64) ^ i =
        (acc[i].toNat + acc[i].toNat + carry.toNat) * (2 ^ 64) ^ i := by
      rw [hspec]
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul] at hstep
    have hpow : c'.toNat * (2 ^ 64) ^ (i + 1) = c'.toNat * 2 ^ 64 * (2 ^ 64) ^ i := by
      rw [Nat.pow_succ (2 ^ 64) i, Nat.mul_comm ((2 ^ 64) ^ i) (2 ^ 64), Nat.mul_assoc]
    have hbound' : 2 * toNat (acc.set i lo) + c'.toNat * (2 ^ 64) ^ (i + 1) <
        (2 ^ 64) ^ (acc.set i lo).size + toNatPrefix (acc.set i lo) (i + 1) := by
      rw [Array.size_set, hpref, hpow, hsetEq]
      omega
    have hih := ih (acc.set i lo) (i + 1) c' (by rw [Array.size_set]; omega) hbound'
      (by rw [Array.size_set]; omega)
    rw [hpref, hpow, hsetEq] at hih
    rw [hsetEq]
    omega

private theorem sqrDiag_comb_arith {B s0 c0 s1 c1 a0 a1 lo hiW sq carry : Nat}
    (hmul : lo + hiW * B = sq)
    (hs0 : s0 + c0 * B = a0 + lo + carry)
    (hs1 : s1 + c1 * B = a1 + hiW + c0) :
    s0 + s1 * B + c1 * (B * B) = a0 + a1 * B + sq + carry := by
  have hm1 := congrArg (· * B) hs1
  simp only [Nat.add_mul, Nat.mul_assoc] at hm1
  omega

private theorem toNat_sqrAddDiagLoop (a : Array UInt64) (i : Nat) (carry : Bool)
    (acc : Array UInt64) (hi : i ≤ a.size) (hsz : acc.size = 2 * a.size)
    (hbound : toNat acc + carry.toNat * (2 ^ 64) ^ (2 * i) + diagSum a a.size <
      (2 ^ 64) ^ (2 * a.size) + diagSum a i) :
    toNat (sqrAddDiagLoop a i carry acc) + diagSum a i =
      toNat acc + carry.toNat * (2 ^ 64) ^ (2 * i) + diagSum a a.size := by
  induction hd : a.size - i generalizing i carry acc with
  | zero =>
    have hia : i = a.size := by omega
    subst hia
    unfold sqrAddDiagLoop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    cases carry
    · simp
    · simp only [Bool.toNat_true, Nat.one_mul] at hbound
      omega
  | succ d ih =>
    have hlt : i < a.size := by omega
    unfold sqrAddDiagLoop
    simp only [hlt, ↓reduceDIte]
    have hmul := mulWide64_spec a[i] a[i]
    rcases hm : mulWide64 a[i] a[i] with ⟨lo, hiW⟩
    rw [hm] at hmul
    have hs0 := addCarry64_spec (getLimb acc (2 * i)) lo carry
    rcases h0 : addCarry64 (getLimb acc (2 * i)) lo carry with ⟨s0, c0⟩
    rw [h0] at hs0
    have hs1 := addCarry64_spec (getLimb acc (2 * i + 1)) hiW c0
    rcases h1 : addCarry64 (getLimb acc (2 * i + 1)) hiW c0 with ⟨s1, c1⟩
    rw [h1] at hs1
    dsimp only at hmul hs0 hs1 ⊢
    let acc1 := setLimb acc (2 * i) s0
    let acc2 := setLimb acc1 (2 * i + 1) s1
    have hlt0 : 2 * i < acc.size := by omega
    have hlt1 : 2 * i + 1 < acc1.size := by rw [size_setLimb]; omega
    have hto1 := toNat_setLimb acc (2 * i) s0 hlt0
    have hto2 := toNat_setLimb acc1 (2 * i + 1) s1 hlt1
    have hget1 : getLimb acc1 (2 * i + 1) = getLimb acc (2 * i + 1) := by
      rw [getLimb_setLimb acc (2 * i) s0 hlt0]
      simp
    rw [hget1] at hto2
    have hcomb : s0.toNat + s1.toNat * 2 ^ 64 + c1.toNat * (2 ^ 64 * 2 ^ 64) =
        (getLimb acc (2 * i)).toNat + (getLimb acc (2 * i + 1)).toNat * 2 ^ 64 +
        a[i].toNat * a[i].toNat + carry.toNat :=
      sqrDiag_comb_arith hmul hs0 hs1
    have hpow1 : (2 ^ 64) ^ (2 * i + 1) = 2 ^ 64 * (2 ^ 64) ^ (2 * i) := by
      rw [Nat.pow_succ (2 ^ 64), Nat.mul_comm]
    have hpow2 : (2 ^ 64) ^ (2 * (i + 1)) = (2 ^ 64 * 2 ^ 64) * (2 ^ 64) ^ (2 * i) := by
      have heq : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
      rw [heq, Nat.pow_succ (2 ^ 64), Nat.pow_succ (2 ^ 64)]
      calc (2 ^ 64) ^ (2 * i) * 2 ^ 64 * 2 ^ 64
          = (2 ^ 64) ^ (2 * i) * (2 ^ 64 * 2 ^ 64) := Nat.mul_assoc _ _ _
        _ = (2 ^ 64 * 2 ^ 64) * (2 ^ 64) ^ (2 * i) := Nat.mul_comm _ _
    have hacc2 : toNat acc2 + c1.toNat * (2 ^ 64) ^ (2 * (i + 1)) =
        toNat acc + carry.toNat * (2 ^ 64) ^ (2 * i) + a[i].toNat * a[i].toNat * (2 ^ 64) ^ (2 * i) := by
      have hmcomb := congrArg (· * (2 ^ 64) ^ (2 * i)) hcomb
      repeat rw [Nat.add_mul] at hmcomb
      rw [hpow1] at hto2
      rw [hpow2]
      have ha1 : s1.toNat * (2 ^ 64 * (2 ^ 64) ^ (2 * i)) = s1.toNat * 2 ^ 64 * (2 ^ 64) ^ (2 * i) := by
        rw [← Nat.mul_assoc]
      have ha2 : (getLimb acc (2 * i + 1)).toNat * (2 ^ 64 * (2 ^ 64) ^ (2 * i)) =
          (getLimb acc (2 * i + 1)).toNat * 2 ^ 64 * (2 ^ 64) ^ (2 * i) := by
        rw [← Nat.mul_assoc]
      have ha3 : c1.toNat * ((2 ^ 64 * 2 ^ 64) * (2 ^ 64) ^ (2 * i)) =
          c1.toNat * (2 ^ 64 * 2 ^ 64) * (2 ^ 64) ^ (2 * i) := by
        rw [← Nat.mul_assoc]
      rw [ha1, ha2] at hto2
      rw [ha3]
      change toNat acc1 + (getLimb acc (2 * i)).toNat * (2 ^ 64) ^ (2 * i) =
          toNat acc + s0.toNat * (2 ^ 64) ^ (2 * i) at hto1
      change toNat acc2 + (getLimb acc (2 * i + 1)).toNat * 2 ^ 64 * (2 ^ 64) ^ (2 * i) =
          toNat acc1 + s1.toNat * 2 ^ 64 * (2 ^ 64) ^ (2 * i) at hto2
      suffices ∀ T0 T1 T2 P0 P1 Q0 Q1 C S A : Nat,
          T1 + P0 = T0 + Q0 → T2 + P1 = T1 + Q1 → Q0 + Q1 + C = P0 + P1 + S + A →
          T2 + C = T0 + A + S from
        this _ _ _ _ _ _ _ _ _ _ hto1 hto2 hmcomb
      intro T0 T1 T2 P0 P1 Q0 Q1 C S A h1 h2 h3; omega
    have hdiag : diagSum a (i + 1) = diagSum a i + a[i].toNat * a[i].toNat * (2 ^ 64) ^ (2 * i) := by
      simp [diagSum, getLimb_lt hlt]
    have hbound' : toNat acc2 + c1.toNat * (2 ^ 64) ^ (2 * (i + 1)) + diagSum a a.size <
        (2 ^ 64) ^ (2 * a.size) + diagSum a (i + 1) := by
      rw [hacc2, hdiag]
      omega
    have hsz2 : acc2.size = 2 * a.size := by simp [acc2, acc1, hsz]
    have hih := ih (i + 1) c1 acc2 (by omega) hsz2 hbound' (by omega)
    rw [hacc2, hdiag] at hih
    change toNat (sqrAddDiagLoop a (i + 1) c1 acc2) + diagSum a i =
      toNat acc + carry.toNat * (2 ^ 64) ^ (2 * i) + diagSum a a.size
    omega

theorem wf_sqrSchoolbook (a : Array UInt64) : WF (sqrSchoolbook a) := by
  unfold sqrSchoolbook
  split
  · exact Or.inl rfl
  · exact wf_normalize _

theorem toNat_sqrSchoolbook (a : Array UInt64) :
    toNat (sqrSchoolbook a) = toNat a * toNat a := by
  unfold sqrSchoolbook
  split
  · rename_i hz
    have hsz : a.size = 0 := eq_of_beq hz
    simp [toNat, hsz]
  · rw [toNat_normalize]
    let acc0 := mkZeros (2 * a.size)
    let acc1 := sqrOffOuter a 0 acc0
    let acc2 := doubleInPlaceLoop acc1 0 false
    have hsz1 : acc1.size = 2 * a.size := by
      rw [size_sqrOffOuter, size_mkZeros]
    have hsz2 : acc2.size = 2 * a.size := by
      rw [size_doubleInPlaceLoop, hsz1]
    have h1 : toNat acc1 = sqCross a a.size := by
      have h := toNat_sqrOffOuter a 0 acc0 (Nat.zero_le _)
        (by rw [size_mkZeros]; exact Nat.le_refl _) (fun k _ => getLimb_mkZeros _ k)
      have h0 : toNat acc0 = 0 := toNat_mkZeros (2 * a.size)
      simp only [rowCrossSum, h0, Nat.add_zero, Nat.zero_add] at h
      rw [show toNat acc1 = toNat (sqrOffOuter a 0 acc0) from rfl, h, rowCrossSum_eq_sqCross]
    have hsq := sq_decomp a a.size
    have hsq_lt : toNat a * toNat a < (2 ^ 64) ^ (2 * a.size) := by
      have hlt : toNat a < (2 ^ 64) ^ a.size := toNat_lt a
      have hpow : (2 ^ 64) ^ a.size * (2 ^ 64) ^ a.size = (2 ^ 64) ^ (2 * a.size) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [← hpow]
      exact Nat.mul_lt_mul_of_lt_of_lt hlt hlt
    have h2 : toNat acc2 = 2 * sqCross a a.size := by
      have h := toNat_doubleInPlaceLoop acc1 0 false (Nat.zero_le _) (by
        rw [hsz1, h1, toNatPrefix_zero]
        simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
        unfold toNat at hsq_lt
        omega)
      simp only [toNatPrefix_zero, Bool.toNat_false, Nat.zero_mul, Nat.add_zero, h1] at h
      exact h
    have h3 := toNat_sqrAddDiagLoop a 0 false acc2 (Nat.zero_le _) hsz2 (by
      rw [h2]
      simp only [diagSum, Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
      unfold toNat at hsq_lt
      omega)
    simp only [diagSum, Bool.toNat_false, Nat.zero_mul, Nat.add_zero, h2] at h3
    rw [h3, hsq]
    rfl

/-! ### Karatsuba Multiplication and Squaring (`mulKaratsuba`, `mul`, `sqrKaratsuba`, `sqr`) -/

theorem wf_mulKaratsuba (a b : Array UInt64) : WF (mulKaratsuba a b) := by
  induction hn : max a.size b.size using Nat.strongRecOn generalizing a b with
  | ind n ih =>
    unfold mulKaratsuba
    split
    · exact wf_mulSchoolbook a b
    · exact wf_add _ _

theorem toNat_mulKaratsuba (a b : Array UInt64) :
    toNat (mulKaratsuba a b) = toNat a * toNat b := by
  induction hn : max a.size b.size using Nat.strongRecOn generalizing a b with
  | ind n ih =>
    unfold mulKaratsuba
    split
    · exact toNat_mulSchoolbook a b
    · rename_i hnotbase
      dsimp only
      have hge : karatsubaThreshold ≤ a.size ∧ karatsubaThreshold ≤ b.size :=
        ⟨Nat.not_lt.mp (fun h => hnotbase (Or.inl h)),
         Nat.not_lt.mp (fun h => hnotbase (Or.inr h))⟩
      let m := max a.size b.size / 2
      let a0 := normalize (slice a 0 m)
      let a1 := normalize (slice a m a.size)
      let b0 := normalize (slice b 0 m)
      let b1 := normalize (slice b m b.size)
      let sA := add a0 a1
      let sB := add b0 b1
      have ha0 : a0.size ≤ m := by
        have h1 := size_normalize_le (slice a 0 m)
        have h2 := size_slice a 0 m
        change (normalize (slice a 0 m)).size ≤ m; omega
      have ha1 : a1.size ≤ max a.size b.size - m := by
        have h1 := size_normalize_le (slice a m a.size)
        have h2 := size_slice a m a.size
        change (normalize (slice a m a.size)).size ≤ max a.size b.size - m; omega
      have hb0 : b0.size ≤ m := by
        have h1 := size_normalize_le (slice b 0 m)
        have h2 := size_slice b 0 m
        change (normalize (slice b 0 m)).size ≤ m; omega
      have hb1 : b1.size ≤ max a.size b.size - m := by
        have h1 := size_normalize_le (slice b m b.size)
        have h2 := size_slice b m b.size
        change (normalize (slice b m b.size)).size ≤ max a.size b.size - m; omega
      have hsA : sA.size ≤ max a0.size a1.size + 1 := size_add_le a0 a1
      have hsB : sB.size ≤ max b0.size b1.size + 1 := size_add_le b0 b1
      have hlt0 : max a0.size b0.size < n := by unfold karatsubaThreshold at hge; omega
      have hlt1 : max a1.size b1.size < n := by unfold karatsubaThreshold at hge; omega
      have hltS : max sA.size sB.size < n := by unfold karatsubaThreshold at hge; omega
      have hz0 : toNat (mulKaratsuba a0 b0) = toNat a0 * toNat b0 := ih _ hlt0 a0 b0 rfl
      have hz2 : toNat (mulKaratsuba a1 b1) = toNat a1 * toNat b1 := ih _ hlt1 a1 b1 rfl
      have hzS : toNat (mulKaratsuba sA sB) = toNat sA * toNat sB := ih _ hltS sA sB rfl
      have haSplit : toNat a = toNat a0 + toNat a1 * (2 ^ 64) ^ m := by
        simpa [a0, a1, toNat_normalize] using toNat_slice_split a m
      have hbSplit : toNat b = toNat b0 + toNat b1 * (2 ^ 64) ^ m := by
        simpa [b0, b1, toNat_normalize] using toNat_slice_split b m
      rw [toNat_add, toNat_add, toNat_shiftLimbs, toNat_shiftLimbs, toNat_subRaw, toNat_add,
          hz0, hz2, hzS, toNat_add, toNat_add, haSplit, hbSplit]
      have hmid : (toNat a0 + toNat a1) * (toNat b0 + toNat b1) -
          (toNat a0 * toNat b0 + toNat a1 * toNat b1) =
          toNat a0 * toNat b1 + toNat a1 * toNat b0 := by
        have hexp : (toNat a0 + toNat a1) * (toNat b0 + toNat b1) =
            toNat a0 * toNat b0 + toNat a0 * toNat b1 + toNat a1 * toNat b0 + toNat a1 * toNat b1 := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
        omega
      rw [hmid]
      have hpow2 : (2 ^ 64) ^ (2 * m) = (2 ^ 64) ^ m * (2 ^ 64) ^ m := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [hpow2]
      calc toNat a0 * toNat b0 + (toNat a0 * toNat b1 + toNat a1 * toNat b0) * (2 ^ 64) ^ m +
            toNat a1 * toNat b1 * ((2 ^ 64) ^ m * (2 ^ 64) ^ m)
          = toNat a0 * toNat b0 + toNat a0 * (toNat b1 * (2 ^ 64) ^ m) +
            (toNat a1 * (2 ^ 64) ^ m * toNat b0 +
             toNat a1 * (2 ^ 64) ^ m * (toNat b1 * (2 ^ 64) ^ m)) := by
            rw [Nat.add_mul]
            have t1 : toNat a0 * toNat b1 * (2 ^ 64) ^ m = toNat a0 * (toNat b1 * (2 ^ 64) ^ m) :=
              Nat.mul_assoc _ _ _
            have t2 : toNat a1 * toNat b0 * (2 ^ 64) ^ m = toNat a1 * (2 ^ 64) ^ m * toNat b0 := by
              rw [Nat.mul_assoc, Nat.mul_comm (toNat b0) ((2 ^ 64) ^ m), ← Nat.mul_assoc]
            have t3 : toNat a1 * toNat b1 * ((2 ^ 64) ^ m * (2 ^ 64) ^ m) =
                toNat a1 * (2 ^ 64) ^ m * (toNat b1 * (2 ^ 64) ^ m) := by
              calc toNat a1 * toNat b1 * ((2 ^ 64) ^ m * (2 ^ 64) ^ m)
                  = toNat a1 * toNat b1 * (2 ^ 64) ^ m * (2 ^ 64) ^ m := (Nat.mul_assoc _ _ _).symm
                _ = toNat a1 * (toNat b1 * (2 ^ 64) ^ m) * (2 ^ 64) ^ m := by
                    rw [Nat.mul_assoc (toNat a1)]
                _ = toNat a1 * (2 ^ 64) ^ m * (toNat b1 * (2 ^ 64) ^ m) := by
                    rw [Nat.mul_assoc, Nat.mul_comm (toNat b1 * (2 ^ 64) ^ m) ((2 ^ 64) ^ m),
                        ← Nat.mul_assoc]
            rw [t1, t2, t3]; omega
        _ = (toNat a0 + toNat a1 * (2 ^ 64) ^ m) * (toNat b0 + toNat b1 * (2 ^ 64) ^ m) := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]

theorem wf_mul (a b : Array UInt64) : WF (mul a b) := wf_mulKaratsuba a b

theorem toNat_mul (a b : Array UInt64) : toNat (mul a b) = toNat a * toNat b :=
  toNat_mulKaratsuba a b

theorem wf_sqrKaratsuba (a : Array UInt64) : WF (sqrKaratsuba a) := by
  unfold sqrKaratsuba
  split
  · exact wf_sqrSchoolbook a
  · exact wf_add _ _

theorem toNat_sqrKaratsuba (a : Array UInt64) :
    toNat (sqrKaratsuba a) = toNat a * toNat a := by
  induction hn : a.size using Nat.strongRecOn generalizing a with
  | ind n ih =>
    unfold sqrKaratsuba
    split
    · exact toNat_sqrSchoolbook a
    · rename_i hnotbase
      dsimp only
      have hge : karatsubaThreshold ≤ a.size := Nat.not_lt.mp hnotbase
      let m := a.size / 2
      let a0 := normalize (slice a 0 m)
      let a1 := normalize (slice a m a.size)
      let sA := add a0 a1
      have ha0 : a0.size ≤ m := by
        have h1 := size_normalize_le (slice a 0 m)
        have h2 := size_slice a 0 m
        change (normalize (slice a 0 m)).size ≤ m; omega
      have ha1 : a1.size ≤ a.size - m := by
        have h1 := size_normalize_le (slice a m a.size)
        have h2 := size_slice a m a.size
        change (normalize (slice a m a.size)).size ≤ a.size - m; omega
      have hsA : sA.size ≤ max a0.size a1.size + 1 := size_add_le a0 a1
      have hlt0 : a0.size < n := by unfold karatsubaThreshold at hge; omega
      have hlt1 : a1.size < n := by unfold karatsubaThreshold at hge; omega
      have hltS : sA.size < n := by unfold karatsubaThreshold at hge; omega
      have hz0 : toNat (sqrKaratsuba a0) = toNat a0 * toNat a0 := ih _ hlt0 a0 rfl
      have hz2 : toNat (sqrKaratsuba a1) = toNat a1 * toNat a1 := ih _ hlt1 a1 rfl
      have hzS : toNat (sqrKaratsuba sA) = toNat sA * toNat sA := ih _ hltS sA rfl
      have haSplit : toNat a = toNat a0 + toNat a1 * (2 ^ 64) ^ m := by
        simpa [a0, a1, toNat_normalize] using toNat_slice_split a m
      rw [toNat_add, toNat_add, toNat_shiftLimbs, toNat_shiftLimbs, toNat_subRaw, toNat_add,
          hz0, hz2, hzS, toNat_add, haSplit]
      have hmid : (toNat a0 + toNat a1) * (toNat a0 + toNat a1) -
          (toNat a0 * toNat a0 + toNat a1 * toNat a1) =
          toNat a0 * toNat a1 + toNat a1 * toNat a0 := by
        have hexp : (toNat a0 + toNat a1) * (toNat a0 + toNat a1) =
            toNat a0 * toNat a0 + toNat a0 * toNat a1 + toNat a1 * toNat a0 + toNat a1 * toNat a1 := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
        omega
      rw [hmid]
      have hpow2 : (2 ^ 64) ^ (2 * m) = (2 ^ 64) ^ m * (2 ^ 64) ^ m := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [hpow2]
      calc toNat a0 * toNat a0 + (toNat a0 * toNat a1 + toNat a1 * toNat a0) * (2 ^ 64) ^ m +
            toNat a1 * toNat a1 * ((2 ^ 64) ^ m * (2 ^ 64) ^ m)
          = toNat a0 * toNat a0 + toNat a0 * (toNat a1 * (2 ^ 64) ^ m) +
            (toNat a1 * (2 ^ 64) ^ m * toNat a0 +
             toNat a1 * (2 ^ 64) ^ m * (toNat a1 * (2 ^ 64) ^ m)) := by
            rw [Nat.add_mul]
            have t1 : toNat a0 * toNat a1 * (2 ^ 64) ^ m = toNat a0 * (toNat a1 * (2 ^ 64) ^ m) :=
              Nat.mul_assoc _ _ _
            have t2 : toNat a1 * toNat a0 * (2 ^ 64) ^ m = toNat a1 * (2 ^ 64) ^ m * toNat a0 := by
              rw [Nat.mul_assoc, Nat.mul_comm (toNat a0) ((2 ^ 64) ^ m), ← Nat.mul_assoc]
            have t3 : toNat a1 * toNat a1 * ((2 ^ 64) ^ m * (2 ^ 64) ^ m) =
                toNat a1 * (2 ^ 64) ^ m * (toNat a1 * (2 ^ 64) ^ m) := by
              calc toNat a1 * toNat a1 * ((2 ^ 64) ^ m * (2 ^ 64) ^ m)
                  = toNat a1 * toNat a1 * (2 ^ 64) ^ m * (2 ^ 64) ^ m := (Nat.mul_assoc _ _ _).symm
                _ = toNat a1 * (toNat a1 * (2 ^ 64) ^ m) * (2 ^ 64) ^ m := by
                    rw [Nat.mul_assoc (toNat a1)]
                _ = toNat a1 * (2 ^ 64) ^ m * (toNat a1 * (2 ^ 64) ^ m) := by
                    rw [Nat.mul_assoc, Nat.mul_comm (toNat a1 * (2 ^ 64) ^ m) ((2 ^ 64) ^ m),
                        ← Nat.mul_assoc]
            rw [t1, t2, t3]; omega
        _ = (toNat a0 + toNat a1 * (2 ^ 64) ^ m) * (toNat a0 + toNat a1 * (2 ^ 64) ^ m) := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]

theorem wf_sqr (a : Array UInt64) : WF (sqr a) := wf_sqrKaratsuba a

theorem toNat_sqr (a : Array UInt64) : toNat (sqr a) = toNat a * toNat a :=
  toNat_sqrKaratsuba a

/-! ### Left-to-Right Binary Exponentiation (`pow`) -/

private theorem natBitLenLoop_eq (n acc : Nat) :
    natBitLenLoop n acc = acc + natBitLenLoop n 0 := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    unfold natBitLenLoop
    split
    · simp
    · rename_i hne
      have hlt : n >>> 1 < n := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hne) (by decide)
      rw [ih (n >>> 1) hlt (acc + 1), ih (n >>> 1) hlt 1]
      omega

private theorem natBitLen_spec (n : Nat) (hn : n ≠ 0) :
    1 ≤ natBitLen n ∧ 2 ^ (natBitLen n - 1) ≤ n ∧ n < 2 ^ (natBitLen n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold natBitLen
    unfold natBitLenLoop
    simp only [hn, ↓reduceDIte]
    rw [natBitLenLoop_eq (n >>> 1) 1, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    change 1 ≤ 1 + natBitLen (n / 2) ∧
      2 ^ (1 + natBitLen (n / 2) - 1) ≤ n ∧ n < 2 ^ (1 + natBitLen (n / 2))
    by_cases h2 : n / 2 = 0
    · have hbl0 : natBitLen (n / 2) = 0 := by
        rw [h2]; unfold natBitLen natBitLenLoop; simp
      rw [hbl0]
      omega
    · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have ⟨hge1, hlo, hhi⟩ := ih (n / 2) hlt h2
      refine ⟨by omega, ?_, ?_⟩
      · have heq : 1 + natBitLen (n / 2) - 1 = (natBitLen (n / 2) - 1) + 1 := by omega
        rw [heq, Nat.pow_succ]
        omega
      · rw [Nat.add_comm 1, Nat.pow_succ]
        omega

private theorem wf_powLoop (base : Array UInt64) (exp i : Nat) (acc : Array UInt64)
    (hacc : WF acc) : WF (powLoop base exp i acc) := by
  induction i generalizing acc with
  | zero => exact hacc
  | succ i ih =>
    unfold powLoop
    apply ih
    split
    · exact wf_mul _ _
    · exact wf_sqr _

private theorem toNat_powLoop (base : Array UInt64) (exp i : Nat) (acc : Array UInt64) :
    toNat (powLoop base exp i acc) =
      (toNat acc) ^ (2 ^ i) * (toNat base) ^ (exp % 2 ^ i) := by
  induction i generalizing acc with
  | zero => simp [powLoop, Nat.mod_one]
  | succ i ih =>
    unfold powLoop
    rw [ih]
    have hbit : ((exp >>> i) &&& 1) = (exp / 2 ^ i) % 2 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
    have hmod_split : exp % 2 ^ (i + 1) = ((exp / 2 ^ i) % 2) * 2 ^ i + exp % 2 ^ i := by
      rw [Nat.pow_succ, Nat.mod_mul, Nat.mul_comm (2 ^ i) ((exp / 2 ^ i) % 2), Nat.add_comm]
    have hpow2 : (toNat acc * toNat acc) ^ (2 ^ i) = (toNat acc) ^ (2 ^ (i + 1)) := by
      rw [← Nat.pow_two, ← Nat.pow_mul, Nat.pow_succ, Nat.mul_comm 2 (2 ^ i)]
    split
    · rename_i h1
      have hb1 : (exp / 2 ^ i) % 2 = 1 := by rw [← hbit]; exact eq_of_beq h1
      rw [toNat_mul, toNat_sqr, Nat.mul_pow, hpow2, hmod_split, hb1, Nat.one_mul,
          Nat.mul_assoc, ← Nat.pow_add]
    · rename_i h0
      have hb0 : (exp / 2 ^ i) % 2 = 0 := by
        have hlt : (exp / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by decide)
        have hne : (exp / 2 ^ i) % 2 ≠ 1 := fun h => h0 (by rw [hbit, h]; rfl)
        omega
      rw [toNat_sqr, hpow2, hmod_split, hb0, Nat.zero_mul, Nat.zero_add]

theorem wf_pow (base : Array UInt64) (exp : Nat) : WF (pow base exp) := by
  unfold pow
  split
  · exact wf_one
  · dsimp only
    split
    · exact wf_zero
    · split
      · exact wf_one
      · exact wf_powLoop _ _ _ _ (wf_normalize base)

theorem toNat_pow (base : Array UInt64) (exp : Nat) :
    toNat (pow base exp) = (toNat base) ^ exp := by
  unfold pow
  split
  · rename_i he0
    have he : exp = 0 := eq_of_beq he0
    subst he
    simp
  · rename_i hene
    have hexp : exp ≠ 0 := fun h => hene (by simp [h])
    dsimp only
    split
    · rename_i hb0
      have hsz : (normalize base).size = 0 := eq_of_beq hb0
      have hb : toNat base = 0 := by rw [← toNat_normalize, toNat, hsz]; rfl
      rw [hb, toNat_zero, Nat.zero_pow (Nat.pos_of_ne_zero hexp)]
    · split
      · rename_i hb1
        have ⟨hsz1, h0⟩ := Bool.and_eq_true_iff.mp hb1
        have hsz : (normalize base).size = 1 := eq_of_beq hsz1
        have hv : getLimb (normalize base) 0 = 1 := eq_of_beq h0
        have hb : toNat base = 1 := by
          rw [← toNat_normalize, toNat, hsz, toNatPrefix_succ, toNatPrefix_zero, hv]
          decide
        rw [hb, toNat_one, Nat.one_pow]
      · rw [toNat_powLoop, toNat_normalize, ← Nat.pow_add]
        have ⟨hge1, hlo, hhi⟩ := natBitLen_spec exp hexp
        have hmod : 2 ^ (natBitLen exp - 1) + exp % 2 ^ (natBitLen exp - 1) = exp := by
          have hpow : 2 ^ natBitLen exp = 2 * 2 ^ (natBitLen exp - 1) := by
            have heq : natBitLen exp = (natBitLen exp - 1) + 1 := by omega
            conv => lhs; rw [heq]
            rw [Nat.pow_succ, Nat.mul_comm]
          have hsub : exp - 2 ^ (natBitLen exp - 1) < 2 ^ (natBitLen exp - 1) := by omega
          rw [Nat.mod_eq_sub_mod hlo, Nat.mod_eq_of_lt hsub]
          omega
        rw [hmod]

end IxCC.BigNat
