import IxCC.BigNat.Mul
import IxCC.BigNat.Proof.Linear
import IxCC.BigNat.Proof.Toom3

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

/-! ### Karatsuba & Toom-Cook 3-Way Multiplication and Squaring -/

private theorem wf_mulKaratsubaLoop (a b : Array UInt64) (fuel : Nat) :
    WF (mulKaratsubaLoop a b fuel) := by
  cases fuel with
  | zero => exact wf_mulSchoolbook a b
  | succ fuel =>
    unfold mulKaratsubaLoop
    split
    · exact wf_mulSchoolbook a b
    · exact wf_karatsubaCombine _ _ _ _ _

theorem wf_mulKaratsuba (a b : Array UInt64) : WF (mulKaratsuba a b) :=
  wf_mulKaratsubaLoop a b _

private theorem toNat_mulKaratsubaLoop (a b : Array UInt64) (fuel : Nat) :
    toNat (mulKaratsubaLoop a b fuel) = toNat a * toNat b := by
  induction fuel generalizing a b with
  | zero => exact toNat_mulSchoolbook a b
  | succ fuel ih =>
    unfold mulKaratsubaLoop
    split
    · exact toNat_mulSchoolbook a b
    · dsimp only
      let n := if a.size ≤ b.size then b.size else a.size
      let m := n / 2
      let a0 := normalize (slice a 0 m)
      let a1 := normalize (slice a m a.size)
      let b0 := normalize (slice b 0 m)
      let b1 := normalize (slice b m b.size)
      let sA := add a0 a1
      let sB := add b0 b1
      have hz0 : toNat (mulKaratsubaLoop a0 b0 fuel) = toNat a0 * toNat b0 := ih a0 b0
      have hz2 : toNat (mulKaratsubaLoop a1 b1 fuel) = toNat a1 * toNat b1 := ih a1 b1
      have hzS : toNat (mulKaratsubaLoop sA sB fuel) = (toNat a0 + toNat a1) * (toNat b0 + toNat b1) := by
        rw [ih sA sB, toNat_add, toNat_add]
      have haSplit : toNat a = toNat a0 + toNat a1 * (2 ^ 64) ^ m := by
        simpa [a0, a1, toNat_normalize] using toNat_slice_split a m
      have hbSplit : toNat b = toNat b0 + toNat b1 * (2 ^ 64) ^ m := by
        simpa [b0, b1, toNat_normalize] using toNat_slice_split b m
      rw [haSplit, hbSplit]
      exact toNat_karatsubaCombine (mulKaratsubaLoop a0 b0 fuel) (mulKaratsubaLoop a1 b1 fuel)
        (mulKaratsubaLoop sA sB fuel) (toNat a0) (toNat a1) (toNat b0) (toNat b1)
        m (a.size + b.size) hz0 hz2 hzS

theorem toNat_mulKaratsuba (a b : Array UInt64) :
    toNat (mulKaratsuba a b) = toNat a * toNat b :=
  toNat_mulKaratsubaLoop a b _

private theorem wf_sqrKaratsubaLoop (a : Array UInt64) (fuel : Nat) :
    WF (sqrKaratsubaLoop a fuel) := by
  cases fuel with
  | zero => exact wf_sqrSchoolbook a
  | succ fuel =>
    unfold sqrKaratsubaLoop
    split
    · exact wf_sqrSchoolbook a
    · exact wf_karatsubaCombine _ _ _ _ _

theorem wf_sqrKaratsuba (a : Array UInt64) : WF (sqrKaratsuba a) :=
  wf_sqrKaratsubaLoop a a.size

private theorem toNat_sqrKaratsubaLoop (a : Array UInt64) (fuel : Nat) :
    toNat (sqrKaratsubaLoop a fuel) = toNat a * toNat a := by
  induction fuel generalizing a with
  | zero => exact toNat_sqrSchoolbook a
  | succ fuel ih =>
    unfold sqrKaratsubaLoop
    split
    · exact toNat_sqrSchoolbook a
    · dsimp only
      let m := a.size / 2
      let a0 := normalize (slice a 0 m)
      let a1 := normalize (slice a m a.size)
      let sA := add a0 a1
      have hz0 : toNat (sqrKaratsubaLoop a0 fuel) = toNat a0 * toNat a0 := ih a0
      have hz2 : toNat (sqrKaratsubaLoop a1 fuel) = toNat a1 * toNat a1 := ih a1
      have hzS : toNat (sqrKaratsubaLoop sA fuel) = (toNat a0 + toNat a1) * (toNat a0 + toNat a1) := by
        rw [ih sA, toNat_add]
      have haSplit : toNat a = toNat a0 + toNat a1 * (2 ^ 64) ^ m := by
        simpa [a0, a1, toNat_normalize] using toNat_slice_split a m
      rw [haSplit]
      exact toNat_karatsubaCombine (sqrKaratsubaLoop a0 fuel) (sqrKaratsubaLoop a1 fuel)
        (sqrKaratsubaLoop sA fuel) (toNat a0) (toNat a1) (toNat a0) (toNat a1)
        m (2 * a.size) hz0 hz2 hzS

theorem toNat_sqrKaratsuba (a : Array UInt64) :
    toNat (sqrKaratsuba a) = toNat a * toNat a :=
  toNat_sqrKaratsubaLoop a a.size

/-! ### Toom-Cook 3-Way Multiplication & Squaring (`mulToom3`, `sqrToom3`, `mul`, `sqr`) -/

private theorem toNat_slice_split3 (a : Array UInt64) (k : Nat) :
    toNat a = toNat (normalize (slice a 0 k)) +
      toNat (normalize (slice a k (2 * k))) * (2 ^ 64) ^ k +
      toNat (normalize (slice a (2 * k) a.size)) * (2 ^ 64) ^ (2 * k) := by
  simp only [toNat_normalize]
  have h1 := toNat_slice_split a k
  have h2 := toNat_slice_split (slice a k a.size) k
  have hmid : toNat (slice (slice a k a.size) 0 k) = toNat (slice a k (2 * k)) := by
    apply toNat_eq_of_getLimb
    intro i
    simp only [getLimb_slice, size_slice, Nat.min_self, Nat.zero_add]
    by_cases hi : i < min k (a.size - k)
    · have hlt1 : k + i < min (2 * k) a.size := by omega
      have hlt2 : k + i < a.size := by omega
      simp only [hi, hlt1, ↓reduceIte, hlt2]
    · have hge1 : ¬ k + i < min (2 * k) a.size := by omega
      simp only [hi, hge1, ↓reduceIte]
  have hhi : toNat (slice (slice a k a.size) k (slice a k a.size).size) =
      toNat (slice a (2 * k) a.size) := by
    apply toNat_eq_of_getLimb
    intro i
    simp only [getLimb_slice, size_slice, Nat.min_self]
    by_cases hi : k + i < a.size - k
    · have hlt3 : 2 * k + i < a.size := by omega
      have heq : k + (k + i) = 2 * k + i := by omega
      simp only [hi, hlt3, ↓reduceIte, heq]
    · have hge3 : ¬ 2 * k + i < a.size := by omega
      simp only [hi, hge3, ↓reduceIte]
  rw [hmid, hhi] at h2
  rw [h1, h2, Nat.add_mul, Nat.mul_assoc]
  have hpow2 : (2 ^ 64) ^ k * (2 ^ 64) ^ k = (2 ^ 64) ^ (2 * k) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hpow2, Nat.add_assoc]

private theorem toom3_eval_1 (a0 a1 a2 b0 b1 b2 : Nat) :
    (a0 + a2 + a1) * (b0 + b2 + b1) =
      a0 * b0 + (a0 * b1 + a1 * b0) + (a0 * b2 + a1 * b1 + a2 * b0) +
      (a1 * b2 + a2 * b1) + a2 * b2 := by
  repeat rw [Nat.add_mul]
  repeat rw [Nat.mul_add]
  omega

private theorem toom3_eval_2 (a0 a1 a2 b0 b1 b2 : Nat) :
    ((a2 * 2 + a1) * 2 + a0) * ((b2 * 2 + b1) * 2 + b0) =
      a0 * b0 + 2 * (a0 * b1 + a1 * b0) + 4 * (a0 * b2 + a1 * b1 + a2 * b0) +
      8 * (a1 * b2 + a2 * b1) + 16 * (a2 * b2) := by
  have ha : (a2 * 2 + a1) * 2 + a0 = a0 + 2 * a1 + 4 * a2 := by omega
  have hb : (b2 * 2 + b1) * 2 + b0 = b0 + 2 * b1 + 4 * b2 := by omega
  rw [ha, hb]
  repeat rw [Nat.add_mul]
  repeat rw [Nat.mul_add]
  have t1 : a0 * (2 * b1) = 2 * (a0 * b1) := by ac_rfl
  have t2 : a0 * (4 * b2) = 4 * (a0 * b2) := by ac_rfl
  have t3 : 2 * a1 * b0 = 2 * (a1 * b0) := by ac_rfl
  have t4 : 2 * a1 * (2 * b1) = 4 * (a1 * b1) := by
    calc 2 * a1 * (2 * b1) = (2 * 2) * (a1 * b1) := by ac_rfl
      _ = 4 * (a1 * b1) := rfl
  have t5 : 2 * a1 * (4 * b2) = 8 * (a1 * b2) := by
    calc 2 * a1 * (4 * b2) = (2 * 4) * (a1 * b2) := by ac_rfl
      _ = 8 * (a1 * b2) := rfl
  have t6 : 4 * a2 * b0 = 4 * (a2 * b0) := by ac_rfl
  have t7 : 4 * a2 * (2 * b1) = 8 * (a2 * b1) := by
    calc 4 * a2 * (2 * b1) = (4 * 2) * (a2 * b1) := by ac_rfl
      _ = 8 * (a2 * b1) := rfl
  have t8 : 4 * a2 * (4 * b2) = 16 * (a2 * b2) := by
    calc 4 * a2 * (4 * b2) = (4 * 4) * (a2 * b2) := by ac_rfl
      _ = 16 * (a2 * b2) := rfl
  rw [t1, t2, t3, t4, t5, t6, t7, t8]
  omega

private theorem toom3_eval_m1 {a0 a1 a2 b0 b1 b2 pm1 qm1 : Nat} {pa pb : Bool}
    (hpa : if pa then a0 + a2 + pm1 = a1 else a1 + pm1 = a0 + a2)
    (hpb : if pb then b0 + b2 + qm1 = b1 else b1 + qm1 = b0 + b2) :
    if (pa != pb) then
      pm1 * qm1 + (a0 * b0 + (a0 * b2 + a1 * b1 + a2 * b0) + a2 * b2) =
        (a0 * b1 + a1 * b0) + (a1 * b2 + a2 * b1)
    else
      pm1 * qm1 + ((a0 * b1 + a1 * b0) + (a1 * b2 + a2 * b1)) =
        a0 * b0 + (a0 * b2 + a1 * b1 + a2 * b0) + a2 * b2 := by
  have heven : a0 * b0 + (a0 * b2 + a1 * b1 + a2 * b0) + a2 * b2 =
      (a0 + a2) * (b0 + b2) + a1 * b1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have hodd : (a0 * b1 + a1 * b0) + (a1 * b2 + a2 * b1) =
      (a0 + a2) * b1 + a1 * (b0 + b2) := by
    rw [Nat.add_mul, Nat.mul_add]; omega
  rw [heven, hodd]
  cases pa <;> cases pb <;> simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, bne_iff_ne,
      ne_eq, Bool.false_eq_true, not_false_eq_true, Bool.true_eq_false] at hpa hpb ⊢
  · -- false, false: a0+a2 = a1+pm1, b0+b2 = b1+qm1
    rw [← hpa, ← hpb]
    repeat rw [Nat.add_mul]
    repeat rw [Nat.mul_add]
    omega
  · -- false, true: a0+a2 = a1+pm1, b1 = b0+b2+qm1
    rw [← hpa, ← hpb]
    repeat rw [Nat.add_mul]
    repeat rw [Nat.mul_add]
    omega
  · -- true, false: a1 = a0+a2+pm1, b0+b2 = b1+qm1
    rw [← hpa, ← hpb]
    repeat rw [Nat.add_mul]
    repeat rw [Nat.mul_add]
    omega
  · -- true, true: a1 = a0+a2+pm1, b1 = b0+b2+qm1
    rw [← hpa, ← hpb]
    repeat rw [Nat.add_mul]
    repeat rw [Nat.mul_add]
    omega

private theorem toom3_poly_ident (a0 a1 a2 b0 b1 b2 k : Nat) :
    a0 * b0 + (a0 * b1 + a1 * b0) * (2 ^ 64) ^ k +
      (a0 * b2 + a1 * b1 + a2 * b0) * (2 ^ 64) ^ (2 * k) +
      (a1 * b2 + a2 * b1) * (2 ^ 64) ^ (3 * k) +
      a2 * b2 * (2 ^ 64) ^ (4 * k) =
    (a0 + a1 * (2 ^ 64) ^ k + a2 * (2 ^ 64) ^ (2 * k)) *
      (b0 + b1 * (2 ^ 64) ^ k + b2 * (2 ^ 64) ^ (2 * k)) := by
  let X := (2 ^ 64) ^ k
  have h2 : (2 ^ 64) ^ (2 * k) = X * X := by
    show (2 ^ 64) ^ (2 * k) = (2 ^ 64) ^ k * (2 ^ 64) ^ k
    rw [← Nat.pow_add]; congr 1; omega
  have h3 : (2 ^ 64) ^ (3 * k) = X * (X * X) := by
    show (2 ^ 64) ^ (3 * k) = (2 ^ 64) ^ k * ((2 ^ 64) ^ k * (2 ^ 64) ^ k)
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have h4 : (2 ^ 64) ^ (4 * k) = (X * X) * (X * X) := by
    show (2 ^ 64) ^ (4 * k) = ((2 ^ 64) ^ k * (2 ^ 64) ^ k) * ((2 ^ 64) ^ k * (2 ^ 64) ^ k)
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  rw [h2, h3, h4]
  show a0 * b0 + (a0 * b1 + a1 * b0) * X + (a0 * b2 + a1 * b1 + a2 * b0) * (X * X) +
      (a1 * b2 + a2 * b1) * (X * (X * X)) + a2 * b2 * ((X * X) * (X * X)) =
    (a0 + a1 * X + a2 * (X * X)) * (b0 + b1 * X + b2 * (X * X))
  repeat rw [Nat.add_mul]
  repeat rw [Nat.mul_add]
  have t01 : a0 * (b1 * X) = a0 * b1 * X := (Nat.mul_assoc _ _ _).symm
  have t02 : a0 * (b2 * (X * X)) = a0 * b2 * (X * X) := (Nat.mul_assoc _ _ _).symm
  have t10 : a1 * X * b0 = a1 * b0 * X := by ac_rfl
  have t11 : a1 * X * (b1 * X) = a1 * b1 * (X * X) := by ac_rfl
  have t12 : a1 * X * (b2 * (X * X)) = a1 * b2 * (X * (X * X)) := by ac_rfl
  have t20 : a2 * (X * X) * b0 = a2 * b0 * (X * X) := by ac_rfl
  have t21 : a2 * (X * X) * (b1 * X) = a2 * b1 * (X * (X * X)) := by ac_rfl
  have t22 : a2 * (X * X) * (b2 * (X * X)) = a2 * b2 * ((X * X) * (X * X)) := by ac_rfl
  rw [t01, t02, t10, t11, t12, t20, t21, t22]
  omega

private theorem wf_mulToom3Loop (a b : Array UInt64) (fuel : Nat) :
    WF (mulToom3Loop a b fuel) := by
  cases fuel with
  | zero => exact wf_mulKaratsuba a b
  | succ fuel =>
    unfold mulToom3Loop
    split
    · exact wf_mulKaratsuba a b
    · dsimp only
      rcases hxy : (if a.size < b.size then (b, a) else (a, b)) with ⟨x, y⟩
      dsimp only
      split
      · exact wf_normalize _
      · exact wf_toom3Interp _ _ _ _ _ _ _ _

theorem wf_mulToom3 (a b : Array UInt64) : WF (mulToom3 a b) :=
  wf_mulToom3Loop a b _

private theorem toNat_mulToom3Loop (a b : Array UInt64) (fuel : Nat) :
    toNat (mulToom3Loop a b fuel) = toNat a * toNat b := by
  induction fuel generalizing a b with
  | zero => exact toNat_mulKaratsuba a b
  | succ fuel ih =>
    unfold mulToom3Loop
    split
    · exact toNat_mulKaratsuba a b
    · dsimp only
      have hxy_mul : ∀ (x y : Array UInt64), (if a.size < b.size then (b, a) else (a, b)) = (x, y) →
          toNat x * toNat y = toNat a * toNat b := by
        intro x y h
        split at h
        · cases h; exact Nat.mul_comm _ _
        · cases h; rfl
      rcases hxy : (if a.size < b.size then (b, a) else (a, b)) with ⟨x, y⟩
      have hprod_eq := hxy_mul x y hxy
      dsimp only
      let n := x.size
      let m := n / 2
      split
      · let x0 := normalize (slice x 0 m)
        let x1 := normalize (slice x m n)
        have hz0 := ih x0 y
        have hz1 := ih x1 y
        rw [toNat_normalize, toNat_addAtInPlace, toNat_copyIntoZeros, hz0, hz1, ← hprod_eq]
        have hxSplit : toNat x = toNat x0 + toNat x1 * (2 ^ 64) ^ m := by
          simpa [x0, x1, n, toNat_normalize] using toNat_slice_split x m
        rw [hxSplit, Nat.add_mul]
        have hcomm : toNat x1 * (2 ^ 64) ^ m * toNat y = toNat x1 * toNat y * (2 ^ 64) ^ m := by ac_rfl
        rw [hcomm]
      · let k := (n + 2) / 3
        rw [toom3EvalLoop_eq x k, toom3EvalLoop_eq y k]
        dsimp only
        let x0 := normalize (slice x 0 k)
        let x1 := normalize (slice x k (2 * k))
        let x2 := normalize (slice x (2 * k) n)
        let y0 := normalize (slice y 0 k)
        let y1 := normalize (slice y k (2 * k))
        let y2 := normalize (slice y (2 * k) y.size)
        let p02 := add x0 x2
        let p1  := add p02 x1
        let pm1Pair := signedSub p02 x1
        let p2  := add (shiftLeft1 (add (shiftLeft1 x2) x1)) x0
        let q02 := add y0 y2
        let q1  := add q02 y1
        let qm1Pair := signedSub q02 y1
        let q2  := add (shiftLeft1 (add (shiftLeft1 y2) y1)) y0
        have hr0 : toNat (mulToom3Loop x0 y0 fuel) = toNat x0 * toNat y0 := ih x0 y0
        have hrInf : toNat (mulToom3Loop x2 y2 fuel) = toNat x2 * toNat y2 := ih x2 y2
        have hr1 : toNat (mulToom3Loop p1 q1 fuel) =
            toNat x0 * toNat y0 + (toNat x0 * toNat y1 + toNat x1 * toNat y0) +
            (toNat x0 * toNat y2 + toNat x1 * toNat y1 + toNat x2 * toNat y0) +
            (toNat x1 * toNat y2 + toNat x2 * toNat y1) + toNat x2 * toNat y2 := by
          rw [ih p1 q1]
          simp only [p1, p02, q1, q02, toNat_add]
          exact toom3_eval_1 (toNat x0) (toNat x1) (toNat x2) (toNat y0) (toNat y1) (toNat y2)
        have hr2 : toNat (mulToom3Loop p2 q2 fuel) =
            toNat x0 * toNat y0 + 2 * (toNat x0 * toNat y1 + toNat x1 * toNat y0) +
            4 * (toNat x0 * toNat y2 + toNat x1 * toNat y1 + toNat x2 * toNat y0) +
            8 * (toNat x1 * toNat y2 + toNat x2 * toNat y1) + 16 * (toNat x2 * toNat y2) := by
          rw [ih p2 q2]
          simp only [p2, q2, toNat_add, toNat_shiftLeft1]
          exact toom3_eval_2 (toNat x0) (toNat x1) (toNat x2) (toNat y0) (toNat y1) (toNat y2)
        have hpa := (signedSub_spec (wf_add x0 x2) (wf_normalize (slice x k (2 * k)))).2
        have hpb := (signedSub_spec (wf_add y0 y2) (wf_normalize (slice y k (2 * k)))).2
        simp only [toNat_add] at hpa hpb
        have hrm1 : if (pm1Pair.1 != qm1Pair.1) then
              toNat (mulToom3Loop pm1Pair.2 qm1Pair.2 fuel) +
                (toNat x0 * toNat y0 + (toNat x0 * toNat y2 + toNat x1 * toNat y1 + toNat x2 * toNat y0) +
                  toNat x2 * toNat y2) =
                (toNat x0 * toNat y1 + toNat x1 * toNat y0) + (toNat x1 * toNat y2 + toNat x2 * toNat y1)
            else
              toNat (mulToom3Loop pm1Pair.2 qm1Pair.2 fuel) +
                ((toNat x0 * toNat y1 + toNat x1 * toNat y0) + (toNat x1 * toNat y2 + toNat x2 * toNat y1)) =
                toNat x0 * toNat y0 + (toNat x0 * toNat y2 + toNat x1 * toNat y1 + toNat x2 * toNat y0) +
                  toNat x2 * toNat y2 := by
          rw [ih pm1Pair.2 qm1Pair.2]
          exact toom3_eval_m1 hpa hpb
        have hinterp := (toom3Interp_spec (mulToom3Loop x0 y0 fuel) (mulToom3Loop p1 q1 fuel)
          (mulToom3Loop pm1Pair.2 qm1Pair.2 fuel) (mulToom3Loop p2 q2 fuel) (mulToom3Loop x2 y2 fuel)
          (pm1Pair.1 != qm1Pair.1) k (n + y.size)
          (toNat x0 * toNat y0)
          (toNat x0 * toNat y1 + toNat x1 * toNat y0)
          (toNat x0 * toNat y2 + toNat x1 * toNat y1 + toNat x2 * toNat y0)
          (toNat x1 * toNat y2 + toNat x2 * toNat y1)
          (toNat x2 * toNat y2) hr0 hrInf hr1 hrm1 hr2).2
        rw [hinterp, toom3_poly_ident, ← toNat_slice_split3 x k, ← toNat_slice_split3 y k, hprod_eq]

theorem toNat_mulToom3 (a b : Array UInt64) :
    toNat (mulToom3 a b) = toNat a * toNat b :=
  toNat_mulToom3Loop a b _

private theorem wf_sqrToom3Loop (a : Array UInt64) (fuel : Nat) :
    WF (sqrToom3Loop a fuel) := by
  cases fuel with
  | zero => exact wf_sqrKaratsuba a
  | succ fuel =>
    unfold sqrToom3Loop
    split
    · exact wf_sqrKaratsuba a
    · exact wf_toom3Interp _ _ _ _ _ _ _ _

theorem wf_sqrToom3 (a : Array UInt64) : WF (sqrToom3 a) :=
  wf_sqrToom3Loop a a.size

private theorem toNat_sqrToom3Loop (a : Array UInt64) (fuel : Nat) :
    toNat (sqrToom3Loop a fuel) = toNat a * toNat a := by
  induction fuel generalizing a with
  | zero => exact toNat_sqrKaratsuba a
  | succ fuel ih =>
    unfold sqrToom3Loop
    split
    · exact toNat_sqrKaratsuba a
    · dsimp only
      let k := (a.size + 2) / 3
      rw [toom3EvalLoop_eq a k]
      dsimp only
      let a0 := normalize (slice a 0 k)
      let a1 := normalize (slice a k (2 * k))
      let a2 := normalize (slice a (2 * k) a.size)
      let p02 := add a0 a2
      let p1  := add p02 a1
      let pm1Pair := signedSub p02 a1
      let p2  := add (shiftLeft1 (add (shiftLeft1 a2) a1)) a0
      have hr0 : toNat (sqrToom3Loop a0 fuel) = toNat a0 * toNat a0 := ih a0
      have hrInf : toNat (sqrToom3Loop a2 fuel) = toNat a2 * toNat a2 := ih a2
      have hr1 : toNat (sqrToom3Loop p1 fuel) =
          toNat a0 * toNat a0 + (toNat a0 * toNat a1 + toNat a1 * toNat a0) +
          (toNat a0 * toNat a2 + toNat a1 * toNat a1 + toNat a2 * toNat a0) +
          (toNat a1 * toNat a2 + toNat a2 * toNat a1) + toNat a2 * toNat a2 := by
        rw [ih p1]
        simp only [p1, p02, toNat_add]
        exact toom3_eval_1 (toNat a0) (toNat a1) (toNat a2) (toNat a0) (toNat a1) (toNat a2)
      have hr2 : toNat (sqrToom3Loop p2 fuel) =
          toNat a0 * toNat a0 + 2 * (toNat a0 * toNat a1 + toNat a1 * toNat a0) +
          4 * (toNat a0 * toNat a2 + toNat a1 * toNat a1 + toNat a2 * toNat a0) +
          8 * (toNat a1 * toNat a2 + toNat a2 * toNat a1) + 16 * (toNat a2 * toNat a2) := by
        rw [ih p2]
        simp only [p2, toNat_add, toNat_shiftLeft1]
        exact toom3_eval_2 (toNat a0) (toNat a1) (toNat a2) (toNat a0) (toNat a1) (toNat a2)
      have hpa := (signedSub_spec (wf_add a0 a2) (wf_normalize (slice a k (2 * k)))).2
      simp only [toNat_add] at hpa
      have hrm1 : if false then
            toNat (sqrToom3Loop pm1Pair.2 fuel) +
              (toNat a0 * toNat a0 + (toNat a0 * toNat a2 + toNat a1 * toNat a1 + toNat a2 * toNat a0) +
                toNat a2 * toNat a2) =
              (toNat a0 * toNat a1 + toNat a1 * toNat a0) + (toNat a1 * toNat a2 + toNat a2 * toNat a1)
          else
            toNat (sqrToom3Loop pm1Pair.2 fuel) +
              ((toNat a0 * toNat a1 + toNat a1 * toNat a0) + (toNat a1 * toNat a2 + toNat a2 * toNat a1)) =
              toNat a0 * toNat a0 + (toNat a0 * toNat a2 + toNat a1 * toNat a1 + toNat a2 * toNat a0) +
                toNat a2 * toNat a2 := by
        rw [ih pm1Pair.2]
        have hm := toom3_eval_m1 hpa hpa
        simpa [bne_self_eq_false] using hm
      have hinterp := (toom3Interp_spec (sqrToom3Loop a0 fuel) (sqrToom3Loop p1 fuel)
        (sqrToom3Loop pm1Pair.2 fuel) (sqrToom3Loop p2 fuel) (sqrToom3Loop a2 fuel)
        false k (2 * a.size)
        (toNat a0 * toNat a0)
        (toNat a0 * toNat a1 + toNat a1 * toNat a0)
        (toNat a0 * toNat a2 + toNat a1 * toNat a1 + toNat a2 * toNat a0)
        (toNat a1 * toNat a2 + toNat a2 * toNat a1)
        (toNat a2 * toNat a2) hr0 hrInf hr1 hrm1 hr2).2
      rw [hinterp, toom3_poly_ident, ← toNat_slice_split3 a k]

theorem toNat_sqrToom3 (a : Array UInt64) :
    toNat (sqrToom3 a) = toNat a * toNat a :=
  toNat_sqrToom3Loop a a.size

private theorem cmpLoop_eq_toNatPrefix (a b : Array UInt64) (k : Nat)
    (h : cmpLoop a b k = .eq) : toNatPrefix a k = toNatPrefix b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold cmpLoop at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hnotlt hnotgt
        have hle1 : (getLimb b k).toNat ≤ (getLimb a k).toNat :=
          Nat.le_of_not_lt (fun hlt => hnotlt (UInt64.lt_iff_toNat_lt.mpr hlt))
        have hle2 : (getLimb a k).toNat ≤ (getLimb b k).toNat :=
          Nat.le_of_not_lt (fun hgt => hnotgt (UInt64.lt_iff_toNat_lt.mpr hgt))
        rw [toNatPrefix_succ, toNatPrefix_succ, ih h, Nat.le_antisymm hle2 hle1]

private theorem toNat_eq_of_beq_same_size {a b : Array UInt64}
    (hsz : a.size = b.size) (hbeq : beq a b = true) : toNat a = toNat b := by
  unfold beq cmp at hbeq
  rw [hsz] at hbeq
  simp only [Nat.lt_irrefl, ↓reduceIte] at hbeq
  cases hc : cmpLoop a b b.size with
  | lt => rw [hc] at hbeq; simp at hbeq
  | gt => rw [hc] at hbeq; simp at hbeq
  | eq =>
    unfold toNat
    rw [hsz]
    exact cmpLoop_eq_toNatPrefix a b b.size hc

theorem wf_mul (a b : Array UInt64) : WF (mul a b) := by
  unfold mul
  split
  · exact wf_sqrToom3 a
  · exact wf_mulToom3 a b

theorem toNat_mul (a b : Array UInt64) : toNat (mul a b) = toNat a * toNat b := by
  unfold mul
  split
  · rename_i hcond
    have ⟨h12, hbeq⟩ := Bool.and_eq_true _ _ |>.mp hcond
    have ⟨hszb, _⟩ := Bool.and_eq_true _ _ |>.mp h12
    have hsz : a.size = b.size := eq_of_beq hszb
    rw [toNat_sqrToom3, toNat_eq_of_beq_same_size hsz hbeq]
  · exact toNat_mulToom3 a b

theorem wf_sqr (a : Array UInt64) : WF (sqr a) := wf_sqrToom3 a

theorem toNat_sqr (a : Array UInt64) : toNat (sqr a) = toNat a * toNat a :=
  toNat_sqrToom3 a

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
