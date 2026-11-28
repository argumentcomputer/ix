import IxCC.BigNat.Basic

/-! # Layer-1 Proofs for `IxCC.BigNat.Basic` (`IxCC.BigNat.Proof.Basic`)

Core algebraic properties of the little-endian `Array UInt64` representation:
limb accessors, `toNatPrefix` / `toNat` bounds, limb updates, slice splitting,
normal-form injectivity, `normalize`, `ofUInt64`, `ofSmall`, `ofNat`, `toSmall?`,
and exact bit-level characterization `testBit_toNat`.

All theorems depend strictly on Lean's standard axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace IxCC.BigNat

/-! ### Limb Accessor Lemmas -/

theorem getLimb_lt {xs : Array UInt64} {i : Nat} (h : i < xs.size) :
    getLimb xs i = xs[i] := by
  simp [getLimb, h]

theorem getLimb_ge {xs : Array UInt64} {i : Nat} (h : xs.size ≤ i) :
    getLimb xs i = 0 := by
  have hnot : ¬ i < xs.size := by omega
  simp [getLimb, hnot]

@[simp] theorem getLimb_empty (i : Nat) : getLimb #[] i = 0 := by
  simp [getLimb]

theorem getLimb_push (xs : Array UInt64) (v : UInt64) (i : Nat) :
    getLimb (xs.push v) i = if i = xs.size then v else getLimb xs i := by
  unfold getLimb
  by_cases heq : i = xs.size
  · subst heq
    simp
  · by_cases hlt : i < xs.size
    · have hlt' : i < (xs.push v).size := by simp; omega
      simp only [heq, hlt, hlt', ↓reduceIte, ↓reduceDIte, Array.getElem_push_lt hlt]
    · have hge' : ¬ i < (xs.push v).size := by simp; omega
      simp only [heq, hlt, hge', ↓reduceIte, ↓reduceDIte]

theorem getLimb_pop (xs : Array UInt64) (i : Nat) :
    getLimb xs.pop i = if i < xs.size - 1 then getLimb xs i else 0 := by
  unfold getLimb
  by_cases h : i < xs.size - 1
  · have h1 : i < xs.pop.size := by simp; omega
    have h2 : i < xs.size := by omega
    simp only [h, h1, h2, ↓reduceIte, ↓reduceDIte, Array.getElem_pop]
  · have h1 : ¬ i < xs.pop.size := by simp; omega
    simp only [h, h1, ↓reduceIte, ↓reduceDIte]

theorem getLimb_setLimb (xs : Array UInt64) (i : Nat) (v : UInt64) (hi : i < xs.size) (j : Nat) :
    getLimb (setLimb xs i v) j = if j = i then v else getLimb xs j := by
  unfold setLimb getLimb
  simp only [hi, ↓reduceDIte, Array.size_set]
  by_cases hji : j = i
  · subst hji
    simp [hi]
  · by_cases hj : j < xs.size
    · simp only [hji, hj, ↓reduceIte, ↓reduceDIte]
      exact Array.getElem_set_ne hi hj (Ne.symm hji)
    · simp only [hji, hj, ↓reduceIte, ↓reduceDIte]

theorem getLimb_mkZerosLoop (rem : Nat) (acc : Array UInt64) (i : Nat) :
    getLimb (mkZerosLoop rem acc) i = if i < acc.size then getLimb acc i else 0 := by
  induction rem generalizing acc with
  | zero =>
    simp only [mkZerosLoop]
    split
    · rfl
    · exact getLimb_ge (by omega)
  | succ k ih =>
    simp only [mkZerosLoop, ih, Array.size_push]
    by_cases h1 : i < acc.size
    · have h2 : i < acc.size + 1 := by omega
      have hne : i ≠ acc.size := by omega
      simp [h1, h2, getLimb_push, hne]
    · by_cases h2 : i = acc.size
      · subst h2
        simp [getLimb_push]
      · have h3 : ¬ i < acc.size + 1 := by omega
        simp [h1, h3]

@[simp] theorem getLimb_mkZeros (n i : Nat) : getLimb (mkZeros n) i = 0 := by
  simp [mkZeros, getLimb_mkZerosLoop]

theorem getLimb_padZerosLoop (rem : Nat) (xs : Array UInt64) (i : Nat) :
    getLimb (padZerosLoop rem xs) i = getLimb xs i := by
  induction rem generalizing xs with
  | zero => simp [padZerosLoop]
  | succ k ih =>
    simp only [padZerosLoop, ih, getLimb_push]
    split
    · rename_i heq
      subst heq
      exact (getLimb_ge (Nat.le_refl _)).symm
    · rfl

@[simp] theorem getLimb_padZeros (xs : Array UInt64) (target i : Nat) :
    getLimb (padZeros xs target) i = getLimb xs i := by
  unfold padZeros
  split
  · rename_i h0
    have hz : xs.size = 0 := eq_of_beq h0
    rw [getLimb_mkZeros, getLimb_ge (by omega)]
  · split
    · exact getLimb_padZerosLoop _ _ _
    · rfl

theorem getLimb_sliceLoop (xs : Array UInt64) (idx rem : Nat) (acc : Array UInt64) (i : Nat) :
    getLimb (sliceLoop xs idx rem acc) i =
      if i < acc.size then getLimb acc i
      else if i < acc.size + rem then getLimb xs (idx + (i - acc.size))
      else 0 := by
  induction rem generalizing idx acc with
  | zero =>
    simp only [sliceLoop, Nat.add_zero]
    split
    · rfl
    · rename_i h; exact getLimb_ge (by omega)
  | succ k ih =>
    simp only [sliceLoop, ih, Array.size_push]
    by_cases h1 : i < acc.size
    · have h2 : i < acc.size + 1 := by omega
      have hne : i ≠ acc.size := by omega
      simp only [h1, h2, ↓reduceIte, getLimb_push, hne]
    · by_cases h2 : i = acc.size
      · subst h2
        have hlt : acc.size < acc.size + (k + 1) := by omega
        have hlt1 : acc.size < acc.size + 1 := by omega
        simp only [h1, hlt1, hlt, ↓reduceIte, getLimb_push, Nat.sub_self, Nat.add_zero]
      · have h3 : ¬ i < acc.size + 1 := by omega
        have h4 : (i < acc.size + 1 + k) ↔ (i < acc.size + (k + 1)) := by omega
        simp only [h1, h3, ↓reduceIte, h4]
        split
        · congr 1; omega
        · rfl

theorem getLimb_slice (xs : Array UInt64) (lo hi i : Nat) :
    getLimb (slice xs lo hi) i = if lo + i < min hi xs.size then getLimb xs (lo + i) else 0 := by
  unfold slice
  dsimp only
  split
  · rename_i hle
    split
    · rename_i hlo
      rw [getLimb_sliceLoop]
      simp only [size_mkEmpty, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add, Nat.sub_zero]
      have hmin : min hi xs.size = hi := Nat.min_eq_left hle
      rw [hmin]
      have hiff : (i < hi - lo) ↔ (lo + i < hi) := by omega
      simp [hiff]
    · rename_i hlo
      have hmin : min hi xs.size = hi := Nat.min_eq_left hle
      rw [hmin]
      have hge : ¬ lo + i < hi := by omega
      simp [hge]
  · rename_i hgt
    split
    · rename_i hlo
      rw [getLimb_sliceLoop]
      simp only [size_mkEmpty, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add, Nat.sub_zero]
      have hmin : min hi xs.size = xs.size := Nat.min_eq_right (by omega)
      rw [hmin]
      have hiff : (i < xs.size - lo) ↔ (lo + i < xs.size) := by omega
      simp [hiff]
    · rename_i hlo
      have hmin : min hi xs.size = xs.size := Nat.min_eq_right (by omega)
      rw [hmin]
      have hge : ¬ lo + i < xs.size := by omega
      simp [hge]

/-! ### Core `toNatPrefix` and `toNat` Properties -/

@[simp] theorem toNatPrefix_zero (xs : Array UInt64) : toNatPrefix xs 0 = 0 := rfl

theorem toNatPrefix_succ (xs : Array UInt64) (k : Nat) :
    toNatPrefix xs (k + 1) = toNatPrefix xs k + (getLimb xs k).toNat * (2 ^ 64) ^ k := rfl

theorem toNatPrefix_lt (xs : Array UInt64) (k : Nat) :
    toNatPrefix xs k < (2 ^ 64) ^ k := by
  induction k with
  | zero => simp [toNatPrefix]
  | succ k ih =>
    rw [toNatPrefix_succ, Nat.pow_succ]
    have hl : (getLimb xs k).toNat < 2 ^ 64 := uint64_toNat_lt _
    have h1 : (getLimb xs k).toNat + 1 ≤ 2 ^ 64 := hl
    have h2 : ((getLimb xs k).toNat + 1) * (2 ^ 64) ^ k ≤ (2 ^ 64) ^ k * 2 ^ 64 := by
      rw [Nat.mul_comm ((2 ^ 64) ^ k)]
      exact Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    have h3 : toNatPrefix xs k + (getLimb xs k).toNat * (2 ^ 64) ^ k <
        (2 ^ 64) ^ k + (getLimb xs k).toNat * (2 ^ 64) ^ k :=
      Nat.add_lt_add_right ih _
    exact Nat.lt_of_lt_of_le (by rw [Nat.add_comm] at h3; exact Nat.lt_of_lt_of_le (by rw [Nat.add_comm]; exact h3) (Nat.le_refl _)) (by rw [Nat.add_comm]; exact h2)

theorem toNat_lt (xs : Array UInt64) : toNat xs < (2 ^ 64) ^ xs.size :=
  toNatPrefix_lt xs xs.size

theorem toNatPrefix_congr {xs ys : Array UInt64} {k : Nat}
    (h : ∀ i < k, getLimb xs i = getLimb ys i) :
    toNatPrefix xs k = toNatPrefix ys k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [toNatPrefix_succ, toNatPrefix_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem toNatPrefix_eq_toNat_of_le (xs : Array UInt64) {k : Nat} (hk : xs.size ≤ k) :
    toNatPrefix xs k = toNat xs := by
  induction k with
  | zero =>
    have hsz : xs.size = 0 := by omega
    simp [toNat, hsz]
  | succ k ih =>
    by_cases heq : xs.size = k + 1
    · simp [toNat, heq]
    · have hle : xs.size ≤ k := by omega
      rw [toNatPrefix_succ, ih hle, getLimb_ge hle]
      simp

theorem toNat_eq_of_getLimb {xs ys : Array UInt64} (h : ∀ i, getLimb xs i = getLimb ys i) :
    toNat xs = toNat ys := by
  let m := max xs.size ys.size
  rw [← toNatPrefix_eq_toNat_of_le xs (Nat.le_max_left _ _),
      ← toNatPrefix_eq_toNat_of_le ys (Nat.le_max_right _ _)]
  exact toNatPrefix_congr (fun i _ => h i)

@[simp] theorem toNat_zero : toNat zero = 0 := rfl

@[simp] theorem toNat_empty : toNat #[] = 0 := rfl

@[simp] theorem toNat_mkEmpty (n : Nat) : toNat (Array.mkEmpty (α := UInt64) n) = 0 := rfl

@[simp] theorem toNat_one : toNat one = 1 := by
  decide

theorem wf_zero : WF zero := Or.inl rfl

theorem wf_one : WF one := Or.inr (by decide)

theorem toNat_push (xs : Array UInt64) (v : UInt64) :
    toNat (xs.push v) = toNat xs + v.toNat * (2 ^ 64) ^ xs.size := by
  unfold toNat
  rw [Array.size_push, toNatPrefix_succ, getLimb_push]
  simp only [↓reduceIte]
  congr 1
  exact toNatPrefix_congr (fun i hi => by rw [getLimb_push]; simp [Nat.ne_of_lt hi])

theorem toNat_pop_of_zero (xs : Array UInt64) (hpos : 0 < xs.size)
    (hz : getLimb xs (xs.size - 1) = 0) :
    toNat xs.pop = toNat xs := by
  apply toNat_eq_of_getLimb
  intro i
  rw [getLimb_pop]
  split
  · rfl
  · rename_i hge
    by_cases heq : i = xs.size - 1
    · rw [heq, hz]
    · exact (getLimb_ge (by omega)).symm

@[simp] theorem toNat_mkZeros (n : Nat) : toNat (mkZeros n) = 0 := by
  rw [← toNat_empty]
  exact toNat_eq_of_getLimb (fun i => by simp)

@[simp] theorem toNat_padZeros (xs : Array UInt64) (target : Nat) :
    toNat (padZeros xs target) = toNat xs :=
  toNat_eq_of_getLimb (fun i => getLimb_padZeros xs target i)

theorem toNatPrefix_setLimb (xs : Array UInt64) (i k : Nat) (v : UInt64)
    (hik : i < k) (his : i < xs.size) :
    toNatPrefix (setLimb xs i v) k + (getLimb xs i).toNat * (2 ^ 64) ^ i =
      toNatPrefix xs k + v.toNat * (2 ^ 64) ^ i := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [toNatPrefix_succ, toNatPrefix_succ, getLimb_setLimb xs i v his]
    by_cases hki : k = i
    · subst hki
      have hcongr : toNatPrefix (setLimb xs k v) k = toNatPrefix xs k :=
        toNatPrefix_congr (fun j hj => by
          rw [getLimb_setLimb xs k v his]
          simp [Nat.ne_of_lt hj])
      simp [hcongr]
      omega
    · simp only [hki, ↓reduceIte]
      have := ih (by omega)
      omega

theorem toNat_setLimb (xs : Array UInt64) (i : Nat) (v : UInt64) (hi : i < xs.size) :
    toNat (setLimb xs i v) + (getLimb xs i).toNat * (2 ^ 64) ^ i =
      toNat xs + v.toNat * (2 ^ 64) ^ i := by
  unfold toNat
  rw [size_setLimb]
  exact toNatPrefix_setLimb xs i xs.size v hi hi

theorem toNat_setLimb_of_zero (xs : Array UInt64) (i : Nat) (v : UInt64)
    (hi : i < xs.size) (hz : getLimb xs i = 0) :
    toNat (setLimb xs i v) = toNat xs + v.toNat * (2 ^ 64) ^ i := by
  have h := toNat_setLimb xs i v hi
  rw [hz] at h
  simpa using h

theorem toNatPrefix_mono (xs : Array UInt64) {k1 k2 : Nat} (h : k1 ≤ k2) :
    toNatPrefix xs k1 ≤ toNatPrefix xs k2 := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rw [toNatPrefix_succ]
    omega

theorem toNat_ge_limb (xs : Array UInt64) (k : Nat) :
    (getLimb xs k).toNat * (2 ^ 64) ^ k ≤ toNat xs := by
  by_cases hk : k < xs.size
  · have h1 := toNatPrefix_mono xs (show k + 1 ≤ xs.size by omega)
    rw [toNatPrefix_succ] at h1
    unfold toNat
    omega
  · rw [getLimb_ge (by omega)]
    simp

theorem toNat_ge_top (xs : Array UInt64) (hwf : WF xs) (hpos : 0 < xs.size) :
    (2 ^ 64) ^ (xs.size - 1) ≤ toNat xs := by
  rcases hwf with h0 | hne
  · omega
  · have h1 := toNat_ge_limb xs (xs.size - 1)
    have hgt : 1 ≤ (getLimb xs (xs.size - 1)).toNat := by
      have : (getLimb xs (xs.size - 1)).toNat ≠ 0 := fun hz =>
        hne (UInt64.toNat_inj.mp (by simpa using hz))
      omega
    have h2 : (2 ^ 64) ^ (xs.size - 1) ≤ (getLimb xs (xs.size - 1)).toNat * (2 ^ 64) ^ (xs.size - 1) :=
      Nat.le_mul_of_pos_left _ hgt
    omega

theorem toNat_eq_zero_iff (xs : Array UInt64) (hwf : WF xs) :
    toNat xs = 0 ↔ xs.size = 0 := by
  constructor
  · intro hz
    apply Classical.byContradiction; intro hne
    have hpos : 0 < xs.size := Nat.pos_of_ne_zero hne
    have hge := toNat_ge_top xs hwf hpos
    have hpow : 0 < (2 ^ 64) ^ (xs.size - 1) := Nat.pow_pos (Nat.two_pow_pos 64)
    omega
  · intro hsz
    simp [toNat, hsz]

theorem toNat_pos_of_ne_zero (xs : Array UInt64) (hwf : WF xs) (hne : xs.size ≠ 0) :
    0 < toNat xs := by
  have h : toNat xs ≠ 0 := fun hz => hne ((toNat_eq_zero_iff xs hwf).mp hz)
  omega

/-! ### Prefix Splitting & Slice Splitting -/

theorem toNatPrefix_add (xs : Array UInt64) (m k : Nat) :
    toNatPrefix xs (m + k) =
      toNatPrefix xs m + toNatPrefix (slice xs m (m + k)) k * (2 ^ 64) ^ m := by
  induction k with
  | zero => simp [toNatPrefix]
  | succ k ih =>
    have hmk : m + (k + 1) = (m + k) + 1 := by omega
    have hcongr : toNatPrefix (slice xs m (m + k)) k = toNatPrefix (slice xs m (m + (k + 1))) k := by
      apply toNatPrefix_congr
      intro i hi
      rw [getLimb_slice, getLimb_slice]
      by_cases hxs : m + i < xs.size
      · have h1 : m + i < min (m + k) xs.size := by omega
        have h2 : m + i < min (m + (k + 1)) xs.size := by omega
        simp [h1, h2]
      · have h1 : ¬ m + i < min (m + k) xs.size := by omega
        have h2 : ¬ m + i < min (m + (k + 1)) xs.size := by omega
        simp [h1, h2]
    have htop : getLimb (slice xs m (m + (k + 1))) k = getLimb xs (m + k) := by
      rw [getLimb_slice]
      by_cases hxs : m + k < xs.size
      · have h1 : m + k < min (m + (k + 1)) xs.size := by omega
        simp [h1]
      · have h1 : ¬ m + k < min (m + (k + 1)) xs.size := by omega
        have hge : xs.size ≤ m + k := by omega
        simp only [h1, ↓reduceIte]
        exact (getLimb_ge hge).symm
    conv => lhs; rw [hmk]
    rw [toNatPrefix_succ, ih, hcongr, toNatPrefix_succ, htop, Nat.add_mul, Nat.mul_assoc,
        ← Nat.pow_add, Nat.add_comm k m, Nat.add_assoc]

theorem toNat_slice_split (xs : Array UInt64) (m : Nat) :
    toNat xs = toNat (slice xs 0 m) + toNat (slice xs m xs.size) * (2 ^ 64) ^ m := by
  by_cases hm : m ≤ xs.size
  · have hsz : xs.size = m + (xs.size - m) := by omega
    have h1 := toNatPrefix_add xs m (xs.size - m)
    rw [← hsz] at h1
    have hlow : toNat (slice xs 0 m) = toNatPrefix xs m := by
      have hmin : (slice xs 0 m).size = m := by rw [size_slice]; omega
      unfold toNat
      rw [hmin]
      apply toNatPrefix_congr
      intro i hi
      rw [getLimb_slice]
      have hlt : i < min m xs.size := by omega
      simp only [Nat.zero_add, hlt, ↓reduceIte]
    have hhigh : toNat (slice xs m xs.size) = toNatPrefix (slice xs m xs.size) (xs.size - m) := by
      unfold toNat
      rw [size_slice]
      simp
    rw [hlow, hhigh]
    exact h1
  · have hlow : toNat (slice xs 0 m) = toNat xs := by
      apply toNat_eq_of_getLimb
      intro i
      rw [getLimb_slice]
      have hmin : min m xs.size = xs.size := Nat.min_eq_right (by omega)
      rw [hmin, Nat.zero_add]
      split
      · rfl
      · exact (getLimb_ge (by omega)).symm
    have hhigh : (slice xs m xs.size).size = 0 := by
      rw [size_slice]; omega
    rw [hlow]
    unfold toNat
    rw [hhigh, toNatPrefix_zero]
    simp

/-! ### Injectivity of `toNatPrefix` and `toNat` on `WF` Arrays -/

theorem toNatPrefix_inj {xs ys : Array UInt64} {k : Nat}
    (h : toNatPrefix xs k = toNatPrefix ys k) :
    ∀ i < k, getLimb xs i = getLimb ys i := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    rw [toNatPrefix_succ, toNatPrefix_succ] at h
    have hltX : toNatPrefix xs k < (2 ^ 64) ^ k := toNatPrefix_lt xs k
    have hltY : toNatPrefix ys k < (2 ^ 64) ^ k := toNatPrefix_lt ys k
    have hpow : 0 < (2 ^ 64) ^ k := Nat.pow_pos (Nat.two_pow_pos 64)
    have hdiv : (getLimb xs k).toNat = (getLimb ys k).toNat := by
      have h1 : (toNatPrefix xs k + (getLimb xs k).toNat * (2 ^ 64) ^ k) / (2 ^ 64) ^ k =
          (getLimb xs k).toNat := by
        rw [Nat.add_mul_div_right _ _ hpow, Nat.div_eq_of_lt hltX, Nat.zero_add]
      have h2 : (toNatPrefix ys k + (getLimb ys k).toNat * (2 ^ 64) ^ k) / (2 ^ 64) ^ k =
          (getLimb ys k).toNat := by
        rw [Nat.add_mul_div_right _ _ hpow, Nat.div_eq_of_lt hltY, Nat.zero_add]
      rw [← h1, h, h2]
    have hlimb : getLimb xs k = getLimb ys k := UInt64.toNat_inj.mp hdiv
    have hpref : toNatPrefix xs k = toNatPrefix ys k := by
      rw [hdiv] at h
      omega
    intro i hi
    by_cases hik : i = k
    · subst hik; exact hlimb
    · exact ih hpref i (by omega)

theorem size_eq_of_wf_toNat_eq {a b : Array UInt64} (ha : WF a) (hb : WF b)
    (heq : toNat a = toNat b) : a.size = b.size := by
  apply Classical.byContradiction; intro hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : toNat a < (2 ^ 64) ^ a.size := toNat_lt a
    have h2 : (2 ^ 64) ^ (b.size - 1) ≤ toNat b := toNat_ge_top b hb (by omega)
    have h3 : (2 ^ 64) ^ a.size ≤ (2 ^ 64) ^ (b.size - 1) :=
      Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
    omega
  · have h1 : toNat b < (2 ^ 64) ^ b.size := toNat_lt b
    have h2 : (2 ^ 64) ^ (a.size - 1) ≤ toNat a := toNat_ge_top a ha (by omega)
    have h3 : (2 ^ 64) ^ b.size ≤ (2 ^ 64) ^ (a.size - 1) :=
      Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
    omega

theorem toNat_inj {a b : Array UInt64} (ha : WF a) (hb : WF b)
    (heq : toNat a = toNat b) : a = b := by
  have hsz : a.size = b.size := size_eq_of_wf_toNat_eq ha hb heq
  apply Array.ext
  · exact hsz
  · intro i hiA hiB
    unfold toNat at heq
    rw [hsz] at heq
    have hget := toNatPrefix_inj heq i hiB
    rw [getLimb_lt hiA, getLimb_lt hiB] at hget
    exact hget

/-! ### `normalize`, `ofUInt64`, `ofSmall`, `ofNat`, `toSmall?` Specifications -/

theorem wf_normalize (xs : Array UInt64) : WF (normalize xs) := by
  induction h : xs.size generalizing xs with
  | zero =>
    unfold normalize
    simp only [h, Nat.lt_irrefl, ↓reduceDIte]
    exact Or.inl h
  | succ n ih =>
    unfold normalize
    have hpos : 0 < xs.size := by omega
    simp only [hpos, ↓reduceDIte]
    split
    · exact ih xs.pop (by simp [h])
    · rename_i hne
      right
      rw [getLimb_lt (by omega)]
      intro hz
      exact hne (by simp [hz])

theorem toNat_normalize (xs : Array UInt64) : toNat (normalize xs) = toNat xs := by
  induction h : xs.size generalizing xs with
  | zero =>
    unfold normalize
    simp [h]
  | succ n ih =>
    unfold normalize
    have hpos : 0 < xs.size := by omega
    simp only [hpos, ↓reduceDIte]
    split
    · rename_i hz
      rw [ih xs.pop (by simp [h])]
      apply toNat_pop_of_zero xs hpos
      rw [getLimb_lt (by omega)]
      exact eq_of_beq hz
    · rfl

theorem normalize_of_wf {xs : Array UInt64} (hwf : WF xs) : normalize xs = xs :=
  toNat_inj (wf_normalize xs) hwf (toNat_normalize xs)

theorem wf_ofUInt64 (x : UInt64) : WF (ofUInt64 x) := by
  unfold ofUInt64
  split
  · exact Or.inl rfl
  · rename_i hne
    right
    simp only [Array.size_singleton, Nat.sub_self, getLimb]
    intro hz
    simp only [Nat.zero_lt_one, ↓reduceDIte, List.getElem_toArray, List.getElem_cons_zero] at hz
    exact hne (by simp [hz])

theorem toNat_ofUInt64 (x : UInt64) : toNat (ofUInt64 x) = x.toNat := by
  unfold ofUInt64
  split
  · rename_i hz
    have h : x = 0 := eq_of_beq hz
    subst h
    rfl
  · simp [toNat, toNatPrefix, getLimb]

theorem wf_ofSmall (n : Nat) : WF (ofSmall n) := wf_ofUInt64 _

theorem toNat_ofSmall (n : Nat) (hn : n < 2 ^ 64) : toNat (ofSmall n) = n := by
  unfold ofSmall
  rw [toNat_ofUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem wf_ofNatLoop (n : Nat) (acc : Array UInt64)
    (h : n = 0 → WF acc) : WF (ofNatLoop n acc) := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    unfold ofNatLoop
    split
    · rename_i hz; exact h hz
    · rename_i hne
      have hlt : n >>> 64 < n := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hne) (by omega)
      apply ih (n >>> 64) hlt (acc.push (UInt64.ofNat n))
      intro hdiv0
      right
      rw [Array.size_push, Nat.add_sub_cancel, getLimb_push]
      simp only [↓reduceIte]
      intro hz
      have hmod0 : n % 2 ^ 64 = 0 := by
        have := congrArg UInt64.toNat hz
        simpa [UInt64.toNat_ofNat'] using this
      rw [Nat.shiftRight_eq_div_pow] at hdiv0
      have hdm := Nat.div_add_mod n (2 ^ 64)
      rw [hdiv0, hmod0] at hdm
      omega

theorem toNat_ofNatLoop (n : Nat) (acc : Array UInt64) :
    toNat (ofNatLoop n acc) = toNat acc + n * (2 ^ 64) ^ acc.size := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    unfold ofNatLoop
    split
    · rename_i hz; subst hz; simp
    · rename_i hne
      have hlt : n >>> 64 < n := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hne) (by omega)
      rw [ih (n >>> 64) hlt (acc.push (UInt64.ofNat n)), toNat_push, Array.size_push,
          Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat', Nat.pow_succ]
      have hdm : 2 ^ 64 * (n / 2 ^ 64) + n % 2 ^ 64 = n := Nat.div_add_mod n (2 ^ 64)
      calc toNat acc + (n % 2 ^ 64) * (2 ^ 64) ^ acc.size +
            (n / 2 ^ 64) * ((2 ^ 64) ^ acc.size * 2 ^ 64)
          = toNat acc + (n % 2 ^ 64 + 2 ^ 64 * (n / 2 ^ 64)) * (2 ^ 64) ^ acc.size := by
            rw [Nat.add_assoc, Nat.add_mul]
            congr 1; congr 1
            rw [Nat.mul_comm ((2 ^ 64) ^ acc.size) (2 ^ 64), ← Nat.mul_assoc,
                Nat.mul_comm (n / 2 ^ 64) (2 ^ 64)]
        _ = toNat acc + n * (2 ^ 64) ^ acc.size := by rw [Nat.add_comm (n % 2 ^ 64), hdm]

theorem wf_ofNat (n : Nat) : WF (ofNat n) :=
  wf_ofNatLoop n #[] (fun _ => Or.inl rfl)

theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  unfold ofNat
  rw [toNat_ofNatLoop]
  simp

theorem uint64_shiftRight63_eq_zero_iff (v : UInt64) :
    ((v >>> (63 : UInt64)) == 0) = true ↔ v.toNat < 2 ^ 63 := by
  have hsr : (v >>> (63 : UInt64)).toNat = v.toNat / 2 ^ 63 := by
    rw [UInt64.toNat_shiftRight]
    have h63 : (63 : UInt64).toNat % 64 = 63 := by decide
    rw [h63, Nat.shiftRight_eq_div_pow]
  constructor
  · intro h
    have hz : v >>> (63 : UInt64) = 0 := eq_of_beq h
    have hz' : (v >>> (63 : UInt64)).toNat = 0 := by rw [hz]; rfl
    rw [hsr] at hz'
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos 63)).mp hz'
  · intro hlt
    have hz' : (v >>> (63 : UInt64)).toNat = 0 := by
      rw [hsr]
      exact Nat.div_eq_of_lt hlt
    have hz : v >>> (63 : UInt64) = 0 := UInt64.toNat_inj.mp hz'
    simp [hz]

theorem toSmall?_spec (xs : Array UInt64) (hwf : WF xs) :
    toSmall? xs = if toNat xs < 2 ^ 63 then some (toNat xs) else none := by
  unfold toSmall?
  by_cases h0 : xs.size = 0
  · simp [h0, toNat]
  · simp only [h0, ↓reduceDIte]
    by_cases h1 : xs.size = 1
    · have h1b : (xs.size == 1) = true := beq_iff_eq.mpr h1
      simp only [h1b, ↓reduceIte]
      have hto : toNat xs = (xs[0]'(Nat.pos_of_ne_zero h0)).toNat := by
        have htop : toNatPrefix xs xs.size = toNatPrefix xs 1 := by rw [h1]
        unfold toNat
        rw [htop, toNatPrefix_succ, toNatPrefix_zero, getLimb_lt (by omega)]
        simp
      rw [hto]
      by_cases hlt : (xs[0]'(Nat.pos_of_ne_zero h0)).toNat < 2 ^ 63
      · have hsr := (uint64_shiftRight63_eq_zero_iff _).mpr hlt
        simp [hlt, hsr]
      · have hsr : ((xs[0]'(Nat.pos_of_ne_zero h0)) >>> (63 : UInt64) == 0) = false := by
          cases hval : ((xs[0]'(Nat.pos_of_ne_zero h0)) >>> (63 : UInt64) == 0)
          · rfl
          · exact absurd ((uint64_shiftRight63_eq_zero_iff _).mp hval) hlt
        simp [hlt, hsr]
    · have h1b : (xs.size == 1) = false := beq_false_of_ne h1
      simp only [h1b, Bool.false_eq_true, ↓reduceIte]
      have hge2 : 2 ≤ xs.size := by omega
      have htop : (2 ^ 64) ^ (xs.size - 1) ≤ toNat xs := toNat_ge_top xs hwf (by omega)
      have hpow : 2 ^ 64 ≤ (2 ^ 64) ^ (xs.size - 1) := by
        calc 2 ^ 64 = (2 ^ 64) ^ 1 := (Nat.pow_one _).symm
          _ ≤ (2 ^ 64) ^ (xs.size - 1) := Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
      have hnot : ¬ toNat xs < 2 ^ 63 := by omega
      simp [hnot]

/-! ### Exact Bit-Level Characterization (`testBit_toNatPrefix`, `testBit_toNat`) -/

private theorem two_pow_64_pow (k : Nat) : (2 ^ 64) ^ k = 2 ^ (64 * k) := by
  rw [← Nat.pow_mul]

theorem testBit_eq_false_of_lt_pow {n i : Nat} (h : n < 2 ^ i) : n.testBit i = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt h]
  rfl

private theorem testBit_add_mul_two_pow {a b s bit : Nat} (ha : a < 2 ^ s) :
    (a + b * 2 ^ s).testBit bit =
      if bit < s then a.testBit bit else b.testBit (bit - s) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hlt : bit < s
  · simp only [hlt, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
    have hs : 2 ^ s = 2 ^ bit * 2 ^ (s - bit) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
    have hdvd : 2 ∣ 2 ^ (s - bit) := by
      have hpos : 1 ≤ s - bit := by omega
      have : 2 ^ (s - bit) = 2 * 2 ^ (s - bit - 1) := by
        conv => lhs; rw [show s - bit = (s - bit - 1) + 1 by omega]
        rw [Nat.pow_succ, Nat.mul_comm]
      exact ⟨2 ^ (s - bit - 1), this⟩
    rcases hdvd with ⟨q, hq⟩
    rw [hs, ← Nat.mul_assoc, Nat.mul_comm b (2 ^ bit), Nat.mul_assoc (2 ^ bit) b,
        Nat.mul_comm (2 ^ bit), Nat.add_mul_div_right _ _ (Nat.two_pow_pos bit),
        hq, ← Nat.mul_assoc, Nat.mul_comm b 2, Nat.mul_assoc 2 b q, Nat.add_mul_mod_self_left]
  · simp only [hlt, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
    have hge : s ≤ bit := by omega
    have hbit : 2 ^ bit = 2 ^ s * 2 ^ (bit - s) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
    rw [hbit, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos s),
        Nat.div_eq_of_lt ha, Nat.zero_add]

theorem testBit_toNatPrefix (xs : Array UInt64) (k bit : Nat) :
    (toNatPrefix xs k).testBit bit =
      if bit / 64 < k then (getLimb xs (bit / 64)).toNat.testBit (bit % 64) else false := by
  induction k with
  | zero => simp [toNatPrefix]
  | succ k ih =>
    rw [toNatPrefix_succ, two_pow_64_pow]
    have hlt : toNatPrefix xs k < 2 ^ (64 * k) := by
      rw [← two_pow_64_pow]
      exact toNatPrefix_lt xs k
    rw [testBit_add_mul_two_pow hlt]
    by_cases hbit : bit < 64 * k
    · have hdiv : bit / 64 < k := by omega
      have hdiv' : bit / 64 < k + 1 := by omega
      simp [hbit, hdiv, hdiv', ih]
    · by_cases hbit2 : bit < 64 * (k + 1)
      · have hdiv : bit / 64 = k := by omega
        have hmod : bit - 64 * k = bit % 64 := by omega
        have hdiv' : bit / 64 < k + 1 := by omega
        simp [hbit, hdiv, hmod]
      · have hdiv' : ¬ bit / 64 < k + 1 := by omega
        have hge64 : 64 ≤ bit - 64 * k := by omega
        have hl : (getLimb xs k).toNat < 2 ^ (bit - 64 * k) :=
          Nat.lt_of_lt_of_le (uint64_toNat_lt _) (Nat.pow_le_pow_right (by decide) hge64)
        simp [hbit, hdiv', testBit_eq_false_of_lt_pow hl]

theorem testBit_toNat (xs : Array UInt64) (bit : Nat) :
    (toNat xs).testBit bit = (getLimb xs (bit / 64)).toNat.testBit (bit % 64) := by
  unfold toNat
  rw [testBit_toNatPrefix]
  split
  · rfl
  · rename_i hge
    rw [getLimb_ge (by omega)]
    simp

end IxCC.BigNat
