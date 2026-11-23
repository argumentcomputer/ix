import IxCC.BigNat.Entry
import IxCC.BigNat.Proof

/-! # Layer-1 Formal Proofs for `IxCC.BigNat.Entry` (`IxCC.BigNat.Proof.Entry`)

Proves canonical normal-form preservation (`SlowNat.Canonical`) and exact
mathematical agreement with Lean's `Nat` (`SlowNat.val`) for every slow-path
entrypoint in `IxCC.BigNat.Entry`:

* Promotion, demotion, tagging, and canonical uniqueness (`val_inj`, `fromUInt64`,
  `fromLimbs`, `ofTaggedWord`, `toTaggedWord?`, `isCanonical_iff`, `isZero_iff`, `isOne_iff`)
* Comparisons (`cmp`, `beq`, `ble`, `blt`)
* Linear arithmetic (`add`, `sub`, `pred`)
* Multiplication and exponentiation (`mul`, `pow`, `pow?`)
* Euclidean division and remainder (`divMod`, `div`, `mod`)
* Greatest common divisor (`gcdU64`, `gcd`)
* Bitwise operations (`land`, `lor`, `xor`)
* Shifts and base-2 logarithm (`shiftLeft`, `shiftLeft?`, `shiftRight`, `shiftRightSlow`,
  `log2`, `log2Slow`)
* Decimal formatting and parsing (`toDecimal`, `ofDecimal`, round-trip)

Strictly standard axioms `[propext, Classical.choice, Quot.sound]`; zero `sorry`. -/

set_option autoImplicit false

namespace IxCC.BigNat.Entry

open IxCC.BigNat

/-! ## Helper Lemmas for `SlowNat` and 1- and 2-Limb Arrays -/

@[simp] theorem val_small (v : UInt64) : (SlowNat.small v).val = v.toNat := rfl
@[simp] theorem val_big (ls : Array UInt64) : (SlowNat.big ls).val = BigNat.toNat ls := rfl
@[simp] theorem canonical_small (v : UInt64) : (SlowNat.small v).Canonical ↔ v.toNat < 2 ^ 63 := Iff.rfl
@[simp] theorem canonical_big (ls : Array UInt64) :
    (SlowNat.big ls).Canonical ↔ BigNat.WF ls ∧ 2 ^ 63 ≤ BigNat.toNat ls := Iff.rfl

private theorem canonical_small_zero : (SlowNat.small 0).Canonical := by
  simp only [canonical_small]; decide
private theorem canonical_small_one : (SlowNat.small 1).Canonical := by
  simp only [canonical_small]; decide

private theorem toNat_singleton (x : UInt64) : BigNat.toNat #[x] = x.toNat := by
  simp [BigNat.toNat, BigNat.toNatPrefix, BigNat.getLimb]

private theorem wf_singleton {x : UInt64} (hx : x ≠ 0) : BigNat.WF #[x] := by
  right
  simp only [Array.size_singleton, Nat.sub_self, BigNat.getLimb, Nat.zero_lt_one, ↓reduceDIte,
    List.getElem_toArray, List.getElem_cons_zero]
  exact hx

private theorem toNat_pair (lo hi : UInt64) :
    BigNat.toNat #[lo, hi] = lo.toNat + hi.toNat * 2 ^ 64 := by
  simp [BigNat.toNat, BigNat.toNatPrefix, BigNat.getLimb]

private theorem wf_pair (lo : UInt64) {hi : UInt64} (hhi : hi ≠ 0) : BigNat.WF #[lo, hi] := by
  right
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.add_sub_cancel,
    BigNat.getLimb, Nat.lt_add_one, ↓reduceDIte, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero]
  exact hhi

private theorem uint64_ne_zero_of_toNat {x : UInt64} (h : 0 < x.toNat) : x ≠ 0 := by
  intro hz
  subst hz
  simp at h

private theorem toNat_size_one {xs : Array UInt64} (h1 : xs.size = 1) :
    BigNat.toNat xs = (xs[0]'(by omega)).toNat := by
  have htop : toNatPrefix xs xs.size = toNatPrefix xs 1 := by rw [h1]
  unfold BigNat.toNat
  rw [htop, toNatPrefix_succ, toNatPrefix_zero, getLimb_lt (by omega)]
  simp

private theorem toNat_ge_2_64_of_size_ge_2 {xs : Array UInt64} (hwf : BigNat.WF xs)
    (hge2 : 2 ≤ xs.size) : 2 ^ 64 ≤ BigNat.toNat xs := by
  have htop := toNat_ge_top xs hwf (by omega)
  have hpow : 2 ^ 64 ≤ (2 ^ 64) ^ (xs.size - 1) := by
    calc 2 ^ 64 = (2 ^ 64) ^ 1 := (Nat.pow_one _).symm
      _ ≤ (2 ^ 64) ^ (xs.size - 1) :=
        Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
  omega

/-! ## Smallness, Promotion, Demotion, and Tagging -/

theorem isSmallU64_iff (v : UInt64) : isSmallU64 v = true ↔ v.toNat < 2 ^ 63 :=
  uint64_shiftRight63_eq_zero_iff v

theorem isSmallU64_false_iff (v : UInt64) : isSmallU64 v = false ↔ 2 ^ 63 ≤ v.toNat := by
  cases h : isSmallU64 v
  · simp only [true_iff]
    exact Nat.le_of_not_lt fun hlt => by
      have := (isSmallU64_iff v).mpr hlt
      rw [h] at this
      cases this
  · simp only [Bool.true_eq_false, false_iff]
    have := (isSmallU64_iff v).mp h
    omega

theorem canonical_ofNat (n : Nat) : (SlowNat.ofNat n).Canonical := by
  unfold SlowNat.ofNat
  by_cases hlt : n < 2 ^ 63
  · simp only [hlt, ↓reduceIte, canonical_small, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hlt
  · simp only [hlt, ↓reduceIte, canonical_big]
    exact ⟨wf_ofNat n, by rw [toNat_ofNat]; omega⟩

theorem val_ofNat (n : Nat) : (SlowNat.ofNat n).val = n := by
  unfold SlowNat.ofNat
  by_cases hlt : n < 2 ^ 63
  · simp only [hlt, ↓reduceIte, val_small, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [hlt, ↓reduceIte, val_big]
    exact toNat_ofNat n

theorem val_inj {a b : SlowNat} (ha : a.Canonical) (hb : b.Canonical) (h : a.val = b.val) :
    a = b := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      congr 1
      exact UInt64.toNat_inj.mp h
    | big lb =>
      simp only [canonical_small, canonical_big, val_small, val_big] at ha hb h
      omega
  | big la =>
    cases b with
    | small vb =>
      simp only [canonical_small, canonical_big, val_small, val_big] at ha hb h
      omega
    | big lb =>
      simp only [canonical_big, val_big] at ha hb h
      congr 1
      exact BigNat.toNat_inj ha.1 hb.1 h

theorem canonical_fromUInt64 (v : UInt64) : (fromUInt64 v).Canonical := by
  unfold fromUInt64
  cases h : isSmallU64 v
  · simp only [Bool.false_eq_true, ↓reduceIte, canonical_big]
    have hge := (isSmallU64_false_iff v).mp h
    refine ⟨wf_singleton (uint64_ne_zero_of_toNat (by omega)), ?_⟩
    rw [toNat_singleton]
    exact hge
  · simp only [↓reduceIte, canonical_small]
    exact (isSmallU64_iff v).mp h

theorem val_fromUInt64 (v : UInt64) : (fromUInt64 v).val = v.toNat := by
  unfold fromUInt64
  split
  · rfl
  · exact toNat_singleton v

theorem canonical_fromLimbs (xs : Array UInt64) : (fromLimbs xs).Canonical := by
  unfold fromLimbs
  dsimp only
  have hwf : BigNat.WF (normalize xs) := wf_normalize xs
  by_cases h0 : (normalize xs).size = 0
  · simp only [h0, ↓reduceDIte]
    exact canonical_small_zero
  · simp only [h0, ↓reduceDIte]
    by_cases h1 : (normalize xs).size = 1
    · have h1b : ((normalize xs).size == 1) = true := beq_iff_eq.mpr h1
      simp only [h1b, ↓reduceIte]
      have hto := toNat_size_one h1
      cases hsm : isSmallU64 ((normalize xs)[0]'(Nat.pos_of_ne_zero h0))
      · simp only [Bool.false_eq_true, ↓reduceIte, canonical_big]
        exact ⟨hwf, by rw [hto]; exact (isSmallU64_false_iff _).mp hsm⟩
      · simp only [↓reduceIte, canonical_small]
        exact (isSmallU64_iff _).mp hsm
    · have h1b : ((normalize xs).size == 1) = false := beq_false_of_ne h1
      simp only [h1b, Bool.false_eq_true, ↓reduceIte, canonical_big]
      have hge := toNat_ge_2_64_of_size_ge_2 hwf (by omega)
      exact ⟨hwf, by omega⟩

theorem val_fromLimbs (xs : Array UInt64) : (fromLimbs xs).val = BigNat.toNat xs := by
  unfold fromLimbs
  dsimp only
  rw [← toNat_normalize xs]
  by_cases h0 : (normalize xs).size = 0
  · simp only [h0, ↓reduceDIte, val_small, BigNat.toNat]
    rfl
  · simp only [h0, ↓reduceDIte]
    by_cases h1 : (normalize xs).size = 1
    · have h1b : ((normalize xs).size == 1) = true := beq_iff_eq.mpr h1
      simp only [h1b, ↓reduceIte]
      have hto := toNat_size_one h1
      split
      · simp [hto]
      · rfl
    · have h1b : ((normalize xs).size == 1) = false := beq_false_of_ne h1
      simp [h1b]

theorem toNat_toLimbs (a : SlowNat) : BigNat.toNat (toLimbs a) = a.val := by
  cases a with
  | small v => exact toNat_ofUInt64 v
  | big ls => rfl

theorem wf_toLimbs {a : SlowNat} (ha : a.Canonical) : BigNat.WF (toLimbs a) := by
  cases a with
  | small v => exact wf_ofUInt64 v
  | big ls => exact ha.1

theorem canonical_canon (a : SlowNat) : (canon a).Canonical := by
  cases a with
  | small v => exact canonical_fromUInt64 v
  | big ls => exact canonical_fromLimbs ls

theorem val_canon (a : SlowNat) : (canon a).val = a.val := by
  cases a with
  | small v => exact val_fromUInt64 v
  | big ls => exact val_fromLimbs ls

theorem canon_of_canonical {a : SlowNat} (ha : a.Canonical) : canon a = a :=
  val_inj (canonical_canon a) ha (val_canon a)

theorem canonical_ofTaggedWord (w : UInt64) : (ofTaggedWord w).Canonical := by
  simp only [ofTaggedWord, canonical_small, UInt64.toNat_shiftRight,
    show (UInt64.toNat 1) % 64 = 1 from rfl, Nat.shiftRight_eq_div_pow]
  have hw := uint64_toNat_lt w
  omega

theorem val_ofTaggedWord (w : UInt64) : (ofTaggedWord w).val = (w >>> (1 : UInt64)).toNat := rfl

theorem toTaggedWord?_spec {a : SlowNat} (ha : a.Canonical) :
    toTaggedWord? a =
      if a.val < 2 ^ 63 then some (UInt64.ofNat (2 * a.val + 1)) else none := by
  cases a with
  | small v =>
    have hv : v.toNat < 2 ^ 63 := ha
    have hsm : isSmallU64 v = true := (isSmallU64_iff v).mpr hv
    simp only [toTaggedWord?, hsm, ↓reduceIte, val_small, hv]
    congr 1
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
      show (UInt64.toNat 1) % 64 = 1 from rfl, show (UInt64.toNat 1) = 1 from rfl,
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ i =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      have h1 : v.toNat * 2 / 2 = v.toNat := by omega
      have h2 : (2 * v.toNat + 1) / 2 = v.toNat := by omega
      have h3 : (1 : Nat) / 2 = 0 := rfl
      rw [h1, h2, h3, Nat.zero_testBit, Bool.or_false]
  | big ls =>
    have hge : 2 ^ 63 ≤ BigNat.toNat ls := ha.2
    have hnot : ¬ BigNat.toNat ls < 2 ^ 63 := by omega
    simp [toTaggedWord?, hnot]

theorem ofTaggedWord_toTaggedWord? {a : SlowNat} {w : UInt64}
    (h : toTaggedWord? a = some w) : ofTaggedWord w = a := by
  cases a with
  | small v =>
    simp only [toTaggedWord?] at h
    cases hsm : isSmallU64 v
    · simp [hsm] at h
    · simp only [hsm, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hv : v.toNat < 2 ^ 63 := (isSmallU64_iff v).mp hsm
      unfold ofTaggedWord
      congr 1
      apply UInt64.toNat_inj.mp
      have hw : (((v <<< (1 : UInt64)) ||| (1 : UInt64))).toNat = 2 * v.toNat + 1 := by
        have hspec := toTaggedWord?_spec (a := .small v) hv
        simp only [toTaggedWord?, hsm, ↓reduceIte, val_small, hv, Option.some.injEq] at hspec
        rw [hspec, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      rw [UInt64.toNat_shiftRight, hw, show (UInt64.toNat 1) % 64 = 1 from rfl,
        Nat.shiftRight_eq_div_pow]
      omega
  | big ls => simp [toTaggedWord?] at h

theorem isCanonical_iff (a : SlowNat) : isCanonical a = true ↔ a.Canonical := by
  cases a with
  | small v => exact isSmallU64_iff v
  | big ls =>
    simp only [isCanonical, canonical_big]
    by_cases hpos : 0 < ls.size
    · simp only [hpos, ↓reduceDIte]
      by_cases htop : ls[ls.size - 1]'(Nat.sub_lt hpos Nat.one_pos) = 0
      · have htb : (ls[ls.size - 1]'(Nat.sub_lt hpos Nat.one_pos) == 0) = true := beq_iff_eq.mpr htop
        simp only [htb, ↓reduceIte, Bool.false_eq_true, false_iff]
        rintro ⟨hwf, _⟩
        rcases hwf with h0 | hne
        · omega
        · rw [getLimb_lt (by omega)] at hne
          exact hne htop
      · have htb : (ls[ls.size - 1]'(Nat.sub_lt hpos Nat.one_pos) == 0) = false := beq_false_of_ne htop
        simp only [htb, Bool.false_eq_true, ↓reduceIte]
        have hwf : BigNat.WF ls := Or.inr (by rw [getLimb_lt (by omega)]; exact htop)
        by_cases h1 : ls.size = 1
        · have h1b : (ls.size == 1) = true := beq_iff_eq.mpr h1
          simp only [h1b, ↓reduceIte, Bool.not_eq_true']
          have hto : BigNat.toNat ls = (ls[ls.size - 1]'(Nat.sub_lt hpos Nat.one_pos)).toNat := by
            have h0 := toNat_size_one h1
            have hidx : ls[0]'(by omega) = ls[ls.size - 1]'(Nat.sub_lt hpos Nat.one_pos) := by
              congr 1; omega
            rw [h0, hidx]
          rw [isSmallU64_false_iff, hto]
          exact ⟨fun hge => ⟨hwf, hge⟩, fun h => h.2⟩
        · have h1b : (ls.size == 1) = false := beq_false_of_ne h1
          simp only [h1b, Bool.false_eq_true, ↓reduceIte, true_iff]
          have hge := toNat_ge_2_64_of_size_ge_2 hwf (by omega)
          exact ⟨hwf, by omega⟩
    · simp only [hpos, ↓reduceDIte, Bool.false_eq_true, false_iff]
      rintro ⟨_, hge⟩
      have h0 : ls.size = 0 := by omega
      have : BigNat.toNat ls = 0 := by simp [BigNat.toNat, h0]
      omega

theorem isZero_iff (a : SlowNat) : isZero a = true ↔ a.val = 0 := by
  cases a with
  | small v =>
    simp only [isZero, val_small, beq_iff_eq]
    constructor
    · intro h; subst h; rfl
    · intro h; exact UInt64.toNat_inj.mp (by simpa using h)
  | big ls =>
    simp only [isZero, val_big, beq_iff_eq]
    rw [← toNat_normalize ls]
    exact (toNat_eq_zero_iff (normalize ls) (wf_normalize ls)).symm

theorem isOne_iff (a : SlowNat) : isOne a = true ↔ a.val = 1 := by
  cases a with
  | small v =>
    simp only [isOne, val_small, beq_iff_eq]
    constructor
    · intro h; subst h; rfl
    · intro h; exact UInt64.toNat_inj.mp (by simpa using h)
  | big ls =>
    simp only [isOne, val_big, Bool.and_eq_true, beq_iff_eq]
    rw [← toNat_normalize ls]
    constructor
    · rintro ⟨hsz, h0⟩
      unfold BigNat.toNat
      rw [hsz, toNatPrefix_succ, toNatPrefix_zero, h0]
      rfl
    · intro h1
      have hwf := wf_normalize ls
      have hnz : (normalize ls).size ≠ 0 := by
        intro hz
        have : BigNat.toNat (normalize ls) = 0 := by simp [BigNat.toNat, hz]
        omega
      have hsz1 : (normalize ls).size = 1 := by
        cases hge : decide (2 ≤ (normalize ls).size)
        · simp only [decide_eq_false_iff_not] at hge; omega
        · simp only [decide_eq_true_eq] at hge
          have hbig := toNat_ge_2_64_of_size_ge_2 hwf hge
          omega
      refine ⟨hsz1, ?_⟩
      have hto : BigNat.toNat (normalize ls) = (getLimb (normalize ls) 0).toNat := by
        unfold BigNat.toNat
        rw [hsz1, toNatPrefix_succ, toNatPrefix_zero]
        simp
      exact UInt64.toNat_inj.mp (by rw [← hto, h1]; rfl)

/-! ## Comparisons (`cmp`, `beq`, `ble`, `blt`) -/

theorem cmp_spec {a b : SlowNat} (ha : a.Canonical) (hb : b.Canonical) :
    cmp a b = compare a.val b.val := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [cmp, val_small, compare, compareOfLessAndEq]
      by_cases hlt : va < vb
      · have hlt' : va.toNat < vb.toNat := UInt64.lt_iff_toNat_lt.mp hlt
        simp [hlt, hlt']
      · have hnotlt : ¬ va.toNat < vb.toNat := fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
        by_cases hgt : vb < va
        · have hgt' : vb.toNat < va.toNat := UInt64.lt_iff_toNat_lt.mp hgt
          have hne : va.toNat ≠ vb.toNat := by omega
          simp [hlt, hgt, hnotlt, hne]
        · have hnotgt : ¬ vb.toNat < va.toNat := fun h => hgt (UInt64.lt_iff_toNat_lt.mpr h)
          have heq : va.toNat = vb.toNat := by omega
          simp [hlt, hgt, heq]
    | big lb =>
      simp only [canonical_small, canonical_big] at ha hb
      have hlt : va.toNat < BigNat.toNat lb := by omega
      simp [cmp, compare, compareOfLessAndEq, hlt]
  | big la =>
    cases b with
    | small vb =>
      simp only [canonical_small, canonical_big] at ha hb
      have hnotlt : ¬ BigNat.toNat la < vb.toNat := by omega
      have hne : BigNat.toNat la ≠ vb.toNat := by omega
      simp [cmp, compare, compareOfLessAndEq, hnotlt, hne]
    | big lb =>
      exact BigNat.cmp_spec ha.1 hb.1

theorem beq_spec {a b : SlowNat} (ha : a.Canonical) (hb : b.Canonical) :
    beq a b = (a.val == b.val) := by
  unfold beq
  rw [cmp_spec ha hb]
  simp only [compare, compareOfLessAndEq]
  by_cases hlt : a.val < b.val
  · have hne : a.val ≠ b.val := by omega
    simp [hlt, hne]
  · by_cases heq : a.val = b.val <;> simp [hlt, heq]

theorem ble_spec {a b : SlowNat} (ha : a.Canonical) (hb : b.Canonical) :
    ble a b = decide (a.val ≤ b.val) := by
  unfold ble
  rw [cmp_spec ha hb]
  simp only [compare, compareOfLessAndEq]
  by_cases hlt : a.val < b.val
  · have hle : a.val ≤ b.val := by omega
    simp [hlt, hle]
  · by_cases heq : a.val = b.val
    · simp [heq]
    · have hnotle : ¬ a.val ≤ b.val := by omega
      simp [hlt, heq, hnotle]

theorem blt_spec {a b : SlowNat} (ha : a.Canonical) (hb : b.Canonical) :
    blt a b = decide (a.val < b.val) := by
  unfold blt
  rw [cmp_spec ha hb]
  simp only [compare, compareOfLessAndEq]
  by_cases hlt : a.val < b.val
  · simp [hlt]
  · by_cases heq : a.val = b.val <;> simp [hlt, heq]

/-! ## Linear Arithmetic (`add`, `sub`, `pred`) -/

theorem canonical_add (a b : SlowNat) : (add a b).Canonical := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [add]
      split
      · refine ⟨wf_pair _ (by decide), ?_⟩
        rw [toNat_pair]
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h1]
        omega
      · exact canonical_fromUInt64 _
    | big lb => exact canonical_fromLimbs _
  | big la => exact canonical_fromLimbs _

theorem val_add (a b : SlowNat) : (add a b).val = a.val + b.val := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [add, val_small]
      have hspec := addCarry64_spec va vb false
      have hf : false.toNat = 0 := rfl
      rw [hf, Nat.add_zero] at hspec
      cases hc : (addCarry64 va vb false).2
      · rw [hc] at hspec
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [val_fromUInt64]
        simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hspec
        exact hspec
      · rw [hc] at hspec
        simp only [↓reduceIte, val_big, toNat_pair]
        simp only [Bool.toNat_true, Nat.one_mul] at hspec
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h1, Nat.one_mul]
        exact hspec
    | big lb =>
      simp only [add, val_fromLimbs, toNat_add, toNat_toLimbs]
  | big la =>
    cases b <;> simp only [add, val_fromLimbs, toNat_add, toNat_toLimbs]

theorem canonical_sub (a b : SlowNat) : (sub a b).Canonical := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [sub]
      split
      · exact canonical_small_zero
      · exact canonical_fromUInt64 _
    | big lb => exact canonical_fromLimbs _
  | big la => exact canonical_fromLimbs _

theorem val_sub (a b : SlowNat) : (sub a b).val = a.val - b.val := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [sub, val_small]
      by_cases hlt : va < vb
      · have hlt' : va.toNat < vb.toNat := UInt64.lt_iff_toNat_lt.mp hlt
        simp only [hlt, ↓reduceIte, val_small]
        have h0 : (0 : UInt64).toNat = 0 := rfl
        rw [h0]
        omega
      · have hge : vb.toNat ≤ va.toNat := Nat.le_of_not_lt (fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h))
        simp only [hlt, ↓reduceIte]
        rw [val_fromUInt64, UInt64.toNat_sub]
        have hva := uint64_toNat_lt va
        have hvb := uint64_toNat_lt vb
        omega
    | big lb =>
      simp only [sub, val_fromLimbs, toNat_subRaw, toNat_toLimbs]
  | big la =>
    cases b <;> simp only [sub, val_fromLimbs, toNat_subRaw, toNat_toLimbs]

theorem canonical_pred (a : SlowNat) : (pred a).Canonical := by
  cases a with
  | small va =>
    simp only [pred]
    split
    · exact canonical_small_zero
    · exact canonical_fromUInt64 _
  | big la => exact canonical_fromLimbs _

theorem val_pred (a : SlowNat) : (pred a).val = a.val - 1 := by
  cases a with
  | small va =>
    simp only [pred, val_small]
    by_cases h0 : va = 0
    · subst h0; rfl
    · have h0b : (va == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      rw [val_fromUInt64, UInt64.toNat_sub, show (1 : UInt64).toNat = 1 from rfl]
      have hpos : 0 < va.toNat := by
        have hne : va.toNat ≠ 0 := fun hz => h0 (UInt64.toNat_inj.mp (by simpa using hz))
        omega
      have hva := uint64_toNat_lt va
      omega
  | big la =>
    simp only [pred, val_big]
    rw [val_fromLimbs, toNat_pred (wf_normalize la), toNat_normalize]

/-! ## Multiplication and Exponentiation (`mul`, `pow`, `pow?`) -/

theorem canonical_mul (a b : SlowNat) : (mul a b).Canonical := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [mul]
      by_cases hhi : (mulWide64 va vb).2 = 0
      · have hb : ((mulWide64 va vb).2 == 0) = true := beq_iff_eq.mpr hhi
        simp only [hb, ↓reduceIte]
        exact canonical_fromUInt64 _
      · have hb : ((mulWide64 va vb).2 == 0) = false := beq_false_of_ne hhi
        simp only [hb, Bool.false_eq_true, ↓reduceIte, canonical_big]
        refine ⟨wf_pair _ hhi, ?_⟩
        rw [toNat_pair]
        have hpos : 0 < (mulWide64 va vb).2.toNat := by
          have hne : (mulWide64 va vb).2.toNat ≠ 0 :=
            fun hz => hhi (UInt64.toNat_inj.mp (by simpa using hz))
          omega
        have hmul : 2 ^ 64 ≤ (mulWide64 va vb).2.toNat * 2 ^ 64 :=
          Nat.le_mul_of_pos_left _ hpos
        omega
    | big lb =>
      simp only [mul]
      split
      · exact canonical_small_zero
      · exact canonical_fromLimbs _
  | big la =>
    cases b with
    | small vb =>
      simp only [mul]
      split
      · exact canonical_small_zero
      · exact canonical_fromLimbs _
    | big lb => exact canonical_fromLimbs _

theorem val_mul (a b : SlowNat) : (mul a b).val = a.val * b.val := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [mul, val_small]
      have hspec := mulWide64_spec va vb
      by_cases hhi : (mulWide64 va vb).2 = 0
      · have hb : ((mulWide64 va vb).2 == 0) = true := beq_iff_eq.mpr hhi
        simp only [hb, ↓reduceIte]
        rw [val_fromUInt64]
        rw [hhi, UInt64.toNat_zero, Nat.zero_mul, Nat.add_zero] at hspec
        exact hspec
      · have hb : ((mulWide64 va vb).2 == 0) = false := beq_false_of_ne hhi
        simp only [hb, Bool.false_eq_true, ↓reduceIte, val_big, toNat_pair]
        exact hspec
    | big lb =>
      simp only [mul, val_small, val_big]
      by_cases hv0 : va = 0
      · subst hv0; simp
      · have hb : (va == 0) = false := beq_false_of_ne hv0
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        rw [val_fromLimbs, toNat_mulAdd1, UInt64.toNat_zero, Nat.add_zero, Nat.mul_comm]
  | big la =>
    cases b with
    | small vb =>
      simp only [mul, val_small, val_big]
      by_cases hv0 : vb = 0
      · subst hv0; simp
      · have hb : (vb == 0) = false := beq_false_of_ne hv0
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        rw [val_fromLimbs, toNat_mulAdd1, UInt64.toNat_zero, Nat.add_zero]
    | big lb =>
      simp only [mul, val_big]
      rw [val_fromLimbs, toNat_mul]

theorem canonical_pow (base : SlowNat) (exp : Nat) : (pow base exp).Canonical :=
  canonical_fromLimbs _

theorem val_pow (base : SlowNat) (exp : Nat) : (pow base exp).val = base.val ^ exp := by
  unfold pow
  rw [val_fromLimbs, toNat_pow, toNat_toLimbs]

private theorem toNat_ge_limit_of_toSmall?_none {ls : Array UInt64}
    (hq : toSmall? (normalize ls) = none) : 2 ^ 63 ≤ BigNat.toNat ls := by
  have hts := toSmall?_spec (normalize ls) (wf_normalize ls)
  rw [toNat_normalize, hq] at hts
  exact Nat.le_of_not_lt fun hlt => by simp [hlt] at hts

theorem pow?_spec (base exp : SlowNat) :
    match pow? base exp with
    | some r => r.Canonical ∧ r.val = base.val ^ exp.val
    | none => 2 ≤ base.val ∧ 2 ^ 63 ≤ exp.val := by
  cases exp with
  | small ve =>
    simp only [pow?, val_small]
    cases hsm : isSmallU64 ve
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hge : 2 ^ 63 ≤ ve.toNat := (isSmallU64_false_iff ve).mp hsm
      cases hz : isZero base
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hnz : base.val ≠ 0 := fun h => by
          have := (isZero_iff base).mpr h; rw [hz] at this; cases this
        cases h1 : isOne base
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hne1 : base.val ≠ 1 := fun h => by
            have := (isOne_iff base).mpr h; rw [h1] at this; cases this
          exact ⟨by omega, hge⟩
        · simp only [↓reduceIte]
          have hb1 : base.val = 1 := (isOne_iff base).mp h1
          exact ⟨canonical_small_one, by rw [hb1, Nat.one_pow]; rfl⟩
      · simp only [↓reduceIte]
        have hb0 : base.val = 0 := (isZero_iff base).mp hz
        refine ⟨canonical_small_zero, ?_⟩
        rw [hb0, Nat.zero_pow (by omega)]
        rfl
    · simp only [↓reduceIte]
      exact ⟨canonical_fromLimbs _, by rw [val_fromLimbs, toNat_pow, toNat_toLimbs]⟩
  | big le =>
    simp only [pow?, val_big]
    by_cases h0 : (normalize le).size = 0
    · have h0b : ((normalize le).size == 0) = true := beq_iff_eq.mpr h0
      simp only [h0b, ↓reduceIte]
      have hle0 : BigNat.toNat le = 0 := by
        rw [← toNat_normalize le]; simp [BigNat.toNat, h0]
      exact ⟨canonical_small_one, by rw [hle0, Nat.pow_zero]; rfl⟩
    · have h0b : ((normalize le).size == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      have hts := toSmall?_spec (normalize le) (wf_normalize le)
      rw [toNat_normalize] at hts
      cases hq : toSmall? (normalize le) with
      | some e =>
        rw [hq] at hts
        split at hts
        · have he : e = BigNat.toNat le := Option.some.inj hts
          subst he
          exact ⟨canonical_fromLimbs _, by rw [val_fromLimbs, toNat_pow, toNat_toLimbs]⟩
        · cases hts
      | none =>
        have hge := toNat_ge_limit_of_toSmall?_none hq
        cases hz : isZero base
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hnz : base.val ≠ 0 := fun h => by
            have := (isZero_iff base).mpr h; rw [hz] at this; cases this
          cases h1 : isOne base
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hne1 : base.val ≠ 1 := fun h => by
              have := (isOne_iff base).mpr h; rw [h1] at this; cases this
            exact ⟨by omega, hge⟩
          · simp only [↓reduceIte]
            have hb1 : base.val = 1 := (isOne_iff base).mp h1
            exact ⟨canonical_small_one, by rw [hb1, Nat.one_pow]; rfl⟩
        · simp only [↓reduceIte]
          have hb0 : base.val = 0 := (isZero_iff base).mp hz
          refine ⟨canonical_small_zero, ?_⟩
          rw [hb0, Nat.zero_pow (by omega)]
          rfl

/-! ## Euclidean Division and Remainder (`divMod`, `div`, `mod`) -/

theorem canonical_divMod (a b : SlowNat) :
    (divMod a b).1.Canonical ∧ (divMod a b).2.Canonical := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [divMod]
      split
      · exact ⟨canonical_small_zero, canonical_fromUInt64 _⟩
      · exact ⟨canonical_fromUInt64 _, canonical_fromUInt64 _⟩
    | big lb =>
      exact ⟨canonical_fromLimbs _, canonical_fromLimbs _⟩
  | big la =>
    cases b with
    | small vb =>
      simp only [divMod]
      split
      · exact ⟨canonical_small_zero, canonical_fromLimbs _⟩
      · exact ⟨canonical_fromLimbs _, canonical_fromUInt64 _⟩
    | big lb =>
      exact ⟨canonical_fromLimbs _, canonical_fromLimbs _⟩

theorem divMod_spec (a b : SlowNat) :
    (divMod a b).1.val = a.val / b.val ∧ (divMod a b).2.val = a.val % b.val := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [divMod, val_small]
      by_cases h0 : vb = 0
      · subst h0
        simp [val_fromUInt64]
      · have h0b : (vb == 0) = false := beq_false_of_ne h0
        simp only [h0b, Bool.false_eq_true, ↓reduceIte]
        rw [val_fromUInt64, val_fromUInt64, UInt64.toNat_div, UInt64.toNat_mod]
        exact ⟨rfl, rfl⟩
    | big lb =>
      have hspec := BigNat.divMod_spec (ofUInt64 va) lb
      simp only [divMod, toLimbs, val_small, val_big]
      rw [val_fromLimbs, val_fromLimbs, hspec.2.2.1, hspec.2.2.2, toNat_ofUInt64]
      exact ⟨rfl, rfl⟩
  | big la =>
    cases b with
    | small vb =>
      simp only [divMod, val_small, val_big]
      by_cases h0 : vb = 0
      · subst h0
        simp [val_fromLimbs]
      · have h0b : (vb == 0) = false := beq_false_of_ne h0
        simp only [h0b, Bool.false_eq_true, ↓reduceIte]
        rw [val_fromLimbs, val_fromUInt64]
        have hspec := divMod1_spec la vb h0
        exact ⟨hspec.2.1, hspec.2.2.1⟩
    | big lb =>
      have hspec := BigNat.divMod_spec la lb
      simp only [divMod, toLimbs, val_big]
      rw [val_fromLimbs, val_fromLimbs]
      exact ⟨hspec.2.2.1, hspec.2.2.2⟩

theorem canonical_div (a b : SlowNat) : (div a b).Canonical := (canonical_divMod a b).1
theorem val_div (a b : SlowNat) : (div a b).val = a.val / b.val := (divMod_spec a b).1
theorem canonical_mod (a b : SlowNat) : (mod a b).Canonical := (canonical_divMod a b).2
theorem val_mod (a b : SlowNat) : (mod a b).val = a.val % b.val := (divMod_spec a b).2

/-! ## Greatest Common Divisor (`gcdU64`, `gcd`) -/

theorem gcdU64_toNat (a b : UInt64) : (gcdU64 a b).toNat = Nat.gcd a.toNat b.toNat := by
  induction hn : b.toNat using Nat.strongRecOn generalizing a b with
  | ind n ih =>
    unfold gcdU64
    split
    · rename_i hz
      subst hz
      rw [← hn]
      simp
    · rename_i hne
      have hbpos : 0 < b.toNat := by
        have h : b.toNat ≠ 0 := fun hz => hne (UInt64.toNat_inj.mp (by simpa using hz))
        omega
      have hlt : (a % b).toNat < n := by
        rw [UInt64.toNat_mod, ← hn]
        exact Nat.mod_lt _ hbpos
      rw [ih (a % b).toNat hlt b (a % b) rfl, UInt64.toNat_mod, ← hn,
        Nat.gcd_comm b.toNat, ← Nat.gcd_rec, Nat.gcd_comm]

theorem canonical_gcd (a b : SlowNat) : (gcd a b).Canonical := by
  cases a with
  | small va =>
    cases b with
    | small vb => exact canonical_fromUInt64 _
    | big lb =>
      simp only [gcd]
      split
      · exact canonical_fromLimbs _
      · exact canonical_fromUInt64 _
  | big la =>
    cases b with
    | small vb =>
      simp only [gcd]
      split
      · exact canonical_fromLimbs _
      · exact canonical_fromUInt64 _
    | big lb => exact canonical_fromLimbs _

private theorem divMod1_snd_eq_mod (la : Array UInt64) {v : UInt64} (hv : v ≠ 0) :
    (divMod1 la v).2.toNat = BigNat.toNat la % v.toNat :=
  (divMod1_spec la v hv).2.2.1

theorem val_gcd (a b : SlowNat) : (gcd a b).val = Nat.gcd a.val b.val := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [gcd, val_small]
      rw [val_fromUInt64, gcdU64_toNat]
    | big lb =>
      simp only [gcd, val_small, val_big]
      by_cases h0 : va = 0
      · subst h0
        simp [val_fromLimbs]
      · have h0b : (va == 0) = false := beq_false_of_ne h0
        simp only [h0b, Bool.false_eq_true, ↓reduceIte]
        rw [val_fromUInt64, gcdU64_toNat, divMod1_snd_eq_mod lb h0,
          Nat.gcd_comm va.toNat, ← Nat.gcd_rec]
  | big la =>
    cases b with
    | small vb =>
      simp only [gcd, val_small, val_big]
      by_cases h0 : vb = 0
      · subst h0
        simp [val_fromLimbs]
      · have h0b : (vb == 0) = false := beq_false_of_ne h0
        simp only [h0b, Bool.false_eq_true, ↓reduceIte]
        rw [val_fromUInt64, gcdU64_toNat, divMod1_snd_eq_mod la h0,
          Nat.gcd_comm vb.toNat, ← Nat.gcd_rec, Nat.gcd_comm]
    | big lb =>
      simp only [gcd, val_big]
      rw [val_fromLimbs, toNat_gcd]

/-! ## Bitwise Operations (`land`, `lor`, `xor`) -/

theorem canonical_land (a b : SlowNat) : (land a b).Canonical := by
  cases a <;> cases b
  · exact canonical_fromUInt64 _
  · exact canonical_fromUInt64 _
  · exact canonical_fromUInt64 _
  · exact canonical_fromLimbs _

private theorem land_uint64_big (v : UInt64) (ls : Array UInt64) :
    (v &&& getLimb ls 0).toNat = v.toNat &&& BigNat.toNat ls := by
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [UInt64.toNat_and, Nat.testBit_and, Nat.testBit_and, testBit_toNat]
  by_cases hlt : bit < 64
  · have hd : bit / 64 = 0 := Nat.div_eq_of_lt hlt
    have hm : bit % 64 = bit := Nat.mod_eq_of_lt hlt
    rw [hd, hm]
  · have hv : v.toNat < 2 ^ bit :=
      Nat.lt_of_lt_of_le (uint64_toNat_lt v) (Nat.pow_le_pow_right (by decide) (by omega))
    have hvf : v.toNat.testBit bit = false := testBit_eq_false_of_lt_pow hv
    simp [hvf]

theorem val_land (a b : SlowNat) : (land a b).val = a.val &&& b.val := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [land, val_small]
      rw [val_fromUInt64, UInt64.toNat_and]
    | big lb =>
      simp only [land, val_small, val_big]
      rw [val_fromUInt64]
      exact land_uint64_big va lb
  | big la =>
    cases b with
    | small vb =>
      simp only [land, val_small, val_big]
      rw [val_fromUInt64, UInt64.and_comm, Nat.and_comm]
      exact land_uint64_big vb la
    | big lb =>
      simp only [land, val_big]
      rw [val_fromLimbs, toNat_land]

theorem canonical_lor (a b : SlowNat) : (lor a b).Canonical := by
  cases a <;> cases b
  · exact canonical_fromUInt64 _
  · exact canonical_fromLimbs _
  · exact canonical_fromLimbs _
  · exact canonical_fromLimbs _

theorem val_lor (a b : SlowNat) : (lor a b).val = a.val ||| b.val := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [lor, val_small]
      rw [val_fromUInt64, UInt64.toNat_or]
    | big lb =>
      simp only [lor, val_fromLimbs, toNat_lor, toNat_toLimbs]
  | big la =>
    cases b <;> simp only [lor, val_fromLimbs, toNat_lor, toNat_toLimbs]

theorem canonical_xor (a b : SlowNat) : (xor a b).Canonical := by
  cases a <;> cases b
  · exact canonical_fromUInt64 _
  · exact canonical_fromLimbs _
  · exact canonical_fromLimbs _
  · exact canonical_fromLimbs _

theorem val_xor (a b : SlowNat) : (xor a b).val = a.val ^^^ b.val := by
  cases a with
  | small va =>
    cases b with
    | small vb =>
      simp only [xor, val_small]
      rw [val_fromUInt64, UInt64.toNat_xor]
    | big lb =>
      simp only [xor, val_fromLimbs, toNat_xor, toNat_toLimbs]
  | big la =>
    cases b <;> simp only [xor, val_fromLimbs, toNat_xor, toNat_toLimbs]

/-! ## Shifts and Base-2 Logarithm (`shiftLeft`, `shiftRight`, `log2`) -/

theorem canonical_shiftLeft (a : SlowNat) (s : Nat) : (shiftLeft a s).Canonical :=
  canonical_fromLimbs _

theorem val_shiftLeft (a : SlowNat) (s : Nat) : (shiftLeft a s).val = a.val <<< s := by
  unfold shiftLeft
  rw [val_fromLimbs, toNat_shiftLeft, toNat_toLimbs]

theorem val_shiftLeft_mul (a : SlowNat) (s : Nat) : (shiftLeft a s).val = a.val * 2 ^ s := by
  rw [val_shiftLeft, Nat.shiftLeft_eq]

theorem shiftLeft?_spec (a s : SlowNat) :
    match shiftLeft? a s with
    | some r => r.Canonical ∧ r.val = a.val * 2 ^ s.val
    | none => 0 < a.val ∧ 2 ^ 63 ≤ s.val := by
  unfold shiftLeft?
  cases hz : isZero a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hpos : 0 < a.val := by
      have hne : a.val ≠ 0 := fun h => by
        have := (isZero_iff a).mpr h; rw [hz] at this; cases this
      omega
    cases s with
    | small vs =>
      simp only [val_small]
      cases hsm : isSmallU64 vs
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨hpos, (isSmallU64_false_iff vs).mp hsm⟩
      · simp only [↓reduceIte]
        exact ⟨canonical_fromLimbs _, by rw [val_fromLimbs, toNat_shiftLeft_mul, toNat_toLimbs]⟩
    | big ls =>
      simp only [val_big]
      have hts := toSmall?_spec (normalize ls) (wf_normalize ls)
      rw [toNat_normalize] at hts
      cases hq : toSmall? (normalize ls) with
      | some sv =>
        rw [hq] at hts
        split at hts
        · have heq : sv = BigNat.toNat ls := Option.some.inj hts
          subst heq
          exact ⟨canonical_fromLimbs _, by rw [val_fromLimbs, toNat_shiftLeft_mul, toNat_toLimbs]⟩
        · cases hts
      | none =>
        exact ⟨hpos, toNat_ge_limit_of_toSmall?_none hq⟩
  · simp only [↓reduceIte]
    have ha0 : a.val = 0 := (isZero_iff a).mp hz
    exact ⟨canonical_small_zero, by rw [ha0, Nat.zero_mul]; rfl⟩

theorem canonical_shiftRight (a : SlowNat) (s : Nat) : (shiftRight a s).Canonical :=
  canonical_fromLimbs _

theorem val_shiftRight (a : SlowNat) (s : Nat) : (shiftRight a s).val = a.val >>> s := by
  unfold shiftRight
  rw [val_fromLimbs, toNat_shiftRight, toNat_toLimbs]

theorem val_shiftRight_div (a : SlowNat) (s : Nat) : (shiftRight a s).val = a.val / 2 ^ s := by
  rw [val_shiftRight, Nat.shiftRight_eq_div_pow]

theorem canonical_shiftRightSlow (a s : SlowNat) : (shiftRightSlow a s).Canonical := by
  cases a with
  | small va =>
    cases s with
    | small vs =>
      simp only [shiftRightSlow]
      split
      · exact canonical_small_zero
      · exact canonical_fromUInt64 _
    | big ls =>
      simp only [shiftRightSlow]
      cases h : toSmall? (normalize ls) with
      | none => exact canonical_small_zero
      | some sv =>
        dsimp only
        split
        · exact canonical_small_zero
        · exact canonical_fromUInt64 _
  | big la =>
    cases s with
    | small vs =>
      simp only [shiftRightSlow]
      split
      · exact canonical_fromLimbs _
      · exact canonical_small_zero
    | big ls =>
      simp only [shiftRightSlow]
      cases h : toSmall? (normalize ls) with
      | none => exact canonical_small_zero
      | some sv => exact canonical_fromLimbs _

private theorem uint64_shr_lt64 (va : UInt64) {s : Nat} (hs : s < 64) :
    (va >>> UInt64.ofNat s).toNat = va.toNat / 2 ^ s := by
  rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega : s < 2 ^ 64), Nat.mod_eq_of_lt hs,
    Nat.shiftRight_eq_div_pow]

private theorem big_div_two_pow_eq_zero {la : Array UInt64} {s : Nat}
    (hbound : la.size < 2 ^ 57) (hs : 2 ^ 63 ≤ s) :
    BigNat.toNat la / 2 ^ s = 0 := by
  apply Nat.div_eq_of_lt
  have h1 : BigNat.toNat la < (2 ^ 64) ^ la.size := BigNat.toNat_lt la
  have h2 : (2 ^ 64) ^ la.size = 2 ^ (64 * la.size) := by rw [← Nat.pow_mul]
  have h3 : 64 * la.size ≤ s := by omega
  have h4 : 2 ^ (64 * la.size) ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) h3
  omega

theorem val_shiftRightSlow (a s : SlowNat) (hbound : a.limbCount < 2 ^ 57) :
    (shiftRightSlow a s).val = a.val / 2 ^ s.val := by
  cases a with
  | small va =>
    cases s with
    | small vs =>
      simp only [shiftRightSlow, val_small]
      by_cases hge : (64 : UInt64) ≤ vs
      · have hge' : 64 ≤ vs.toNat := by
          have := UInt64.le_iff_toNat_le.mp hge
          simpa using this
        simp only [ge_iff_le, hge, ↓reduceIte, val_small]
        have hlt : va.toNat < 2 ^ vs.toNat :=
          Nat.lt_of_lt_of_le (uint64_toNat_lt va) (Nat.pow_le_pow_right (by decide) hge')
        rw [Nat.div_eq_of_lt hlt]
        rfl
      · have hlt : vs.toNat < 64 := by
          have : ¬ (64 : UInt64).toNat ≤ vs.toNat := fun h => hge (UInt64.le_iff_toNat_le.mpr h)
          simpa using Nat.lt_of_not_le this
        simp only [ge_iff_le, hge, ↓reduceIte]
        rw [val_fromUInt64, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow]
    | big ls =>
      simp only [shiftRightSlow, val_small, val_big]
      have hts := toSmall?_spec (normalize ls) (wf_normalize ls)
      rw [toNat_normalize] at hts
      cases hq : toSmall? (normalize ls) with
      | some sv =>
        rw [hq] at hts
        split at hts
        · have heq : sv = BigNat.toNat ls := Option.some.inj hts
          subst heq
          by_cases hge : 64 ≤ BigNat.toNat ls
          · simp only [ge_iff_le, hge, ↓reduceIte, val_small]
            have hlt : va.toNat < 2 ^ BigNat.toNat ls :=
              Nat.lt_of_lt_of_le (uint64_toNat_lt va) (Nat.pow_le_pow_right (by decide) hge)
            rw [Nat.div_eq_of_lt hlt]
            rfl
          · simp only [ge_iff_le, hge, ↓reduceIte]
            rw [val_fromUInt64]
            exact uint64_shr_lt64 va (by omega)
        · cases hts
      | none =>
        have hge := toNat_ge_limit_of_toSmall?_none hq
        simp only [val_small]
        have hlt : va.toNat < 2 ^ BigNat.toNat ls :=
          Nat.lt_of_lt_of_le (uint64_toNat_lt va)
            (Nat.pow_le_pow_right (by decide) (by omega))
        rw [Nat.div_eq_of_lt hlt]
        rfl
  | big la =>
    have hla : la.size < 2 ^ 57 := hbound
    cases s with
    | small vs =>
      simp only [shiftRightSlow, val_small, val_big]
      cases hsm : isSmallU64 vs
      · simp only [Bool.false_eq_true, ↓reduceIte, val_small]
        have hge := (isSmallU64_false_iff vs).mp hsm
        rw [big_div_two_pow_eq_zero hla hge]
        rfl
      · simp only [↓reduceIte]
        rw [val_fromLimbs, toNat_shiftRight_div]
    | big ls =>
      simp only [shiftRightSlow, val_big]
      have hts := toSmall?_spec (normalize ls) (wf_normalize ls)
      rw [toNat_normalize] at hts
      cases hq : toSmall? (normalize ls) with
      | some sv =>
        rw [hq] at hts
        split at hts
        · have heq : sv = BigNat.toNat ls := Option.some.inj hts
          subst heq
          rw [val_fromLimbs, toNat_shiftRight_div]
        · cases hts
      | none =>
        have hge := toNat_ge_limit_of_toSmall?_none hq
        simp only [val_small]
        rw [big_div_two_pow_eq_zero hla hge]
        rfl

theorem log2_spec (a : SlowNat) : log2 a = Nat.log2 a.val := by
  cases a with
  | small va =>
    simp only [log2, val_small]
    by_cases h0 : va = 0
    · subst h0; rfl
    · have h0b : (va == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      rw [clz64_toNat_of_ne_zero va h0]
      have hlt := log2_uint64_lt_64 va
      omega
  | big la =>
    simp only [log2, val_big]
    rw [BigNat.log2_spec (wf_normalize la), toNat_normalize]

theorem canonical_log2Slow (a : SlowNat) : (log2Slow a).Canonical :=
  canonical_fromUInt64 _

theorem val_log2Slow (a : SlowNat) (hbound : a.limbCount < 2 ^ 57) :
    (log2Slow a).val = Nat.log2 a.val := by
  unfold log2Slow
  rw [val_fromUInt64, log2_spec a, UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  cases a with
  | small va =>
    have := log2_uint64_lt_64 va
    simp only [val_small]
    omega
  | big la =>
    have hla : la.size < 2 ^ 57 := hbound
    simp only [val_big]
    by_cases h0 : BigNat.toNat la = 0
    · rw [h0]; decide
    · have hlt : BigNat.toNat la < 2 ^ (64 * la.size) := by
        rw [Nat.pow_mul]
        exact BigNat.toNat_lt la
      have hlog : Nat.log2 (BigNat.toNat la) < 64 * la.size := (Nat.log2_lt h0).mpr hlt
      omega

/-! ## Decimal Formatting and Parsing (`toDecimal`, `ofDecimal`) -/

theorem canonical_ofDecimal {s : String} {a : SlowNat} (h : ofDecimal s = some a) :
    a.Canonical := by
  unfold ofDecimal at h
  cases hd : BigNat.ofDecimal s with
  | none => simp [hd] at h
  | some ls =>
    simp only [hd, Option.map_some, Option.some.injEq] at h
    rw [← h]
    exact canonical_fromLimbs ls

theorem ofDecimal_toDecimal {a : SlowNat} (ha : a.Canonical) :
    ofDecimal (toDecimal a) = some a := by
  unfold ofDecimal toDecimal
  rw [BigNat.ofDecimal_toDecimal (wf_toLimbs ha)]
  simp only [Option.map_some, Option.some.injEq]
  exact val_inj (canonical_fromLimbs _) ha (by rw [val_fromLimbs, toNat_toLimbs])

end IxCC.BigNat.Entry
