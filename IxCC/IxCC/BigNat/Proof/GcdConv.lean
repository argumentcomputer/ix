import IxCC.BigNat.GcdConv
import IxCC.BigNat.Proof.Div
import IxCC.BigNat.Proof.Lehmer

/-! # Layer-1 Proofs for `IxCC.BigNat.GcdConv` (`IxCC.BigNat.Proof.GcdConv`)

Formal correctness and canonical normal-form preservation for:
- Euclidean GCD (`gcd`)
- Linear single-limb multiply-add (`mulAdd1`)
- Base-`10^19` chunked decimal conversion (`toDecimalChunks`, `ofDecimalChunks`)
- Full decimal digit and ASCII string conversion (`toDecimalDigits`, `ofDecimalDigits`,
  `toDecimal`, `ofDecimal`) including exact round-trip theorems.

All theorems depend strictly on `[propext, Classical.choice, Quot.sound]`.
-/

namespace IxCC.BigNat

/-! ### Constants and Lehmer GCD (`gcd`) -/

theorem ten19_toNat : ten19.toNat = 10 ^ 19 := by
  unfold ten19
  rw [UInt64.toNat_mul]
  rfl

theorem ten19_gt_one : 1 < ten19.toNat := by
  rw [ten19_toNat]
  omega

theorem ten19_ne_zero : ten19 ≠ 0 := by
  intro h
  have := congrArg UInt64.toNat h
  rw [ten19_toNat] at this
  have hpos : 0 < 10 ^ 19 := Nat.pow_pos (by decide)
  have h0 : (0 : UInt64).toNat = 0 := rfl
  omega

theorem wf_gcd (a b : Array UInt64) : WF (gcd a b) :=
  wf_gcdLehmer a b

theorem toNat_gcd (a b : Array UInt64) : toNat (gcd a b) = Nat.gcd (toNat a) (toNat b) :=
  toNat_gcdLehmer a b

/-! ### Single-Limb Multiply-Add (`mulAdd1`) -/

private theorem toNat_mulAdd1Loop (a : Array UInt64) (m : UInt64) (i rem : Nat)
    (carry : UInt64) (acc : Array UInt64) (hsz : acc.size = i) :
    toNat (mulAdd1Loop a m i carry acc rem) + toNatPrefix a i * m.toNat =
      toNat acc + carry.toNat * (2 ^ 64) ^ i + toNatPrefix a (i + rem) * m.toNat := by
  induction rem generalizing i carry acc with
  | zero =>
    unfold mulAdd1Loop
    simp only [Nat.add_zero]
    split
    · rename_i hc0
      have hc : carry = 0 := eq_of_beq hc0
      subst hc
      rw [UInt64.toNat_zero, Nat.zero_mul, Nat.add_zero]
    · rw [toNat_push, hsz]
  | succ rem ih =>
    unfold mulAdd1Loop
    dsimp only
    have hmul := mulWide64_spec (getLimb a i) m
    rcases hm : mulWide64 (getLimb a i) m with ⟨pLo, pHi⟩
    rw [hm] at hmul
    have hadd := addCarry64_spec pLo carry false
    rcases ha : addCarry64 pLo carry false with ⟨lo, c⟩
    rw [ha] at hadd
    dsimp only at hmul hadd ⊢
    have hf : false.toNat = 0 := rfl
    rw [hf, Nat.add_zero] at hadd
    have hcar_lt : pHi.toNat + c.toNat < 2 ^ 64 := by
      have ha_lt : (getLimb a i).toNat < 2 ^ 64 := uint64_toNat_lt _
      have hm_lt : m.toNat < 2 ^ 64 := uint64_toNat_lt m
      have hc_lt : carry.toNat < 2 ^ 64 := uint64_toNat_lt carry
      have hprod : (getLimb a i).toNat * m.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have htot : lo.toNat + (pHi.toNat + c.toNat) * 2 ^ 64 = (getLimb a i).toNat * m.toNat + carry.toNat := by
        calc lo.toNat + (pHi.toNat + c.toNat) * 2 ^ 64
            = lo.toNat + (pHi.toNat * 2 ^ 64 + c.toNat * 2 ^ 64) := by rw [Nat.add_mul]
          _ = (lo.toNat + c.toNat * 2 ^ 64) + pHi.toNat * 2 ^ 64 := by ac_rfl
          _ = (pLo.toNat + carry.toNat) + pHi.toNat * 2 ^ 64 := by rw [hadd]
          _ = (pLo.toNat + pHi.toNat * 2 ^ 64) + carry.toNat := by ac_rfl
          _ = (getLimb a i).toNat * m.toNat + carry.toNat := by rw [hmul]
      have hbound : (2 ^ 64 - 1) * (2 ^ 64 - 1) + (2 ^ 64 - 1) < 2 ^ 64 * 2 ^ 64 := by decide
      have hlt2 : (pHi.toNat + c.toNat) * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 := by
        have h1 : (pHi.toNat + c.toNat) * 2 ^ 64 ≤ (getLimb a i).toNat * m.toNat + carry.toNat := by
          rw [← htot]; exact Nat.le_add_left _ _
        have h2 : (getLimb a i).toNat * m.toNat + carry.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) + (2 ^ 64 - 1) :=
          Nat.add_le_add hprod (by omega)
        exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) hbound
      exact Nat.lt_of_mul_lt_mul_right hlt2
    let carry' : UInt64 := if c then pHi + 1 else pHi
    have hcar'_toNat : carry'.toNat = pHi.toNat + c.toNat := by
      dsimp only [carry']
      cases c
      · simp
      · simp only [↓reduceIte, Bool.toNat_true]
        rw [UInt64.toNat_add]
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h1, Nat.mod_eq_of_lt (by simpa using hcar_lt)]
    have hspec : lo.toNat + carry'.toNat * 2 ^ 64 = (getLimb a i).toNat * m.toNat + carry.toNat := by
      calc lo.toNat + carry'.toNat * 2 ^ 64
          = lo.toNat + (pHi.toNat + c.toNat) * 2 ^ 64 := by rw [hcar'_toNat]
        _ = (lo.toNat + c.toNat * 2 ^ 64) + pHi.toNat * 2 ^ 64 := by rw [Nat.add_mul]; ac_rfl
        _ = (pLo.toNat + carry.toNat) + pHi.toNat * 2 ^ 64 := by rw [hadd]
        _ = (pLo.toNat + pHi.toNat * 2 ^ 64) + carry.toNat := by ac_rfl
        _ = (getLimb a i).toNat * m.toNat + carry.toNat := by rw [hmul]
    have hih := ih (i + 1) carry' (acc.push lo) (by simp [hsz])
    have hidx : i + 1 + rem = i + (rem + 1) := by omega
    rw [hidx, toNat_push, hsz, toNatPrefix_succ a i, Nat.pow_succ (2 ^ 64), Nat.add_mul] at hih
    have hstep := congrArg (· * (2 ^ 64) ^ i) hspec
    rw [Nat.add_mul, Nat.add_mul] at hstep
    have hr1 : carry'.toNat * ((2 ^ 64) ^ i * 2 ^ 64) = carry'.toNat * 2 ^ 64 * (2 ^ 64) ^ i := by
      rw [Nat.mul_comm ((2 ^ 64) ^ i) (2 ^ 64), ← Nat.mul_assoc]
    have hr2 : (getLimb a i).toNat * (2 ^ 64) ^ i * m.toNat = (getLimb a i).toNat * m.toNat * (2 ^ 64) ^ i := by
      rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ i) m.toNat, ← Nat.mul_assoc]
    rw [hr1, hr2] at hih
    dsimp only [carry'] at hih hstep
    clear hm ha hmul hadd hcar_lt hcar'_toNat hspec hr1 hr2
    omega

theorem wf_mulAdd1 (a : Array UInt64) (m c : UInt64) : WF (mulAdd1 a m c) := by
  unfold mulAdd1
  split
  · exact wf_ofUInt64 c
  · split
    · exact wf_normalize a
    · split
      · exact wf_shiftLeft1 a
      · exact wf_normalize _

theorem toNat_mulAdd1 (a : Array UInt64) (m c : UInt64) :
    toNat (mulAdd1 a m c) = toNat a * m.toNat + c.toNat := by
  unfold mulAdd1
  split
  · rename_i hm0
    have hm : m = 0 := eq_of_beq hm0
    subst hm; simp [toNat_ofUInt64]
  · split
    · rename_i _ h10
      have ⟨hm1, hc0⟩ := Bool.and_eq_true _ _ |>.mp h10
      have hm : m = 1 := eq_of_beq hm1
      have hc : c = 0 := eq_of_beq hc0
      subst hm; subst hc
      rw [toNat_normalize]; simp
    · split
      · rename_i _ _ h20
        have ⟨hm2, hc0⟩ := Bool.and_eq_true _ _ |>.mp h20
        have hm : m = 2 := eq_of_beq hm2
        have hc : c = 0 := eq_of_beq hc0
        subst hm; subst hc
        rw [toNat_shiftLeft1]; simp
      · rw [toNat_normalize]
        have h := toNat_mulAdd1Loop a m 0 a.size c (Array.mkEmpty (a.size + 1)) (by simp)
        simp only [toNatPrefix_zero, toNat_mkEmpty, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
          Nat.pow_zero, Nat.mul_one] at h
        rw [h, Nat.add_comm]
        rfl

/-! ### Base-`10^19` Chunk Conversion Specifications -/

/-- Specification: big-endian base-`10^19` valuation with accumulator. -/
def chunksToNatAux (acc : Nat) : List UInt64 → Nat
  | [] => acc
  | c :: rest => chunksToNatAux (acc * 10 ^ 19 + c.toNat) rest

/-- Specification: exact `Nat` value of a big-endian list of base-`10^19` chunks. -/
def chunksToNat (cs : List UInt64) : Nat :=
  chunksToNatAux 0 cs

private theorem chunksToNatAux_eq (acc : Nat) (cs : List UInt64) :
    chunksToNatAux acc cs = acc * (10 ^ 19) ^ cs.length + chunksToNatAux 0 cs := by
  induction cs generalizing acc with
  | nil => simp [chunksToNatAux]
  | cons c rest ih =>
    simp only [chunksToNatAux, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (acc * 10 ^ 19 + c.toNat), ih c.toNat, Nat.pow_succ (10 ^ 19), Nat.add_mul]
    have hr : acc * 10 ^ 19 * (10 ^ 19) ^ rest.length = acc * ((10 ^ 19) ^ rest.length * 10 ^ 19) := by
      rw [Nat.mul_assoc, Nat.mul_comm (10 ^ 19) ((10 ^ 19) ^ rest.length)]
    rw [hr]
    omega

private theorem chunksToNat_cons (c : UInt64) (rest : List UInt64) :
    chunksToNat (c :: rest) = c.toNat * (10 ^ 19) ^ rest.length + chunksToNat rest := by
  unfold chunksToNat
  simp only [chunksToNatAux, Nat.zero_mul, Nat.zero_add]
  exact chunksToNatAux_eq c.toNat rest

private theorem chunksToNat_append_singleton (cs : List UInt64) (c : UInt64) :
    chunksToNat (cs ++ [c]) = chunksToNat cs * 10 ^ 19 + c.toNat := by
  suffices ∀ acc, chunksToNatAux acc (cs ++ [c]) = chunksToNatAux acc cs * 10 ^ 19 + c.toNat from
    this 0
  intro acc
  induction cs generalizing acc with
  | nil => simp [chunksToNatAux]
  | cons h t ih => simp only [List.cons_append, chunksToNatAux]; exact ih _

private theorem toDecimalChunksLoop_val (a : Array UInt64) (acc : List UInt64) (fuel : Nat)
    (hfuel : toNat a < (10 ^ 19) ^ fuel) :
    chunksToNat (toDecimalChunksLoop a acc fuel) =
      toNat a * (10 ^ 19) ^ acc.length + chunksToNat acc := by
  induction fuel generalizing a acc with
  | zero =>
    unfold toDecimalChunksLoop
    simp only [Nat.pow_zero] at hfuel
    have ha0 : toNat a = 0 := by omega
    rw [ha0, Nat.zero_mul, Nat.zero_add]
  | succ fuel ih =>
    unfold toDecimalChunksLoop
    split
    · rename_i hz
      have hsz0 : a.size = 0 := eq_of_beq hz
      have ha0 : toNat a = 0 := by rw [toNat, hsz0]; rfl
      rw [ha0, Nat.zero_mul, Nat.zero_add]
    · dsimp only
      have ⟨_, hdiv, hmod, _⟩ := divMod1_spec a ten19 ten19_ne_zero
      have hfuel' : toNat (divMod1 a ten19).1 < (10 ^ 19) ^ fuel := by
        rw [hdiv, ten19_toNat]
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        simpa [Nat.pow_succ] using hfuel
      rw [ih (divMod1 a ten19).1 ((divMod1 a ten19).2 :: acc) hfuel']
      rw [List.length_cons, chunksToNat_cons, hdiv, hmod, ten19_toNat, Nat.pow_succ (10 ^ 19)]
      have hdm := Nat.div_add_mod (toNat a) (10 ^ 19)
      have h1 : toNat a / 10 ^ 19 * ((10 ^ 19) ^ acc.length * 10 ^ 19) +
          toNat a % 10 ^ 19 * (10 ^ 19) ^ acc.length =
          (10 ^ 19 * (toNat a / 10 ^ 19) + toNat a % 10 ^ 19) * (10 ^ 19) ^ acc.length := by
        rw [Nat.add_mul, Nat.mul_comm ((10 ^ 19) ^ acc.length) (10 ^ 19), ← Nat.mul_assoc,
            Nat.mul_comm (toNat a / 10 ^ 19) (10 ^ 19)]
      rw [← Nat.add_assoc, h1, hdm]

private theorem toDecimalChunksLoop_lt (a : Array UInt64) (acc : List UInt64) (fuel : Nat)
    (hacc : ∀ c ∈ acc, c.toNat < 10 ^ 19) :
    ∀ c ∈ toDecimalChunksLoop a acc fuel, c.toNat < 10 ^ 19 := by
  induction fuel generalizing a acc with
  | zero => exact hacc
  | succ fuel ih =>
    unfold toDecimalChunksLoop
    split
    · exact hacc
    · dsimp only
      have ⟨_, _, hmod, _⟩ := divMod1_spec a ten19 ten19_ne_zero
      apply ih (divMod1 a ten19).1 ((divMod1 a ten19).2 :: acc)
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hmem
      · rw [hmod, ten19_toNat]
        exact Nat.mod_lt _ (by omega)
      · exact hacc c hmem

theorem toDecimalChunks_spec (a : Array UInt64) :
    chunksToNat (toDecimalChunks a) = toNat a ∧
    ∀ c ∈ toDecimalChunks a, c.toNat < 10 ^ 19 := by
  unfold toDecimalChunks
  dsimp only
  have hfuel : toNat (normalize a) < (10 ^ 19) ^ ((normalize a).size * 2 + 1) := by
    have hlt := toNat_lt (normalize a)
    have hbase : 2 ^ 64 ≤ (10 ^ 19) ^ 2 := by decide
    have hpow1 : (2 ^ 64) ^ (normalize a).size ≤ (10 ^ 19) ^ ((normalize a).size * 2) := by
      rw [Nat.mul_comm, Nat.pow_mul]
      exact Nat.pow_le_pow_left hbase _
    have hpow2 : (10 ^ 19) ^ ((normalize a).size * 2) ≤ (10 ^ 19) ^ ((normalize a).size * 2 + 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
    exact Nat.lt_of_lt_of_le hlt (Nat.le_trans hpow1 hpow2)
  constructor
  · have h := toDecimalChunksLoop_val (normalize a) [] ((normalize a).size * 2 + 1) hfuel
    simp only [List.length_nil, Nat.pow_zero, Nat.mul_one, chunksToNat, chunksToNatAux,
      Nat.add_zero, toNat_normalize] at h
    exact h
  · exact toDecimalChunksLoop_lt (normalize a) [] ((normalize a).size * 2 + 1) (fun _ h => nomatch h)

private theorem ofDecimalChunksLoop_spec (cs : List UInt64) (acc : Array UInt64) (hacc : WF acc) :
    WF (ofDecimalChunksLoop cs acc) ∧
    toNat (ofDecimalChunksLoop cs acc) = chunksToNatAux (toNat acc) cs := by
  induction cs generalizing acc with
  | nil => exact ⟨hacc, rfl⟩
  | cons c rest ih =>
    unfold ofDecimalChunksLoop
    have ⟨hwf, hto⟩ := ih (mulAdd1 acc ten19 c) (wf_mulAdd1 _ _ _)
    rw [toNat_mulAdd1, ten19_toNat] at hto
    exact ⟨hwf, hto⟩

theorem wf_ofDecimalChunks (cs : List UInt64) : WF (ofDecimalChunks cs) :=
  (ofDecimalChunksLoop_spec cs #[] wf_zero).1

theorem toNat_ofDecimalChunks (cs : List UInt64) :
    toNat (ofDecimalChunks cs) = chunksToNat cs :=
  (ofDecimalChunksLoop_spec cs #[] wf_zero).2

theorem ofDecimalChunks_toDecimalChunks {a : Array UInt64} (ha : WF a) :
    ofDecimalChunks (toDecimalChunks a) = a := by
  apply toNat_inj (wf_ofDecimalChunks _) ha
  rw [toNat_ofDecimalChunks, (toDecimalChunks_spec a).1]

/-! ### Decimal Digits and ASCII String Specifications -/

/-- Specification: big-endian base-10 valuation with accumulator. -/
def digitsToNatAux (acc : Nat) : List UInt8 → Nat
  | [] => acc
  | d :: rest => digitsToNatAux (acc * 10 + d.toNat) rest

/-- Specification: exact `Nat` value of a big-endian list of decimal digits `0..9`. -/
def digitsToNat (ds : List UInt8) : Nat :=
  digitsToNatAux 0 ds

private theorem digitsToNatAux_eq (acc : Nat) (ds : List UInt8) :
    digitsToNatAux acc ds = acc * 10 ^ ds.length + digitsToNatAux 0 ds := by
  induction ds generalizing acc with
  | nil => simp [digitsToNatAux]
  | cons d rest ih =>
    simp only [digitsToNatAux, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (acc * 10 + d.toNat), ih d.toNat, Nat.pow_succ, Nat.add_mul]
    have hr : acc * 10 * 10 ^ rest.length = acc * (10 ^ rest.length * 10) := by
      rw [Nat.mul_assoc, Nat.mul_comm 10 (10 ^ rest.length)]
    rw [hr]
    omega

private theorem digitsToNat_cons (d : UInt8) (rest : List UInt8) :
    digitsToNat (d :: rest) = d.toNat * 10 ^ rest.length + digitsToNat rest := by
  unfold digitsToNat
  simp only [digitsToNatAux, Nat.zero_mul, Nat.zero_add]
  exact digitsToNatAux_eq d.toNat rest

private theorem uint64_mod10_toUInt8_toNat (x : UInt64) :
    (x % (10 : UInt64)).toUInt8.toNat = x.toNat % 10 := by
  rw [UInt64.toNat_toUInt8, UInt64.toNat_mod]
  have h10 : (10 : UInt64).toNat = 10 := rfl
  rw [h10]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

private theorem uint64_div10_toNat (x : UInt64) :
    (x / (10 : UInt64)).toNat = x.toNat / 10 := by
  rw [UInt64.toNat_div]; rfl

private theorem u64ToDigitsPad_spec (x : UInt64) (k : Nat) (acc : List UInt8)
    (hacc : ∀ d ∈ acc, d.toNat < 10) :
    (u64ToDigitsPad x k acc).length = k + acc.length ∧
    digitsToNat (u64ToDigitsPad x k acc) = (x.toNat % 10 ^ k) * 10 ^ acc.length + digitsToNat acc ∧
    ∀ d ∈ u64ToDigitsPad x k acc, d.toNat < 10 := by
  induction k generalizing x acc with
  | zero =>
    exact ⟨by simp [u64ToDigitsPad], by simp [u64ToDigitsPad, Nat.mod_one], hacc⟩
  | succ k ih =>
    unfold u64ToDigitsPad
    dsimp only
    let d := (x % (10 : UInt64)).toUInt8
    have hd : d.toNat = x.toNat % 10 := uint64_mod10_toUInt8_toNat x
    have hacc' : ∀ e ∈ d :: acc, e.toNat < 10 := by
      intro e he
      rcases List.mem_cons.mp he with rfl | hm
      · rw [hd]; exact Nat.mod_lt _ (by decide)
      · exact hacc e hm
    have ⟨hlen, hval, hlt⟩ := ih (x / (10 : UInt64)) (d :: acc) hacc'
    refine ⟨by rw [hlen]; simp only [List.length_cons]; omega, ?_, hlt⟩
    rw [hval, List.length_cons, digitsToNat_cons, hd, uint64_div10_toNat, Nat.pow_succ 10 acc.length,
        Nat.pow_succ 10 k]
    have hmod : x.toNat % (10 ^ k * 10) = (x.toNat / 10 % 10 ^ k) * 10 + x.toNat % 10 := by
      rw [Nat.mul_comm (10 ^ k) 10, Nat.mod_mul, Nat.mul_comm 10, Nat.add_comm]
    rw [hmod, Nat.add_mul]
    have hr : x.toNat / 10 % 10 ^ k * (10 ^ acc.length * 10) =
        x.toNat / 10 % 10 ^ k * 10 * 10 ^ acc.length := by
      rw [Nat.mul_comm (10 ^ acc.length) 10, ← Nat.mul_assoc]
    rw [hr]
    omega

private theorem u64ToDigitsMinimalLoop_len_ge (y : UInt64) (l : List UInt8) (fuel : Nat) :
    l.length ≤ (u64ToDigitsMinimalLoop y l fuel).length := by
  induction fuel generalizing y l with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    unfold u64ToDigitsMinimalLoop
    split
    · exact Nat.le_refl _
    · dsimp only
      have h := ih (y / (10 : UInt64)) ((y % (10 : UInt64)).toUInt8 :: l)
      simp only [List.length_cons] at h
      omega

private theorem u64ToDigitsMinimalLoop_spec (x : UInt64) (acc : List UInt8) (fuel : Nat)
    (hfuel : x.toNat < 10 ^ fuel)
    (hacc : ∀ d ∈ acc, d.toNat < 10) :
    digitsToNat (u64ToDigitsMinimalLoop x acc fuel) = x.toNat * 10 ^ acc.length + digitsToNat acc ∧
    (x ≠ 0 → u64ToDigitsMinimalLoop x acc fuel ≠ []) ∧
    ∀ d ∈ u64ToDigitsMinimalLoop x acc fuel, d.toNat < 10 := by
  induction fuel generalizing x acc with
  | zero =>
    unfold u64ToDigitsMinimalLoop
    simp only [Nat.pow_zero] at hfuel
    have hx0 : x = 0 := UInt64.toNat_inj.mp (by rw [UInt64.toNat_zero]; omega)
    subst hx0
    exact ⟨by simp, fun h => absurd rfl h, hacc⟩
  | succ fuel ih =>
    unfold u64ToDigitsMinimalLoop
    split
    · rename_i hx0_beq
      have hx0 : x = 0 := eq_of_beq hx0_beq
      subst hx0
      exact ⟨by simp, fun h => absurd rfl h, hacc⟩
    · dsimp only
      let d := (x % (10 : UInt64)).toUInt8
      have hd : d.toNat = x.toNat % 10 := uint64_mod10_toUInt8_toNat x
      have hfuel' : (x / (10 : UInt64)).toNat < 10 ^ fuel := by
        rw [uint64_div10_toNat, Nat.div_lt_iff_lt_mul (by decide)]
        simpa [Nat.pow_succ] using hfuel
      have hacc' : ∀ e ∈ d :: acc, e.toNat < 10 := by
        intro e he
        rcases List.mem_cons.mp he with rfl | hm
        · rw [hd]; exact Nat.mod_lt _ (by decide)
        · exact hacc e hm
      have ⟨hval, _, hlt⟩ := ih (x / (10 : UInt64)) (d :: acc) hfuel' hacc'
      refine ⟨?_, ?_, hlt⟩
      · rw [hval, List.length_cons, digitsToNat_cons, hd, uint64_div10_toNat, Nat.pow_succ]
        have hdm := Nat.div_add_mod x.toNat 10
        have hr : x.toNat / 10 * (10 ^ acc.length * 10) = 10 * (x.toNat / 10) * 10 ^ acc.length := by
          rw [Nat.mul_comm (10 ^ acc.length) 10, ← Nat.mul_assoc, Nat.mul_comm (x.toNat / 10) 10]
        rw [← Nat.add_assoc, hr, ← Nat.add_mul, hdm]
      · intro _ hempty
        have hge := u64ToDigitsMinimalLoop_len_ge (x / (10 : UInt64)) (d :: acc) fuel
        simp only [List.length_cons] at hge
        rw [hempty] at hge
        simp at hge

private theorem u64ToDigitsMinimal_spec (x : UInt64) (acc : List UInt8)
    (hacc : ∀ d ∈ acc, d.toNat < 10) :
    digitsToNat (u64ToDigitsMinimal x acc) = x.toNat * 10 ^ acc.length + digitsToNat acc ∧
    (x ≠ 0 → u64ToDigitsMinimal x acc ≠ []) ∧
    ∀ d ∈ u64ToDigitsMinimal x acc, d.toNat < 10 := by
  have hx : x.toNat < 10 ^ 20 := Nat.lt_trans (uint64_toNat_lt x) (by decide)
  exact u64ToDigitsMinimalLoop_spec x acc 20 hx hacc

private theorem chunksRevToDigits_spec (revChunks : List UInt64) (acc : List UInt8)
    (hlt : ∀ c ∈ revChunks, c.toNat < 10 ^ 19)
    (hacc : ∀ d ∈ acc, d.toNat < 10) :
    digitsToNat (chunksRevToDigits revChunks acc) =
      chunksToNat revChunks.reverse * 10 ^ acc.length + digitsToNat acc ∧
    (revChunks ≠ [] → chunksRevToDigits revChunks acc ≠ []) ∧
    ∀ d ∈ chunksRevToDigits revChunks acc, d.toNat < 10 := by
  induction revChunks generalizing acc with
  | nil =>
    simp [chunksRevToDigits, chunksToNat, chunksToNatAux]
    exact hacc
  | cons c rest ih =>
    cases rest with
    | nil =>
      unfold chunksRevToDigits
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, chunksToNat, chunksToNatAux,
        Nat.zero_mul, Nat.zero_add]
      split
      · rename_i hc0
        have hc : c = 0 := eq_of_beq hc0
        subst hc
        cases acc with
        | nil =>
          refine ⟨by decide, fun _ => by simp, ?_⟩
          intro d hd
          simp only [List.mem_singleton] at hd
          subst hd; decide
        | cons a l =>
          exact ⟨by simp, fun _ => by simp, hacc⟩
      · rename_i hcne
        have hne : c ≠ 0 := fun h => hcne (by simp [h])
        have ⟨hval, hnonempty, hdlt⟩ := u64ToDigitsMinimal_spec c acc hacc
        exact ⟨hval, fun _ => hnonempty hne, hdlt⟩
    | cons c2 rest2 =>
      unfold chunksRevToDigits
      have hc_lt : c.toNat < 10 ^ 19 := hlt c (List.mem_cons_self ..)
      have hrest_lt : ∀ x ∈ c2 :: rest2, x.toNat < 10 ^ 19 :=
        fun x hx => hlt x (List.mem_cons_of_mem c hx)
      have ⟨hlen_p, hval_p, hdlt_p⟩ := u64ToDigitsPad_spec c 19 acc hacc
      rw [Nat.mod_eq_of_lt hc_lt] at hval_p
      have ⟨hval, hnonempty, hdlt⟩ := ih (u64ToDigitsPad c 19 acc) hrest_lt hdlt_p
      refine ⟨?_, fun _ => hnonempty (by simp), hdlt⟩
      rw [hval, hlen_p, hval_p, List.reverse_cons (a := c), chunksToNat_append_singleton,
          Nat.pow_add, Nat.add_mul, Nat.mul_assoc]
      omega

theorem toDecimalDigits_spec (a : Array UInt64) :
    digitsToNat (toDecimalDigits a) = toNat a ∧
    toDecimalDigits a ≠ [] ∧
    ∀ d ∈ toDecimalDigits a, d.toNat < 10 := by
  unfold toDecimalDigits
  have ⟨hval, hlt⟩ := toDecimalChunks_spec a
  cases hcs : toDecimalChunks a with
  | nil =>
    rw [hcs] at hval
    simp only [chunksToNat, chunksToNatAux] at hval
    refine ⟨by rw [← hval]; decide, by simp, ?_⟩
    intro d hd; simp only [List.mem_singleton] at hd; subst hd; decide
  | cons c rest =>
    rw [hcs] at hval hlt
    have hrev_lt : ∀ x ∈ (c :: rest).reverse, x.toNat < 10 ^ 19 := by
      intro x hx; exact hlt x (List.mem_reverse.mp hx)
    have ⟨hv, hne, hdlt⟩ := chunksRevToDigits_spec (c :: rest).reverse [] hrev_lt (fun _ h => nomatch h)
    rw [List.reverse_reverse, List.length_nil, Nat.pow_zero, Nat.mul_one, hval] at hv
    simp only [digitsToNat, digitsToNatAux, Nat.add_zero] at hv
    exact ⟨hv, hne (by simp), hdlt⟩

private theorem ofDecimalDigitsLoop_spec (ds : List UInt8) (chunkVal chunkPow : UInt64)
    (cnt : Nat) (acc : Array UInt64)
    (hacc : WF acc) (hcnt : cnt < 19)
    (hpow : chunkPow.toNat = 10 ^ cnt) (hval : chunkVal.toNat < 10 ^ cnt)
    (hds : ∀ d ∈ ds, d.toNat < 10) :
    WF (ofDecimalDigitsLoop ds chunkVal chunkPow cnt acc) ∧
    toNat (ofDecimalDigitsLoop ds chunkVal chunkPow cnt acc) =
      digitsToNatAux (toNat acc * chunkPow.toNat + chunkVal.toNat) ds := by
  induction ds generalizing chunkVal chunkPow cnt acc with
  | nil =>
    unfold ofDecimalDigitsLoop
    simp only [digitsToNatAux]
    split
    · rename_i hc0
      have hc : cnt = 0 := eq_of_beq hc0
      subst hc
      simp only [Nat.pow_zero] at hpow hval
      have hv0 : chunkVal.toNat = 0 := by omega
      rw [hpow, hv0, Nat.mul_one, Nat.add_zero]
      exact ⟨hacc, rfl⟩
    · exact ⟨wf_mulAdd1 _ _ _, toNat_mulAdd1 _ _ _⟩
  | cons d rest ih =>
    unfold ofDecimalDigitsLoop
    dsimp only
    have hd_lt : d.toNat < 10 := hds d (List.mem_cons_self ..)
    have hrest_lt : ∀ e ∈ rest, e.toNat < 10 := fun e he => hds e (List.mem_cons_of_mem d he)
    have h10_19_lt : 10 ^ 19 < 2 ^ 64 := by omega
    have hpow_next_le : 10 ^ (cnt + 1) ≤ 10 ^ 19 := Nat.pow_le_pow_right (by decide) (by omega)
    have hv_toNat : (chunkVal * (10 : UInt64) + d.toUInt64).toNat = chunkVal.toNat * 10 + d.toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64]
      have h10 : (10 : UInt64).toNat = 10 := rfl
      rw [h10]
      have h1 : chunkVal.toNat * 10 < 10 ^ (cnt + 1) := by
        rw [Nat.pow_succ]; exact Nat.mul_lt_mul_of_pos_right hval (by decide)
      have h2 : chunkVal.toNat * 10 + d.toNat < 10 ^ (cnt + 1) := by
        rw [Nat.pow_succ]
        have : chunkVal.toNat + 1 ≤ 10 ^ cnt := hval
        have : (chunkVal.toNat + 1) * 10 ≤ 10 ^ cnt * 10 := Nat.mul_le_mul_right 10 this
        omega
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hp_toNat : (chunkPow * (10 : UInt64)).toNat = 10 ^ (cnt + 1) := by
      rw [UInt64.toNat_mul, hpow]
      have h10 : (10 : UInt64).toNat = 10 := rfl
      rw [h10, ← Nat.pow_succ]
      exact Nat.mod_eq_of_lt (by omega)
    have hv_lt : (chunkVal * (10 : UInt64) + d.toUInt64).toNat < 10 ^ (cnt + 1) := by
      rw [hv_toNat, Nat.pow_succ]
      have : chunkVal.toNat + 1 ≤ 10 ^ cnt := hval
      have : (chunkVal.toNat + 1) * 10 ≤ 10 ^ cnt * 10 := Nat.mul_le_mul_right 10 this
      omega
    have hstep_eq : toNat acc * (chunkPow * (10 : UInt64)).toNat +
        (chunkVal * (10 : UInt64) + d.toUInt64).toNat =
        (toNat acc * chunkPow.toNat + chunkVal.toNat) * 10 + d.toNat := by
      rw [hp_toNat, hv_toNat, hpow, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc]
      omega
    split
    · have ⟨hwf, hto⟩ := ih 0 1 0
        (mulAdd1 acc (chunkPow * (10 : UInt64)) (chunkVal * (10 : UInt64) + d.toUInt64))
        (wf_mulAdd1 _ _ _) (by decide) (by decide) (by decide) hrest_lt
      rw [toNat_mulAdd1] at hto
      have h1 : (1 : UInt64).toNat = 1 := rfl
      have h0 : (0 : UInt64).toNat = 0 := rfl
      rw [h1, h0, Nat.mul_one, Nat.add_zero, hstep_eq] at hto
      exact ⟨hwf, hto⟩
    · rename_i hne19
      have hcnt' : cnt + 1 < 19 := by
        have : cnt + 1 ≠ 19 := fun h => hne19 (by simp [h])
        omega
      have ⟨hwf, hto⟩ := ih _ _ (cnt + 1) acc hacc hcnt' hp_toNat hv_lt hrest_lt
      rw [hstep_eq] at hto
      exact ⟨hwf, hto⟩

theorem wf_ofDecimalDigits (ds : List UInt8) : WF (ofDecimalDigits ds) := by
  -- Note: even without hds, ofDecimalDigits only ever returns #[] or mulAdd1 ... which is WF!
  suffices ∀ l cv cp c acc, WF acc → WF (ofDecimalDigitsLoop l cv cp c acc) from
    this ds 0 1 0 #[] wf_zero
  intro l
  induction l with
  | nil =>
    intro cv cp c acc hacc
    unfold ofDecimalDigitsLoop
    split
    · exact hacc
    · exact wf_mulAdd1 _ _ _
  | cons d rest ih =>
    intro cv cp c acc hacc
    unfold ofDecimalDigitsLoop
    dsimp only
    split
    · exact ih _ _ _ _ (wf_mulAdd1 _ _ _)
    · exact ih _ _ _ _ hacc

theorem toNat_ofDecimalDigits (ds : List UInt8) (hds : ∀ d ∈ ds, d.toNat < 10) :
    toNat (ofDecimalDigits ds) = digitsToNat ds := by
  unfold ofDecimalDigits
  have ⟨_, hto⟩ := ofDecimalDigitsLoop_spec ds 0 1 0 #[] wf_zero (by decide)
    (by decide) (by decide) hds
  simpa [digitsToNat] using hto

theorem ofDecimalDigits_toDecimalDigits {a : Array UInt64} (ha : WF a) :
    ofDecimalDigits (toDecimalDigits a) = a := by
  have ⟨hval, _, hdlt⟩ := toDecimalDigits_spec a
  apply toNat_inj (wf_ofDecimalDigits _) ha
  rw [toNat_ofDecimalDigits _ hdlt, hval]

private theorem digitsToCharsLoop_eq (ds : List UInt8) (acc : List Char) :
    digitsToCharsLoop ds acc = acc.reverse ++ ds.map (fun d => Char.ofNat (48 + d.toNat)) := by
  induction ds generalizing acc with
  | nil => simp [digitsToCharsLoop]
  | cons d rest ih =>
    simp only [digitsToCharsLoop, ih, List.reverse_cons, List.map_cons, List.append_assoc,
      List.singleton_append]

private theorem parseAsciiDigitsLoop_map (ds : List UInt8) (hds : ∀ d ∈ ds, d.toNat < 10)
    (acc : List UInt8) :
    parseAsciiDigitsLoop (ds.map (fun d => Char.ofNat (48 + d.toNat))) acc =
      some (acc.reverse ++ ds) := by
  induction ds generalizing acc with
  | nil => simp [parseAsciiDigitsLoop]
  | cons d rest ih =>
    have hd : d.toNat < 10 := hds d (List.mem_cons_self ..)
    have hrest : ∀ e ∈ rest, e.toNat < 10 := fun e he => hds e (List.mem_cons_of_mem d he)
    simp only [List.map_cons, parseAsciiDigitsLoop]
    have hvalid : (Char.ofNat (48 + d.toNat)).toNat = 48 + d.toNat := by
      have hv : Nat.isValidChar (48 + d.toNat) := Or.inl (by omega)
      simp only [Char.ofNat, hv, ↓reduceDIte, Char.toNat, Char.ofNatAux]
      rfl
    rw [hvalid]
    have hcond : (decide (48 ≤ 48 + d.toNat) && decide (48 + d.toNat ≤ 57)) = true := by
      simp; omega
    simp only [hcond, ↓reduceIte]
    have hsub : UInt8.ofNat (48 + d.toNat - 48) = d := by
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_ofNat']
      have : 48 + d.toNat - 48 = d.toNat := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [hsub, ih hrest (d :: acc)]
    simp [List.reverse_cons, List.append_assoc]

theorem wf_ofDecimal {s : String} {a : Array UInt64} (h : ofDecimal s = some a) : WF a := by
  unfold ofDecimal at h
  cases hs : s.toList with
  | nil => rw [hs] at h; simp at h
  | cons c cs =>
    rw [hs] at h
    dsimp only at h
    cases hp : parseAsciiDigitsLoop (c :: cs) [] with
    | none => rw [hp] at h; simp at h
    | some ds =>
      rw [hp] at h
      simp only [Option.some.injEq] at h
      rw [← h]
      exact wf_ofDecimalDigits ds

theorem ofDecimal_toDecimal {a : Array UInt64} (ha : WF a) :
    ofDecimal (toDecimal a) = some a := by
  unfold ofDecimal toDecimal
  rw [digitsToCharsLoop_eq, List.reverse_nil, List.nil_append, String.toList_ofList]
  have ⟨_, hne, hdlt⟩ := toDecimalDigits_spec a
  cases hds : toDecimalDigits a with
  | nil => exact absurd hds hne
  | cons d rest =>
    rw [hds] at hdlt
    simp only [List.map_cons]
    have hparse := parseAsciiDigitsLoop_map (d :: rest) hdlt []
    simp only [List.map_cons, List.reverse_nil, List.nil_append] at hparse
    rw [hparse]
    dsimp only
    rw [← hds, ofDecimalDigits_toDecimalDigits ha]

end IxCC.BigNat
