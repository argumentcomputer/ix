import IxCC.BigNat.GcdConv
import IxCC.BigNat.Proof.Div

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

/-! ### Euclidean GCD (`gcd`) -/

private theorem gcdLoop_spec (a b : Array UInt64) (ha : WF a) (hb : WF b) :
    WF (gcdLoop a b hb) ∧ toNat (gcdLoop a b hb) = Nat.gcd (toNat a) (toNat b) := by
  induction hn : toNat b using Nat.strongRecOn generalizing a b with
  | ind n ih =>
    unfold gcdLoop
    split
    · rename_i hz
      have hb0 : toNat b = 0 := by rw [toNat, hz]; rfl
      rw [← hn, hb0, Nat.gcd_zero_right]
      exact ⟨ha, rfl⟩
    · rename_i hne
      have hlt : toNat (mod a b) < n := by rw [← hn]; exact toNat_mod_lt a b hb hne
      have ⟨hwf, hto⟩ := ih (toNat (mod a b)) hlt b (mod a b) hb (wf_mod a b) rfl
      refine ⟨hwf, ?_⟩
      rw [hto, toNat_mod, ← hn]
      rw [Nat.gcd_comm (toNat a) (toNat b), Nat.gcd_rec (toNat b) (toNat a), Nat.gcd_comm]

theorem wf_gcd (a b : Array UInt64) : WF (gcd a b) :=
  (gcdLoop_spec (normalize a) (normalize b) (wf_normalize a) (wf_normalize b)).1

theorem toNat_gcd (a b : Array UInt64) : toNat (gcd a b) = Nat.gcd (toNat a) (toNat b) := by
  unfold gcd
  have h := (gcdLoop_spec (normalize a) (normalize b) (wf_normalize a) (wf_normalize b)).2
  rw [toNat_normalize, toNat_normalize] at h
  exact h

/-! ### Single-Limb Multiply-Add (`mulAdd1`) -/

private theorem toNat_mulAdd1Loop (a : Array UInt64) (m : UInt64) (i : Nat)
    (carry : UInt64) (acc : Array UInt64) (hi : i ≤ a.size) (hsz : acc.size = i) :
    toNat (mulAdd1Loop a m i carry acc) + toNatPrefix a i * m.toNat =
      toNat acc + carry.toNat * (2 ^ 64) ^ i + toNat a * m.toNat := by
  induction hd : a.size - i generalizing i carry acc with
  | zero =>
    have hia : i = a.size := by omega
    subst hia
    unfold mulAdd1Loop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    have hto : toNatPrefix a a.size = toNat a := rfl
    rw [hto]
    split
    · rename_i hc0
      have hc : carry = 0 := eq_of_beq hc0
      subst hc
      rw [UInt64.toNat_zero, Nat.zero_mul, Nat.add_zero]
    · rw [toNat_push, hsz]
  | succ d ih =>
    have hlt : i < a.size := by omega
    unfold mulAdd1Loop
    simp only [hlt, ↓reduceDIte]
    have hspec := mulAddCarry64_spec a[i] m 0 carry
    rcases hm : mulAddCarry64 a[i] m 0 carry with ⟨lo, carry'⟩
    rw [hm] at hspec
    dsimp only at hspec ⊢
    have h0N : (0 : UInt64).toNat = 0 := rfl
    rw [h0N, Nat.add_zero] at hspec
    have hih := ih (i + 1) carry' (acc.push lo) (by omega) (by simp [hsz]) (by omega)
    rw [toNat_push, hsz, toNatPrefix_succ a i, getLimb_lt hlt, Nat.pow_succ (2 ^ 64), Nat.add_mul] at hih
    have hstep := congrArg (· * (2 ^ 64) ^ i) hspec
    rw [Nat.add_mul, Nat.add_mul] at hstep
    have hr1 : carry'.toNat * ((2 ^ 64) ^ i * 2 ^ 64) = carry'.toNat * 2 ^ 64 * (2 ^ 64) ^ i := by
      rw [Nat.mul_comm ((2 ^ 64) ^ i) (2 ^ 64), ← Nat.mul_assoc]
    have hr2 : a[i].toNat * (2 ^ 64) ^ i * m.toNat = a[i].toNat * m.toNat * (2 ^ 64) ^ i := by
      rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ i) m.toNat, ← Nat.mul_assoc]
    rw [hr1, hr2] at hih
    omega

theorem wf_mulAdd1 (a : Array UInt64) (m c : UInt64) : WF (mulAdd1 a m c) :=
  wf_normalize _

theorem toNat_mulAdd1 (a : Array UInt64) (m c : UInt64) :
    toNat (mulAdd1 a m c) = toNat a * m.toNat + c.toNat := by
  unfold mulAdd1
  rw [toNat_normalize]
  have h := toNat_mulAdd1Loop a m 0 c (Array.mkEmpty (a.size + 1)) (Nat.zero_le _) (by simp)
  simp only [toNatPrefix_zero, toNat_mkEmpty, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.pow_zero, Nat.mul_one] at h
  omega

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

private theorem toDecimalChunksLoop_val (a : Array UInt64) (ha : WF a) (acc : List UInt64) :
    chunksToNat (toDecimalChunksLoop a ha acc) =
      toNat a * (10 ^ 19) ^ acc.length + chunksToNat acc := by
  induction hn : toNat a using Nat.strongRecOn generalizing a acc with
  | ind n ih =>
    unfold toDecimalChunksLoop
    split
    · rename_i hz
      have ha0 : toNat a = 0 := by rw [toNat, hz]; rfl
      rw [← hn, ha0, Nat.zero_mul, Nat.zero_add]
    · rename_i hne
      dsimp only
      have ⟨hq_wf, hdiv, hmod, _⟩ := divMod1_spec a ten19 ten19_ne_zero
      have hlt : toNat (divMod1 a ten19).1 < n := by
        rw [← hn]
        exact toNat_divMod1_lt a ten19 ha hne ten19_gt_one
      rw [ih (toNat (divMod1 a ten19).1) hlt (divMod1 a ten19).1 hq_wf
          ((divMod1 a ten19).2 :: acc) rfl]
      rw [List.length_cons, chunksToNat_cons, hdiv, hmod, ten19_toNat, Nat.pow_succ (10 ^ 19), ← hn]
      have hdm := Nat.div_add_mod (toNat a) (10 ^ 19)
      have h1 : toNat a / 10 ^ 19 * ((10 ^ 19) ^ acc.length * 10 ^ 19) +
          toNat a % 10 ^ 19 * (10 ^ 19) ^ acc.length =
          (10 ^ 19 * (toNat a / 10 ^ 19) + toNat a % 10 ^ 19) * (10 ^ 19) ^ acc.length := by
        rw [Nat.add_mul, Nat.mul_comm ((10 ^ 19) ^ acc.length) (10 ^ 19), ← Nat.mul_assoc,
            Nat.mul_comm (toNat a / 10 ^ 19) (10 ^ 19)]
      rw [← Nat.add_assoc, h1, hdm]

private theorem toDecimalChunksLoop_lt (a : Array UInt64) (ha : WF a) (acc : List UInt64)
    (hacc : ∀ c ∈ acc, c.toNat < 10 ^ 19) :
    ∀ c ∈ toDecimalChunksLoop a ha acc, c.toNat < 10 ^ 19 := by
  induction hn : toNat a using Nat.strongRecOn generalizing a acc with
  | ind n ih =>
    unfold toDecimalChunksLoop
    split
    · exact hacc
    · rename_i hne
      dsimp only
      have ⟨hq_wf, _, hmod, _⟩ := divMod1_spec a ten19 ten19_ne_zero
      have hlt : toNat (divMod1 a ten19).1 < n := by
        rw [← hn]
        exact toNat_divMod1_lt a ten19 ha hne ten19_gt_one
      apply ih (toNat (divMod1 a ten19).1) hlt (divMod1 a ten19).1 hq_wf
        ((divMod1 a ten19).2 :: acc) _ rfl
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hmem
      · rw [hmod, ten19_toNat]
        exact Nat.mod_lt _ (by omega)
      · exact hacc c hmem

theorem toDecimalChunks_spec (a : Array UInt64) :
    chunksToNat (toDecimalChunks a) = toNat a ∧
    ∀ c ∈ toDecimalChunks a, c.toNat < 10 ^ 19 := by
  unfold toDecimalChunks
  constructor
  · have h := toDecimalChunksLoop_val (normalize a) (wf_normalize a) []
    simp only [List.length_nil, Nat.pow_zero, Nat.mul_one, chunksToNat, chunksToNatAux,
      Nat.add_zero, toNat_normalize] at h
    exact h
  · exact toDecimalChunksLoop_lt (normalize a) (wf_normalize a) [] (fun _ h => nomatch h)

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

private theorem u64ToDigitsMinimal_spec (x : UInt64) (acc : List UInt8)
    (hacc : ∀ d ∈ acc, d.toNat < 10) :
    digitsToNat (u64ToDigitsMinimal x acc) = x.toNat * 10 ^ acc.length + digitsToNat acc ∧
    (x ≠ 0 → u64ToDigitsMinimal x acc ≠ []) ∧
    ∀ d ∈ u64ToDigitsMinimal x acc, d.toNat < 10 := by
  induction hn : x.toNat using Nat.strongRecOn generalizing x acc with
  | ind n ih =>
    unfold u64ToDigitsMinimal
    split
    · rename_i hx0
      subst hx0
      rw [← hn]
      exact ⟨by simp, fun h => absurd rfl h, hacc⟩
    · rename_i hxne
      dsimp only
      let d := (x % (10 : UInt64)).toUInt8
      have hd : d.toNat = x.toNat % 10 := uint64_mod10_toUInt8_toNat x
      have hxpos : 0 < x.toNat := by
        have : x.toNat ≠ 0 := fun h0 => hxne (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      have hltDiv : (x / (10 : UInt64)).toNat < n := by
        rw [uint64_div10_toNat, ← hn]
        exact Nat.div_lt_self hxpos (by decide)
      have hacc' : ∀ e ∈ d :: acc, e.toNat < 10 := by
        intro e he
        rcases List.mem_cons.mp he with rfl | hm
        · rw [hd]; exact Nat.mod_lt _ (by decide)
        · exact hacc e hm
      have ⟨hval, _, hlt⟩ := ih (x / (10 : UInt64)).toNat hltDiv (x / (10 : UInt64)) (d :: acc) hacc' rfl
      refine ⟨?_, ?_, hlt⟩
      · rw [hval, List.length_cons, digitsToNat_cons, hd, uint64_div10_toNat, Nat.pow_succ, ← hn]
        have hdm := Nat.div_add_mod x.toNat 10
        have hr : x.toNat / 10 * (10 ^ acc.length * 10) = 10 * (x.toNat / 10) * 10 ^ acc.length := by
          rw [Nat.mul_comm (10 ^ acc.length) 10, ← Nat.mul_assoc, Nat.mul_comm (x.toNat / 10) 10]
        rw [← Nat.add_assoc, hr, ← Nat.add_mul, hdm]
      · intro _
        -- Output contains at least d (or length > 0): prove length ≥ acc.length + 1
        have hlen_ge : ∀ (y : UInt64) (l : List UInt8), l.length ≤ (u64ToDigitsMinimal y l).length := by
          intro y l
          induction hm : y.toNat using Nat.strongRecOn generalizing y l with
          | ind m ihm =>
            unfold u64ToDigitsMinimal
            split
            · exact Nat.le_refl _
            · rename_i hyne
              dsimp only
              have hypos : 0 < y.toNat := by
                have : y.toNat ≠ 0 := fun h0 => hyne (UInt64.toNat_inj.mp (by simpa using h0))
                omega
              have hdivlt : (y / (10 : UInt64)).toNat < m := by
                rw [uint64_div10_toNat, ← hm]; exact Nat.div_lt_self hypos (by decide)
              have hrec := ihm _ hdivlt (y / (10 : UInt64)) ((y % (10 : UInt64)).toUInt8 :: l) rfl
              simp only [List.length_cons] at hrec
              omega
        have hge := hlen_ge (x / (10 : UInt64)) (d :: acc)
        simp only [List.length_cons] at hge
        intro hempty
        rw [hempty] at hge
        simp at hge

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
