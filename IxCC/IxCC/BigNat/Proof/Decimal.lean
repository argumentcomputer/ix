import IxCC.BigNat.Proof.GcdConv

/-! # Decimal conversion is `Nat.repr` and `Nat.ofDigitChars` (`IxCC.BigNat.Proof.Decimal`)

The round trip `ofDecimal (toDecimal a) = some a` of `IxCC.BigNat.Proof.GcdConv` does not say
which string `toDecimal` prints. This module says it exactly, as an equation with Lean's own
functions on `Nat`:

* `toDecimal_eq_repr`: `toDecimal a = (toNat a).repr` for every limb array (so no leading zero,
  `"0"` for zero);
* `toNat_ofDecimal`: `ofDecimal s` answers exactly on a non-empty string of ASCII digits, and
  then with `Nat.ofDigitChars 10 s.toList 0`, the natural those digits denote. (Unlike
  `String.toNat?`, it does not accept `_` separators.)

The proof of the first: both character lists are non-empty lists of digits that denote
`toNat a` and, for a non-zero value, do not start with `'0'` (for the library's list: the most
significant base-`10^19` chunk is not zero, and it is printed without padding); two such lists
are equal (`eq_of_canonical`).
-/

set_option autoImplicit false

namespace IxCC.BigNat

/-! ## Lists of decimal digit characters -/

private theorem toNat_zero_char : '0'.toNat = 48 := rfl

private theorem toNat_nine_char : '9'.toNat = 57 := rfl

private theorem digit_bounds {c : Char} (h : c.isDigit = true) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  have h1 := Char.isDigit_iff_toNat.mp h
  rw [toNat_zero_char, toNat_nine_char] at h1
  exact h1

private theorem isDigit_of_bounds {c : Char} (h1 : 48 ≤ c.toNat) (h2 : c.toNat ≤ 57) :
    c.isDigit = true := by
  apply Char.isDigit_iff_toNat.mpr
  rw [toNat_zero_char, toNat_nine_char]
  exact And.intro h1 h2

private theorem ofDigitChars_cons_zero (c : Char) (l : List Char) :
    Nat.ofDigitChars 10 (c :: l) 0 = Nat.ofDigitChars 10 l 0 + 10 ^ l.length * (c.toNat - 48) := by
  rw [Nat.ofDigitChars_cons,
    Nat.ofDigitChars_eq_ofDigitChars_zero (init := 10 * 0 + (c.toNat - '0'.toNat)), Nat.mul_zero,
    Nat.zero_add, toNat_zero_char]
  exact Nat.add_comm _ _

private theorem ofDigitChars_lt : ∀ (l : List Char), (∀ c, c ∈ l → c.isDigit = true) →
    Nat.ofDigitChars 10 l 0 < 10 ^ l.length
  | [], _ => by
    rw [Nat.ofDigitChars_nil, List.length_nil, Nat.pow_zero]
    exact Nat.zero_lt_one
  | c :: l, h => by
    have hc := digit_bounds (h c List.mem_cons_self)
    have ih := ofDigitChars_lt l (fun x hx => h x (List.mem_cons_of_mem c hx))
    rw [ofDigitChars_cons_zero, List.length_cons, Nat.pow_succ]
    have h9 : c.toNat - 48 ≤ 9 := by omega
    have hm := Nat.mul_le_mul_left (10 ^ l.length) h9
    omega

/-- A digit list that does not start with `'0'` denotes at least `10 ^ (length - 1)`. -/
private theorem pow_le_ofDigitChars (c : Char) (l : List Char) (hc : c.isDigit = true)
    (h0 : c ≠ '0') : 10 ^ l.length ≤ Nat.ofDigitChars 10 (c :: l) 0 := by
  have hb := digit_bounds hc
  have hne : c.toNat ≠ 48 := fun h => h0 (Char.toNat_inj.mp (h.trans toNat_zero_char.symm))
  rw [ofDigitChars_cons_zero]
  have h1 : 1 ≤ c.toNat - 48 := by omega
  have hm := Nat.mul_le_mul_left (10 ^ l.length) h1
  rw [Nat.mul_one] at hm
  omega

/-- Two digit lists of one length that denote one natural are equal. -/
private theorem eq_of_ofDigitChars_eq : ∀ (l m : List Char), l.length = m.length →
    (∀ c, c ∈ l → c.isDigit = true) → (∀ c, c ∈ m → c.isDigit = true) →
    Nat.ofDigitChars 10 l 0 = Nat.ofDigitChars 10 m 0 → l = m
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => absurd h (by simp)
  | _ :: _, [], h, _, _, _ => absurd h (by simp)
  | c :: l, d :: m, hlen, hl, hm, hv => by
    have hlen' : l.length = m.length := by
      simp only [List.length_cons] at hlen
      omega
    have hl' : ∀ x, x ∈ l → x.isDigit = true := fun x hx => hl x (List.mem_cons_of_mem c hx)
    have hm' : ∀ x, x ∈ m → x.isDigit = true := fun x hx => hm x (List.mem_cons_of_mem d hx)
    have hcb := digit_bounds (hl c List.mem_cons_self)
    have hdb := digit_bounds (hm d List.mem_cons_self)
    have hlu := ofDigitChars_lt l hl'
    have hmu := ofDigitChars_lt m hm'
    rw [ofDigitChars_cons_zero, ofDigitChars_cons_zero, ← hlen'] at hv
    rw [← hlen'] at hmu
    have hP : 0 < 10 ^ l.length := Nat.pow_pos (by decide)
    have hdiv := congrArg (· / 10 ^ l.length) hv
    rw [Nat.add_mul_div_left _ _ hP, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hlu,
      Nat.div_eq_of_lt hmu, Nat.zero_add, Nat.zero_add] at hdiv
    have hmod := congrArg (· % 10 ^ l.length) hv
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlu,
      Nat.mod_eq_of_lt hmu] at hmod
    have hcd : c = d := Char.toNat_inj.mp (by omega)
    rw [hcd, eq_of_ofDigitChars_eq l m hlen' hl' hm' hmod]

/-- **Canonical digit lists are determined by their value**: two lists of digits that do not
start with `'0'` and denote one natural are equal. -/
private theorem eq_of_canonical (c d : Char) (l m : List Char)
    (hl : ∀ x, x ∈ c :: l → x.isDigit = true) (hm : ∀ x, x ∈ d :: m → x.isDigit = true)
    (hc : c ≠ '0') (hd : d ≠ '0')
    (hv : Nat.ofDigitChars 10 (c :: l) 0 = Nat.ofDigitChars 10 (d :: m) 0) : c :: l = d :: m := by
  have h1 := pow_le_ofDigitChars c l (hl c List.mem_cons_self) hc
  have h2 := pow_le_ofDigitChars d m (hm d List.mem_cons_self) hd
  have u1 := ofDigitChars_lt (c :: l) hl
  have u2 := ofDigitChars_lt (d :: m) hm
  rw [List.length_cons] at u1 u2
  have hle1 : l.length ≤ m.length := by
    apply Nat.le_of_not_lt
    intro hlt
    have hp := Nat.pow_le_pow_right (show 10 > 0 by decide)
      (show m.length + 1 ≤ l.length by omega)
    omega
  have hle2 : m.length ≤ l.length := by
    apply Nat.le_of_not_lt
    intro hlt
    have hp := Nat.pow_le_pow_right (show 10 > 0 by decide)
      (show l.length + 1 ≤ m.length by omega)
    omega
  exact eq_of_ofDigitChars_eq (c :: l) (d :: m)
    (by rw [List.length_cons, List.length_cons]; omega) hl hm hv

/-! ## `Nat.toDigits` -/

private theorem toDigits_head : ∀ (fuel n : Nat), n < fuel → n ≠ 0 →
    ∃ c l, Nat.toDigits 10 n = c :: l ∧ c ≠ '0'
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, hf, hn => by
    rw [Nat.toDigits_eq_ite (b := 10) (by decide)]
    by_cases h : n < 10
    · rw [ite_eq_left h]
      exact ⟨_, _, rfl, fun hc => hn (Nat.digitChar_eq_zero.mp hc)⟩
    · rw [ite_eq_right h]
      have hq : n / 10 ≠ 0 := by omega
      obtain ⟨c, l, he, hc⟩ := toDigits_head fuel (n / 10) (by omega) hq
      rw [he]
      exact ⟨c, l ++ [(n % 10).digitChar], rfl, hc⟩

/-! ## The library's digits -/

/-- The character of a decimal digit, as `toDecimal` prints it. -/
private theorem toNat_ofNat_digit {d : UInt8} (h : d.toNat < 10) :
    (Char.ofNat (48 + d.toNat)).toNat = 48 + d.toNat := by
  have hv : Nat.isValidChar (48 + d.toNat) := Or.inl (by omega)
  simp only [Char.ofNat, hv, ↓reduceDIte, Char.toNat, Char.ofNatAux]
  rfl

private theorem digitsToCharsLoop_map (ds : List UInt8) (acc : List Char) :
    digitsToCharsLoop ds acc = acc.reverse ++ ds.map (fun d => Char.ofNat (48 + d.toNat)) := by
  induction ds generalizing acc with
  | nil => simp [digitsToCharsLoop]
  | cons d rest ih =>
    simp only [digitsToCharsLoop, ih, List.reverse_cons, List.map_cons, List.append_assoc,
      List.singleton_append]

private theorem ofDigitChars_map (ds : List UInt8) (hds : ∀ d, d ∈ ds → d.toNat < 10)
    (acc : Nat) :
    Nat.ofDigitChars 10 (ds.map (fun d => Char.ofNat (48 + d.toNat))) acc =
      digitsToNatAux acc ds := by
  induction ds generalizing acc with
  | nil => exact Nat.ofDigitChars_nil
  | cons d rest ih =>
    have hd := hds d List.mem_cons_self
    show Nat.ofDigitChars 10
        (Char.ofNat (48 + d.toNat) :: rest.map (fun d => Char.ofNat (48 + d.toNat))) acc =
      digitsToNatAux (acc * 10 + d.toNat) rest
    rw [Nat.ofDigitChars_cons, toNat_ofNat_digit hd, toNat_zero_char, Nat.add_sub_cancel_left,
      ih (fun x hx => hds x (List.mem_cons_of_mem d hx)), Nat.mul_comm 10 acc]

private theorem isDigit_map (ds : List UInt8) (hds : ∀ d, d ∈ ds → d.toNat < 10) :
    ∀ c, c ∈ ds.map (fun d => Char.ofNat (48 + d.toNat)) → c.isDigit = true := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  show (Char.ofNat (48 + d.toNat)).isDigit = true
  have hd10 := hds d hd
  have h := toNat_ofNat_digit hd10
  exact isDigit_of_bounds (by omega) (by omega)

private theorem minimalLoop_zero (acc : List UInt8) (fuel : Nat) :
    u64ToDigitsMinimalLoop 0 acc fuel = acc := by
  cases fuel with
  | zero => rfl
  | succ f => simp [u64ToDigitsMinimalLoop]

private theorem u64ToNat_ne_zero {x : UInt64} (hx : x ≠ 0) : x.toNat ≠ 0 :=
  fun h => hx (UInt64.toNat_inj.mp (h.trans rfl))

/-- The minimal digits of a non-zero word start with a non-zero digit. -/
private theorem minimalLoop_head (x : UInt64) (acc : List UInt8) (fuel : Nat) (hx : x ≠ 0)
    (hf : x.toNat < 10 ^ fuel) :
    ∃ d rest, u64ToDigitsMinimalLoop x acc fuel = d :: rest ∧ d ≠ 0 := by
  induction fuel generalizing x acc with
  | zero =>
    rw [Nat.pow_zero] at hf
    exact absurd (show x.toNat = 0 by omega) (u64ToNat_ne_zero hx)
  | succ fuel ih =>
    have hxb : (x == 0) = false := by simp [hx]
    simp only [u64ToDigitsMinimalLoop, hxb, Bool.false_eq_true, ↓reduceIte]
    have hq : (x / (10 : UInt64)).toNat = x.toNat / 10 := by rw [UInt64.toNat_div]; rfl
    have hr : ((x % (10 : UInt64)).toUInt8).toNat = x.toNat % 10 := by
      rw [UInt64.toNat_toUInt8, UInt64.toNat_mod]
      have h10 : (10 : UInt64).toNat = 10 := rfl
      rw [h10]
      exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
    by_cases h0 : x / (10 : UInt64) = 0
    · rw [h0, minimalLoop_zero]
      refine ⟨_, _, rfl, ?_⟩
      intro hd
      have hq0 : x.toNat / 10 = 0 := by rw [← hq, h0]; rfl
      have hd0 : ((x % (10 : UInt64)).toUInt8).toNat = 0 := by rw [hd]; rfl
      rw [hr] at hd0
      exact u64ToNat_ne_zero hx (by omega)
    · apply ih (x / (10 : UInt64)) _ h0
      rw [hq, Nat.div_lt_iff_lt_mul (by decide)]
      rw [Nat.pow_succ] at hf
      exact hf

private theorem chunksLoop_size_zero (a : Array UInt64) (acc : List UInt64) (fuel : Nat)
    (h : a.size = 0) : toDecimalChunksLoop a acc fuel = acc := by
  cases fuel with
  | zero => rfl
  | succ f => simp [toDecimalChunksLoop, h]

/-- The most significant base-`10^19` chunk of a non-zero value is not zero. -/
private theorem chunksLoop_head (a : Array UInt64) (acc : List UInt64) (fuel : Nat) (ha : WF a)
    (h0 : toNat a ≠ 0) (hf : toNat a < (10 ^ 19) ^ fuel) :
    ∃ c rest, toDecimalChunksLoop a acc fuel = c :: rest ∧ c ≠ 0 := by
  induction fuel generalizing a acc with
  | zero =>
    rw [Nat.pow_zero] at hf
    omega
  | succ fuel ih =>
    have hsz : a.size ≠ 0 := fun h => h0 ((toNat_eq_zero_iff a ha).mpr h)
    have hsb : (a.size == 0) = false := by simp [hsz]
    simp only [toDecimalChunksLoop, hsb, Bool.false_eq_true, ↓reduceIte]
    have ⟨hwq, hdiv, hmod, _⟩ := divMod1_spec a ten19 ten19_ne_zero
    rw [ten19_toNat] at hdiv hmod
    by_cases hq0 : toNat (divMod1 a ten19).1 = 0
    · rw [chunksLoop_size_zero _ _ _ ((toNat_eq_zero_iff _ hwq).mp hq0)]
      refine ⟨_, _, rfl, ?_⟩
      intro hr
      have hr0 : (divMod1 a ten19).2.toNat = 0 := by rw [hr]; rfl
      rw [hmod] at hr0
      rw [hdiv] at hq0
      have hdm := Nat.div_add_mod (toNat a) (10 ^ 19)
      rw [hq0, Nat.mul_zero, Nat.zero_add, hr0] at hdm
      exact h0 hdm.symm
    · apply ih _ _ hwq hq0
      rw [hdiv, Nat.div_lt_iff_lt_mul (by decide)]
      rw [Nat.pow_succ] at hf
      exact hf

private theorem chunks_fuel (a : Array UInt64) :
    toNat (normalize a) < (10 ^ 19) ^ ((normalize a).size * 2 + 1) := by
  have hlt := toNat_lt (normalize a)
  have hbase : 2 ^ 64 ≤ (10 ^ 19) ^ 2 := by decide
  have hpow1 : (2 ^ 64) ^ (normalize a).size ≤ (10 ^ 19) ^ ((normalize a).size * 2) := by
    rw [Nat.mul_comm, Nat.pow_mul]
    exact Nat.pow_le_pow_left hbase _
  have hpow2 : (10 ^ 19) ^ ((normalize a).size * 2) ≤ (10 ^ 19) ^ ((normalize a).size * 2 + 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  exact Nat.lt_of_lt_of_le hlt (Nat.le_trans hpow1 hpow2)

private theorem toDecimalChunks_zero {a : Array UInt64} (h0 : toNat a = 0) :
    toDecimalChunks a = [] := by
  have h : (normalize a).size = 0 :=
    (toNat_eq_zero_iff _ (wf_normalize a)).mp ((toNat_normalize a).trans h0)
  exact chunksLoop_size_zero (normalize a) [] ((normalize a).size * 2 + 1) h

private theorem toDecimalChunks_head {a : Array UInt64} (h0 : toNat a ≠ 0) :
    ∃ c rest, toDecimalChunks a = c :: rest ∧ c ≠ 0 := by
  show ∃ c rest, toDecimalChunksLoop (normalize a) [] ((normalize a).size * 2 + 1) = c :: rest ∧
    c ≠ 0
  exact chunksLoop_head (normalize a) [] ((normalize a).size * 2 + 1) (wf_normalize a)
    (by rw [toNat_normalize]; exact h0) (chunks_fuel a)

/-- The padded chunks below the most significant one, prepended in order. -/
private def padAll (xs : List UInt64) (acc : List UInt8) : List UInt8 :=
  xs.foldl (fun acc c => u64ToDigitsPad c 19 acc) acc

private theorem chunksRevToDigits_append : ∀ (xs : List UInt64) (h : UInt64) (acc : List UInt8),
    chunksRevToDigits (xs ++ [h]) acc = chunksRevToDigits [h] (padAll xs acc)
  | [], _, _ => rfl
  | [c], h, acc => rfl
  | c :: x :: xs, h, acc => by
    show chunksRevToDigits (x :: xs ++ [h]) (u64ToDigitsPad c 19 acc) = _
    rw [chunksRevToDigits_append (x :: xs) h (u64ToDigitsPad c 19 acc)]
    rfl

/-- The library's digits of a non-zero value start with a non-zero digit. -/
private theorem toDecimalDigits_head {a : Array UInt64} (h0 : toNat a ≠ 0) :
    ∃ d rest, toDecimalDigits a = d :: rest ∧ d ≠ 0 := by
  obtain ⟨c, rest, hcs, hc⟩ := toDecimalChunks_head h0
  unfold toDecimalDigits
  simp only [hcs, List.reverse_cons]
  rw [chunksRevToDigits_append]
  have hcb : (c == 0) = false := by simp [hc]
  simp only [chunksRevToDigits, hcb, Bool.false_eq_true, ↓reduceIte, u64ToDigitsMinimal]
  apply minimalLoop_head c _ 20 hc
  exact Nat.lt_trans (UInt64.toNat_lt c) (by decide)

private theorem toDecimalDigits_zero {a : Array UInt64} (h0 : toNat a = 0) :
    toDecimalDigits a = [0] := by
  unfold toDecimalDigits
  simp only [toDecimalChunks_zero h0]

/-! ## The two equations -/

/-- **`toDecimal` is `Nat.repr`**: the decimal string of the value, for every limb array. -/
theorem toDecimal_eq_repr (a : Array UInt64) : toDecimal a = (toNat a).repr := by
  unfold toDecimal
  rw [digitsToCharsLoop_map, List.reverse_nil, List.nil_append, Nat.repr_eq_ofList_toDigits]
  congr 1
  by_cases h0 : toNat a = 0
  · rw [toDecimalDigits_zero h0, h0, Nat.toDigits_zero 10]
    rfl
  · have ⟨hval, _, hlt⟩ := toDecimalDigits_spec a
    obtain ⟨d, rest, hds, hd⟩ := toDecimalDigits_head h0
    obtain ⟨c, l, htd, hc⟩ := toDigits_head (toNat a + 1) (toNat a) (Nat.lt_succ_self _) h0
    have hdig := isDigit_map (toDecimalDigits a) hlt
    have hv1 := ofDigitChars_map (toDecimalDigits a) hlt 0
    have hv2 : Nat.ofDigitChars 10 (Nat.toDigits 10 (toNat a)) 0 = toNat a :=
      Nat.ofDigitChars_ten_toDigits
    have hdig2 : ∀ x, x ∈ Nat.toDigits 10 (toNat a) → x.isDigit = true :=
      fun x hx => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hx
    rw [hds] at hdig hv1 hlt
    rw [htd] at hdig2 hv2 ⊢
    rw [hds, List.map_cons]
    rw [List.map_cons] at hdig hv1
    have hd10 := hlt d List.mem_cons_self
    have hd' : Char.ofNat (48 + d.toNat) ≠ '0' := by
      intro he
      have h1 := congrArg Char.toNat he
      rw [toNat_ofNat_digit hd10, toNat_zero_char] at h1
      have hdz : d.toNat = 0 := by omega
      exact hd (UInt8.toNat_inj.mp (hdz.trans rfl))
    apply eq_of_canonical _ _ _ _ hdig hdig2 hd' hc
    rw [hv1, hv2]
    have hdn : digitsToNat (d :: rest) = toNat a := by rw [← hds]; exact hval
    exact hdn

private theorem isDigit_eq (c : Char) :
    c.isDigit = (decide (48 ≤ c.toNat) && decide (c.toNat ≤ 57)) := by
  cases h : c.isDigit with
  | true =>
    have hb := digit_bounds h
    simp [hb.1, hb.2]
  | false =>
    apply Eq.symm
    cases h2 : (decide (48 ≤ c.toNat) && decide (c.toNat ≤ 57)) with
    | false => rfl
    | true =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      rw [isDigit_of_bounds h2.1 h2.2] at h
      cases h

private theorem parseAsciiDigitsLoop_eq (cs : List Char) (acc : List UInt8) :
    parseAsciiDigitsLoop cs acc =
      if cs.all Char.isDigit then
        some (acc.reverse ++ cs.map (fun c => UInt8.ofNat (c.toNat - 48)))
      else none := by
  induction cs generalizing acc with
  | nil => simp [parseAsciiDigitsLoop]
  | cons c rest ih =>
    simp only [parseAsciiDigitsLoop]
    rw [← isDigit_eq, List.all_cons]
    cases hc : c.isDigit with
    | false => simp
    | true =>
      rw [ite_eq_left rfl, ih]
      simp [List.reverse_cons, List.append_assoc]

private theorem digitsToNatAux_map (cs : List Char) (hcs : ∀ c, c ∈ cs → c.isDigit = true)
    (acc : Nat) :
    digitsToNatAux acc (cs.map (fun c => UInt8.ofNat (c.toNat - 48))) =
      Nat.ofDigitChars 10 cs acc := by
  induction cs generalizing acc with
  | nil => exact Nat.ofDigitChars_nil.symm
  | cons c rest ih =>
    have hb := digit_bounds (hcs c List.mem_cons_self)
    have hu : (UInt8.ofNat (c.toNat - 48)).toNat = c.toNat - 48 := by
      rw [UInt8.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (show c.toNat - 48 ≤ 9 by omega) (by decide))
    rw [List.map_cons, Nat.ofDigitChars_cons, toNat_zero_char]
    show digitsToNatAux (acc * 10 + (UInt8.ofNat (c.toNat - 48)).toNat) _ = _
    rw [hu, ih (fun x hx => hcs x (List.mem_cons_of_mem c hx)), Nat.mul_comm acc 10]

/-- **`ofDecimal` is `Nat.ofDigitChars` on a non-empty string of ASCII digits**, and declines
on every other string. -/
theorem toNat_ofDecimal (s : String) :
    (ofDecimal s).map toNat =
      if (s.toList.all Char.isDigit && !s.toList.isEmpty) then
        some (Nat.ofDigitChars 10 s.toList 0)
      else none := by
  unfold ofDecimal
  cases hs : s.toList with
  | nil => rfl
  | cons c cs =>
    simp only [List.isEmpty_cons, Bool.not_false, Bool.and_true]
    rw [parseAsciiDigitsLoop_eq]
    cases hall : (c :: cs).all Char.isDigit with
    | false => rfl
    | true =>
      rw [ite_eq_left rfl, ite_eq_left rfl]
      simp only [List.reverse_nil, List.nil_append, Option.map_some]
      have hdig : ∀ x, x ∈ c :: cs → x.isDigit = true := by
        intro x hx
        exact List.all_eq_true.mp hall x hx
      have hlt : ∀ d, d ∈ (c :: cs).map (fun c => UInt8.ofNat (c.toNat - 48)) → d.toNat < 10 := by
        intro d hd
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
        show (UInt8.ofNat (x.toNat - 48)).toNat < 10
        have hb := digit_bounds (hdig x hx)
        rw [UInt8.toNat_ofNat',
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (show x.toNat - 48 ≤ 9 by omega) (by decide))]
        omega
      rw [toNat_ofDecimalDigits _ hlt]
      exact congrArg some (digitsToNatAux_map (c :: cs) hdig 0)

end IxCC.BigNat
