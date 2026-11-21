import Aiur.Generic.AST

/-! `Instance.ofSymbol` inverts `Instance.symbol`: the instance symbols the
source semantics computes for calls and enum values name the instances they
were made from. Both are structurally recursive, so the kernel also computes
them. -/

namespace Aiur.Generic.Symbol

theorem expect_append (p s : List Char) : expect p (p ++ s) = some s := by
  induction p with
  | nil => rfl
  | cons c cs ih => simp [expect, ih]

/-! ### Distinct literal prefixes -/

section
variable (s : List Char)

theorem field_tuple : expect litField (litTuple ++ s) = none := by
  simp [expect, litField, litTuple]
theorem field_array : expect litField (litArray ++ s) = none := by
  simp [expect, litField, litArray]
theorem field_ptr : expect litField (litPtr ++ s) = none := by
  simp [expect, litField, litPtr]
theorem field_param : expect litField (litParam ++ s) = none := by
  simp [expect, litField, litParam]
theorem field_named : expect litField (litNamed ++ s) = none := by
  simp [expect, litField, litNamed]
theorem tuple_array : expect litTuple (litArray ++ s) = none := by
  simp [expect, litTuple, litArray]
theorem tuple_ptr : expect litTuple (litPtr ++ s) = none := by
  simp [expect, litTuple, litPtr]
theorem tuple_param : expect litTuple (litParam ++ s) = none := by
  simp [expect, litTuple, litParam]
theorem tuple_named : expect litTuple (litNamed ++ s) = none := by
  simp [expect, litTuple, litNamed]
theorem array_ptr : expect litArray (litPtr ++ s) = none := by
  simp [expect, litArray, litPtr]
theorem array_param : expect litArray (litParam ++ s) = none := by
  simp [expect, litArray, litParam]
theorem array_named : expect litArray (litNamed ++ s) = none := by
  simp [expect, litArray, litNamed]
theorem ptr_param : expect litPtr (litParam ++ s) = none := by
  simp [expect, litPtr, litParam]
theorem ptr_named : expect litPtr (litNamed ++ s) = none := by
  simp [expect, litPtr, litNamed]
theorem param_named : expect litParam (litNamed ++ s) = none := by
  simp [expect, litParam, litNamed]
end

/-! ### Strings -/

theorem hexValue_digitChar : ∀ k, k < 16 → hexValue (Nat.digitChar k) = some k := by
  decide

theorem parseString_escape (cs : List Char) (f : Nat) (r : List Char) (hf : cs.length < f) :
    parseString f (cs.flatMap escapeChar ++ '"' :: r) = some (cs, r) := by
  induction cs generalizing f with
  | nil =>
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp [parseString]
  | cons c cs ih =>
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    have ih' := ih g (by simp at hf; omega)
    simp only [List.flatMap_cons, List.append_assoc]
    by_cases h1 : c = '"'
    · subst h1
      simp [escapeChar, parseString, unescape, ih']
    by_cases h2 : c = '\\'
    · subst h2
      simp [escapeChar, parseString, unescape, ih']
    by_cases h3 : c = '\n'
    · subst h3
      simp [escapeChar, parseString, unescape, ih']
    by_cases h4 : c = '\r'
    · subst h4
      simp [escapeChar, parseString, unescape, ih']
    by_cases h5 : 0x20 ≤ c.toNat
    · simp [escapeChar, h1, h2, h3, h4, h5, parseString, ih']
    · have hn : c.toNat < 32 := by omega
      have d1 := hexValue_digitChar (c.toNat / 4096) (by omega)
      have d2 := hexValue_digitChar (c.toNat % 4096 / 256) (by omega)
      have d3 := hexValue_digitChar (c.toNat % 256 / 16) (by omega)
      have d4 := hexValue_digitChar (c.toNat % 16) (by omega)
      have hv : 4096 * (c.toNat / 4096) + 256 * (c.toNat % 4096 / 256) +
          16 * (c.toNat % 256 / 16) + c.toNat % 16 = c.toNat := by omega
      simp [escapeChar, h1, h2, h3, h4, h5, parseString, d1, d2, d3, d4, hv, ih',
        Char.ofNat_toNat]

theorem escapeChar_ne_nil (c : Char) : escapeChar c ≠ [] := by
  unfold escapeChar
  by_cases h1 : c = '"' <;> by_cases h2 : c = '\\' <;> by_cases h3 : c = '\n' <;>
    by_cases h4 : c = '\r' <;> by_cases h5 : 0x20 ≤ c.toNat <;> simp [h1, h2, h3, h4, h5]

theorem length_le_escape (l : List Char) : l.length ≤ (l.flatMap escapeChar).length := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    have : 1 ≤ (escapeChar c).length := by
      have := escapeChar_ne_nil c
      cases h : escapeChar c <;> simp_all
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem parseQuoted_string (n : String) (f : Nat) (r : List Char) (hf : (string n).length ≤ f) :
    parseQuoted f (string n ++ r) = some (n, r) := by
  have hlen : n.toList.length < f := by
    have := length_le_escape n.toList
    simp only [string, List.length_cons, List.length_append, List.length_singleton] at hf
    omega
  simp only [string, List.cons_append, List.append_assoc, List.singleton_append, parseQuoted,
    if_true, parseString_escape _ _ _ hlen, Option.map, String.ofList_toList, List.nil_append]

/-! ### Numbers -/

theorem digit_facts : ∀ k, k < 10 →
    isDigit (Nat.digitChar k) = true ∧ (Nat.digitChar k).toNat - 48 = k := by
  decide

theorem decimal_eq (n : Nat) :
    decimal n = if n < 10 then [Nat.digitChar n] else decimal (n / 10) ++ [Nat.digitChar (n % 10)] := by
  conv => lhs; rw [decimal]
  simp only [dite_eq_ite]

theorem decimal_digits (n : Nat) : ∀ c ∈ decimal n, isDigit c = true := by
  rw [decimal_eq]
  by_cases h : n < 10
  · simp only [h, if_true, List.mem_singleton]
    rintro c rfl
    exact (digit_facts n h).1
  · simp only [h, if_false, List.mem_append, List.mem_singleton]
    rintro c (hc | rfl)
    · exact decimal_digits (n / 10) c hc
    · exact (digit_facts (n % 10) (by omega)).1
termination_by n
decreasing_by omega

theorem decimal_value (n : Nat) :
    (decimal n).foldl (fun acc c => 10 * acc + (c.toNat - 48)) 0 = n := by
  rw [decimal_eq]
  by_cases h : n < 10
  · simp [h, (digit_facts n h).2]
  · simp only [h, if_false, List.foldl_append, decimal_value (n / 10), List.foldl_cons,
      List.foldl_nil, (digit_facts (n % 10) (by omega)).2]
    omega
termination_by n
decreasing_by omega

theorem decimal_ne_nil (n : Nat) : decimal n ≠ [] := by
  rw [decimal_eq]; split <;> simp

theorem takeWhile_digits (l r : List Char) (c : Char) (hl : ∀ x ∈ l, isDigit x = true)
    (hc : isDigit c = false) : (l ++ c :: r).takeWhile isDigit = l := by
  induction l with
  | nil => simp [List.takeWhile, hc]
  | cons x xs ih =>
    simp only [List.cons_append, List.takeWhile, hl x (by simp)]
    rw [ih (fun y hy => hl y (by simp [hy]))]

theorem dropWhile_digits (l r : List Char) (c : Char) (hl : ∀ x ∈ l, isDigit x = true)
    (hc : isDigit c = false) : (l ++ c :: r).dropWhile isDigit = c :: r := by
  induction l with
  | nil => simp [List.dropWhile, hc]
  | cons x xs ih =>
    simp only [List.cons_append, List.dropWhile, hl x (by simp)]
    exact ih (fun y hy => hl y (by simp [hy]))

theorem parseDecimal_decimal (n : Nat) (r : List Char) :
    parseDecimal (decimal n ++ (litClose2 ++ r)) = some (n, litClose2 ++ r) := by
  have hc : isDigit '}' = false := by decide
  have ht := takeWhile_digits (decimal n) ('}' :: r) '}' (decimal_digits n) hc
  have hd := dropWhile_digits (decimal n) ('}' :: r) '}' (decimal_digits n) hc
  simp only [litClose2, List.cons_append, List.nil_append] at *
  simp [parseDecimal, ht, hd, decimal_ne_nil, decimal_value]

/-! ### Types -/

theorem ty_head (t : Ty) : ∃ d cs, ty t = d :: cs ∧ d ≠ ']' := by
  cases t <;> simp [ty, litField, litTuple, litArray, litPtr, litParam, litNamed]

theorem parseTys_cons (g : Nat) (s : List Char) (hs : ∃ d r', s = d :: r' ∧ d ≠ ']') :
    parseTys (g + 1) ('[' :: s) = parseElems g s := by
  obtain ⟨d, r', rfl, hd⟩ := hs
  simp [parseTys, hd]

mutual
  theorem parseTy_ty : ∀ (t : Ty) (f : Nat) (r : List Char), (ty t).length ≤ f →
      parseTy f (ty t ++ r) = some (t, r)
    | .field, f, r, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [ty, litField] at hf; omega⟩
      rw [parseTy]
      simp only [ty, expect_append]
    | .tuple items, f, r, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [ty, litTuple] at hf; omega⟩
      have ih := parseTys_tys items g (litClose2 ++ r)
        (by simp [ty, litTuple, litClose2] at hf; omega)
      rw [parseTy]
      simp only [ty, List.append_assoc, field_tuple, expect_append, ih, Option.map]
    | .array t n, f, r, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [ty, litArray] at hf; omega⟩
      have ih := parseTy_ty t g (litLength ++ (decimal n ++ (litClose2 ++ r)))
        (by simp [ty, litArray, litLength, litClose2] at hf; omega)
      rw [parseTy]
      simp only [ty, List.append_assoc, field_array, tuple_array, expect_append, ih,
        parseDecimal_decimal, Option.map]
    | .ptr t, f, r, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [ty, litPtr] at hf; omega⟩
      have ih := parseTy_ty t g (litClose2 ++ r)
        (by simp [ty, litPtr, litClose2] at hf; omega)
      rw [parseTy]
      simp only [ty, List.append_assoc, field_ptr, tuple_ptr, array_ptr, expect_append, ih,
        Option.map]
    | .param n, f, r, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [ty, litParam] at hf; omega⟩
      have hq := parseQuoted_string n g (litClose2 ++ r)
        (by simp [ty, litParam, litClose2] at hf ⊢; omega)
      rw [parseTy]
      simp only [ty, List.append_assoc, field_param, tuple_param, array_param, ptr_param,
        expect_append, hq, Option.map]
    | .named n args, f, r, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [ty, litNamed] at hf; omega⟩
      have ih := parseTys_tys args g (litName ++ (string n ++ (litClose2 ++ r)))
        (by simp [ty, litNamed, litName, litClose2] at hf; omega)
      have hq := parseQuoted_string n g (litClose2 ++ r)
        (by simp [ty, litNamed, litName, litClose2] at hf ⊢; omega)
      rw [parseTy]
      simp only [ty, List.append_assoc, field_named, tuple_named, array_named, ptr_named,
        param_named, expect_append, ih, hq, Option.map]
  termination_by t _ _ _ => 2 * sizeOf t

  theorem parseTys_tys : ∀ (ts : List Ty) (f : Nat) (r : List Char), (tys ts).length ≤ f →
      parseTys f (tys ts ++ r) = some (ts, r)
    | [], f, r, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [tys] at hf; omega⟩
      simp [tys, parseTys]
    | t :: ts, f, r, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [tys] at hf; omega⟩
      have ih := parseElems_elems t ts g r (by simp [tys, List.length_append] at hf ⊢; omega)
      obtain ⟨d, cs, hty, hd⟩ := ty_head t
      simp only [tys, List.cons_append, List.append_assoc]
      rw [parseTys_cons g _ ⟨d, cs ++ (elems ts ++ r), by rw [hty]; rfl, hd⟩]
      exact ih
  termination_by ts _ _ _ => 2 * sizeOf ts

  theorem parseElems_elems : ∀ (t : Ty) (ts : List Ty) (f : Nat) (r : List Char),
      (ty t ++ elems ts).length ≤ f → parseElems f (ty t ++ (elems ts ++ r)) = some (t :: ts, r)
    | t, [], f, r, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [elems, List.length_append] at hf; omega⟩
      have ih := parseTy_ty t g (elems [] ++ r) (by simp [elems, List.length_append] at hf ⊢; omega)
      rw [parseElems, ih]
      simp [elems]
    | t, t' :: ts, f, r, hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [elems, List.length_append] at hf; omega⟩
      have ih := parseTy_ty t g (elems (t' :: ts) ++ r) (by simp [elems, List.length_append] at hf ⊢; omega)
      have ih' := parseElems_elems t' ts g r (by simp [elems, List.length_append] at hf ⊢; omega)
      rw [parseElems, ih]
      simp only [elems, List.cons_append, List.append_assoc]
      simp [ih']
  termination_by t ts _ _ _ => 2 * sizeOf t + 2 * sizeOf ts + 1
end

theorem parseKey_key (k : Instance) : parseKey (key k) = some k := by
  have hq := parseQuoted_string k.name (key k).length (litKeyTypes ++ (tys k.types ++ ['}']))
    (by simp only [key, List.length_append]; omega)
  have ht := parseTys_tys k.types (key k).length ['}']
    (by simp only [key, List.length_append]; omega)
  have he : expect litKeyName (key k) =
      some (string k.name ++ (litKeyTypes ++ (tys k.types ++ ['}']))) :=
    expect_append _ _
  unfold parseKey
  rw [he]
  simp only [hq, expect_append, ht]

end Aiur.Generic.Symbol

namespace Aiur.Generic

/-- **`Instance.ofSymbol` inverts `Instance.symbol`**, for every instance
whose plain name (no type arguments) does not begin with the reserved `$`. -/
theorem Instance.ofSymbol_symbol (k : Instance)
    (h : k.types = [] → k.name.toList.head? ≠ some '$') :
    Instance.ofSymbol k.symbol = .ok k := by
  rcases k with ⟨name, types⟩
  cases types with
  | nil =>
    have hh : name.toList.head? ≠ some '$' := h rfl
    have hs : Instance.symbol ⟨name, []⟩ = name := by simp [Instance.symbol]
    rw [hs]
    unfold Instance.ofSymbol
    cases hn : name.toList with
    | nil => rfl
    | cons c rest =>
      rw [hn] at hh
      have hc : c ≠ '$' := by simpa using hh
      simp [hc]
  | cons t ts =>
    have hs : Instance.symbol ⟨name, t :: ts⟩ =
        String.ofList ('$' :: Symbol.key ⟨name, t :: ts⟩) := by
      simp [Instance.symbol]
    rw [hs]
    unfold Instance.ofSymbol
    simp [String.toList_ofList, Symbol.parseKey_key]

/-- **Instances with type arguments round-trip unconditionally.** -/
theorem Instance.ofSymbol_symbol_of_ne_nil (k : Instance) (h : k.types ≠ []) :
    Instance.ofSymbol k.symbol = .ok k :=
  Instance.ofSymbol_symbol k (fun e => absurd e h)

end Aiur.Generic
