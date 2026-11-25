/-!
# The two representation primitives of arbitrary-precision `Nat` (`IxCC.Nat.Rep`)

Design note: `plans/ONE-PIPELINE.md`, section 4.3 (decision D4).

`Nat` is Lean's arbitrary-precision `Nat` at every level of the pipeline. Only two operations
ever see a natural as limbs:

* `toLimbs n`: the array of the **canonical** little-endian 64-bit limbs of `n` (no leading
  zero limb, `#[]` for `0`);
* `ofLimbs a`: the natural an array of 64-bit limbs denotes, canonical or not.

The arithmetic library (`IxCC.BigNat`) is written over `Array UInt64`; its entries
(`IxCC.BigNat.NatEntry`) are plain functions over `Nat` of the form
`ofLimbs (op (toLimbs a) (toLimbs b))`. So the contract of an entry is an equation between `Nat`
functions, and no limb, cell or tag occurs in it.

This module has no import and names nothing of the library. It gives:

1. the specification over lists of naturals (`limbsOf`, `natOfLimbs`, `CanonicalLimbs`), in the
   design's own words, and `LimbsBijection` **proved** (`limbsBijection`);
2. the two primitives as Lean functions (`toLimbs`, `ofLimbs`), which are their reference
   bodies, with their specification (`toLimbs_spec`, `ofLimbs_spec`) and the round trips
   (`ofLimbs_toLimbs`, `toLimbs_ofLimbs`);
3. the **canonical equations** a source-level binding needs (`toLimbs_eqn`, `ofLimbs_nil_eqn`,
   `ofLimbs_cons_eqn`): kernel-checked theorems whose statements are written term for term over
   applied `Nat.*` constants, raw literals and constructors, in the shape
   `IxCC.Src.Table.checkWord` and `checkLimb` accept (compare `IxCC.BigNat.Bootstrap.clz64_eqn`).
   Every symbol of them is the primitive itself, a constructor (`Array.mk`, `List.nil`,
   `List.cons`), the projection `Array.toList`, a variable, a literal, `cond`, a `Nat`
   operation the kernel's model gives natively, or `UInt64.ofNat`, which the word table binds.
   They determine each primitive on every closed argument (by induction on the natural, and on
   the list), so a wrong address pin cannot make a statement about the model false.

At an evaluator the two are primitives (`NatRepOp` of the design, to be added with the value
model by the lanes that own the evaluators); natively each is constant time on a limb cell with
one reference. `ofLimbs` there is stuck on an array holding a value that is not a 64-bit limb;
for the Lean function that case does not exist (`limbs_lt`).
-/

set_option autoImplicit false

namespace IxCC.NatRep

/-! ## Specification over lists of naturals -/

/-- The radix: one 64-bit limb. -/
def limbBase : Nat := 2 ^ 64

theorem limbBase_eq : limbBase = 18446744073709551616 := rfl

theorem limbBase_pos : 0 < limbBase := Nat.two_pow_pos 64

theorem one_lt_limbBase : 1 < limbBase := by decide

/-- The natural a little-endian limb list denotes. -/
def natOfLimbs : List Nat → Nat
  | [] => 0
  | l :: ls => l + limbBase * natOfLimbs ls

/-- The limbs of `n`, least significant first, with `fuel` steps. -/
def limbsFuel : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else n % limbBase :: limbsFuel fuel (n / limbBase)

/-- **The canonical limbs of a natural**: least significant first, no leading zero limb, `[]` for
`0`. (`n` steps suffice: each divides by `2^64`.) -/
def limbsOf (n : Nat) : List Nat := limbsFuel n n

/-- A limb list is canonical: every limb is a 64-bit word and the most significant is not zero. -/
def CanonicalLimbs (ls : List Nat) : Prop :=
  (∀ l, l ∈ ls → l < limbBase) ∧ ls.getLast? ≠ some 0

/-- **The two functions are inverse on canonical lists.** -/
def LimbsBijection : Prop :=
  (∀ n, natOfLimbs (limbsOf n) = n ∧ CanonicalLimbs (limbsOf n)) ∧
    ∀ ls, CanonicalLimbs ls → limbsOf (natOfLimbs ls) = ls

@[simp] theorem natOfLimbs_nil : natOfLimbs [] = 0 := rfl

@[simp] theorem natOfLimbs_cons (l : Nat) (ls : List Nat) :
    natOfLimbs (l :: ls) = l + limbBase * natOfLimbs ls := rfl

theorem limbsFuel_zero (n : Nat) : limbsFuel 0 n = [] := rfl

theorem limbsFuel_succ (fuel n : Nat) :
    limbsFuel (fuel + 1) n =
      if n = 0 then [] else n % limbBase :: limbsFuel fuel (n / limbBase) := rfl

theorem limbsFuel_zero_right (fuel : Nat) : limbsFuel fuel 0 = [] := by
  cases fuel with
  | zero => rfl
  | succ f => rw [limbsFuel_succ, ite_eq_left rfl]

theorem limbsFuel_succ_of_ne (fuel : Nat) {n : Nat} (h : n ≠ 0) :
    limbsFuel (fuel + 1) n = n % limbBase :: limbsFuel fuel (n / limbBase) := by
  rw [limbsFuel_succ, ite_eq_right h]

/-- One division by the radix uses one unit of fuel. -/
theorem div_limbBase_le {n fuel : Nat} (h0 : n ≠ 0) (hf : n ≤ fuel + 1) :
    n / limbBase ≤ fuel := by
  have hlt : n / limbBase < n := Nat.div_lt_self (Nat.pos_of_ne_zero h0) one_lt_limbBase
  omega

theorem natOfLimbs_limbsFuel : ∀ (fuel n : Nat), n ≤ fuel → natOfLimbs (limbsFuel fuel n) = n
  | 0, n, h => by
    have h0 : n = 0 := by omega
    subst h0
    rfl
  | fuel + 1, n, h => by
    by_cases h0 : n = 0
    · rw [h0, limbsFuel_zero_right, natOfLimbs_nil]
    · rw [limbsFuel_succ_of_ne fuel h0, natOfLimbs_cons,
        natOfLimbs_limbsFuel fuel (n / limbBase) (div_limbBase_le h0 h)]
      exact Nat.mod_add_div n limbBase

theorem limbsFuel_lt : ∀ (fuel n l : Nat), l ∈ limbsFuel fuel n → l < limbBase
  | 0, n, l, h => by
    rw [limbsFuel_zero] at h
    exact absurd h List.not_mem_nil
  | fuel + 1, n, l, h => by
    by_cases h0 : n = 0
    · rw [h0, limbsFuel_zero_right] at h
      exact absurd h List.not_mem_nil
    · rw [limbsFuel_succ_of_ne fuel h0] at h
      cases List.mem_cons.mp h with
      | inl hl => rw [hl]; exact Nat.mod_lt n limbBase_pos
      | inr hl => exact limbsFuel_lt fuel (n / limbBase) l hl

theorem limbsFuel_ne_nil {fuel m : Nat} (hm : m ≠ 0) (hle : m ≤ fuel) : limbsFuel fuel m ≠ [] := by
  cases fuel with
  | zero => omega
  | succ f =>
    rw [limbsFuel_succ_of_ne f hm]
    exact List.cons_ne_nil _ _

theorem limbsFuel_getLast : ∀ (fuel n : Nat), n ≤ fuel → (limbsFuel fuel n).getLast? ≠ some 0
  | 0, n, _ => by
    rw [limbsFuel_zero, List.getLast?_nil]
    intro hc
    cases hc
  | fuel + 1, n, h => by
    by_cases h0 : n = 0
    · rw [h0, limbsFuel_zero_right, List.getLast?_nil]
      intro hc
      cases hc
    · rw [limbsFuel_succ_of_ne fuel h0]
      have hle : n / limbBase ≤ fuel := div_limbBase_le h0 h
      by_cases hq : n / limbBase = 0
      · have hmod : n % limbBase = n := by
          have h1 := Nat.mod_add_div n limbBase
          rw [hq, Nat.mul_zero, Nat.add_zero] at h1
          exact h1
        rw [hq, limbsFuel_zero_right, hmod, List.getLast?_singleton]
        intro hc
        exact h0 (Option.some.inj hc)
      · have ih := limbsFuel_getLast fuel (n / limbBase) hle
        have hne : limbsFuel fuel (n / limbBase) ≠ [] := limbsFuel_ne_nil hq hle
        rw [List.getLast?_cons]
        cases hl : (limbsFuel fuel (n / limbBase)).getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
        | some x =>
          rw [hl] at ih
          exact ih

theorem canonical_limbsFuel {fuel n : Nat} (h : n ≤ fuel) : CanonicalLimbs (limbsFuel fuel n) :=
  And.intro (fun l hl => limbsFuel_lt fuel n l hl) (limbsFuel_getLast fuel n h)

/-- A canonical list that is not empty denotes a positive natural. -/
theorem natOfLimbs_pos : ∀ (ls : List Nat), ls ≠ [] → ls.getLast? ≠ some 0 → 0 < natOfLimbs ls
  | [], h, _ => absurd rfl h
  | [l], _, h => by
    have hl : l ≠ 0 := by
      intro h0
      apply h
      rw [h0, List.getLast?_singleton]
    rw [natOfLimbs_cons, natOfLimbs_nil, Nat.mul_zero, Nat.add_zero]
    exact Nat.pos_of_ne_zero hl
  | l :: l' :: ls, _, h => by
    have h' : (l' :: ls).getLast? ≠ some 0 := by
      rw [List.getLast?_cons_cons] at h
      exact h
    have ih := natOfLimbs_pos (l' :: ls) (List.cons_ne_nil _ _) h'
    rw [natOfLimbs_cons]
    have hmul := Nat.mul_pos limbBase_pos ih
    omega

theorem canonical_tail {l : Nat} {ls : List Nat} (hc : CanonicalLimbs (l :: ls)) :
    CanonicalLimbs ls := by
  refine And.intro (fun x hx => hc.1 x (List.mem_cons_of_mem l hx)) ?_
  cases ls with
  | nil =>
    rw [List.getLast?_nil]
    intro h
    cases h
  | cons l' ls' =>
    have h := hc.2
    rw [List.getLast?_cons_cons] at h
    exact h

theorem limbsFuel_natOfLimbs : ∀ (ls : List Nat) (fuel : Nat), CanonicalLimbs ls →
    natOfLimbs ls ≤ fuel → limbsFuel fuel (natOfLimbs ls) = ls
  | [], fuel, _, _ => limbsFuel_zero_right fuel
  | l :: ls, fuel, hc, hf => by
    have hl : l < limbBase := hc.1 l List.mem_cons_self
    have hrest : CanonicalLimbs ls := canonical_tail hc
    have hpos : natOfLimbs (l :: ls) ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (natOfLimbs_pos (l :: ls) (List.cons_ne_nil _ _) hc.2)
    have hmod : natOfLimbs (l :: ls) % limbBase = l := by
      rw [natOfLimbs_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
    have hdiv : natOfLimbs (l :: ls) / limbBase = natOfLimbs ls := by
      rw [natOfLimbs_cons, Nat.add_mul_div_left _ _ limbBase_pos, Nat.div_eq_of_lt hl,
        Nat.zero_add]
    cases fuel with
    | zero => omega
    | succ f =>
      have hle : natOfLimbs ls ≤ f := by
        have h1 := div_limbBase_le hpos hf
        rw [hdiv] at h1
        exact h1
      rw [limbsFuel_succ_of_ne f hpos, hmod, hdiv, limbsFuel_natOfLimbs ls f hrest hle]

/-- **`LimbsBijection`, proved**: `limbsOf` is a right inverse of `natOfLimbs` with canonical
values, and a left inverse on canonical lists. -/
theorem limbsBijection : LimbsBijection :=
  And.intro
    (fun n => And.intro (natOfLimbs_limbsFuel n n (Nat.le_refl n))
      (canonical_limbsFuel (Nat.le_refl n)))
    (fun ls hc => limbsFuel_natOfLimbs ls (natOfLimbs ls) hc (Nat.le_refl _))

theorem natOfLimbs_limbsOf (n : Nat) : natOfLimbs (limbsOf n) = n := (limbsBijection.1 n).1

theorem canonical_limbsOf (n : Nat) : CanonicalLimbs (limbsOf n) := (limbsBijection.1 n).2

theorem limbsOf_natOfLimbs {ls : List Nat} (h : CanonicalLimbs ls) :
    limbsOf (natOfLimbs ls) = ls := limbsBijection.2 ls h

/-- Any sufficient fuel gives the canonical limbs. -/
theorem limbsFuel_eq_limbsOf {fuel m : Nat} (h : m ≤ fuel) : limbsFuel fuel m = limbsOf m := by
  have h2 := limbsOf_natOfLimbs (canonical_limbsFuel h)
  rw [natOfLimbs_limbsFuel fuel m h] at h2
  exact h2.symm

theorem limbsOf_zero : limbsOf 0 = [] := rfl

/-- The recursion equation of `limbsOf`: the low limb, then the limbs of the quotient. -/
theorem limbsOf_of_ne {n : Nat} (h : n ≠ 0) :
    limbsOf n = n % limbBase :: limbsOf (n / limbBase) := by
  cases n with
  | zero => exact absurd rfl h
  | succ f =>
    show limbsFuel (f + 1) (f + 1) = _
    rw [limbsFuel_succ_of_ne f h, limbsFuel_eq_limbsOf (div_limbBase_le h (Nat.le_refl _))]

/-- A canonical list is determined by the natural it denotes. -/
theorem natOfLimbs_inj {ls ms : List Nat} (hl : CanonicalLimbs ls) (hm : CanonicalLimbs ms)
    (h : natOfLimbs ls = natOfLimbs ms) : ls = ms := by
  rw [← limbsOf_natOfLimbs hl, ← limbsOf_natOfLimbs hm, h]

/-- The number of limbs bounds the natural: `ls` of length `k` denotes a natural below
`2^(64 k)`. -/
theorem natOfLimbs_lt : ∀ (ls : List Nat), (∀ l, l ∈ ls → l < limbBase) →
    natOfLimbs ls < limbBase ^ ls.length
  | [], _ => by
    rw [natOfLimbs_nil, List.length_nil, Nat.pow_zero]
    exact Nat.zero_lt_one
  | l :: ls, h => by
    have hl : l < limbBase := h l List.mem_cons_self
    have ih := natOfLimbs_lt ls (fun x hx => h x (List.mem_cons_of_mem l hx))
    rw [natOfLimbs_cons, List.length_cons, Nat.pow_succ, Nat.mul_comm (limbBase ^ ls.length)]
    have h1 : limbBase * (natOfLimbs ls + 1) ≤ limbBase * limbBase ^ ls.length :=
      Nat.mul_le_mul_left limbBase ih
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega

/-- A canonical list of length `k + 1` denotes a natural of at least `2^(64 k)`: the limb count
of a natural is exactly its size in the radix. -/
theorem le_natOfLimbs : ∀ (ls : List Nat), ls ≠ [] → ls.getLast? ≠ some 0 →
    limbBase ^ (ls.length - 1) ≤ natOfLimbs ls
  | [], h, _ => absurd rfl h
  | [l], _, h => by
    have hpos := natOfLimbs_pos [l] (List.cons_ne_nil _ _) h
    show limbBase ^ 0 ≤ natOfLimbs [l]
    rw [Nat.pow_zero]
    exact hpos
  | l :: l' :: ls, _, h => by
    have h' : (l' :: ls).getLast? ≠ some 0 := by
      rw [List.getLast?_cons_cons] at h
      exact h
    have ih := le_natOfLimbs (l' :: ls) (List.cons_ne_nil _ _) h'
    rw [natOfLimbs_cons]
    show limbBase ^ ((l' :: ls).length - 1 + 1) ≤ _
    rw [Nat.pow_succ, Nat.mul_comm (limbBase ^ ((l' :: ls).length - 1))]
    have h1 : limbBase * limbBase ^ ((l' :: ls).length - 1) ≤ limbBase * natOfLimbs (l' :: ls) :=
      Nat.mul_le_mul_left limbBase ih
    omega

/-! ## The two primitives as Lean functions -/

/-- Tail-recursive worker of `toLimbs`: push the low limb, divide by the radix. -/
def toLimbsFuel : Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    if n = 0 then acc else toLimbsFuel fuel (n / limbBase) (acc.push (UInt64.ofNat n))

/-- **`toLimbs n`**: the array of the canonical little-endian 64-bit limbs of `n` (`#[]` for
`0`). Reference body of the representation primitive. -/
def toLimbs (n : Nat) : Array UInt64 := toLimbsFuel n n #[]

/-- **`ofLimbs a`**: the natural the little-endian 64-bit limbs of `a` denote; `a` need not be
canonical. Reference body of the representation primitive. -/
def ofLimbs (a : Array UInt64) : Nat :=
  a.toList.foldr (fun l acc => l.toNat + limbBase * acc) 0

theorem toLimbsFuel_zero (n : Nat) (acc : Array UInt64) : toLimbsFuel 0 n acc = acc := rfl

theorem toLimbsFuel_succ (fuel n : Nat) (acc : Array UInt64) :
    toLimbsFuel (fuel + 1) n acc =
      if n = 0 then acc else toLimbsFuel fuel (n / limbBase) (acc.push (UInt64.ofNat n)) := rfl

/-- A limb is its natural reduced by the radix. -/
theorem ofNat_mod_limbBase (n : Nat) : UInt64.ofNat (n % limbBase) = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  exact Nat.mod_mod n (2 ^ 64)

theorem toNat_ofNat_of_lt {l : Nat} (h : l < limbBase) : (UInt64.ofNat l).toNat = l :=
  UInt64.toNat_ofNat_of_lt' h

theorem toList_toLimbsFuel : ∀ (fuel n : Nat) (acc : Array UInt64),
    (toLimbsFuel fuel n acc).toList = acc.toList ++ (limbsFuel fuel n).map UInt64.ofNat
  | 0, n, acc => by
    rw [toLimbsFuel_zero, limbsFuel_zero, List.map_nil, List.append_nil]
  | fuel + 1, n, acc => by
    by_cases h0 : n = 0
    · rw [toLimbsFuel_succ, ite_eq_left h0, h0, limbsFuel_zero_right, List.map_nil, List.append_nil]
    · rw [toLimbsFuel_succ, ite_eq_right h0, limbsFuel_succ_of_ne fuel h0,
        toList_toLimbsFuel fuel (n / limbBase) (acc.push (UInt64.ofNat n)), Array.toList_push,
        List.append_assoc, List.map_cons, ofNat_mod_limbBase, List.singleton_append]

/-- **Specification of `toLimbs`**: its elements are the canonical limbs of `n`. -/
theorem toList_toLimbs (n : Nat) : (toLimbs n).toList = (limbsOf n).map UInt64.ofNat :=
  toList_toLimbsFuel n n #[]

theorem map_toNat_map_ofNat (ls : List Nat) (h : ∀ l, l ∈ ls → l < limbBase) :
    (ls.map UInt64.ofNat).map UInt64.toNat = ls := by
  rw [List.map_map]
  have h1 : List.map (UInt64.toNat ∘ UInt64.ofNat) ls = List.map id ls :=
    List.map_congr_left (fun l hl => toNat_ofNat_of_lt (h l hl))
  rw [h1, List.map_id]

theorem map_ofNat_map_toNat (ls : List UInt64) :
    (ls.map UInt64.toNat).map UInt64.ofNat = ls := by
  rw [List.map_map]
  have h1 : List.map (UInt64.ofNat ∘ UInt64.toNat) ls = List.map id ls :=
    List.map_congr_left (fun _ _ => UInt64.ofNat_toNat)
  rw [h1, List.map_id]

/-- **Specification of `toLimbs`**, read as naturals: `limbsOf n`. -/
theorem toLimbs_spec (n : Nat) : (toLimbs n).toList.map UInt64.toNat = limbsOf n := by
  rw [toList_toLimbs]
  exact map_toNat_map_ofNat (limbsOf n) (canonical_limbsOf n).1

theorem ofLimbs_mk_nil : ofLimbs (Array.mk []) = 0 := rfl

theorem ofLimbs_mk_cons (l : UInt64) (ls : List UInt64) :
    ofLimbs (Array.mk (l :: ls)) = l.toNat + limbBase * ofLimbs (Array.mk ls) := rfl

theorem foldr_eq_natOfLimbs (ls : List UInt64) :
    ls.foldr (fun l acc => l.toNat + limbBase * acc) 0 = natOfLimbs (ls.map UInt64.toNat) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => exact congrArg (fun t => l.toNat + limbBase * t) ih

/-- **Specification of `ofLimbs`**: `natOfLimbs` of the elements read as naturals. -/
theorem ofLimbs_spec (a : Array UInt64) : ofLimbs a = natOfLimbs (a.toList.map UInt64.toNat) :=
  foldr_eq_natOfLimbs a.toList

/-- Every element of an `Array UInt64` is a 64-bit limb, so `ofLimbs` is never outside its
domain on a typed array. -/
theorem limbs_lt (a : Array UInt64) : ∀ l, l ∈ a.toList.map UInt64.toNat → l < limbBase := by
  intro l hl
  cases List.mem_map.mp hl with
  | intro x hx =>
    rw [← hx.2]
    exact UInt64.toNat_lt x

/-- The limbs `toLimbs` returns are canonical. -/
theorem canonical_toLimbs (n : Nat) : CanonicalLimbs ((toLimbs n).toList.map UInt64.toNat) := by
  rw [toLimbs_spec]
  exact canonical_limbsOf n

/-- **Round trip 1**: `ofLimbs` is a left inverse of `toLimbs`. -/
theorem ofLimbs_toLimbs (n : Nat) : ofLimbs (toLimbs n) = n := by
  rw [ofLimbs_spec, toLimbs_spec]
  exact natOfLimbs_limbsOf n

/-- **Round trip 2**: `toLimbs` is a left inverse of `ofLimbs` on canonical arrays. -/
theorem toLimbs_ofLimbs (a : Array UInt64) (h : CanonicalLimbs (a.toList.map UInt64.toNat)) :
    toLimbs (ofLimbs a) = a := by
  apply Array.ext'
  rw [toList_toLimbs, ofLimbs_spec, limbsOf_natOfLimbs h]
  exact map_ofNat_map_toNat a.toList

/-- `toLimbs` is injective. -/
theorem toLimbs_inj {m n : Nat} (h : toLimbs m = toLimbs n) : m = n := by
  rw [← ofLimbs_toLimbs m, ← ofLimbs_toLimbs n, h]

theorem toLimbs_zero : toLimbs 0 = #[] := rfl

/-- The recursion equation of `toLimbs`. -/
theorem toList_toLimbs_of_ne {n : Nat} (h : n ≠ 0) :
    (toLimbs n).toList = UInt64.ofNat (n % limbBase) :: (toLimbs (n / limbBase)).toList := by
  rw [toList_toLimbs, toList_toLimbs, limbsOf_of_ne h, List.map_cons]

/-- The limb count of `toLimbs n` is the size of `n` in the radix: `n < 2^(64 k)`. -/
theorem lt_pow_size_toLimbs (n : Nat) : n < limbBase ^ (toLimbs n).size := by
  have h1 := natOfLimbs_lt ((toLimbs n).toList.map UInt64.toNat) (limbs_lt (toLimbs n))
  rw [← ofLimbs_spec, ofLimbs_toLimbs, List.length_map] at h1
  exact h1

/-- ... and, for `n ≠ 0`, `2^(64 (k - 1)) ≤ n`. -/
theorem pow_size_toLimbs_le {n : Nat} (h : n ≠ 0) : limbBase ^ ((toLimbs n).size - 1) ≤ n := by
  have hc := canonical_toLimbs n
  have hne : (toLimbs n).toList.map UInt64.toNat ≠ [] := by
    intro he
    have h0 : ofLimbs (toLimbs n) = 0 := by rw [ofLimbs_spec, he, natOfLimbs_nil]
    rw [ofLimbs_toLimbs] at h0
    exact h h0
  have h1 := le_natOfLimbs _ hne hc.2
  rw [← ofLimbs_spec, ofLimbs_toLimbs, List.length_map] at h1
  exact h1

/-- **The limb count of a natural, from its value**: `toLimbs n` has at most `k` limbs exactly
when `n < 2^(64 k)`. So a bound on the value of an operand or a result is a bound on the size of
its limb array (and of the loops over it). -/
theorem size_toLimbs_le_iff (n k : Nat) : (toLimbs n).size ≤ k ↔ n < limbBase ^ k := by
  constructor
  · intro h
    exact Nat.lt_of_lt_of_le (lt_pow_size_toLimbs n) (Nat.pow_le_pow_right limbBase_pos h)
  · intro h
    apply Nat.le_of_not_lt
    intro hlt
    have hn : n ≠ 0 := by
      intro h0
      rw [h0, toLimbs_zero] at hlt
      exact Nat.not_lt_zero k hlt
    have h1 := pow_size_toLimbs_le hn
    have h2 : limbBase ^ k ≤ limbBase ^ ((toLimbs n).size - 1) :=
      Nat.pow_le_pow_right limbBase_pos (by omega)
    omega

/-! ## The canonical equations

The statements a table entry for each primitive checks, written as the table writes them
(`IxCC.Src.Table.wordEqnType`, `limbEqnType`): applied `Nat.*` constants, raw literals, explicit
`@Array.mk`, `@Array.toList`, `@List.nil`, `@List.cons`, `@cond`, a limb argument as
`UInt64.ofNat x` over a natural `x`. `18446744073709551616` is `2^64`.

* `toLimbs`, one equation, by recursion on the natural (`n / 2^64 < n` for `n ≠ 0`):
  `Array.toList (toLimbs n) = cond (n == 0) [] (ofNat (n % 2^64) :: Array.toList (toLimbs (n / 2^64)))`.
* `ofLimbs`, the two constructor equations of its argument:
  `ofLimbs (Array.mk []) = 0` and
  `ofLimbs (Array.mk (ofNat x :: ls)) = x % 2^64 + 2^64 * ofLimbs (Array.mk ls)`.
-/

/-- **Canonical equation of `toLimbs`.** -/
theorem toLimbs_eqn (n : Nat) :
    @Array.toList UInt64 (toLimbs n) =
      @cond (List UInt64) (Nat.beq n (nat_lit 0))
        (@List.nil UInt64)
        (@List.cons UInt64
          (UInt64.ofNat (Nat.mod n (nat_lit 18446744073709551616)))
          (@Array.toList UInt64 (toLimbs (Nat.div n (nat_lit 18446744073709551616))))) := by
  by_cases h : n = 0
  · subst h
    rfl
  · have hb : Nat.beq n (nat_lit 0) = false := by
      cases hc : Nat.beq n (nat_lit 0) with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hc) h
    rw [hb]
    exact toList_toLimbs_of_ne h

/-- **Canonical equation of `ofLimbs`, the empty array.** -/
theorem ofLimbs_nil_eqn :
    ofLimbs (@Array.mk UInt64 (@List.nil UInt64)) = nat_lit 0 := rfl

/-- **Canonical equation of `ofLimbs`, one more limb.** -/
theorem ofLimbs_cons_eqn (x : Nat) (ls : List UInt64) :
    ofLimbs (@Array.mk UInt64 (@List.cons UInt64 (UInt64.ofNat x) ls)) =
      Nat.add (Nat.mod x (nat_lit 18446744073709551616))
        (Nat.mul (nat_lit 18446744073709551616) (ofLimbs (@Array.mk UInt64 ls))) := by
  have h : (UInt64.ofNat x).toNat = Nat.mod x (nat_lit 18446744073709551616) :=
    UInt64.toNat_ofNat'
  exact (ofLimbs_mk_cons (UInt64.ofNat x) ls).trans
    (congrArg (fun t => Nat.add t
      (Nat.mul (nat_lit 18446744073709551616) (ofLimbs (@Array.mk UInt64 ls)))) h)

end IxCC.NatRep
