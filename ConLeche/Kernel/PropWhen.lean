module

public import ConLeche.Kernel.Name

/-!
# The zero-ness datum `PropWhen` — representation, API and laws
(task #161; the small-list constructors, 2026-09-06; the canonical
representation, task #194, 2026-09-06)

The binder annotation of the validated-annotation design: the reading
of a codomain sort's zero-ness predicate `Z(l) = {φ | eval φ l = 0}`.

**This module is the datum's whole boundary.**  It owns the
representation, the API that is the only way to build, read and
compare a datum, and — following the `Std.HashMap` pattern that
`CLAUDE.md` licenses for a self-contained data-structure verification
— every law about the datum *alone*.  Downstream never re-proves them
and never sees a constructor:

* the readout `holds` and its algebra (`holds_inter`,
  `holds_bindZ_go`, `holds_ext`);
* the comparison — which is **equality**: `=`/`==`/`DecidableEq`
  decide zero-ness agreement at every valuation (`eq_iff_holds`), so
  the checker's validation and defeq sites compare with `==` and no
  separate comparison exists (task #197 deleted `equiv`);
* the `inter`/`bindZ` algebra the substitution laws rest on
  (`inter_assoc`, `bindZ_inter`, `bindZ_go_append`,
  `bindZ_congr_names`, `bindZ_unit`, `paramsDefined_inter_of`).

**Canonical by construction (task #194).**  Every value of the type is
the unique representative of its parameter *set*: the parameter list
is strictly ascending in a total order on names (`Name.cmp`, defined
here), the invariant is carried by the constructors themselves, and
every producer (`ifAllZero`, `inter`, `bindZ`, hence
`Level.zeronessOf`/`Level.substPW`) normalizes.  Consequently
`ifAllZero ps = ifAllZero qs ↔ (∀ n, n ∈ ps ↔ n ∈ qs)`
(`ifAllZero_eq_iff`), `=`/`==`/`DecidableEq`/`Hashable` all decide
zero-ness agreement, and the level-instantiation identity law
(`Level.substPW_self`, `ConLeche/Verify/PropWhen.lean`) holds
unconditionally — amendment 2's counterexample (DESIGN.md, task #161
P1) was a *normalizing* substitution meeting a *non-canonical* input,
and non-canonical inputs no longer exist.

What is *not* here is what is not about the datum alone: the laws
relating it to `Level` (`Level.zeronessOf`, `Level.substPW` —
`zeronessOf_sound`, `zeronessOf_subst`, `substPW_self`,
`substPW_comp`, `holds_substPW`) live in `ConLeche/Verify/PropWhen.lean`,
because `Level` is defined *above* this module, and they are proved
purely through the API exported here.

Layering: this module imports `ConLeche.Kernel.Name` and nothing else.
-/

public section

namespace ConLeche

/-! ## A strict total order on names

There is no order on `ConLeche.Name` elsewhere in the tree (the `NNode`
arena keys by interned index, the level arena stores raw names), so
the canonical form needs one.  `Name.cmp` is the structural
lexicographic order — the shape of `Lean.Name.quickLt` minus the hash
short-cut, which would make the order depend on hashing.  Constructor
order is `anonymous < str < num`; equal constructors compare the
prefix first, then the payload with the core `Ord` instances
(`String`/`Nat`), whose `Std.TransCmp`/`Std.LawfulEqCmp` instances
supply the payload half of every law below.  `a < b` is `cmp a b =
.lt`; it is decidable, irreflexive, transitive, asymmetric and
trichotomous (`lt_irrefl`, `lt_trans`, `lt_asymm`, `lt_trichotomy`) —
a strict total order. -/

namespace Name

/-- Structural lexicographic comparison of names. -/
def cmp : Name → Name → Ordering
  | .anonymous, .anonymous => .eq
  | .anonymous, .str _ _ => .lt
  | .anonymous, .num _ _ => .lt
  | .str _ _, .anonymous => .gt
  | .num _ _, .anonymous => .gt
  | .str _ _, .num _ _ => .lt
  | .num _ _, .str _ _ => .gt
  | .str p s, .str q t => (cmp p q).then (compare s t)
  | .num p m, .num q n => (cmp p q).then (compare m n)

/-- The strict order: `cmp` reading `lt`. -/
instance : LT Name := ⟨fun a b => cmp a b = .lt⟩

instance (a b : Name) : Decidable (a < b) :=
  inferInstanceAs (Decidable (cmp a b = .lt))

theorem lt_def {a b : Name} : a < b ↔ cmp a b = .lt := Iff.rfl

theorem cmp_self : ∀ a : Name, cmp a a = .eq
  | .anonymous => rfl
  | .str p s => by
    simp [cmp, cmp_self p, Ordering.then, Std.ReflCmp.compare_self]
  | .num p n => by
    simp [cmp, cmp_self p, Ordering.then, Std.ReflCmp.compare_self]

theorem eq_of_cmp : ∀ {a b : Name}, cmp a b = .eq → a = b
  | .anonymous, .anonymous, _ => rfl
  | .str p s, .str q t, h => by
    rw [cmp, Ordering.then_eq_eq] at h
    rw [eq_of_cmp h.1, Std.LawfulEqCmp.compare_eq_iff_eq.mp h.2]
  | .num p m, .num q n, h => by
    rw [cmp, Ordering.then_eq_eq] at h
    rw [eq_of_cmp h.1, Std.LawfulEqCmp.compare_eq_iff_eq.mp h.2]

theorem cmp_swap : ∀ a b : Name, cmp a b = (cmp b a).swap
  | .anonymous, .anonymous => rfl
  | .anonymous, .str _ _ => rfl
  | .anonymous, .num _ _ => rfl
  | .str _ _, .anonymous => rfl
  | .num _ _, .anonymous => rfl
  | .str _ _, .num _ _ => rfl
  | .num _ _, .str _ _ => rfl
  | .str p s, .str q t => by
    rw [cmp, cmp, Ordering.swap_then, ← cmp_swap p q,
      ← Std.OrientedCmp.eq_swap (cmp := compare)]
  | .num p m, .num q n => by
    rw [cmp, cmp, Ordering.swap_then, ← cmp_swap p q,
      ← Std.OrientedCmp.eq_swap (cmp := compare)]

theorem cmp_trans : ∀ {a b c : Name}, cmp a b = .lt → cmp b c = .lt →
    cmp a c = .lt
  | .anonymous, .str _ _, .str _ _, _, _ => rfl
  | .anonymous, .str _ _, .num _ _, _, _ => rfl
  | .anonymous, .num _ _, .num _ _, _, _ => rfl
  | .str _ _, .num _ _, .num _ _, _, _ => rfl
  | .anonymous, .anonymous, _, h, _ => by simp [cmp] at h
  | .str _ _, .str _ _, .num _ _, _, _ => rfl
  | .str p s, .str q t, .str r u, h1, h2 => by
    rw [cmp, Ordering.then_eq_lt] at h1 h2 ⊢
    rcases h1 with h1 | ⟨h1, hs⟩
    · rcases h2 with h2 | ⟨h2, _⟩
      · exact Or.inl (cmp_trans h1 h2)
      · exact Or.inl (eq_of_cmp h2 ▸ h1)
    · rcases h2 with h2 | ⟨h2, ht⟩
      · exact Or.inl (eq_of_cmp h1 ▸ h2)
      · have hpq : p = q := eq_of_cmp h1
        have hqr : q = r := eq_of_cmp h2
        subst hpq; subst hqr
        exact Or.inr ⟨cmp_self p, Std.TransCmp.lt_trans hs ht⟩
  | .num p m, .num q n, .num r k, h1, h2 => by
    rw [cmp, Ordering.then_eq_lt] at h1 h2 ⊢
    rcases h1 with h1 | ⟨h1, hs⟩
    · rcases h2 with h2 | ⟨h2, _⟩
      · exact Or.inl (cmp_trans h1 h2)
      · exact Or.inl (eq_of_cmp h2 ▸ h1)
    · rcases h2 with h2 | ⟨h2, ht⟩
      · exact Or.inl (eq_of_cmp h1 ▸ h2)
      · have hpq : p = q := eq_of_cmp h1
        have hqr : q = r := eq_of_cmp h2
        subst hpq; subst hqr
        exact Or.inr ⟨cmp_self p, Std.TransCmp.lt_trans hs ht⟩

theorem lt_irrefl (a : Name) : ¬ a < a := by
  simp [lt_def, cmp_self]

theorem lt_trans {a b c : Name} (h1 : a < b) (h2 : b < c) : a < c :=
  cmp_trans h1 h2

theorem lt_asymm {a b : Name} (h : a < b) : ¬ b < a := by
  have h' : cmp a b = .lt := h
  have : cmp b a = .gt := by
    rw [cmp_swap b a, h']; rfl
  simp [lt_def, this]

theorem ne_of_lt {a b : Name} (h : a < b) : a ≠ b := by
  intro he
  rw [he] at h
  exact lt_irrefl b h

/-- `gt` read backwards. -/
theorem lt_of_gt {a b : Name} (h : cmp a b = .gt) : b < a := by
  rw [lt_def, cmp_swap b a, h]; rfl

/-- Trichotomy: names are linearly ordered by `<`. -/
theorem lt_trichotomy (a b : Name) : a = b ∨ a < b ∨ b < a := by
  cases h : cmp a b with
  | eq => exact Or.inl (eq_of_cmp h)
  | lt => exact Or.inr (Or.inl h)
  | gt => exact Or.inr (Or.inr (lt_of_gt h))

end Name

/-! ## The sorted-list layer

The representation invariant is one predicate: `Sorted` — strictly
ascending, which is sortedness and duplicate-freeness in a single
clause (`List.Pairwise (· < ·)`).  `merge` is the ordered union of two
sorted lists, `canon` sorts-and-deduplicates an arbitrary list by
folding singletons in, and `sorted_ext` is the canonical-form theorem
the whole module rests on: two sorted lists with the same members are
the same list. -/

namespace PropWhen

/-- Strictly ascending: sorted **and** duplicate-free, in one clause. -/
abbrev Sorted (ps : List Name) : Prop := List.Pairwise (· < ·) ps

/-- Membership-equal lists agree on every `all`. -/
private theorem all_eq_of_mem_iff {ps qs : List Name}
    (h : ∀ n, n ∈ ps ↔ n ∈ qs) (f : Name → Bool) :
    ps.all f = qs.all f := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  exact ⟨fun hp n hn => hp n ((h n).mpr hn), fun hq n hn => hq n ((h n).mp hn)⟩

/-- The ordered merge of two sorted lists — the union of the two sets,
sorted again (`sorted_merge`). -/
def merge : List Name → List Name → List Name
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs =>
    match Name.cmp a b with
    | .lt => a :: merge as (b :: bs)
    | .eq => a :: merge as bs
    | .gt => b :: merge (a :: as) bs
termination_by as bs => as.length + bs.length

@[simp] theorem merge_nil : ∀ as : List Name, merge as [] = as
  | [] => by simp [merge]
  | _ :: _ => by simp [merge]

@[simp] theorem nil_merge (bs : List Name) : merge [] bs = bs := by
  simp [merge]

@[simp] theorem mem_merge : ∀ (as bs : List Name) {n : Name},
    n ∈ merge as bs ↔ n ∈ as ∨ n ∈ bs := by
  intro as bs
  fun_induction merge as bs with
  | case1 bs => simp
  | case2 a as => simp
  | case3 a as b bs hc ih =>
    intro n; simp only [List.mem_cons, ih]; grind
  | case4 a as b bs hc ih =>
    intro n
    have hab : a = b := Name.eq_of_cmp hc
    simp only [List.mem_cons, ih, hab]; grind
  | case5 a as b bs hc ih =>
    intro n; simp only [List.mem_cons, ih]; grind

theorem all_merge (P : Name → Bool) (as bs : List Name) :
    (merge as bs).all P = (as.all P && bs.all P) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, List.all_eq_true, mem_merge]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

theorem sorted_merge : ∀ {as bs : List Name}, Sorted as → Sorted bs →
    Sorted (merge as bs) := by
  intro as bs
  fun_induction merge as bs with
  | case1 bs => intro _ h; exact h
  | case2 a as => intro h1 _; exact h1
  | case3 a as b bs hc ih =>
    intro h1 h2
    simp only [Sorted, List.pairwise_cons] at h1 h2 ⊢
    refine ⟨fun m hm => ?_, ih h1.2 (List.pairwise_cons.mpr h2)⟩
    rcases (mem_merge _ _).mp hm with hm | hm
    · exact h1.1 m hm
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact hc
      · exact Name.lt_trans hc (h2.1 m hm)
  | case4 a as b bs hc ih =>
    intro h1 h2
    have hab : a = b := Name.eq_of_cmp hc
    subst hab
    simp only [Sorted, List.pairwise_cons] at h1 h2 ⊢
    refine ⟨fun m hm => ?_, ih h1.2 h2.2⟩
    rcases (mem_merge _ _).mp hm with hm | hm
    · exact h1.1 m hm
    · exact h2.1 m hm
  | case5 a as b bs hc ih =>
    intro h1 h2
    have hba : b < a := Name.lt_of_gt hc
    simp only [Sorted, List.pairwise_cons] at h1 h2 ⊢
    refine ⟨fun m hm => ?_, ih (List.pairwise_cons.mpr h1) h2.2⟩
    rcases (mem_merge _ _).mp hm with hm | hm
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact hba
      · exact Name.lt_trans hba (h1.1 m hm)
    · exact h2.1 m hm

/-- Canonicalize a raw list: sort and deduplicate, by folding the
singletons together. -/
def canon (ps : List Name) : List Name :=
  ps.foldr (fun n s => merge [n] s) []

@[simp] theorem canon_nil : canon [] = [] := by simp [canon]

@[simp] theorem canon_cons (n : Name) (ps : List Name) :
    canon (n :: ps) = merge [n] (canon ps) := by simp [canon]

@[simp] theorem mem_canon {n : Name} : ∀ {ps : List Name},
    n ∈ canon ps ↔ n ∈ ps
  | [] => by simp
  | m :: rest => by simp [mem_canon (ps := rest)]

theorem sorted_canon : ∀ ps : List Name, Sorted (canon ps)
  | [] => List.Pairwise.nil
  | m :: rest => sorted_merge (by simp [Sorted]) (sorted_canon rest)

theorem all_canon (P : Name → Bool) (ps : List Name) :
    (canon ps).all P = ps.all P :=
  all_eq_of_mem_iff (fun _ => mem_canon) P

theorem canon_eq_nil_iff {ps : List Name} : canon ps = [] ↔ ps = [] := by
  rw [List.eq_nil_iff_forall_not_mem, List.eq_nil_iff_forall_not_mem]
  simp only [mem_canon]

theorem isEmpty_canon (ps : List Name) : (canon ps).isEmpty = ps.isEmpty := by
  rw [Bool.eq_iff_iff, List.isEmpty_iff, List.isEmpty_iff, canon_eq_nil_iff]

/-- **The canonical-form theorem**: two sorted lists with the same
members are the same list. -/
theorem sorted_ext : ∀ {as bs : List Name}, Sorted as → Sorted bs →
    (∀ n, n ∈ as ↔ n ∈ bs) → as = bs
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => by simpa using (h b).mpr (by simp)
  | a :: _, [], _, _, h => by simpa using (h a).mp (by simp)
  | a :: as, b :: bs, ha, hb, h => by
    simp only [Sorted, List.pairwise_cons] at ha hb
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).mp (by simp)) with hx | hx
      · exact hx
      rcases List.mem_cons.mp ((h b).mpr (by simp)) with hy | hy
      · exact hy.symm
      exact absurd (hb.1 a hx) (Name.lt_asymm (ha.1 b hy))
    subst hab
    have htail : ∀ n, n ∈ as ↔ n ∈ bs := by
      intro n
      constructor
      · intro hn
        rcases List.mem_cons.mp ((h n).mp (by simp [hn])) with rfl | hn'
        · exact absurd (ha.1 n hn) (Name.lt_irrefl n)
        · exact hn'
      · intro hn
        rcases List.mem_cons.mp ((h n).mpr (by simp [hn])) with rfl | hn'
        · exact absurd (hb.1 n hn) (Name.lt_irrefl n)
        · exact hn'
    rw [sorted_ext ha.2 hb.2 htail]

/-- Canonicalizing a sorted list is the identity. -/
theorem canon_eq_self {ps : List Name} (h : Sorted ps) : canon ps = ps :=
  sorted_ext (sorted_canon ps) h fun _ => mem_canon

/-- `canon` is idempotent. -/
theorem canon_canon (ps : List Name) : canon (canon ps) = canon ps :=
  canon_eq_self (sorted_canon ps)

theorem canon_pair (p q : Name) : canon [p, q] = merge [p] [q] := by
  simp

end PropWhen

/-- The private representation of the zero-ness datum (canonical since
task #194).  The census (DESIGN.md, "THE PACKED `pw` DATUM" §1) found
the parameter lists tiny: on init-full 605 492 data are `ifAllZero
[]`, 123 332 are one name, 16 are two names and **none** is longer.
So the small cases get dedicated, allocation-free constructors, and
only lists of length ≥ 3 keep a `List` cell chain.

**Every constructor carries its invariant**: `two p q` requires
`p < q`, and `many ps` requires `ps` strictly ascending (sorted and
duplicate-free — `PropWhen.Sorted`) *and* of length > 2, so that no
list a small constructor could hold is ever a `many`.  Together with
`never`/`always`/`one` (which have nothing to get wrong) this makes
the representation a bijection with {`never`} ∪ {finite sets of
names}: **equal sets are equal values**, by construction rather than
by a normalization pass anyone could forget.

This type is `private`: it cannot be named, matched on or constructed
outside this module. -/
private inductive PropWhenRepr where
  | never
  | always
  | one (p : Name)
  | two (p q : Name) (h : p < q)
  | many (ps : List Name) (h : PropWhen.Sorted ps ∧ 2 < ps.length)
  deriving Inhabited, Hashable

/-- The zero-ness datum of a binder's codomain sort — the regime
discriminator of the validated-annotation design (task #161).  For
every level `l`, the set `Z(l) := {φ | eval φ l = 0}` of zeroing
valuations is either empty (`never`) or of the form "every parameter
in `ps` is zero" (`ifAllZero ps`; `ps = []` = always zero) — see
`Level.zeronessOf` and the mechanized battery in
`ConLeche.Verify.PropWhen`.

`ps` is a parameter *set*, and the datum is its **canonical**
representative (task #194): the smart constructor `ifAllZero` sorts
and deduplicates, `inter`/`bindZ` (hence `Level.substPW`) produce
canonical output from canonical input, and no other producer exists.
So syntactic equality decides zero-ness agreement at every valuation
(`eq_iff_holds`): the checker's validation and defeq sites compare
with `==`, the derived `Hashable` hashes the set, and the
level-instantiation identity law (`Level.substPW_self`) holds
unconditionally.

**The representation is hidden, not hidden by convention.**  The datum
is a one-field structure whose constructor *and* field are `private`,
wrapping the equally private `PropWhenRepr`.  Outside this module the
type is opaque: it cannot be pattern-matched, taken apart or built
except through the API below (`never`, `ifAllZero`, `toList`,
`toList?`, `casesZ`, the observers and their laws).  Nothing in this
module is `@[expose]`d either, so no `rfl`/`decide` downstream can
reach around the API and reduce through a body — every fact about the
datum is one of the exported theorems. -/
structure PropWhen where
  private ofRepr ::
  private repr : PropWhenRepr

namespace PropWhen

private theorem ofRepr_repr (a : PropWhen) : ofRepr a.repr = a := rfl

private theorem repr_inj {a b : PropWhen} (h : a.repr = b.repr) : a = b := by
  rw [← ofRepr_repr a, ← ofRepr_repr b, h]

/-! ### The comparison, and the instances

`DecidableEq` is structural equality spelled constructor-wise
(`equivR`) so that the name comparisons go through `Name.beq` (the
pointer-and-hash-guarded equality, `ConLeche/Kernel/Name.lean`) rather
than the derived structural walk; `equivR_iff_eq` says it *is*
equality.  `==` is the `DecidableEq`, so `=`, `==`, `decide` and every
checker comparison site run the same code.

`instance` bodies are always exposed, so they may not mention the
private representation; each therefore goes through a public (sealed)
helper that may. -/

/-- The comparison on the representation. -/
private def equivR : PropWhenRepr → PropWhenRepr → Bool
  | .never, .never => true
  | .always, .always => true
  | .one x, .one y => x == y
  | .two x y _, .two x' y' _ => x == x' && y == y'
  | .many ps _, .many qs _ => ps == qs
  | _, _ => false

private theorem equivR_iff_eq (x y : PropWhenRepr) : equivR x y = true ↔ x = y := by
  cases x <;> cases y <;> simp [equivR]

/-- Structural equality, decided constructor-wise on the hidden
representation. -/
def decEq (a b : PropWhen) : Decidable (a = b) :=
  decidable_of_iff (equivR a.repr b.repr = true)
    ((equivR_iff_eq _ _).trans ⟨repr_inj, fun h => h ▸ rfl⟩)

instance : DecidableEq PropWhen := decEq

/-- The hash of a datum — a hash of the parameter *set*, by
canonicity. -/
def hash' (pw : PropWhen) : UInt64 := hash pw.repr

instance : Hashable PropWhen := ⟨hash'⟩

/-! ### The encapsulation boundary

`never`, `ifAllZero`, `toList`, `toList?` and `casesZ` are the whole
interface to the shape; every observer below is stated over them, and
every fact anyone downstream needs is one of the exported equations.
-/

/-- "The codomain sort is nonzero at every valuation."  A *definition*
now, not a constructor — but `.never` reads the same at every use
site. -/
def never : PropWhen := ofRepr .never

instance : Inhabited PropWhen := ⟨never⟩

private theorem sorted_pair {p q : Name} (h : Sorted [p, q]) : p < q :=
  (List.pairwise_cons.mp h).1 q (List.mem_singleton.mpr rfl)

/-- Build the datum of a *sorted* list: the dedicated small
constructors for length ≤ 2, the `many` chain above, its invariant
discharged from the sortedness proof. -/
private def ofSorted : (ps : List Name) → Sorted ps → PropWhen
  | [], _ => ofRepr .always
  | [p], _ => ofRepr (.one p)
  | [p, q], h => ofRepr (.two p q (sorted_pair h))
  | p :: q :: r :: rest, h => ofRepr (.many (p :: q :: r :: rest) ⟨h, by simp⟩)

/-- The two-name datum from two arbitrary names: one comparison,
no list cell. -/
private def two' (p q : Name) : PropWhen :=
  match h : Name.cmp p q with
  | .lt => ofRepr (.two p q h)
  | .eq => ofRepr (.one p)
  | .gt => ofRepr (.two q p (Name.lt_of_gt h))

/-- **Smart constructor**: "every parameter in `ps` is zero".
Normalizing: the result is the canonical representative of the *set*
of `ps` (`toList_ifAllZero : (ifAllZero ps).toList = canon ps`, and
`ifAllZero_eq_iff`).  The empty and singleton cases touch no list
cell and no comparison; the pair case is one comparison; only lists
of length ≥ 3 run the sort. -/
@[inline] def ifAllZero : List Name → PropWhen
  | [] => ofRepr .always
  | [p] => ofRepr (.one p)
  | [p, q] => two' p q
  | ps => ofSorted (canon ps) (sorted_canon ps)

/-- The parameter list of a datum — sorted and duplicate-free
(`sorted_toList`); `never` reads as `[]` (use `toList?` where the
distinction matters). -/
def toList (pw : PropWhen) : List Name :=
  match pw.repr with
  | .never => []
  | .always => []
  | .one p => [p]
  | .two p q _ => [p, q]
  | .many ps _ => ps

/-- The parameter list of a non-`never` datum; `none` at `never`.  The
view that inverts `ifAllZero`. -/
def toList? (pw : PropWhen) : Option (List Name) :=
  match pw.repr with
  | .never => none
  | _ => some pw.toList

/-- The invariant, read off any datum. -/
theorem sorted_toList (pw : PropWhen) : Sorted pw.toList := by
  obtain ⟨x⟩ := pw
  cases x with
  | two p q h => simp [toList, Sorted, h]
  | many ps h => exact h.1
  | _ => simp [toList, Sorted]

@[simp] theorem toList_never : toList .never = [] := by
  simp [toList, never]

private theorem toList_ofSorted (ps : List Name) (h : Sorted ps) :
    (ofSorted ps h).toList = ps := by
  match ps, h with
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _, _ => simp [ofSorted, toList]

private theorem toList_two' (p q : Name) : (two' p q).toList = merge [p] [q] := by
  unfold two'
  split <;> simp [toList, merge, *]

/-- The smart constructor's list is the canonical form of its input. -/
@[simp] theorem toList_ifAllZero (ps : List Name) :
    (ifAllZero ps).toList = canon ps := by
  match ps with
  | [] => simp [ifAllZero, toList]
  | [p] => simp [ifAllZero, toList]
  | [p, q] => rw [ifAllZero, toList_two', canon_pair]
  | p :: q :: r :: rest =>
    show (ofSorted (canon (p :: q :: r :: rest)) _).toList = _
    exact toList_ofSorted _ _

/-- Membership in the smart constructor's list is membership in its
input. -/
theorem mem_toList_ifAllZero {n : Name} {ps : List Name} :
    n ∈ (ifAllZero ps).toList ↔ n ∈ ps := by
  rw [toList_ifAllZero, mem_canon]

private theorem two'_ne_never (p q : Name) : two' p q ≠ never := by
  unfold two'
  split <;> simp [never]

private theorem ofSorted_ne_never (ps : List Name) (h : Sorted ps) :
    ofSorted ps h ≠ never := by
  match ps, h with
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _, _ => simp [ofSorted, never]

/-- The smart constructor never produces `never`. -/
@[simp] theorem ifAllZero_ne_never (ps : List Name) : ifAllZero ps ≠ .never := by
  match ps with
  | [] | [_] => simp [ifAllZero, never]
  | [p, q] => exact two'_ne_never p q
  | _ :: _ :: _ :: _ => exact ofSorted_ne_never _ _

@[simp] theorem toList?_never : toList? .never = none := by
  simp [toList?, never]

private theorem toList?_eq {pw : PropWhen} (h : pw ≠ never) :
    pw.toList? = some pw.toList := by
  obtain ⟨x⟩ := pw
  cases x with
  | never => exact absurd rfl h
  | _ => simp [toList?]

@[simp] theorem toList?_ifAllZero (ps : List Name) :
    (ifAllZero ps).toList? = some (canon ps) := by
  rw [toList?_eq (ifAllZero_ne_never ps), toList_ifAllZero]

/-- **Extensionality on the list**: two non-`never` data with the same
parameter list are the same datum — the representation has one value
per list. -/
theorem eq_of_toList {a b : PropWhen} (ha : a ≠ never) (hb : b ≠ never)
    (h : a.toList = b.toList) : a = b := by
  obtain ⟨x⟩ := a
  obtain ⟨y⟩ := b
  cases x <;> cases y <;> simp_all [toList, never] <;> (subst h; simp_all)

/-- **Extensionality on the set**: two non-`never` data with the same
parameters are the same datum — the canonicity theorem at the datum
level. -/
theorem eq_of_mem_iff {a b : PropWhen} (ha : a ≠ never) (hb : b ≠ never)
    (h : ∀ n, n ∈ a.toList ↔ n ∈ b.toList) : a = b :=
  eq_of_toList ha hb (sorted_ext (sorted_toList a) (sorted_toList b) h)

/-- Reassembling a datum from its list — the `casesZ` companion. -/
theorem ifAllZero_toList {pw : PropWhen} (h : pw ≠ .never) :
    ifAllZero pw.toList = pw :=
  eq_of_toList (ifAllZero_ne_never _) h
    (by rw [toList_ifAllZero, canon_eq_self (sorted_toList pw)])

/-- **Unique representatives**: two smart-constructor applications are
equal exactly when their inputs have the same members. -/
theorem ifAllZero_eq_iff (ps qs : List Name) :
    ifAllZero ps = ifAllZero qs ↔ ∀ n, n ∈ ps ↔ n ∈ qs := by
  constructor
  · intro h n
    have h1 := mem_toList_ifAllZero (n := n) (ps := ps)
    rw [h, mem_toList_ifAllZero] at h1
    exact h1.symm
  · intro h
    exact eq_of_mem_iff (ifAllZero_ne_never ps) (ifAllZero_ne_never qs)
      fun n => by rw [mem_toList_ifAllZero, mem_toList_ifAllZero]; exact h n

/-- Canonicalizing the input changes nothing. -/
@[simp] theorem ifAllZero_canon (ps : List Name) :
    ifAllZero (canon ps) = ifAllZero ps :=
  (ifAllZero_eq_iff _ _).mpr fun _ => mem_canon

private theorem ifAllZero_two {p q : Name} (h : p < q) :
    ifAllZero [p, q] = ofRepr (.two p q h) :=
  ifAllZero_toList (pw := ofRepr (.two p q h)) (by simp [never])

private theorem ifAllZero_many {ps : List Name}
    (h : Sorted ps ∧ 2 < ps.length) :
    ifAllZero ps = ofRepr (.many ps h) :=
  ifAllZero_toList (pw := ofRepr (.many ps h)) (by simp [never])

/-- **The view**: every datum is `never` or `ifAllZero ps`.  Registered
as the `cases`/`induction` eliminator, so case analysis outside this
module is written — and reads — exactly as it did against the
two-constructor datum.  (The `ifAllZero` case is offered for *every*
list `ps`, canonical or not: the smart constructor normalizes, so
`ifAllZero ps` names every non-`never` datum, and a proof for all
`ps` is a proof for the canonical ones.) -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def casesZ {motive : PropWhen → Sort u} (never : motive .never)
    (ifAllZero : (ps : List Name) → motive (PropWhen.ifAllZero ps)) :
    (pw : PropWhen) → motive pw
  | .ofRepr .never => never
  | .ofRepr .always => ifAllZero []
  | .ofRepr (.one p) => ifAllZero [p]
  | .ofRepr (.two p q h) =>
    Eq.mpr (congrArg motive (ifAllZero_two h).symm) (ifAllZero [p, q])
  | .ofRepr (.many ps h) =>
    Eq.mpr (congrArg motive (ifAllZero_many h).symm) (ifAllZero ps)

/-- The old datum's `Repr`, kept **byte-identical** in shape.  It was
written for the `annotate-basis` generator, whose `repr` output was
pasted into `Basis/*.lean`, `StdAxioms.lean` and `TrustAxioms.lean` as
the annotated literals; that generator is gone (2026-09-06 — the
literals are computed by `#annotate_basis` at elaboration time now),
but the spelling stays: it is what a `#eval (repr …)` of a stored pin
prints, and it names the smart constructor rather than the private
representation.  This reproduces exactly what `deriving Repr` emitted
for the old `never | ifAllZero (ps : List Name)` datum (the list is
the canonical one now). -/
def reprPrec' (pw : PropWhen) (prec : Nat) : Std.Format :=
  Repr.addAppParen
    (Std.Format.group (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
      (match pw.toList? with
        | none => Std.Format.text "ConLeche.PropWhen.never"
        | some ps =>
          Std.Format.text "ConLeche.PropWhen.ifAllZero" ++ Std.Format.line ++
            reprArg ps)))
    prec

instance : Repr PropWhen := ⟨reprPrec'⟩

/-! ### The observers

Each is defined representation-wise (so the small cases touch no list
cells), characterized once through `toList`, and re-stated in the
`never`/`ifAllZero` form — those equations, not the definitions, are
the whole downstream surface. -/

/-- Does the datum hold at a valuation — is the codomain sort zero
there?  (The model side's dispatch bit; the kernel never evaluates
this, it only compares data by `==`.) -/
def holds (φ : Name → Nat) (pw : PropWhen) : Bool :=
  match pw.repr with
  | .never => false
  | .always => true
  | .one p => φ p == 0
  | .two p q _ => (φ p == 0) && (φ q == 0)
  | .many ps _ => ps.all fun n => φ n == 0

@[simp] theorem holds_never (φ : Name → Nat) : holds φ .never = false := by
  simp [holds, never]

private theorem holds_eq_toList (φ : Name → Nat) {pw : PropWhen} (h : pw ≠ never) :
    holds φ pw = pw.toList.all fun n => φ n == 0 := by
  obtain ⟨x⟩ := pw
  cases x with
  | never => exact absurd rfl h
  | _ => simp [holds, toList]

@[simp] theorem holds_ifAllZero (φ : Name → Nat) (ps : List Name) :
    holds φ (ifAllZero ps) = ps.all fun n => φ n == 0 := by
  rw [holds_eq_toList φ (ifAllZero_ne_never ps), toList_ifAllZero, all_canon]

/-- Is the datum `never` — "the codomain sort is nonzero at *every*
valuation", the graph regime everywhere?  This is the **only**
kernel-decidable reading of the annotation that the verification tier
licenses a check-skip on (task #161 bucket 2): the P-tier claims split
their certificate cases on `pwBit φ m.pw = 0`, and `isNever` is
exactly the ∀-`φ` uniform version of the positive branch —
`pwBit φ .never = 1` at every `φ`, and no other datum has that
property (`.ifAllZero ps` holds at the all-zero valuation).  Sound
*and* exact: `isNever_iff_forall_pwBit_ne_zero` (`Model/Annot/Bit.lean`)
rests on `holds_never`/`holds_ifAllZero` here.

The datum may be read **only** to skip a re-check; it must never
select a reduct, a computed type, or a comparison result (law 1 as
amended at task #161: "annotations never change a reduct or a computed
type; annotation-gated check-skipping is permitted where the skip's
soundness is a P-tier theorem *and* the gate fires only where the
licensing theorems' hypotheses hold — `μ.verifiedChecks = true`").  Every
executable call site therefore carries the `μ.verifiedChecks` conjunct; see
`inferBodyIO` (`Kernel/CoreIO.lean`). -/
@[inline] def isNever (pw : PropWhen) : Bool :=
  match pw.repr with
  | .never => true
  | _ => false

theorem isNever_iff {pw : PropWhen} : isNever pw = true ↔ pw = never := by
  obtain ⟨x⟩ := pw
  cases x <;> simp [isNever, never]

@[simp] theorem isNever_never : isNever .never = true := isNever_iff.mpr rfl

@[simp] theorem isNever_ifAllZero (ps : List Name) :
    isNever (ifAllZero ps) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => ifAllZero_ne_never ps (isNever_iff.mp h)

/-- Does the datum mention any level parameter — is `Level.substPW`
ever non-trivial on it?  Folded into `Expr.hasLevelParam` and the
eager `eparamBs` recurrence (task #87), so the has-param shortcut of
the interned level-instantiation walk stays exact. -/
@[inline] def hasParams (pw : PropWhen) : Bool :=
  match pw.repr with
  | .never => false
  | .always => false
  | _ => true

private theorem hasParams_eq_toList (pw : PropWhen) :
    hasParams pw = !pw.toList.isEmpty := by
  obtain ⟨x⟩ := pw
  cases x with
  | many ps h =>
    have : ps ≠ [] := by
      intro he; rw [he] at h; simp at h
    simp [hasParams, toList, this]
  | _ => simp [hasParams, toList]

@[simp] theorem hasParams_never : hasParams .never = false := by
  simp [hasParams, never]

@[simp] theorem hasParams_ifAllZero (ps : List Name) :
    hasParams (ifAllZero ps) = !ps.isEmpty := by
  rw [hasParams_eq_toList, toList_ifAllZero, isEmpty_canon]

/-- Are all parameters of the datum among `params`?  Folded into
`Expr.allLevelParamsDefined` (task #161): level instantiation's
composition law (`Level.substPW_comp`) is *false* for data whose
parameters escape the declaration's — exactly as for the levels
themselves. -/
def paramsDefined (params : List Name) (pw : PropWhen) : Bool :=
  match pw.repr with
  | .never => true
  | .always => true
  | .one p => params.contains p
  | .two p q _ => params.contains p && params.contains q
  | .many ps _ => ps.all params.contains

private theorem paramsDefined_eq_toList (params : List Name) (pw : PropWhen) :
    paramsDefined params pw = pw.toList.all params.contains := by
  obtain ⟨x⟩ := pw
  cases x <;> simp [paramsDefined, toList]

@[simp] theorem paramsDefined_never (params : List Name) :
    paramsDefined params .never = true := by simp [paramsDefined, never]

@[simp] theorem paramsDefined_ifAllZero (params ps : List Name) :
    paramsDefined params (ifAllZero ps) = ps.all params.contains := by
  rw [paramsDefined_eq_toList, toList_ifAllZero, all_canon]

/-! ### Extensionality at the valuations

The canonicity payoff in its semantic form: data that agree at every
valuation are equal.  Everything about the producers (`inter`,
`bindZ`) is proved through it — a `holds` computation on each side,
and the representation never appears. -/

private theorem mem_of_all_eq {ps qs : List Name}
    (h : ∀ φ : Name → Nat, (ps.all fun n => φ n == 0) = (qs.all fun n => φ n == 0)) :
    ∀ n, n ∈ ps → n ∈ qs := by
  intro n hin
  by_cases hout : n ∈ qs
  · exact hout
  exfalso
  have hn := h fun m => if m = n then 1 else 0
  have hbs : (qs.all fun m => (if m = n then (1 : Nat) else 0) == 0)
      = true :=
    List.all_eq_true.mpr fun m hm => by
      have hne : m ≠ n := fun he => hout (he ▸ hm)
      simp [hne]
  have has : (ps.all fun m => (if m = n then (1 : Nat) else 0) == 0)
      = false :=
    List.all_eq_false.mpr ⟨n, hin, by simp⟩
  rw [has, hbs] at hn
  exact Bool.false_ne_true hn

/-- **Canonicity, semantically**: zero-ness agreement at every
valuation *is* equality of the data.  The separating valuations: the
all-zero valuation separates `never` from every `ifAllZero`, and
`φ n := 1, else 0` separates parameter sets that disagree on `n`. -/
theorem eq_iff_holds (p q : PropWhen) :
    p = q ↔ ∀ φ, p.holds φ = q.holds φ := by
  constructor
  · rintro rfl _; rfl
  · intro h
    by_cases hp : p = never
    · subst hp
      by_cases hq : q = never
      · exact hq.symm
      · have := h fun _ => 0
        rw [holds_never, holds_eq_toList _ hq] at this
        simp at this
    · by_cases hq : q = never
      · subst hq
        have := h fun _ => 0
        rw [holds_never, holds_eq_toList _ hp] at this
        simp at this
      · have h' : ∀ φ : Name → Nat, (p.toList.all fun n => φ n == 0)
            = (q.toList.all fun n => φ n == 0) := fun φ => by
          rw [← holds_eq_toList φ hp, ← holds_eq_toList φ hq]; exact h φ
        exact eq_of_mem_iff hp hq fun n =>
          ⟨mem_of_all_eq h' n, mem_of_all_eq (fun φ => (h' φ).symm) n⟩

theorem eq_of_holds {p q : PropWhen} (h : ∀ φ, p.holds φ = q.holds φ) : p = q :=
  (eq_iff_holds p q).mpr h

/-! ### The producers -/

/-- Intersection of two zero-ness predicates (the `max` rule: a `max`
is zero iff both sides are): `never` absorbs, sets unite — the
ordered merge, so the output is canonical.  The `always`/singleton
cases are answered without touching a list cell — they are 99.99 % of
the calls (the census). -/
def inter (a b : PropWhen) : PropWhen :=
  match a.repr, b.repr with
  | .never, _ => never
  | _, .never => never
  | .always, _ => b
  | _, .always => a
  | .one x, .one y => two' x y
  | _, _ => ofSorted (merge a.toList b.toList)
      (sorted_merge (sorted_toList a) (sorted_toList b))

@[simp] theorem inter_never_left (q : PropWhen) : inter .never q = .never := by
  simp [inter, never]

/-- `never` absorbs on the right too. -/
@[simp] theorem inter_never_right (p : PropWhen) : p.inter .never = .never := by
  obtain ⟨x⟩ := p
  cases x <;> simp [inter, never]

private theorem inter_ne_never {p q : PropWhen} (hp : p ≠ never) (hq : q ≠ never) :
    p.inter q ≠ never := by
  obtain ⟨x⟩ := p
  obtain ⟨y⟩ := q
  cases x <;> cases y <;> simp only [inter] <;>
    first
    | exact two'_ne_never _ _
    | exact ofSorted_ne_never _ _
    | simp_all [never]

private theorem toList_inter {p q : PropWhen} (hp : p ≠ never) (hq : q ≠ never) :
    (p.inter q).toList = merge p.toList q.toList := by
  obtain ⟨x⟩ := p
  obtain ⟨y⟩ := q
  cases x <;> cases y <;> simp only [inter] <;>
    first
    | exact toList_two' _ _
    | exact toList_ofSorted _ _
    | simp_all [never, toList]

theorem holds_inter (φ : Name → Nat) (p q : PropWhen) :
    (p.inter q).holds φ = (p.holds φ && q.holds φ) := by
  by_cases hp : p = never
  · subst hp; simp
  by_cases hq : q = never
  · subst hq; simp
  rw [holds_eq_toList φ (inter_ne_never hp hq), toList_inter hp hq, all_merge,
    holds_eq_toList φ hp, holds_eq_toList φ hq]

@[simp] theorem inter_ifAllZero (ps qs : List Name) :
    inter (ifAllZero ps) (ifAllZero qs) = ifAllZero (ps ++ qs) :=
  eq_of_holds fun φ => by
    rw [holds_inter, holds_ifAllZero, holds_ifAllZero, holds_ifAllZero,
      List.all_append]

/-- The shape of `inter` away from `never`: the parameter lists append
(and the smart constructor normalizes). -/
theorem inter_eq_toList {p q : PropWhen} (hp : p ≠ .never) (hq : q ≠ .never) :
    p.inter q = ifAllZero (p.toList ++ q.toList) := by
  have h := inter_ifAllZero p.toList q.toList
  rwa [ifAllZero_toList hp, ifAllZero_toList hq] at h

/-- `ifAllZero []` is the right unit of `inter`. -/
@[simp] theorem inter_nil (p : PropWhen) : p.inter (ifAllZero []) = p := by
  cases p with
  | never => simp
  | ifAllZero ps => rw [inter_ifAllZero, List.append_nil]

/-- `ifAllZero []` is the left unit of `inter`. -/
@[simp] theorem nil_inter (q : PropWhen) : (ifAllZero []).inter q = q := by
  cases q with
  | never => simp
  | ifAllZero qs => rw [inter_ifAllZero, List.nil_append]

/-- The list-level `bindZ` fold. -/
def bindZ.go (f : Name → PropWhen) : List Name → PropWhen
  | [] => ifAllZero []
  | n :: rest => (f n).inter (go f rest)

/-- Substitute each parameter of the datum by a whole datum and
intersect ("all of `ps` zero" becomes "all replacements zero") — the
monadic bind of the zero-ness reading.  Canonical on output because
`inter` is; parameters mapped to `ifAllZero [n]` reproduce the datum
(`bindZ_unit`), which is what the unconditional identity law of level
instantiation rests on. -/
def bindZ (f : Name → PropWhen) (pw : PropWhen) : PropWhen :=
  match pw.repr with
  | .never => never
  | .always => ifAllZero []
  | .one p => f p
  | .two p q _ => (f p).inter (f q)
  | .many ps _ => bindZ.go f ps

@[simp] theorem bindZ_never (f : Name → PropWhen) :
    bindZ f .never = .never := by simp [bindZ, never]

@[simp] theorem bindZ_go_nil (f : Name → PropWhen) :
    bindZ.go f [] = ifAllZero [] := by simp [bindZ.go]

theorem holds_bindZ_go (φ : Name → Nat) (f : Name → PropWhen) :
    ∀ ps : List Name,
      (bindZ.go f ps).holds φ = ps.all fun n => (f n).holds φ
  | [] => by rw [bindZ_go_nil, holds_ifAllZero]; rfl
  | n :: rest => by
    simp [bindZ.go, holds_inter, holds_bindZ_go φ f rest]

private theorem bindZ_eq_go (f : Name → PropWhen) {pw : PropWhen} (h : pw ≠ never) :
    bindZ f pw = bindZ.go f pw.toList := by
  obtain ⟨x⟩ := pw
  cases x with
  | never => exact absurd rfl h
  | always => simp [bindZ, toList]
  | one p => simp [bindZ, toList, bindZ.go]
  | two p q _ => simp [bindZ, toList, bindZ.go]
  | many ps _ => simp [bindZ, toList]

private theorem bindZ_go_canon (f : Name → PropWhen) (ps : List Name) :
    bindZ.go f (canon ps) = bindZ.go f ps :=
  eq_of_holds fun φ => by
    rw [holds_bindZ_go, holds_bindZ_go]
    exact all_eq_of_mem_iff (fun _ => mem_canon) _

@[simp] theorem bindZ_ifAllZero (f : Name → PropWhen) (ps : List Name) :
    bindZ f (ifAllZero ps) = bindZ.go f ps := by
  rw [bindZ_eq_go f (ifAllZero_ne_never ps), toList_ifAllZero, bindZ_go_canon]

end PropWhen

/-! ## The law battery

Everything below is a fact about the datum alone; it needs no `Level`
and no `Expr`.  Moved here from `ConLeche/Verify/PropWhen.lean` on
2026-09-06 (the `Std.HashMap` pattern: the structure carries its
laws), statements unchanged — and unchanged again at task #194, when
the representation became canonical: the proofs below go through the
exported `never`/`ifAllZero` equations only, and those kept their
statements. -/

namespace PropWhen

/-! ### `paramsDefined` -/

theorem paramsDefined_inter_of {params : List Name} {p q : PropWhen}
    (hp : p.paramsDefined params = true)
    (hq : q.paramsDefined params = true) :
    (p.inter q).paramsDefined params = true := by
  cases p <;> cases q <;>
    simp_all [List.all_append]

/-- **Parameter locality**: a datum reads its valuation only at its
own parameters (the `paramsDefined` footprint) — `denoteMeta`'s
φ-congruence walk (`denoteMeta_params_ext`) rides this at every binder. -/
theorem holds_ext {ps : List Name} {pw : PropWhen}
    (hdef : pw.paramsDefined ps = true) {φ₁ φ₂ : Name → Nat}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) : pw.holds φ₁ = pw.holds φ₂ := by
  cases pw with
  | never => rfl
  | ifAllZero qs =>
    simp only [paramsDefined_ifAllZero, List.all_eq_true] at hdef
    rw [holds_ifAllZero, holds_ifAllZero]
    induction qs with
    | nil => rfl
    | cons n rest ih =>
      simp only [List.all_cons]
      rw [hφ n (by simpa [List.contains_iff_mem] using hdef n (by simp)),
        ih fun m hm => hdef m (by simp [hm])]

/-! ### `inter` / `bindZ` algebra -/

/-- `inter` is associative (the datum is a set union). -/
theorem inter_assoc (a b c : PropWhen) :
    (a.inter b).inter c = a.inter (b.inter c) := by
  cases a <;> cases b <;> cases c <;> simp [List.append_assoc]

/-- `inter` is commutative (a set union; canonicity makes it an
equality, not an `equiv`). -/
theorem inter_comm (a b : PropWhen) : a.inter b = b.inter a :=
  eq_of_holds fun φ => by rw [holds_inter, holds_inter, Bool.and_comm]

/-- `inter` is idempotent. -/
theorem inter_self (a : PropWhen) : a.inter a = a :=
  eq_of_holds fun φ => by rw [holds_inter, Bool.and_self]

/-- The `bindZ` fold over an append splits — the list-level half of
`bindZ_inter`. -/
theorem bindZ_go_append (g : Name → PropWhen) : ∀ ps qs : List Name,
    bindZ.go g (ps ++ qs) = (bindZ.go g ps).inter (bindZ.go g qs)
  | [], qs => (nil_inter (bindZ.go g qs)).symm
  | n :: rest, qs => by
    show (g n).inter (bindZ.go g (rest ++ qs))
      = ((g n).inter (bindZ.go g rest)).inter (bindZ.go g qs)
    rw [bindZ_go_append g rest qs, inter_assoc]

theorem bindZ_inter (g : Name → PropWhen) (p q : PropWhen) :
    (p.inter q).bindZ g = (p.bindZ g).inter (q.bindZ g) := by
  cases p with
  | never => simp
  | ifAllZero ps =>
    cases q with
    | never => simp
    | ifAllZero qs => simp [bindZ_go_append]

theorem bindZ_congr_names {f g : Name → PropWhen} :
    ∀ {ps : List Name}, (∀ n ∈ ps, f n = g n) →
      bindZ.go f ps = bindZ.go g ps
  | [], _ => rfl
  | n :: rest, h => by
    show (f n).inter _ = (g n).inter _
    rw [h n (by simp), bindZ_congr_names fun m hm => h m (by simp [hm])]

/-- `bindZ` at the unit (`n ↦ ifAllZero [n]`) reproduces the datum —
an equality, by canonicity.  This is the datum half of the level
instantiation identity law (`Level.substPW_self`). -/
theorem bindZ_unit : ∀ pw : PropWhen,
    pw.bindZ (fun n => .ifAllZero [n]) = pw := by
  intro pw
  cases pw with
  | never => simp
  | ifAllZero ps => rw [bindZ_ifAllZero]; exact bindZ_unit.go ps
where
  go : ∀ ps : List Name,
      bindZ.go (fun n => PropWhen.ifAllZero [n]) ps = .ifAllZero ps
  | [] => rfl
  | n :: rest => by
    show (PropWhen.ifAllZero [n]).inter _ = _
    rw [go rest, inter_ifAllZero]
    rfl

end PropWhen

end ConLeche
