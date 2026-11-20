import IxAICore.Decision
import Std.Data.HashSet.Lemmas

/-!
# Curation rules for the premise-selection dataset

The dataset's items are theorems of a compiled library, identified by Ixon content address. Every
rule here is a pure function, generic in the address type `α`, so the same rules run on host
digests and could be evaluated by a kernel over byte lists.

* `acceptance`: why an item is refused, if it is: a constant of its proof or one of its axioms
  that the extraction could not address (`unresolvedName`; an item is never accepted with a
  shortened list, `accepted_resolved`), `sorryAx`, an axiom outside the allowed set
  (`propext`, `Classical.choice`, `Quot.sound`, which also excludes `Lean.ofReduceBool` and so
  `native_decide`), or a direct reference to a constant implemented natively (`@[extern]`,
  `@[implemented_by]`).
* `premiseRule`: an item's premises are the library theorems its proof term uses, other than
  itself. The library is every theorem outside `Init`, `Std` and `Lean`; definitions, instances,
  constructors, recursors and core lemmas are never premises.
* `dedup`: one item per address (`dedup_nodup`).
* `split`: the test set is a set of modules; a training item is from no test module, is not itself
  a test theorem, and uses no test theorem as a premise (`split_disjoint`, `split_addr_disjoint`).
* `splitBy`: the same rule for any test predicate on items, such as the time-ordered split that
  holds out the last theorems of every module (`splitBy_disjoint`, `splitBy_addr_disjoint`).

The list forms above are the specifications; their membership tests are linear, so on a whole
library they are quadratic. `dedupFast`, `splitFast`, `splitByFast`, `disjointFast` and
`premiseRuleSet` are the same functions over hash sets, each proved equal to its specification
(`dedupFast_eq`, `splitFast_eq`, `splitByFast_eq`, `disjointFast_eq`, `premiseRuleSet_eq`), and are
what the pipeline runs.
-/

namespace IxAIData

/-- A statement's shape: the constants it mentions, with multiplicity, and the counts of the
twelve expression node kinds; the head constants of the conclusion and of its last two arguments
(`none` when not a constant application, or not extracted); the leading binders and how many of
them are non-dependent. -/
structure Statement (α : Type) where
  consts : List (α × Nat)
  kinds : List Nat
  heads : List (Option α) := []
  binders : Nat := 0
  hyps : Nat := 0
  deriving Repr, Inhabited

/-- A library theorem: a candidate premise. `module` indexes the environment's module list and
`decl` is the declaration's position in its module. -/
structure Premise (α : Type) where
  addr : α
  module : Nat
  decl : Nat
  stmt : Statement α
  deriving Repr, Inhabited

/-- A theorem of the scope with what its proof uses. `uses` is every constant in the proof term;
`premises` is set by `premiseRule`. `unresolved` counts the names of `uses` and `axioms` that the
extraction could not address: those lists then omit them, so such an item is refused. -/
structure Item (α : Type) where
  thm : Premise α
  uses : List α
  axioms : List α
  native : Bool
  premises : List α := []
  unresolved : Nat := 0
  deriving Repr, Inhabited

def Item.addr {α : Type} (it : Item α) : α := it.thm.addr
def Item.module {α : Type} (it : Item α) : Nat := it.thm.module

inductive Refusal where
  /-- A constant or axiom name that the extraction could not address. -/
  | unresolvedName
  | usesSorry
  | extraAxiom
  | nativeRef
  deriving DecidableEq, Repr

/-- The addresses the acceptance rule needs: `sorryAx` and the allowed axioms. -/
structure Policy (α : Type) where
  sorryAx : α
  allowedAxioms : List α

def acceptance {α : Type} [DecidableEq α] (p : Policy α) (it : Item α) : Option Refusal :=
  if it.unresolved ≠ 0 then some .unresolvedName
  else if p.sorryAx ∈ it.axioms then some .usesSorry
  else if it.axioms.any (fun a => !(p.allowedAxioms.contains a)) then some .extraAxiom
  else if it.native then some .nativeRef
  else none

def accepted {α : Type} [DecidableEq α] (p : Policy α) (it : Item α) : Bool := (acceptance p it).isNone

theorem accepted_axioms {α : Type} [DecidableEq α] (p : Policy α) (it : Item α)
    (h : accepted p it = true) : ∀ a ∈ it.axioms, a ∈ p.allowedAxioms := by
  intro a ha
  simp only [accepted, acceptance] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hany
        simp only [List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_exists, not_and,
          Bool.not_eq_false, List.contains_iff_mem] at hany
        exact (hany a ha)

/-- An accepted item's constants and axioms were all addressed: its lists are complete. -/
theorem accepted_resolved {α : Type} [DecidableEq α] (p : Policy α) (it : Item α)
    (h : accepted p it = true) : it.unresolved = 0 := by
  simp only [accepted, acceptance] at h
  split at h
  · simp at h
  · rename_i hu
    exact Decidable.of_not_not hu

def premiseRule {α : Type} [DecidableEq α] (library : List α) (it : Item α) : Item α :=
  { it with premises := it.uses.filter fun c => c ≠ it.addr && library.contains c }

/-- Keep the first item of every address, skipping addresses in `seen`. -/
def dedupAux {α β : Type} [DecidableEq α] (f : β → α) : List α → List β → List β
  | _, [] => []
  | seen, x :: xs => if f x ∈ seen then dedupAux f seen xs else x :: dedupAux f (f x :: seen) xs

def dedup {α : Type} [DecidableEq α] (items : List (Item α)) : List (Item α) := dedupAux Item.addr [] items

theorem dedupAux_spec {α β : Type} [DecidableEq α] (f : β → α) (l : List β) :
    ∀ seen : List α, ((dedupAux f seen l).map f).Nodup ∧ ∀ y ∈ dedupAux f seen l, f y ∉ seen := by
  induction l with
  | nil => intro seen; exact ⟨List.nodup_nil, fun y hy => by simp [dedupAux] at hy⟩
  | cons x xs ih =>
    intro seen
    by_cases hx : f x ∈ seen
    · rw [dedupAux, if_pos hx]; exact ih seen
    · rw [dedupAux, if_neg hx]
      obtain ⟨hn, hs⟩ := ih (f x :: seen)
      refine ⟨?_, ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, hn⟩
        obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
        exact hs y hy (List.mem_cons.mpr (Or.inl hxy))
      · intro y hy
        rcases List.mem_cons.mp hy with h | h
        · rw [h]; exact hx
        · exact fun hm => hs y h (List.mem_cons.mpr (Or.inr hm))

theorem dedup_nodup {α : Type} [DecidableEq α] (items : List (Item α)) :
    ((dedup items).map Item.addr).Nodup := (dedupAux_spec Item.addr items []).1

theorem dedupAux_sub {α β : Type} [DecidableEq α] (f : β → α) (l : List β) :
    ∀ seen : List α, ∀ y ∈ dedupAux f seen l, y ∈ l := by
  induction l with
  | nil => intro seen y hy; simp [dedupAux] at hy
  | cons x xs ih =>
    intro seen y hy
    by_cases hx : f x ∈ seen
    · rw [dedupAux, if_pos hx] at hy; exact List.mem_cons.mpr (Or.inr (ih seen y hy))
    · rw [dedupAux, if_neg hx] at hy
      rcases List.mem_cons.mp hy with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (ih _ y h))

/-! ## Train/test split -/

def testAddrs {α : Type} (isTest : Nat → Bool) (items : List (Item α)) : List α :=
  (items.filter fun it => isTest it.module).map Item.addr

/-- A training item is from another module, is not a test theorem, and uses no test theorem as a
premise. -/
def keepTrain {α : Type} [DecidableEq α] (isTest : Nat → Bool) (items : List (Item α)) (it : Item α) :
    Bool :=
  !isTest it.module && !(testAddrs isTest items).contains it.addr &&
    it.premises.all fun p => !(testAddrs isTest items).contains p

/-- The test set is the items of the test modules; the training set is the items `keepTrain`
keeps. -/
def split {α : Type} [DecidableEq α] (isTest : Nat → Bool) (items : List (Item α)) :
    List (Item α) × List (Item α) :=
  (items.filter (keepTrain isTest items), items.filter fun it => isTest it.module)

theorem mem_testAddrs {α : Type} [DecidableEq α] {isTest : Nat → Bool} {items : List (Item α)}
    {x : Item α} (hx : x ∈ (split isTest items).2) : (testAddrs isTest items).contains x.addr = true := by
  have : x.addr ∈ testAddrs isTest items := List.mem_map.mpr ⟨x, hx, rfl⟩
  simpa using this

theorem split_disjoint {α : Type} [DecidableEq α] (isTest : Nat → Bool) (items : List (Item α)) :
    ∀ t ∈ (split isTest items).1, ∀ x ∈ (split isTest items).2, x.addr ∉ t.premises := by
  intro t ht x hx hp
  have hk : keepTrain isTest items t = true := (List.mem_filter.mp ht).2
  unfold keepTrain at hk
  simp only [Bool.and_eq_true] at hk
  have h : (!(testAddrs isTest items).contains x.addr) = true := List.all_eq_true.mp hk.2 x.addr hp
  rw [mem_testAddrs hx] at h
  exact absurd h (by decide)

theorem split_addr_disjoint {α : Type} [DecidableEq α] (isTest : Nat → Bool) (items : List (Item α)) :
    ∀ t ∈ (split isTest items).1, ∀ x ∈ (split isTest items).2, x.addr ≠ t.addr := by
  intro t ht x hx he
  have hk : keepTrain isTest items t = true := (List.mem_filter.mp ht).2
  unfold keepTrain at hk
  simp only [Bool.and_eq_true] at hk
  have h := hk.1.2
  rw [← he] at h
  rw [mem_testAddrs hx] at h
  exact absurd h (by decide)

/-! ## Train/test split by an item predicate -/

def testAddrsBy {α : Type} (isTest : Item α → Bool) (items : List (Item α)) : List α :=
  (items.filter isTest).map Item.addr

def keepTrainBy {α : Type} [DecidableEq α] (isTest : Item α → Bool) (items : List (Item α))
    (it : Item α) : Bool :=
  !isTest it && !(testAddrsBy isTest items).contains it.addr &&
    it.premises.all fun p => !(testAddrsBy isTest items).contains p

/-- The test set is the items `isTest` selects; the training set is the items `keepTrainBy`
keeps. -/
def splitBy {α : Type} [DecidableEq α] (isTest : Item α → Bool) (items : List (Item α)) :
    List (Item α) × List (Item α) :=
  (items.filter (keepTrainBy isTest items), items.filter isTest)

theorem split_eq_splitBy {α : Type} [DecidableEq α] (isTest : Nat → Bool) (items : List (Item α)) :
    split isTest items = splitBy (fun it => isTest it.module) items := rfl

theorem mem_testAddrsBy {α : Type} [DecidableEq α] {isTest : Item α → Bool} {items : List (Item α)}
    {x : Item α} (hx : x ∈ (splitBy isTest items).2) :
    (testAddrsBy isTest items).contains x.addr = true := by
  have : x.addr ∈ testAddrsBy isTest items := List.mem_map.mpr ⟨x, hx, rfl⟩
  simpa using this

theorem splitBy_disjoint {α : Type} [DecidableEq α] (isTest : Item α → Bool) (items : List (Item α)) :
    ∀ t ∈ (splitBy isTest items).1, ∀ x ∈ (splitBy isTest items).2, x.addr ∉ t.premises := by
  intro t ht x hx hp
  have hk : keepTrainBy isTest items t = true := (List.mem_filter.mp ht).2
  unfold keepTrainBy at hk
  simp only [Bool.and_eq_true] at hk
  have h : (!(testAddrsBy isTest items).contains x.addr) = true := List.all_eq_true.mp hk.2 x.addr hp
  rw [mem_testAddrsBy hx] at h
  exact absurd h (by decide)

theorem splitBy_addr_disjoint {α : Type} [DecidableEq α] (isTest : Item α → Bool)
    (items : List (Item α)) :
    ∀ t ∈ (splitBy isTest items).1, ∀ x ∈ (splitBy isTest items).2, x.addr ≠ t.addr := by
  intro t ht x hx he
  have hk : keepTrainBy isTest items t = true := (List.mem_filter.mp ht).2
  unfold keepTrainBy at hk
  simp only [Bool.and_eq_true] at hk
  have h := hk.1.2
  rw [← he] at h
  rw [mem_testAddrsBy hx] at h
  exact absurd h (by decide)

/-- The time-ordered test predicate: the last `num/den` of every module's items, by declaration
position. `rank` is an item's position among its module's items and `count` their number. -/
def heldOutLate (num den : Nat) (rank count : Nat) : Bool := den * rank ≥ (den - num) * count

/-- The run-time form of the disjointness statement, for reporting on a concrete split. -/
def disjoint {α : Type} [DecidableEq α] (train test : List (Item α)) : Bool :=
  let testAddrs := test.map Item.addr
  train.all fun t => !testAddrs.contains t.addr && t.premises.all fun p => !testAddrs.contains p

theorem disjoint_sound {α : Type} [DecidableEq α] {train test : List (Item α)}
    (h : disjoint train test = true) :
    ∀ t ∈ train, ∀ x ∈ test, x.addr ∉ t.premises ∧ x.addr ≠ t.addr := by
  intro t ht x hx
  have hk := List.all_eq_true.mp h t ht
  simp only [Bool.and_eq_true] at hk
  have hm : (test.map Item.addr).contains x.addr = true := by
    simpa using List.mem_map.mpr ⟨x, hx, rfl⟩
  refine ⟨fun hp => ?_, fun he => ?_⟩
  · have := List.all_eq_true.mp hk.2 x.addr hp
    rw [hm] at this; exact absurd this (by decide)
  · have := hk.1
    rw [← he, hm] at this; exact absurd this (by decide)

/-! ## Hash-set forms -/

section Fast

variable {α : Type} [DecidableEq α] [Hashable α]

/-- The addresses of a list as a hash set. -/
def setOf (l : List α) : Std.HashSet α := l.foldl (·.insert ·) {}

theorem contains_foldl_insert (l : List α) (s : Std.HashSet α) (a : α) :
    (l.foldl (·.insert ·) s).contains a = (l.contains a || s.contains a) := by
  induction l generalizing s with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert, List.contains_cons]
    by_cases hx : x = a
    · subst hx; simp
    · simp [beq_eq_false_iff_ne.mpr hx, beq_eq_false_iff_ne.mpr (Ne.symm hx)]

theorem contains_setOf (l : List α) (a : α) : (setOf l).contains a = l.contains a := by
  simp [setOf, contains_foldl_insert]

/-- `dedupAux` with the addresses seen in a hash set and the result accumulated in reverse. -/
def dedupSetAux {β : Type} (f : β → α) : Std.HashSet α → List β → List β → List β
  | _, acc, [] => acc.reverse
  | seen, acc, x :: xs =>
    if seen.contains (f x) then dedupSetAux f seen acc xs
    else dedupSetAux f (seen.insert (f x)) (x :: acc) xs

theorem dedupSetAux_eq {β : Type} (f : β → α) (l : List β) :
    ∀ (seen : Std.HashSet α) (seenL : List α) (acc : List β),
      (∀ a, seen.contains a = seenL.contains a) →
      dedupSetAux f seen acc l = acc.reverse ++ dedupAux f seenL l := by
  induction l with
  | nil => intro seen seenL acc _; simp [dedupSetAux, dedupAux]
  | cons x xs ih =>
    intro seen seenL acc h
    have hc : seen.contains (f x) = decide (f x ∈ seenL) := by rw [h]; simp
    by_cases hx : f x ∈ seenL
    · simp only [dedupSetAux, dedupAux, hc, hx, decide_true, ↓reduceIte]
      exact ih seen seenL acc h
    · simp only [dedupSetAux, dedupAux, hc, hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [ih (seen.insert (f x)) (f x :: seenL) (x :: acc)]
      · simp
      · intro a
        rw [Std.HashSet.contains_insert, h, List.contains_cons]
        by_cases hxa : f x = a
        · subst hxa; simp
        · simp [beq_eq_false_iff_ne.mpr hxa, beq_eq_false_iff_ne.mpr (Ne.symm hxa)]

/-- `dedup` over a hash set. -/
def dedupFast (items : List (Item α)) : List (Item α) := dedupSetAux Item.addr {} [] items

theorem dedupFast_eq (items : List (Item α)) : dedupFast items = dedup items := by
  rw [dedupFast, dedupSetAux_eq Item.addr items {} [] [] (fun a => by simp)]
  rfl

theorem dedupFast_nodup (items : List (Item α)) : ((dedupFast items).map Item.addr).Nodup := by
  rw [dedupFast_eq]; exact dedup_nodup items

/-- `keepTrainBy` with the test addresses in a hash set. -/
def keepTrainSet (isTest : Item α → Bool) (s : Std.HashSet α) (it : Item α) : Bool :=
  !isTest it && !s.contains it.addr && it.premises.all fun p => !s.contains p

/-- `splitBy` with the test addresses in a hash set built once. -/
def splitByFast (isTest : Item α → Bool) (items : List (Item α)) : List (Item α) × List (Item α) :=
  let s := setOf (testAddrsBy isTest items)
  (items.filter (keepTrainSet isTest s), items.filter isTest)

theorem splitByFast_eq (isTest : Item α → Bool) (items : List (Item α)) :
    splitByFast isTest items = splitBy isTest items := by
  simp only [splitByFast, splitBy]
  congr 1
  apply List.filter_congr
  intro it _
  simp only [keepTrainSet, keepTrainBy, contains_setOf]

/-- `split` with the test addresses in a hash set built once. -/
def splitFast (isTest : Nat → Bool) (items : List (Item α)) : List (Item α) × List (Item α) :=
  splitByFast (fun it => isTest it.module) items

theorem splitFast_eq (isTest : Nat → Bool) (items : List (Item α)) :
    splitFast isTest items = split isTest items := by
  rw [splitFast, splitByFast_eq, split_eq_splitBy]

theorem splitByFast_disjoint (isTest : Item α → Bool) (items : List (Item α)) :
    ∀ t ∈ (splitByFast isTest items).1, ∀ x ∈ (splitByFast isTest items).2,
      x.addr ∉ t.premises ∧ x.addr ≠ t.addr := by
  rw [splitByFast_eq]
  exact fun t ht x hx => ⟨splitBy_disjoint isTest items t ht x hx, splitBy_addr_disjoint isTest items t ht x hx⟩

theorem splitFast_disjoint (isTest : Nat → Bool) (items : List (Item α)) :
    ∀ t ∈ (splitFast isTest items).1, ∀ x ∈ (splitFast isTest items).2,
      x.addr ∉ t.premises ∧ x.addr ≠ t.addr := by
  rw [splitFast_eq]
  exact fun t ht x hx => ⟨split_disjoint isTest items t ht x hx, split_addr_disjoint isTest items t ht x hx⟩

/-- `disjoint` with the test addresses in a hash set. -/
def disjointFast (train test : List (Item α)) : Bool :=
  let s := setOf (test.map Item.addr)
  train.all fun t => !s.contains t.addr && t.premises.all fun p => !s.contains p

theorem disjointFast_eq (train test : List (Item α)) : disjointFast train test = disjoint train test := by
  simp only [disjointFast, disjoint, contains_setOf]

/-- `premiseRule` with the library in a hash set. -/
def premiseRuleSet (library : Std.HashSet α) (it : Item α) : Item α :=
  { it with premises := it.uses.filter fun c => c ≠ it.addr && library.contains c }

theorem premiseRuleSet_eq (library : List α) (it : Item α) :
    premiseRuleSet (setOf library) it = premiseRule library it := by
  simp only [premiseRuleSet, premiseRule, contains_setOf]

end Fast

end IxAIData
