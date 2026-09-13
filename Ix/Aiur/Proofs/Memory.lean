/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Semantics.AIR
import Ix.Aiur.Proofs.Lookup

/-!
Immutable memory facts from incrementing memory tables and exact balance.

The native memory AIR has no first-pointer-zero constraint. Active rows form
a prefix and their pointers increment in the field; an arbitrary initial
pointer and wraparound are permitted. A trace-height bound below the field
characteristic suffices to make these pointers distinct. A separate bound
on query counts prevents modular cancellation in the lookup argument.

The local polynomial and exact-message interfaces below still require
extraction from the native proof system. Contents need not be injectively
stored, acyclic, or created by earlier runtime operations. These theorems
establish functionality at a fixed width and pointer, not refinement to the
reference evaluator's insertion-order memory.
-/

namespace Aiur

theorem G.ext_n {a b : G} (equal : a.n = b.n) : a = b :=
  Subtype.ext (UInt64.toNat_inj.mp equal)

theorem G.add_zero (a : G) : a + 0 = a := by
  change G.ofNat (a.n + 0) = a
  simpa only [Nat.add_zero] using G.ofNat_n a

theorem G.ofNat_add (a b : Nat) : G.ofNat (a + b) = G.ofNat a + G.ofNat b := by
  apply G.ext_n
  simp only [G.n_ofNat, G.n_add, Nat.add_mod, Nat.mod_mod]

theorem G.add_assoc (a b c : G) : (a + b) + c = a + (b + c) := by
  apply G.ext_n
  simp only [G.n_add, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem G.add_left_cancel (a : G) {b c : G} (equal : a + b = a + c) : b = c := by
  have ha : a.n < gSize.toNat := UInt64.lt_iff_toNat_lt.mp a.property
  have hb : b.n < gSize.toNat := UInt64.lt_iff_toNat_lt.mp b.property
  have hc : c.n < gSize.toNat := UInt64.lt_iff_toNat_lt.mp c.property
  have equal := congrArg G.n equal
  simp only [G.n_add] at equal
  apply G.ext_n
  have modulus : gSize.toNat = 18446744069414584321 := by decide
  rw [modulus] at ha hb hc equal
  omega

theorem G.ofNat_injective_below {a b : Nat} (ha : a < gSize.toNat)
    (hb : b < gSize.toNat) (equal : G.ofNat a = G.ofNat b) : a = b := by
  have equal := congrArg G.n equal
  simpa only [G.n_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using equal

namespace AIR

/-- Columns of a memory row; the table fixes the contents width. -/
structure MemoryRow where
  selector : G
  multiplicity : G
  pointer : G
  contents : Array G

/-- Interior transition polynomial: an active successor requires an active row. -/
def memoryActivityTransition (row next : MemoryRow) : G :=
  next.selector * (row.selector - 1)

/-- Interior transition polynomial for the incrementing pointer column. -/
def memoryPointerTransition (row next : MemoryRow) : G :=
  next.selector * (row.pointer + 1 - next.pointer)

/-- Local memory constraints after decoding boolean selectors. The last row
has no successor constraint, matching the native transition selector. -/
structure MemoryRowsValid (width : Nat) (rows : Array MemoryRow) : Prop where
  selectors : ∀ i (hi : i < rows.size), rows[i].selector = 0 ∨ rows[i].selector = 1
  activity : ∀ i (hi : i < rows.size), activityConstraint rows[i].multiplicity rows[i].selector = 0
  widths : ∀ i (hi : i < rows.size), rows[i].contents.size = width
  activityTransition : ∀ i (hi : i + 1 < rows.size),
    memoryActivityTransition (rows[i]'(by omega)) rows[i + 1] = 0
  pointerTransition : ∀ i (hi : i + 1 < rows.size),
    memoryPointerTransition (rows[i]'(by omega)) rows[i + 1] = 0

theorem MemoryRowsValid.previous_active {width : Nat} {rows : Array MemoryRow}
    (valid : MemoryRowsValid width rows) (i : Nat) (hi : i + 1 < rows.size)
    (active : rows[i + 1].selector = 1) : (rows[i]'(by omega)).selector = 1 := by
  have satisfied := valid.activityTransition i hi
  unfold memoryActivityTransition at satisfied
  rw [active, G.mul_comm, G.mul_one] at satisfied
  exact (G.sub_eq_zero_iff (rows[i]'(by omega)).selector 1).mp satisfied

theorem MemoryRowsValid.next_pointer {width : Nat} {rows : Array MemoryRow}
    (valid : MemoryRowsValid width rows) (i : Nat) (hi : i + 1 < rows.size)
    (active : rows[i + 1].selector = 1) :
    rows[i + 1].pointer = (rows[i]'(by omega)).pointer + 1 := by
  have satisfied := valid.pointerTransition i hi
  unfold memoryPointerTransition at satisfied
  rw [active, G.mul_comm, G.mul_one] at satisfied
  exact ((G.sub_eq_zero_iff ((rows[i]'(by omega)).pointer + 1) rows[i + 1].pointer).mp satisfied).symm

theorem MemoryRowsValid.pointer_eq_first_add {width : Nat} {rows : Array MemoryRow}
    (valid : MemoryRowsValid width rows) (i : Nat) (hi : i < rows.size)
    (active : rows[i].selector = 1) :
    rows[i].pointer = (rows[0]'(by omega)).pointer + G.ofNat i := by
  induction i with
  | zero => simp only [show G.ofNat 0 = (0 : G) from rfl, G.add_zero]
  | succ i ih =>
    rw [valid.next_pointer i hi active]
    rw [ih (by omega) (valid.previous_active i hi active), G.ofNat_add, G.add_assoc]
    rfl

theorem MemoryRowsValid.pointer_injective {width : Nat} {rows : Array MemoryRow}
    (valid : MemoryRowsValid width rows) (bounded : rows.size < gSize.toNat)
    (i j : Nat) (hi : i < rows.size) (hj : j < rows.size)
    (activeI : rows[i].selector = 1) (activeJ : rows[j].selector = 1)
    (same : rows[i].pointer = rows[j].pointer) : i = j := by
  rw [valid.pointer_eq_first_add i hi activeI, valid.pointer_eq_first_add j hj activeJ] at same
  exact G.ofNat_injective_below (by omega) (by omega) (G.add_left_cancel _ same)

def memoryFacts (tables : Nat → Array MemoryRow) : Bytecode.AIR.Memory :=
  fun width pointer contents => ∃ i : Nat, ∃ hi : i < (tables width).size,
    (tables width)[i].selector = 1 ∧ (tables width)[i].pointer = pointer ∧
    (tables width)[i].contents = contents

theorem memoryFacts_functional (tables : Nat → Array MemoryRow)
    (valid : ∀ width, MemoryRowsValid width (tables width))
    (bounded : ∀ width, (tables width).size < gSize.toNat)
    {width : Nat} {pointer : G} {left right : Array G}
    (loadedLeft : memoryFacts tables width pointer left)
    (loadedRight : memoryFacts tables width pointer right) : left = right := by
  obtain ⟨i, hi, ai, pi, vi⟩ := loadedLeft
  obtain ⟨j, hj, aj, pj, vj⟩ := loadedRight
  have same := (valid width).pointer_injective (bounded width) i j hi hj ai aj (pi.trans pj.symm)
  subst j
  exact vi.symm.trans vj

/-- Providers for one fixed-width memory table, in native row order. -/
def memoryProviders (rows : Array MemoryRow) : List (Provider (G × Array G)) :=
  List.ofFn fun i : Fin rows.size =>
    ((rows[i].pointer, rows[i].contents), rows[i].multiplicity)

theorem memoryQueries_provider {width : Nat} {rows : Array MemoryRow}
    (valid : MemoryRowsValid width rows) {queries : List (G × Array G)}
    (balanced : ExactLookupBalance queries (memoryProviders rows))
    (bounded : queries.length < gSize.toNat)
    {pointer : G} {contents : Array G} (queried : (pointer, contents) ∈ queries) :
    ∃ i : Nat, ∃ hi : i < rows.size,
      rows[i].selector = 1 ∧ rows[i].pointer = pointer ∧ rows[i].contents = contents := by
  obtain ⟨provider, member, same, nonzero⟩ := exactLookupBalance_provider balanced bounded queried
  obtain ⟨i, provided⟩ := List.mem_ofFn.mp member
  subst provider
  have active : rows[i].selector = 1 := by
    rcases valid.selectors i i.isLt with inactive | active
    · exact False.elim (nonzero (inactive_multiplicity_zero inactive (valid.activity i i.isLt)))
    · exact active
  exact ⟨i, i.isLt, active, congrArg Prod.fst same, congrArg Prod.snd same⟩

theorem memoryQueries_width {width : Nat} {rows : Array MemoryRow}
    (valid : MemoryRowsValid width rows) {queries : List (G × Array G)}
    (balanced : ExactLookupBalance queries (memoryProviders rows))
    (bounded : queries.length < gSize.toNat)
    {pointer : G} {contents : Array G} (queried : (pointer, contents) ∈ queries) :
    contents.size = width := by
  obtain ⟨i, hi, _, _, same⟩ := memoryQueries_provider valid balanced bounded queried
  rw [← same]
  exact valid.widths i hi

/-- Two balanced requests for the same width and pointer have equal data.
The trace-height bound prevents a pointer from recurring after a full field
cycle; the query-count bound separately prevents requests cancelling out. -/
theorem memoryQueries_consistent {width : Nat} {rows : Array MemoryRow}
    (valid : MemoryRowsValid width rows) (heightBound : rows.size < gSize.toNat)
    {queries : List (G × Array G)}
    (balanced : ExactLookupBalance queries (memoryProviders rows))
    (queryBound : queries.length < gSize.toNat)
    {pointer : G} {left right : Array G}
    (queriedLeft : (pointer, left) ∈ queries)
    (queriedRight : (pointer, right) ∈ queries) : left = right := by
  obtain ⟨i, hi, ai, pi, vi⟩ := memoryQueries_provider valid balanced queryBound queriedLeft
  obtain ⟨j, hj, aj, pj, vj⟩ := memoryQueries_provider valid balanced queryBound queriedRight
  have same := valid.pointer_injective heightBound i j hi hj ai aj (pi.trans pj.symm)
  subst j
  exact vi.symm.trans vj

theorem memoryQueries_fact (tables : Nat → Array MemoryRow)
    (valid : ∀ width, MemoryRowsValid width (tables width))
    (queries : Nat → List (G × Array G))
    (balanced : ∀ width, ExactLookupBalance (queries width) (memoryProviders (tables width)))
    (bounded : ∀ width, (queries width).length < gSize.toNat)
    {width : Nat} {pointer : G} {contents : Array G}
    (queried : (pointer, contents) ∈ queries width) :
    memoryFacts tables width pointer contents :=
  memoryQueries_provider (valid width) (balanced width) (bounded width) queried

/-- A size-parameterized table used symbolically at `period = p`. Keeping
the size as an argument avoids a native initializer allocating `p + 1` rows
when this proof module is imported. -/
def memoryPointerCycle (period : Nat) : Array MemoryRow :=
  Array.ofFn fun i : Fin (period + 1) =>
    ⟨1, 0, G.ofNat i.val, #[G.ofNat (i.val / period)]⟩

theorem memoryPointerCycle_valid : MemoryRowsValid 1 (memoryPointerCycle gSize.toNat) := by
  constructor
  · intro i hi
    right
    simp only [memoryPointerCycle, Array.getElem_ofFn]
  · intro i hi
    simp only [memoryPointerCycle, Array.getElem_ofFn]
    exact active_satisfies 0
  · intro i hi
    simp only [memoryPointerCycle, Array.getElem_ofFn, List.size_toArray, List.length_cons,
      List.length_nil]
  · intro i hi
    simp only [memoryActivityTransition, memoryPointerCycle, Array.getElem_ofFn]
    have same : (1 : G) - 1 = 0 := (G.sub_eq_zero_iff _ _).mpr rfl
    rw [same, G.mul_zero]
  · intro i hi
    simp only [memoryPointerTransition, memoryPointerCycle, Array.getElem_ofFn]
    have same : G.ofNat i + 1 = G.ofNat (i + 1) := (G.ofNat_add i 1).symm
    rw [same, (G.sub_eq_zero_iff _ _).mpr rfl, G.mul_zero]

theorem memoryPointerCycle_inconsistent :
    ∃ i j : Fin (memoryPointerCycle gSize.toNat).size,
      (memoryPointerCycle gSize.toNat)[i].selector = 1 ∧ (memoryPointerCycle gSize.toNat)[j].selector = 1 ∧
      (memoryPointerCycle gSize.toNat)[i].pointer = (memoryPointerCycle gSize.toNat)[j].pointer ∧
      (memoryPointerCycle gSize.toNat)[i].contents ≠ (memoryPointerCycle gSize.toNat)[j].contents := by
  have size : (memoryPointerCycle gSize.toNat).size = gSize.toNat + 1 := by
    simp only [memoryPointerCycle, Array.size_ofFn]
  refine ⟨⟨0, by rw [size]; omega⟩, ⟨gSize.toNat, by rw [size]; omega⟩, ?_⟩
  simp only [Fin.getElem_fin, memoryPointerCycle, Array.getElem_ofFn]
  decide

end AIR
end Aiur
