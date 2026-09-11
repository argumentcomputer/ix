/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Field
import Ix.Aiur.Proofs.Memory

/-!
Arithmetic extraction from the native AIR's local polynomial forms.

Boolean selector equations, the two `eq_zero` equations, case equality and
default disequality imply their semantic properties over `G`. Boolean sums
select at most one branch when the number of summands is below the field
characteristic. The bound is explicit and a cancellation counterexample
shows its necessity. These sums use the native emitter's left-fold order.

Memory-table functionality now follows from its polynomial equations and
trace-height bound without separately assuming boolean selectors. Decoding
the Rust expressions, trace widths and transition selectors, and extracting
exact lookup balance from proof verification, remain separate obligations.
-/

namespace Aiur.AIR

/-- Selector-column equation used in function and memory circuits. -/
def booleanConstraint (value : G) : G := value * (value - 1)

/-- Block and grouped-circuit selector equation, with the opposite sign. -/
def oneSubBooleanConstraint (value : G) : G := value * (1 - value)

def selectorSum (selectors : List G) : G := selectors.foldl (· + ·) 0

theorem foldl_add_eq (selectors : List G) (initial : G) :
    selectors.foldl (· + ·) initial = initial + selectorSum selectors := by
  induction selectors generalizing initial with
  | nil => exact (G.add_zero initial).symm
  | cons head tail ih =>
    simp only [List.foldl_cons, selectorSum]
    rw [ih, ih]
    simp only [G.zero_add, G.add_assoc]

theorem selectorSum_cons (head : G) (tail : List G) :
    selectorSum (head :: tail) = head + selectorSum tail := by
  simpa only [selectorSum, List.foldl_cons, G.zero_add] using foldl_add_eq tail head

theorem selectorSum_eq_count (selectors : List G)
    (boolean : ∀ value ∈ selectors, value = 0 ∨ value = 1) :
    selectorSum selectors = G.ofNat (selectors.count 1) := by
  induction selectors with
  | nil => rfl
  | cons head tail ih =>
    have rest : ∀ value ∈ tail, value = 0 ∨ value = 1 :=
      fun value member => boolean value (List.mem_cons_of_mem _ member)
    rcases boolean head List.mem_cons_self with rfl | rfl
    · rw [selectorSum_cons, G.zero_add, List.count_cons_of_ne (Ne.symm G.one_ne_zero), ih rest]
    · rw [selectorSum_cons, List.count_cons_self, ih rest, G.ofNat_add, G.add_comm]
      rfl

theorem selectorSum_n_eq_count {selectors : List G}
    (boolean : ∀ value ∈ selectors, value = 0 ∨ value = 1)
    (bounded : selectors.length < gSize.toNat) :
    (selectorSum selectors).n = selectors.count 1 := by
  rw [selectorSum_eq_count selectors boolean, G.n_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt List.count_le_length bounded)

theorem selectorSum_count_le_one {selectors : List G}
    (individual : ∀ value ∈ selectors, booleanConstraint value = 0)
    (combined : oneSubBooleanConstraint (selectorSum selectors) = 0)
    (bounded : selectors.length < gSize.toNat) : selectors.count 1 ≤ 1 := by
  have boolean : ∀ value ∈ selectors, value = 0 ∨ value = 1 :=
    fun value member => G.boolean_of_constraint (individual value member)
  have count := selectorSum_n_eq_count boolean bounded
  rcases G.boolean_of_one_sub_constraint combined with zero | one
  · rw [zero] at count
    change 0 = selectors.count 1 at count
    omega
  · rw [one] at count
    change 1 = selectors.count 1 at count
    omega

theorem selectorSum_inactive {selectors : List G}
    (individual : ∀ value ∈ selectors, booleanConstraint value = 0)
    (bounded : selectors.length < gSize.toNat)
    (inactive : selectorSum selectors = 0) : ∀ value ∈ selectors, value = 0 := by
  have boolean : ∀ value ∈ selectors, value = 0 ∨ value = 1 :=
    fun value member => G.boolean_of_constraint (individual value member)
  have count := selectorSum_n_eq_count boolean bounded
  rw [inactive] at count
  have absent : (1 : G) ∉ selectors := List.count_eq_zero.mp count.symm
  intro value member
  rcases boolean value member with zero | one
  · exact zero
  · subst value; exact False.elim (absent member)

theorem selectorSum_active_count {selectors : List G}
    (individual : ∀ value ∈ selectors, booleanConstraint value = 0)
    (bounded : selectors.length < gSize.toNat)
    (active : selectorSum selectors = 1) : selectors.count 1 = 1 := by
  have boolean : ∀ value ∈ selectors, value = 0 ∨ value = 1 :=
    fun value member => G.boolean_of_constraint (individual value member)
  have count := selectorSum_n_eq_count boolean bounded
  rw [active] at count
  exact count.symm

/-- An active bounded sum has exactly one active occurrence; all other
occurrences are zero, even when list values repeat. -/
theorem selectorSum_active_split {selectors : List G}
    (individual : ∀ value ∈ selectors, booleanConstraint value = 0)
    (bounded : selectors.length < gSize.toNat) (active : selectorSum selectors = 1) :
    ∃ before after : List G, selectors = before ++ 1 :: after ∧
      ∀ value ∈ before ++ after, value = 0 := by
  have count := selectorSum_active_count individual bounded active
  have member : (1 : G) ∈ selectors := List.count_pos_iff.mp (by omega)
  obtain ⟨before, after, equal, _⟩ := List.eq_append_cons_of_mem member
  refine ⟨before, after, equal, ?_⟩
  rw [equal, List.count_append, List.count_cons_self] at count
  have absent : (1 : G) ∉ before ++ after := by
    apply List.count_eq_zero.mp
    rw [List.count_append]
    omega
  intro value member
  have member' : value ∈ selectors := by
    rw [equal]
    rcases List.mem_append.mp member with left | right
    · exact List.mem_append_left _ left
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ right)
  rcases G.boolean_of_constraint (individual value member') with zero | one
  · exact zero
  · subst value; exact False.elim (absent member)

/-- Boolean summands alone do not prevent a full characteristic of active
branches from being represented by an inactive field sum. -/
theorem selectorSum_characteristic_cancel :
    selectorSum (List.replicate gSize.toNat (1 : G)) = 0 := by
  rw [selectorSum_eq_count _ (fun value member =>
    Or.inr (List.eq_of_mem_replicate member)), List.count_replicate_self]
  rfl

theorem nonzero_multiplicity_selector_one {multiplicity selector : G}
    (satisfied : activityConstraint multiplicity selector = 0)
    (nonzero : multiplicity ≠ 0) : selector = 1 := by
  have zero := G.mul_eq_zero_of_left_ne_zero nonzero satisfied
  exact ((G.sub_eq_zero_iff 1 selector).mp zero).symm

theorem active_eqZero {selector input inverse output : G} (active : selector = 1)
    (annihilate : selector * input * output = 0)
    (complement : selector * (input * inverse + output - 1) = 0) :
    output = G.eqZero input := by
  rw [active, G.mul_comm (1 : G) input, G.mul_one] at annihilate
  rw [active, G.mul_comm, G.mul_one] at complement
  exact G.eqZero_of_constraints annihilate complement

theorem active_case {selector matched key : G} (active : selector = 1)
    (satisfied : selector * (matched - key) = 0) : matched = key := by
  rw [active, G.mul_comm, G.mul_one] at satisfied
  exact (G.sub_eq_zero_iff matched key).mp satisfied

theorem active_default {selector matched key inverse : G} (active : selector = 1)
    (satisfied : selector * ((matched - key) * inverse - 1) = 0) : matched ≠ key := by
  rw [active, G.mul_comm, G.mul_one] at satisfied
  intro equal
  have nonzero := G.ne_zero_of_inverse_constraint satisfied
  exact nonzero ((G.sub_eq_zero_iff matched key).mpr equal)

/-- The four memory polynomial forms, with interior transition gating
resolved and column widths decoded. No boolean-selector premise. -/
structure MemoryRowsPolynomials (width : Nat) (rows : Array MemoryRow) : Prop where
  selectors : ∀ i (hi : i < rows.size), booleanConstraint rows[i].selector = 0
  activity : ∀ i (hi : i < rows.size), activityConstraint rows[i].multiplicity rows[i].selector = 0
  widths : ∀ i (hi : i < rows.size), rows[i].contents.size = width
  activityTransition : ∀ i (hi : i + 1 < rows.size),
    memoryActivityTransition (rows[i]'(by omega)) rows[i + 1] = 0
  pointerTransition : ∀ i (hi : i + 1 < rows.size),
    memoryPointerTransition (rows[i]'(by omega)) rows[i + 1] = 0

theorem MemoryRowsPolynomials.valid {width : Nat} {rows : Array MemoryRow}
    (polynomials : MemoryRowsPolynomials width rows) : MemoryRowsValid width rows :=
  ⟨fun i hi => G.boolean_of_constraint (polynomials.selectors i hi),
    polynomials.activity, polynomials.widths, polynomials.activityTransition, polynomials.pointerTransition⟩

theorem MemoryRowsPolynomials.functional (tables : Nat → Array MemoryRow)
    (polynomials : ∀ width, MemoryRowsPolynomials width (tables width))
    (bounded : ∀ width, (tables width).size < gSize.toNat)
    {width : Nat} {pointer : G} {left right : Array G}
    (loadedLeft : memoryFacts tables width pointer left)
    (loadedRight : memoryFacts tables width pointer right) : left = right :=
  memoryFacts_functional tables (fun width => (polynomials width).valid) bounded loadedLeft loadedRight

end Aiur.AIR
