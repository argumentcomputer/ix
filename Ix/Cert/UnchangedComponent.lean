import Ix.Cert.Unchanged

/-! # An unchanged component is Lean's block (Route A, H1, B9c)

The changed set reads a compiled component off the artifact (its classes, in
canonical order, and its nested layout) and Lean's block `all`, and counts it
changed (`componentChanged`) when the plan predicate holds (`isChanged`: split,
collapsed, permuted, a nested auxiliary moved or evaporated) or two members
share a class (`collapsesInside`). This module reads `componentChanged = false`
back (`unchanged_component`): every class is one member; with as many classes
of `all`'s members as `all` has members, each is the member of `all` at its
position; and no nested auxiliary moved or evaporated.

(c1) of B9c; (c2), the aux tail's `Muts` entry is the driver's classes, and
(c3), the entry reaches the artifact (with B9b's merge), follow. -/

namespace Ix.Cert.UnchangedComponent

open Ix (Name)
open Ix.Compile.ChangedSet

/-- No collapse inside: every class has at most one member. -/
theorem collapsesInside_false {classes : Array (Array Name)} :
    collapsesInside classes = false ↔ ∀ cls ∈ classes, cls.size ≤ 1 := by
  unfold collapsesInside
  rw [Bool.eq_false_iff, ne_eq, Array.any_eq_true]
  constructor
  · intro h cls hc
    apply Nat.le_of_not_lt
    intro lt
    obtain ⟨i, hi, hcls⟩ := Array.mem_iff_getElem.mp hc
    exact h ⟨i, hi, by simpa [hcls] using lt⟩
  · rintro h ⟨i, hi, lt⟩
    exact absurd (h _ (Array.getElem_mem hi)) (by simpa using lt)

/-- **An unchanged component**: no collapse inside; for a nonempty `all`, at
least as many classes of `all`'s members as `all` has members, and with
exactly as many, each class's representative is `all`'s member at its
position (by `==`, the stored hash); and no nested auxiliary moved or
evaporated. -/
theorem unchanged_component {all : Array Name} {classes : Array (Array Name)}
    {layout? : Option Ixon.AuxLayout} (h : componentChanged all classes layout? = false) :
    (∀ cls ∈ classes, cls.size ≤ 1) ∧
      (all.isEmpty = false →
        all.size ≤ (planClasses all classes).size ∧
          ((planClasses all classes).size = all.size →
            ∀ i (hp : i < (planClasses all classes).size) (ha : i < all.size),
              ((planClasses all classes)[i][0]? != some all[i]) = false)) ∧
      (∀ l, layout? = some l → nestedEvaporated l = false ∧ nestedMoved l = false) := by
  unfold componentChanged at h
  rw [Bool.or_eq_false_iff] at h
  obtain ⟨plan, collapse⟩ := h
  refine ⟨collapsesInside_false.mp collapse, fun nonempty => ?_, fun l hl => ?_⟩
  · unfold isChanged at plan
    rw [Bool.or_eq_false_iff] at plan
    obtain ⟨user, -⟩ := plan
    simp only [nonempty, Bool.not_false, Bool.true_and, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      Nat.not_lt] at user
    obtain ⟨size, order⟩ := user
    refine ⟨size, fun same i hp ha => ?_⟩
    unfold outOfOrder at order
    simp only [same, beq_self_eq_true, Bool.true_and, Array.any_eq_false] at order
    have hz : i < (planClasses all classes |>.zip all).size := by
      rw [Array.size_zip]; exact Nat.lt_min.mpr ⟨hp, ha⟩
    have := order i hz
    simpa [Array.getElem_zip] using this
  · unfold isChanged at plan
    rw [Bool.or_eq_false_iff] at plan
    obtain ⟨-, aux⟩ := plan
    rw [hl] at aux
    simpa only [Bool.or_eq_false_iff] using aux

end Ix.Cert.UnchangedComponent
