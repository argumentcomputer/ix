import Compilatrix.Ixby.Stage2.Fri

namespace Compilatrix.Ixby.Stage2.Fri

open MultiStark.Verify

/-- Every suffix has the exact source fold, including its alpha powers and
both accumulator values. No field-algebra reassociation is needed. -/
theorem reduceLoop_eq_pairs (alpha reciprocal : Ext) (row : Array Field)
    (opened : Array Ext) (sizes : row.size = opened.size) (index : Nat)
    (power value : Ext) :
    reduceLoop alpha reciprocal row opened sizes index power value =
      MultiStark.Verify.Fri.reduceCoordinatePairs alpha reciprocal
        ((row.toList.drop index).zip (opened.toList.drop index)) (power, value) := by
  rw [reduceLoop]
  split
  next inside =>
    rw [List.drop_eq_getElem_cons (l := row.toList) (i := index) (by simpa using inside),
      List.drop_eq_getElem_cons (l := opened.toList) (i := index) (by simpa [← sizes] using inside)]
    simp only [List.zip_cons_cons, MultiStark.Verify.Fri.reduceCoordinatePairs,
      MultiStark.Verify.Fri.coordinateStep, Array.getElem_toList]
    exact reduceLoop_eq_pairs alpha reciprocal row opened sizes (index + 1) _ _
  next outside =>
    rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt outside)]
    rfl
termination_by row.size - index

theorem reduceLoop_eq_coordinates (alpha reciprocal : Ext) (row : Array Field)
    (opened : Array Ext) (sizes : row.size = opened.size) (power value : Ext) :
    MultiStark.Verify.Fri.reduceCoordinates alpha reciprocal row.toList opened.toList
      power value = .ok (reduceLoop alpha reciprocal row opened sizes 0 power value) := by
  simp [MultiStark.Verify.Fri.reduceCoordinates, MultiStark.Verify.ensure, sizes,
    reduceLoop_eq_pairs, Functor.map, Except.map]

theorem reduceCoordinates_eq (alpha reciprocal : Ext) (row : Array Field)
    (opened : Array Ext) (power value : Ext) :
    MultiStark.Verify.Fri.reduceCoordinates alpha reciprocal row.toList opened.toList
      power value = reduceCoordinates alpha reciprocal row opened power value := by
  by_cases sizes : row.size = opened.size
  · rw [reduceCoordinates, dif_pos sizes]
    exact reduceLoop_eq_coordinates alpha reciprocal row opened sizes power value
  · simp [reduceCoordinates, MultiStark.Verify.Fri.reduceCoordinates,
      MultiStark.Verify.ensure, sizes, Functor.map, Except.map]

private theorem bind_congr {ε α β : Type} (result : Except ε α)
    (left right : α → Except ε β) (same : ∀ value, left value = right value) :
    result.bind left = result.bind right := congrArg (result.bind ·) (funext same)

/-- Complete source equality, including width errors, denominator errors,
empty opening lists, and alpha-power continuation across points. -/
theorem reducePoints_eq : MultiStark.Verify.Fri.reducePoints = reducePoints := by
  funext alpha x width row openings power value
  induction openings generalizing power value with
  | nil => rfl
  | cons opening openings ih =>
    rw [MultiStark.Verify.Fri.reducePoints, reducePoints]
    apply bind_congr
    intro checkedWidth
    apply bind_congr
    intro reciprocal
    rw [reduceCoordinates_eq]
    apply bind_congr
    intro pair
    exact ih pair.1 pair.2

end Compilatrix.Ixby.Stage2.Fri
