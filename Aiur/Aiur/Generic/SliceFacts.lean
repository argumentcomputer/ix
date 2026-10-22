import Aiur.Generic.SourceSemantics
import Aiur.Generic.ArrayFacts

namespace Aiur.Generic.ArrayLowering

private theorem range_projects (values : List (SourceValue F)) (length : Nat) (start : Nat)
    (bound : start + length ≤ values.length) :
    (List.range' start length).mapM (projectValue (.tuple values)) =
      .ok ((values.drop start).take length) := by
  induction length generalizing start with
  | zero => simp
  | succ length ih =>
      have index : start < values.length := by omega
      have rest := ih (start + 1) (by omega)
      rw [List.range'_succ, List.mapM_cons]
      have head : projectValue (.tuple values) start = .ok values[start] := by
        simp [projectValue, List.getElem?_eq_getElem index]
      rw [head, rest, List.drop_eq_getElem_cons index, List.take_succ_cons]
      rfl

/-- Static projections select exactly the native array slice. No heap
operation is introduced, and the result holds for nested values and pointers. -/
theorem slice_projects (values : List (SourceValue F)) (start stop : Nat)
    (ordered : start ≤ stop) (bound : stop ≤ values.length) :
    ((List.range (stop - start)).map (start + ·)).mapM (projectValue (.tuple values)) =
      .ok ((values.drop start).take (stop - start)) := by
  have indices : (List.range (stop - start)).map (start + ·) = List.range' start (stop - start) := by
    simpa only [List.range_eq_range', Nat.add_zero] using List.map_add_range' (a := start) 0 (stop - start) 1
  rw [indices]
  exact range_projects values (stop - start) start (by omega)

/-- A successful native slice gives exactly the compiler's projection list.
This direction obtains shape and bounds from the native operation itself. -/
theorem projects_of_source_slice {input result : SourceValue F} {start stop : Nat}
    (sliced : SourceSemantics.sliceValue input start (some stop) = .ok result) :
    ∃ values,
      ((List.range (stop - start)).map (start + ·)).mapM (projectValue input) = .ok values ∧
      result = .tuple values := by
  cases input <;> simp only [SourceSemantics.sliceValue, Option.getD_some] at sliced
  all_goals first | contradiction | skip
  rename_i values
  split at sliced
  · contradiction
  · rename_i bounds
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at bounds
    have ordered : start ≤ stop := by omega
    have bound : stop ≤ values.length := by omega
    have same : result = .tuple ((values.drop start).take (stop - start)) := by
      simpa only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] using sliced.symm
    exact ⟨_, slice_projects values start stop ordered bound, same⟩

/-- Under the checked operand shape and static bounds, the projection result
reflects back to native slicing, including the empty-slice case. -/
theorem source_slice_of_projects {items values : List (SourceValue F)} {start stop : Nat}
    (ordered : start ≤ stop) (bound : stop ≤ items.length)
    (projected : ((List.range (stop - start)).map (start + ·)).mapM
      (projectValue (.tuple items)) = .ok values) :
    SourceSemantics.sliceValue (.tuple items) start (some stop) = .ok (.tuple values) := by
  have same := Except.ok.inj ((slice_projects items start stop ordered bound).symm.trans projected)
  rw [← same]
  simp [SourceSemantics.sliceValue, Nat.not_lt.mpr ordered, Nat.not_lt.mpr bound]

end Aiur.Generic.ArrayLowering
