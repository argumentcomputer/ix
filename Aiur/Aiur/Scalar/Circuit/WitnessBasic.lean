import Aiur.Scalar.Circuit.ExpressionCorrectness

namespace Aiur.Scalar.Circuit.Compiler

/-- New equations vanish and every new send is disabled under this assignment. -/
structure InactiveExtension [Field F] (before after : BuildState F)
    (assignment : Var → F) : Prop where
  increase : before.nextVar ≤ after.nextVar
  equations : ∃ added, after.constraints.toList = before.constraints.toList ++ added ∧
    Satisfies added assignment
  sends : ∃ added, after.sends.toList = before.sends.toList ++ added ∧
    ∀ send ∈ added, send.enable.denote assignment = 0

theorem InactiveExtension.refl [Field F] (state : BuildState F) (assignment : Var → F) :
    InactiveExtension state state assignment :=
  ⟨Nat.le_refl _, ⟨[], by simp, by simp [Satisfies]⟩, ⟨[], by simp, by simp⟩⟩

theorem InactiveExtension.trans [Field F] {first middle last : BuildState F}
    {assignment : Var → F} (left : InactiveExtension first middle assignment)
    (right : InactiveExtension middle last assignment) : InactiveExtension first last assignment := by
  obtain ⟨leftEquations, leftShape, leftZero⟩ := left.equations
  obtain ⟨rightEquations, rightShape, rightZero⟩ := right.equations
  obtain ⟨leftSends, leftSendShape, leftDisabled⟩ := left.sends
  obtain ⟨rightSends, rightSendShape, rightDisabled⟩ := right.sends
  refine ⟨le_trans left.increase right.increase,
    ⟨leftEquations ++ rightEquations, by simp [rightShape, leftShape, List.append_assoc],
      (satisfies_append _ _ _).mpr ⟨leftZero, rightZero⟩⟩,
    ⟨leftSends ++ rightSends, by simp [rightSendShape, leftSendShape, List.append_assoc], ?_⟩⟩
  intro send member
  rcases List.mem_append.mp member with member | member
  · exact leftDisabled send member
  · exact rightDisabled send member

/-- Inactive code preserves all earlier equations and call justifications. -/
theorem InactiveExtension.valid [Field F] {before after : BuildState F}
    {assignment : Var → F} (extension : InactiveExtension before after assignment)
    {calls : CallRelation F} (valid : before.Valid calls assignment) :
    after.Valid calls assignment := by
  obtain ⟨equations, shape, zero⟩ := extension.equations
  obtain ⟨sends, sendShape, disabled⟩ := extension.sends
  constructor
  · rw [shape]
    exact (satisfies_append _ _ _).mpr ⟨valid.constraints, zero⟩
  · intro send member active
    rw [sendShape] at member
    rcases List.mem_append.mp member with member | member
    · exact valid.calls send member active
    · have := disabled send member
      simp [this] at active

theorem InactiveExtension.fresh [Field F] (state : BuildState F) (assignment : Var → F) :
    InactiveExtension state { state with nextVar := state.nextVar + 1 } assignment :=
  ⟨Nat.le_succ _, ⟨[], by simp, by simp [Satisfies]⟩, ⟨[], by simp, by simp⟩⟩

theorem InactiveExtension.constrain [Field F] (state : BuildState F)
    {assignment : Var → F} {polynomial : ArithExpr F}
    (zero : polynomial.denote assignment = 0) :
    InactiveExtension state { state with constraints := state.constraints.push polynomial } assignment :=
  ⟨Nat.le_refl _, ⟨[polynomial], by simp, by simpa [Satisfies] using zero⟩,
    ⟨[], by simp, by simp⟩⟩

theorem InactiveExtension.send [Field F] (state : BuildState F)
    {assignment : Var → F} {send : Send F} (disabled : send.enable.denote assignment = 0) :
    InactiveExtension state { state with sends := state.sends.push send } assignment :=
  ⟨Nat.le_refl _, ⟨[], by simp, by simp [Satisfies]⟩,
    ⟨[send], by simp, by simpa using disabled⟩⟩

theorem InactiveExtension.constrainMany [Field F] (state : BuildState F)
    {assignment : Var → F} {polynomials : List (ArithExpr F)}
    (zero : Satisfies polynomials assignment) :
    InactiveExtension state
      { state with constraints := state.constraints ++ polynomials.toArray } assignment :=
  ⟨Nat.le_refl _, ⟨polynomials, by simp, zero⟩, ⟨[], by simp, by simp⟩⟩

theorem denote_of_prefix [Field F] {function : String} {initial values : List F}
    (extension : initial.IsPrefix values) {bound : Nat} (size : initial.length = bound)
    {polynomial : ArithExpr F} (bounded : polynomial.inBounds bound = true) :
    polynomial.denote (Row.assignment ⟨function, values⟩) =
      polynomial.denote (Row.assignment ⟨function, initial⟩) :=
  ArithExpr.denote_eq_of_agree
    (fun _ bound => Row.assignment_of_prefix extension (by simpa [size] using bound)) bounded

theorem value_of_prefix [Zero F] {function : String} {initial values : List F}
    (extension : initial.IsPrefix values) {bound : Nat} (size : initial.length = bound)
    {id : Var} (bounded : id < bound) :
    Row.assignment ⟨function, values⟩ id = Row.assignment ⟨function, initial⟩ id :=
  Row.assignment_of_prefix extension (by simpa [size] using bounded)

theorem denotes_of_prefix [Field F] {function : String} {initial values : List F}
    (extension : initial.IsPrefix values) {bound : Nat} (size : initial.length = bound)
    {polynomials : List (ArithExpr F)}
    (bounded : ∀ polynomial ∈ polynomials, polynomial.inBounds bound = true) :
    polynomials.map (ArithExpr.denote (Row.assignment ⟨function, values⟩)) =
      polynomials.map (ArithExpr.denote (Row.assignment ⟨function, initial⟩)) := by
  apply List.map_congr_left
  exact fun polynomial member => denote_of_prefix extension size (bounded polynomial member)

theorem assignment_append_value [Zero F] (function : String) (initial : List F) (value : F) :
    Row.assignment ⟨function, initial ++ [value]⟩ initial.length = value := by
  simp [Row.assignment]

theorem localsEnvironment_of_prefix [Zero F] {function : String} {initial values : List F}
    (extension : initial.IsPrefix values) {bound : Nat} (size : initial.length = bound)
    {locals : List (String × Var)} (bounded : ∀ binding ∈ locals, binding.2 < bound) :
    localsEnvironment locals (Row.assignment ⟨function, values⟩) =
      localsEnvironment locals (Row.assignment ⟨function, initial⟩) := by
  apply List.map_congr_left
  intro binding member
  rw [Row.assignment_of_prefix (before := ⟨function, initial⟩) extension
    (by simpa [size] using bounded binding member)]

theorem BuildState.WellFormed.fresh {state : BuildState F} (layout : state.WellFormed) :
    { state with nextVar := state.nextVar + 1 }.WellFormed :=
  ⟨fun equation member => ArithExpr.inBounds_mono (Nat.le_succ _) (layout.constraints equation member),
    fun send member => Send.inBounds_mono (Nat.le_succ _) (layout.sends send member)⟩

theorem BuildState.WellFormed.constrain {state : BuildState F} (layout : state.WellFormed)
    {polynomial : ArithExpr F} (bound : polynomial.inBounds state.nextVar = true) :
    { state with constraints := state.constraints.push polynomial }.WellFormed := by
  refine ⟨?_, layout.sends⟩
  intro equation member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact layout.constraints equation member
  · exact bound

theorem BuildState.WellFormed.constrainMany {state : BuildState F} (layout : state.WellFormed)
    {polynomials : List (ArithExpr F)}
    (bound : ∀ polynomial ∈ polynomials, polynomial.inBounds state.nextVar = true) :
    { state with constraints := state.constraints ++ polynomials.toArray }.WellFormed := by
  refine ⟨?_, layout.sends⟩
  intro polynomial member
  simp only [Array.toList_append, List.mem_append] at member
  rcases member with member | member
  · exact layout.constraints polynomial member
  · exact bound polynomial member

theorem BuildState.WellFormed.send {state : BuildState F} (layout : state.WellFormed)
    {send : Send F} (bound : send.inBounds state.nextVar = true) :
    { state with sends := state.sends.push send }.WellFormed := by
  refine ⟨layout.constraints, ?_⟩
  intro next member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact layout.sends next member
  · exact bound

theorem BuildState.Valid.constrain [Field F] {state : BuildState F} {calls : CallRelation F}
    {assignment : Var → F} (valid : state.Valid calls assignment) {polynomial : ArithExpr F}
    (zero : polynomial.denote assignment = 0) :
    { state with constraints := state.constraints.push polynomial }.Valid calls assignment := by
  refine ⟨?_, valid.calls⟩
  intro equation member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact valid.constraints equation member
  · exact zero

theorem BuildState.Valid.constrainMany [Field F] {state : BuildState F} {calls : CallRelation F}
    {assignment : Var → F} (valid : state.Valid calls assignment) {polynomials : List (ArithExpr F)}
    (zero : Satisfies polynomials assignment) :
    { state with constraints := state.constraints ++ polynomials.toArray }.Valid calls assignment := by
  refine ⟨?_, valid.calls⟩
  simpa using (satisfies_append _ _ _).mpr ⟨valid.constraints, zero⟩

theorem BuildState.Valid.of_prefix [Field F] {function : String} {initial values : List F}
    {state : BuildState F} {calls : CallRelation F}
    (valid : state.Valid calls (Row.assignment ⟨function, initial⟩))
    (layout : state.WellFormed) (size : initial.length = state.nextVar)
    (extension : initial.IsPrefix values) :
    state.Valid calls (Row.assignment ⟨function, values⟩) := by
  constructor
  · intro equation member
    rw [denote_of_prefix extension size (layout.constraints equation member)]
    exact valid.constraints equation member
  · intro send member active
    have bounds := layout.sends send member
    simp only [Send.inBounds, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at bounds
    have enable := denote_of_prefix (function := function) extension size bounds.1.2
    rw [enable] at active
    have args : send.args.map (ArithExpr.denote (Row.assignment ⟨function, values⟩)) =
        send.args.map (ArithExpr.denote (Row.assignment ⟨function, initial⟩)) := by
      apply List.map_congr_left
      exact fun arg member => denote_of_prefix extension size (bounds.2 arg member)
    rw [args, Row.assignment_of_prefix (before := ⟨function, initial⟩) extension
      (by simpa [size] using bounds.1.1)]
    exact valid.calls send member active

theorem foldl_add_inBounds {selectors : List (ArithExpr F)} {initial : ArithExpr F} {bound : Nat}
    (initialBound : initial.inBounds bound = true)
    (bounded : ∀ selector ∈ selectors, selector.inBounds bound = true) :
    (selectors.foldl ArithExpr.add initial).inBounds bound = true := by
  induction selectors generalizing initial with
  | nil => exact initialBound
  | cons head tail ih =>
      apply ih
      · simp [ArithExpr.inBounds, initialBound, bounded head (by simp)]
      · exact fun selector member => bounded selector (by simp [member])

theorem exclusionConstraints_inBounds {selectors : List (ArithExpr F)} {bound : Nat}
    (bounded : ∀ selector ∈ selectors, selector.inBounds bound = true) :
    ∀ equation ∈ exclusionConstraints selectors, equation.inBounds bound = true := by
  induction selectors with
  | nil => simp [exclusionConstraints]
  | cons head tail ih =>
      intro equation member
      simp only [exclusionConstraints, List.mem_append, List.mem_map] at member
      rcases member with ⟨selector, member, rfl⟩ | member
      · simp [ArithExpr.inBounds, bounded head (by simp), bounded selector (by simp [member])]
      · exact ih (fun selector member => bounded selector (by simp [member])) equation member

theorem selectionConstraints_inBounds [Field F] {parent : ArithExpr F}
    {selectors : List (ArithExpr F)} {bound : Nat} (parentBound : parent.inBounds bound = true)
    (bounded : ∀ selector ∈ selectors, selector.inBounds bound = true) :
    ∀ equation ∈ selectionConstraints parent selectors, equation.inBounds bound = true := by
  intro equation member
  simp only [selectionConstraints, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with (⟨selector, member, rfl⟩ | member) | rfl
  · simp [ArithExpr.inBounds, bounded selector member]
  · exact exclusionConstraints_inBounds bounded equation member
  · simp [ArithExpr.inBounds, parentBound,
      foldl_add_inBounds (initial := .const (0 : F)) rfl bounded]

theorem selectionConstraints_zero [Field F] {parent : ArithExpr F}
    {selectors : List (ArithExpr F)} {assignment : Var → F}
    (inactive : parent.denote assignment = 0)
    (zeros : ∀ selector ∈ selectors, selector.denote assignment = 0) :
    Satisfies (selectionConstraints parent selectors) assignment := by
  apply (selectionConstraints_satisfies _ _ _).mpr
  rw [inactive]
  apply SelectorsValid.zeros
  intro value present
  obtain ⟨selector, selectorMember, same⟩ := List.mem_map.mp present
  rw [← same]
  exact zeros selector selectorMember

/-- Appending zeroes leaves the total assignment unchanged, including out-of-bounds values. -/
theorem assignment_append_zeros [Zero F] (function : String) (initial : List F) (count : Nat) :
    Row.assignment ⟨function, initial ++ List.replicate count 0⟩ =
      Row.assignment ⟨function, initial⟩ := by
  funext id
  by_cases bound : id < initial.length
  · simp [Row.assignment, List.getElem?_append_left bound]
  · simp [Row.assignment, List.getElem?_append_right (Nat.le_of_not_gt bound),
      List.getElem?_eq_none (Nat.le_of_not_gt bound), List.getElem?_replicate]
    split <;> rfl

end Aiur.Scalar.Circuit.Compiler
