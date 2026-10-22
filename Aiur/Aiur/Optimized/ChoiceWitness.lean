import Aiur.Optimized.ChoiceFacts
import Aiur.Scalar.Circuit.WitnessBasic

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]

theorem State.Scoped.activation_bound {state : State F} (scopeLayout : state.Scoped) (id : ScopeId) :
    (state.activation id).inBounds state.roles.size = true := by
  cases found : state.scopes[id]? with
  | none => simp [State.activation, found, Circuit.ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds]
  | some scope =>
      simpa [State.activation, found] using scopeLayout.activations scope
        (by simpa using Array.mem_of_getElem? found)

theorem State.Scoped.fresh {state : State F} (scopeLayout : state.Scoped) (role : Role) :
    ({ state with roles := state.roles.push role, aliases := state.aliases.push none } : State F).Scoped := by
  refine ⟨scopeLayout.equations, scopeLayout.calls, scopeLayout.cells, ?_⟩
  intro scope member
  exact Scalar.Circuit.ArithExpr.inBounds_mono (by simp) (scopeLayout.activations scope member)

theorem State.Scoped.equation {state : State F} (scopeLayout : state.Scoped) {scope : ScopeId}
    (bounded : scope < state.scopes.size) (polynomial : Polynomial F) :
    ({ state with equations := state.equations.push ⟨scope, polynomial⟩ } : State F).Scoped := by
  refine ⟨?_, scopeLayout.calls, scopeLayout.cells, scopeLayout.activations⟩
  intro equation member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact scopeLayout.equations equation member
  · exact bounded

private theorem choiceEquation_scope {before : State F} {enclosing : Scope F} {count : Nat}
    {equation : Equation F} (member : equation ∈ choiceEquations before enclosing count) :
    equation.scope = 0 := by
  simp only [choiceEquations, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.mem_map, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with ⟨i, _, equal | ⟨j, _, equal⟩⟩ | equal <;> subst equation <;> rfl

theorem choice_scoped {parent count : Nat} {children : List ScopeId} {before after : State F}
    (compiled : choice parent count before = .ok (children, after))
    (scopeLayout : before.Scoped) : after.Scoped := by
  obtain ⟨enclosing, found, _, rfl⟩ := choice_eq compiled
  have rootBound : 0 < before.scopes.size := by
    have := (Array.getElem?_eq_some_iff.mp found).1
    omega
  have grow : before.roles.size ≤ before.roles.size + count := Nat.le_add_right _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro equation member
    simp only [choiceState, Array.toList_append, List.toList_toArray, List.mem_append] at member
    rcases member with old | new
    · exact lt_of_lt_of_le (scopeLayout.equations equation old) (by simp)
    · rw [choiceEquation_scope new]
      simpa using lt_of_lt_of_le rootBound (Nat.le_add_right before.scopes.size count)
  · intro call member
    exact lt_of_lt_of_le (scopeLayout.calls call member) (by simp)
  · intro cell member
    exact lt_of_lt_of_le (scopeLayout.cells cell member) (by simp)
  · intro scope member
    simp only [choiceState, Array.toList_append, List.toList_toArray, List.mem_append,
      List.mem_map, List.mem_range] at member
    rcases member with old | ⟨i, bounded, rfl⟩
    · exact Scalar.Circuit.ArithExpr.inBounds_mono (by simpa using grow) (scopeLayout.activations scope old)
    · simpa [Circuit.ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
        (Nat.add_lt_add_left bounded before.roles.size)

private theorem choiceEquation_bounded {before : State F} {enclosing : Scope F} {count : Nat}
    (enclosingBound : enclosing.activation.inBounds before.roles.size = true)
    {equation : Equation F} (member : equation ∈ choiceEquations before enclosing count) :
    equation.polynomial.inBounds (before.roles.size + count) = true := by
  have selector (i : Nat) (bounded : i < count) :
      (Polynomial.var (F := F) (before.roles.size + i)).inBounds (before.roles.size + count) = true := by
    simpa [Circuit.ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
      Nat.add_lt_add_left bounded before.roles.size
  have total : ((choiceSelectors before count).foldl Polynomial.add (.const 0)).inBounds
      (before.roles.size + count) = true := by
    apply Scalar.Circuit.Compiler.foldl_add_inBounds rfl
    intro p member
    obtain ⟨i, bounded, rfl⟩ := List.mem_map.mp member
    exact selector i (List.mem_range.mp bounded)
  simp only [choiceEquations, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.mem_map, List.mem_singleton, List.mem_range, List.not_mem_nil, or_false] at member
  rcases member with ⟨i, bounded, equal | ⟨j, less, equal⟩⟩ | equal
  · subst equation
    simpa [Circuit.ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using selector i bounded
  · subst equation
    simpa [Circuit.ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
      And.intro (selector i bounded) (selector j (less.trans bounded))
  · subst equation
    simpa [Circuit.ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
      And.intro total (Scalar.Circuit.ArithExpr.inBounds_mono (Nat.le_add_right _ _) enclosingBound)

private theorem choiceState_wellformed {before : State F} {parent count : Nat} {enclosing : Scope F}
    (found : before.scopes[parent]? = some enclosing) (scopeLayout : before.Scoped)
    (layout : before.toReference.WellFormed) :
    (choiceState before parent enclosing count).toReference.WellFormed := by
  let after := choiceState before parent enclosing count
  have rootBound : 0 < before.scopes.size := by
    have := (Array.getElem?_eq_some_iff.mp found).1
    omega
  have increase : before.roles.size ≤ after.roles.size := by simp [after]
  have enclosingBound : enclosing.activation.inBounds before.roles.size = true :=
    scopeLayout.activations enclosing (by simpa using Array.mem_of_getElem? found)
  refine ⟨?_, ?_, ?_⟩
  · intro polynomial member
    simp only [State.toReference, Array.toList_map, List.mem_map] at member
    obtain ⟨equation, member, rfl⟩ := member
    change (Polynomial.mul (after.activation equation.scope) equation.polynomial).inBounds after.roles.size = true
    simp only [choiceState, Array.toList_append, List.toList_toArray, List.mem_append] at member
    rcases member with old | new
    · rw [choiceState_activation (scopeLayout.equations equation old)]
      apply Scalar.Circuit.ArithExpr.inBounds_mono increase
      exact layout.constraints _ (by
        simp only [State.toReference, Array.toList_map, List.mem_map]
        exact ⟨equation, old, rfl⟩)
    · rw [choiceEquation_scope new, choiceState_activation rootBound]
      simpa only [after, choiceState_roles_size, Circuit.ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true] using
        And.intro (Scalar.Circuit.ArithExpr.inBounds_mono increase (scopeLayout.activation_bound 0))
          (choiceEquation_bounded enclosingBound new)
  · intro send member
    simp only [State.toReference, Array.toList_map, List.mem_map] at member
    obtain ⟨call, member, rfl⟩ := member
    change (Circuit.Send.mk call.channel call.args call.result (after.activation call.scope)).inBounds after.roles.size = true
    rw [choiceState_activation (scopeLayout.calls call member)]
    apply Circuit.Compiler.Send_bounds_mono increase
    exact layout.sends _ (by
      simp only [State.toReference, Array.toList_map, List.mem_map]
      exact ⟨call, member, rfl⟩)
  · intro lookup member
    simp only [State.toReference, Array.toList_map, List.mem_map] at member
    obtain ⟨cell, member, rfl⟩ := member
    change (Circuit.MemoryLookup.mk cell.address cell.value (after.activation cell.scope)).inBounds after.roles.size = true
    rw [choiceState_activation (scopeLayout.cells cell member)]
    apply Circuit.Compiler.MemoryLookup_bounds_mono increase
    exact layout.memory _ (by
      simp only [State.toReference, Array.toList_map, List.mem_map]
      exact ⟨cell, member, rfl⟩)

private theorem choiceState_valid {before : State F} {parent count : Nat} {enclosing : Scope F}
    (scopeLayout : before.Scoped) {rom : WireROM F} {calls : Circuit.CallRelation F}
    {assignment : Witness → F} (valid : before.Valid rom calls assignment)
    (zero : ∀ equation ∈ choiceEquations before enclosing count,
      equation.polynomial.denote assignment = 0) :
    (choiceState before parent enclosing count).Valid rom calls assignment := by
  refine ⟨?_, ?_, ?_⟩
  · intro equation member
    simp only [choiceState, Array.toList_append, List.toList_toArray, List.mem_append] at member
    rcases member with old | new
    · rw [choiceState_activation (scopeLayout.equations equation old)]
      exact valid.1 equation old
    · rw [zero equation new, mul_zero]
  · intro call member active
    rw [choiceState_activation (scopeLayout.calls call member)] at active
    exact valid.2.1 call member active
  · intro cell member active
    rw [choiceState_activation (scopeLayout.cells cell member)] at active
    exact valid.2.2 cell member active

/-- A choice witness selects one arm, or no arm when its parent is inactive. -/
def choiceSelected {count : Nat} (selected : Option (Fin count)) (i : Nat) : F :=
  if selected.map Fin.val = some i then 1 else 0

private theorem choiceSelected_boolean {count : Nat} (selected : Option (Fin count)) (i : Nat) :
    choiceSelected (F := F) selected i * (choiceSelected selected i - 1) = 0 := by
  unfold choiceSelected
  split <;> simp

private theorem choiceSelected_exclusive {count : Nat} (selected : Option (Fin count))
    (i j : Nat) (different : i ≠ j) :
    choiceSelected (F := F) selected i * choiceSelected selected j = 0 := by
  by_cases left : selected.map Fin.val = some i
  · have right : selected.map Fin.val ≠ some j := fun equal => different (Option.some.inj (left.symm.trans equal))
    simp [choiceSelected, left, different]
  · simp [choiceSelected, left]

private theorem choiceSelected_sum {count : Nat} (selected : Option (Fin count)) :
    ∑ i : Fin count, choiceSelected (F := F) selected i = if selected.isSome then 1 else 0 := by
  cases selected with
  | none => simp [choiceSelected]
  | some selected =>
      have pointwise (i : Fin count) : choiceSelected (F := F) (some selected) i =
          if selected = i then 1 else 0 := by simp [choiceSelected, Fin.ext_iff]
      simp_rw [pointwise]
      simp

/-- Construct all selector witnesses, keeping every existing witness fixed.
The optional arm is absent exactly when the parent activation is zero. -/
theorem choice_complete {parent count : Nat} {children : List ScopeId} {before after : State F}
    (compiled : choice parent count before = .ok (children, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
    (valid : before.Valid rom calls initial) (selected : Option (Fin count))
    (parentValue : (before.activation parent).denote initial = if selected.isSome then 1 else 0) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      ∀ i : Fin children.length,
        (after.activation children[i]).denote assignment = choiceSelected selected i := by
  obtain ⟨enclosing, found, rfl, rfl⟩ := choice_eq compiled
  let assignment : Witness → F := fun id =>
    if id < before.roles.size then initial id else choiceSelected selected (id - before.roles.size)
  have agree : ∀ id < before.roles.size, assignment id = initial id := by
    intro id bounded
    simp [assignment, bounded]
  have witness (i : Nat) : assignment (before.roles.size + i) = choiceSelected selected i := by
    simp [assignment, Nat.not_lt.mpr (Nat.le_add_right _ _)]
  have enclosingBound := scopeLayout.activations enclosing (by simpa using Array.mem_of_getElem? found)
  have parentValue' : enclosing.activation.denote assignment = if selected.isSome then 1 else 0 := by
    change Scalar.Circuit.ArithExpr.denote assignment enclosing.activation = _
    rw [Scalar.Circuit.ArithExpr.denote_eq_of_agree agree enclosingBound]
    simpa [State.activation, found, Circuit.ArithExpr.denote] using parentValue
  have oldValid : before.Valid rom calls assignment := by
    apply (before.valid_iff_reference rom calls assignment).mpr
    exact ((before.valid_iff_reference rom calls initial).mp valid).of_agree layout agree
  have zero : ∀ equation ∈ choiceEquations before enclosing count,
      equation.polynomial.denote assignment = 0 := by
    intro equation member
    simp only [choiceEquations, List.mem_append, List.mem_flatMap, List.mem_cons,
      List.mem_map, List.mem_singleton, List.mem_range, List.not_mem_nil, or_false] at member
    rcases member with ⟨i, bounded, equal | ⟨j, less, equal⟩⟩ | equal
    · subst equation
      simpa only [Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, witness] using
        choiceSelected_boolean (F := F) selected i
    · subst equation
      simpa only [Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, witness] using
        choiceSelected_exclusive (F := F) selected i j (Nat.ne_of_gt less)
    · subst equation
      change ((choiceSelectors before count).foldl Polynomial.add (.const 0)).denote assignment -
        enclosing.activation.denote assignment = 0
      rw [choice_total_denote, parentValue']
      simp_rw [witness]
      rw [choiceSelected_sum, sub_self]
  have finalValid := choiceState_valid (parent := parent) scopeLayout oldValid zero
  refine ⟨assignment, ⟨?_, agree, choiceState_wellformed found scopeLayout layout,
    ((choiceState before parent enclosing count).valid_iff_reference rom calls assignment).mp finalValid⟩, ?_⟩
  · change before.roles.size ≤ (choiceState before parent enclosing count).roles.size
    simp
  · intro i
    simp only [Fin.getElem_fin, choiceChildren_getElem, choiceState_child (by simpa using i.isLt),
      Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, witness]

end Aiur.Optimized.Compiler
