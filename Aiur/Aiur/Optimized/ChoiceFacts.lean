import Aiur.Optimized.ReferenceState
import Aiur.Optimized.BranchFacts
import Mathlib.Algebra.BigOperators.Fin

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]

/-- Every scoped obligation refers to an existing scope, and every activation
uses only allocated logical witnesses. This includes unused scopes. -/
structure State.Scoped (state : State F) : Prop where
  equations : ∀ equation ∈ state.equations.toList, equation.scope < state.scopes.size
  calls : ∀ call ∈ state.calls.toList, call.scope < state.scopes.size
  cells : ∀ cell ∈ state.cells.toList, cell.scope < state.scopes.size
  activations : ∀ scope ∈ state.scopes.toList, scope.activation.inBounds state.roles.size = true

theorem choice_eq {parent count : Nat} {children : List ScopeId} {before after : State F}
    (compiled : choice parent count before = .ok (children, after)) :
    ∃ enclosing, before.scopes[parent]? = some enclosing ∧
      children = choiceChildren before count ∧ after = choiceState before parent enclosing count := by
  simp only [choice] at compiled
  obtain ⟨enclosing, middle, scopeRun, remaining⟩ := bind_ok.mp compiled
  obtain ⟨found, stateEq⟩ := getScope_eq scopeRun
  subst middle
  change Except.ok (choiceChildren before count, choiceState before parent enclosing count) =
    Except.ok (children, after) at remaining
  obtain ⟨childEq, afterEq⟩ := Prod.mk.inj (Except.ok.inj remaining)
  exact ⟨enclosing, found, childEq.symm, afterEq.symm⟩

@[simp] theorem choiceChildren_length (before : State F) (count : Nat) :
    (choiceChildren before count).length = count := by simp [choiceChildren]

@[simp] theorem choiceChildren_getElem (before : State F) (count : Nat) (i : Nat)
    (bound : i < (choiceChildren before count).length) :
    (choiceChildren before count)[i] = before.scopes.size + i := by
  simp [choiceChildren]

@[simp] theorem choiceState_roles_size (before : State F) (parent : ScopeId)
    (enclosing : Scope F) (count : Nat) :
    (choiceState before parent enclosing count).roles.size = before.roles.size + count := by
  simp [choiceState]

@[simp] theorem choiceState_scopes_size (before : State F) (parent : ScopeId)
    (enclosing : Scope F) (count : Nat) :
    (choiceState before parent enclosing count).scopes.size = before.scopes.size + count := by
  simp [choiceState]

theorem choiceState_scope {before : State F} {parent count : Nat} {enclosing : Scope F}
    {id : ScopeId} {value : Scope F} (found : before.scopes[id]? = some value) :
    (choiceState before parent enclosing count).scopes[id]? = some value := by
  have bounded := (Array.getElem?_eq_some_iff.mp found).1
  simpa [choiceState, Array.getElem?_append, bounded] using found

theorem choiceState_activation {before : State F} {parent count : Nat} {enclosing : Scope F}
    {id : ScopeId} (bounded : id < before.scopes.size) :
    (choiceState before parent enclosing count).activation id = before.activation id := by
  simp [State.activation, choiceState, Array.getElem?_append, bounded]

theorem choiceState_child {before : State F} {parent count : Nat} {enclosing : Scope F}
    {i : Nat} (bounded : i < count) :
    (choiceState before parent enclosing count).activation (before.scopes.size + i) =
      .var (before.roles.size + i) := by
  simp [State.activation, choiceState, Array.getElem?_append, Nat.not_lt.mpr (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_range bounded]

theorem choiceState_extends (before : State F) (parent : ScopeId) (enclosing : Scope F) (count : Nat) :
    before.Extends (choiceState before parent enclosing count) := by
  refine ⟨fun _ _ => choiceState_scope, ?_, ?_, ?_⟩
  · intro equation member
    simp [choiceState, member]
  · exact fun _ => id
  · exact fun _ => id

theorem choice_extends {parent count : Nat} {children : List ScopeId} {before after : State F}
    (compiled : choice parent count before = .ok (children, after)) : before.Extends after := by
  obtain ⟨enclosing, _, _, rfl⟩ := choice_eq compiled
  exact choiceState_extends before parent enclosing count

theorem choice_length {parent count : Nat} {children : List ScopeId} {before after : State F}
    (compiled : choice parent count before = .ok (children, after)) : children.length = count := by
  obtain ⟨_, _, rfl, _⟩ := choice_eq compiled
  simp

theorem State.Extends.activation_eq {before after : State F} (extension : before.Extends after)
    {scope : ScopeId} (bounded : scope < before.scopes.size) :
    after.activation scope = before.activation scope := by
  cases found : before.scopes[scope]? with
  | none => exact False.elim (Nat.not_le_of_gt bounded (Array.getElem?_eq_none_iff.mp found))
  | some value => simp only [State.activation, found, extension.scopes scope value found]

theorem choice_child_bound {parent count : Nat} {children : List ScopeId} {before after : State F}
    (compiled : choice parent count before = .ok (children, after)) :
    ∀ child ∈ children, child < after.scopes.size := by
  obtain ⟨enclosing, _, rfl, rfl⟩ := choice_eq compiled
  intro child member
  obtain ⟨i, bounded, rfl⟩ := List.mem_map.mp member
  simpa using Nat.add_lt_add_left (List.mem_range.mp bounded) before.scopes.size

/-- The semantic output of a choice. Parent activation need not be Boolean for
this local result; the actual equations imply it whenever the choice is valid. -/
structure ChoiceSound (before after : State F) (parent : ScopeId)
    (children : List ScopeId) (assignment : Witness → F) : Prop where
  boolean : ∀ i : Fin children.length,
    (after.activation children[i]).denote assignment = 0 ∨
      (after.activation children[i]).denote assignment = 1
  exclusive : ∀ i j : Fin children.length, i ≠ j →
    (after.activation children[i]).denote assignment * (after.activation children[j]).denote assignment = 0
  coverage : ∑ i : Fin children.length, (after.activation children[i]).denote assignment =
    (before.activation parent).denote assignment

theorem choice_total_denote (before : State F) (count : Nat) (assignment : Witness → F) :
    ((choiceSelectors before count).foldl Polynomial.add (.const 0)).denote assignment =
      ∑ i : Fin count, assignment (before.roles.size + i) := by
  change Scalar.Circuit.ArithExpr.denote assignment _ = _
  rw [Scalar.Circuit.ArithExpr.denote_foldl_add]
  simp only [Scalar.Circuit.ArithExpr.denote, zero_add, choiceSelectors, List.map_map]
  rw [← List.ofFn_getElem_eq_map]
  simp only [List.length_range, List.getElem_range, Circuit.ArithExpr.denote,
    Scalar.Circuit.ArithExpr.denote]
  exact Fin.sum_ofFn _

theorem choice_sound {parent count : Nat} {children : List ScopeId} {before after : State F}
    (compiled : choice parent count before = .ok (children, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (valid : after.Valid rom calls assignment)
    (root : (before.activation 0).denote assignment = 1) :
    before.Valid rom calls assignment ∧ ChoiceSound before after parent children assignment := by
  have oldValid := valid.of_extends (choice_extends compiled)
  obtain ⟨enclosing, found, rfl, rfl⟩ := choice_eq compiled
  let after := choiceState before parent enclosing count
  have rootBound : 0 < before.scopes.size := by
    by_contra absent
    have empty : before.scopes[0]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
    simp [State.activation, empty, Scalar.Circuit.ArithExpr.denote] at root
  have global : (after.activation 0).denote assignment = 1 := by
    rw [choiceState_activation rootBound]
    exact root
  have imposed (polynomial : Polynomial F)
      (member : (⟨0, polynomial⟩ : Equation F) ∈ choiceEquations before enclosing count) :
      polynomial.denote assignment = 0 := by
    have satisfied := valid.1 ⟨0, polynomial⟩ (by simp [choiceState, member])
    change (after.activation 0).denote assignment * polynomial.denote assignment = 0 at satisfied
    simpa [global] using satisfied
  have bool (i : Nat) (bounded : i < count) :
      assignment (before.roles.size + i) * (assignment (before.roles.size + i) - 1) = 0 := by
    apply imposed (.mul (.var (before.roles.size + i)) (.sub (.var (before.roles.size + i)) (.const 1)))
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨i, List.mem_range.mpr bounded, by simp⟩
  have pair (i j : Nat) (iBound : i < count) (less : j < i) :
      assignment (before.roles.size + i) * assignment (before.roles.size + j) = 0 := by
    apply imposed (.mul (.var (before.roles.size + i)) (.var (before.roles.size + j)))
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨i, List.mem_range.mpr iBound, by simp [less]⟩
  have cover := imposed (.sub ((choiceSelectors before count).foldl Polynomial.add (.const 0))
    enclosing.activation) (by simp [choiceEquations])
  change ((choiceSelectors before count).foldl Polynomial.add (.const 0)).denote assignment -
    enclosing.activation.denote assignment = 0 at cover
  rw [choice_total_denote] at cover
  refine ⟨oldValid, ⟨?_, ?_, ?_⟩⟩
  · intro i
    simpa only [Fin.getElem_fin, choiceChildren_getElem, choiceState_child (by simpa using i.isLt),
      Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using (selector_boolean _).mp (bool i (by simpa using i.isLt))
  · intro i j different
    simp only [Fin.getElem_fin, choiceChildren_getElem, choiceState_child (by simpa using i.isLt),
      choiceState_child (by simpa using j.isLt), Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote]
    have distinct : i.val ≠ j.val := fun same => different (Fin.ext same)
    rcases lt_or_gt_of_ne distinct with less | greater
    · rw [mul_comm]
      exact pair j i (by simpa using j.isLt) less
    · exact pair i j (by simpa using i.isLt) greater
  · have pointwise (i : Fin (choiceChildren before count).length) :
        (choiceState before parent enclosing count).activation (before.scopes.size + i) =
          .var (before.roles.size + i) := choiceState_child (by simpa using i.isLt)
    simp only [Fin.getElem_fin, choiceChildren_getElem]
    simp_rw [pointwise]
    simp only [Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote]
    rw [Fin.sum_univ_eq_sum_range (fun i => assignment (before.roles.size + i)) (choiceChildren before count).length]
    rw [Fin.sum_univ_eq_sum_range (fun i => assignment (before.roles.size + i)) count] at cover
    simpa [State.activation, found, Circuit.ArithExpr.denote] using sub_eq_zero.mp cover

theorem ChoiceSound.active {before after : State F} {parent : ScopeId} {children : List ScopeId}
    {assignment : Witness → F} (sound : ChoiceSound before after parent children assignment)
    (active : (before.activation parent).denote assignment = 1) :
    ∃! i : Fin children.length, (after.activation children[i]).denote assignment = 1 := by
  apply selector_exactly_one _ _ sound.exclusive (sound.coverage.trans active)
  intro i
  exact (selector_boolean _).mpr (sound.boolean i)

theorem ChoiceSound.inactive {before after : State F} {parent : ScopeId} {children : List ScopeId}
    {assignment : Witness → F} (sound : ChoiceSound before after parent children assignment)
    (inactive : (before.activation parent).denote assignment = 0) :
    ∀ i : Fin children.length, (after.activation children[i]).denote assignment = 0 :=
  selector_inactive _ sound.exclusive (sound.coverage.trans inactive)

theorem choice_active {parent count : Nat} {children : List ScopeId} {before after : State F}
    (compiled : choice parent count before = .ok (children, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (valid : after.Valid rom calls assignment)
    (root : (before.activation 0).denote assignment = 1)
    (active : (before.activation parent).denote assignment = 1) :
    ∃ branch ∈ children, (after.activation branch).denote assignment = 1 := by
  obtain ⟨i, selected, _⟩ := (choice_sound compiled valid root).2.active active
  exact ⟨children[i], List.getElem_mem i.isLt, selected⟩

end Aiur.Optimized.Compiler
