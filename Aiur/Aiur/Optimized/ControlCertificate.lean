import Aiur.Optimized.AliasCertificate
import Aiur.Optimized.BranchFacts
import Aiur.Optimized.EquationIndex
import Mathlib.Algebra.BigOperators.Fin

namespace Aiur.Optimized.Control

variable {F : Type} [Field F] [DecidableEq F]

/-- A polynomial is zero either by simplification or by an actual global
equation. The choice metadata by itself imposes no semantic restrictions. -/
def ZeroEquation (chip : ScopedChip F) (polynomial : Polynomial F) : Prop :=
  Polynomial.Identical polynomial (.const 0) ∨
  ∃ equation ∈ chip.equations.toList, equation.scope = 0 ∧
    Polynomial.Identical equation.polynomial polynomial

instance (chip : ScopedChip F) (polynomial : Polynomial F) : Decidable (ZeroEquation chip polynomial) := by
  unfold ZeroEquation
  infer_instance

def Choice.total (chip : ScopedChip F) (choice : Aiur.Optimized.Choice) : Polynomial F :=
  choice.children.foldl (fun sum child => .add sum (chip.activation child)) (.const 0)

def Choice.Checked (chip : ScopedChip F) (choice : Aiur.Optimized.Choice) : Prop :=
  ZeroEquation chip (.sub (Choice.total chip choice) (chip.activation choice.parent)) ∧
  ∀ i j : Fin choice.children.length, j < i →
    ZeroEquation chip (.mul (chip.activation choice.children[i]) (chip.activation choice.children[j]))

instance (chip : ScopedChip F) (choice : Aiur.Optimized.Choice) : Decidable (Choice.Checked chip choice) := by
  unfold Choice.Checked
  infer_instance

def ParentChecked (chip : ScopedChip F) (id : ScopeId) : Prop :=
  match chip.scopes[id]? with
  | none => False
  | some scope =>
    match scope.path.getLast? with
    | none => True
    | some (choiceId, arm) =>
      match chip.choices[choiceId]? with
      | none => False
      | some choice =>
        match chip.scopes[choice.parent]? with
        | none => False
        | some parent => choice.children[arm]? = some id ∧ choice.parent < id ∧
            scope.path = parent.path ++ [(choiceId, arm)]

instance (chip : ScopedChip F) (id : ScopeId) : Decidable (ParentChecked chip id) := by
  unfold ParentChecked
  split <;> (try infer_instance)
  split <;> (try infer_instance)
  split <;> (try infer_instance)
  split <;> infer_instance

def Certificate (chip : ScopedChip F) : Prop :=
  Polynomial.Identical (chip.activation 0) (.const 1) ∧
  (∀ choice ∈ chip.choices.toList, Choice.Checked chip choice) ∧
  ∀ id ∈ List.range chip.scopes.size, ParentChecked chip id

open EquationIndex (expressionKey)

def globalNormalForms (chip : ScopedChip F) : List (Polynomial F) :=
  (chip.equations.toList.filter (fun eq => eq.scope == 0)).map
    (fun eq => eq.polynomial.normalForm)

theorem zeroEquation_iff_indexed (chip : ScopedChip F) (polynomial : Polynomial F) :
    ZeroEquation chip polynomial ↔
      polynomial.normalForm = (.const 0 : Polynomial F) ∨
      polynomial.normalForm ∈
        (Index.build expressionKey (globalNormalForms chip)).getD
          (expressionKey polynomial.normalForm) [] := by
  rw [Index.mem_build]
  simp only [ZeroEquation, Polynomial.Identical, globalNormalForms,
    Polynomial.normalForm, Polynomial.simplify, List.mem_map, List.mem_filter, beq_iff_eq]
  aesop

set_option synthInstance.maxSize 4096 in
/-- Normalize the actual global equations once, then use indexed membership
to check coverage and exclusion. The proposition being decided is unchanged. -/
instance (chip : ScopedChip F) : Decidable (Certificate chip) := by
  letI : BEq (Polynomial F) := instBEqOfDecidableEq
  let index := Index.build expressionKey (globalNormalForms chip)
  letI (polynomial : Polynomial F) : Decidable (ZeroEquation chip polynomial) :=
    decidable_of_iff
      (polynomial.normalForm = (.const 0 : Polynomial F) ∨
        polynomial.normalForm ∈ index.getD (expressionKey polynomial.normalForm) [])
      (zeroEquation_iff_indexed chip polynomial).symm
  unfold Certificate Choice.Checked
  infer_instance

def ActivePath (chip : ScopedChip F) (assignment : Witness → F) (path : Path) : Prop :=
  ∀ tag ∈ path, ∃ choice, chip.choices[tag.1]? = some choice ∧
    ∃ child, choice.children[tag.2]? = some child ∧ (chip.activation child).denote assignment ≠ 0

namespace Certificate

variable {chip : ScopedChip F} {rom : WireROM F} {assignment : Witness → F}

theorem zero (checked : Certificate chip) (valid : chip.ValidAssignment rom assignment)
    {polynomial : Polynomial F} (equation : ZeroEquation chip polynomial) : polynomial.denote assignment = 0 := by
  rcases equation with zero | ⟨equation, member, scope, same⟩
  · exact zero.denote assignment
  · have satisfied := valid.1 equation member
    rw [scope, checked.1.denote, same.denote] at satisfied
    simpa only [Scalar.Circuit.ArithExpr.denote, one_mul] using satisfied

theorem exclusive (checked : Certificate chip) (valid : chip.ValidAssignment rom assignment)
    {choice : Aiur.Optimized.Choice} (member : choice ∈ chip.choices.toList)
    (i j : Fin choice.children.length) (different : i ≠ j) :
    (chip.activation choice.children[i]).denote assignment *
      (chip.activation choice.children[j]).denote assignment = 0 := by
  rcases lt_or_gt_of_ne different with less | greater
  · simpa only [Scalar.Circuit.ArithExpr.denote, mul_comm] using
      checked.zero valid ((checked.2.1 choice member).2 j i less)
  · exact checked.zero valid ((checked.2.1 choice member).2 i j greater)

private theorem total_denote (choice : Aiur.Optimized.Choice) :
    (Choice.total chip choice).denote assignment =
      ∑ i : Fin choice.children.length, (chip.activation choice.children[i]).denote assignment := by
  have fold (children : List ScopeId) (start : Polynomial F) :
      (children.foldl (fun sum child => Polynomial.add sum (chip.activation child)) start).denote assignment =
        start.denote assignment + (children.map (fun child => (chip.activation child).denote assignment)).sum := by
    induction children generalizing start with
    | nil => simp
    | cons child children ih => simp [ih, Scalar.Circuit.ArithExpr.denote, add_assoc]
  unfold Choice.total
  change Scalar.Circuit.ArithExpr.denote assignment _ = _
  rw [fold]
  simp only [Scalar.Circuit.ArithExpr.denote, zero_add]
  rw [← List.ofFn_getElem_eq_map]
  exact Fin.sum_ofFn _

theorem parent_active (checked : Certificate chip) (valid : chip.ValidAssignment rom assignment)
    {choice : Aiur.Optimized.Choice} (member : choice ∈ chip.choices.toList)
    (i : Fin choice.children.length) (active : (chip.activation choice.children[i]).denote assignment ≠ 0) :
    (chip.activation choice.parent).denote assignment ≠ 0 := by
  have coverage := checked.zero valid (checked.2.1 choice member).1
  change (Choice.total chip choice).denote assignment - (chip.activation choice.parent).denote assignment = 0 at coverage
  have sum := sub_eq_zero.mp coverage
  rw [total_denote] at sum
  rw [← sum, exclusive_sum _ (checked.exclusive valid member) active]
  exact active

/-- Active descendants force every branch on their recorded path to be active.
This follows from checked coverage/exclusion equations, not from path labels. -/
theorem activePath (checked : Certificate chip) (valid : chip.ValidAssignment rom assignment)
    {id : ScopeId} {scope : Scope F} (found : chip.scopes[id]? = some scope)
    (active : (chip.activation id).denote assignment ≠ 0) : ActivePath chip assignment scope.path := by
  have prove (id : ScopeId) : ∀ scope, chip.scopes[id]? = some scope →
      (chip.activation id).denote assignment ≠ 0 → ActivePath chip assignment scope.path := by
    induction id using Nat.strong_induction_on with
    | h id ih =>
      intro scope found active
      have step := checked.2.2 id (List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1)
      unfold ParentChecked at step
      simp only [found] at step
      cases last : scope.path.getLast? with
      | none => simp [ActivePath, List.getLast?_eq_none_iff.mp last]
      | some tag =>
        simp only [last] at step
        cases choiceFound : chip.choices[tag.1]? with
        | none => simp [choiceFound] at step
        | some choice =>
          simp only [choiceFound] at step
          cases parentFound : chip.scopes[choice.parent]? with
          | none => simp [parentFound] at step
          | some parent =>
            simp only [parentFound] at step
            obtain ⟨child, earlier, path⟩ := step
            obtain ⟨bounded, childEq⟩ := List.getElem?_eq_some_iff.mp child
            have parentActive := checked.parent_active valid
              (by simpa using Array.mem_of_getElem? choiceFound) ⟨tag.2, bounded⟩ (by simpa [childEq] using active)
            have ancestor := ih choice.parent earlier parent parentFound parentActive
            intro item member
            rw [path] at member
            rcases List.mem_append.mp member with previous | lastItem
            · exact ancestor item previous
            · have same := List.mem_singleton.mp lastItem
              subst item
              exact ⟨choice, choiceFound, id, child, active⟩
  exact prove id scope found active

theorem paths_exclusive (checked : Certificate chip) (valid : chip.ValidAssignment rom assignment)
    {left right : Path} (different : left.exclusive right = true)
    (leftActive : ActivePath chip assignment left) (rightActive : ActivePath chip assignment right) : False := by
  obtain ⟨⟨choiceId, arm⟩, leftMem, rest⟩ := List.any_eq_true.mp different
  obtain ⟨⟨other, branch⟩, rightMem, condition⟩ := List.any_eq_true.mp rest
  obtain ⟨same, distinct⟩ := Bool.and_eq_true_iff.mp condition
  have same : choiceId = other := beq_iff_eq.mp same
  have distinct : arm ≠ branch := by simpa using distinct
  subst other
  obtain ⟨choice, found, a, aFound, aActive⟩ := leftActive _ leftMem
  obtain ⟨otherChoice, otherFound, b, bFound, bActive⟩ := rightActive _ rightMem
  have equal : choice = otherChoice := Option.some.inj (found.symm.trans otherFound)
  subst otherChoice
  obtain ⟨aBound, aEq⟩ := List.getElem?_eq_some_iff.mp aFound
  obtain ⟨bBound, bEq⟩ := List.getElem?_eq_some_iff.mp bFound
  have zero := checked.exclusive valid (by simpa using Array.mem_of_getElem? found)
    ⟨arm, aBound⟩ ⟨branch, bBound⟩ (by simpa using distinct)
  simp only [Fin.getElem_fin, aEq, bEq] at zero
  exact (mul_ne_zero aActive bActive) zero

end Certificate
end Aiur.Optimized.Control
