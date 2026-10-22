import Aiur.Optimized.DegreeCertificate

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

theorem ScopedChip.substitute_activation (chip : ScopedChip F) (replace : Witness → Polynomial F)
    (assignment : Witness → F) (scope : ScopeId) :
    ((chip.substitute replace).activation scope).denote assignment =
      (chip.activation scope).denote (fun id => (replace id).denote assignment) := by
  cases found : chip.scopes[scope]? <;>
    simp [ScopedChip.substitute, ScopedChip.activation, found, Polynomial.denote_simplify,
      Polynomial.denote_subst, Scalar.Circuit.ArithExpr.denote]

theorem ScopedChip.substitute_validAssignment (chip : ScopedChip F) (replace : Witness → Polynomial F)
    (rom : WireROM F) (assignment : Witness → F) :
    (chip.substitute replace).ValidAssignment rom assignment ↔
      chip.ValidAssignment rom (fun id => (replace id).denote assignment) := by
  unfold ScopedChip.ValidAssignment
  change (∀ equation ∈ (chip.equations.map _).toList, _) ∧
    (∀ cell ∈ (chip.cells.map _).toList, _) ↔ _
  simp only [Array.toList_map, List.forall_mem_map, ScopedChip.substitute_activation,
    Polynomial.denote_simplify, Polynomial.denote_subst, WireValue.map_map, Function.comp_def]

def ScopedChip.fixedInterface (chip : ScopedChip F) (replace : Witness → Polynomial F) : Prop :=
  ∀ id ∈ chip.inputs.flatMap WireValue.words ++ chip.output.words ++
    chip.calls.toList.flatMap (fun call => call.result.words), replace id = .var id

instance (chip : ScopedChip F) (replace : Witness → Polynomial F) :
    Decidable (chip.fixedInterface replace) := by unfold ScopedChip.fixedInterface; infer_instance

theorem ScopedChip.substitute_conclusion (chip : ScopedChip F) (replace : Witness → Polynomial F)
    (fixed : chip.fixedInterface replace) (assignment : Witness → F) :
    (chip.substitute replace).conclusion assignment =
      chip.conclusion (fun id => (replace id).denote assignment) := by
  have fixedInput (value : WireValue Witness) (member : value ∈ chip.inputs) :
      value.map assignment = value.map (fun id => (replace id).denote assignment) := by
    apply WireValue.map_congr
    intro id present
    rw [fixed id (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨value, member, present⟩)))]
    rfl
  have fixedOutput : chip.output.map assignment = chip.output.map (fun id => (replace id).denote assignment) := by
    apply WireValue.map_congr
    intro id present
    rw [fixed id (by simp only [List.mem_append]; exact Or.inl (Or.inr present))]
    rfl
  simp only [ScopedChip.conclusion, ScopedChip.substitute]
  rw [List.map_congr_left fixedInput, fixedOutput]

theorem ScopedChip.substitute_premises (chip : ScopedChip F) (replace : Witness → Polynomial F)
    (fixed : chip.fixedInterface replace) (assignment : Witness → F) :
    (chip.substitute replace).premises assignment =
      chip.premises (fun id => (replace id).denote assignment) := by
  unfold ScopedChip.premises
  change (chip.calls.map _).toList.filterMap _ = _
  simp only [Array.toList_map, List.filterMap_map]
  apply List.filterMap_congr
  intro call member
  simp only [Function.comp_def, ScopedChip.substitute_activation]
  split
  · congr 1
    have fixedResult : call.result.map assignment =
        call.result.map (fun id => (replace id).denote assignment) := by
      apply WireValue.map_congr
      intro id present
      rw [fixed id (List.mem_append_right _ (List.mem_flatMap.mpr ⟨call, member, present⟩))]
      rfl
    simp only [Call.message, List.map_map, WireValue.map_map, Function.comp_def,
      Polynomial.denote_simplify, Polynomial.denote_subst, fixedResult]
  · rfl

namespace Alias

def Certificate (chip : ScopedChip F) (values : Array (Polynomial F)) : Prop :=
  values.size = chip.roles.size ∧ chip.fixedInterface (Degree.replacement values) ∧
  ∀ id ∈ List.range chip.roles.size,
    Degree.replacement values id = .var id ∨
      match chip.aliases[id]?.getD none with
      | none => False
      | some expression =>
        (∀ other ∈ expression.vars, id < other ∧ other < chip.roles.size) ∧
        Polynomial.Identical (expression.subst (Degree.replacement values)) (Degree.replacement values id) ∧
        ∃ equation ∈ chip.equations.toList,
          Polynomial.Identical (chip.activation equation.scope) (.const 1) ∧
          Polynomial.Identical equation.polynomial (.sub expression (.var id))

instance (chip : ScopedChip F) (values : Array (Polynomial F)) : Decidable (Certificate chip values) := by
  unfold Certificate
  refine @instDecidableAnd _ _ inferInstance ?_
  refine @instDecidableAnd _ _ inferInstance ?_
  refine @List.decidableBAll _ _ ?_ _
  intro id
  refine @instDecidableOr _ _ inferInstance ?_
  split <;> infer_instance

namespace Certificate

variable {chip : ScopedChip F} {values : Array (Polynomial F)}

/-- Every eliminated selector is determined by an equation in the input chip.
Forward references decrease the remaining suffix length, ruling out cycles. -/
theorem assignment (checked : Certificate chip values) {rom : WireROM F} {a : Witness → F}
    (valid : chip.ValidAssignment rom a) : (fun id => (Degree.replacement values id).denote a) = a := by
  have prove (fuel : Nat) : ∀ id, chip.roles.size - id < fuel →
      a id = (Degree.replacement values id).denote a := by
    induction fuel with
    | zero => intro id bound; omega
    | succ fuel ih =>
      intro id bound
      by_cases bounded : id < chip.roles.size
      · rcases checked.2.2 id (List.mem_range.mpr bounded) with unchanged | defined
        · rw [unchanged]; rfl
        · cases found : chip.aliases[id]?.getD none with
          | none => simp only [found] at defined
          | some expression =>
            rw [found] at defined
            obtain ⟨earlier, expanded, equation, member, global, definition⟩ := defined
            have equation := valid.1 equation member
            rw [global.denote, definition.denote] at equation
            change 1 * (expression.denote a - a id) = 0 at equation
            have equality : a id = expression.denote a := (sub_eq_zero.mp (by simpa using equation)).symm
            have expand : expression.denote a = (expression.subst (Degree.replacement values)).denote a := by
              rw [Polynomial.denote_subst]
              apply Polynomial.denote_congr
              intro other member
              have order := earlier other member
              exact ih other (by omega)
            exact equality.trans (expand.trans (expanded.denote a))
      · have sized := checked.1
        have absent : values[id]? = none := Array.getElem?_eq_none (by omega)
        simp [Degree.replacement, absent, Scalar.Circuit.ArithExpr.denote]
  funext id
  exact (prove (chip.roles.size + 1) id (by omega)).symm

theorem equivalent (checked : Certificate chip values) :
    chip.Equivalent (chip.substitute (Degree.replacement values)) := by
  constructor
  · intro rom a valid
    refine ⟨a, ?_, ?_, ?_⟩
    · rw [ScopedChip.substitute_validAssignment, checked.assignment valid]
      exact valid
    · rw [chip.substitute_conclusion _ checked.2.1, checked.assignment valid]
    · rw [chip.substitute_premises _ checked.2.1, checked.assignment valid]
  · intro rom a valid
    exact ⟨_, (chip.substitute_validAssignment _ _ _).mp valid,
      (chip.substitute_conclusion _ checked.2.1 a).symm,
      (chip.substitute_premises _ checked.2.1 a).symm⟩

end Certificate

def checkedResolve (chip : ScopedChip F) : Except String (Degree.Checked chip) := do
  let values ← resolveAliasValues chip
  if checked : Certificate chip values then
    return ⟨chip.substitute (Degree.replacement values), checked.equivalent, rfl, rfl, rfl⟩
  else throw s!"invalid selector-elimination certificate in {chip.name}"

end Alias
end Aiur.Optimized
