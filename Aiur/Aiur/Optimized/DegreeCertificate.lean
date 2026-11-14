import Aiur.Optimized.ScopedSemantics
import Aiur.Optimized.PolynomialIdentity
import Aiur.Optimized.EquationIndex

namespace Aiur.Optimized.Degree

variable {F : Type} [Field F] [DecidableEq F]

abbrev Definition (F : Type) := ScopeId × Polynomial F × Witness

def replacement (values : Array (Polynomial F)) (id : Witness) : Polynomial F :=
  values[id]?.getD (.var id)

def expand (width : Nat) (definitions : List (Definition F)) : Array (Polynomial F) := Id.run do
  let mut values := (List.range width).toArray.map Polynomial.var
  for (_, expression, id) in definitions.reverse do
    values := values.set! id (expression.subst (replacement values)).simplify
  return values

def Supported (base : Nat) (definitions : List (Definition F)) (scope : ScopeId) (polynomial : Polynomial F) : Prop :=
  ∀ id ∈ polynomial.vars, id < base ∨ ∃ definition ∈ definitions, definition.2.2 = id ∧ definition.1 = scope

instance (base : Nat) (definitions : List (Definition F)) (scope : ScopeId) (polynomial : Polynomial F) :
    Decidable (Supported base definitions scope polynomial) := by unfold Supported; infer_instance

abbrev NormalCall (F : Type) :=
  ScopeId × String × List (WireValue (Polynomial F)) × WireValue Witness
abbrev NormalCell (F : Type) := ScopeId × Polynomial F × WireValue (Polynomial F)

def normalCall (replace : Witness → Polynomial F) (call : Call F) : NormalCall F :=
  (call.scope, call.channel, call.args.map (WireValue.map (fun p => (p.subst replace).normalForm)), call.result)

def normalCell (replace : Witness → Polynomial F) (cell : Cell F) : NormalCell F :=
  (cell.scope, (cell.address.subst replace).normalForm,
    cell.value.map (fun p => (p.subst replace).normalForm))

def NormalCall.message (call : NormalCall F) (assignment : Witness → F) : Circuit.Message F :=
  ⟨call.2.1, call.2.2.1.map (WireValue.map (Circuit.ArithExpr.denote assignment)),
    call.2.2.2.map assignment⟩

def NormalCell.entry (cell : NormalCell F) (assignment : Witness → F) : F × WireValue F :=
  (cell.2.1.denote assignment, cell.2.2.map (Circuit.ArithExpr.denote assignment))

@[simp] theorem normalCall_id (call : Call F) (assignment : Witness → F) :
    (normalCall Polynomial.var call).message assignment = call.message assignment := by
  simp [normalCall, NormalCall.message, Call.message, List.map_map, WireValue.map_map,
    Function.comp_def, Polynomial.eval_normalForm, Polynomial.denote_subst,
    Scalar.Circuit.ArithExpr.denote]

@[simp] theorem normalCell_id (cell : Cell F) (assignment : Witness → F) :
    (normalCell Polynomial.var cell).entry assignment =
      (cell.address.denote assignment, cell.value.map (Circuit.ArithExpr.denote assignment)) := by
  simp [normalCell, NormalCell.entry, WireValue.map_map, Function.comp_def,
    Polynomial.eval_normalForm, Polynomial.denote_subst, Scalar.Circuit.ArithExpr.denote]

private theorem filterMap_of_map_eq {α β γ δ : Type} {xs : List α} {ys : List β}
    {f : α → γ} {g : β → γ} {left : α → Option δ} {right : β → Option δ}
    (same : xs.map f = ys.map g)
    (pointwise : ∀ x ∈ xs, ∀ y ∈ ys, f x = g y → left x = right y) :
    xs.filterMap left = ys.filterMap right := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at same
      | cons y ys =>
          obtain ⟨head, tail⟩ := List.cons.inj same
          have rest := ih tail (fun a ha b hb => pointwise a (by simp [ha]) b (by simp [hb]))
          simp only [List.filterMap_cons, pointwise x (by simp) y (by simp) head, rest]

/-- The finite certificate records total-expression definitions and checks the
two scoped equation systems after eliminating precisely those fresh columns. -/
def Certificate (source target : ScopedChip F) (definitions : List (Definition F))
    (values : Array (Polynomial F)) : Prop :=
  let replace := replacement values
  let base := source.roles.size
  target.name = source.name ∧ target.inputs = source.inputs ∧ target.output = source.output ∧
  target.scopes = source.scopes ∧
  (∀ id ∈ List.range base, replace id = .var id) ∧
  (∀ id ∈ source.inputs.flatMap WireValue.words ++ source.output.words, id < base) ∧
  (∀ scope ∈ source.scopes.toList, ∀ id ∈ scope.activation.vars, id < base) ∧
  (∀ definition ∈ definitions,
    Supported base definitions definition.1 definition.2.1 ∧
    (∀ id ∈ definition.2.1.vars, id < definition.2.2) ∧
    Polynomial.Identical (definition.2.1.subst replace) (replace definition.2.2) ∧
    ∃ equation ∈ target.equations.toList, equation.scope = definition.1 ∧
      Polynomial.Identical equation.polynomial (.sub (.var definition.2.2) definition.2.1)) ∧
  (∀ equation ∈ source.equations.toList,
    Polynomial.Identical equation.polynomial (.const 0) ∨
    ∃ translated ∈ target.equations.toList, translated.scope = equation.scope ∧
      Supported base definitions translated.scope translated.polynomial ∧
      Polynomial.Identical (translated.polynomial.subst replace) equation.polynomial) ∧
  (∀ equation ∈ target.equations.toList,
    Polynomial.Identical (equation.polynomial.subst replace) (.const 0) ∨
    ∃ original ∈ source.equations.toList, original.scope = equation.scope ∧
      Polynomial.Identical (equation.polynomial.subst replace) original.polynomial) ∧
  target.calls.toList.map (normalCall replace) = source.calls.toList.map (normalCall Polynomial.var) ∧
  (∀ call ∈ target.calls.toList,
    (∀ polynomial ∈ call.args.flatMap WireValue.words, Supported base definitions call.scope polynomial) ∧
    (∀ id ∈ call.result.words, id < base)) ∧
  target.cells.toList.map (normalCell replace) = source.cells.toList.map (normalCell Polynomial.var) ∧
  (∀ cell ∈ target.cells.toList, Supported base definitions cell.scope cell.address ∧
    ∀ polynomial ∈ cell.value.words, Supported base definitions cell.scope polynomial)

set_option synthInstance.maxSize 4096 in
instance (source target : ScopedChip F) (definitions : List (Definition F)) (values : Array (Polynomial F)) :
    Decidable (Certificate source target definitions values) := by
  letI : BEq (ScopeId × Polynomial F) := instBEqOfDecidableEq
  let replace := replacement values
  let targetRaw := EquationIndex.build target.equations.toList id
  let sourceRaw := EquationIndex.build source.equations.toList id
  let supported := target.equations.toList.filter fun eq =>
    decide (Supported source.roles.size definitions eq.scope eq.polynomial)
  let targetExpanded := EquationIndex.build supported (Polynomial.subst replace)
  letI (scope : ScopeId) (polynomial : Polynomial F) : Decidable
      (∃ equation ∈ target.equations.toList, equation.scope = scope ∧
        Polynomial.Identical equation.polynomial polynomial) :=
    decidable_of_iff
      ((scope, polynomial.normalForm) ∈
        targetRaw.getD (EquationIndex.key (scope, polynomial.normalForm)) [])
      (EquationIndex.member_build target.equations.toList id scope polynomial)
  letI (scope : ScopeId) (polynomial : Polynomial F) : Decidable
      (∃ equation ∈ source.equations.toList, equation.scope = scope ∧
        Polynomial.Identical polynomial equation.polynomial) :=
    decidable_of_iff
      ((scope, polynomial.normalForm) ∈
        sourceRaw.getD (EquationIndex.key (scope, polynomial.normalForm)) [])
      (by
        rw [EquationIndex.member_build]
        simp only [id_eq, Polynomial.Identical]
        exact exists_congr fun eq => and_congr_right fun _ => and_congr_right fun _ => eq_comm)
  letI (scope : ScopeId) (polynomial : Polynomial F) : Decidable
      (∃ equation ∈ target.equations.toList, equation.scope = scope ∧
        Supported source.roles.size definitions equation.scope equation.polynomial ∧
        Polynomial.Identical (equation.polynomial.subst replace) polynomial) :=
    decidable_of_iff
      ((scope, polynomial.normalForm) ∈
        targetExpanded.getD (EquationIndex.key (scope, polynomial.normalForm)) [])
      (by
        rw [EquationIndex.member_build]
        simp only [supported, List.mem_filter, decide_eq_true_eq]
        aesop)
  unfold Certificate
  dsimp only
  infer_instance

namespace Certificate

variable {source target : ScopedChip F} {definitions : List (Definition F)} {values : Array (Polynomial F)}

theorem scopes (checked : Certificate source target definitions values) (scope : ScopeId) :
    target.activation scope = source.activation scope := by
  simp only [ScopedChip.activation, checked.2.2.2.1]

theorem original (checked : Certificate source target definitions values) {id : Witness}
    (bounded : id < source.roles.size) : replacement values id = .var id :=
  checked.2.2.2.2.1 id (List.mem_range.mpr bounded)

theorem activation_bounded (checked : Certificate source target definitions values) (scope : ScopeId) :
    ∀ id ∈ (source.activation scope).vars, id < source.roles.size := by
  cases found : source.scopes[scope]? with
  | none => simp [ScopedChip.activation, found, Polynomial.vars]
  | some value =>
      simpa only [ScopedChip.activation, found, Option.map_some, Option.getD_some] using
        checked.2.2.2.2.2.2.1 value (by simpa using Array.mem_of_getElem? found)

theorem activation_extend (checked : Certificate source target definitions values)
    (assignment : Witness → F) (scope : ScopeId) :
    (target.activation scope).denote (fun id => (replacement values id).denote assignment) =
      (source.activation scope).denote assignment := by
  rw [checked.scopes]
  apply Polynomial.denote_congr
  intro id member
  rw [checked.original (checked.activation_bounded scope id member)]
  rfl

/-- Active defining equations identify each fresh column with its expansion.
The strict ordering check prevents a definition from justifying itself. -/
theorem definition_sound (checked : Certificate source target definitions values)
    {rom : WireROM F} {assignment : Witness → F} (valid : target.ValidAssignment rom assignment)
    {definition : Definition F} (member : definition ∈ definitions)
    (active : (source.activation definition.1).denote assignment ≠ 0) :
    assignment definition.2.2 = (replacement values definition.2.2).denote assignment := by
  have prove (id : Witness) : ∀ definition ∈ definitions, definition.2.2 = id →
      (source.activation definition.1).denote assignment ≠ 0 →
      assignment id = (replacement values id).denote assignment := by
    induction id using Nat.strong_induction_on with
    | h id ih =>
      intro definition member same active
      obtain ⟨support, earlier, expansion, equation, present, owner, polynomial⟩ :=
        checked.2.2.2.2.2.2.2.1 definition member
      have zero := valid.1 equation present
      rw [checked.scopes, owner, polynomial.denote] at zero
      change (source.activation definition.1).denote assignment *
        (assignment definition.2.2 - definition.2.1.denote assignment) = 0 at zero
      have equal := sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left active)
      have substitute : definition.2.1.denote assignment =
          (definition.2.1.subst (replacement values)).denote assignment := by
        rw [Polynomial.denote_subst]
        apply Polynomial.denote_congr
        intro other used
        rcases support other used with old | ⟨previous, previousMem, index, scope⟩
        · rw [checked.original old]; rfl
        · exact ih other (same ▸ earlier other used) previous previousMem index (scope ▸ active)
      exact same ▸ (equal.trans (substitute.trans (expansion.denote assignment)))
  exact prove definition.2.2 definition member rfl active

theorem expression_sound (checked : Certificate source target definitions values)
    {rom : WireROM F} {assignment : Witness → F} (valid : target.ValidAssignment rom assignment)
    {scope : ScopeId} {polynomial : Polynomial F}
    (support : Supported source.roles.size definitions scope polynomial)
    (active : (source.activation scope).denote assignment ≠ 0) :
    polynomial.denote assignment = (polynomial.subst (replacement values)).denote assignment := by
  rw [Polynomial.denote_subst]
  apply Polynomial.denote_congr
  intro id member
  rcases support id member with old | ⟨definition, present, index, owner⟩
  · rw [checked.original old]; rfl
  · simpa only [index] using checked.definition_sound valid present (owner ▸ active)

theorem conclusion_extend (checked : Certificate source target definitions values)
    (assignment : Witness → F) :
    target.conclusion (fun id => (replacement values id).denote assignment) = source.conclusion assignment := by
  have bound := checked.2.2.2.2.2.1
  have inputs : source.inputs.map (WireValue.map (fun id => (replacement values id).denote assignment)) =
      source.inputs.map (WireValue.map assignment) := by
    apply List.map_congr_left
    intro value member
    apply WireValue.map_congr
    intro id present
    rw [checked.original (bound id (List.mem_append_left _ (List.mem_flatMap.mpr ⟨value, member, present⟩)))]
    rfl
  have output : source.output.map (fun id => (replacement values id).denote assignment) =
      source.output.map assignment := by
    apply WireValue.map_congr
    intro id present
    rw [checked.original (bound id (List.mem_append_right _ present))]
    rfl
  simp only [ScopedChip.conclusion, checked.1, checked.2.1, checked.2.2.1, inputs, output]

theorem conclusion_project (checked : Certificate source target definitions values)
    (assignment : Witness → F) : target.conclusion assignment = source.conclusion assignment := by
  simp only [ScopedChip.conclusion, checked.1, checked.2.1, checked.2.2.1]

theorem call_extend (checked : Certificate source target definitions values)
    (assignment : Witness → F) {call : Call F} (member : call ∈ target.calls.toList) :
    (normalCall (replacement values) call).message assignment =
      call.message (fun id => (replacement values id).denote assignment) := by
  have result : call.result.map assignment =
      call.result.map (fun id => (replacement values id).denote assignment) := by
    apply WireValue.map_congr
    intro id present
    rw [checked.original ((checked.2.2.2.2.2.2.2.2.2.2.2.1 call member).2 id present)]
    rfl
  simpa only [normalCall, NormalCall.message, Call.message, List.map_map, WireValue.map_map,
    Function.comp_def, Polynomial.eval_normalForm, Polynomial.denote_subst] using
      congrArg (fun result => Circuit.Message.mk call.channel
        (call.args.map (WireValue.map (Circuit.ArithExpr.denote
          (fun id => (replacement values id).denote assignment)))) result) result

theorem call_project (checked : Certificate source target definitions values)
    {rom : WireROM F} {assignment : Witness → F} (valid : target.ValidAssignment rom assignment)
    {call : Call F} (member : call ∈ target.calls.toList)
    (active : (source.activation call.scope).denote assignment = 1) :
    (normalCall (replacement values) call).message assignment = call.message assignment := by
  have args : call.args.map (WireValue.map (fun p => (p.subst (replacement values)).denote assignment)) =
      call.args.map (WireValue.map (Circuit.ArithExpr.denote assignment)) := by
    apply List.map_congr_left
    intro value present
    apply WireValue.map_congr
    intro polynomial used
    exact (checked.expression_sound valid
      ((checked.2.2.2.2.2.2.2.2.2.2.2.1 call member).1 polynomial
        (List.mem_flatMap.mpr ⟨value, present, used⟩)) (by rw [active]; exact one_ne_zero)).symm
  simpa only [normalCall, NormalCall.message, Call.message, List.map_map, WireValue.map_map,
    Function.comp_def, Polynomial.eval_normalForm] using
      congrArg (fun args => Circuit.Message.mk call.channel args (call.result.map assignment)) args

theorem premises_extend (checked : Certificate source target definitions values)
    (assignment : Witness → F) :
    target.premises (fun id => (replacement values id).denote assignment) = source.premises assignment := by
  apply filterMap_of_map_eq checked.2.2.2.2.2.2.2.2.2.2.1
  intro call member original _ same
  have scope : call.scope = original.scope := congrArg Prod.fst same
  have message := congrArg (fun c => NormalCall.message c assignment) same
  rw [checked.call_extend assignment member, normalCall_id] at message
  simp only [checked.activation_extend, scope, message]

theorem premises_project (checked : Certificate source target definitions values)
    {rom : WireROM F} {assignment : Witness → F} (valid : target.ValidAssignment rom assignment) :
    target.premises assignment = source.premises assignment := by
  apply filterMap_of_map_eq checked.2.2.2.2.2.2.2.2.2.2.1
  intro call member original _ same
  have scope : call.scope = original.scope := congrArg Prod.fst same
  by_cases active : (source.activation call.scope).denote assignment = 1
  · have message := congrArg (fun c => NormalCall.message c assignment) same
    rw [checked.call_project valid member active, normalCall_id] at message
    simp only [checked.scopes, ← scope, active, ↓reduceIte, message]
  · simp only [checked.scopes, ← scope, active, ↓reduceIte]

theorem cell_extend (cell : Cell F) (assignment : Witness → F) :
    (normalCell (replacement values) cell).entry assignment =
      (cell.address.denote (fun id => (replacement values id).denote assignment),
        cell.value.map (Circuit.ArithExpr.denote (fun id => (replacement values id).denote assignment))) := by
  simp [normalCell, NormalCell.entry, WireValue.map_map, Function.comp_def,
    Polynomial.eval_normalForm, Polynomial.denote_subst]

theorem cell_project (checked : Certificate source target definitions values)
    {rom : WireROM F} {assignment : Witness → F} (valid : target.ValidAssignment rom assignment)
    {cell : Cell F} (member : cell ∈ target.cells.toList)
    (active : (source.activation cell.scope).denote assignment = 1) :
    (normalCell (replacement values) cell).entry assignment =
      (cell.address.denote assignment, cell.value.map (Circuit.ArithExpr.denote assignment)) := by
  obtain ⟨address, payload⟩ := checked.2.2.2.2.2.2.2.2.2.2.2.2.2 cell member
  have nonzero : (source.activation cell.scope).denote assignment ≠ 0 := by rw [active]; exact one_ne_zero
  simp only [normalCell, NormalCell.entry, WireValue.map_map, Function.comp_def,
    Polynomial.eval_normalForm]
  rw [← checked.expression_sound valid address nonzero]
  congr 1
  exact WireValue.map_congr _ (fun p hp => (checked.expression_sound valid (payload p hp) nonzero).symm)

theorem valid_extend (checked : Certificate source target definitions values)
    {rom : WireROM F} {assignment : Witness → F} (valid : source.ValidAssignment rom assignment) :
    target.ValidAssignment rom (fun id => (replacement values id).denote assignment) := by
  constructor
  · intro equation member
    rw [checked.activation_extend, ← Polynomial.denote_subst]
    rcases checked.2.2.2.2.2.2.2.2.2.1 equation member with zero | ⟨original, present, scope, same⟩
    · rw [zero.denote]; simp [Scalar.Circuit.ArithExpr.denote]
    · rw [same.denote, ← scope]
      exact valid.1 original present
  · intro cell member active
    rw [checked.activation_extend] at active
    have cells := checked.2.2.2.2.2.2.2.2.2.2.2.2.1
    have present : normalCell (replacement values) cell ∈
        target.cells.toList.map (normalCell (replacement values)) := List.mem_map.mpr ⟨cell, member, rfl⟩
    rw [cells] at present
    obtain ⟨original, present, same⟩ := List.mem_map.mp present
    have scope : original.scope = cell.scope := congrArg Prod.fst same
    have entry := congrArg (fun c => NormalCell.entry c assignment) same
    rw [normalCell_id, cell_extend] at entry
    rw [← entry]
    exact valid.2 original present (scope ▸ active)

theorem valid_project (checked : Certificate source target definitions values)
    {rom : WireROM F} {assignment : Witness → F} (valid : target.ValidAssignment rom assignment) :
    source.ValidAssignment rom assignment := by
  constructor
  · intro equation member
    rcases checked.2.2.2.2.2.2.2.2.1 equation member with zero | ⟨translated, present, scope, support, same⟩
    · rw [zero.denote]; simp [Scalar.Circuit.ArithExpr.denote]
    · by_cases inactive : (source.activation equation.scope).denote assignment = 0
      · simp [inactive]
      · have eq := valid.1 translated present
        rw [checked.scopes, checked.expression_sound valid support (scope ▸ inactive), same.denote, scope] at eq
        exact eq
  · intro cell member active
    have cells := checked.2.2.2.2.2.2.2.2.2.2.2.2.1
    have present : normalCell Polynomial.var cell ∈
        source.cells.toList.map (normalCell Polynomial.var) := List.mem_map.mpr ⟨cell, member, rfl⟩
    rw [← cells] at present
    obtain ⟨translated, present, same⟩ := List.mem_map.mp present
    have scope : translated.scope = cell.scope := congrArg Prod.fst same
    have entry := congrArg (fun c => NormalCell.entry c assignment) same
    rw [checked.cell_project valid present (scope ▸ active), normalCell_id] at entry
    rw [← entry]
    exact valid.2 translated present (by rw [checked.scopes, scope]; exact active)

/-- A checked degree-reduction certificate gives both witness directions,
including the ordered list of call premises and all ROM obligations. -/
theorem equivalent (checked : Certificate source target definitions values) : source.Equivalent target := by
  constructor
  · intro rom assignment valid
    exact ⟨_, checked.valid_extend valid, checked.conclusion_extend assignment, checked.premises_extend assignment⟩
  · intro rom assignment valid
    exact ⟨_, checked.valid_project valid, (checked.conclusion_project assignment).symm,
      (checked.premises_project valid).symm⟩

end Certificate

structure Checked (source : ScopedChip F) where
  chip : ScopedChip F
  equivalent : source.Equivalent chip
  name_eq : chip.name = source.name
  inputs_eq : chip.inputs = source.inputs
  output_eq : chip.output = source.output

/-- Check the actual optimizer output; no correctness claim about its search
or cache heuristics is trusted by the certificate theorem. -/
def certify (source : ScopedChip F) (state : State F) : Except String (Checked source) := do
  let values := expand state.chip.roles.size state.cache
  if checked : Certificate source state.chip state.cache values then
    return ⟨state.chip, checked.equivalent, checked.1, checked.2.1, checked.2.2.1⟩
  else throw s!"invalid degree-reduction certificate in {source.name}"

def checkedBound (config : Config) (source : ScopedChip F) : Except String (Checked source) := do
  certify source (← boundState config source)

end Aiur.Optimized.Degree
