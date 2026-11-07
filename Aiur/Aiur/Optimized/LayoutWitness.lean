import Aiur.Optimized.ScopedSemantics

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

/-- Logical variables whose values matter in this assignment. Inactive
payloads are deliberately absent; all activation expressions remain relevant. -/
inductive ScopedChip.Relevant (chip : ScopedChip F) (assignment : Witness → F) : Witness → Prop
  | input {value id} : value ∈ chip.inputs → id ∈ value.words → chip.Relevant assignment id
  | output {id} : id ∈ chip.output.words → chip.Relevant assignment id
  | activation {scope id} : id ∈ (chip.activation scope).vars → chip.Relevant assignment id
  | equation {equation id} : equation ∈ chip.equations.toList →
      (chip.activation equation.scope).denote assignment ≠ 0 → id ∈ equation.polynomial.vars →
      chip.Relevant assignment id
  | callArgument {call value polynomial id} : call ∈ chip.calls.toList →
      (chip.activation call.scope).denote assignment = 1 → value ∈ call.args → polynomial ∈ value.words →
      id ∈ polynomial.vars → chip.Relevant assignment id
  | callResult {call id} : call ∈ chip.calls.toList →
      (chip.activation call.scope).denote assignment = 1 → id ∈ call.result.words → chip.Relevant assignment id
  | address {cell id} : cell ∈ chip.cells.toList → (chip.activation cell.scope).denote assignment = 1 →
      id ∈ cell.address.vars → chip.Relevant assignment id
  | payload {cell polynomial id} : cell ∈ chip.cells.toList → (chip.activation cell.scope).denote assignment = 1 →
      polynomial ∈ cell.value.words → id ∈ polynomial.vars → chip.Relevant assignment id

private theorem wire_map_congr {α β : Type} (value : WireValue α) {left right : α → β}
    (agree : ∀ word ∈ value.words, left word = right word) : value.map left = value.map right := by
  cases value
  simp only [WireValue.map, WireValue.mk.injEq, true_and]
  exact List.map_congr_left agree

namespace ScopedChip

variable {chip : ScopedChip F} {a b : Witness → F}

omit [DecidableEq F] in
theorem activation_agree (agree : ∀ id, chip.Relevant a id → a id = b id) (scope : ScopeId) :
    (chip.activation scope).denote a = (chip.activation scope).denote b :=
  Polynomial.denote_congr _ (fun _ member => agree _ (.activation member))

omit [DecidableEq F] in
theorem conclusion_agree (agree : ∀ id, chip.Relevant a id → a id = b id) :
    chip.conclusion a = chip.conclusion b := by
  have inputs : chip.inputs.map (WireValue.map a) = chip.inputs.map (WireValue.map b) := by
    apply List.map_congr_left
    intro value member
    exact wire_map_congr value (fun id present => agree id (.input member present))
  have output := wire_map_congr chip.output (fun id present => agree id (.output present))
  simp only [conclusion, inputs, output]

omit [DecidableEq F] in
theorem call_agree (agree : ∀ id, chip.Relevant a id → a id = b id) {call : Call F}
    (member : call ∈ chip.calls.toList) (active : (chip.activation call.scope).denote a = 1) :
    call.message a = call.message b := by
  have args : call.args.map (WireValue.map (Circuit.ArithExpr.denote a)) =
      call.args.map (WireValue.map (Circuit.ArithExpr.denote b)) := by
    apply List.map_congr_left
    intro value present
    apply wire_map_congr
    intro polynomial found
    exact Polynomial.denote_congr _ (fun id used => agree id (.callArgument member active present found used))
  have result := wire_map_congr call.result (fun id present => agree id (.callResult member active present))
  simp only [Call.message, args, result]

theorem premises_agree (agree : ∀ id, chip.Relevant a id → a id = b id) :
    chip.premises a = chip.premises b := by
  apply List.filterMap_congr
  intro call member
  by_cases active : (chip.activation call.scope).denote a = 1
  · simp only [← activation_agree agree, active, ↓reduceIte, call_agree agree member active]
  · simp only [← activation_agree agree, active, ↓reduceIte]

theorem validAssignment_agree (agree : ∀ id, chip.Relevant a id → a id = b id)
    {rom : WireROM F} (valid : chip.ValidAssignment rom a) : chip.ValidAssignment rom b := by
  constructor
  · intro equation member
    rw [← activation_agree agree]
    by_cases inactive : (chip.activation equation.scope).denote a = 0
    · simp [inactive]
    · have equal := Polynomial.denote_congr equation.polynomial
        (fun id used => agree id (.equation member inactive used))
      rw [← equal]
      exact valid.1 equation member
  · intro cell member active
    rw [← activation_agree agree] at active
    have address := Polynomial.denote_congr cell.address
      (fun id used => agree id (.address member active used))
    have payload : cell.value.map (Circuit.ArithExpr.denote a) = cell.value.map (Circuit.ArithExpr.denote b) := by
      apply wire_map_congr
      intro polynomial present
      exact Polynomial.denote_congr polynomial
        (fun id used => agree id (.payload member active present used))
    rw [← address, ← payload]
    exact valid.2 cell member active

end ScopedChip

/-- Existentially pack a logical witness into shared physical columns. Only
simultaneously relevant values must agree when their columns coincide. -/
theorem emitChip_complete (chip : ScopedChip F) (layout : ColumnLayout) (rom : WireROM F)
    (assignment : Witness → F) (formed : (emitChip chip layout).wellFormed = true)
    (valid : chip.ValidAssignment rom assignment)
    (bounded : ∀ id, chip.Relevant assignment id → layout.column id < layout.occupants.size)
    (compatible : ∀ i j, chip.Relevant assignment i → chip.Relevant assignment j →
      layout.column i = layout.column j → assignment i = assignment j) :
    ∃ row : Circuit.Row F, row.chip = chip.name ∧ (emitChip chip layout).ValidRow rom row ∧
      (emitChip chip layout).receive row = chip.conclusion assignment ∧
      (emitChip chip layout).premises row = chip.premises assignment := by
  classical
  let physical : Circuit.Var → F := fun column =>
    if present : ∃ id, chip.Relevant assignment id ∧ layout.column id = column then
      assignment (Classical.choose present)
    else 0
  have pack (id : Witness) (relevant : chip.Relevant assignment id) : physical (layout.column id) = assignment id := by
    have present : ∃ other, chip.Relevant assignment other ∧ layout.column other = layout.column id :=
      ⟨id, relevant, rfl⟩
    simp only [physical, dif_pos present]
    exact compatible _ id (Classical.choose_spec present).1 relevant (Classical.choose_spec present).2
  let row := Circuit.Row.ofAssignment chip.name layout.occupants.size physical
  have agree (id : Witness) (relevant : chip.Relevant assignment id) :
      assignment id = (row.assignment ∘ layout.column) id := by
    rw [Function.comp_apply, Circuit.Row.ofAssignment_agree _ _ _ _ (bounded id relevant)]
    exact (pack id relevant).symm
  refine ⟨row, rfl, ?_, ?_, ?_⟩
  · apply (emitChip_validRow chip layout rom row).mpr
    exact ⟨formed, Circuit.Row.ofAssignment_length _ _ _, chip.validAssignment_agree agree valid⟩
  · rw [emitChip_receive]
    exact (chip.conclusion_agree agree).symm
  · rw [emitChip_premises]
    exact (chip.premises_agree agree).symm

end Aiur.Optimized
