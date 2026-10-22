import Aiur.Optimized.Layout
import Aiur.Optimized.PolynomialFacts
import Aiur.Circuit.RowWitness

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

def Call.message (call : Call F) (assignment : Witness → F) : Circuit.Message F :=
  ⟨call.channel, call.args.map (WireValue.map (Circuit.ArithExpr.denote assignment)), call.result.map assignment⟩

/-- Equations and ROM membership have no evaluation order. Calls are exposed
as premises rather than interpreted recursively at this boundary. -/
def ScopedChip.ValidAssignment (chip : ScopedChip F) (rom : WireROM F) (assignment : Witness → F) : Prop :=
  (∀ equation ∈ chip.equations.toList,
    (chip.activation equation.scope).denote assignment * equation.polynomial.denote assignment = 0) ∧
  (∀ cell ∈ chip.cells.toList, (chip.activation cell.scope).denote assignment = 1 →
    (cell.address.denote assignment, cell.value.map (Circuit.ArithExpr.denote assignment)) ∈ rom.entries)

def ScopedChip.conclusion (chip : ScopedChip F) (assignment : Witness → F) : Circuit.Message F :=
  ⟨chip.name, chip.inputs.map (WireValue.map assignment), chip.output.map assignment⟩

def ScopedChip.premises (chip : ScopedChip F) (assignment : Witness → F) : List (Circuit.Message F) :=
  chip.calls.toList.filterMap fun call =>
    if (chip.activation call.scope).denote assignment = 1 then some (call.message assignment) else none

/-- Witness transport preserves every call occurrence and the same ROM. -/
def ScopedChip.Refines (source target : ScopedChip F) : Prop :=
  ∀ rom assignment, source.ValidAssignment rom assignment →
    ∃ translated, target.ValidAssignment rom translated ∧
      target.conclusion translated = source.conclusion assignment ∧
      target.premises translated = source.premises assignment

def ScopedChip.Equivalent (source target : ScopedChip F) : Prop :=
  source.Refines target ∧ target.Refines source

def ScopedChip.Rule (chip : ScopedChip F) (rom : WireROM F)
    (conclusion : Circuit.Message F) (premises : List (Circuit.Message F)) : Prop :=
  ∃ assignment, chip.ValidAssignment rom assignment ∧
    chip.conclusion assignment = conclusion ∧ chip.premises assignment = premises

theorem ScopedChip.Equivalent.rule_iff {source target : ScopedChip F} (same : source.Equivalent target)
    (rom : WireROM F) (conclusion : Circuit.Message F) (premises : List (Circuit.Message F)) :
    source.Rule rom conclusion premises ↔ target.Rule rom conclusion premises := by
  constructor
  · rintro ⟨a, valid, root, calls⟩
    obtain ⟨b, valid, root', calls'⟩ := same.1 rom a valid
    exact ⟨b, valid, root'.trans root, calls'.trans calls⟩
  · rintro ⟨a, valid, root, calls⟩
    obtain ⟨b, valid, root', calls'⟩ := same.2 rom a valid
    exact ⟨b, valid, root'.trans root, calls'.trans calls⟩

theorem ScopedChip.Refines.trans {first second third : ScopedChip F}
    (left : first.Refines second) (right : second.Refines third) : first.Refines third := by
  intro rom assignment valid
  obtain ⟨middle, valid, conclusion, premises⟩ := left rom assignment valid
  obtain ⟨last, valid, conclusion', premises'⟩ := right rom middle valid
  exact ⟨last, valid, conclusion'.trans conclusion, premises'.trans premises⟩

theorem ScopedChip.Equivalent.trans {first second third : ScopedChip F}
    (left : first.Equivalent second) (right : second.Equivalent third) : first.Equivalent third :=
  ⟨left.1.trans right.1, right.2.trans left.2⟩

@[simp] theorem ColumnLayout.expression_denote (layout : ColumnLayout) (expr : Polynomial F)
    (assignment : Circuit.Var → F) :
    (layout.expression expr).denote assignment = expr.denote (assignment ∘ layout.column) := by
  simp [ColumnLayout.expression, Polynomial.denote_simplify, Polynomial.denote_subst,
    Function.comp_def, Scalar.Circuit.ArithExpr.denote]

private theorem discard_zero {α : Type} (xs : List α) (polynomial : α → Polynomial F)
    (assignment : Witness → F) :
    Circuit.Satisfies (xs.filterMap fun x => if polynomial x == .const 0 then none else some (polynomial x)) assignment ↔
      ∀ x ∈ xs, (polynomial x).denote assignment = 0 := by
  constructor
  · intro valid x member
    by_cases zero : (polynomial x == .const 0) = true
    · rw [(Polynomial.beq_eq _ _).mp zero]
      rfl
    · exact valid _ (List.mem_filterMap.mpr ⟨x, member, by simp [zero]⟩)
  · intro valid p member
    obtain ⟨x, inputMember, emitted⟩ := List.mem_filterMap.mp member
    split at emitted
    · contradiction
    · cases emitted
      exact valid x inputMember

theorem emitChip_constraints (chip : ScopedChip F) (layout : ColumnLayout) (assignment : Witness → F) :
    Circuit.Satisfies (emitChip chip layout).constraints assignment ↔
      ∀ equation ∈ chip.equations.toList,
        (chip.activation equation.scope).denote (assignment ∘ layout.column) *
          equation.polynomial.denote (assignment ∘ layout.column) = 0 := by
  change Circuit.Satisfies (chip.equations.toList.filterMap _) assignment ↔ _
  rw [discard_zero]
  simp only [Polynomial.denote_simplify, Circuit.ArithExpr.denote,
    Scalar.Circuit.ArithExpr.denote]
  change (∀ equation ∈ chip.equations.toList,
    (layout.expression (chip.activation equation.scope)).denote assignment *
      (layout.expression equation.polynomial).denote assignment = 0) ↔ _
  simp only [ColumnLayout.expression_denote]

theorem emitChip_memory (chip : ScopedChip F) (layout : ColumnLayout) (rom : WireROM F)
    (assignment : Witness → F) :
    (∀ lookup ∈ (emitChip chip layout).memory, lookup.Valid rom assignment) ↔
      ∀ cell ∈ chip.cells.toList,
        (chip.activation cell.scope).denote (assignment ∘ layout.column) = 1 →
        (cell.address.denote (assignment ∘ layout.column),
          cell.value.map (Circuit.ArithExpr.denote (assignment ∘ layout.column))) ∈ rom.entries := by
  simp only [emitChip, Id.run, pure, Circuit.MemoryLookup.Valid, List.forall_mem_map]
  simp only [ColumnLayout.expression_denote, WireValue.map_map, Function.comp_def]

/-- Emission is exactly substitution of physical columns for logical witnesses,
even for layouts which share columns. This direction needs no ownership claim. -/
theorem emitChip_validRow (chip : ScopedChip F) (layout : ColumnLayout) (rom : WireROM F) (row : Circuit.Row F) :
    (emitChip chip layout).ValidRow rom row ↔
      (emitChip chip layout).wellFormed = true ∧ row.values.length = layout.occupants.size ∧
        chip.ValidAssignment rom (row.assignment ∘ layout.column) := by
  unfold Circuit.Chip.ValidRow ScopedChip.ValidAssignment
  rw [emitChip_constraints, emitChip_memory]
  rfl

theorem emitChip_receive (chip : ScopedChip F) (layout : ColumnLayout) (row : Circuit.Row F) :
    (emitChip chip layout).receive row = chip.conclusion (row.assignment ∘ layout.column) := by
  simp [emitChip, Circuit.Chip.receive, ScopedChip.conclusion, WireValue.map_map, List.map_map,
    Function.comp_def, Scalar.Circuit.ArithExpr.denote]

theorem emitChip_premises (chip : ScopedChip F) (layout : ColumnLayout) (row : Circuit.Row F) :
    (emitChip chip layout).premises row = chip.premises (row.assignment ∘ layout.column) := by
  simp only [emitChip, Id.run, pure, Circuit.Chip.premises, ScopedChip.premises, List.filterMap_map]
  congr 1
  funext call
  simp only [Function.comp_def, ColumnLayout.expression_denote]
  split
  · congr 1
    simp [Circuit.Send.message, Call.message, WireValue.map_map, List.map_map,
      ColumnLayout.expression_denote, Function.comp_def]
  · rfl

end Aiur.Optimized
