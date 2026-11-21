import Aiur.Circuit.ExpressionCorrectness
import Aiur.Circuit.CompileFacts

namespace Aiur.Circuit

variable {F : Type} {rom : WireROM F}

theorem Chip.premises_forall [Field F] [DecidableEq F] (chip : Chip F) (row : Row F)
    (property : Message F → Prop) :
    (∀ message ∈ chip.premises row, property message) ↔
      ∀ send ∈ chip.sends, send.enable.denote row.assignment = 1 →
        property (send.message row.assignment) := by
  constructor
  · intro valid send member enabled
    apply valid (send.message row.assignment)
    apply List.mem_filterMap.mpr
    exact ⟨send, member, by simp [enabled]⟩
  · intro valid message member
    obtain ⟨send, sendMember, selected⟩ := List.mem_filterMap.mp member
    split at selected
    · rename_i enabled
      cases selected
      exact valid send sendMember enabled
    · cases selected

namespace Compiler

theorem parameter_environment [Field F] (names : List String) (inputs : List (WireValue Var))
    (assignment : Var → F) :
    localsEnvironment (names.zip (inputs.map (WireValue.map ArithExpr.var))) assignment =
      names.zip (inputs.map (WireValue.map assignment)) := by
  induction names generalizing inputs with
  | nil => simp [localsEnvironment]
  | cons name names ih =>
      cases inputs with
      | nil => simp [localsEnvironment]
      | cons input inputs =>
          simp only [List.map_cons, List.zip_cons_cons]
          change (name, _) :: localsEnvironment _ assignment = _
          rw [ih]
          simp only [WireValue.map_map]
          rfl

/-- A valid row has canonical interface values and realizes its function body. -/
theorem lowerFunction_sound [Field F] [DecidableEq F]
    {program : Program F} (checked : checkDeclarations program.enums = .ok ())
    (tags : program.enums.tagsValid F = true) {fn : Function F} {chip : Chip F}
    (compiled : lowerFunction program fn = .ok chip)
    {sourceCalls : Aiur.CallRelation F} {row : Row F} (valid : chip.ValidRow rom row)
    (premises : ∀ message ∈ chip.premises row, ∀ args result,
      DecodesValues program.enums message.args args → message.result.decode program.enums = some result →
      sourceCalls message.channel args result) :
    ∃ args result, DecodesValues program.enums (chip.receive row).args args ∧
      (chip.receive row).result.decode program.enums = some result ∧
      ROMEvalExprWith program.enums (rom.decode program.enums) sourceCalls
        ((fn.params.map Prod.fst).zip args) fn.body result := by
  let calls : Circuit.CallRelation F := fun name args result => ⟨name, args, result⟩ ∈ chip.premises row
  have callSound : CallsSound program.enums calls sourceCalls := fun name args result member =>
    premises ⟨name, args, result⟩ member
  obtain ⟨inputs, output, s₁, s₂, s₃, s₄, body, s₅, s₆,
    _, _, inputValidation, outputValidation, bodyRun, outputRun, rfl⟩ := lowerFunction_stages compiled
  have stateValid : s₆.Valid rom calls row.assignment := ⟨valid.2.2.1,
    (Chip.premises_forall _ row (fun message => calls message.channel message.args message.result)).mp
      (fun _ h => h), valid.2.2.2⟩
  obtain ⟨s₅valid, resultEq⟩ := constrainValue_sound outputRun stateValid
  obtain ⟨s₄valid, evaluated⟩ := lowerExpr_sound checked tags callSound bodyRun s₅valid
  have s₃valid := (validateValue_sound checked outputValidation s₄valid).1
  have inputDecoded := (validateValues_sound checked inputValidation s₃valid).2 rfl
  have allInputs : ∀ wire ∈ inputs.map (WireValue.map row.assignment),
      ∃ value, wire.decode program.enums = some value := by
    intro wire member
    obtain ⟨input, inputMember, rfl⟩ := List.mem_map.mp member
    simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using inputDecoded (input.map ArithExpr.var) (List.mem_map.mpr ⟨input, inputMember, rfl⟩)
  obtain ⟨args, decoded⟩ := DecodesValues.exists_of_each allInputs
  obtain ⟨result, resultDecode, bodyEval⟩ := evaluated rfl ((fn.params.map Prod.fst).zip args)
    (by simpa only [parameter_environment] using decoded.environment (fn.params.map Prod.fst))
  refine ⟨args, result, decoded, ?_, bodyEval⟩
  have equal := resultEq rfl
  simp only [WireValue.map_map] at equal
  change output.map row.assignment = body.map (ArithExpr.denote row.assignment) at equal
  simpa only [Chip.receive, WireValue.map_map, Function.comp_def,
    ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, equal] using resultDecode

end Compiler
end Aiur.Circuit
