import Aiur.Optimized.ExpressionCorrectness
import Aiur.Circuit.LocalCorrectness
import Aiur.Optimized.ParameterWitness

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

theorem ScopedChip.premises_forall (chip : ScopedChip F) (assignment : Witness → F)
    (property : Circuit.Message F → Prop) :
    (∀ message ∈ chip.premises assignment, property message) ↔
      ∀ call ∈ chip.calls.toList, (chip.activation call.scope).denote assignment = 1 →
        property (call.message assignment) := by
  constructor
  · intro valid call member enabled
    exact valid (call.message assignment) (List.mem_filterMap.mpr ⟨call, member, by simp [enabled]⟩)
  · intro valid message member
    obtain ⟨call, callMember, selected⟩ := List.mem_filterMap.mp member
    split at selected
    · rename_i enabled
      cases selected
      exact valid call callMember enabled
    · cases selected

namespace Compiler

open Circuit.Compiler (parameter_environment)

/-- Internal rows preserve canonicality from their arguments. The call premise
produces a decoded result; callers never assume the result is canonical. -/
theorem function_sound {program : Program F} (checked : checkDeclarations program.enums = .ok ())
    (tags : program.enums.tagsValid F = true) {config : Config} {fn : Function F} {chip : ScopedChip F}
    {validateInputs : Bool} (compiled : function program config fn validateInputs = .ok chip)
    {rom : WireROM F} {sourceCalls : Aiur.CallRelation F} {assignment : Witness → F}
    (romValid : rom.Valid)
    (valid : chip.ValidAssignment rom assignment)
    (premises : ∀ message ∈ chip.premises assignment, ∀ args,
      DecodesValues program.enums message.args args →
      (∀ v ∈ args, (rom.decode program.enums).Provenance v) →
      ∃ result, message.result.decode program.enums = some result ∧ sourceCalls message.channel args result)
    (callProvenance : ∀ name args result, sourceCalls name args result →
      (∀ v ∈ args, (rom.decode program.enums).Provenance v) →
      (rom.decode program.enums).Provenance result)
    {args : List (Value F)}
    (arguments : DecodesValues program.enums (chip.conclusion assignment).args args)
    (trusted : ∀ v ∈ args, (rom.decode program.enums).Provenance v) :
    ∃ result, (chip.conclusion assignment).result.decode program.enums = some result ∧
      ROMEvalExprWith program.enums (rom.decode program.enums) sourceCalls
        ((fn.params.map Prod.fst).zip args) fn.body result ∧
      (rom.decode program.enums).Provenance result := by
  let calls : Circuit.CallRelation F := fun name args result => ⟨name, args, result⟩ ∈ chip.premises assignment
  have callSound : CallsSound program.enums rom calls sourceCalls := fun name args result member =>
    premises ⟨name, args, result⟩ member
  obtain ⟨inputs, output, s₁, s₂, s₃, body, s₄,
    inputsRun, outputRun, inputValidation, bodyRun, chipEq⟩ := function_stages compiled
  have stateValid : s₄.Valid rom calls assignment := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [chipEq, ScopedChip.ValidAssignment, ScopedChip.activation, State.activation] using valid.1
    · have activeCalls := (ScopedChip.premises_forall chip assignment
        (fun message => calls message.channel message.args message.result)).mp (fun _ h => h)
      simpa only [chipEq, ScopedChip.activation, State.activation, Call.message] using activeCalls
    · simpa only [chipEq, ScopedChip.ValidAssignment, ScopedChip.activation, State.activation] using valid.2
  have s₁root : (s₁.activation 0).denote assignment = 1 := by
    simp only [State.activation, (freshValues_preserves inputsRun).1]
    rfl
  have s₂root := (freshValue_extends outputRun).active s₁root
  have inputExtension : s₂.Extends s₃ := by
    cases validateInputs with
    | false =>
        obtain ⟨_, rfl⟩ := pure_ok.mp inputValidation
        exact .refl _
    | true =>
        have run : (do for wire in inputs.map (WireValue.map Polynomial.var) do
            validateValue program.enums 0 wire : Build F Unit) s₂ = .ok ((), s₃) := by
          simpa only [validateParameters, Bool.true_eq, ↓reduceIte, List.forIn_map] using inputValidation
        exact (validateValues_sound checked tags run).1
  have s₃root := inputExtension.active s₂root
  obtain ⟨_, bodyMeaning⟩ := lower_sound checked tags romValid callSound callProvenance bodyRun
  have environmentTrusted : Environment.Provenance (rom.decode program.enums) ((fn.params.map Prod.fst).zip args) := by
    intro binding member
    exact trusted binding.2 (List.of_mem_zip member).2
  have decoded : DecodesValues program.enums (inputs.map (WireValue.map assignment)) args := by
    simpa only [chipEq, ScopedChip.conclusion] using arguments
  obtain ⟨result, resultDecode, evaluated⟩ := (bodyMeaning assignment s₃root stateValid).2 s₃root
    ((fn.params.map Prod.fst).zip args)
    (by simpa only [parameter_environment] using decoded.environment (fn.params.map Prod.fst)) environmentTrusted
  refine ⟨result, ?_, evaluated, evaluated.provenance (WireROM.decode_valid romValid) callProvenance environmentTrusted⟩
  simpa only [chipEq, ScopedChip.conclusion, lower_target bodyRun, WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultDecode

/-- Entry arguments are checked independently of whether the body uses them.
This is the base case of the canonical-value invariant. -/
theorem function_arguments_sound {program : Program F} (checked : checkDeclarations program.enums = .ok ())
    (tags : program.enums.tagsValid F = true) {config : Config} {fn : Function F} {chip : ScopedChip F}
    (compiled : function program config fn true = .ok chip)
    {rom : WireROM F} {assignment : Witness → F} (valid : chip.ValidAssignment rom assignment) :
    ∃ args, DecodesValues program.enums (chip.conclusion assignment).args args := by
  obtain ⟨inputs, output, s₁, s₂, s₃, body, s₄,
    inputsRun, outputRun, inputValidation, bodyRun, chipEq⟩ := function_stages compiled
  let initialState : State F := {config, scopes := #[⟨.const 1, []⟩]}
  have initialScoped : initialState.Scoped := by
    exact ⟨by simp [initialState], by simp [initialState], by simp [initialState],
      by simp [initialState, Scalar.Circuit.ArithExpr.inBounds]⟩
  have s₂scoped := freshValue_scoped outputRun (freshValues_scoped inputsRun initialScoped)
  have s₂scopes : s₂.scopes = initialState.scopes :=
    (freshValue_preserves outputRun).1.trans (freshValues_preserves inputsRun).1
  have s₂bound : 0 < s₂.scopes.size := by simp [s₂scopes, initialState]
  have run : (do for wire in inputs.map (WireValue.map Polynomial.var) do
      validateValue program.enums 0 wire : Build F Unit) s₂ = .ok ((), s₃) := by
    simpa only [validateParameters, Bool.true_eq, ↓reduceIte, List.forIn_map] using inputValidation
  obtain ⟨inputExtension, s₃scoped⟩ := validateValues_scoped run s₂scoped s₂bound
  have bodyExtension := (lower_scoped bodyRun s₃scoped (inputExtension.scopeValid s₂bound)).1
  let calls : Circuit.CallRelation F := fun _ _ _ => True
  have stateValid : s₄.Valid rom calls assignment := by
    refine ⟨?_, by simp [calls], ?_⟩
    · simpa only [chipEq, ScopedChip.ValidAssignment, ScopedChip.activation, State.activation] using valid.1
    · simpa only [chipEq, ScopedChip.ValidAssignment, ScopedChip.activation, State.activation] using valid.2
  have root : (s₂.activation 0).denote assignment = 1 := by
    simp [State.activation, s₂scopes, initialState, Scalar.Circuit.ArithExpr.denote]
  have decoded := ((validateValues_sound checked tags run).2 rom calls assignment root
    (stateValid.of_extends bodyExtension)).2 root
  apply DecodesValues.exists_of_each
  intro wire member
  simp only [chipEq, ScopedChip.conclusion] at member
  obtain ⟨input, inputMember, rfl⟩ := List.mem_map.mp member
  simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using decoded (input.map Polynomial.var)
    (List.mem_map.mpr ⟨input, inputMember, rfl⟩)

end Compiler
end Aiur.Optimized
