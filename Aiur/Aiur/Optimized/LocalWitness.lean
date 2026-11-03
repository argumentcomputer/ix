import Aiur.Optimized.ParameterWitness
import Aiur.Optimized.ValidationWitness
import Aiur.Optimized.LocalCorrectness
import Aiur.Optimized.ExpressionWitness

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
open Circuit.Compiler (Bounded LocalsBounded CallsComplete parameter_types parameter_wellFormed
  parameter_bounded parameter_environment)

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Finite source body evaluation supplies an assignment for the actual scoped
function compiler, with the same decoded interface and active call claims. -/
theorem function_complete {program : Program F} (declarations : checkDeclarations program.enums = .ok ())
    (tags : program.enums.tagsValid F = true) {config : Config} {fn : Function F} {chip : ScopedChip F}
    {validateInputs : Bool} (compiled : function program config fn validateInputs = .ok chip)
    {rom : WireROM F} {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
    (typed : CallsTyped program sourceCalls) (callComplete : CallsComplete program.enums sourceCalls calls)
    (checked : inferType program fn.name fn.params fn.body = .ok fn.result)
    {args : List (Value F)} {value : Value F}
    (types : fn.params.map Prod.snd = args.map Value.type)
    (formed : ∀ arg ∈ args, arg.wellFormed program.enums = true)
    (evaluated : ROMEvalExprWith program.enums (rom.decode program.enums) sourceCalls
      ((fn.params.map Prod.fst).zip args) fn.body value) :
    ∃ assignment, chip.ValidAssignment rom assignment ∧
      DecodesValues program.enums (chip.conclusion assignment).args args ∧
      (chip.conclusion assignment).result.decode program.enums = some value ∧
      ∀ message ∈ chip.premises assignment, calls message.channel message.args message.result := by
  have resultType := evaluated.wellTyped typed (WireROM.decode_wellFormed program.enums rom)
    (parameter_wellFormed formed) fn.name fn.result (by rw [parameter_types fn.params args types]; exact checked)
  obtain ⟨inputs, output, s₁, s₂, s₃, body, s₅,
    inputsRun, outputRun, inputsValidation, bodyRun, chipEq⟩ := function_stages compiled
  let initialState : State F := {config, scopes := #[⟨.const 1, []⟩]}
  have emptyLayout : initialState.toReference.WellFormed := by
    exact ⟨by simp [initialState, State.toReference], by simp [initialState, State.toReference],
      by simp [initialState, State.toReference]⟩
  have emptyValid : initialState.Valid rom calls (fun _ => 0) := by
    exact ⟨by simp [initialState], by simp [initialState], by simp [initialState]⟩
  have emptyScoped : initialState.Scoped := by
    exact ⟨by simp [initialState], by simp [initialState], by simp [initialState],
      by simp [initialState, Scalar.Circuit.ArithExpr.inBounds]⟩
  obtain ⟨a, e₁, inputsBound, inputsDecode⟩ := freshValues_decoded_complete declarations tags inputsRun
    emptyLayout emptyValid args types.symm formed
  have inputSymbolicBound : ∀ wire ∈ inputs.map (WireValue.map Polynomial.var), Bounded (F := F) s₁.roles.size wire := by
    simpa only [List.forall_mem_map] using inputsBound
  have inputsDecodeA : DecodesValues program.enums
      ((inputs.map (WireValue.map Polynomial.var)).map (WireValue.map (Circuit.ArithExpr.denote a))) args := by
    simpa only [List.map_map, Function.comp_def, WireValue.map_map, Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using inputsDecode
  have s₁scoped := freshValues_scoped inputsRun emptyScoped
  obtain ⟨b, e₂, outputBound, outputDecode⟩ := freshValue_decoded_complete declarations tags outputRun
    e₁.layout e₁.validAssignment value resultType.1 resultType.2
  have s₂scoped := freshValue_scoped outputRun s₁scoped
  have s₂scopes : s₂.scopes = initialState.scopes :=
    (freshValue_preserves outputRun).1.trans (freshValues_preserves inputsRun).1
  have s₂root : (s₂.activation 0).denote b = 1 := by
    simp [State.activation, s₂scopes, initialState, Scalar.Circuit.ArithExpr.denote]
  have s₂valid : 0 < s₂.scopes.size := by simp [s₂scopes, initialState]
  have outputDecodeB : ((output.map Polynomial.var).map (Circuit.ArithExpr.denote b)).decode program.enums = some value := by
    simpa only [WireValue.map_map, Function.comp_def, Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using outputDecode
  obtain ⟨c, e₃, inputStructure, s₃scoped⟩ : ∃ c, Extension rom calls s₂ s₃ b c ∧
      s₂.Extends s₃ ∧ s₃.Scoped := by
    cases validateInputs with
    | false =>
        obtain ⟨_, rfl⟩ := pure_ok.mp inputsValidation
        exact ⟨b, .refl e₂.layout e₂.valid, .refl _, s₂scoped⟩
    | true =>
        have run : (do for wire in inputs.map (WireValue.map Polynomial.var) do
            validateValue program.enums 0 wire : Build F Unit) s₂ = .ok ((), s₃) := by
          simpa only [validateParameters, Bool.true_eq, ↓reduceIte, List.forIn_map] using inputsValidation
        obtain ⟨c, e₃⟩ := validateValues_complete tags run e₂.layout s₂scoped e₂.validAssignment s₂valid
          (fun wire member => (inputSymbolicBound wire member).mono e₂.increase)
          (Or.inr ⟨s₂root, fun wire member => (e₂.decoded_values inputSymbolicBound inputsDecodeA).each
            (wire.map (Circuit.ArithExpr.denote b)) (List.mem_map.mpr ⟨wire, member, rfl⟩)⟩)
        obtain ⟨extension, nextScoped⟩ := validateValues_scoped run s₂scoped s₂valid
        exact ⟨c, e₃, extension, nextScoped⟩
  have s₃root := (e₃.activation inputStructure s₂scoped s₂valid).trans s₂root
  have s₃valid := inputStructure.scopeValid s₂valid
  have throughInterface := e₂.trans e₃
  have argsDecodeC : DecodesValues program.enums (inputs.map (WireValue.map c)) args := by
    simpa only [List.map_map, Function.comp_def, WireValue.map_map, Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using
      throughInterface.decoded_values inputSymbolicBound inputsDecodeA
  have bodyWitness : ∃ e, Extension rom calls s₃ s₅ c e ∧ Bounded s₅.roles.size body ∧
      (body.map (Circuit.ArithExpr.denote e)).decode program.enums = some value := by
    apply lower_complete declarations tags typed callComplete bodyRun e₃.layout s₃scoped
      e₃.validAssignment s₃valid
      (parameter_bounded (fun input member => (inputsBound input member).mono throughInterface.increase))
    · intro candidate same
      have candidateEq : candidate = output := (Option.some.inj same).symm
      subst candidate
      exact outputBound.mono e₃.increase
    · exact s₃root
    · simpa only [parameter_environment] using argsDecodeC.environment (fn.params.map Prod.fst)
    · intro candidate same
      have candidateEq : candidate = output := (Option.some.inj same).symm
      subst candidate
      simpa only [WireValue.map_map, Function.comp_def, Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using e₃.decoded_value outputBound outputDecodeB
    · exact evaluated
  obtain ⟨e, e₅, _, _⟩ := bodyWitness
  have finalValid := e₅.validAssignment
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · simpa only [chipEq, ScopedChip.ValidAssignment, ScopedChip.activation, State.activation] using
      And.intro finalValid.1 finalValid.2.2
  · simpa only [chipEq, ScopedChip.conclusion, List.map_map, Function.comp_def, WireValue.map_map,
      Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using
      (throughInterface.trans e₅).decoded_values inputSymbolicBound inputsDecodeA
  · simpa only [chipEq, ScopedChip.conclusion, WireValue.map_map, Function.comp_def, Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using
      (e₃.trans e₅).decoded_value outputBound outputDecodeB
  · apply (ScopedChip.premises_forall chip e (fun message => calls message.channel message.args message.result)).mpr
    simpa only [chipEq, ScopedChip.activation, State.activation, Call.message] using finalValid.2.1

end Aiur.Optimized.Compiler
