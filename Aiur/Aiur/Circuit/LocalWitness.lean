import Aiur.Circuit.ExpressionWitness
import Aiur.Circuit.ParameterWitness
import Aiur.Circuit.LocalCorrectness
import Aiur.Circuit.RowWitness

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

/-- Every finite source body evaluation supplies a row with canonical interface encodings. -/
theorem lowerFunction_complete [Field F] [DecidableEq F]
    {program : Program F} (declarations : checkDeclarations program.enums = .ok ())
    (tags : program.enums.tagsValid F = true) {fn : Function F} {chip : Chip F}
    (compiled : lowerFunction program fn = .ok chip)
    {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
    (typed : CallsTyped program sourceCalls) (callComplete : CallsComplete program.enums sourceCalls calls)
    (checked : inferType program fn.name fn.params fn.body = .ok fn.result)
    {args : List (Value F)} {value : Value F}
    (types : fn.params.map Prod.snd = args.map Value.type)
    (formed : ∀ arg ∈ args, arg.wellFormed program.enums = true)
    (evaluated : ROMEvalExprWith program.enums (rom.decode program.enums) sourceCalls
      ((fn.params.map Prod.fst).zip args) fn.body value) :
    ∃ row, row.chip = fn.name ∧ chip.ValidRow rom row ∧
      DecodesValues program.enums (chip.receive row).args args ∧
      (chip.receive row).result.decode program.enums = some value ∧
      ∀ message ∈ chip.premises row, calls message.channel message.args message.result := by
  have resultType := evaluated.wellTyped typed (WireROM.decode_wellFormed program.enums rom)
    (parameter_wellFormed formed) fn.name fn.result (by rw [parameter_types fn.params args types]; exact checked)
  obtain ⟨inputs, output, s₁, s₂, s₃, s₄, body, s₅, s₆,
    inputsRun, outputRun, inputsValidation, outputValidation, bodyRun, constraintRun, rfl⟩ := lowerFunction_stages compiled
  have emptyLayout : ({} : BuildState F).WellFormed := ⟨by simp, by simp, by simp⟩
  have emptyValid : ({} : BuildState F).Valid rom calls (fun _ => 0) :=
    ⟨by simp [Satisfies, Scalar.Circuit.Satisfies], by simp, by simp⟩
  obtain ⟨a, e₁, inputsBound, inputsDecode⟩ := freshValues_decoded_complete declarations tags inputsRun
    emptyLayout emptyValid args types.symm formed
  have inputSymbolicBound : ∀ wire ∈ inputs.map (WireValue.map ArithExpr.var), Bounded (F := F) s₁.nextVar wire := by
    simpa only [List.forall_mem_map] using inputsBound
  have inputsDecodeA : DecodesValues program.enums
      ((inputs.map (WireValue.map ArithExpr.var)).map (WireValue.map (ArithExpr.denote a))) args := by
    simpa only [List.map_map, Function.comp_def, WireValue.map_map, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using inputsDecode
  obtain ⟨b, e₂, outputBound, outputDecode⟩ := freshValue_decoded_complete declarations tags outputRun
    e₁.layout e₁.valid value resultType.1 resultType.2
  have outputDecodeB : ((output.map ArithExpr.var).map (ArithExpr.denote b)).decode program.enums = some value := by
    simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using outputDecode
  obtain ⟨c, e₃⟩ := validateValues_complete tags inputsValidation e₂.layout e₂.valid rfl
    (fun wire member => (inputSymbolicBound wire member).mono e₂.increase)
    (Or.inr (fun wire member => (e₂.decoded_values inputSymbolicBound inputsDecodeA).each
      (wire.map (ArithExpr.denote b)) (List.mem_map.mpr ⟨wire, member, rfl⟩)))
  obtain ⟨d, e₄⟩ := validateValue_complete tags outputValidation e₃.layout e₃.valid rfl
    (outputBound.mono e₃.increase) (Or.inr ⟨value, e₃.decoded_value outputBound outputDecodeB⟩)
  have throughInterface := (e₂.trans e₃).trans e₄
  have argsDecodeD : DecodesValues program.enums (inputs.map (WireValue.map d)) args := by
    simpa only [List.map_map, Function.comp_def, WireValue.map_map, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using throughInterface.decoded_values inputSymbolicBound inputsDecodeA
  obtain ⟨e, e₅, bodyBound, bodyDecode⟩ := lowerExpr_complete declarations tags typed callComplete bodyRun
    e₄.layout e₄.valid (parameter_bounded (fun input member => (inputsBound input member).mono throughInterface.increase))
    rfl rfl (by simpa only [parameter_environment] using argsDecodeD.environment (fn.params.map Prod.fst)) evaluated
  have throughOutput := (e₃.trans e₄).trans e₅
  have e₆ := constrainValue_decoded_complete declarations constraintRun e₅.layout e₅.valid rfl
    (outputBound.mono throughOutput.increase) bodyBound (throughOutput.decoded_value outputBound outputDecodeB) bodyDecode
  let row := Row.ofAssignment fn.name s₆.nextVar e
  have finiteExt := BuildState.finite_witness e₆.layout e₆.valid fn.name
  have inputFinal : ∀ input ∈ inputs, Bounded (F := F) s₆.nextVar (input.map ArithExpr.var) :=
    fun input member => (inputsBound input member).mono ((throughInterface.trans e₅).trans e₆).increase
  have outputFinal := outputBound.mono (throughOutput.trans e₆).increase
  have rowValid : (Chip.mk fn.name inputs (output.map ArithExpr.var) s₆.nextVar s₆.constraints.toList s₆.sends.toList s₆.memory.toList).ValidRow rom row :=
    ⟨chip_wellFormed e₆.layout inputFinal outputFinal, Row.ofAssignment_length _ _ _,
      finiteExt.valid.constraints, finiteExt.valid.memory⟩
  refine ⟨row, rfl, rowValid, ?_, ?_, ?_⟩
  · simpa only [Chip.receive, List.map_map, Function.comp_def, WireValue.map_map, ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using
      (((throughInterface.trans e₅).trans e₆).trans finiteExt).decoded_values inputSymbolicBound inputsDecodeA
  · simpa only [Chip.receive, WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using
      ((throughOutput.trans e₆).trans finiteExt).decoded_value outputBound outputDecodeB
  · exact (Chip.premises_forall _ row (fun message =>
      calls message.channel message.args message.result)).mpr finiteExt.valid.calls

end Aiur.Circuit.Compiler
