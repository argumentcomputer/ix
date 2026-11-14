import Aiur.Circuit.SemanticModel

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F]
  {program : Program F} {system : System F} {rom : WireROM F}

theorem System.SemanticModel.derivation_sound (model : system.SemanticModel program)
    {message : Message F} (tree : Derivation system rom message) : message.Evaluates program rom := by
  induction tree using Derivation.rec
    (motive_2 := fun messages _ => ∀ message ∈ messages, message.Evaluates program rom) with
  | node chip row lookup valid children ih =>
      obtain ⟨args, result, arguments, decoded, locals, body, prepared, evaluated⟩ :=
        model.sound rom (.node chip row lookup valid) (ROMEvalCall (rom.decode program.enums) program) (by
          intro premise member args result arguments decoded
          obtain ⟨oldArgs, oldResult, oldArguments, oldDecoded, evaluated⟩ := ih premise member
          have sameArgs := arguments.unique oldArguments
          have sameResult := Option.some.inj (decoded.symm.trans oldDecoded)
          simpa only [sameArgs, sameResult] using evaluated)
      exact ⟨args, result, arguments, decoded, .intro prepared evaluated.toEvalExpr⟩
  | table member =>
      obtain ⟨args, result, arguments, decoded, locals, body, prepared, evaluated⟩ :=
        model.sound rom (.table _ member) (ROMEvalCall (rom.decode program.enums) program)
          (by simp [RuleInstance.premises])
      exact ⟨args, result, arguments, decoded, .intro prepared evaluated.toEvalExpr⟩
  | nil => simp_all
  | cons _ _ head tail =>
      rename_i message member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail message member

theorem System.SemanticModel.sound_encoded (model : system.SemanticModel program)
    {name : String} {wires : List (WireValue F)} {output : WireValue F}
    (derived : CircuitEvaluates system rom name wires output)
    {args : List (Value F)} {result : Value F}
    (arguments : DecodesValues program.enums wires args) (decoded : output.decode program.enums = some result) :
    ROMEvalCall (rom.decode program.enums) program name args result := by
  obtain ⟨tree⟩ := derived
  obtain ⟨otherArgs, otherResult, otherArguments, otherDecoded, evaluated⟩ := model.derivation_sound tree
  have sameArgs := arguments.unique otherArguments
  have sameResult := Option.some.inj (decoded.symm.trans otherDecoded)
  simpa only [sameArgs, sameResult] using evaluated

theorem System.SemanticModel.calls_typed (model : system.SemanticModel program) :
    CallsTyped program (EncodedEvaluates program.enums system rom) := by
  intro name args result evaluated signature found
  obtain ⟨wires, output, _, decoded, ⟨tree⟩⟩ := evaluated
  cases tree with
  | node chip row lookup valid children =>
      have declared := model.resultType rom (.node chip row lookup valid) signature found
      exact ⟨(WireValue.decode_spec decoded).1.trans declared, (WireValue.decode_spec decoded).2.1⟩
  | table member =>
      have declared := model.resultType rom (.table _ member) signature found
      exact ⟨(WireValue.decode_spec decoded).1.trans declared, (WireValue.decode_spec decoded).2.1⟩

theorem System.SemanticModel.calls_complete (model : system.SemanticModel program) :
    Compiler.CallsComplete program.enums (EncodedEvaluates program.enums system rom)
      (CircuitEvaluates system rom) := by
  intro name args result evaluated wires output arguments decoded
  obtain ⟨oldWires, oldOutput, oldArguments, oldDecoded, derived⟩ := evaluated
  have sameArgs := arguments.wires_unique model.declarations oldArguments
  have sameResult := WireValue.decode_injective model.declarations decoded oldDecoded
  simpa only [sameArgs, sameResult] using derived

theorem System.SemanticModel.evaluation_complete (model : system.SemanticModel program)
    {name : String} {args : List (Value F)} {result : Value F}
    (evaluated : ROMEvalCall (rom.decode program.enums) program name args result) :
    EncodedEvaluates program.enums system rom name args result := by
  induction evaluated using ROMEvalCall.rec
    (motive_1 := fun locals expr value _ =>
      ROMEvalExprWith program.enums (rom.decode program.enums) (EncodedEvaluates program.enums system rom) locals expr value)
    (motive_2 := fun locals exprs values _ =>
      ROMEvalArgsWith program.enums (rom.decode program.enums) (EncodedEvaluates program.enums system rom) locals exprs values) with
  | literal => exact .literal
  | var lookup => exact .var lookup
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | project _ projected ih => exact .project ih projected
  | letValue _ matched _ inputIH bodyIH => exact .letValue inputIH matched bodyIH
  | store _ cell ih => exact .store ih cell
  | load _ cell typed ih => exact .load ih cell typed
  | hint _ typed ih => exact .hint ih typed
  | neg _ operation ih => exact .neg ih operation
  | assertEq _ _ operation leftIH rightIH => exact .assertEq leftIH rightIH operation
  | binary _ _ operation leftIH rightIH => exact .binary leftIH rightIH operation
  | call _ _ argsIH calleeIH => exact .call argsIH calleeIH
  | matchValue _ selected _ inputIH bodyIH => exact .matchValue inputIH selected bodyIH
  | nil => exact .nil
  | cons _ _ headIH tailIH => exact .cons headIH tailIH
  | intro prepared _ bodyIH =>
      obtain ⟨rule, name, arguments, decoded, premises⟩ :=
        model.complete rom (CircuitEvaluates system rom) (EncodedEvaluates program.enums system rom)
          model.calls_typed model.calls_complete _ _ _ ⟨_, _, prepared, bodyIH⟩
      refine ⟨rule.conclusion.args, rule.conclusion.result, arguments, decoded, ?_⟩
      have tree := rule.derives premises
      simpa only [← name, CircuitEvaluates] using tree

theorem System.SemanticModel.complete_encoded (model : system.SemanticModel program)
    {name : String} {args : List (Value F)} {result : Value F}
    (evaluated : ROMEvalCall (rom.decode program.enums) program name args result)
    {wires : List (WireValue F)} {output : WireValue F}
    (arguments : DecodesValues program.enums wires args) (decoded : output.decode program.enums = some result) :
    CircuitEvaluates system rom name wires output :=
  model.calls_complete name args result (model.evaluation_complete evaluated) wires output arguments decoded

theorem System.SemanticModel.evaluates_iff (model : system.SemanticModel program)
    {name : String} {args : List (Value F)} {result : Value F} :
    ROMEvalCall (rom.decode program.enums) program name args result ↔
      EncodedEvaluates program.enums system rom name args result := by
  refine ⟨model.evaluation_complete, ?_⟩
  rintro ⟨wires, output, arguments, decoded, derived⟩
  exact model.sound_encoded derived arguments decoded

end Aiur.Circuit
