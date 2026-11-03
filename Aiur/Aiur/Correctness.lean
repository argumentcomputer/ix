import Aiur.Circuit.LocalCorrectness
import Aiur.Circuit.Derivation
import Aiur.Circuit.MapFacts
import Aiur.Semantics.CallFacts

namespace Aiur

variable {F : Type} {rom : WireROM F}

/-- A raw circuit claim represents well-formed arguments and a correct evaluated result. -/
def Circuit.Message.Evaluates [Field F] [DecidableEq F] (program : Program F) (rom : WireROM F)
    (message : Circuit.Message F) : Prop :=
  ∃ args result, DecodesValues program.enums message.args args ∧
    message.result.decode program.enums = some result ∧
    ROMEvalCall (rom.decode program.enums) program message.channel args result

/-- Every closed derivation has canonical values and a finite evaluation against the decoded ROM. -/
theorem derivation_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) {message : Circuit.Message F}
    (derivation : Circuit.Derivation system rom message) : message.Evaluates program rom := by
  have stages := Circuit.compile_stages compiled
  have checked := typecheck_declarations stages.1
  induction derivation using Circuit.Derivation.rec
    (motive_2 := fun messages _ => ∀ message ∈ messages, message.Evaluates program rom) with
  | node chip row lookup valid _ childrenIH =>
      obtain ⟨fn, found, lowered⟩ := Circuit.compile_find_chip compiled lookup
      have interface := Circuit.Compiler.lowerFunction_interface lowered
      obtain ⟨args, result, argsDecoded, resultDecoded, body⟩ :=
        Circuit.Compiler.lowerFunction_sound checked stages.2.1 lowered valid
          (sourceCalls := ROMEvalCall (rom.decode program.enums) program) (by
            intro message member args result argsDecode resultDecode
            obtain ⟨otherArgs, otherResult, otherArgsDecode, otherResultDecode, evaluated⟩ := childrenIH message member
            have sameArgs := argsDecode.unique otherArgsDecode
            have sameResult := Option.some.inj (resultDecode.symm.trans otherResultDecode)
            simpa only [sameArgs, sameResult] using evaluated)
      refine ⟨args, result, argsDecoded, resultDecoded, ?_⟩
      have types : fn.params.map Prod.snd = args.map Value.type := by
        rw [argsDecoded.types]
        simpa only [Circuit.Chip.receive, List.map_map, Function.comp_def, WireValue.type_map]
          using interface.2.1.symm
      apply ROMEvalCall.intro (prepareCall_of_types (fn := fn) ?_ types argsDecoded.wellFormed) body.toEvalExpr
      change program.findFunction? chip.name = some fn
      rw [interface.1, Circuit.findFunction_name found]
      exact found
  | table member =>
      obtain ⟨args, constant, arguments, output, absent, looked⟩ := Circuit.compile_map_spec compiled member
      refine ⟨args, constant.toValue, arguments, output, .intro (prepareCall_map absent looked) ?_⟩
      exact ((ROMEvalExprWith.constant_iff (rom := rom.decode program.enums)
        (calls := ROMEvalCall (rom.decode program.enums) program) constant).mpr rfl).toEvalExpr
  | nil => simp_all
  | cons _ _ headIH tailIH =>
      rename_i message member
      rcases List.mem_cons.mp member with same | member
      · subst message; exact headIH
      · exact tailIH message member

/-- For a well-formed encoded root claim, derivability proves the claimed source result. -/
theorem compiler_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (WireValue F)} {result : WireValue F}
    (derives : Circuit.CircuitEvaluates system rom name args result)
    {values : List (Value F)} {value : Value F}
    (arguments : DecodesValues program.enums args values)
    (output : result.decode program.enums = some value) :
    ROMEvalCall (rom.decode program.enums) program name values value := by
  obtain ⟨tree⟩ := derives
  obtain ⟨otherArgs, otherResult, decodedArgs, decodedResult, evaluated⟩ := derivation_sound compiled tree
  have sameArgs := arguments.unique decodedArgs
  have sameResult := Option.some.inj (output.symm.trans decodedResult)
  simpa only [sameArgs, sameResult] using evaluated

end Aiur
