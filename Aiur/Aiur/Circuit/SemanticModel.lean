import Aiur.Circuit.SupportedEquivalence
import Aiur.Completeness

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F]

/-- One source function or map step, with calls left as premises. The body
evaluation is finite even when the supplied premise relation is cyclic. -/
def CallStep (program : Program F) (rom : WireROM F) (calls : Aiur.CallRelation F)
    (name : String) (args : List (Value F)) (result : Value F) : Prop :=
  ∃ locals body, prepareCall program name args = .ok (locals, body) ∧
    ROMEvalExprWith program.enums (rom.decode program.enums) calls locals body result

/-- A compiler's local obligations. These are proved once for its executable
function compiler; the global tree, graph, and checker transports are shared. -/
structure System.SemanticModel (program : Program F) (system : System F) : Prop where
  declarations : checkDeclarations program.enums = .ok ()
  resultType : ∀ rom (rule : RuleInstance system rom) signature,
    program.findSignature? rule.conclusion.channel = some signature →
    rule.conclusion.result.type = signature.result
  sound : ∀ rom (rule : RuleInstance system rom) (calls : Aiur.CallRelation F),
    (∀ premise ∈ rule.premises, ∀ args result,
      DecodesValues program.enums premise.args args → premise.result.decode program.enums = some result →
      calls premise.channel args result) →
    ∃ args result, DecodesValues program.enums rule.conclusion.args args ∧
      rule.conclusion.result.decode program.enums = some result ∧
      CallStep program rom calls rule.conclusion.channel args result
  complete : ∀ rom (calls : CallRelation F) (sourceCalls : Aiur.CallRelation F),
    CallsTyped program sourceCalls → Compiler.CallsComplete program.enums sourceCalls calls →
    ∀ name args result, CallStep program rom sourceCalls name args result →
    ∃ rule : RuleInstance system rom, rule.conclusion.channel = name ∧
      DecodesValues program.enums rule.conclusion.args args ∧
      rule.conclusion.result.decode program.enums = some result ∧
      ∀ premise ∈ rule.premises, calls premise.channel premise.args premise.result

theorem System.SemanticModel.supportRefines {program : Program F} {source target : System F}
    (sourceModel : source.SemanticModel program) (targetModel : target.SemanticModel program) :
    source.SupportRefines target := by
  intro rom rule supported
  let calls : CallRelation F := fun name args result => ⟨name, args, result⟩ ∈ rule.premises
  let sourceCalls : Aiur.CallRelation F := fun name args result =>
    ∃ wires output, DecodesValues program.enums wires args ∧
      output.decode program.enums = some result ∧ calls name wires output
  have typed : CallsTyped program sourceCalls := by
    intro name args result available signature found
    obtain ⟨wires, output, arguments, decoded, member⟩ := available
    obtain ⟨provider, same⟩ := supported ⟨name, wires, output⟩ member
    have declared := sourceModel.resultType rom provider signature (by simpa only [same] using found)
    refine ⟨(WireValue.decode_spec decoded).1.trans ?_, (WireValue.decode_spec decoded).2.1⟩
    simpa only [same] using declared
  have callComplete : Compiler.CallsComplete program.enums sourceCalls calls := by
    intro name args result available wires output arguments decoded
    obtain ⟨previousArgs, previousResult, previousArguments, previousDecoded, member⟩ := available
    have sameArgs := arguments.wires_unique sourceModel.declarations previousArguments
    have sameResult := WireValue.decode_injective sourceModel.declarations decoded previousDecoded
    simpa only [sameArgs, sameResult] using member
  obtain ⟨args, result, arguments, decoded, step⟩ := sourceModel.sound rom rule sourceCalls
    (fun premise member args result arguments decoded =>
      ⟨premise.args, premise.result, arguments, decoded, member⟩)
  obtain ⟨next, name, nextArguments, nextDecoded, premises⟩ :=
    targetModel.complete rom calls sourceCalls typed callComplete rule.conclusion.channel args result step
  have sameArgs := nextArguments.wires_unique sourceModel.declarations arguments
  have sameResult := WireValue.decode_injective sourceModel.declarations nextDecoded decoded
  refine ⟨next, ?_, ?_⟩
  · cases nextConclusion : next.conclusion
    cases sourceConclusion : rule.conclusion
    simp only [nextConclusion, sourceConclusion] at name sameArgs sameResult ⊢
    simp_all only [Message.mk.injEq]
  · intro premise member
    exact premises premise member

theorem System.SemanticModel.supportEquiv {program : Program F} {source target : System F}
    (sourceModel : source.SemanticModel program) (targetModel : target.SemanticModel program) :
    source.SupportEquiv target :=
  ⟨sourceModel.supportRefines targetModel, targetModel.supportRefines sourceModel⟩

/-- The reference compiler discharges the same local interface required of
the optimized compiler. Static maps remain zero-premise rules. -/
theorem compile_semanticModel {program : Program F} {system : System F}
    (compiled : compile program = .ok system) : system.SemanticModel program := by
  have stages := compile_stages compiled
  have declarations := typecheck_declarations stages.1
  refine ⟨declarations, ?_, ?_, ?_⟩
  · intro rom rule signature found
    cases rule with
    | node chip row lookup valid =>
        obtain ⟨function, functionFound, lowered⟩ := compile_find_chip compiled lookup
        have interface := Compiler.lowerFunction_interface lowered
        have names : chip.name = row.chip := by simpa using List.find?_some lookup
        have sourceSignature : program.findSignature? chip.name = some ⟨function.params, function.result⟩ := by
          rw [names]
          exact Program.signature_of_function functionFound
        change program.findSignature? chip.name = some signature at found
        obtain rfl := Option.some.inj (found.symm.trans sourceSignature)
        exact interface.2.2
    | table message member =>
        obtain ⟨args, constant, arguments, decoded, absent, looked⟩ := compile_map_spec compiled member
        obtain ⟨map, _, mapFound, _, _, _, _, typed⟩ := lookupMap_spec looked
        have signatureFound := Program.signature_of_map absent mapFound
        obtain rfl := Option.some.inj (found.symm.trans signatureFound)
        have resultType := (WireValue.decode_spec decoded).1
        simp only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] at typed
        exact resultType.symm.trans (by simpa using typed.1)
  · intro rom rule calls premises
    cases rule with
    | node chip row lookup valid =>
        obtain ⟨function, found, lowered⟩ := compile_find_chip compiled lookup
        have interface := Compiler.lowerFunction_interface lowered
        obtain ⟨args, result, arguments, decoded, body⟩ :=
          Compiler.lowerFunction_sound declarations stages.2.1 lowered valid premises
        refine ⟨args, result, arguments, decoded, _, _, ?_, body⟩
        have types : function.params.map Prod.snd = args.map Value.type := by
          rw [arguments.types]
          simpa only [Chip.receive, List.map_map, Function.comp_def, WireValue.type_map] using interface.2.1.symm
        apply prepareCall_of_types (fn := function) ?_ types arguments.wellFormed
        change program.findFunction? chip.name = some function
        rw [interface.1, findFunction_name found]
        exact found
    | table message member =>
        obtain ⟨args, constant, arguments, decoded, absent, looked⟩ := compile_map_spec compiled member
        refine ⟨args, constant.toValue, arguments, decoded, _, _, prepareCall_map absent looked, ?_⟩
        exact (ROMEvalExprWith.constant_iff constant).mpr rfl
  · intro rom calls sourceCalls typed callComplete name args result step
    obtain ⟨locals, body, prepared, evaluated⟩ := step
    rcases prepareCall_spec prepared with function | table
    · obtain ⟨function, found, types, formed, rfl, rfl⟩ := function
      obtain ⟨chip, lookup, lowered⟩ := compile_find_function compiled found
      have checked := typecheck_function stages.1 (List.mem_of_find?_eq_some found)
      obtain ⟨row, rowName, valid, arguments, decoded, premises⟩ :=
        Compiler.lowerFunction_complete declarations stages.2.1 lowered typed callComplete checked types formed evaluated
      have functionName := findFunction_name found
      have rowLookup : system.findChip? row.chip = some chip := by rw [rowName, functionName]; exact lookup
      exact ⟨.node chip row rowLookup valid, (Compiler.lowerFunction_interface lowered).1.trans functionName,
        arguments, decoded, premises⟩
    · obtain ⟨constant, _, looked, rfl, rfl⟩ := table
      obtain rfl := (ROMEvalExprWith.constant_iff constant).mp evaluated
      obtain ⟨wires, output, arguments, decoded, member⟩ := compile_map_lookup compiled looked
      exact ⟨.table ⟨name, wires, output⟩ member, rfl, arguments, decoded, by simp [RuleInstance.premises]⟩

end Aiur.Circuit
