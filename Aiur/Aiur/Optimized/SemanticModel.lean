import Aiur.Optimized.LocalCorrectness
import Aiur.Optimized.LocalWitness
import Aiur.Optimized.MapFacts
import Aiur.Circuit.ProvenanceModel

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

/-- Internal expressions preserve canonicality and store provenance. Only entry
arguments and fresh hints require validation. Physical layout preserves this
conditional local semantics. -/
theorem compile_semanticModel {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}
    (compiled : compile program entries config = .ok artifact) : artifact.unmerged.ProvenanceModel program := by
  have stages := compile_stages compiled
  have declarations := typecheck_declarations stages.1
  refine ⟨declarations, ?_, ?_, ?_, ?_⟩
  · intro rom rule signature found
    cases rule with
    | node chip row lookup valid =>
        obtain ⟨function, functionFound, lowered⟩ := compile_find_chip compiled lookup
        have names : chip.name = row.chip := by simpa using List.find?_some lookup
        have sourceSignature : program.findSignature? chip.name = some ⟨function.params, function.result⟩ := by
          rw [names]
          exact Program.signature_of_function functionFound
        change program.findSignature? chip.name = some signature at found
        obtain rfl := Option.some.inj (found.symm.trans sourceSignature)
        simpa only [Circuit.RuleInstance.conclusion, Circuit.Chip.receive, List.map_map,
          Function.comp_def, WireValue.type_map] using lowered.interface.2.1
    | table message member =>
        obtain ⟨args, constant, arguments, decoded, absent, looked⟩ := compile_map_spec compiled member
        obtain ⟨map, _, mapFound, types, _, _, _, _⟩ := lookupMap_spec looked
        have signatureFound := Program.signature_of_map absent mapFound
        obtain rfl := Option.some.inj (found.symm.trans signatureFound)
        exact arguments.types.symm.trans types.symm
  · intro rom rule signature found
    cases rule with
    | node chip row lookup valid =>
        obtain ⟨function, functionFound, lowered⟩ := compile_find_chip compiled lookup
        have names : chip.name = row.chip := by simpa using List.find?_some lookup
        have sourceSignature : program.findSignature? chip.name = some ⟨function.params, function.result⟩ := by
          rw [names]
          exact Program.signature_of_function functionFound
        change program.findSignature? chip.name = some signature at found
        obtain rfl := Option.some.inj (found.symm.trans sourceSignature)
        exact lowered.interface.2.2
    | table message member =>
        obtain ⟨args, constant, arguments, decoded, absent, looked⟩ := compile_map_spec compiled member
        obtain ⟨map, _, mapFound, _, _, _, _, typed⟩ := lookupMap_spec looked
        have signatureFound := Program.signature_of_map absent mapFound
        obtain rfl := Option.some.inj (found.symm.trans signatureFound)
        have resultType := (WireValue.decode_spec decoded).1
        simp only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] at typed
        exact resultType.symm.trans (by simpa using typed.1)
  · intro rom romValid rule calls premises callProvenance args arguments trusted
    cases rule with
    | node chip row lookup valid =>
        obtain ⟨function, found, lowered⟩ := compile_find_chip compiled lookup
        have interface := lowered.interface
        obtain ⟨logical, layout, lowered, laidOut, rfl⟩ := lowered
        obtain ⟨assignment, logicalValid, conclusion, requires⟩ :=
          (layOut_correct laidOut rom (layout.chip.receive row) (layout.chip.premises row)).mpr
            ⟨{row with chip := layout.chip.name}, rfl, valid, rfl, rfl⟩
        have logicalArguments : DecodesValues program.enums (logical.conclusion assignment).args args := by
          simpa only [conclusion, Circuit.RuleInstance.conclusion] using arguments
        obtain ⟨result, decoded, evaluated, resultTrusted⟩ :=
          Compiler.function_sound declarations stages.2.1 lowered romValid logicalValid (sourceCalls := calls) (by
            intro premise member values argumentDecode trusted
            exact premises premise (by simpa only [requires, Circuit.RuleInstance.premises] using member) values argumentDecode trusted)
            callProvenance logicalArguments trusted
        rw [conclusion] at decoded
        refine ⟨result, decoded, ⟨_, _, ?_, evaluated⟩, resultTrusted⟩
        have types : function.params.map Prod.snd = args.map Value.type := by
          rw [arguments.types]
          simpa only [Circuit.RuleInstance.conclusion, Circuit.Chip.receive, List.map_map, Function.comp_def, WireValue.type_map]
            using interface.2.1.symm
        apply prepareCall_of_types (fn := function) ?_ types arguments.wellFormed
        change program.findFunction? layout.chip.name = some function
        rw [interface.1, Circuit.findFunction_name found]
        exact found
    | table message member =>
        obtain ⟨mapArgs, constant, mapArguments, decoded, absent, looked⟩ := compile_map_spec compiled member
        have same := arguments.unique mapArguments
        subst mapArgs
        exact ⟨constant.toValue, decoded,
          ⟨_, _, prepareCall_map absent looked, (ROMEvalExprWith.constant_iff constant).mpr rfl⟩,
          .of_pointerFree constant.toValue (Constant.toValue_pointerFree constant)⟩
  · intro rom calls sourceCalls typed callComplete name args result step
    obtain ⟨locals, body, prepared, evaluated⟩ := step
    rcases prepareCall_spec prepared with function | table
    · obtain ⟨function, found, types, formed, rfl, rfl⟩ := function
      obtain ⟨chip, lookup, lowered⟩ := compile_find_function compiled found
      have interface := lowered.interface
      obtain ⟨logical, layout, lowered, laidOut, rfl⟩ := lowered
      have checked := typecheck_function stages.1 (List.mem_of_find?_eq_some found)
      obtain ⟨assignment, logicalValid, arguments, decoded, premises⟩ :=
        Compiler.function_complete declarations stages.2.1 lowered typed callComplete checked types formed evaluated
      obtain ⟨row, rowName, valid, conclusion, requires⟩ :=
        (layOut_correct laidOut rom (logical.conclusion assignment) (logical.premises assignment)).mp
          ⟨assignment, logicalValid, rfl, rfl⟩
      have functionName := Circuit.findFunction_name found
      have rowLookup : artifact.unmerged.findChip? row.chip = some layout.chip := by
        rw [rowName, interface.1, functionName]
        exact lookup
      refine ⟨.node layout.chip row rowLookup valid, interface.1.trans functionName, ?_, ?_, ?_⟩
      · simpa only [Circuit.RuleInstance.conclusion, conclusion] using arguments
      · simpa only [Circuit.RuleInstance.conclusion, conclusion] using decoded
      · simpa only [Circuit.RuleInstance.premises, requires] using premises
    · obtain ⟨constant, _, looked, rfl, rfl⟩ := table
      obtain rfl := (ROMEvalExprWith.constant_iff constant).mp evaluated
      obtain ⟨wires, output, arguments, decoded, member⟩ := compile_map_lookup compiled looked
      exact ⟨.table ⟨name, wires, output⟩ member, rfl, arguments, decoded,
        by simp [Circuit.RuleInstance.premises]⟩

/-- Selected entry chips validate every argument, including unused ones.
Internal chips rely on the caller's canonical-value invariant instead. -/
theorem compile_entry_arguments {program : Program F} {entries : List String} {config : Config}
    {artifact : Artifact F} (compiled : compile program entries config = .ok artifact)
    {rom : WireROM F} (rule : Circuit.RuleInstance artifact.unmerged rom)
    (entry : rule.conclusion.channel ∈ entries) :
    ∃ args, DecodesValues program.enums rule.conclusion.args args := by
  cases rule with
  | node chip row lookup valid =>
      obtain ⟨function, _, lowered⟩ := compile_find_chip compiled lookup
      have interface := lowered.interface
      obtain ⟨logical, layout, lowered, laidOut, rfl⟩ := lowered
      have selected : entries.contains function.name = true := by
        apply List.contains_iff_mem.mpr
        simpa only [Circuit.RuleInstance.conclusion, Circuit.Chip.receive, interface.1] using entry
      rw [selected] at lowered
      obtain ⟨assignment, logicalValid, conclusion, _⟩ :=
        (layOut_correct laidOut rom (layout.chip.receive row) (layout.chip.premises row)).mpr
          ⟨{row with chip := layout.chip.name}, rfl, valid, rfl, rfl⟩
      have stages := compile_stages compiled
      obtain ⟨args, decoded⟩ := Compiler.function_arguments_sound
        (typecheck_declarations stages.1) stages.2.1 lowered logicalValid
      exact ⟨args, by simpa only [conclusion, Circuit.RuleInstance.conclusion] using decoded⟩
  | table message member =>
      obtain ⟨args, _, arguments, _⟩ := compile_map_spec compiled member
      exact ⟨args, arguments⟩

end Aiur.Optimized
