import Aiur.Correctness
import Aiur.Circuit.LocalWitness
import Aiur.Semantics.CallTypes

namespace Aiur

variable {F : Type} {rom : WireROM F}

/-- Derivability of the canonical flat encodings of a semantic call. -/
def Circuit.EncodedEvaluates [Field F] [DecidableEq F] (decls : Declarations)
    (system : Circuit.System F) (rom : WireROM F) (name : String)
    (args : List (Value F)) (result : Value F) : Prop :=
  ∃ wires output, DecodesValues decls wires args ∧ output.decode decls = some result ∧
    Circuit.CircuitEvaluates system rom name wires output

/-- Compiled premises carry the declared result type and a well-formed nominal value. -/
theorem circuit_calls_typed [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F} (compiled : Circuit.compile program = .ok system) :
    CallsTyped program (Circuit.EncodedEvaluates program.enums system rom) := by
  intro name args result derives fn found
  obtain ⟨wires, output, _, decoded, ⟨tree⟩⟩ := derives
  cases tree with
  | node chip row lookup valid children =>
      obtain ⟨source, sourceFound, lowered⟩ := Circuit.compile_find_chip compiled lookup
      have names : chip.name = row.chip := by simpa using List.find?_some lookup
      change program.findSignature? chip.name = some fn at found
      have sourceSignature : program.findSignature? chip.name = some ⟨source.params, source.result⟩ := by
        rw [names]
        exact Program.signature_of_function sourceFound
      have same := Option.some.inj (found.symm.trans sourceSignature)
      subst fn
      refine ⟨?_, (WireValue.decode_spec decoded).2.1⟩
      exact (WireValue.decode_spec decoded).1.trans (by
        simpa only [Circuit.Chip.receive, WireValue.type_map] using
          (Circuit.Compiler.lowerFunction_interface lowered).2.2)
  | table member =>
      obtain ⟨_, constant, _, resultDecoded, absent, looked⟩ := Circuit.compile_map_spec compiled member
      have same := Option.some.inj (decoded.symm.trans resultDecoded)
      subst result
      obtain ⟨map, _, mapFound, _, _, _, _, typed⟩ := lookupMap_spec looked
      have signature := Program.signature_of_map absent mapFound
      have sameSignature := Option.some.inj (found.symm.trans signature)
      subst fn
      simp only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] at typed
      exact ⟨by simpa using typed.1, by simpa using typed.2⟩

theorem circuit_calls_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F} (compiled : Circuit.compile program = .ok system) :
    Circuit.Compiler.CallsComplete program.enums (Circuit.EncodedEvaluates program.enums system rom)
      (Circuit.CircuitEvaluates system rom) := by
  intro name args result evaluated wires output arguments decoded
  obtain ⟨otherArgs, otherResult, otherArguments, otherDecoded, derived⟩ := evaluated
  have checked := typecheck_declarations (Circuit.compile_stages compiled).1
  have sameArgs := arguments.wires_unique checked otherArguments
  have sameResult := WireValue.decode_injective checked decoded otherDecoded
  simpa only [sameArgs, sameResult] using derived

/-- Every finite ROM evaluation produces a closed derivation of its canonical encodings. -/
theorem evaluation_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (Value F)} {result : Value F}
    (evaluated : ROMEvalCall (rom.decode program.enums) program name args result) :
    Circuit.EncodedEvaluates program.enums system rom name args result := by
  have stages := Circuit.compile_stages compiled
  have declarations := typecheck_declarations stages.1
  induction evaluated using ROMEvalCall.rec
    (motive_1 := fun locals expr value _ =>
      ROMEvalExprWith program.enums (rom.decode program.enums) (Circuit.EncodedEvaluates program.enums system rom) locals expr value)
    (motive_2 := fun locals exprs values _ =>
      ROMEvalArgsWith program.enums (rom.decode program.enums) (Circuit.EncodedEvaluates program.enums system rom) locals exprs values) with
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
      rcases prepareCall_spec prepared with function | table
      · obtain ⟨fn, lookup, types, formed, rfl, rfl⟩ := function
        obtain ⟨chip, found, lowered⟩ := Circuit.compile_find_function compiled lookup
        have checked := typecheck_function stages.1 (List.mem_of_find?_eq_some lookup)
        obtain ⟨row, rowName, valid, arguments, decoded, premises⟩ := Circuit.Compiler.lowerFunction_complete
          declarations stages.2.1 lowered (circuit_calls_typed compiled) (circuit_calls_complete compiled)
          checked types formed bodyIH
        have name := Circuit.findFunction_name lookup
        have rowLookup : system.findChip? row.chip = some chip := by rw [rowName, name]; exact found
        obtain ⟨children⟩ := Circuit.derivations_nonempty_iff.mpr premises
        have tree := Circuit.Derivation.node chip row rowLookup valid children
        refine ⟨(chip.receive row).args, (chip.receive row).result, arguments, decoded, ?_⟩
        have chipName := (Circuit.Compiler.lowerFunction_interface lowered).1.trans name
        simpa only [Circuit.Chip.receive, chipName, Circuit.CircuitEvaluates, Circuit.Derives] using Nonempty.intro tree
      · obtain ⟨constant, _, looked, rfl, rfl⟩ := table
        obtain rfl := (ROMEvalExprWith.constant_iff constant).mp bodyIH
        obtain ⟨wires, output, arguments, decoded, member⟩ := Circuit.compile_map_lookup compiled looked
        exact ⟨wires, output, arguments, decoded, ⟨.table member⟩⟩

/-- Completeness also holds for any supplied canonical encodings of the root values. -/
theorem evaluation_complete_encoded [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (Value F)} {result : Value F}
    (evaluated : ROMEvalCall (rom.decode program.enums) program name args result)
    {wires : List (WireValue F)} {output : WireValue F}
    (arguments : DecodesValues program.enums wires args) (decoded : output.decode program.enums = some result) :
    Circuit.CircuitEvaluates system rom name wires output :=
  circuit_calls_complete compiled name args result (evaluation_complete compiled evaluated) wires output arguments decoded

/-- The compiled rules preserve and reflect evaluation of nominal, canonically encoded values. -/
theorem compiler_correct [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (Value F)} {result : Value F} :
    ROMEvalCall (rom.decode program.enums) program name args result ↔
      Circuit.EncodedEvaluates program.enums system rom name args result := by
  refine ⟨evaluation_complete compiled, ?_⟩
  rintro ⟨_, _, arguments, decoded, derived⟩
  exact compiler_sound compiled derived arguments decoded

end Aiur
