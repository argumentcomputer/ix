import Aiur.Optimized.ProgramFacts
import Aiur.Circuit.MapFacts

namespace Aiur.Optimized

open Circuit

variable {F : Type}

set_option linter.unusedSimpArgs false

theorem compile_mapClaims [Field F] [DecidableEq F]
    {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}
    (compiled : compile program entries config = .ok artifact)
    (message : Message F) :
    artifact.unmerged.MapClaim message ↔ ∃ map ∈ program.maps, ∃ entry ∈ program.mapEntries map,
      encodeMapEntry program.enums map.name entry = some message := by
  rw [(compile_stages compiled).2.2.2.2.2]
  simp only [System.MapClaim, System.mapClaims, List.mem_flatMap, List.mem_filterMap]
  rfl

/-- A static leaf gives exactly the source lookup, including its canonical encodings. -/
theorem compile_map_spec [Field F] [DecidableEq F]
    {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}
    (compiled : compile program entries config = .ok artifact)
    {message : Message F} (member : artifact.unmerged.MapClaim message) :
    ∃ args constant, DecodesValues program.enums message.args args ∧
      message.result.decode program.enums = some constant.toValue ∧
      program.findFunction? message.channel = none ∧
      lookupMap program message.channel args = .ok constant := by
  obtain ⟨map, mapMember, entry, entryMember, encoded⟩ := (compile_mapClaims compiled message).mp member
  have stages := compile_stages compiled
  obtain ⟨name, arguments, result⟩ := encodeMapEntry_spec stages.2.1 encoded
  exact ⟨entry.args.map Constant.toValue, entry.result, arguments, result,
    by rw [name]; exact map_function_absent stages.1 mapMember,
    by rw [name]; exact lookupMap_of_entry stages.1 mapMember entryMember⟩

/-- Lookup succeeds only at one of the fixed, aligned rows of the compiled traces. -/
theorem compile_map_lookup [Field F] [DecidableEq F]
    {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}
    (compiled : compile program entries config = .ok artifact)
    {name : String} {args : List (Value F)} {constant : Constant F}
    (looked : lookupMap program name args = .ok constant) :
    ∃ wires output, DecodesValues program.enums wires args ∧
      output.decode program.enums = some constant.toValue ∧
      artifact.unmerged.MapClaim ⟨name, wires, output⟩ := by
  obtain ⟨map, key, found, _, formed, extracted, row, outputTyped⟩ := lookupMap_spec looked
  have mapped : map.name = name := by simpa using List.find?_some found
  have reconstructed := Value.toConstant_spec extracted
  cases key with
  | field x => simp [Constant.toValue, Value.mapAddress] at reconstructed
  | construct e c xs => simp [Constant.toValue, Value.mapAddress] at reconstructed
  | ptr _ address => exact Empty.elim address
  | tuple constants =>
      have same : constants.map (Constant.toValue (Address := F)) = args := by
        simpa only [show (Constant.toValue : Constant F → Value F F) = Value.mapAddress Empty.elim from rfl, Constant.toValue, Value.mapAddress, Value.tuple.injEq] using reconstructed
      let entry : MapEntry F := ⟨constants, constant⟩
      have argsGood : ∀ c ∈ constants, c.wellFormed program.enums = true := by
        intro c member
        have good := formed (Constant.toValue c) (by rw [← same]; exact List.mem_map.mpr ⟨c, member, rfl⟩)
        simpa using good
      have resultGood : constant.wellFormed program.enums = true := by
        simp only [Value.hasType, Bool.and_eq_true] at outputTyped
        exact outputTyped.2
      have stages := compile_stages compiled
      obtain ⟨message, encoded⟩ := encodeMapEntry_total (name := name)
        (typecheck_declarations stages.1) entry argsGood resultGood
      obtain ⟨messageName, arguments, result⟩ := encodeMapEntry_spec stages.2.1 encoded
      have claim : artifact.unmerged.MapClaim message := (compile_mapClaims compiled message).mpr
        ⟨map, List.mem_of_find?_eq_some found, entry, mapEntry_mem_iff.mpr row,
          by simpa only [mapped] using encoded⟩
      refine ⟨message.args, message.result, ?_, result, ?_⟩
      · simpa only [entry, same] using arguments
      · cases message
        simpa only [Message.mk.injEq] using (messageName ▸ claim)

end Aiur.Optimized
