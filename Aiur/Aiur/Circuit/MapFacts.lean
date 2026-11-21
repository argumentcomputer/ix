import Aiur.Circuit.CompileFacts
import Aiur.TableChecking
import Aiur.WireRelation
import Aiur.Memory.WireEncoding

namespace Aiur.Circuit

variable {F : Type}

set_option linter.unusedSimpArgs false

theorem compile_mapClaims [Field F] [DecidableEq F]
    {program : Program F} {system : System F} (compiled : compile program = .ok system)
    (message : Message F) :
    system.MapClaim message ↔ ∃ map ∈ program.maps, ∃ entry ∈ program.mapEntries map,
      encodeMapEntry program.enums map.name entry = some message := by
  have stages := compile_stages compiled
  simp only [System.MapClaim, System.mapClaims, stages.2.2.2.1,
    stages.2.2.2.2.1, stages.2.2.2.2.2, List.mem_flatMap, List.mem_filterMap]
  rfl

theorem encodeMapEntry_spec [Field F] [DecidableEq F] {decls : Declarations}
    (tags : decls.tagsValid F = true) {name : String} {entry : MapEntry F} {message : Message F}
    (encoded : encodeMapEntry decls name entry = some message) :
    message.channel = name ∧ DecodesValues decls message.args (entry.args.map Constant.toValue) ∧
      message.result.decode decls = some entry.result.toValue := by
  unfold encodeMapEntry at encoded
  obtain ⟨wires, arguments, rest⟩ := Option.bind_eq_some_iff.mp encoded
  obtain ⟨output, result, finished⟩ := Option.bind_eq_some_iff.mp rest
  cases finished
  refine ⟨rfl, ?_, Value.decode_encode result (fun _ => Declarations.layout_tagSafe tags)⟩
  have related := StaticList.mapM_some_iff.mp arguments
  apply List.forall₂_map_right_iff.mpr
  exact related.flip.imp (fun _ _ head =>
    Value.decode_encode head (fun _ => Declarations.layout_tagSafe tags))

theorem encodeMapEntry_total [Field F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) (entry : MapEntry F)
    (argsGood : ∀ arg ∈ entry.args, arg.wellFormed decls = true)
    (resultGood : entry.result.wellFormed decls = true) :
    ∃ message, encodeMapEntry decls name entry = some message := by
  have values (items : List (Constant F)) (good : ∀ arg ∈ items, arg.wellFormed decls = true) :
      ∃ wires, items.mapM (fun arg => arg.toValue.encode decls) = some wires := by
    induction items with
    | nil => exact ⟨[], rfl⟩
    | cons arg args ih =>
      obtain ⟨wire, encoded⟩ := Value.encode_total checked
        ⟨by simpa using good arg (by simp),
          Value.pointerNames_of_free (Constant.toValue_pointerFree arg)⟩
      obtain ⟨wires, rest⟩ := ih (fun arg h => good arg (by simp [h]))
      exact ⟨wire :: wires, by simp [List.mapM_cons, encoded, rest]⟩
  obtain ⟨wires, arguments⟩ := values entry.args argsGood
  obtain ⟨output, result⟩ := Value.encode_total checked
    ⟨by simpa using resultGood,
      Value.pointerNames_of_free (Constant.toValue_pointerFree entry.result)⟩
  exact ⟨⟨name, wires, output⟩, by simp [encodeMapEntry, arguments, result]⟩

/-- A static leaf gives exactly the source lookup, including its canonical encodings. -/
theorem compile_map_spec [Field F] [DecidableEq F]
    {program : Program F} {system : System F} (compiled : compile program = .ok system)
    {message : Message F} (member : system.MapClaim message) :
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
    {program : Program F} {system : System F} (compiled : compile program = .ok system)
    {name : String} {args : List (Value F)} {constant : Constant F}
    (looked : lookupMap program name args = .ok constant) :
    ∃ wires output, DecodesValues program.enums wires args ∧
      output.decode program.enums = some constant.toValue ∧
      system.MapClaim ⟨name, wires, output⟩ := by
  obtain ⟨map, key, found, _, formed, extracted, row, outputTyped⟩ := lookupMap_spec looked
  have mapped : map.name = name := by simpa using List.find?_some found
  have reconstructed := Value.toConstant_spec extracted
  cases key with
  | field x => simp [show (Constant.toValue : Constant F → Value F _) = Value.mapAddress Empty.elim from rfl, Constant.toValue, Value.mapAddress] at reconstructed
  | construct e c xs => simp [show (Constant.toValue : Constant F → Value F _) = Value.mapAddress Empty.elim from rfl, Constant.toValue, Value.mapAddress] at reconstructed
  | ptr _ address => exact Empty.elim address
  | tuple constants =>
      have same : constants.map (Constant.toValue (Address := F)) = args := by
        simpa only [show (Constant.toValue : Constant F → Value F _) = Value.mapAddress Empty.elim from rfl, Constant.toValue, Value.mapAddress, Value.tuple.injEq] using reconstructed
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
      have claim : system.MapClaim message := (compile_mapClaims compiled message).mpr
        ⟨map, List.mem_of_find?_eq_some found, entry, mapEntry_mem_iff.mpr row,
          by simpa only [mapped] using encoded⟩
      refine ⟨message.args, message.result, ?_, result, ?_⟩
      · simpa only [entry, same] using arguments
      · cases message
        simpa only [Message.mk.injEq] using (messageName ▸ claim)

end Aiur.Circuit
