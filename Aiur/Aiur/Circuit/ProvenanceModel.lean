import Aiur.Circuit.SemanticMemory
import Aiur.Memory.WireProvenance

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F]

/-- Local compiler correctness from canonical arguments with store provenance.
Return canonicality is a conclusion. The ROM need only be functional; unused
cells may be malformed. Completeness remains unconditional. -/
structure System.ProvenanceModel (program : Program F) (system : System F) : Prop where
  declarations : checkDeclarations program.enums = .ok ()
  argumentTypes : ∀ rom (rule : RuleInstance system rom) signature,
    program.findSignature? rule.conclusion.channel = some signature →
    rule.conclusion.args.map WireValue.type = signature.params.map Prod.snd
  resultType : ∀ rom (rule : RuleInstance system rom) signature,
    program.findSignature? rule.conclusion.channel = some signature →
    rule.conclusion.result.type = signature.result
  sound : ∀ rom, rom.Valid → ∀ (rule : RuleInstance system rom) (calls : Aiur.CallRelation F),
    (∀ premise ∈ rule.premises, ∀ args,
      DecodesValues program.enums premise.args args →
      (∀ value ∈ args, (rom.decode program.enums).Provenance value) →
      ∃ result, premise.result.decode program.enums = some result ∧ calls premise.channel args result) →
    (∀ name args result, calls name args result →
      (∀ value ∈ args, (rom.decode program.enums).Provenance value) →
      (rom.decode program.enums).Provenance result) →
    ∀ args, DecodesValues program.enums rule.conclusion.args args →
      (∀ value ∈ args, (rom.decode program.enums).Provenance value) →
      ∃ result, rule.conclusion.result.decode program.enums = some result ∧
        CallStep program rom calls rule.conclusion.channel args result ∧
        (rom.decode program.enums).Provenance result
  complete : ∀ rom (calls : CallRelation F) (sourceCalls : Aiur.CallRelation F),
    CallsTyped program sourceCalls → Compiler.CallsComplete program.enums sourceCalls calls →
    ∀ name args result, CallStep program rom sourceCalls name args result →
    ∃ rule : RuleInstance system rom, rule.conclusion.channel = name ∧
      DecodesValues program.enums rule.conclusion.args args ∧
      rule.conclusion.result.decode program.enums = some result ∧
      ∀ premise ∈ rule.premises, calls premise.channel premise.args premise.result

variable {program : Program F} {system : System F} {rom : WireROM F}

/-- Canonical arguments and store provenance flow down the finite call tree;
canonical results and source evaluation flow back up. No return encoding is
assumed to decode in this induction. -/
theorem System.ProvenanceModel.derivation_sound (model : system.ProvenanceModel program)
    (valid : rom.Valid) {message : Message F} (tree : Derivation system rom message)
    {args : List (Value F)} (arguments : DecodesValues program.enums message.args args)
    (trusted : ∀ value ∈ args, (rom.decode program.enums).Provenance value) :
    ∃ result, message.result.decode program.enums = some result ∧
      ROMEvalCall (rom.decode program.enums) program message.channel args result ∧
      (rom.decode program.enums).Provenance result := by
  suffices ∀ args, DecodesValues program.enums message.args args →
      (∀ value ∈ args, (rom.decode program.enums).Provenance value) →
      ∃ result, message.result.decode program.enums = some result ∧
        ROMEvalCall (rom.decode program.enums) program message.channel args result ∧
        (rom.decode program.enums).Provenance result from this args arguments trusted
  clear arguments trusted args
  induction tree using Derivation.rec
    (motive_2 := fun messages _ => ∀ message ∈ messages, ∀ args,
      DecodesValues program.enums message.args args →
      (∀ value ∈ args, (rom.decode program.enums).Provenance value) →
      ∃ result, message.result.decode program.enums = some result ∧
        ROMEvalCall (rom.decode program.enums) program message.channel args result ∧
        (rom.decode program.enums).Provenance result) with
  | node chip row lookup rowValid children ih =>
      intro args arguments trusted
      obtain ⟨result, decoded, ⟨locals, body, prepared, evaluated⟩, resultTrusted⟩ :=
        model.sound rom valid (.node chip row lookup rowValid)
          (ROMEvalCall (rom.decode program.enums) program) (by
            intro premise member args arguments trusted
            obtain ⟨value, decoded, evaluated, _⟩ := ih premise member args arguments trusted
            exact ⟨value, decoded, evaluated⟩)
          (fun _ _ _ evaluated trusted => evaluated.provenance (WireROM.decode_valid valid) trusted)
          args arguments trusted
      exact ⟨result, decoded, .intro prepared evaluated.toEvalExpr, resultTrusted⟩
  | table member =>
      intro args arguments trusted
      obtain ⟨result, decoded, ⟨locals, body, prepared, evaluated⟩, resultTrusted⟩ :=
        model.sound rom valid (.table _ member) (ROMEvalCall (rom.decode program.enums) program)
          (by simp [RuleInstance.premises])
          (fun _ _ _ evaluated trusted => evaluated.provenance (WireROM.decode_valid valid) trusted)
          args arguments trusted
      exact ⟨result, decoded, .intro prepared evaluated.toEvalExpr, resultTrusted⟩
  | nil => simp_all
  | cons _ _ head tail =>
      rename_i message member args arguments trusted
      rcases List.mem_cons.mp member with rfl | member
      · exact head args arguments trusted
      · exact tail message member args arguments trusted

theorem System.ProvenanceModel.sound_encoded (model : system.ProvenanceModel program)
    (valid : rom.Valid) {name : String} {wires : List (WireValue F)} {output : WireValue F}
    (derived : CircuitEvaluates system rom name wires output)
    {args : List (Value F)} {result : Value F}
    (arguments : DecodesValues program.enums wires args) (decoded : output.decode program.enums = some result)
    (trusted : ∀ value ∈ args, (rom.decode program.enums).Provenance value) :
    ROMEvalCall (rom.decode program.enums) program name args result := by
  obtain ⟨tree⟩ := derived
  obtain ⟨otherResult, otherDecoded, evaluated, _⟩ := model.derivation_sound valid tree arguments trusted
  have sameResult := Option.some.inj (decoded.symm.trans otherDecoded)
  subst otherResult
  exact evaluated

/-- Validated pointer-free public inputs start the induction. The decoded
return is a conclusion, not a public-input assumption. -/
theorem System.ProvenanceModel.derivation_evaluates (model : system.ProvenanceModel program)
    (valid : rom.Valid) {message : Message F} (free : message.PublicArguments program.enums)
    (canonical : ∃ args, DecodesValues program.enums message.args args)
    (tree : Derivation system rom message) : message.Evaluates program rom := by
  obtain ⟨args, arguments⟩ := canonical
  have trusted : ∀ value ∈ args, (rom.decode program.enums).Provenance value := by
    intro value member
    have typeMember : value.type ∈ message.args.map WireValue.type := by
      rw [← arguments.types]
      exact List.mem_map.mpr ⟨value, member, rfl⟩
    obtain ⟨wire, wireMember, same⟩ := List.mem_map.mp typeMember
    exact .of_pointerFree value
      (Value.pointerFree_of_type (same ▸ free wire wireMember) (arguments.wellFormed value member))
  obtain ⟨result, decoded, evaluated, _⟩ := model.derivation_sound valid tree arguments trusted
  exact ⟨args, result, arguments, decoded, evaluated⟩

theorem System.ProvenanceModel.calls_typed (model : system.ProvenanceModel program) :
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

theorem System.ProvenanceModel.calls_complete (model : system.ProvenanceModel program) :
    Compiler.CallsComplete program.enums (EncodedEvaluates program.enums system rom)
      (CircuitEvaluates system rom) := by
  intro name args result evaluated wires output arguments decoded
  obtain ⟨oldWires, oldOutput, oldArguments, oldDecoded, derived⟩ := evaluated
  have sameArgs := arguments.wires_unique model.declarations oldArguments
  have sameResult := WireValue.decode_injective model.declarations decoded oldDecoded
  simpa only [sameArgs, sameResult] using derived

theorem System.ProvenanceModel.evaluation_complete (model : system.ProvenanceModel program)
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

theorem System.ProvenanceModel.complete_encoded (model : system.ProvenanceModel program)
    {name : String} {args : List (Value F)} {result : Value F}
    (evaluated : ROMEvalCall (rom.decode program.enums) program name args result)
    {wires : List (WireValue F)} {output : WireValue F}
    (arguments : DecodesValues program.enums wires args) (decoded : output.decode program.enums = some result) :
    CircuitEvaluates system rom name wires output :=
  model.calls_complete name args result (model.evaluation_complete evaluated) wires output arguments decoded

theorem System.ProvenanceModel.evaluates_iff (model : system.ProvenanceModel program)
    (valid : rom.Valid) {name : String} {args : List (Value F)} {result : Value F}
    (trusted : ∀ value ∈ args, (rom.decode program.enums).Provenance value) :
    ROMEvalCall (rom.decode program.enums) program name args result ↔
      EncodedEvaluates program.enums system rom name args result := by
  refine ⟨model.evaluation_complete, ?_⟩
  rintro ⟨wires, output, arguments, decoded, derived⟩
  exact model.sound_encoded valid derived arguments decoded trusted

/-- A compiler that validates every read refines a compiler whose completeness
uses the same source steps, including for cyclic memoized graphs. -/
theorem System.SemanticModel.supportRefinesProvenance {source target : System F}
    (sourceModel : source.SemanticModel program) (targetModel : target.ProvenanceModel program) :
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

private theorem provenance_public_arguments {decls : Declarations}
    {wires : List (WireValue F)} {values : List (Value F)}
    (arguments : DecodesValues decls wires values)
    (free : ∀ value ∈ values, value.type.pointerFree decls = true) :
    ∀ wire ∈ wires, wire.type.pointerFree decls = true := by
  induction arguments with
  | nil => simp
  | @cons wire value wires values head tail ih =>
      have headFree := free value (by simp)
      rw [(WireValue.decode_spec head).1] at headFree
      simpa using And.intro headFree (ih (fun v h => free v (by simp [h])))

/-- Heap completeness only uses local compiler correctness. Addresses may be
chosen freely, provided distinct allocated cells have distinct field addresses. -/
theorem System.ProvenanceModel.heap_complete (model : system.ProvenanceModel program)
    (checked : typecheck program = .ok ()) (tags : program.enums.tagsValid F = true)
    (enums : system.enums = program.enums)
    {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
    (entry : checkEntry program name = .ok ()) (evaluated : EvalFn program name args [] value heap)
    (encode : Nat → F)
    (distinct : ∀ i j, i < heap.length → j < heap.length → encode i = encode j → i = j) :
    EncodedEntryDerives system name (entryValues args) (value.mapAddress encode) := by
  have free := evaluated.public_pointerFree entry
  have heapGood := (evaluated.heap_good checked (by simp [Heap.Good])
    (fun arg member => Value.pointerNames_of_free (free arg member))).2
  let table := ROM.ofHeap heap encode
  have good := ROM.ofHeap_good heapGood encode
  have decodeTable := ROM.decode_encode model.declarations tags good
  have body := evaluated.toROM (ROM.ofHeap_cells heap encode)
  have encodedBody : ROMEvalCall ((table.encode program.enums).decode program.enums) program name
      (args.map (Value.mapAddress encode)) (value.mapAddress encode) := by
    rw [decodeTable]; exact body
  obtain ⟨wires, output, arguments, decoded, derives⟩ := model.evaluation_complete encodedBody
  rw [entryValues_eq free encode] at arguments
  have argsFree : ∀ arg ∈ entryValues args, arg.type.pointerFree program.enums = true := by
    intro arg member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    simpa using (evaluated.publicArguments entry source sourceMember).1
  have tableValid := ROM.encode_valid model.declarations good (ROM.ofHeap_valid heap encode distinct)
  refine ⟨wires, output, ?_, ?_, ?_⟩
  · simpa only [enums] using arguments
  · simpa only [enums] using decoded
  · refine ⟨?_, ?_, table.encode program.enums, tableValid, derives⟩
    · exact ⟨by simpa only [enums] using arguments.each,
        by simpa only [enums] using
          (show ∃ value, output.decode program.enums = some value from ⟨_, decoded⟩)⟩
    · simpa only [enums, Message.PublicArguments] using provenance_public_arguments arguments argsFree

/-- The validated function interface establishes public input types before
provenance is used; this does not assume the desired evaluation judgment. -/
theorem System.ProvenanceModel.publicArguments (model : system.ProvenanceModel program)
    {message : Message F} (entry : checkEntry program message.channel = .ok ())
    (derived : Derives system rom message) : message.PublicArguments program.enums := by
  obtain ⟨tree⟩ := derived
  obtain ⟨rule, _, same⟩ := tree.root_instance
  obtain ⟨signature, found, free⟩ := (checkEntry_ok program message.channel).mp entry
  have types := model.argumentTypes rom rule signature (by simpa only [same] using found)
  rw [same] at types
  intro wire member
  apply free wire.type
  rw [← types]
  exact List.mem_map.mpr ⟨wire, member, rfl⟩

theorem System.ProvenanceModel.heap_sound (model : system.ProvenanceModel program)
    (valid : rom.Valid) {name : String} {args : List (SourceValue F)} {result : Value F}
    (entry : checkEntry program name = .ok ()) {wires : List (WireValue F)} {output : WireValue F}
    (derived : CircuitEvaluates system rom name wires output)
    (arguments : DecodesValues program.enums wires (entryValues args))
    (decoded : output.decode program.enums = some result) :
    ∃ source heap, EvalFn program name args [] source heap ∧
      Represents (rom.decode program.enums) heap source result := by
  have publicArgs := model.publicArguments entry derived
  have encodedFree : ∀ value ∈ entryValues args, value.pointerFree = true := by
    intro value member
    have typeMember : value.type ∈ wires.map WireValue.type := by
      rw [← arguments.types]
      exact List.mem_map.mpr ⟨value, member, rfl⟩
    obtain ⟨wire, wireMember, same⟩ := List.mem_map.mp typeMember
    exact Value.pointerFree_of_type (same ▸ publicArgs wire wireMember) (arguments.wellFormed value member)
  have trusted : ∀ value ∈ entryValues args, (rom.decode program.enums).Provenance value :=
    fun value member => .of_pointerFree value (encodedFree value member)
  have evaluated := model.sound_encoded valid derived arguments decoded trusted
  have free : ∀ value ∈ args, value.pointerFree = true := by
    intro value member
    have formed := evaluated.publicArguments entry (value.mapAddress (fun _ => 0))
      (List.mem_map.mpr ⟨value, member, rfl⟩)
    exact Value.pointerFree_of_type (by simpa using formed.1) (by simpa using formed.2)
  have relatedArgs : RepresentsArgs (rom.decode program.enums) [] args (entryValues args) := by
    apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun value member => Represents.of_pointerFree value (free value member) _)
  obtain ⟨source, heap, evaluated, _, related⟩ := evaluated.realize (WireROM.decode_valid valid) relatedArgs
  exact ⟨source, heap, evaluated, related⟩

end Aiur.Circuit
