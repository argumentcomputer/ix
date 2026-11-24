import Aiur.Optimized.SemanticModel
import Aiur.Optimized.Physical
import Aiur.Optimized.Depth.StructuralSound

/-!
# Local soundness for exempt SCCs, and physical rows seen as source rows

`compile_structural_sound` is the row-local soundness of the compiled circuits
(`compile_semanticModel`, third clause) with the call premise asked only of the calls the
static analysis of the function body allows (`Depth.Structural.Allowed`): the calls it lists,
with arguments that satisfy their static relations to the row's own arguments.

The memo checker runs on the physical circuits: interfaces type-erased, then deduplicated
twice. `Physical.Prepared.rule_view` reads a physical row back as a row of the circuits before
any of that (`artifact.unmerged`), at any source claim that translates to its conclusion.
One physical row has one view per function that shares its circuit.
-/

namespace Aiur.Optimized

open Circuit

variable {F : Type} [Field F] [DecidableEq F]

/-- Row-local soundness with the call premise restricted to the calls the static analysis
allows. A fixed-table row has no premises. -/
theorem compile_structural_sound {program : Program F} {entries : List String} {config : Config}
    {artifact : Artifact F} (compiled : compile program entries config = .ok artifact)
    (rom : WireROM F) (romValid : rom.Valid) (rule : RuleInstance artifact.unmerged rom)
    (calls : Aiur.CallRelation F) (args : List (Value F))
    (arguments : DecodesValues program.enums rule.conclusion.args args)
    (trusted : ∀ value ∈ args, (rom.decode program.enums).Provenance value)
    (premises : ∀ premise ∈ rule.premises, ∀ values,
      DecodesValues program.enums premise.args values →
      (∀ value ∈ values, (rom.decode program.enums).Provenance value) →
      (∀ function, program.findFunction? rule.conclusion.channel = some function →
        Depth.Structural.Allowed (rom.decode program.enums) args (Depth.Structural.calls function)
          premise.channel values) →
      ∃ result, premise.result.decode program.enums = some result ∧
        calls premise.channel values result)
    (callProvenance : ∀ name values result, calls name values result →
      (∀ value ∈ values, (rom.decode program.enums).Provenance value) →
      (rom.decode program.enums).Provenance result) :
    ∃ result, rule.conclusion.result.decode program.enums = some result ∧
      CallStep program rom calls rule.conclusion.channel args result ∧
      (rom.decode program.enums).Provenance result := by
  have stages := compile_stages compiled
  have declarations := typecheck_declarations stages.1
  cases rule with
  | node chip row lookup valid =>
      obtain ⟨function, found, lowered⟩ := compile_find_chip compiled lookup
      have interface := lowered.interface
      obtain ⟨logical, layout, lowered, laidOut, rfl⟩ := lowered
      have functionFound : program.findFunction? layout.chip.name = some function := by
        rw [interface.1, Circuit.findFunction_name found]
        exact found
      obtain ⟨assignment, logicalValid, conclusion, requires⟩ :=
        (layOut_correct laidOut rom (layout.chip.receive row) (layout.chip.premises row)).mpr
          ⟨{row with chip := layout.chip.name}, rfl, valid, rfl, rfl⟩
      have logicalArguments : DecodesValues program.enums (logical.conclusion assignment).args args := by
        simpa only [conclusion, Circuit.RuleInstance.conclusion] using arguments
      obtain ⟨result, decoded, evaluated, resultTrusted⟩ :=
        Compiler.function_sound declarations stages.2.1 lowered romValid (sourceCalls := calls)
          (Depth.Structural.guard program.enums (rom.decode program.enums) calls args
            (Depth.Structural.calls function)) logicalValid (by
            intro premise member values argumentDecode trusted allowed
            refine premises premise
              (by simpa only [requires, Circuit.RuleInstance.premises] using member)
              values argumentDecode trusted ?_
            intro other otherFound
            obtain rfl := Option.some.inj (otherFound.symm.trans functionFound)
            exact allowed)
          callProvenance logicalArguments trusted (Depth.Structural.guard_body function args)
      rw [conclusion] at decoded
      refine ⟨result, decoded, ⟨_, _, ?_, evaluated⟩, resultTrusted⟩
      have types : function.params.map Prod.snd = args.map Value.type := by
        rw [arguments.types]
        simpa only [Circuit.RuleInstance.conclusion, Circuit.Chip.receive, List.map_map,
          Function.comp_def, WireValue.type_map] using interface.2.1.symm
      exact prepareCall_of_types (fn := function) functionFound types arguments.wellFormed
  | table message member =>
      obtain ⟨mapArgs, constant, mapArguments, decoded, absent, looked⟩ := compile_map_spec compiled member
      have same := arguments.unique mapArguments
      subst mapArgs
      exact ⟨constant.toValue, decoded,
        ⟨_, _, prepareCall_map absent looked, (ROMEvalExprWith.constant_iff constant).mpr rfl⟩,
        .of_pointerFree constant.toValue (Constant.toValue_pointerFree constant)⟩

namespace Physical

/-- A claim of the circuits before deduplication, as the physical circuits state it: renamed
to its representative, its interface erased, renamed again. -/
def Prepared.translate {artifact : Artifact F} (prepared : Prepared artifact) (claim : Message F) :
    Message F :=
  (Erasure.message artifact.system (claim.rename (Dedup.rename artifact.representatives))).rename
    (Dedup.rename prepared.merged.representatives)

/-- The claim keeps its static interface through the first deduplication. -/
def Prepared.Signed {artifact : Artifact F} (_ : Prepared artifact) (claim : Message F) : Prop :=
  Erasure.Signed artifact.system (claim.rename (Dedup.rename artifact.representatives))

/-- A row of the type-erased circuits, seen at a signed claim that erases to its conclusion:
a row of the typed circuits with that conclusion, whose premises are signed and erase to the
physical row's premises, in order. -/
theorem _root_.Aiur.Circuit.Erasure.rule_backward (source : System F)
    (compatible : Erasure.Compatible source)
    (separated : ∀ claim, source.MapClaim claim → source.findChip? claim.channel = none)
    {rom : WidthROM F} (rule : RuleInstance (Erasure.system source) (Erasure.rawROM rom))
    (claim : Message F) (signed : Erasure.Signed source claim)
    (same : Erasure.message source claim = rule.conclusion) :
    ∃ previous : RuleInstance source (Erasure.typedROM source rom),
      previous.conclusion = claim ∧
      previous.premises.map (Erasure.message source) = rule.premises ∧
      ∀ premise ∈ previous.premises, Erasure.Signed source premise := by
  cases rule with
  | node next row found valid =>
      have lookup := found
      rw [Erasure.system_findChip] at lookup
      obtain ⟨original, originalFound, rfl⟩ := Option.map_eq_some_iff.mp lookup
      change Erasure.message source claim = (Erasure.chip source original).receive row at same
      have names : claim.channel = original.name := by
        simpa [Chip.receive, Erasure.chip] using congrArg Message.channel same
      have foundClaim : source.findChip? claim.channel = some original := by
        rw [names, System.findChip_name originalFound]; exact originalFound
      have sameFlat : Erasure.flatten claim = Erasure.flatten (original.receive row) := by
        simpa only [Erasure.message, Erasure.dynamic, foundClaim, Option.isSome_some, ↓reduceIte,
          Erasure.chip_receive] using same
      have equal : claim = original.receive row := Erasure.flatten_injective
        ((signed original foundClaim).trans (Erasure.receive_shape original row).symm) sameFlat
      have member := List.mem_of_find?_eq_some originalFound
      refine ⟨.node original row originalFound
        ((Erasure.chip_validRow source compatible member rom row).mp valid), equal.symm,
        (Erasure.chip_premises source original row).symm, ?_⟩
      intro premise required
      exact Erasure.premise_signed source compatible member row required
  | table physical member =>
      change Erasure.message source claim = physical at same
      have names : claim.channel = physical.channel := by
        simpa using congrArg Message.channel same
      have fixed : Erasure.message source claim = claim := by
        simp [Erasure.message, Erasure.dynamic, names, separated physical member]
      rw [fixed] at same
      subst same
      exact ⟨.table claim member, rfl, rfl, by simp [RuleInstance.premises]⟩

omit [Field F] [DecidableEq F] in
/-- Two signed claims on one channel with one erasure are equal. -/
theorem _root_.Aiur.Circuit.Erasure.message_injective (source : System F) {first second : Message F}
    (channel : first.channel = second.channel) (firstSigned : Erasure.Signed source first)
    (secondSigned : Erasure.Signed source second)
    (same : Erasure.message source first = Erasure.message source second) : first = second := by
  cases found : source.findChip? first.channel with
  | none =>
      have other : source.findChip? second.channel = none := channel ▸ found
      simpa [Erasure.message, Erasure.dynamic, found, other] using same
  | some target =>
      have other : source.findChip? second.channel = some target := channel ▸ found
      have flat : Erasure.flatten first = Erasure.flatten second := by
        simpa [Erasure.message, Erasure.dynamic, found, other] using same
      exact Erasure.flatten_injective
        ((firstSigned target found).trans (secondSigned target other).symm) flat

@[simp] theorem Prepared.translate_channel {artifact : Artifact F} (prepared : Prepared artifact)
    (claim : Message F) : (prepared.translate claim).channel = prepared.representative claim.channel := by
  simp [Prepared.translate, Prepared.representative, Message.rename]

/-- A physical row, seen at a source claim that translates to its conclusion: a row of the
circuits before deduplication with that conclusion, whose premises translate to the physical
row's premises, in order. -/
theorem Prepared.rule_view {artifact : Artifact F} (prepared : Prepared artifact) {rom : WidthROM F}
    (rule : RuleInstance prepared.system (Erasure.rawROM rom)) (claim : Message F)
    (signed : prepared.Signed claim) (same : prepared.translate claim = rule.conclusion) :
    ∃ view : RuleInstance artifact.unmerged (Erasure.typedROM artifact.system rom),
      view.conclusion = claim ∧ view.premises.map prepared.translate = rule.premises ∧
      ∀ premise ∈ view.premises, prepared.Signed premise := by
  obtain ⟨erased, erasedConclusion, erasedPremises⟩ :=
    prepared.merged.certificate.ruleTranslation.backward (Erasure.rawROM rom) rule _ same
  obtain ⟨typed, typedConclusion, typedPremises, typedSigned⟩ :=
    Erasure.rule_backward artifact.system prepared.compatible (table_separated artifact) erased _
      signed erasedConclusion.symm
  obtain ⟨view, viewConclusion, viewPremises⟩ :=
    artifact.deduplication.ruleTranslation.backward (Erasure.typedROM artifact.system rom) typed
      claim typedConclusion.symm
  refine ⟨view, viewConclusion, ?_, ?_⟩
  · have composed : view.premises.map prepared.translate =
        (((view.premises.map (Message.rename (Dedup.rename artifact.representatives))).map
          (Erasure.message artifact.system)).map
          (Message.rename (Dedup.rename prepared.merged.representatives))) := by
      simp only [List.map_map]
      rfl
    rw [composed, viewPremises, typedPremises]
    exact erasedPremises
  · intro premise member
    exact typedSigned _ (viewPremises ▸ List.mem_map.mpr ⟨premise, member, rfl⟩)

/-- Two signed claims on one channel that translate to one physical message are equal. -/
theorem Prepared.translate_injective {artifact : Artifact F} (prepared : Prepared artifact)
    {first second : Message F} (channel : first.channel = second.channel)
    (firstSigned : prepared.Signed first) (secondSigned : prepared.Signed second)
    (same : prepared.translate first = prepared.translate second) : first = second := by
  have extensional : ∀ left right : Message F, left.channel = right.channel →
      left.args = right.args → left.result = right.result → left = right := by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ rfl rfl rfl
    rfl
  have args := congrArg Message.args same
  have result := congrArg Message.result same
  have renamed : first.rename (Dedup.rename artifact.representatives) =
      second.rename (Dedup.rename artifact.representatives) :=
    Erasure.message_injective artifact.system
      (congrArg (Dedup.rename artifact.representatives) channel) firstSigned secondSigned
      (extensional _ _ (by simp only [Erasure.message_channel, Message.rename, channel])
        args result)
  have renamedArgs := congrArg Message.args renamed
  have renamedResult := congrArg Message.result renamed
  exact extensional _ _ channel renamedArgs renamedResult

end Physical

end Aiur.Optimized
