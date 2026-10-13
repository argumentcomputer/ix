import Ix.CompileCert.PayloadArrays
import Ix.CompileCert.HeaderReading

/-! Primary-table wire preservation through actual recursor, constructor,
inductive and mutual payload compilation. These are successful-run operational
facts, independent of expression reading or metadata value correspondence. -/

namespace Ix.CompileCert.FamilyWire

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open EmissionWire (Safe Valid)

theorem Safe.withBlockEnv (update : BlockEnv → BlockEnv) {action : CompileM α} (safe : Safe action) :
    Safe (withBlockEnv update action) := fun context before valid output after ran =>
  safe (context.1, update context.2) before valid output after ran

theorem Safe.withCurrent (name : Name) {action : CompileM α} (safe : Safe action) :
    Safe (withCurrent name action) := Safe.withBlockEnv _ safe

theorem Safe.withUnivCtx (params : List Name) {action : CompileM α} (safe : Safe action) :
    Safe (withUnivCtx params action) :=
  EmissionWire.Safe.seq (EmissionWire.Safe.modify _ (fun _ => rfl)) (fun _ => Safe.withBlockEnv _ safe)

theorem Safe.takeArena : Safe takeArena := EmissionWire.Safe.modifyGet _ (fun _ => rfl)
theorem Safe.takeSharing : Safe takeMetaSharing := EmissionWire.Safe.modifyGet _ (fun _ => rfl)
theorem Safe.takeRefs : Safe takeMetaRefs := EmissionWire.Safe.modifyGet _ (fun _ => rfl)
theorem Safe.takeUnivs : Safe takeUnivPatches := EmissionWire.Safe.modifyGet _ (fun _ => rfl)
theorem Safe.clear : Safe clearExprCache := EmissionWire.Safe.modify _ (fun _ => rfl)
theorem Safe.reset : Safe resetArena := EmissionWire.Safe.modify _ (fun _ => rfl)
theorem Safe.mutNames : Safe getMutCtxAddrs := EmissionWire.Safe.seq EmissionWire.Safe.readBlock (fun _ => EmissionWire.Safe.pure _)

local macro "wire_metadata" : tactic => `(tactic|
  with_reducible repeat' first
    | exact Safe.takeArena
    | exact Safe.takeSharing
    | exact Safe.takeRefs
    | exact Safe.takeUnivs
    | exact Safe.clear
    | exact EmissionWire.Safe.checkedCount _ _
    | exact EmissionWire.Safe.checkedIndex _ _
    | exact EmissionWire.Safe.compileName _
    | exact EmissionWire.Safe.compileNames _
    | exact Safe.mutNames
    | exact EmissionWire.Safe.readBlock
    | exact EmissionWire.Safe.pure _
    | refine EmissionWire.Safe.seq ?_ (fun _ => ?_))

theorem Safe.rule (source : RecursorRule) : Safe (compileRecursorRule source) :=
  EmissionWire.Safe.seq (EmissionWire.Safe.expression _) fun _ =>
    EmissionWire.Safe.seq (EmissionWire.Safe.checkedCount _ _) fun _ => EmissionWire.Safe.pure _

theorem Safe.rules (sources : List RecursorRule) (initial : RecursorRuleCompileState) :
    Safe (compileRecursorRules sources initial) := by
  induction sources generalizing initial with
  | nil => exact EmissionWire.Safe.pure _
  | cons source rest ih =>
    rw [compileRecursorRules]
    exact EmissionWire.Safe.seq (Safe.rule source) (fun _ => ih _)

theorem Safe.finishRecursor (source : RecursorVal) (type : Ixon.Expr) (root : UInt64) (rules : RecursorRuleCompileState) :
    Safe (finishRecursorCompilation source type root rules) := by
  unfold finishRecursorCompilation
  wire_metadata

theorem Safe.recursor (source : RecursorVal) : Safe (compileRecursor source) := by
  apply Safe.withCurrent
  apply Safe.withUnivCtx
  exact EmissionWire.Safe.seq Safe.reset fun _ =>
    EmissionWire.Safe.seq (EmissionWire.Safe.expression _) fun type =>
      EmissionWire.Safe.seq (Safe.rules _ _) fun rules => Safe.finishRecursor source type.1 type.2 rules

theorem Safe.finishConstructor (source : ConstructorVal) (type : Ixon.Expr) (root : UInt64) :
    Safe (finishConstructorCompilation source type root) := by
  unfold finishConstructorCompilation
  wire_metadata

theorem Safe.constructor (source : ConstructorVal) : Safe (compileConstructor source) := by
  apply Safe.withCurrent
  exact EmissionWire.Safe.seq Safe.reset fun _ =>
    EmissionWire.Safe.seq (EmissionWire.Safe.expression _) fun type => Safe.finishConstructor source type.1 type.2

theorem Safe.inductiveMetadata : Safe takeInductiveTypeCompileMeta := by
  unfold takeInductiveTypeCompileMeta
  wire_metadata

theorem Safe.constructors (sources : List ConstructorVal) (initial : InductiveConstructorCompileState) :
    Safe (compileInductiveConstructors sources initial) := by
  induction sources generalizing initial with
  | nil => exact EmissionWire.Safe.pure _
  | cons source rest ih =>
    rw [compileInductiveConstructors]
    exact EmissionWire.Safe.seq (Safe.constructor source) (fun _ => ih _)

theorem Safe.finishInductive (source : InductiveVal) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Safe (finishInductiveCompilation source type root metadata constructors) := by
  unfold finishInductiveCompilation
  wire_metadata

theorem Safe.inductive (source : InductiveVal) (constructors : Array ConstructorVal) : Safe (compileInductive source constructors) := by
  apply Safe.withCurrent
  apply Safe.withUnivCtx
  exact EmissionWire.Safe.seq Safe.reset fun _ =>
    EmissionWire.Safe.seq (EmissionWire.Safe.expression _) fun type =>
      EmissionWire.Safe.seq Safe.inductiveMetadata fun metadata =>
        EmissionWire.Safe.seq (Safe.constructors _ _) fun ctors => Safe.finishInductive source type.1 type.2 metadata ctors

theorem Safe.finishInductiveData (source : Ind) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Safe (finishInductiveDataCompilation source type root metadata constructors) := by
  unfold finishInductiveDataCompilation
  wire_metadata

theorem Safe.inductiveData (source : Ind) : Safe (compileInductiveData source) := by
  apply Safe.withCurrent
  apply Safe.withUnivCtx
  exact EmissionWire.Safe.seq Safe.reset fun _ =>
    EmissionWire.Safe.seq (EmissionWire.Safe.expression _) fun type =>
      EmissionWire.Safe.seq Safe.inductiveMetadata fun metadata =>
        EmissionWire.Safe.seq (Safe.constructors _ _) fun ctors => Safe.finishInductiveData source type.1 type.2 metadata ctors

theorem Safe.member (source : MutConst) : Safe (compileMutConstMember source) := by
  cases source <;> unfold compileMutConstMember
  all_goals with_reducible repeat' first
    | exact Safe.inductiveData _
    | exact EmissionWire.Safe.definition _
    | exact Safe.recursor _
    | exact EmissionWire.Safe.pure _
    | apply Safe.withCurrent
    | refine EmissionWire.Safe.seq ?_ (fun _ => ?_)
    | unfold compileRecursorData

theorem Safe.equivalents (sources : List MutConst) (initial : MutConstCompileState) : Safe (compileEquivalentMutConsts sources initial) := by
  induction sources generalizing initial with
  | nil => exact EmissionWire.Safe.pure _
  | cons source rest ih =>
    rw [compileEquivalentMutConsts]
    exact EmissionWire.Safe.seq (Safe.member source) (fun _ => ih _)

theorem Safe.constClass (sources : List MutConst) (initial : MutConstCompileState) : Safe (compileMutConstClass sources initial) := by
  cases sources with
  | nil => exact EmissionWire.Safe.pure _
  | cons source rest => exact EmissionWire.Safe.seq (Safe.member source) (fun _ => Safe.equivalents rest _)

theorem Safe.classes (sources : List (List MutConst)) (initial : MutConstCompileState) : Safe (compileMutConstClasses sources initial) := by
  induction sources generalizing initial with
  | nil => exact EmissionWire.Safe.pure _
  | cons source rest ih =>
    rw [compileMutConstClasses]
    exact EmissionWire.Safe.seq (Safe.constClass source initial) (fun _ => ih _)

theorem Safe.mutConsts (sources : List (List MutConst)) : Safe (compileMutConsts sources) :=
  EmissionWire.Safe.seq (Safe.classes sources {}) (fun _ => EmissionWire.Safe.pure _)

theorem recursorBlock_codec (source : RecursorVal) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult) (valid : Valid context.1 before)
    (ran : rawRun (compileRecursorBlock source) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output := by
  rw [compileRecursorBlock] at ran
  obtain ⟨value, middle, compiled, finished⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have tables := (Safe.recursor source context before valid value middle compiled).1.2.1
  have header := PayloadArrays.recursor_compiled source context before value middle compiled
  exact (PayloadArrays.finish_shared_codec context (.recr value.1) value.2.1 middle after output header tables finished).2

theorem build_block_run (info : Ixon.ConstantInfo) (refs : Array Address) (univs : Array Ixon.Univ)
    (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (buildBlockConstant info refs univs) context before =
      (buildConstantWithSharing context.1.sharingLimits info refs univs, before) := by
  have readContext : rawRun (read : CompileM (CompileEnv × BlockEnv)) context before = (.ok context, before) := rfl
  simp only [buildBlockConstant, rawRun_bind, readContext]
  cases buildConstantWithSharing context.1.sharingLimits info refs univs <;> rfl

theorem finishInductive_codec (source : InductiveVal) (ind : Ixon.Inductive) (metadata : Ixon.ConstantMeta)
    (constructors : Array (Name × Ixon.ConstantMeta)) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult)
    (bounded : ind.ctors.size < UInt64.size) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (ran : rawRun (finishInductiveFamilyBlock source ind metadata constructors) context before = (.ok output, after)) :
    after = before ∧ Ix.Sharing.Verify.BlockResultCodecWF output := by
  unfold finishInductiveFamilyBlock at ran
  obtain ⟨count, middle, guarded, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have same := Interning.checkedTableCount_state "inductive constructors" source.ctors.size context before
  rw [guarded] at same
  dsimp only at same
  subst middle
  obtain ⟨pairCount, middle, pairGuarded, rest⟩ := PreseedReferences.bind_ok _ _ context before output after rest
  have pairSame := Interning.checkedTableCount_state "constructor projections" constructors.size context before
  rw [pairGuarded] at pairSame
  dsimp only at pairSame
  subst middle
  rw [rawRun_bind, rawRun_get] at rest
  obtain ⟨block, finalState, built, returned⟩ := PreseedReferences.bind_ok _ _ context before output after rest
  rw [DefinitionBlock.rawRun_timedC, build_block_run] at built
  have buildResult := congrArg Prod.fst built
  have buildState := congrArg Prod.snd built
  dsimp only at buildState
  subst finalState
  rw [rawRun_pure] at returned
  obtain ⟨values, states⟩ := Prod.mk.inj returned
  cases Except.ok.inj values
  have headers : Ix.Sharing.Verify.ConstantInfoHeaderWF (.muts #[.indc ind]) := by
    refine ⟨by change 1 < UInt64.size; decide, ?_⟩
    intro member present
    have memberEq : member = .indc ind := by simpa using present
    subst member
    exact bounded
  exact ⟨states.symm, Ix.Sharing.Verify.BlockResult.mk'_codecWF _ _ _
    (Ix.Sharing.Verify.buildConstantWithSharing_wireWF_headers headers tables buildResult)⟩

theorem inductiveFamilyBlock_codec (source : InductiveVal) (constructors : Array ConstructorVal) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult) (valid : Valid context.1 before)
    (ran : rawRun (compileInductiveFamilyBlock source constructors) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output := by
  rw [compileInductiveFamilyBlock] at ran
  obtain ⟨value, middle, compiled, finished⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have tables := (Safe.inductive source constructors context before valid value middle compiled).1.2.1
  have header := PayloadArrays.inductive_compiled source constructors context before value middle compiled
  exact (finishInductive_codec source value.1 value.2.1 value.2.2.1 context middle after output header tables finished).2

theorem seeded_valid (roots : Array (Expr × List Name)) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) : Valid context.1 after := by
  have prepared := PreseedState.preseed_ready_checked context roots bindings before after ready ran
  have wire := PreseedWire.preseed_wire_checked context roots before after tables widths ran
  have afterWidths : ReferenceWidths.LookupWidths context.1 after := by
    intro name address found
    rw [prepared.1.bindings, ← ready.bindings] at found
    exact widths name address found
  exact ⟨afterWidths, wire, prepared.2.1⟩

theorem recursorInfo_codec (source : RecursorVal) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileRecursorInfo source) context before = (.ok output, after)) : Ix.Sharing.Verify.BlockResultCodecWF output := by
  rw [compileRecursorInfo] at ran
  obtain ⟨done, middle, seeded, compiled⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  cases done
  exact recursorBlock_codec source context middle after output (seeded_valid _ context bindings before middle ready tables widths seeded) compiled

theorem inductiveFamilyInfo_codec (source : InductiveVal) (constructors : Array ConstructorVal) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileInductiveFamilyInfo source constructors) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output := by
  rw [compileInductiveFamilyInfo] at ran
  obtain ⟨done, middle, seeded, compiled⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  cases done
  exact inductiveFamilyBlock_codec source constructors context middle after output
    (seeded_valid _ context bindings before middle ready tables widths seeded) compiled

theorem find_state (name : Name) : UniversePipeline.Preserves id (findConst name) := by
  intro context before
  simp only [findConst, rawRun_bind, rawRun_read]
  cases context.1.env.get? name <;> rfl

theorem constructors_state (names : List Name) (initial : Array ConstructorVal) :
    UniversePipeline.Preserves id (collectInductiveConstructors names initial) := by
  induction names generalizing initial with
  | nil => exact UniversePipeline.Preserves.pure _ _
  | cons name rest ih =>
    rw [collectInductiveConstructors]
    apply UniversePipeline.Preserves.bind (find_state name)
    intro source
    cases source <;> first
      | exact ih _
      | exact UniversePipeline.Preserves.throw _ _

theorem inductiveInfo_codec (source : InductiveVal) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileInductiveInfo source) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output := by
  rw [compileInductiveInfo] at ran
  obtain ⟨constructors, middle, found, compiled⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have same := constructors_state source.ctors.toList #[] context before
  change (rawRun (lookupInductiveConstructors source) context before).2 = before at same
  rw [found] at same
  dsimp only at same
  subst middle
  exact inductiveFamilyInfo_codec source constructors
    (context.1, { context.2 with mutCtx := buildInductiveMutCtx source constructors }) bindings before after output ready tables widths compiled

theorem constructorInfo_codec (source : ConstructorVal) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileConstructorInfo source) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output := by
  rw [compileConstructorInfo] at ran
  obtain ⟨parent, middle, found, compiled⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have same := find_state source.induct context before
  rw [found] at same
  change middle = before at same
  subst middle
  cases parent <;> try cases compiled
  exact inductiveInfo_codec _ context bindings before after output ready tables widths compiled

theorem constant_recursor_codec (source : RecursorVal) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileConstantInfo (.recInfo source)) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output :=
  recursorInfo_codec source (DefinitionReading.singletonContext source.cnst.name context) bindings before after output ready tables widths ran

theorem constant_inductive_codec (source : InductiveVal) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output :=
  inductiveInfo_codec source (DefinitionReading.singletonContext source.cnst.name context) bindings before after output ready tables widths ran

theorem constant_constructor_codec (source : ConstructorVal) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileConstantInfo (.ctorInfo source)) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output :=
  constructorInfo_codec source (DefinitionReading.singletonContext source.cnst.name context) bindings before after output ready tables widths ran

theorem headerInfo_codec (source : HeaderEmission.Source) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (HeaderBlock.info source) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output := by
  rw [HeaderBlock.info_eq] at ran
  obtain ⟨done, middle, seeded, compiled⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  cases done
  exact HeaderBlock.block_wire source context middle after output
    (seeded_valid _ context bindings before middle ready tables widths seeded) compiled

/-- Main-block wire validity and actual byte decoding for every public
constant-dispatch kind. This does not claim source semantics, projection
correspondence or admission of the resulting declarations. -/
theorem constant_codec (source : ConstantInfo) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileConstantInfo source) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output := by
  cases source with
  | defnInfo value =>
    rw [DefinitionReading.constant_run (.defnInfo value) (definitionValData value) rfl] at ran
    exact (EmissionWire.compileDefinitionDataInfo_codec_checked (DefinitionReading.singletonContext value.cnst.name context)
      (definitionValData value) bindings before after ready tables widths output ran).2
  | thmInfo value =>
    rw [DefinitionReading.constant_run (.thmInfo value) (theoremValData value) rfl] at ran
    exact (EmissionWire.compileDefinitionDataInfo_codec_checked (DefinitionReading.singletonContext value.cnst.name context)
      (theoremValData value) bindings before after ready tables widths output ran).2
  | opaqueInfo value =>
    rw [DefinitionReading.constant_run (.opaqueInfo value) (opaqueValData value) rfl] at ran
    exact (EmissionWire.compileDefinitionDataInfo_codec_checked (DefinitionReading.singletonContext value.cnst.name context)
      (opaqueValData value) bindings before after ready tables widths output ran).2
  | axiomInfo value =>
    change rawRun (compileConstantInfo (HeaderReading.constant (.axio value))) context before = (.ok output, after) at ran
    rw [HeaderReading.constant_run] at ran
    exact headerInfo_codec (.axio value) (DefinitionReading.singletonContext value.cnst.name context) bindings before after output ready tables widths ran
  | quotInfo value =>
    change rawRun (compileConstantInfo (HeaderReading.constant (.quot value))) context before = (.ok output, after) at ran
    rw [HeaderReading.constant_run] at ran
    exact headerInfo_codec (.quot value) (DefinitionReading.singletonContext value.cnst.name context) bindings before after output ready tables widths ran
  | recInfo value => exact constant_recursor_codec value context bindings before after output ready tables widths ran
  | inductInfo value => exact constant_inductive_codec value context bindings before after output ready tables widths ran
  | ctorInfo value => exact constant_constructor_codec value context bindings before after output ready tables widths ran

theorem mutualPayload_codec (sources : List (List MutConst)) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult) (valid : Valid context.1 before)
    (ran : rawRun (compileMutualPayload sources) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output := by
  rw [compileMutualPayload] at ran
  obtain ⟨compiled, middle, payloadRun, finalRun⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have tables := (Safe.mutConsts sources context before valid compiled middle payloadRun).1.2.1
  exact (PayloadArrays.finish_mutual_codec context sources compiled.1 compiled.2.2 middle after tables output finalRun).2

/-- Successful whole mutual compilation supplies its own nested array-count
evidence. Source semantics, projection correspondence and admission are separate. -/
theorem mutualBlock_codec (sources : List (List MutConst)) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileMutualBlock sources) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output := by
  let localContext : CompileEnv × BlockEnv := (context.1, { context.2 with mutCtx := MutConst.ctx sources })
  change rawRun (do preseedExprTables (mutualPreseedExprs sources); compileMutualPayload sources)
    localContext before = (.ok output, after) at ran
  obtain ⟨done, seededState, seeded, compiled⟩ := PreseedReferences.bind_ok _ _ localContext before output after ran
  cases done
  have prepared := PreseedState.preseed_ready_checked localContext _ bindings before seededState ready seeded
  have wire := PreseedWire.preseed_wire_checked localContext _ before seededState tables widths seeded
  have afterWidths : ReferenceWidths.LookupWidths localContext.1 seededState := by
    intro name address found
    rw [prepared.1.bindings, ← ready.bindings] at found
    exact widths name address found
  exact mutualPayload_codec sources localContext seededState after output ⟨afterWidths, wire, prepared.2.1⟩ compiled

end Ix.CompileCert.FamilyWire
