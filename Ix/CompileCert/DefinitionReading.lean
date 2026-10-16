import Ix.CompileCert.EmissionDispatch
import IxC.Kernel.Ixon.ReaderSpec

/-! # Compiled definitions are read back as their sources

Public dispatch of a definition, theorem or opaque compiles one singleton
block (`EmissionDispatch.definition_run`). The certified reader reads such
a record with `Ix.Kernel.Reader.readRecord`: under the record's own key
(`Ctx.memberKey (.member owner 0)`), with level parameters
`List.range lvls`, universe variables read positionally (`id`), and
`recur 0` read as the record's own key (`ReaderSpec.definitionReader`).

`constant_reads` composes the compile-side theorem of the block
(`EmissionBlocks.definitionInfo_correct`, with exactly that reader) with
the reader: a successful compile from a clean state, whose record's key
reads and whose self references resolve to it (`SelfAliases`), reads
under `readRecord` as exactly one declaration, the one the definition's
kind makes (`ReaderSpec.DefinitionDecl`) of its key, its level parameters
and the readings of its type and value, which are terms `Related` to the
source's; the returned block decodes exactly; and a definition the
reader's safety policy declines is declined (`constant_declines`).
The reader runs over the block's blobs overlaid on the context's, as the
compiler's in-flight reader does (publication is CT-16's R13).

CT-16's `DefinitionReading`, adapted to keys read through `memberKey`
(which can decline), positional levels and the reader's own
`definitionReader`. Under `surgeryFree` until CQ3.5. -/

namespace Ix.CompileCert.DefinitionReading

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader
open Ix.Sharing.Verify (BlockWireTablesWF BlockResultCodecWF)

variable {md : Mode}

/-! ## The singleton's self references -/

/-- The self map `readRecord` reads a singleton definition with: member 0
is the record's own key. -/
def selfAt (cx : Ctx md) (owner : Address) : Nat → Option (ReadM (CName md)) :=
  fun index => if index == 0 then some (cx.memberKey (.member owner 0)) else none

theorem definitionReader_eq (cx : Ctx md) (owner : Address) (record : Ixon.Constant) (target : Ixon.Definition) :
    definitionReader cx owner record target = MemberReader.mk' cx record id (selfAt cx owner) := rfl

/-- The singleton mutual context maps exactly the names whose hash field is
the declaration's to slot 0 (`Ix.MutCtx` compares names by `nameCompare`). -/
theorem singleton_lookup (name query : Ix.Name) (index : Nat)
    (found : ((Std.TreeMap.empty : Ix.MutCtx).insert name 0).get? query = some index) :
    Ix.nameCompare query name = .eq ∧ index = 0 := by
  have unfolded : ((Std.TreeMap.empty : Ix.MutCtx).insert name 0).get? query =
      (match Ix.nameCompare query name with | .lt => none | .gt => none | .eq => some 0) := rfl
  rw [unfolded] at found
  cases compared : Ix.nameCompare query name <;> rw [compared] at found
  · cases found
  · exact ⟨rfl, (Option.some.inj found).symm⟩
  · cases found

/-- Every name the compiler resolves as the singleton's self reference (an
equal hash field) is related to the record's key. -/
def SelfAliases (source : Ix.Name) (key : CName md) (names : Ix.Name → CName md → Prop) : Prop :=
  ∀ query, Ix.nameCompare query source = .eq → names query key

/-- **The singleton's self references read as its key.** -/
theorem singleton_self (cx : Ctx md) (owner : Address) (source : Ix.Name) (context : CompileEnv × BlockEnv)
    (names : Ix.Name → CName md → Prop) {key : CName md}
    (keyed : cx.memberKey (.member owner 0) = .ok key) (aliases : SelfAliases source key names) :
    SelfCorrect (EmissionDispatch.singletonContext source context).2 (selfAt cx owner) names := by
  intro query index found
  obtain ⟨same, rfl⟩ := singleton_lookup source query index found
  exact ⟨key, by simp [selfAt, keyed], aliases query same⟩

/-! ## The reader on a definition record -/

theorem readDefinition_ok (cx : Ctx md) (state : State md) (heights : CName md → Nat)
    (reference : Ix.Kernel.ConstRef Address) (params : List LevelParam) (member : MemberReader md)
    (target : Ixon.Definition) {key : CName md} {type value : CExpr md}
    (keyed : cx.memberKey reference = .ok key) (typeRead : member.read target.typ = .ok type)
    (valueRead : member.read target.value = .ok value) (safe : safetyDeclineOf target.kind target.safety = none) :
    ∃ output, readDefinition cx state heights reference params member target = .ok output := by
  unfold readDefinition lowerDefinition
  simp only [keyed, typeRead, valueRead, safe, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

/-- A definition record whose key reads and whose type and value read, and
which the safety policy admits, is read. -/
theorem readRecord_ok (cx : Ctx md) (state : State md) (owner : Address) (record : Ixon.Constant)
    (target : Ixon.Definition) (info : record.info = .defn target) {key : CName md} {type value : CExpr md}
    (keyed : cx.memberKey (.member owner 0) = .ok key)
    (typeRead : (definitionReader cx owner record target).read target.typ = .ok type)
    (valueRead : (definitionReader cx owner record target).read target.value = .ok value)
    (safe : safetyDeclineOf target.kind target.safety = none) :
    ∃ result, readRecord cx state owner record = .ok result := by
  obtain ⟨⟨declaration, rewritten⟩, read⟩ := readDefinition_ok cx state (state.heights.getD · 0) (.member owner 0)
    (List.range target.lvls.toNat) (definitionReader cx owner record target) target keyed typeRead valueRead safe
  refine ⟨{ decls := #[declaration], projRewrites := if rewritten then 1 else 0 }, ?_⟩
  unfold readRecord
  rw [info]
  dsimp only
  change (do
    let (decl, flag) ← readDefinition cx state (state.heights.getD · 0) (.member owner 0)
      (List.range target.lvls.toNat) (definitionReader cx owner record target) target
    pure ({ decls := #[decl], projRewrites := if flag then 1 else 0 } : Read md)) = _
  rw [read]
  rfl

/-- A definition record the safety policy declines is declined once its
key, type and value read. -/
theorem readRecord_declines (cx : Ctx md) (state : State md) (owner : Address) (record : Ixon.Constant)
    (target : Ixon.Definition) (info : record.info = .defn target) {key : CName md} {type value : CExpr md}
    (keyed : cx.memberKey (.member owner 0) = .ok key)
    (typeRead : (definitionReader cx owner record target).read target.typ = .ok type)
    (valueRead : (definitionReader cx owner record target).read target.value = .ok value)
    (reason : String) (policy : safetyDeclineOf target.kind target.safety = some reason) :
    readRecord cx state owner record = .error (.declined reason) := by
  unfold readRecord
  rw [info]
  dsimp only
  change (do
    let (decl, flag) ← readDefinition cx state (state.heights.getD · 0) (.member owner 0)
      (List.range target.lvls.toNat) (definitionReader cx owner record target) target
    pure ({ decls := #[decl], projRewrites := if flag then 1 else 0 } : Read md)) = _
  unfold readDefinition lowerDefinition
  simp only [keyed, typeRead, valueRead, policy, bind, Except.bind, declined, throw, throwThe,
    MonadExceptOf.throw]

/-! ## The compiled record -/

/-- The skeleton fixes a definition record's kind, safety and level count. -/
theorem erase_defn {info : Ixon.ConstantInfo} {source : Ix.Def}
    (same : SharingRoots.erase info = SharingRoots.erase (EmissionBlocks.definitionSkeleton source)) :
    ∃ target : Ixon.Definition, info = .defn target ∧ target.kind = source.kind ∧
      target.safety = source.safety ∧ target.lvls = source.levelParams.size.toUInt64 := by
  cases info with
  | defn target =>
    have inner : Ixon.ConstantInfo.defn { target with typ := .sort 0, value := .sort 0 } =
        .defn (Emission.definitionPayload source (.sort 0) (.sort 0)) := same
    have fields := Ixon.ConstantInfo.defn.inj inner
    exact ⟨target, rfl, congrArg Ixon.Definition.kind fields, congrArg Ixon.Definition.safety fields,
      congrArg Ixon.Definition.lvls fields⟩
  | _ => cases same

/-- A successful definition-like block's level count is the source's. -/
theorem definitionInfo_levels (source : Ix.Def) :
    Emission.Yields (compileDefinitionDataInfo source) (fun output =>
      ∀ target : Ixon.Definition, output.block.info = .defn target →
        target.lvls.toNat = source.levelParams.size) := by
  intro context before output after ran
  unfold compileDefinitionDataInfo at ran
  obtain ⟨_, middle, _, compiled⟩ := bind_ok ran
  unfold compileDefinitionDataBlock at compiled
  obtain ⟨payload, payloadRan, built, _⟩ := EmissionBlocks.block_ok (fun payload => .defn payload.1)
    (fun payload => payload.2.1) (fun payload => by obtain ⟨_, _, _, _⟩ := payload; rfl) compiled
  have header := Emission.definitionData_header source context middle payload after payloadRan
  obtain ⟨erased, _, _, _⟩ := SharingRoots.build_roots (md := .anon) _ _ _ _ _ built
  intro target info
  rw [info] at erased
  have fields := Ixon.ConstantInfo.defn.inj (show Ixon.ConstantInfo.defn
    { target with typ := .sort 0, value := .sort 0 } = .defn { payload.1 with typ := .sort 0, value := .sort 0 }
    from erased)
  have lvlsEq : target.lvls = payload.1.lvls := by
    have same := congrArg Ixon.Definition.lvls fields; exact same
  rw [lvlsEq]
  exact header

section Reading

variable (cx : Ctx md) (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam) (bindings : Bindings)

/-- The source relation of a definition-like declaration: levels mean its
own level parameters, read positionally. -/
abbrev related (source : Ix.Def) : Ix.Expr → CExpr md → Prop :=
  Related names (LevelMeaning source.levelParams.toList σ id)

/-- **A compiled definition is read back as its source**: public dispatch of
a definition, theorem or opaque, under an environment without call-site
plans, from a clean state whose tables are on the wire and whose
declaration prefix resolves names to 32-byte addresses, returns a block
that decodes exactly and that `readRecord` (over the block's blobs overlaid
on the context's) reads as exactly one declaration: the one the kind makes
of the record's key, the level parameters `0, …, n - 1`, and the readings
of the type and the value, which are terms related to the source's; given
that the record's key reads, that the names the compiler resolves as the
self reference are related to it, and that the reader's safety policy
admits the declaration. -/
theorem constant_reads (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (info : ConstantInfo) (source : Ix.Def)
    (view : EmissionDispatch.sourceData info = some source) {before after : BlockState} {output : BlockResult}
    (state : State md) {key : CName md} (keyed : cx.memberKey (.member output.blockAddr 0) = .ok key)
    (aliases : SelfAliases source.name key names) (clean : Emission.Clean bindings before)
    (wire : BlockWireTablesWF before) (widths : PreseedWire.LookupWidths context.1 before)
    (safe : safetyDeclineOf source.kind source.safety = none)
    (ran : rawRun (compileConstantInfo info) context before = (.ok output, after)) :
    BlockResultCodecWF output ∧ (∃ blockMeta, output = BlockResult.mk' output.block blockMeta) ∧
      ∃ result declaration type value,
        readRecord (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block = .ok result ∧
        result.decls = #[declaration] ∧
        related names σ source source.type type ∧ related names σ source source.value value ∧
        DefinitionDecl ⟨key, List.range source.levelParams.size, type⟩ value
          (projRewrite state ⟨key, List.range source.levelParams.size, type⟩ value) source.kind declaration := by
  have codec := EmissionDispatch.constant_codec context free info wire widths ran
  rw [EmissionDispatch.definition_run context free info source view] at ran
  have levels := definitionInfo_levels source _ before output after ran
  have selfSound := singleton_self cx output.blockAddr source.name context names keyed aliases
  obtain ⟨_, _, wrapped, erased, roots⟩ := EmissionBlocks.definitionInfo_correct cx id (selfAt cx output.blockAddr)
    names σ bindings (EmissionDispatch.singletonContext source.name context) free aligned external source
    (constsSatisfy_of_forall (fun name => selfSound name) _) (constsSatisfy_of_forall (fun name => selfSound name) _)
    clean ran
  obtain ⟨target, info, kind, safety, lvls⟩ := erase_defn erased
  have count := levels target info
  rw [info] at roots
  obtain ⟨type, typeRel, typeRead, value, valueRel, valueRead⟩ :
      ∃ type, related names σ source source.type type ∧
        (definitionReader (ExpressionRead.withBlockBlobs cx after) output.blockAddr output.block target).read
          target.typ = .ok type ∧
        ∃ value, related names σ source source.value value ∧
          (definitionReader (ExpressionRead.withBlockBlobs cx after) output.blockAddr output.block target).read
            target.value = .ok value := by
    cases roots with
    | cons head rest =>
      cases rest with
      | cons second _ =>
        obtain ⟨type, typeRel, typeRead⟩ := head
        obtain ⟨value, valueRel, valueRead⟩ := second
        exact ⟨type, typeRel, typeRead, value, valueRel, valueRead⟩
  have keyed' : (ExpressionRead.withBlockBlobs cx after).memberKey (.member output.blockAddr 0) = .ok key := keyed
  have admitted : safetyDeclineOf target.kind target.safety = none := by rw [kind, safety]; exact safe
  obtain ⟨result, read⟩ := readRecord_ok (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block
    target info keyed' typeRead valueRead admitted
  obtain ⟨declaration, singleton, decls⟩ := readRecord_singleton (by rw [info]; rfl) read
  refine ⟨codec, wrapped, result, declaration, type, value, read, decls, typeRel, valueRel, ?_⟩
  cases singleton with
  | defn info' keyed'' type' value' kind' =>
    rename_i target' key' type'' value''
    rw [info] at info'
    cases Ixon.ConstantInfo.defn.inj info'
    rw [keyed'] at keyed''
    cases Except.ok.inj keyed''
    rw [typeRead] at type'
    cases Except.ok.inj type'
    rw [valueRead] at value'
    cases Except.ok.inj value'
    have range : singletonLps target.lvls = List.range source.levelParams.size := by
      unfold singletonLps
      rw [count]
    rw [range, kind] at kind'
    exact kind'
  | axio info' => rw [info] at info'; cases info'
  | quot info' => rw [info] at info'; cases info'

/-- **A compiled definition the reader's safety policy declines is
declined** (under the same premises, but the policy). -/
theorem constant_declines (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (info : ConstantInfo) (source : Ix.Def)
    (view : EmissionDispatch.sourceData info = some source) {before after : BlockState} {output : BlockResult}
    (state : State md) {key : CName md} (keyed : cx.memberKey (.member output.blockAddr 0) = .ok key)
    (aliases : SelfAliases source.name key names) (clean : Emission.Clean bindings before)
    (reason : String) (policy : safetyDeclineOf source.kind source.safety = some reason)
    (ran : rawRun (compileConstantInfo info) context before = (.ok output, after)) :
    readRecord (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block =
      .error (.declined reason) := by
  rw [EmissionDispatch.definition_run context free info source view] at ran
  have selfSound := singleton_self cx output.blockAddr source.name context names keyed aliases
  obtain ⟨_, _, _, erased, roots⟩ := EmissionBlocks.definitionInfo_correct cx id (selfAt cx output.blockAddr)
    names (fun _ => 0) bindings (EmissionDispatch.singletonContext source.name context) free aligned external source
    (constsSatisfy_of_forall (fun name => selfSound name) _) (constsSatisfy_of_forall (fun name => selfSound name) _)
    clean ran
  obtain ⟨target, info, kind, safety, _⟩ := erase_defn erased
  rw [info] at roots
  cases roots with
  | cons head rest =>
    cases rest with
    | cons second _ =>
      obtain ⟨_, _, typeRead⟩ := head
      obtain ⟨_, _, valueRead⟩ := second
      have keyed' : (ExpressionRead.withBlockBlobs cx after).memberKey (.member output.blockAddr 0) = .ok key :=
        keyed
      exact readRecord_declines (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block target
        info keyed' typeRead valueRead reason (by rw [kind, safety]; exact policy)

end Reading

end Ix.CompileCert.DefinitionReading
