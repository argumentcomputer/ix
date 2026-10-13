import Ix.CompileCert.FamilyReader

/-! Source-related fields in the actual family reader's logical contexts.
Universe arity and rule/constructor identities are explicit family conditions;
no presentation metadata is interpreted. -/

namespace Ix.CompileCert.FamilyFields

open Ix Ix.CompileM
open Kernel.Reader
open _root_.Ix.Kernel (ConstRef)

theorem recLps_length (reader : Ctx) (reference : ConstRef Address) (large : Bool)
    (count : Nat) (blockParams : List Kernel.Name)
    (arity : count = blockParams.length + if large then 1 else 0) :
    (reader.recLps reference large count blockParams).length = count := by
  have fallback : (Ctx.recLps.fallback large count blockParams).length = count := by
    cases large <;> simp_all [Ctx.recLps.fallback]
  unfold Ctx.recLps
  cases reader.pins.levels[reference]? with
  | none => exact fallback
  | some params =>
    dsimp only
    by_cases same : params.length = count
    · simp [same]
    · simp [same, fallback]

theorem lpsAt_length (first count : UInt64) (blockParams : List Kernel.Name)
    (arity : blockParams.length = first.toNat) :
    (if count == first then blockParams else levelNames count.toNat).length = count.toNat := by
  by_cases same : count = first
  · simp [same, arity]
  · simp [same, levelNames]

theorem blob_recLps (reader : Ctx) (state : BlockState) (reference : ConstRef Address)
    (large : Bool) (count : Nat) (blockParams : List Kernel.Name) :
    (SharingRead.blobContext reader state).recLps reference large count blockParams =
      reader.recLps reference large count blockParams := rfl

def decodedRule (reader : Ctx) (block : Address) (index position : Nat)
    (fields : Nat) (rhs : Kernel.Expr) : Kernel.RecRule :=
  ⟨reader.nameOf (.ctor block index position), fields, 0, .inert, rhs, false, false, false⟩

def ruleStep (reader : Ctx) (member : MemberReader) (block : Address) (index : Nat)
    (entry : Ixon.RecursorRule × Nat) (initial : List Kernel.RecRule) : ReadM (ForInStep (List Kernel.RecRule)) := do
  let rhs ← member.read entry.1.rhs
  pure (.yield (initial ++ [decodedRule reader block index entry.2 entry.1.fields.toNat rhs]))

theorem rules_run (reader : Ctx) (member : MemberReader) (block : Address) (index : Nat)
    (sources : Array Ixon.RecursorRule) :
    FamilyReader.readRules reader member block index sources =
      forIn sources.zipIdx [] (ruleStep reader member block index) := by
  unfold FamilyReader.readRules ruleStep decodedRule
  simp only [bind_pure]

structure RuleMeaning (names : Name → Kernel.Name → Prop) (sourceParams : List Name)
    (params : List Kernel.Name) (source : RecursorRule) (target : Kernel.RecRule) : Prop where
  fields : target.nfields = source.nfields
  ctorParams : target.ctorParams = 0
  fire : target.fire = .inert
  k : target.k = false
  eta : target.eta = false
  paramsBlind : target.paramsBlind = false
  rhs : ExpressionState.Related names sourceParams params source.rhs target.rhs

theorem rules_loop (reader : Ctx) (member : MemberReader) (block : Address) (index : Nat)
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (sources : List RecursorRule) (targets : List Ixon.RecursorRule)
    (related : List.Forall₂ (RecursorEmission.RuleRelated member names sourceParams params) sources targets)
    (start : Nat) (initial : List Kernel.RecRule) :
    ∃ decoded, forIn (targets.zipIdx start) initial (ruleStep reader member block index) = .ok (initial ++ decoded) ∧
      List.Forall₂ (RuleMeaning names sourceParams params) sources decoded ∧
      decoded.map (·.ctor) = (List.range' start sources.length).map (fun position => reader.nameOf (.ctor block index position)) := by
  induction related generalizing start initial with
  | nil => exact ⟨[], by simp; rfl, .nil, by simp⟩
  | @cons source target sources targets head rest ih =>
    obtain ⟨fields, rhs, meaning, read⟩ := head
    let decoded := decodedRule reader block index start target.fields.toNat rhs
    obtain ⟨tail, tailRun, tailMeanings, tailNames⟩ := ih (start + 1) (initial ++ [decoded])
    refine ⟨decoded :: tail, ?_, .cons ?_ tailMeanings, ?_⟩
    · rw [List.zipIdx_cons, List.forIn_cons]
      simp only [ruleStep, read, bind, Except.bind, pure, Except.pure]
      simpa only [decoded, List.append_assoc, List.singleton_append] using tailRun
    · exact ⟨fields, rfl, rfl, rfl, rfl, rfl, meaning⟩
    · simp only [List.map_cons, decoded, decodedRule, List.length_cons, List.range'_succ, tailNames]

/-- The actual rule loop constructs source-related kernel rules and assigns
the major inductive's constructor identities by position. Pairing those
identities with the source rule's constructor is a source-family obligation. -/
theorem rules_read (reader : Ctx) (member : MemberReader) (block : Address) (index : Nat)
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (sources : Array RecursorRule) (targets : Array Ixon.RecursorRule)
    (related : List.Forall₂ (RecursorEmission.RuleRelated member names sourceParams params) sources.toList targets.toList) :
    ∃ decoded, FamilyReader.readRules reader member block index targets = .ok decoded ∧
      List.Forall₂ (RuleMeaning names sourceParams params) sources.toList decoded ∧
      decoded.map (·.ctor) = (List.range' 0 sources.size).map (fun position => reader.nameOf (.ctor block index position)) := by
  obtain ⟨decoded, ran, meanings, identities⟩ := rules_loop reader member block index names sourceParams params
    sources.toList targets.toList related 0 []
  refine ⟨decoded, ?_, meanings, by simpa using identities⟩
  rw [rules_run, ← Array.forIn_toList]
  simpa using ran

private theorem paired_length {α β : Type} {related : α → β → Prop}
    {sources : List α} {targets : List β} (pairs : List.Forall₂ related sources targets) :
    sources.length = targets.length := by
  induction pairs with
  | nil => rfl
  | cons head rest ih => exact congrArg Nat.succ ih

def recursorReader (reader : Ctx) (blockParams : List Kernel.Name) (owner : Address) (position : Nat)
    (constant : Ixon.Constant) (entry : RecEntry) (target : Ixon.Recursor) : MemberReader :=
  MemberReader.mk' reader constant
    (paramOf (reader.recLps (.member owner position) entry.large target.lvls.toNat blockParams))
    (FamilyReader.recursorSelf reader owner constant entry)

/-- Successful field readings discharge the real per-recursor loop body for
any continuation. Actual index/store lookup, major identity and family counts
remain explicit, so the theorem applies directly inside the family traversal. -/
theorem recursor_action (reader : Ctx) (blockParams : List Kernel.Name) (owner : Address) (position : Nat)
    (constant : Ixon.Constant) (entry : RecEntry) (source : RecursorVal) (target : Ixon.Recursor)
    (majorOwner : Address) (majorIndex : Nat) (major : Ixon.Inductive)
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name)
    (indexed : reader.index.recs[ConstRef.member owner position]? = some entry)
    (stored : reader.store owner = some constant)
    (member : (recursorMembers constant).find? (·.1 == position) = some (position, target))
    (majorRef : entry.major = .member majorOwner majorIndex)
    (majorFound : inductiveAt reader.store entry.major = some major)
    (count : major.ctors.size = source.rules.size) (safe : source.isUnsafe = false)
    (related : RecursorEmission.Related (recursorReader reader blockParams owner position constant entry target)
      names sourceParams (reader.recLps (.member owner position) entry.large target.lvls.toNat blockParams) source target)
    (next : FamilyReader.RecRow → ReadM α) :
    ∃ type rules,
      FamilyReader.recursorAction reader blockParams (.member owner position) next =
        next (⟨entry.name, reader.recLps (.member owner position) entry.large target.lvls.toNat blockParams, type⟩,
          target, rules) ∧
      ExpressionState.Related names sourceParams
        (reader.recLps (.member owner position) entry.large target.lvls.toNat blockParams) source.cnst.type type ∧
      List.Forall₂ (RuleMeaning names sourceParams
        (reader.recLps (.member owner position) entry.large target.lvls.toNat blockParams)) source.rules.toList rules ∧
      rules.map (·.ctor) = (List.range' 0 source.rules.size).map
        (fun index => reader.nameOf (.ctor majorOwner majorIndex index)) := by
  have lengths : source.rules.size = target.rules.size := by simpa using paired_length related.rules
  have counts : (major.ctors.size == target.rules.size) = true := by simp [count, lengths]
  have targetSafe : target.isUnsafe = false := related.safety.trans safe
  obtain ⟨type, meaning, typeRead⟩ := related.type
  obtain ⟨rules, rulesRead, ruleMeanings, ruleNames⟩ := rules_read reader
    (recursorReader reader blockParams owner position constant entry target) majorOwner majorIndex names sourceParams
    (reader.recLps (.member owner position) entry.large target.lvls.toNat blockParams) source.rules target.rules related.rules
  refine ⟨type, rules, ?_, meaning, ruleMeanings, ruleNames⟩
  unfold FamilyReader.recursorAction
  simp only [indexed, stored, member, targetSafe, Bool.false_eq_true, ↓reduceIte]
  change (do
    let type ← (recursorReader reader blockParams owner position constant entry target).read target.typ
    let some found := inductiveAt reader.store entry.major
      | declined s!"recursor {entry.name}: its major premise is not an inductive"
    unless found.ctors.size == target.rules.size do
      malformed s!"recursor {entry.name} has {target.rules.size} rules for {found.ctors.size} constructors"
    let .member mb mi := entry.major | malformed "recursor major is a constructor"
    let rules ← FamilyReader.readRules reader (recursorReader reader blockParams owner position constant entry target) mb mi target.rules
    next (⟨entry.name, reader.recLps (.member owner position) entry.large target.lvls.toNat blockParams, type⟩, target, rules)) = _
  simp only [typeRead, bind, Except.bind]
  rw [majorFound]
  simp only [counts, ↓reduceIte, majorRef, rulesRead]

def singletonSelf (name : Kernel.Name) : Nat → Option Kernel.Name :=
  fun index => if index == 0 then some name else none

theorem singleton_self (source : Name) (target : Kernel.Name) (context : CompileEnv × BlockEnv)
    (names : Name → Kernel.Name → Prop) (aliases : DefinitionReading.SelfAliases source target names) :
    ExpressionState.SelfCorrect (DefinitionReading.singletonContext source context).2 (singletonSelf target) names := by
  intro query index found
  change ((Std.TreeMap.empty : MutCtx).insert source 0)[query]? = some index at found
  rw [Canon.treeMap_insert_getElem?] at found
  split at found
  · rename_i sameKey
    cases Option.some.inj found
    exact ⟨target, by simp [singletonSelf], aliases query sameKey⟩
  · simp at found

/-- Instantiate the public recursor compiler at the universe/self context
that its indexed family reader uses. The family-level arity discharges the
parameter-list length; no metadata-name reconstruction is required. -/
theorem compiled_recursor (reader : Ctx) (base : Ixon.Constant) (blockParams : List Kernel.Name)
    (entry : RecEntry) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : RecursorVal) (before after : BlockState) (output : BlockResult)
    (arity : source.cnst.levelParams.size = blockParams.length + if entry.large then 1 else 0)
    (aliases : DefinitionReading.SelfAliases source.cnst.name entry.name names)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (ready : DefinitionEmission.Ready bindings before)
    (tables : Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : HeadWriterFrame.rawRun (compileConstantInfo (.recInfo source)) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ DefinitionBlock.Wrapped output ∧ Sharing.Verify.BlockResultCodecWF output ∧
      ∃ target, output.block.info = .recr target ∧
        RecursorEmission.Related
          (recursorReader (SharingRead.blobContext reader after) blockParams output.blockAddr 0 output.block entry target)
          names source.cnst.levelParams.toList
          (reader.recLps (.member output.blockAddr 0) entry.large target.lvls.toNat blockParams) source target := by
  let params := reader.recLps (.member output.blockAddr 0) entry.large source.cnst.levelParams.size blockParams
  have compiled := RecursorBlock.constant_correct reader base (singletonSelf entry.name) names params bindings context source
    (recLps_length reader _ entry.large _ blockParams arity) aligned external
    (singleton_self source.cnst.name entry.name context names aliases) before after output ready tables widths ran
  obtain ⟨wrapped, target, kind, related⟩ := compiled.2.1
  refine ⟨compiled.1, wrapped, compiled.2.2, target, kind, ?_⟩
  have selfEq : FamilyReader.recursorSelf (SharingRead.blobContext reader after) output.blockAddr output.block entry =
      singletonSelf entry.name := by
    funext index
    simp only [FamilyReader.recursorSelf, kind, singletonSelf]
  simpa only [recursorReader, selfEq, blob_recLps, related.levels, params] using related

/-- Compose public compilation with the actual family's per-recursor action.
Index construction and publication must supply the stated lookups; the
compiled artifact and its type/rule readings are produced by the theorem. -/
theorem compiled_recursor_action (reader : Ctx) (base : Ixon.Constant) (blockParams : List Kernel.Name)
    (entry : RecEntry) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : RecursorVal) (before after : BlockState) (output : BlockResult)
    (majorOwner : Address) (majorIndex : Nat) (major : Ixon.Inductive)
    (arity : source.cnst.levelParams.size = blockParams.length + if entry.large then 1 else 0)
    (aliases : DefinitionReading.SelfAliases source.cnst.name entry.name names)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (ready : DefinitionEmission.Ready bindings before)
    (tables : Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : HeadWriterFrame.rawRun (compileConstantInfo (.recInfo source)) context before = (.ok output, after))
    (indexed : reader.index.recs[ConstRef.member output.blockAddr 0]? = some entry)
    (stored : reader.store output.blockAddr = some output.block)
    (majorRef : entry.major = .member majorOwner majorIndex)
    (majorFound : inductiveAt reader.store entry.major = some major)
    (count : major.ctors.size = source.rules.size) (safe : source.isUnsafe = false)
    (next : FamilyReader.RecRow → ReadM α) :
    DefinitionEmission.Clean bindings after ∧ DefinitionBlock.Wrapped output ∧ Sharing.Verify.BlockResultCodecWF output ∧
      ∃ target type rules, output.block.info = .recr target ∧
        RecursorEmission.Related
          (recursorReader (SharingRead.blobContext reader after) blockParams output.blockAddr 0 output.block entry target)
          names source.cnst.levelParams.toList
          (reader.recLps (.member output.blockAddr 0) entry.large target.lvls.toNat blockParams) source target ∧
        FamilyReader.recursorAction (SharingRead.blobContext reader after) blockParams (.member output.blockAddr 0) next =
          next (⟨entry.name, reader.recLps (.member output.blockAddr 0) entry.large target.lvls.toNat blockParams, type⟩,
            target, rules) ∧
        ExpressionState.Related names source.cnst.levelParams.toList
          (reader.recLps (.member output.blockAddr 0) entry.large target.lvls.toNat blockParams) source.cnst.type type ∧
        List.Forall₂ (RuleMeaning names source.cnst.levelParams.toList
          (reader.recLps (.member output.blockAddr 0) entry.large target.lvls.toNat blockParams)) source.rules.toList rules ∧
        rules.map (·.ctor) = (List.range' 0 source.rules.size).map
          (fun index => reader.nameOf (.ctor majorOwner majorIndex index)) := by
  have compiled := compiled_recursor reader base blockParams entry names bindings context source before after output
    arity aliases aligned external ready tables widths ran
  obtain ⟨target, kind, related⟩ := compiled.2.2.2
  have member : (recursorMembers output.block).find? (·.1 == 0) = some (0, target) := by
    simp [recursorMembers, kind]
  obtain ⟨type, rules, action, typeMeaning, ruleMeanings, ruleNames⟩ := recursor_action
    (SharingRead.blobContext reader after) blockParams output.blockAddr 0 output.block entry source target
    majorOwner majorIndex major names source.cnst.levelParams.toList indexed stored member majorRef majorFound count safe related next
  exact ⟨compiled.1, compiled.2.1, compiled.2.2.1, target, type, rules, kind, related, action, typeMeaning, ruleMeanings, ruleNames⟩

end Ix.CompileCert.FamilyFields
