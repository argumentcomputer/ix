import Ix.CompileCert.HeaderEmission
import Ix.CompileCert.DeclarationHeaders

/-! Actual recursor payload compilation, including source-ordered rule bodies
and the warm expression cache retained across the type and rule loop. Logical
self/dependency bindings remain explicit; presentation metadata is absent from
the source relation. -/

namespace Ix.CompileCert.RecursorEmission

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame

def RuleRelated (reader : Kernel.Reader.MemberReader) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name)
    (source : RecursorRule) (target : Ixon.RecursorRule) : Prop :=
  target.fields.toNat = source.nfields ∧
    ∃ rhs, ExpressionState.Related names sourceParams params source.rhs rhs ∧ reader.read target.rhs = .ok rhs

theorem rule_grows (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name) (before after : BlockState)
    (growth : ExpressionRead.Extends
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx)
    (source : RecursorRule) (target : Ixon.RecursorRule)
    (related : RuleRelated (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before)
      names sourceParams params source target) :
    RuleRelated (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
      names sourceParams params source target := by
  obtain ⟨fields, rhs, meaning, read⟩ := related
  exact ⟨fields, rhs, meaning,
    ExpressionRead.convExpr_preserves growth (table := #[]) (nextTable := #[])
      (by intros; assumption) target.rhs rhs read⟩

theorem rules_grow (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name) (before after : BlockState)
    (growth : ExpressionRead.Extends
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx)
    (sources : List RecursorRule) (targets : List Ixon.RecursorRule)
    (related : List.Forall₂
      (RuleRelated (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before)
        names sourceParams params) sources targets) :
    List.Forall₂
      (RuleRelated (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
        names sourceParams params) sources targets := by
  induction related with
  | nil => exact .nil
  | cons head rest ih =>
    exact .cons (rule_grows reader base self names sourceParams params before after growth _ _ head) ih

section Rules

variable (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
  (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
  (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
local notation "param" => Kernel.Reader.paramOf params
local notation "meaning" => ExpressionState.Related names (BlockEnv.univCtx (Prod.snd context)) params
local notation "Good" => ExpressionState.Good reader base param self meaning bindings
local notation "view" => ExpressionRead.blockReader reader base param self

theorem rule_correct (source : RecursorRule) (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before after : BlockState) (output : Ixon.RecursorRule × Address × UInt64)
    (good : Good before) (mode : before.p3MetaMode = false)
    (ran : rawRun (compileRecursorRule source) context before = (.ok output, after)) :
    Good after ∧ after.p3MetaMode = false ∧
      ExpressionRead.Extends (view before).ecx (view after).ecx ∧
      RuleRelated (view after) names context.2.univCtx params source output.1 := by
  have fields := DeclarationHeaders.recursorRule source context before output after ran
  unfold compileRecursorRule at ran
  obtain ⟨expression, middle, compiled, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  obtain ⟨count, last, guarded, returned⟩ := PreseedReferences.bind_ok _ _ context middle output after rest
  have same := Interning.checkedTableCount_state "recursor rule fields" source.nfields context middle
  rw [guarded] at same
  dsimp only at same
  subst last
  rw [rawRun_pure] at returned
  obtain ⟨outEq, stateEq⟩ := Prod.mk.inj returned
  cases stateEq
  cases Except.ok.inj outEq
  have checked := MetadataMode.compileExpr_checked reader base self names params bindings context
    arity aligned external selfSound source.rhs before good mode
  rw [compiled] at checked
  obtain ⟨rhs, related, read⟩ := checked.1.2.2 expression rfl
  exact ⟨checked.1.1, checked.2 expression rfl, checked.1.2.1, fields, rhs, related, read⟩

/-- Every rule is related in the final reader, with the actual cache retained
between calls. The loop appends payloads in source order. -/
theorem rules_correct (sources : List RecursorRule) (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (initial : RecursorRuleCompileState) (before after : BlockState) (output : RecursorRuleCompileState)
    (good : Good before) (mode : before.p3MetaMode = false)
    (ran : rawRun (compileRecursorRules sources initial) context before = (.ok output, after)) :
    Good after ∧ after.p3MetaMode = false ∧
      ExpressionRead.Extends (view before).ecx (view after).ecx ∧
      ∃ targets, output.rules.toList = initial.rules.toList ++ targets ∧
        List.Forall₂ (RuleRelated (view after) names context.2.univCtx params) sources targets := by
  induction sources generalizing initial before with
  | nil =>
    change ((Except.ok initial : Except CompileError _), before) = (.ok output, after) at ran
    obtain ⟨outEq, stateEq⟩ := Prod.mk.inj ran
    cases stateEq
    cases Except.ok.inj outEq
    exact ⟨good, mode, ExpressionState.extends_refl _, [], by simp, .nil⟩
  | cons source rest ih =>
    rw [compileRecursorRules] at ran
    obtain ⟨compiled, middle, first, last⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    have head := rule_correct reader base self names params bindings context source arity aligned external selfSound
      before middle compiled good mode first
    have tail := ih
      { rules := initial.rules.push compiled.1
        ruleAddrs := initial.ruleAddrs.push compiled.2.1
        ruleRoots := initial.ruleRoots.push compiled.2.2 }
      middle head.1 head.2.1 last
    obtain ⟨targets, payloads, meanings⟩ := tail.2.2.2
    refine ⟨tail.1, tail.2.1, ExpressionState.extends_trans head.2.2.1 tail.2.2.1,
      compiled.1 :: targets, ?_, .cons ?_ meanings⟩
    · simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using payloads
    · exact rule_grows reader base self names context.2.univCtx params middle after
        tail.2.2.1 source compiled.1 head.2.2.2

end Rules

def payload (source : RecursorVal) (type : Ixon.Expr) (rules : Array Ixon.RecursorRule) : Ixon.Recursor :=
  { k := source.k, isUnsafe := source.isUnsafe, lvls := source.cnst.levelParams.size.toUInt64,
    params := source.numParams.toUInt64, indices := source.numIndices.toUInt64,
    motives := source.numMotives.toUInt64, minors := source.numMinors.toUInt64, typ := type, rules }

def finishChecks (source : RecursorVal) (count : Nat) (block : BlockEnv) : CompileM Unit := do
  let _ ← checkedTableCount "declaration universe parameters" source.cnst.levelParams.size
  let _ ← checkedTableCount "recursor parameters" source.numParams
  let _ ← checkedTableCount "recursor indices" source.numIndices
  let _ ← checkedTableCount "recursor motives" source.numMotives
  let _ ← checkedTableCount "recursor minors" source.numMinors
  let _ ← checkedTableCount "recursor rules" count
  compileName source.cnst.name
  compileNames source.cnst.levelParams
  compileNames source.all
  compileNames (block.mutCtx.toList.toArray.map (·.1))
  compileNames (source.rules.map (·.ctor))

theorem finish_run (source : RecursorVal) (type : Ixon.Expr) (root : UInt64)
    (rules : RecursorRuleCompileState) (context : CompileEnv × BlockEnv) (before : BlockState) :
    ∃ metadata, rawRun (finishRecursorCompilation source type root rules) context before =
      rawRun (do
        finishChecks source rules.rules.size context.2
        pure (payload source type rules.rules, metadata, type)) context (DefinitionEmission.drained before) := by
  simp only [finishRecursorCompilation, takeArena, takeMetaSharing, takeMetaRefs,
    takeUnivPatches, clearExprCache, getMutCtxAddrs, rawRun_bind,
    Interning.rawRun_modifyGet, rawRun_modify, UniverseMeaning.rawRun_readBlock,
    finishChecks, payload, DefinitionEmission.drained, bind_assoc, rawRun_pure]
  exact ⟨_, rfl⟩

section Finish

variable (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name)
  (self : Nat → Option Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)

theorem checks_preserve (source : RecursorVal) (count : Nat)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address) :
    DefinitionEmission.Preserves reader base param self bindings context (finishChecks source count context.2) := by
  unfold finishChecks
  with_reducible repeat' first
    | exact HeaderEmission.count_preserves reader base param self bindings context _ _
    | exact DefinitionEmission.Preserves.compileName reader base param self bindings context _ aligned
    | exact DefinitionEmission.Preserves.compileNames reader base param self bindings context _ aligned
    | refine DefinitionEmission.Preserves.bind reader base param self bindings context ?_ (fun _ => ?_)

theorem finish_correct (source : RecursorVal) (type : Ixon.Expr) (root : UInt64)
    (rules : RecursorRuleCompileState) (before after : BlockState)
    (output : Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr)
    (sound : ExpressionState.StateSound bindings before) (mode : before.p3MetaMode = false)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (ran : rawRun (finishRecursorCompilation source type root rules) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends (ExpressionRead.blockReader reader base param self before).ecx
        (ExpressionRead.blockReader reader base param self after).ecx ∧
      output.1 = payload source type rules.rules ∧ output.2.2 = type := by
  obtain ⟨metadata, expanded⟩ := finish_run source type root rules context before
  rw [expanded] at ran
  obtain ⟨done, middle, checkedRun, returned⟩ := PreseedReferences.bind_ok _ _ context _ output after ran
  rw [rawRun_pure] at returned
  obtain ⟨outEq, stateEq⟩ := Prod.mk.inj returned
  cases stateEq
  have preserved := checks_preserve reader base param self bindings context source rules.rules.size aligned
    (DefinitionEmission.drained before) (DefinitionEmission.drained_clean bindings before sound mode)
  rw [checkedRun, DefinitionEmission.drained_reader reader base param self before mode] at preserved
  cases Except.ok.inj outEq
  exact ⟨preserved.1, preserved.2, rfl, rfl⟩

end Finish

structure Related (reader : Kernel.Reader.MemberReader) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name)
    (source : RecursorVal) (target : Ixon.Recursor) : Prop where
  k : target.k = source.k
  safety : target.isUnsafe = source.isUnsafe
  levels : target.lvls.toNat = source.cnst.levelParams.size
  parameters : target.params.toNat = source.numParams
  indices : target.indices.toNat = source.numIndices
  motives : target.motives.toNat = source.numMotives
  minors : target.minors.toNat = source.numMinors
  type : ∃ type, ExpressionState.Related names sourceParams params source.cnst.type type ∧
    reader.read target.typ = .ok type
  rules : List.Forall₂ (RuleRelated reader names sourceParams params) source.rules.toList target.rules.toList

def body (source : RecursorVal) : CompileM (Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr) := do
  let (type, root) ← compileExpr source.cnst.type
  let rules ← compileRecursorRules source.rules.toList {}
  finishRecursorCompilation source type root rules

def contextFor (source : RecursorVal) (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with current := source.cnst.name, univCtx := source.cnst.levelParams.toList })

theorem compile_run (source : RecursorVal) (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (compileRecursor source) context before =
      rawRun (body source) (contextFor source context) (DefinitionEmission.prepared before) := by
  simp only [compileRecursor, withCurrent, withUnivCtx, resetArena, body,
    DefinitionEmission.rawRun_withBlockEnv, rawRun_bind, rawRun_modify,
    contextFor, DefinitionEmission.prepared]

theorem body_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : RecursorVal) (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before after : BlockState) (output : Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr)
    (good : ExpressionState.Good reader base (Kernel.Reader.paramOf params) self
      (ExpressionState.Related names context.2.univCtx params) bindings before)
    (mode : before.p3MetaMode = false)
    (ran : rawRun (body source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx ∧
      Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
        names context.2.univCtx params source output.1 ∧ output.2.2 = output.1.typ := by
  rw [body] at ran
  obtain ⟨type, typed, typeRun, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have checked := MetadataMode.compileExpr_checked reader base self names params bindings context
    arity aligned external selfSound source.cnst.type before good mode
  rw [typeRun] at checked
  obtain ⟨value, meaning, read⟩ := checked.1.2.2 type rfl
  obtain ⟨rules, compiled, rulesRun, finishRun⟩ := PreseedReferences.bind_ok _ _ context typed output after rest
  have ruleFacts := rules_correct reader base self names params bindings context source.rules.toList arity
    aligned external selfSound {} typed compiled rules checked.1.1 (checked.2 type rfl) rulesRun
  have finished := finish_correct reader base (Kernel.Reader.paramOf params) self bindings context
    source type.1 type.2 rules compiled after output ruleFacts.1.1 ruleFacts.2.1 aligned finishRun
  have headers := DeclarationHeaders.recursor source type.1 type.2 rules context compiled output after finishRun
  have growth := ExpressionState.extends_trans ruleFacts.2.2.1 finished.2.1
  obtain ⟨targets, targetEq, ruleMeanings⟩ := ruleFacts.2.2.2
  have targetEq : rules.rules.toList = targets := by simpa using targetEq
  refine ⟨finished.1, ExpressionState.extends_trans checked.1.2.1 growth, ?_, ?_⟩
  · refine ⟨?_, ?_, headers.1, headers.2.1, headers.2.2.1, headers.2.2.2.1,
      headers.2.2.2.2, ?_, ?_⟩
    · rw [finished.2.2.1]; rfl
    · rw [finished.2.2.1]; rfl
    · refine ⟨value, meaning, ?_⟩
      rw [finished.2.2.1]
      exact ExpressionRead.convExpr_preserves growth (table := #[]) (nextTable := #[])
        (by intros; assumption) type.1 value read
    · rw [finished.2.2.1]
      change List.Forall₂ _ source.rules.toList rules.rules.toList
      rw [targetEq]
      exact rules_grow reader base self names context.2.univCtx params compiled after finished.2.1
        source.rules.toList targets ruleMeanings
  · rw [finished.2.2.1]; exact finished.2.2.2

/-- The production initializer discharges the initial cache requirements;
the actual type/rule fold carries a sound warm cache until finalization. -/
theorem compile_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : RecursorVal) (arity : params.length = source.cnst.levelParams.size)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before after : BlockState) (output : Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr)
    (ready : DefinitionEmission.Ready bindings before)
    (ran : rawRun (compileRecursor source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx ∧
      Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
        names source.cnst.levelParams.toList params source output.1 ∧ output.2.2 = output.1.typ := by
  rw [compile_run] at ran
  have initial := DefinitionEmission.prepared_clean bindings before ready
  have result := body_correct reader base self names params bindings (contextFor source context) source
    (by simpa [contextFor] using arity) aligned external selfSound _ after output
    (initial.good reader base (Kernel.Reader.paramOf params) self _) initial.2.2 ran
  rw [DefinitionEmission.prepared_reader reader base (Kernel.Reader.paramOf params) self before ready.mode] at result
  exact result

end Ix.CompileCert.RecursorEmission
