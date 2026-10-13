import Ix.CompileCert.DefinitionReading
import Ix.CompileCert.ExpressionScope

/-! Successful Pass 3 record compilation restores the ordinary expression
cache. Its operational state/growth result does not require the metadata
record sources to satisfy the payload's self-reference scope condition. -/

namespace Ix.CompileCert.MetadataErasure

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame

def CacheFrame (action : CompileM α) : Prop :=
  ∀ context before output after, rawRun action context before = (.ok output, after) → after.exprCache = before.exprCache

theorem CacheFrame.pure (value : α) : CacheFrame (pure value) := by
  intro context before output after ran
  have same := congrArg (fun result => result.2.exprCache) ran
  exact same.symm

theorem CacheFrame.read : CacheFrame getCompileEnv := by
  intro context before output after ran
  have same := congrArg Prod.snd ran
  cases same
  rfl

theorem CacheFrame.bind {action : CompileM α} {next : α → CompileM β}
    (head : CacheFrame action) (tail : ∀ value, CacheFrame (next value)) : CacheFrame (action >>= next) := by
  intro context before output after ran
  obtain ⟨value, middle, first, last⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  exact (tail value context middle output after last).trans (head context before value middle first)

theorem CacheFrame.record (environment : CompileEnv) (index : Nat) : CacheFrame (MetadataMode.recordStep environment index) := by
  intro context before output after ran
  unfold MetadataMode.recordStep at ran
  simp only [rawRun_bind, rawRun_get] at ran
  by_cases hit : before.p3Records.contains index = true
  · simp only [hit, ↓reduceIte, rawRun_pure] at ran
    have same := congrArg Prod.snd ran
    cases same
    rfl
  · simp only [hit, Bool.false_eq_true, ↓reduceIte] at ran
    cases found : environment.p3Sources.get? index with
    | none => rw [found] at ran; cases ran
    | some source =>
      simp only [found, rawRun_bind, rawRun_get, rawRun_modify] at ran
      cases compiled : rawRun (compileExprPartial source) context { before with p3MetaMode := true } with
      | mk result middle =>
        rw [compiled] at ran
        cases result with
        | error error => cases ran
        | ok value =>
          rcases value with ⟨value, root⟩
          have same := congrArg (fun result => result.2.exprCache) ran
          exact same.symm

theorem CacheFrame.forIn_list (items : List α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (each : ∀ item state, CacheFrame (body item state)) : CacheFrame (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact CacheFrame.pure _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply CacheFrame.bind (each item initial)
    intro step
    cases step with
    | done value => exact CacheFrame.pure value
    | yield value => exact ih value

theorem CacheFrame.forIn_array (items : Array α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (each : ∀ item state, CacheFrame (body item state)) : CacheFrame (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact CacheFrame.forIn_list _ initial body each

theorem CacheFrame.records (source : Expr) : CacheFrame (pass3CompileRecords source) := by
  rw [MetadataMode.pass3CompileRecords_eq]
  apply CacheFrame.bind CacheFrame.read
  intro environment
  apply CacheFrame.bind
  · apply CacheFrame.forIn_array
    intro index _
    exact CacheFrame.bind (CacheFrame.record environment index) (fun _ => CacheFrame.pure _)
  · intro _; exact CacheFrame.pure _

theorem growth_retarget (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (params : Nat → Kernel.Name)
    (first last : Nat → Option Kernel.Name) (before after : BlockState)
    (growth : ExpressionRead.Extends (ExpressionRead.blockReader reader base params first before).ecx
      (ExpressionRead.blockReader reader base params first after).ecx) :
    ExpressionRead.Extends (ExpressionRead.blockReader reader base params last before).ecx
      (ExpressionRead.blockReader reader base params last after).ecx :=
  ⟨growth.level, growth.ref, growth.blob, fun _ _ found => found, growth.name⟩

/-- A total auxiliary self interpretation discharges the old metadata proof
internally. Its result is used only for state validity and reader growth;
metadata value correspondence is absent from this endpoint. -/
theorem records_empty (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (source : Expr) (before after : BlockState) (output : Unit)
    (clean : DefinitionEmission.Clean bindings before)
    (ran : rawRun (pass3CompileRecords source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx := by
  let auxiliarySelf : Nat → Option Kernel.Name := fun _ => some .anonymous
  let auxiliaryNames : Name → Kernel.Name → Prop := fun _ _ => True
  have auxiliaryExternal : ExpressionState.BindingsCorrect context.1 bindings reader auxiliaryNames := by
    intro name address found
    obtain ⟨reference, resolved, _⟩ := external name address found
    exact ⟨reference, resolved, trivial⟩
  have auxiliaryBindings : ExpressionState.SelfCorrect context.2 auxiliarySelf auxiliaryNames := by
    intro name index found
    exact ⟨.anonymous, rfl, trivial⟩
  have initial := clean.good reader base (Kernel.Reader.paramOf params) auxiliarySelf
    (ExpressionState.Related auxiliaryNames context.2.univCtx params)
  have checked := MetadataMode.pass3CompileRecords_correct reader base auxiliarySelf auxiliaryNames params bindings context
    arity aligned auxiliaryExternal auxiliaryBindings source before initial clean.2.2
  rw [ran] at checked
  have cache := (CacheFrame.records source context before output after ran).trans clean.2.1
  exact ⟨⟨checked.1.1, cache, checked.2.2 output rfl⟩,
    growth_retarget reader base (Kernel.Reader.paramOf params) auxiliarySelf self before after checked.2.1⟩

theorem ordinary_scoped (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (source : Expr) (scope : ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) source)
    (before after : BlockState) (output : Ixon.Expr × UInt64)
    (clean : DefinitionEmission.Clean bindings before)
    (ran : rawRun (compileExprPartial source) context before = (.ok output, after)) :
    ExpressionState.Checked reader base (Kernel.Reader.paramOf params) self
      (ExpressionState.Related names context.2.univCtx params) bindings source before (.ok output, after) ∧
        after.p3MetaMode = false := by
  have good := clean.good reader base (Kernel.Reader.paramOf params) self
    (ExpressionState.Related names context.2.univCtx params)
  have checked := ExpressionScope.partial_scoped reader base self names params bindings context arity aligned external source scope before good
  have mode := (MetadataMode.Frame.compileExprPartial source context before).1.trans clean.2.2
  rw [ran] at checked mode
  exact ⟨checked, mode⟩

/-- The public expression entry from a fresh per-declaration cache. Only the
payload expression needs the self-scope condition. Metadata source expressions
have no such premise; successful records restore the cache before payload work. -/
theorem compile_scoped (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (source : Expr) (scope : ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) source)
    (before after : BlockState) (output : Ixon.Expr × UInt64)
    (clean : DefinitionEmission.Clean bindings before)
    (ran : rawRun (compileExpr source) context before = (.ok output, after)) :
    ExpressionState.Checked reader base (Kernel.Reader.paramOf params) self
      (ExpressionState.Related names context.2.univCtx params) bindings source before (.ok output, after) ∧
        after.p3MetaMode = false := by
  unfold compileExpr at ran
  simp only [rawRun_bind, rawRun_read] at ran
  by_cases pass3 : context.1.pass3 = true
  · simp only [pass3, ↓reduceIte] at ran
    by_cases empty : context.1.p3Sources.isEmpty = true
    · simp only [empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ran
      exact ordinary_scoped reader base self names params bindings context arity aligned external source scope before after output clean ran
    · have nonempty : context.1.p3Sources.isEmpty = false := Bool.eq_false_iff.mpr empty
      simp only [nonempty, Bool.not_false, ↓reduceIte] at ran
      obtain ⟨done, middle, recordsRan, payloadRan⟩ := PreseedReferences.bind_ok _ _ context before output after ran
      have records := records_empty reader base self names params bindings context arity aligned external source before middle done clean recordsRan
      have payload := ordinary_scoped reader base self names params bindings context arity aligned external source scope middle after output records.1 payloadRan
      exact ⟨⟨payload.1.1, ExpressionState.extends_trans records.2 payload.1.2.1, payload.1.2.2⟩, payload.2⟩
  · simp only [pass3, Bool.false_eq_true, ↓reduceIte] at ran
    rw [compileExprTotal_eq_partial] at ran
    exact ordinary_scoped reader base self names params bindings context arity aligned external source scope before after output clean ran

end Ix.CompileCert.MetadataErasure
