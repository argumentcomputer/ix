import Ix.CompileCert.ExpressionFrame

/-! Head-claim preservation through source declaration payload compilation.
These facts compose the production expression frame with reader contexts and
metadata finalizers. Preseeding, block publication and the auxiliary tail are
separate boundaries; payload preservation alone does not certify a worker. -/

namespace Ix.CompileCert.HeadWriterFrame

open Ix Ix.CompileM

theorem Frame.withBlockEnv {action : CompileM α} (framed : Frame action)
    (update : BlockEnv → BlockEnv) : Frame (withBlockEnv update action) := by
  intro context state
  exact framed (context.1, update context.2) state

theorem Frame.withUnivCtx {action : CompileM α} (framed : Frame action)
    (params : List Name) : Frame (withUnivCtx params action) :=
  Frame.bind (Frame.modify _ (fun _ => rfl)) (fun _ => Frame.withBlockEnv framed _)

theorem Frame.withCurrent {action : CompileM α} (framed : Frame action)
    (name : Name) : Frame (withCurrent name action) := Frame.withBlockEnv framed _

theorem Frame.withMutCtx {action : CompileM α} (framed : Frame action)
    (context : Ix.MutCtx) : Frame (withMutCtx context action) := Frame.withBlockEnv framed _

theorem Frame.timedC {action : CompileM α} (framed : Frame action)
    (phase : Ix.PhaseTimers.Phase) : Frame (timedC phase action) := by
  intro context state
  simpa only [rawRun, Ix.CompileM.timedC, ExceptT.run, ExceptT.mk, StateT.run,
    Ix.PhaseTimers.enterV, Ix.PhaseTimers.exitV, ite_self] using
    framed context state

theorem Frame.takeArena : Frame takeArena := Frame.modifyGet _ (fun _ => rfl)
theorem Frame.takeMetaSharing : Frame takeMetaSharing := Frame.modifyGet _ (fun _ => rfl)
theorem Frame.takeMetaRefs : Frame takeMetaRefs := Frame.modifyGet _ (fun _ => rfl)
theorem Frame.takeUnivPatches : Frame takeUnivPatches := Frame.modifyGet _ (fun _ => rfl)
theorem Frame.resetArena : Frame resetArena := Frame.modify _ (fun _ => rfl)
theorem Frame.clearExprCache : Frame clearExprCache := Frame.modify _ (fun _ => rfl)
theorem Frame.recordDefHints (name : Name) (hints : Lean.ReducibilityHints) :
    Frame (recordDefHints name hints) := Frame.modify _ (fun _ => rfl)

theorem Frame.getMutCtxAddrs : Frame getMutCtxAddrs :=
  Frame.bind Frame.readBlock (fun _ => Frame.pure _)

theorem compileNames_heads (state : BlockState) (ambient : Std.HashMap Address ByteArray) (names : Array Name) :
    ∀ after, state.compileNames ambient names = .ok after → after.p3Heads = state.p3Heads := by
  unfold BlockState.compileNames
  rw [← Array.foldlM_toList]
  induction names.toList generalizing state with
  | nil => intro after success; cases Except.ok.inj success; rfl
  | cons name names ih =>
    rw [List.foldlM_cons]
    intro after success
    cases ran : state.compileName ambient name with
    | error error => simp only [ran, bind, Except.bind] at success; cases success
    | ok middle =>
      simp only [ran, bind, Except.bind] at success
      exact (ih middle after success).trans (compileName_heads state ambient name middle ran)

theorem Frame.compileNames (names : Array Name) : Frame (compileNames names) := by
  intro context state
  simp only [Ix.CompileM.compileNames, rawRun_bind, rawRun_get, rawRun_read, rawRun_applyBlockState]
  cases ran : state.compileNames context.1.blobs names with
  | error error => rfl
  | ok after => exact compileNames_heads state context.1.blobs names after ran

local macro "frame_metadata" : tactic => `(tactic|
  with_reducible repeat' first
    | exact Frame.takeArena
    | exact Frame.takeMetaSharing
    | exact Frame.takeMetaRefs
    | exact Frame.takeUnivPatches
    | exact Frame.clearExprCache
    | exact Frame.compileName _
    | exact Frame.compileNames _
    | exact Frame.getMutCtxAddrs
    | exact Frame.recordDefHints _ _
    | exact Frame.readBlock
    | exact Frame.pure _
    | refine Frame.bind ?_ (fun value => ?_))

theorem Frame.finishDefinitionDataCompilation (definition : Ix.Def)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64) (valueExpr : Ixon.Expr) (valueRoot : UInt64) :
    Frame (finishDefinitionDataCompilation definition typeExpr typeRoot valueExpr valueRoot) := by
  unfold Ix.CompileM.finishDefinitionDataCompilation
  with_reducible repeat' first
    | exact Frame.takeArena
    | exact Frame.takeMetaSharing
    | exact Frame.takeMetaRefs
    | exact Frame.takeUnivPatches
    | exact Frame.clearExprCache
    | exact Frame.compileName _
    | exact Frame.compileNames _
    | exact Frame.getMutCtxAddrs
    | exact Frame.recordDefHints _ _
    | exact Frame.readBlock
    | exact Frame.pure _
    | refine Frame.bind ?_ (fun value => ?_)

theorem Frame.compileDefinition (definition : Ix.DefinitionVal) :
    Frame (compileDefinition definition) := by
  apply Frame.withCurrent
  apply Frame.withUnivCtx
  exact Frame.bind Frame.resetArena fun _ =>
    Frame.bind (Frame.compileExpr _) fun type =>
    Frame.bind (Frame.compileExpr _) fun value =>
    Frame.finishDefinitionDataCompilation _ type.1 type.2 value.1 value.2

theorem Frame.compileTheorem (declaration : Ix.TheoremVal) : Frame (compileTheorem declaration) := by
  apply Frame.withCurrent
  apply Frame.withUnivCtx
  exact Frame.bind Frame.resetArena fun _ =>
    Frame.bind (Frame.compileExpr _) fun type =>
    Frame.bind (Frame.compileExpr _) fun value =>
    Frame.finishDefinitionDataCompilation _ type.1 type.2 value.1 value.2

theorem Frame.compileOpaque (declaration : Ix.OpaqueVal) : Frame (compileOpaque declaration) := by
  apply Frame.withCurrent
  apply Frame.withUnivCtx
  exact Frame.bind Frame.resetArena fun _ =>
    Frame.bind (Frame.compileExpr _) fun type =>
    Frame.bind (Frame.compileExpr _) fun value =>
    Frame.finishDefinitionDataCompilation _ type.1 type.2 value.1 value.2

theorem Frame.finishAxiomCompilation (declaration : Ix.AxiomVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64) :
    Frame (finishAxiomCompilation declaration typeExpr typeRoot) := by
  unfold Ix.CompileM.finishAxiomCompilation
  frame_metadata

theorem Frame.compileAxiom (declaration : Ix.AxiomVal) : Frame (compileAxiom declaration) := by
  apply Frame.withCurrent
  apply Frame.withUnivCtx
  exact Frame.bind Frame.resetArena fun _ =>
    Frame.bind (Frame.compileExpr _) fun type => Frame.finishAxiomCompilation _ type.1 type.2

theorem Frame.finishQuotientCompilation (declaration : Ix.QuotVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64) :
    Frame (finishQuotientCompilation declaration typeExpr typeRoot) := by
  unfold Ix.CompileM.finishQuotientCompilation
  frame_metadata

theorem Frame.compileQuotient (declaration : Ix.QuotVal) : Frame (compileQuotient declaration) := by
  apply Frame.withCurrent
  apply Frame.withUnivCtx
  exact Frame.bind Frame.resetArena fun _ =>
    Frame.bind (Frame.compileExpr _) fun type => Frame.finishQuotientCompilation _ type.1 type.2

theorem Frame.compileRecursorRule (rule : Ix.RecursorRule) : Frame (compileRecursorRule rule) :=
  Frame.bind (Frame.compileExpr _) (fun _ => Frame.pure _)

theorem Frame.compileRecursorRules (rules : List Ix.RecursorRule) (acc : RecursorRuleCompileState) :
    Frame (compileRecursorRules rules acc) := by
  induction rules generalizing acc with
  | nil => exact Frame.pure _
  | cons rule rules ih =>
    rw [Ix.CompileM.compileRecursorRules]
    exact Frame.bind (Frame.compileRecursorRule rule) fun _ => ih _

theorem Frame.finishRecursorCompilation (declaration : Ix.RecursorVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64) (rules : RecursorRuleCompileState) :
    Frame (finishRecursorCompilation declaration typeExpr typeRoot rules) := by
  unfold Ix.CompileM.finishRecursorCompilation
  frame_metadata

theorem Frame.compileRecursor (declaration : Ix.RecursorVal) : Frame (compileRecursor declaration) := by
  apply Frame.withCurrent
  apply Frame.withUnivCtx
  exact Frame.bind Frame.resetArena fun _ =>
    Frame.bind (Frame.compileExpr _) fun type =>
    Frame.bind (Frame.compileRecursorRules _ _) fun rules =>
    Frame.finishRecursorCompilation _ type.1 type.2 rules

theorem Frame.finishConstructorCompilation (declaration : Ix.ConstructorVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64) :
    Frame (finishConstructorCompilation declaration typeExpr typeRoot) := by
  unfold Ix.CompileM.finishConstructorCompilation
  frame_metadata

theorem Frame.compileConstructor (declaration : Ix.ConstructorVal) : Frame (compileConstructor declaration) := by
  apply Frame.withCurrent
  exact Frame.bind Frame.resetArena fun _ =>
    Frame.bind (Frame.compileExpr _) fun type => Frame.finishConstructorCompilation _ type.1 type.2

theorem Frame.takeInductiveTypeCompileMeta : Frame takeInductiveTypeCompileMeta := by
  unfold Ix.CompileM.takeInductiveTypeCompileMeta
  frame_metadata

theorem Frame.compileInductiveConstructors (ctors : List Ix.ConstructorVal)
    (acc : InductiveConstructorCompileState) : Frame (compileInductiveConstructors ctors acc) := by
  induction ctors generalizing acc with
  | nil => exact Frame.pure _
  | cons ctor ctors ih =>
    rw [Ix.CompileM.compileInductiveConstructors]
    exact Frame.bind (Frame.compileConstructor ctor) fun _ => ih _

theorem Frame.finishInductiveCompilation (declaration : Ix.InductiveVal)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64) (metadata : InductiveTypeCompileMeta)
    (ctors : InductiveConstructorCompileState) :
    Frame (finishInductiveCompilation declaration typeExpr typeRoot metadata ctors) := by
  unfold Ix.CompileM.finishInductiveCompilation
  frame_metadata

theorem Frame.compileInductive (declaration : Ix.InductiveVal) (ctors : Array Ix.ConstructorVal) :
    Frame (compileInductive declaration ctors) := by
  apply Frame.withCurrent
  apply Frame.withUnivCtx
  exact Frame.bind Frame.resetArena fun _ =>
    Frame.bind (Frame.compileExpr _) fun type =>
    Frame.bind Frame.takeInductiveTypeCompileMeta fun metadata =>
    Frame.bind (Frame.compileInductiveConstructors _ _) fun ctors =>
    Frame.finishInductiveCompilation _ type.1 type.2 metadata ctors

theorem Frame.compileDefinitionData (definition : Ix.Def) : Frame (compileDefinitionData definition) := by
  apply Frame.withCurrent
  apply Frame.withUnivCtx
  exact Frame.bind Frame.resetArena fun _ =>
    Frame.bind (Frame.compileExpr _) fun type =>
    Frame.bind (Frame.compileExpr _) fun value =>
    Frame.finishDefinitionDataCompilation _ type.1 type.2 value.1 value.2

theorem Frame.finishInductiveDataCompilation (declaration : Ix.Ind)
    (typeExpr : Ixon.Expr) (typeRoot : UInt64) (metadata : InductiveTypeCompileMeta)
    (ctors : InductiveConstructorCompileState) :
    Frame (finishInductiveDataCompilation declaration typeExpr typeRoot metadata ctors) := by
  unfold Ix.CompileM.finishInductiveDataCompilation
  frame_metadata

theorem Frame.compileInductiveData (declaration : Ix.Ind) : Frame (compileInductiveData declaration) := by
  apply Frame.withCurrent
  apply Frame.withUnivCtx
  exact Frame.bind Frame.resetArena fun _ =>
    Frame.bind (Frame.compileExpr _) fun type =>
    Frame.bind Frame.takeInductiveTypeCompileMeta fun metadata =>
    Frame.bind (Frame.compileInductiveConstructors _ _) fun ctors =>
    Frame.finishInductiveDataCompilation _ type.1 type.2 metadata ctors

theorem Frame.compileRecursorData (declaration : Ix.RecursorVal) : Frame (compileRecursorData declaration) :=
  Frame.compileRecursor declaration

theorem Frame.compileMutConstMember (member : Ix.MutConst) : Frame (compileMutConstMember member) := by
  cases member <;> unfold Ix.CompileM.compileMutConstMember
  all_goals with_reducible repeat' first
    | exact Frame.pure _
    | exact Frame.compileDefinitionData _
    | exact Frame.compileInductiveData _
    | exact Frame.compileRecursorData _
    | apply Frame.withCurrent
    | refine Frame.bind ?_ (fun value => ?_)

theorem Frame.compileEquivalentMutConsts (members : List Ix.MutConst) (state : MutConstCompileState) :
    Frame (compileEquivalentMutConsts members state) := by
  induction members generalizing state with
  | nil => exact Frame.pure _
  | cons member members ih =>
    rw [Ix.CompileM.compileEquivalentMutConsts]
    exact Frame.bind (Frame.compileMutConstMember member) fun _ => ih _

theorem Frame.compileMutConstClass (members : List Ix.MutConst) (state : MutConstCompileState) :
    Frame (compileMutConstClass members state) := by
  cases members with
  | nil => exact Frame.pure _
  | cons member members =>
    rw [Ix.CompileM.compileMutConstClass]
    exact Frame.bind (Frame.compileMutConstMember member) fun _ => Frame.compileEquivalentMutConsts members _

theorem Frame.compileMutConstClasses (classes : List (List Ix.MutConst)) (state : MutConstCompileState) :
    Frame (compileMutConstClasses classes state) := by
  induction classes generalizing state with
  | nil => exact Frame.pure _
  | cons members classes ih =>
    rw [Ix.CompileM.compileMutConstClasses]
    exact Frame.bind (Frame.compileMutConstClass members state) fun _ => ih _

theorem Frame.compileMutConsts (classes : List (List Ix.MutConst)) : Frame (compileMutConsts classes) :=
  Frame.bind (Frame.compileMutConstClasses _ _) (fun _ => Frame.pure _)

end Ix.CompileCert.HeadWriterFrame
