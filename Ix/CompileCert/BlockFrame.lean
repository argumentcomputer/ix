import Ix.CompileCert.PayloadFrame
import Ix.CompileDriver

/-! Head-claim preservation through expression-table collection, preseeding
and block assembly. These statements cover the production definitions on
arbitrary initial states, including error effects. The table worklists use
the production module's proved runtime equations; these frames do not assert
semantic correspondence of the resulting declarations. -/

namespace Ix.CompileCert.HeadWriterFrame

open Ix Ix.CompileM

theorem Frame.collectExprTableUnivs (levels : List Level) (univs : Array Ixon.Univ) :
    Frame (collectExprTableUnivs levels univs) := by
  induction levels generalizing univs with
  | nil => exact Frame.pure _
  | cons level levels ih =>
    rw [Ix.CompileM.collectExprTableUnivs]
    exact Frame.bind (Frame.compileUniv level) fun _ => ih _

theorem Frame.collectExprTablesStructural (context : Address) (mutualContext : MutCtx)
    (params : List Name) (expr : Expr) (acc : ExprTableCollection) :
    Frame (collectExprTablesStructural context mutualContext params expr acc) := by
  induction expr generalizing acc
  all_goals try cases ‹Lean.Literal›
  all_goals
    rcases acc with ⟨refs, univs, seen⟩
    rw [Ix.CompileM.collectExprTablesStructural]
    split
    · exact Frame.pure _
    · with_reducible repeat' first
        | exact Frame.pure _
        | exact Frame.throw _
        | exact Frame.compileUniv _
        | exact Frame.lookupConstAddr _
        | exact Frame.storeBlob _
        | exact Frame.collectExprTableUnivs _ _
        | refine Frame.bind ?_ (fun value => ?_)
        | dsimp only
        | split
        | apply_assumption

theorem Frame.collectExprTables (expr : Expr) (context : Address) (acc : ExprTableCollection) :
    Frame (collectExprTables expr context acc) :=
  Frame.bind Frame.readBlock fun _ => Frame.collectExprTablesStructural _ _ _ _ _

theorem Frame.collectExprTablesWorklist (expr : Expr) (context : Address) (acc : ExprTableCollection) :
    Frame (Ix.CompileM.collectExprTablesWorklist expr context acc) := by
  rw [← Ix.CompileM.collectExprTables_eq_worklist]
  exact Frame.collectExprTables expr context acc

theorem Frame.collectPreseedExprs (roots : List (Expr × List Name)) (acc : ExprTableCollection) :
    Frame (collectPreseedExprs roots acc) := by
  induction roots generalizing acc with
  | nil => exact Frame.pure _
  | cons root roots ih =>
    rcases root with ⟨expr, params⟩
    rw [Ix.CompileM.collectPreseedExprs]
    exact Frame.bind (Frame.withUnivCtx (Frame.collectExprTables _ _ _) _) fun _ => ih _

theorem Frame.internPreseedRefs (refs : List Address) (previous : Option Address) :
    Frame (internPreseedRefs refs previous) := by
  induction refs generalizing previous with
  | nil => exact Frame.pure _
  | cons address refs ih =>
    rw [Ix.CompileM.internPreseedRefs]
    with_reducible repeat' first
      | exact ih _
      | exact Frame.pure _
      | exact Frame.internRef _
      | apply Frame.discard
      | refine Frame.bind ?_ (fun value => ?_)
      | split

theorem Frame.canonPreseedUnivs (univs : List Ixon.Univ) (acc : Array Ixon.Univ) :
    Frame (canonPreseedUnivs univs acc) := by
  induction univs generalizing acc with
  | nil => exact Frame.pure _
  | cons univ univs ih =>
    rw [Ix.CompileM.canonPreseedUnivs]
    exact Frame.bind (Frame.canonUnivCached univ) fun _ => ih _

theorem Frame.internPreseedUnivs (univs : List (ByteArray × Ixon.Univ))
    (previous : Option ByteArray) : Frame (internPreseedUnivs univs previous) := by
  induction univs generalizing previous with
  | nil => exact Frame.pure _
  | cons entry univs ih =>
    rcases entry with ⟨key, univ⟩
    rw [Ix.CompileM.internPreseedUnivs]
    with_reducible repeat' first
      | exact ih _
      | exact Frame.pure _
      | exact Frame.internUniv _
      | apply Frame.discard
      | refine Frame.bind ?_ (fun value => ?_)
      | split

theorem Frame.preseedExprTables (roots : Array (Expr × List Name)) :
    Frame (preseedExprTables roots) := by
  unfold Ix.CompileM.preseedExprTables
  with_reducible repeat' first
    | exact Frame.collectPreseedExprs _ _
    | exact Frame.internPreseedRefs _ _
    | exact Frame.canonPreseedUnivs _ _
    | (unfold Ix.CompileM.checkPreseedUnivs; split <;> first | exact Frame.pure _ | exact Frame.throw _)
    | exact Frame.internPreseedUnivs _ _
    | apply Frame.modify; intro _; rfl
    | refine Frame.bind ?_ (fun value => ?_)

theorem Frame.preseedTableWorklist (roots : Array (Expr × List Name)) :
    Frame (Ix.CompileM.TableWorklist.preseed roots) := by
  rw [← Ix.CompileM.preseedExprTables_eq_worklist]
  exact Frame.preseedExprTables roots

theorem Frame.readContext : Frame (MonadReader.read : CompileM (CompileEnv × BlockEnv)) := by
  intro _ _
  rfl

theorem Frame.liftSharing (result : Except CompileError Ixon.Constant) : Frame (liftSharing result) := by
  cases result with
  | ok _ => exact Frame.pure _
  | error _ => exact Frame.throw _

theorem Frame.buildBlockConstant (info : Ixon.ConstantInfo) (refs : Array Address)
    (univs : Array Ixon.Univ) : Frame (buildBlockConstant info refs univs) :=
  Frame.bind Frame.readContext fun _ => Frame.liftSharing _

theorem Frame.checkMutConstArrayCounts (payload : Ixon.MutConst) : Frame (checkMutConstArrayCounts payload) := by
  cases payload <;> unfold Ix.CompileM.checkMutConstArrayCounts
  · exact Frame.pure _
  all_goals exact Frame.bind (Frame.checkedTableCount _ _) (fun _ => Frame.pure _)

theorem Frame.checkMutualPayloadCounts (payloads : Array Ixon.MutConst) : Frame (checkMutualPayloadCounts payloads) := by
  unfold Ix.CompileM.checkMutualPayloadCounts
  apply Frame.bind (Frame.checkedTableCount _ _)
  intro _
  apply Frame.bind
  · apply frame_forIn_array
    intro payload _
    exact Frame.bind (Frame.checkMutConstArrayCounts payload) (fun _ => Frame.pure _)
  · intro _; exact Frame.pure _

theorem Frame.finishMutualCompilation (classes : List (List MutConst))
    (payloads : Array Ixon.MutConst) (metas : Array (Name × Ixon.ConstantMeta)) :
    Frame (finishMutualCompilation classes payloads metas) := by
  unfold Ix.CompileM.finishMutualCompilation
  apply Frame.bind (Frame.checkMutualPayloadCounts payloads)
  intro _
  apply Frame.bind Frame.get
  intro cache
  apply Frame.bind Frame.readContext
  intro context
  dsimp only
  split
  · exact Frame.pure _
  · exact Frame.throw _

theorem Frame.compileMutualPayload (classes : List (List MutConst)) :
    Frame (compileMutualPayload classes) :=
  Frame.bind (Frame.compileMutConsts classes) fun _ => Frame.finishMutualCompilation _ _ _

theorem Frame.compileMutualBlock (classes : List (List MutConst)) :
    Frame (compileMutualBlock classes) :=
  Frame.withMutCtx (Frame.bind (Frame.preseedExprTables _) fun _ => Frame.compileMutualPayload _) _

theorem Frame.findConst (name : Name) : Frame (findConst name) := by
  unfold Ix.CompileM.findConst
  apply Frame.bind Frame.read
  intro env
  split
  · exact Frame.pure _
  · exact Frame.throw _

theorem Frame.collectInductiveConstructors (names : List Name) (acc : Array ConstructorVal) :
    Frame (collectInductiveConstructors names acc) := by
  induction names generalizing acc with
  | nil => exact Frame.pure _
  | cons name names ih =>
    rw [Ix.CompileM.collectInductiveConstructors]
    apply Frame.bind (Frame.findConst name)
    intro source
    split
    · exact ih _
    · exact Frame.throw _

theorem Frame.lookupInductiveConstructors (inductiveVal : InductiveVal) :
    Frame (lookupInductiveConstructors inductiveVal) := Frame.collectInductiveConstructors _ _

theorem Frame.finishInductiveFamilyBlock (inductiveVal : InductiveVal)
    (ind : Ixon.Inductive) (indMeta : Ixon.ConstantMeta)
    (ctorMetaPairs : Array (Name × Ixon.ConstantMeta)) :
    Frame (finishInductiveFamilyBlock inductiveVal ind indMeta ctorMetaPairs) :=
  Frame.bind (Frame.checkedTableCount _ _) fun _ =>
  Frame.bind (Frame.checkedTableCount _ _) fun _ =>
  Frame.bind Frame.get fun _ =>
    Frame.bind (Frame.timedC (Frame.buildBlockConstant _ _ _) _) fun _ => Frame.pure _

theorem Frame.finishConstantWithSharing (info : Ixon.ConstantInfo)
    (metadata : Ixon.ConstantMeta) : Frame (finishConstantWithSharing info metadata) :=
  Frame.bind Frame.get fun _ =>
    Frame.bind (Frame.buildBlockConstant _ _ _) fun _ => Frame.pure _

theorem Frame.finishConstantInfoWithSharing (info : Ixon.ConstantInfo)
    (metadata : Ixon.ConstantMeta) : Frame (finishConstantInfoWithSharing info metadata) :=
  Frame.finishConstantWithSharing _ _

theorem Frame.compileDefinitionBlock (definition : DefinitionVal) : Frame (compileDefinitionBlock definition) :=
  Frame.bind (Frame.compileDefinition _) fun _ =>
    Frame.timedC (Frame.finishConstantInfoWithSharing _ _) _

theorem Frame.compileDefinitionInfo (definition : DefinitionVal) : Frame (compileDefinitionInfo definition) :=
  Frame.bind (Frame.preseedExprTables _) fun _ => Frame.compileDefinitionBlock _

theorem Frame.compileDefinitionDataBlock (definition : Def) : Frame (compileDefinitionDataBlock definition) :=
  Frame.bind (Frame.compileDefinitionData _) fun _ =>
    Frame.timedC (Frame.finishConstantInfoWithSharing _ _) _

theorem Frame.compileDefinitionDataInfo (definition : Def) : Frame (compileDefinitionDataInfo definition) :=
  Frame.bind (Frame.preseedExprTables _) fun _ => Frame.compileDefinitionDataBlock _

theorem Frame.compileTheoremInfo (declaration : TheoremVal) : Frame (compileTheoremInfo declaration) :=
  Frame.compileDefinitionDataInfo _

theorem Frame.compileOpaqueInfo (declaration : OpaqueVal) : Frame (compileOpaqueInfo declaration) :=
  Frame.compileDefinitionDataInfo _

theorem Frame.compileAxiomBlock (declaration : AxiomVal) : Frame (compileAxiomBlock declaration) :=
  Frame.bind (Frame.compileAxiom _) fun _ =>
    Frame.timedC (Frame.finishConstantInfoWithSharing _ _) _

theorem Frame.compileAxiomInfo (declaration : AxiomVal) : Frame (compileAxiomInfo declaration) :=
  Frame.bind (Frame.preseedExprTables _) fun _ => Frame.compileAxiomBlock _

theorem Frame.compileQuotientBlock (declaration : QuotVal) : Frame (compileQuotientBlock declaration) :=
  Frame.bind (Frame.compileQuotient _) fun _ =>
    Frame.timedC (Frame.finishConstantInfoWithSharing _ _) _

theorem Frame.compileQuotientInfo (declaration : QuotVal) : Frame (compileQuotientInfo declaration) :=
  Frame.bind (Frame.preseedExprTables _) fun _ => Frame.compileQuotientBlock _

theorem Frame.compileRecursorBlock (declaration : RecursorVal) : Frame (compileRecursorBlock declaration) :=
  Frame.bind (Frame.compileRecursor _) fun _ =>
    Frame.timedC (Frame.finishConstantInfoWithSharing _ _) _

theorem Frame.compileRecursorInfo (declaration : RecursorVal) : Frame (compileRecursorInfo declaration) :=
  Frame.bind (Frame.preseedExprTables _) fun _ => Frame.compileRecursorBlock _

theorem Frame.compileInductiveFamilyBlock (declaration : InductiveVal) (ctors : Array ConstructorVal) :
    Frame (compileInductiveFamilyBlock declaration ctors) :=
  Frame.bind (Frame.compileInductive _ _) fun _ => Frame.finishInductiveFamilyBlock _ _ _ _

theorem Frame.compileInductiveFamilyInfo (declaration : InductiveVal) (ctors : Array ConstructorVal) :
    Frame (compileInductiveFamilyInfo declaration ctors) :=
  Frame.bind (Frame.preseedExprTables _) fun _ => Frame.compileInductiveFamilyBlock _ _

theorem Frame.compileInductiveInfo (declaration : InductiveVal) : Frame (compileInductiveInfo declaration) :=
  Frame.bind (Frame.lookupInductiveConstructors _) fun _ =>
    Frame.withMutCtx (Frame.compileInductiveFamilyInfo _ _) _

theorem Frame.compileConstructorInfo (declaration : ConstructorVal) : Frame (compileConstructorInfo declaration) := by
  unfold Ix.CompileM.compileConstructorInfo
  apply Frame.bind (Frame.findConst _)
  intro source
  split
  · exact Frame.compileInductiveInfo _
  · exact Frame.throw _

theorem Frame.compileConstantInfo (source : ConstantInfo) : Frame (compileConstantInfo source) := by
  cases source <;> unfold Ix.CompileM.compileConstantInfo
  all_goals with_reducible repeat' first
    | exact Frame.compileDefinitionInfo _
    | exact Frame.compileTheoremInfo _
    | exact Frame.compileOpaqueInfo _
    | exact Frame.compileAxiomInfo _
    | exact Frame.compileQuotientInfo _
    | exact Frame.compileRecursorInfo _
    | exact Frame.compileInductiveInfo _
    | exact Frame.compileConstructorInfo _
    | apply Frame.withMutCtx
    | unfold Ix.CompileM.compileConstantInfoCore
    | unfold Ix.CompileM.compileDefinitionConstantInfo
    | unfold Ix.CompileM.compileTheoremConstantInfo
    | unfold Ix.CompileM.compileOpaqueConstantInfo
    | unfold Ix.CompileM.compileQuotientConstantInfo
    | unfold Ix.CompileM.compileRecursorConstantInfo
    | unfold Ix.CompileM.compileInductiveConstantInfo
    | unfold Ix.CompileM.compileConstructorConstantInfo

theorem Frame.constAddrLookup : Frame constAddrLookup :=
  Frame.bind Frame.read fun _ => Frame.bind Frame.get fun _ => Frame.pure _

theorem Frame.sortConstsCore (sources : List MutConst) : Frame (sortConstsCore sources) := by
  unfold Ix.CompileM.sortConstsCore
  apply Frame.bind Frame.constAddrLookup
  intro addresses
  split
  · exact Frame.pure _
  · exact Frame.throw _

theorem Frame.sortConsts (sources : List MutConst) : Frame (sortConsts sources) :=
  Frame.timedC (Frame.sortConstsCore sources) _

theorem Frame.collectMutConstConstructors (names : List Name) (acc : Array ConstructorVal) :
    Frame (collectMutConstConstructors names acc) := by
  induction names generalizing acc with
  | nil => exact Frame.pure _
  | cons name names ih =>
    rw [Ix.CompileM.collectMutConstConstructors]
    apply Frame.bind (Frame.findConst name)
    intro source
    split
    · exact ih _
    · exact Frame.throw _

theorem Frame.mkIndc (declaration : InductiveVal) : Frame (MutConst.mkIndc declaration) :=
  Frame.bind (Frame.collectMutConstConstructors _ _) fun _ => Frame.pure _

theorem Frame.collectMutConst? (source : ConstantInfo) : Frame (collectMutConst? source) := by
  cases source <;> unfold Ix.CompileM.collectMutConst?
  all_goals first
    | exact Frame.pure _
    | exact Frame.bind (Frame.mkIndc _) (fun _ => Frame.pure _)

theorem Frame.resolveMutConst? (name : Name) : Frame (resolveMutConst? name) :=
  Frame.bind (Frame.findConst name) fun source => Frame.collectMutConst? source

theorem Frame.collectMutConsts (names : List Name) (acc : Array MutConst) :
    Frame (collectMutConsts names acc) := by
  induction names generalizing acc with
  | nil => exact Frame.pure _
  | cons name names ih =>
    rw [Ix.CompileM.collectMutConsts]
    exact Frame.bind (Frame.resolveMutConst? name) fun _ => ih _

theorem Frame.compileMutualConstants (all : Set Name) : Frame (compileMutualConstants all) :=
  Frame.bind (Frame.collectMutConsts _ _) fun _ =>
    Frame.bind (Frame.sortConsts _) fun _ => Frame.compileMutualBlock _

theorem Frame.compileConstant (name : Name) : Frame (compileConstant name) := by
  unfold Ix.CompileM.compileConstant
  apply Frame.bind (Frame.findConst name)
  intro source
  apply Frame.bind Frame.readBlock
  intro context
  dsimp only
  split
  · exact Frame.compileConstantInfo source
  · exact Frame.compileMutualConstants _

theorem compileBlockPure_heads {env : CompileEnv} {all : Set Name} {name : Name}
    {result : BlockResult} {state : BlockState}
    (success : compileBlockPure env all name = .ok (result, state)) :
    state.p3Heads = #[] :=
  (Frame.compileConstant name).run_heads success

/-- The driver's source-form recompilation may select a different original
auxiliary family, but every selected path starts with an empty head table and
uses the framed plain compiler. No phase/ownership validity premise is needed
for this state-effect fact. -/
theorem compileConstNoAuxPure_heads {env : CompileEnv} {all : Set Name} {name : Name}
    {result : BlockResult} {state : BlockState}
    (success : compileConstNoAuxPure env name all = .ok (result, state)) :
    state.p3Heads = #[] := by
  unfold compileConstNoAuxPure at success
  dsimp only [Id.run, bind, pure] at success
  with_reducible repeat' first
    | exact (Frame.compileConstant name).run_heads success
    | split at success

end Ix.CompileCert.HeadWriterFrame
