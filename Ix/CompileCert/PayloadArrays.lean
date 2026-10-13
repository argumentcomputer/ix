import Ix.CompileCert.DeclarationHeaders
import Ix.CompileCert.EmissionWire

/-! Production admission of nested payload-array counts. Sharing supplies
wire-safe rewritten roots; the producer supplies only unchanged header fields.
The pure sharing API and its original success domains remain intact. -/

namespace Ix.CompileCert.PayloadArrays

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open Ix.Sharing.Verify (MutConstHeaderWF ConstantInfoHeaderWF BlockWireTablesWF)
open DeclarationHeaders (Returns)

theorem member_counts (member : Ixon.MutConst) :
    Returns (checkMutConstArrayCounts member) (fun _ => MutConstHeaderWF member) := by
  cases member <;> unfold checkMutConstArrayCounts
  all_goals simp only [MutConstHeaderWF]
  · exact Returns.pure True.intro
  all_goals
    with_reducible exact Returns.bind (Returns.count _ _) (fun _ bound => Returns.pure bound)

theorem forIn_checks (values : List α) (action : α → CompileM Unit) (post : α → Prop)
    (checks : ∀ value, Returns (action value) (fun _ => post value)) :
    Returns (forIn values () (fun value _ => do action value; pure (ForInStep.yield ())))
      (fun _ => ∀ value ∈ values, post value) := by
  induction values with
  | nil => exact Returns.pure (by simp)
  | cons value rest ih =>
    intro context before output after ran
    rw [List.forIn_cons] at ran
    obtain ⟨step, middle, first, last⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    obtain ⟨done, next, checked, returned⟩ := PreseedReferences.bind_ok _ _ context before step middle first
    rw [rawRun_pure] at returned
    cases Except.ok.inj (congrArg Prod.fst returned)
    have head := checks value context before done next checked
    have tail := ih context middle output after last
    intro query member
    rcases List.mem_cons.mp member with same | remaining
    · exact same ▸ head
    · exact tail query remaining

theorem mutual_counts (members : Array Ixon.MutConst) :
    Returns (checkMutualPayloadCounts members) (fun _ => ConstantInfoHeaderWF (.muts members)) := by
  intro context before output after ran
  unfold checkMutualPayloadCounts at ran
  obtain ⟨count, firstState, counted, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have capacity := (Interning.checkedTableCount_value "mutual members" members.size context before (congrArg Prod.fst counted)).2
  obtain ⟨done, finalState, loopRan, _⟩ := PreseedReferences.bind_ok _ _ context firstState output after rest
  rw [← Array.forIn_toList] at loopRan
  have each := forIn_checks members.toList checkMutConstArrayCounts MutConstHeaderWF member_counts
    context firstState done finalState loopRan
  exact ⟨capacity, fun member present => each member (by simpa using present)⟩

theorem member_state (member : Ixon.MutConst) (context : CompileEnv × BlockEnv) (before : BlockState) :
    (rawRun (checkMutConstArrayCounts member) context before).2 = before := by
  cases member
  · rfl
  all_goals
    simp only [checkMutConstArrayCounts]
    unfold checkedTableCount
    split <;> rfl

theorem forIn_frame (projection : BlockState → γ) (values : List α) (initial : β)
    (body : α → β → CompileM (ForInStep β))
    (each : ∀ value state, UniversePipeline.Preserves projection (body value state)) :
    UniversePipeline.Preserves projection (forIn values initial body) := by
  induction values generalizing initial with
  | nil => exact UniversePipeline.Preserves.pure _ _
  | cons value rest ih =>
    rw [List.forIn_cons]
    apply UniversePipeline.Preserves.bind (each value initial)
    intro step
    cases step with
    | done value => exact UniversePipeline.Preserves.pure _ _
    | yield value => exact ih value

theorem mutual_state (members : Array Ixon.MutConst) (context : CompileEnv × BlockEnv) (before : BlockState) :
    (rawRun (checkMutualPayloadCounts members) context before).2 = before := by
  have stable : UniversePipeline.Preserves id (checkMutualPayloadCounts members) := by
    unfold checkMutualPayloadCounts
    apply UniversePipeline.Preserves.bind
    · intro context before; exact Interning.checkedTableCount_state _ _ context before
    · intro _
      apply UniversePipeline.Preserves.bind
      · rw [← Array.forIn_toList]
        apply forIn_frame
        intro member _
        exact UniversePipeline.Preserves.bind (member_state member) (fun _ => UniversePipeline.Preserves.pure _ _)
      · intro _; exact UniversePipeline.Preserves.pure _ _
  exact stable context before

theorem recursor_rules (source : RecursorVal) (type : Ixon.Expr) (root : UInt64) (rules : RecursorRuleCompileState) :
    Returns (finishRecursorCompilation source type root rules) (fun output => output.1.rules.size < UInt64.size) := by
  unfold finishRecursorCompilation
  with_reducible repeat' first
    | exact Returns.pure (by assumption)
    | refine Returns.bind (Returns.count _ _) (fun _ bound => ?_)
    | refine Returns.bindAny _ (fun _ => ?_)

theorem inductive_ctors (source : InductiveVal) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Returns (finishInductiveCompilation source type root metadata constructors)
      (fun output => output.1.ctors.size < UInt64.size) := by
  unfold finishInductiveCompilation
  with_reducible repeat' first
    | exact Returns.pure (by assumption)
    | refine Returns.bind (Returns.count _ _) (fun _ bound => ?_)
    | refine Returns.bindAny _ (fun _ => ?_)

theorem inductiveData_ctors (source : Ind) (type : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState) :
    Returns (finishInductiveDataCompilation source type root metadata constructors)
      (fun output => output.1.ctors.size < UInt64.size) := by
  unfold finishInductiveDataCompilation
  with_reducible repeat' first
    | exact Returns.pure (by assumption)
    | refine Returns.bind (Returns.count _ _) (fun _ bound => ?_)
    | refine Returns.bindAny _ (fun _ => ?_)

theorem Returns.withBlockEnv (update : BlockEnv → BlockEnv) {action : CompileM α} {post : α → Prop}
    (holds : Returns action post) : Returns (withBlockEnv update action) post :=
  fun context before output after ran => holds (context.1, update context.2) before output after ran

theorem Returns.withCurrent (name : Name) {action : CompileM α} {post : α → Prop}
    (holds : Returns action post) : Returns (withCurrent name action) post := Returns.withBlockEnv _ holds

theorem Returns.withUnivCtx (params : List Name) {action : CompileM α} {post : α → Prop}
    (holds : Returns action post) : Returns (withUnivCtx params action) post :=
  Returns.bindAny _ (fun _ => Returns.withBlockEnv _ holds)

theorem recursor_compiled (source : RecursorVal) : Returns (compileRecursor source)
    (fun output => output.1.rules.size < UInt64.size) := by
  apply Returns.withCurrent
  apply Returns.withUnivCtx
  exact Returns.bindAny _ fun _ => Returns.bindAny _ fun type => Returns.bindAny _ fun rules => recursor_rules source type.1 type.2 rules

theorem inductive_compiled (source : InductiveVal) (constructors : Array ConstructorVal) : Returns (compileInductive source constructors)
    (fun output => output.1.ctors.size < UInt64.size) := by
  apply Returns.withCurrent
  apply Returns.withUnivCtx
  exact Returns.bindAny _ fun _ => Returns.bindAny _ fun type => Returns.bindAny _ fun metadata =>
    Returns.bindAny _ fun ctors => inductive_ctors source type.1 type.2 metadata ctors

theorem member_refuses (member : Ixon.MutConst) (context : CompileEnv × BlockEnv) (before : BlockState)
    (invalid : ¬MutConstHeaderWF member) :
    ∃ reason, rawRun (checkMutConstArrayCounts member) context before = (.error (.resourceLimit reason), before) := by
  cases member with
  | defn _ => exact False.elim (invalid True.intro)
  | indc value =>
    change ¬value.ctors.size < UInt64.size at invalid
    simp only [checkMutConstArrayCounts, rawRun_bind, checkedTableCount, invalid, ↓reduceIte]
    exact ⟨_, rfl⟩
  | recr value =>
    change ¬value.rules.size < UInt64.size at invalid
    simp only [checkMutConstArrayCounts, rawRun_bind, checkedTableCount, invalid, ↓reduceIte]
    exact ⟨_, rfl⟩

theorem outer_refuses (members : Array Ixon.MutConst) (context : CompileEnv × BlockEnv) (before : BlockState)
    (large : UInt64.size ≤ members.size) :
    ∃ reason, rawRun (checkMutualPayloadCounts members) context before = (.error (.resourceLimit reason), before) := by
  unfold checkMutualPayloadCounts
  rw [rawRun_bind]
  have noRoom : ¬members.size < UInt64.size := by omega
  simp only [checkedTableCount, noRoom, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem standalone_header (members : Array Ixon.MutConst) (info : Ixon.ConstantInfo)
    (bounds : ConstantInfoHeaderWF (.muts members)) (chosen : standaloneMutConstInfo? members = some info) :
    ConstantInfoHeaderWF info := by
  rcases members with ⟨members⟩
  cases members with
  | nil => change (none : Option Ixon.ConstantInfo) = some info at chosen; cases chosen
  | cons member rest =>
    cases rest with
    | cons next rest => change (none : Option Ixon.ConstantInfo) = some info at chosen; cases chosen
    | nil =>
      cases member with
      | defn value =>
        change some (Ixon.ConstantInfo.defn value) = some info at chosen
        cases Option.some.inj chosen
        trivial
      | indc value => change (none : Option Ixon.ConstantInfo) = some info at chosen; cases chosen
      | recr value =>
        change some (Ixon.ConstantInfo.recr value) = some info at chosen
        cases Option.some.inj chosen
        exact bounds.2 (.recr value) (by simp)

/-- The pure mutual builder retains its broad API. Header-count evidence and
the actual successful sharing run suffice for the main block's codec facts. -/
theorem build_mutual_codec (limits : Ix.Sharing.Exact.Limits) (classes : List (List MutConst))
    (members : Array Ixon.MutConst) (metadata : Array (Name × Ixon.ConstantMeta)) (state : BlockState)
    (bounds : ConstantInfoHeaderWF (.muts members)) (tables : BlockWireTablesWF state) (output : BlockResult)
    (ran : buildCompiledMutualBlock limits classes members metadata state = .ok output) :
    Ix.Sharing.Verify.BlockResultCodecWF output := by
  unfold buildCompiledMutualBlock at ran
  cases chosen : standaloneMutConstInfo? members with
  | some info =>
    simp only [chosen] at ran
    obtain ⟨block, built, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    exact Ix.Sharing.Verify.BlockResult.mk'_codecWF _ _ _
      (Ix.Sharing.Verify.buildConstantWithSharing_wireWF_headers (standalone_header members info bounds chosen) tables built)
  | none =>
    simp only [chosen] at ran
    obtain ⟨block, built, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    exact Ix.Sharing.Verify.BlockResult.mk'_codecWF _ _ _
      (Ix.Sharing.Verify.buildConstantWithSharing_wireWF_headers bounds tables built)

theorem finish_shared_codec (context : CompileEnv × BlockEnv) (info : Ixon.ConstantInfo) (metadata : Ixon.ConstantMeta)
    (before after : BlockState) (output : BlockResult) (header : ConstantInfoHeaderWF info) (tables : BlockWireTablesWF before)
    (ran : rawRun (timedC .sharing (finishConstantInfoWithSharing info metadata)) context before = (.ok output, after)) :
    after = before ∧ Ix.Sharing.Verify.BlockResultCodecWF output := by
  rw [DefinitionBlock.rawRun_timedC, DefinitionBlock.finish_run] at ran
  cases built : buildConstantWithSharing context.1.sharingLimits info before.refs before.univs with
  | error error => simp [built, Except.map] at ran
  | ok value =>
    simp only [built, Except.map, Prod.mk.injEq, Except.ok.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    exact ⟨rfl, Ix.Sharing.Verify.BlockResult.mk'_codecWF _ _ _
      (Ix.Sharing.Verify.buildConstantWithSharing_wireWF_headers header tables built)⟩

/-- Actual mutual finalization derives its nested payload bounds from the
new executable guard. No original-expression wire premise is needed. -/
theorem finish_mutual_codec (context : CompileEnv × BlockEnv) (classes : List (List MutConst))
    (members : Array Ixon.MutConst) (metadata : Array (Name × Ixon.ConstantMeta)) (before after : BlockState)
    (tables : BlockWireTablesWF before) (output : BlockResult)
    (ran : rawRun (finishMutualCompilation classes members metadata) context before = (.ok output, after)) :
    after = before ∧ Ix.Sharing.Verify.BlockResultCodecWF output := by
  unfold finishMutualCompilation at ran
  obtain ⟨done, middle, guarded, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have same := mutual_state members context before
  rw [guarded] at same
  dsimp only at same
  subst middle
  have bounds := mutual_counts members context before done before guarded
  have readContext : rawRun (read : CompileM (CompileEnv × BlockEnv)) context before = (.ok context, before) := rfl
  simp only [rawRun_bind, rawRun_get, readContext, Ix.PhaseTimers.withPhase,
    Ix.PhaseTimers.enterV, Ix.PhaseTimers.exitV, ite_self] at rest
  cases built : buildCompiledMutualBlock context.1.sharingLimits classes members metadata before with
  | error error => rw [built] at rest; cases rest
  | ok result =>
    rw [built, rawRun_pure] at rest
    obtain ⟨values, states⟩ := Prod.mk.inj rest
    cases Except.ok.inj values
    exact ⟨states.symm, build_mutual_codec _ classes members metadata before bounds tables output built⟩

end Ix.CompileCert.PayloadArrays
