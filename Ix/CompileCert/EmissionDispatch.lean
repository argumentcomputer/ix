import Ix.CompileCert.EmissionBlocks

/-! # Public constant dispatch: every block decodes exactly

`Ix.CompileM.compileConstantInfo` installs the singleton mutual context and
runs the kind's preseeded block compiler, so dispatch is exactly the kind's
block compiler in the singleton context (`*_run`), and the inductive kinds
resolve their constructors without touching the state (`collect_state`).
This module proves:

* the dispatch equations, for every `ConstantInfo` kind;
* `constant_codec`: for every kind, a successful compile from a state whose
  tables are on the wire returns a block that decodes exactly (CT-15's
  `FamilyWire.constant_codec`);
* the mutual payload's count guards (`PayloadArrays`: the outer and nested
  array counts the wire format needs) and `mutualBlock_codec` (CT-15's
  `FamilyWire.mutualBlock_codec`). -/

namespace Ix.CompileCert.EmissionDispatch

open Ix.CompileM Ix.CompileCert
open Ix.Sharing.Verify (BlockWireTablesWF ConstantInfoHeaderWF MutConstHeaderWF BlockResultCodecWF)

/-! ## Dispatch -/

/-- The singleton mutual context the dispatcher installs. -/
def singletonContext (name : Ix.Name) (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with mutCtx := (Std.TreeMap.empty : MutCtx).insert name 0 })

/-- The definition-like source data of the three definition-like kinds. -/
def sourceData : ConstantInfo → Option Ix.Def
  | .defnInfo value => some (definitionValData value)
  | .thmInfo value => some (theoremValData value)
  | .opaqueInfo value => some (opaqueValData value)
  | _ => none

theorem compileDefinitionInfo_eq (source : DefinitionVal) :
    compileDefinitionInfo source = compileDefinitionDataInfo (definitionValData source) := rfl

/-- **Definition-like dispatch** is the preseeded definition-like block in
the singleton context. -/
theorem definition_run (context : CompileEnv × BlockEnv)
    (info : ConstantInfo) (source : Ix.Def) (view : sourceData info = some source) (state : BlockState) :
    rawRun (compileConstantInfo info) context state =
      rawRun (compileDefinitionDataInfo source) (singletonContext source.name context) state := by
  cases info <;> simp only [sourceData, reduceCtorEq, Option.some.injEq] at view
  all_goals subst view
  · show rawRun (compileDefinitionConstantInfo _) context state = _
    simp only [compileDefinitionConstantInfo, withMutCtx,
      rawRun_withBlockEnv, compileDefinitionInfo_eq]
    rfl
  · show rawRun (compileTheoremConstantInfo _) context state = _
    simp only [compileTheoremConstantInfo, withMutCtx,
      rawRun_withBlockEnv, compileTheoremInfo]
    rfl
  · show rawRun (compileOpaqueConstantInfo _) context state = _
    simp only [compileOpaqueConstantInfo, withMutCtx,
      rawRun_withBlockEnv, compileOpaqueInfo]
    rfl

theorem axiom_run (context : CompileEnv × BlockEnv)
    (source : AxiomVal) (state : BlockState) :
    rawRun (compileConstantInfo (.axiomInfo source)) context state =
      rawRun (compileAxiomInfo source) (singletonContext source.cnst.name context) state := by
  show rawRun (compileConstantInfoCore (.axiomInfo source)) context state = _
  simp only [compileConstantInfoCore, withMutCtx,
    rawRun_withBlockEnv]
  rfl

theorem quotient_run (context : CompileEnv × BlockEnv)
    (source : QuotVal) (state : BlockState) :
    rawRun (compileConstantInfo (.quotInfo source)) context state =
      rawRun (compileQuotientInfo source) (singletonContext source.cnst.name context) state := by
  show rawRun (compileQuotientConstantInfo source) context state = _
  simp only [compileQuotientConstantInfo, withMutCtx,
    rawRun_withBlockEnv]
  rfl

theorem recursor_run (context : CompileEnv × BlockEnv)
    (source : RecursorVal) (state : BlockState) :
    rawRun (compileConstantInfo (.recInfo source)) context state =
      rawRun (compileRecursorInfo source) (singletonContext source.cnst.name context) state := by
  show rawRun (compileRecursorConstantInfo source) context state = _
  simp only [compileRecursorConstantInfo, withMutCtx,
    rawRun_withBlockEnv]
  rfl

theorem inductive_run (context : CompileEnv × BlockEnv)
    (source : InductiveVal) (state : BlockState) :
    rawRun (compileConstantInfo (.inductInfo source)) context state =
      rawRun (compileInductiveInfo source) (singletonContext source.cnst.name context) state := by
  show rawRun (compileInductiveConstantInfo source) context state = _
  simp only [compileInductiveConstantInfo, withMutCtx,
    rawRun_withBlockEnv]
  rfl

theorem constructor_run (context : CompileEnv × BlockEnv)
    (source : ConstructorVal) (state : BlockState) :
    rawRun (compileConstantInfo (.ctorInfo source)) context state =
      rawRun (compileConstructorInfo source) (singletonContext source.cnst.name context) state := by
  show rawRun (compileConstructorConstantInfo source) context state = _
  simp only [compileConstructorConstantInfo, withMutCtx,
    rawRun_withBlockEnv]
  rfl

/-! ## Constructor resolution -/

theorem find_state (name : Ix.Name) (context : CompileEnv × BlockEnv) (state : BlockState) :
    (rawRun (findConst name) context state).2 = state := by
  simp only [findConst, rawRun_bind, rawRun_read]
  cases context.1.env.get? name <;> rfl

/-- Resolving a family's constructors changes no
state. -/
theorem collect_state (context : CompileEnv × BlockEnv) :
    ∀ (names : List Ix.Name) (initial : Array ConstructorVal) (state : BlockState),
      (rawRun (collectInductiveConstructors names initial) context state).2 = state := by
  intro names
  induction names with
  | nil => intro initial state; rfl
  | cons name rest ih =>
    intro initial state
    rw [collectInductiveConstructors, rawRun_bind]
    have found := find_state name context state
    cases ran : rawRun (findConst name) context state with
    | mk outcome middle =>
      rw [ran] at found
      cases outcome with
      | error error => exact found
      | ok value =>
        dsimp only at found ⊢
        subst found
        cases value
        all_goals first
          | rfl
          | exact ih _ _

/-- The family's own mutual context. -/
def familyContext (source : InductiveVal) (constructors : Array ConstructorVal)
    (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with mutCtx := buildInductiveMutCtx source constructors })

/-- **A standalone inductive's dispatch** resolves its constructors without
changing the state, then runs the preseeded family block in the family's
mutual context. -/
theorem family_run (context : CompileEnv × BlockEnv)
    (source : InductiveVal) {before after : BlockState} {output : BlockResult}
    (ran : rawRun (compileInductiveInfo source) context before = (.ok output, after)) :
    ∃ constructors, rawRun (lookupInductiveConstructors source) context before = (.ok constructors, before) ∧
      rawRun (compileInductiveFamilyInfo source constructors) (familyContext source constructors context) before =
        (.ok output, after) := by
  unfold compileInductiveInfo at ran
  obtain ⟨constructors, middle, found, compiled⟩ := bind_ok ran
  have same := collect_state context source.ctors.toList #[] before
  change (rawRun (lookupInductiveConstructors source) context before).2 = before at same
  rw [found] at same
  subst same
  exact ⟨constructors, found, compiled⟩

/-! ## Every dispatch kind decodes exactly -/

theorem inductive_codec (context : CompileEnv × BlockEnv)
    (source : InductiveVal) {before after : BlockState} {output : BlockResult}
    (wire : BlockWireTablesWF before)
    (ran : rawRun (compileInductiveInfo source) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  obtain ⟨constructors, _, compiled⟩ := family_run context source ran
  exact EmissionBlocks.familyInfo_codec (familyContext source constructors context) source constructors
    wire compiled

/-- **Every public dispatch kind's block decodes exactly**: a successful
compile from a state whose tables are on the wire returns a wire-valid block
whose stored bytes decode to it. No source semantics, projection correspondence or admission is
claimed here. -/
theorem constant_codec (context : CompileEnv × BlockEnv)
    (info : ConstantInfo) {before after : BlockState} {output : BlockResult}
    (wire : BlockWireTablesWF before)
    (ran : rawRun (compileConstantInfo info) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  cases info with
  | defnInfo value =>
    rw [definition_run context _ (definitionValData value) rfl] at ran
    exact EmissionBlocks.definitionInfo_codec (singletonContext _ context) _ wire ran
  | thmInfo value =>
    rw [definition_run context _ (theoremValData value) rfl] at ran
    exact EmissionBlocks.definitionInfo_codec (singletonContext _ context) _ wire ran
  | opaqueInfo value =>
    rw [definition_run context _ (opaqueValData value) rfl] at ran
    exact EmissionBlocks.definitionInfo_codec (singletonContext _ context) _ wire ran
  | axiomInfo value =>
    rw [axiom_run context] at ran
    exact EmissionBlocks.axiomInfo_codec (singletonContext value.cnst.name context) _ wire ran
  | quotInfo value =>
    rw [quotient_run context] at ran
    exact EmissionBlocks.quotientInfo_codec (singletonContext value.cnst.name context) _ wire ran
  | recInfo value =>
    rw [recursor_run context] at ran
    exact EmissionBlocks.recursorInfo_codec (singletonContext value.cnst.name context) _ wire ran
  | inductInfo value =>
    rw [inductive_run context] at ran
    exact inductive_codec (singletonContext value.cnst.name context) value wire ran
  | ctorInfo value =>
    rw [constructor_run context] at ran
    unfold compileConstructorInfo at ran
    obtain ⟨parent, middle, found, compiled⟩ := bind_ok ran
    have same := find_state value.induct (singletonContext value.cnst.name context) before
    rw [found] at same
    subst same
    cases parent
    all_goals try (cases compiled)
    exact inductive_codec (singletonContext value.cnst.name context) _ wire compiled

/-! ## Mutual payload counts (CT-15's `PayloadArrays`) -/

theorem member_counts (member : Ixon.MutConst) :
    Emission.Yields (checkMutConstArrayCounts member) (fun _ => MutConstHeaderWF member) := by
  cases member <;> unfold checkMutConstArrayCounts
  · exact Emission.Yields.pure trivial
  all_goals exact Emission.Yields.bind (Emission.Yields.count _ _) (fun _ bound => Emission.Yields.pure bound)

theorem forIn_checks (values : List α) (action : α → CompileM Unit) (post : α → Prop)
    (checks : ∀ value, Emission.Yields (action value) (fun _ => post value)) :
    Emission.Yields (forIn values () (fun value _ => do action value; pure (ForInStep.yield ())))
      (fun _ => ∀ value ∈ values, post value) := by
  induction values with
  | nil => exact Emission.Yields.pure (by simp)
  | cons value rest ih =>
    intro context before output after ran
    rw [List.forIn_cons] at ran
    obtain ⟨step, middle, first, last⟩ := bind_ok ran
    obtain ⟨done, next, checked, returned⟩ := bind_ok first
    rw [rawRun_pure] at returned
    cases returned
    have head := checks value context before done _ checked
    have tail := ih context _ output after last
    intro query member
    rcases List.mem_cons.mp member with same | remaining
    · exact same ▸ head
    · exact tail query remaining

/-- **The mutual count guard admits exactly the header-valid payloads.** -/
theorem mutual_counts (members : Array Ixon.MutConst) :
    Emission.Yields (checkMutualPayloadCounts members) (fun _ => ConstantInfoHeaderWF (.muts members)) := by
  intro context before output after ran
  unfold checkMutualPayloadCounts at ran
  obtain ⟨count, middle, counted, rest⟩ := bind_ok ran
  have capacity := (Interning.checkedTableCount_value "mutual members" members.size context before
    (congrArg Prod.fst counted)).2
  obtain ⟨done, last, loopRan, _⟩ := bind_ok rest
  rw [← Array.forIn_toList] at loopRan
  have each := forIn_checks members.toList checkMutConstArrayCounts MutConstHeaderWF member_counts
    context middle done last loopRan
  exact ⟨capacity, fun member present => each member (by simpa using present)⟩

theorem member_state (member : Ixon.MutConst) : Preserves id (checkMutConstArrayCounts member) := by
  intro context before
  cases member
  · rfl
  all_goals
    simp only [checkMutConstArrayCounts]
    unfold checkedTableCount
    split <;> rfl

theorem mutual_state (members : Array Ixon.MutConst) : Preserves id (checkMutualPayloadCounts members) := by
  unfold checkMutualPayloadCounts
  apply Preserves.bind
  · intro context before
    exact Interning.checkedTableCount_state _ _ context before
  · intro _
    apply Preserves.bind
    · apply Preserves.forIn_array
      intro member _
      exact Preserves.bind (member_state member) (fun _ => Preserves.pure _ _)
    · intro _
      exact Preserves.pure _ _

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

/-- The pure mutual builder's result decodes exactly, given header-valid
members and wire-valid tables. -/
theorem build_mutual_codec (limits : Ix.Sharing.Exact.Limits) (classes : List MutConst)
    (members : Array Ixon.MutConst) (metadata : Array (Ix.Name × Ixon.ConstantMeta)) (state : BlockState)
    (bounds : ConstantInfoHeaderWF (.muts members)) (tables : BlockWireTablesWF state) (output : BlockResult)
    (ran : buildCompiledMutualBlock limits classes members metadata state = .ok output) :
    BlockResultCodecWF output := by
  unfold buildCompiledMutualBlock at ran
  cases chosen : standaloneMutConstInfo? members with
  | some info =>
    simp only [chosen] at ran
    obtain ⟨block, built, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    exact EmissionBlocks.block_codec (standalone_header members info bounds chosen) tables built _ _
  | none =>
    simp only [chosen] at ran
    obtain ⟨block, built, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    exact EmissionBlocks.block_codec bounds tables built _ _

/-- The mutual finisher changes no state and returns a block that decodes
exactly, given wire-valid tables: its own guard supplies the member
headers. -/
theorem finish_mutual_codec (context : CompileEnv × BlockEnv) (classes : List MutConst)
    (members : Array Ixon.MutConst) (metadata : Array (Ix.Name × Ixon.ConstantMeta)) {before after : BlockState}
    (tables : BlockWireTablesWF before) {output : BlockResult}
    (ran : rawRun (finishMutualCompilation classes members metadata) context before = (.ok output, after)) :
    after = before ∧ BlockResultCodecWF output := by
  unfold finishMutualCompilation at ran
  obtain ⟨done, middle, guarded, rest⟩ := bind_ok ran
  have same := mutual_state members context before
  rw [guarded] at same
  change middle = before at same
  subst same
  have bounds := mutual_counts members context middle done middle guarded
  obtain ⟨cache, cached, getRan, rest⟩ := bind_ok rest
  rw [rawRun_get] at getRan
  cases getRan
  obtain ⟨environment, environed, readRan, rest⟩ := bind_ok rest
  have readEq : rawRun (read : CompileM (CompileEnv × BlockEnv)) context middle = (.ok context, middle) := rfl
  rw [readEq] at readRan
  cases readRan
  try dsimp only at rest
  cases built : buildCompiledMutualBlock context.1.sharingLimits classes members metadata middle with
  | error error => rw [built] at rest; cases rest
  | ok result =>
    rw [built, rawRun_pure] at rest
    obtain ⟨values, states⟩ := Prod.mk.inj rest
    cases Except.ok.inj values
    exact ⟨states.symm, build_mutual_codec _ classes members metadata middle bounds tables output built⟩

/-- **A mutual block decodes exactly**: a successful compile from a state whose
tables are on the wire returns a block that decodes exactly; the mutual guard
supplies the nested array counts. -/
theorem mutualBlock_codec (context : CompileEnv × BlockEnv)
    (classes : List MutConst) {before after : BlockState} {output : BlockResult}
    (wire : BlockWireTablesWF before)
    (ran : rawRun (compileMutualBlock classes) context before = (.ok output, after)) :
    BlockResultCodecWF output := by
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, seededState, seeded, compiled⟩ := bind_ok ran
  have valid := EmissionWire.seeded_valid _ (context.1, { context.2 with mutCtx := MutConst.ctx classes }) wire
    seeded
  unfold compileMutualPayload at compiled
  obtain ⟨payload, middle, payloadRan, finished⟩ := bind_ok compiled
  have tables := (EmissionWire.Safe.mutConsts classes (context.1, { context.2 with mutCtx := MutConst.ctx classes })
    _ payload middle valid payloadRan).1.1
  obtain ⟨members, roots, metadata⟩ := payload
  dsimp only at finished
  exact (finish_mutual_codec _ classes members metadata tables finished).2

end Ix.CompileCert.EmissionDispatch
