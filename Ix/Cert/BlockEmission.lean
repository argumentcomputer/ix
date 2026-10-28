import Ix.CompileCert.MutualInductiveReading

/-! # A block of several members, compiled one member per class

The compiler lays a block out in Lean's order, one member per class
(`compileMutualBlock (ms.map ([·]))`). Each member runs the emitter of its kind (a
definition's, an inductive's with its constructors, a recursor's), from a clean state, in the
block's mutual context; the emitters' theorems (`Emission.definition_correct`,
`Emission.inductiveData_correct`, `Emission.recursor_correct`) say each member's payload keeps
its source's skeleton and the in-flight reader reads its roots as terms related to the
source's. `classes_correct` folds them over the block, and `mutualBlock_correct` carries the
roots through the block's sharing to the emitted record (`SharingRoots.build_read`): the record
keeps the payloads' skeletons and its member reader reads every member's roots, in member
order, as terms related to the members' sources, for members sharing their level
parameters. -/

namespace Ix.Cert.BlockEmission

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM MemberReader)

/-- The source expressions of a member, in the order its payload's roots are. -/
def memberSources : MutConst → List Ix.Expr
  | .defn d => [d.type, d.value]
  | .indc i => i.type :: i.ctors.toList.map (·.cnst.type)
  | .recr r => r.cnst.type :: r.rules.toList.map (·.rhs)

/-- The level parameters of a member. -/
def memberLps : MutConst → List Ix.Name
  | .defn d => d.levelParams.toList
  | .indc i => i.levelParams.toList
  | .recr r => r.cnst.levelParams.toList

/-- A recursor payload's header: the source's counts, as natural numbers, and its rules' field
counts in range. -/
def RecHeader (source : Ix.RecursorVal) (target : Ixon.Recursor) : Prop :=
  target.lvls.toNat = source.cnst.levelParams.size ∧ target.params.toNat = source.numParams ∧
    target.indices.toNat = source.numIndices ∧ target.motives.toNat = source.numMotives ∧
    target.minors.toNat = source.numMinors ∧ ∀ rule ∈ source.rules.toList, rule.nfields < UInt64.size

/-- **The payload a member compiles to keeps its source's skeleton and headers.** -/
def PayloadOf : MutConst → Ixon.MutConst → Prop
  | .defn d, p => ∃ target, p = .defn target ∧ target = Emission.definitionPayload d target.typ target.value
  | .indc i, p => ∃ target, p = .indc target ∧ target = Emission.inductivePayload i target.typ target.ctors ∧
      List.Forall₂ (fun ctor t => t = Emission.constructorPayload ctor t.typ) i.ctors.toList target.ctors.toList ∧
      ProjectionLayout.IndHeader i target ∧
      List.Forall₂ ProjectionLayout.CtorHeader i.ctors.toList target.ctors.toList
  | .recr r, p => ∃ target, p = .recr target ∧ target = Emission.recursorPayload r target.typ target.rules ∧
      target.rules.toList.map (·.fields) = r.rules.toList.map (fun rule => rule.nfields.toUInt64) ∧
      RecHeader r target

/-- The rule loop compiles only rules whose field counts are in range. -/
theorem rules_bounded : ∀ (sources : List Ix.RecursorRule) (acc : RecursorRuleCompileState),
    Emission.Yields (compileRecursorRules sources acc) (fun _ => ∀ rule ∈ sources, rule.nfields < UInt64.size)
  | [], _ => Emission.Yields.pure (by simp)
  | source :: rest, acc => by
    rw [compileRecursorRules]
    refine Emission.Yields.bind (first := fun _ => source.nfields < UInt64.size) ?_ fun value bounded => ?_
    · unfold compileRecursorRule
      exact Emission.Yields.bindAny _ fun _ =>
        Emission.Yields.bind (Emission.Yields.count _ _) fun _ b => Emission.Yields.pure b
    · intro context before output after ran
      have tail := rules_bounded rest _ context before output after ran
      intro rule member
      rcases List.mem_cons.mp member with rfl | member
      · exact bounded
      · exact tail rule member

/-- **The recursor emitter keeps its source's header.** -/
theorem recursor_headers (source : Ix.RecursorVal) :
    Emission.Yields (compileRecursor source) (fun output => RecHeader source output.1) := by
  unfold compileRecursor
  refine Emission.Yields.withCurrent _ (Emission.Yields.withUnivCtx _
    (Emission.Yields.bindAny _ fun _ => Emission.Yields.bindAny _ fun typed => ?_))
  obtain ⟨typeExpr, typeRoot⟩ := typed
  dsimp only
  refine Emission.Yields.bind (rules_bounded source.rules.toList {}) fun rules bounded => ?_
  intro context before output after ran
  obtain ⟨lvls, params, indices, motives, minors, _⟩ :=
    Emission.recursorHeader source typeExpr typeRoot rules context before output after ran
  exact ⟨lvls, params, indices, motives, minors, bounded⟩

/-- The context the block's members run in. -/
def mutContext (classes : List (List MutConst)) (context : CompileEnv × BlockEnv) :
    CompileEnv × BlockEnv :=
  (context.1, { context.2 with mutCtx := MutConst.ctx classes })

/-! ## One member -/

theorem member_defn (d : Ix.Def) {context : CompileEnv × BlockEnv} {before after : BlockState}
    {member : CompiledMutConstMember}
    (ran : rawRun (compileMutConstMember (.defn d)) context before = (.ok member, after)) :
    ∃ out, rawRun (compileDefinitionData d) (Emission.current d.name context) before = (.ok out, after) ∧
      member.payload = .defn out.1 := by
  unfold compileMutConstMember at ran
  obtain ⟨out, middle, outRan, wrapRan⟩ := bind_ok ran
  unfold withCurrent at outRan
  rw [rawRun_withBlockEnv] at outRan
  obtain ⟨defn, constMeta, typeExpr, valueExpr⟩ := out
  dsimp only at wrapRan
  rw [rawRun_pure] at wrapRan
  cases wrapRan
  exact ⟨_, outRan, rfl⟩

theorem member_indc (i : Ix.Ind) {context : CompileEnv × BlockEnv} {before after : BlockState}
    {member : CompiledMutConstMember}
    (ran : rawRun (compileMutConstMember (.indc i)) context before = (.ok member, after)) :
    ∃ out, rawRun (compileInductiveData i) (Emission.current i.name context) before = (.ok out, after) ∧
      member.payload = .indc out.1 := by
  unfold compileMutConstMember at ran
  obtain ⟨out, middle, outRan, wrapRan⟩ := bind_ok ran
  unfold withCurrent at outRan
  rw [rawRun_withBlockEnv] at outRan
  obtain ⟨ind, constMeta, ctorMetaPairs, exprs⟩ := out
  dsimp only at wrapRan
  rw [rawRun_pure] at wrapRan
  cases wrapRan
  exact ⟨_, outRan, rfl⟩

theorem member_recr (r : Ix.RecursorVal) {context : CompileEnv × BlockEnv} {before after : BlockState}
    {member : CompiledMutConstMember}
    (ran : rawRun (compileMutConstMember (.recr r)) context before = (.ok member, after)) :
    ∃ out, rawRun (compileRecursor r) (Emission.current r.cnst.name context) before = (.ok out, after) ∧
      member.payload = .recr out.1 := by
  unfold compileMutConstMember at ran
  obtain ⟨out, middle, outRan, wrapRan⟩ := bind_ok ran
  unfold withCurrent at outRan
  rw [rawRun_withBlockEnv] at outRan
  obtain ⟨recursor, constMeta, typeExpr⟩ := out
  dsimp only at wrapRan
  rw [rawRun_pure] at wrapRan
  cases wrapRan
  exact ⟨_, outRan, rfl⟩

section Blocks

variable {md : Mode} (cx : Ctx md) (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md)))
  (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam) (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx param self

/-- The source relation of members whose level parameters are `lps`. -/
abbrev rel (lps : List Ix.Name) : Ix.Expr → CExpr md → Prop :=
  Related names (LevelMeaning lps σ param)

/-- **One member, compiled from a clean state, keeps its skeleton and reads its roots.** -/
theorem member_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (m : MutConst)
    (scope : ∀ e ∈ memberSources m, ConstsSatisfy (SelfName context.2 self names) e)
    {before after : BlockState} {member : CompiledMutConstMember}
    (good : Good cx param self (rel param names σ (memberLps m)) bindings before)
    (ran : rawRun (compileMutConstMember m) context before = (.ok member, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      PayloadOf m member.payload ∧
      SharingRoots.RootsRead (reader after) (rel param names σ (memberLps m)) (memberSources m)
        (mutConstRootExprs member.payload) := by
  cases m with
  | defn d =>
    obtain ⟨out, outRan, hp⟩ := member_defn d ran
    obtain ⟨cleanD, growth, shape, roots, read⟩ := Emission.definition_correct cx param self names σ bindings
      (Emission.current d.name context) aligned external d (scope _ (by simp [memberSources]))
      (scope _ (by simp [memberSources])) good outRan
    refine ⟨cleanD, growth, ⟨out.1, hp, shape⟩, ?_⟩
    rw [hp]
    exact read
  | indc i =>
    obtain ⟨out, outRan, hp⟩ := member_indc i ran
    obtain ⟨cleanD, growth, shape, ctorShapes, _, read⟩ := Emission.inductiveData_correct cx param self names σ
      bindings (Emission.current i.name context) aligned external i (scope _ (by simp [memberSources]))
      (fun ctor hc => scope _ (by simp only [memberSources, List.mem_cons, List.mem_map]; exact .inr ⟨ctor, hc, rfl⟩))
      good outRan
    obtain ⟨header, ctorHeaders, -⟩ := ProjectionLayout.inductiveData_headers i _ _ _ _ outRan
    refine ⟨cleanD, growth, ⟨out.1, hp, shape, ctorShapes, header, ctorHeaders⟩, ?_⟩
    rw [hp]
    exact read
  | recr r =>
    obtain ⟨out, outRan, hp⟩ := member_recr r ran
    obtain ⟨cleanD, growth, shape, fields, _, read⟩ := Emission.recursor_correct cx param self names σ bindings
      (Emission.current r.cnst.name context) aligned external r (scope _ (by simp [memberSources]))
      (fun rule hr => scope _ (by simp only [memberSources, List.mem_cons, List.mem_map]; exact .inr ⟨rule, hr, rfl⟩))
      good outRan
    refine ⟨cleanD, growth, ⟨out.1, hp, shape, fields, recursor_headers r _ _ _ _ outRan⟩, ?_⟩
    rw [hp]
    exact read

/-- **The members of a block, one per class, compiled from a clean state**: each keeps its
skeleton, and the final in-flight reader reads every member's roots, in member order. -/
theorem classes_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (lps : List Ix.Name) :
    ∀ (ms : List MutConst) (acc : MutConstCompileState) {before after : BlockState}
      {state : MutConstCompileState},
      (∀ m ∈ ms, memberLps m = lps) →
      (∀ m ∈ ms, ∀ e ∈ memberSources m, ConstsSatisfy (SelfName context.2 self names) e) →
      Good cx param self (rel param names σ lps) bindings before →
      rawRun (compileMutConstClasses (ms.map ([·])) acc) context before = (.ok state, after) →
      ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
        ∃ ps : List Ixon.MutConst, state.payloads = acc.payloads ++ ps.toArray ∧
          List.Forall₂ PayloadOf ms ps ∧
          SharingRoots.RootsRead (reader after) (rel param names σ lps) (ms.flatMap memberSources)
            (ps.flatMap mutConstRootExprs)
  | [], acc, before, after, state, _, _, good, ran => by
    rw [List.map_nil, compileMutConstClasses, rawRun_pure] at ran
    cases ran
    exact ⟨ExpressionRead.Extends.refl _, [], by simp, .nil, .nil⟩
  | m :: ms, acc, before, after, state, hlps, scopes, good, ran => by
    rw [List.map_cons, compileMutConstClasses] at ran
    obtain ⟨classState, middle, classRan, restRan⟩ := bind_ok ran
    rw [compileMutConstClass] at classRan
    obtain ⟨member, memberMiddle, memberRan, equivRan⟩ := bind_ok classRan
    rw [compileEquivalentMutConsts, rawRun_pure] at equivRan
    cases equivRan
    have hm := hlps m List.mem_cons_self
    obtain ⟨clean₁, growth₁, payload₁, roots₁⟩ := member_correct cx param self names σ bindings context
      aligned external m (scopes m List.mem_cons_self) (by rw [hm]; exact good) memberRan
    obtain ⟨growth₂, ps, hps, payloads, roots₂⟩ := classes_correct context aligned external lps ms
      _ (fun m' hm => hlps m' (List.mem_cons_of_mem _ hm))
      (fun m' hm => scopes m' (List.mem_cons_of_mem _ hm)) (clean₁.good cx param self _) restRan
    refine ⟨extends_trans growth₁ growth₂, member.payload :: ps, ?_, .cons payload₁ payloads, ?_⟩
    · rw [hps]
      simp [MutConstCompileState.addRepresentative]
    · rw [List.flatMap_cons, List.flatMap_cons]
      rw [hm] at roots₁
      exact SharingRoots.RootsRead.append (SharingRoots.RootsRead.grow growth₂ roots₁) roots₂

/-- The record a block of payloads is built as: a lone definition or recursor standalone,
any other block as its mutual wrapper. -/
def blockInfo (ps : List Ixon.MutConst) : Ixon.ConstantInfo :=
  match standaloneMutConstInfo? ps.toArray with
  | some info => info
  | none => .muts ps.toArray

theorem blockInfo_roots (ps : List Ixon.MutConst) :
    (constantInfoRootExprs (blockInfo ps)).toList = ps.flatMap mutConstRootExprs := by
  rcases ps with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · rfl
  · cases p with
    | defn d => rfl
    | indc i => rfl
    | recr r =>
      have : blockInfo [.recr r] = .recr r := rfl
      rw [this]
      simp [constantInfoRootExprs]
  · have : blockInfo (p :: q :: rest) = .muts (p :: q :: rest).toArray := rfl
    rw [this]
    simp [constantInfoRootExprs]

/-- **A block compiled one member per class reads back as its sources**: the emitted record
keeps its payloads' skeletons, and its member reader reads every member's roots, in member
order, as terms related to the members' sources. -/
theorem mutualBlock_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (ms : List MutConst) (lps : List Ix.Name)
    (hlps : ∀ m ∈ ms, memberLps m = lps)
    (scopes : ∀ m ∈ ms, ∀ e ∈ memberSources m,
      ConstsSatisfy (SelfName (mutContext (ms.map ([·])) context).2 self names) e)
    {before after : BlockState} {output : BlockResult} (clean : Emission.Clean bindings before)
    (ran : rawRun (compileMutualBlock (ms.map ([·]))) context before = (.ok output, after)) :
    ∃ ps : List Ixon.MutConst, List.Forall₂ PayloadOf ms ps ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (blockInfo ps) ∧
      SharingRoots.RootsRead (EmissionBlocks.recordReader cx param self after output.block)
        (rel param names σ lps) (ms.flatMap memberSources)
        (constantInfoRootExprs output.block.info).toList := by
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, seededState, seeded, compiled⟩ := bind_ok ran
  have kept := EmissionBlocks.preseed_then cx param self bindings (related := rel param names σ lps)
    (context := mutContext (ms.map ([·])) context) aligned (clean.good cx param self _) seeded
  unfold compileMutualPayload at compiled
  obtain ⟨payload, middle, payloadRan, finished⟩ := bind_ok compiled
  unfold compileMutConsts at payloadRan
  obtain ⟨state, middle', classesRan, finish⟩ := bind_ok payloadRan
  rw [rawRun_pure] at finish
  cases finish
  obtain ⟨_, ps, hps, payloads, roots⟩ := classes_correct cx param self names σ bindings
    (mutContext (ms.map ([·])) context) aligned external lps ms {} hlps scopes kept.1 classesRan
  obtain ⟨same, _, built⟩ := ProjectionLayout.finish_mutual_ok _ _ _ _ finished
  subst same
  simp only [hps] at built
  have hps' : (({} : MutConstCompileState).payloads ++ ps.toArray) = ps.toArray := by
    simp
  rw [hps'] at built
  unfold buildCompiledMutualBlock at built
  rw [← blockInfo_roots] at roots
  refine ⟨ps, payloads, ?_⟩
  cases hs : standaloneMutConstInfo? ps.toArray with
  | some info =>
    rw [hs] at built
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok built
    cases Except.ok.inj returned
    have hinfo : blockInfo ps = info := by unfold blockInfo; rw [hs]
    rw [hinfo] at roots
    obtain ⟨erased, read⟩ := SharingRoots.build_read cx param self _ _ info block hb roots
    exact ⟨by rw [hinfo]; exact erased, read⟩
  | none =>
    rw [hs] at built
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok built
    cases Except.ok.inj returned
    have hinfo : blockInfo ps = .muts ps.toArray := by unfold blockInfo; rw [hs]
    rw [hinfo] at roots
    obtain ⟨erased, read⟩ := SharingRoots.build_read cx param self _ _ (.muts ps.toArray) block hb roots
    exact ⟨by rw [hinfo]; exact erased, read⟩

end Blocks

/--
info: 'Ix.Cert.BlockEmission.mutualBlock_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mutualBlock_correct

end Ix.Cert.BlockEmission
