import Ix.Tc.Verify.Inductive.GeneratedRecursorAcceptanceClosure
import Ix.Tc.Verify.Inductive.StructuralCacheSemantics
import Ix.Tc.Verify.Check.BlockIdentity
import Ix.Tc.Verify.Whnf.StructEta.ExactMajorTelescope

/-!
# Generated-recursor member-check handoff

The production member checker has two semantically different phases.  Its
prelude resolves and validates the major family, checks the constructive K
target, transactionally populates generated rules, and freezes the resulting
cache entry.  Its tail selects one generated entry and exhaustively compares
the frozen stored type and rules.

This module proves the exact operational handoff.  It intentionally does not
postulate that the prelude preserves the K2S invariant; subsequent modules
must prove that from the individual production operations.
-/

namespace Ix.Tc

open GeneratedRecursorSemantics

namespace KConst

/-- The exact physical declaration classes admitted by the coordinated
inductive-block cache shell.  Recursors and unrelated declarations force the
production member-check fallback instead. -/
def IsInductiveBlockMember : KConst m → Prop
  | .indc .. | .ctor .. => True
  | _ => False

/-- Semantic coordinated-block ownership is stronger than the physical
declaration-class test used by the cache shell. -/
theorem isInductiveBlockMember_of_inductiveMemberOf
    {catalog : Catalog} {block : KId .anon} {constant : KConst .anon}
    (member : constant.IsInductiveMemberOf catalog block) :
    constant.IsInductiveBlockMember := by
  cases constant <;>
    simp_all [KConst.IsInductiveMemberOf, IsInductiveBlockMember]

end KConst

namespace TcM

/-- A physically loaded block likewise takes the eager, state-preserving
lookup path. -/
theorem tryGetBlock_loaded_run
    {state : TcState .anon} {block : KId .anon}
    {members : Array (KId .anon)}
    (loaded : state.env.getBlock? block = some members) :
    TcM.tryGetBlock block state = .ok (some members) state := by
  unfold TcM.tryGetBlock
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) state =
    .ok state state from rfl]
  simp only [loaded]
  rfl

end TcM

/-- Complete successful execution trace of the production recursor-member
checker, split at its data-bearing preparation boundary.  Existentials retain
the concrete data while keeping the trace proof-irrelevant. -/
def GeneratedRecursorMemberCheckTrace (id : KId m)
    (methods : Methods m) (initial final : TcState m) : Prop :=
  ∃ prepared : RecM.PreparedRecursorMemberCheck m,
    ∃ afterPreparation : TcState m,
      (RecM.prepareRecursorMemberCheck id).run methods initial =
          .ok prepared afterPreparation ∧
        (RecM.checkPreparedRecursorMember id prepared).run methods
          afterPreparation = .ok () final

/-- Exhaustive successful trace of the stateful preparation phase.  Each
existential state is the actual handoff between one named production stage
and the next; the final equality prevents a proof from replacing the frozen
declaration or generated cache batch after the fact. -/
def RecursorMemberPreparationTrace (id : KId m)
    (methods : Methods m) (initial : TcState m)
    (prepared : RecM.PreparedRecursorMemberCheck m)
    (final : TcState m) : Prop :=
  ∃ snapshot : RecM.RecursorMemberDeclarationSnapshot m,
    ∃ afterSnapshot : TcState m,
      (RecM.snapshotRecursorMemberDeclaration id).run methods initial =
          .ok snapshot afterSnapshot ∧
      ∃ indId : KId m, ∃ afterMajor : TcState m,
        (RecM.validateRecursorMemberMajor snapshot).run methods afterSnapshot =
            .ok indId afterMajor ∧
        ∃ resolvedBlock : KId m, ∃ afterResolution : TcState m,
          (RecM.resolveRecursorMemberBlock snapshot indId).run methods
              afterMajor = .ok resolvedBlock afterResolution ∧
          ∃ computedK : Bool, ∃ afterK : TcState m,
            (RecM.validateRecursorMemberKTarget snapshot indId).run methods
                afterResolution = .ok computedK afterK ∧
            ∃ afterPopulation : TcState m,
              (RecM.populateRecursorRulesFromBlock resolvedBlock
                  snapshot.recBlock).run methods afterK =
                    .ok () afterPopulation ∧
              ∃ generated : Array (GeneratedRecursor m),
                (RecM.snapshotGeneratedRecursors resolvedBlock).run methods
                    afterPopulation = .ok generated final ∧
                prepared = {
                  recBlock := snapshot.recBlock
                  ty := snapshot.ty
                  declaredK := snapshot.declaredK
                  declaredLvls := snapshot.declaredLvls
                  declaredIsUnsafe := snapshot.declaredIsUnsafe
                  params := snapshot.params
                  motives := snapshot.motives
                  minors := snapshot.minors
                  indices := snapshot.indices
                  storedRules := snapshot.storedRules
                  indId
                  resolvedBlock
                  computedK
                  generated
                }

namespace ScopedWhnfStateInv

/-- Publishing a successful verdict for an already accepted immutable block
preserves both the semantic checker invariant and an arbitrary finite suffix
model's state domain.  The update changes only `blockCheckResults`, hence is a
digest-neutral frame. -/
theorem withBlockCheckSuccess
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {Delta : KVLCtx}
    {state : TcState .anon} {block : KId .anon}
    (accepted : world.AcceptedBlock block)
    (h : ScopedWhnfStateInv model layer semantics support Delta state) :
    ScopedWhnfStateInv model layer semantics support Delta
      (state.withBlockCheckResult block (.ok ())) := by
  refine ⟨?_, model.preservesFrame h.2 ?_⟩
  · rcases h.1 with ⟨hkernel, hctx, hlayer⟩
    refine ⟨?_, ?_, ?_⟩
    · exact {
        core := hkernel.core.of_consts_eq rfl (by
          simpa [TcState.withBlockCheckResult] using hkernel.core.intern)
        internSupport := by
          simpa [TcState.withBlockCheckResult] using hkernel.internSupport
        caches := by
          simpa [TcState.withBlockCheckResult] using
            hkernel.caches.insertBlockSuccess accepted
        equivalences := by
          simpa [TcState.withBlockCheckResult] using hkernel.equivalences }
    · exact hctx.of_fields_eq rfl rfl rfl rfl (Nat.le_refl _)
    · cases layer <;> exact hlayer
  · simp only [TcState.withBlockCheckResult]
    constructor <;> rfl

end ScopedWhnfStateInv

namespace RecM

/-- Expose the state-carrying bind at the preparation/checker handoff. -/
private theorem runTcBind {α β : Type}
    (x : TcM m α) (k : α → TcM m β) (state : TcState m) :
    (x >>= k) state = match x state with
      | .ok value after => k value after
      | .error error after => .error error after := by
  show EStateM.bind x k state = _
  unfold EStateM.bind
  cases x state <;> rfl

/-- The named production member-classification scan is read-only whenever
every source-ordered member is physically loaded as an inductive or
constructor.  The proof covers the complete recursive traversal, rather than
assuming the aggregate Boolean result. -/
theorem inductiveBlockMembersAreSupported_loaded_run
    (methods : Methods .anon) (state : TcState .anon) :
    ∀ (members : List (KId .anon)),
      (∀ member ∈ members, ∃ constant,
        state.env.get? member = some constant ∧
          constant.IsInductiveBlockMember) →
      (inductiveBlockMembersAreSupported members).run methods state =
        .ok true state
  | [], _ => rfl
  | member :: members, loaded => by
      obtain ⟨constant, memberLoaded, supported⟩ :=
        loaded member (List.mem_cons_self ..)
      unfold inductiveBlockMembersAreSupported
      rw [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
      change EStateM.bind (TcM.tryGetConst member) _ state = _
      unfold EStateM.bind
      rw [TcM.tryGetConst_loaded_run memberLoaded]
      simp only
      cases constant <;> simp_all [KConst.IsInductiveBlockMember]
      all_goals
        exact inductiveBlockMembersAreSupported_loaded_run methods state
          members loaded

/-- A coordinated success verdict for a physically loaded, uniformly
classified inductive block makes `checkInductive` an exact state-preserving
cache hit.  In particular, this theorem grants no authority to replay
`checkInductiveBlockImpl` or the mixed-block member fallback. -/
theorem checkInductive_cached_run
    {state : TcState .anon} {id block : KId .anon}
    {lvls params indices memberIdx : UInt64} {isUnsafe : Bool}
    {ty : KExpr .anon} {ctors members : Array (KId .anon)}
    (methods : Methods .anon)
    (root : state.env.get? id = some
      (.indc () () lvls params indices isUnsafe block memberIdx ty ctors ()))
    (physicalBlock : state.env.getBlock? block = some members)
    (supported : ∀ member ∈ members.toList, ∃ constant,
      state.env.get? member = some constant ∧
        constant.IsInductiveBlockMember)
    (cached : state.env.blockCheckResults[block]? = some (.ok ())) :
    (checkInductive id).run methods state = .ok () state := by
  have rootLookup : TcM.getConst id state = .ok
      (.indc () () lvls params indices isUnsafe block memberIdx ty ctors ())
        state := by
    unfold TcM.getConst
    change EStateM.bind (TcM.tryGetConst id) _ state = _
    unfold EStateM.bind
    rw [TcM.tryGetConst_loaded_run root]
    rfl
  have blockLookup : TcM.tryGetBlock block state =
      .ok (some members) state :=
    TcM.tryGetBlock_loaded_run physicalBlock
  have scan :
      (inductiveBlockMembersAreSupported members.toList).run methods state =
        .ok true state :=
    inductiveBlockMembersAreSupported_loaded_run methods state members.toList
      supported
  unfold checkInductive
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.getConst id) _ state = _
  unfold EStateM.bind
  rw [rootLookup]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_pure, pure_bind]
  rw [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
  change EStateM.bind (TcM.tryGetBlock block) _ state = _
  unfold EStateM.bind
  rw [blockLookup]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((inductiveBlockMembersAreSupported members.toList).run methods) _
      state = _
  unfold EStateM.bind
  rw [scan]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) state =
    .ok state state from rfl]
  simp only [cached]
  rfl

/-- Keep the successful execution equation while restoring the original
error postcondition, so it composes through an ordinary Hoare bind. -/
private theorem wf_with_success_run_eq
    {I : TcState .anon → Prop} {state : TcState .anon}
    {action : TcM .anon α} {Q : α → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (h : TcM.WF I state action Q E) :
    TcM.WF I state action
      (fun value after => Q value after ∧ action state = .ok value after)
      E :=
  TcM.WF.mono (TcM.WF.with_run_eq h)
    (fun _ _ result => result) (fun _ _ result => result.1)

/-- Checked metadata arithmetic is method- and state-independent, including
its overflow error. -/
theorem checkedMetadataSum_preserves
    {I : TcState .anon → Prop} (label : String) (parts : Array UInt64)
    (methods : Methods .anon) (state : TcState .anon) :
    TcM.WF I state ((checkedMetadataSum label parts).run methods)
      (fun _ _ => True) := by
  unfold checkedMetadataSum checkedNatMetadataSum
  simp only [pure_bind]
  split
  · exact TcM.WF.pure (I := I) (s := state)
      (Q := fun _ _ => True) (E := fun _ _ => True) (fun _ => trivial)
  · exact TcM.WF.throw (I := I) (s := state)
      (Q := fun _ _ => True) (E := fun _ _ => True) (fun _ => trivial)

/-- Freezing the stored declaration preserves any invariant respected by the
configured lazy-ingress hook.  The theorem covers successful snapshots,
non-recursor errors, lookup misses, overflow, and partial lazy-ingress errors. -/
theorem snapshotRecursorMemberDeclaration_wf
    {I : TcState .anon → Prop} (hfault : TcM.LazyFaultPreserves I)
    (id : KId .anon) (methods : Methods .anon) (state : TcState .anon) :
    TcM.WF I state ((snapshotRecursorMemberDeclaration id).run methods)
      (fun _ _ => True) := by
  unfold snapshotRecursorMemberDeclaration
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (TcM.getConst_wf hfault id state)
  intro declaration after _
  cases declaration <;> simp only
  all_goals first
    | exact TcM.WF.throw (fun _ => trivial)
    | apply TcM.WF.bind
        (checkedMetadataSum_preserves
          "recursor major index" _ methods after)
      intro majorSkip final _
      exact TcM.WF.pure (fun _ => trivial)

/-- The final generated-cache freeze is a read-only success or error and
therefore preserves every state predicate without an auxiliary premise. -/
theorem snapshotGeneratedRecursors_wf
    {I : TcState .anon → Prop} (resolvedBlock : KId .anon)
    (methods : Methods .anon) (state : TcState .anon) :
    TcM.WF I state ((snapshotGeneratedRecursors resolvedBlock).run methods)
      (fun _ _ => True) := by
  unfold snapshotGeneratedRecursors
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
      (Q₁ := fun read after => read = after)
      (E := fun _ _ => True)
      (TcM.WF.get (fun _ => rfl))
  intro current after hread
  subst current
  split
  · exact TcM.WF.pure (I := I) (s := after)
      (Q := fun _ _ => True) (E := fun _ _ => True) (fun _ => trivial)
  · exact TcM.WF.throw (I := I) (s := after)
      (Q := fun _ _ => True) (E := fun _ _ => True) (fun _ => trivial)

/-- State-preservation plumbing for major discovery.  The telescope scan and
the coordinated inductive check are deliberately separate premises: the
constant lookup and branch dispatch are proved here, while neither callback
is hidden behind a contract for the whole stage. -/
theorem validateRecursorMemberMajor_wf
    {I : TcState .anon → Prop} (hfault : TcM.LazyFaultPreserves I)
    (snapshot : RecursorMemberDeclarationSnapshot .anon)
    (methods : Methods .anon) (state : TcState .anon)
    (major : ∀ before,
      TcM.WF I before
        ((getMajorInductiveId snapshot.ty snapshot.majorSkip).run methods)
        (fun _ _ => True))
    (inductiveCheck : ∀ id before,
      TcM.WF I before ((checkInductive id).run methods)
        (fun _ _ => True)) :
    TcM.WF I state ((validateRecursorMemberMajor snapshot).run methods)
      (fun _ _ => True) := by
  unfold validateRecursorMemberMajor
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (major state)
  intro indId afterMajor _
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (TcM.tryGetConst_wf hfault indId afterMajor)
  intro declaration afterLookup _
  cases declaration with
  | none => exact TcM.WF.pure (fun _ => trivial)
  | some declaration =>
      cases declaration <;> simp only
      all_goals first
        | exact TcM.WF.pure (fun _ => trivial)
        | apply TcM.WF.bind (inductiveCheck indId afterLookup)
          intro _ afterCheck _
          exact TcM.WF.pure (fun _ => trivial)

/-- The generated-block fast-path query performs one lazy-aware declaration
lookup followed only by a state read.  Hits, misses, undersized entries, and
partial lazy-ingress errors all preserve an arbitrary invariant. -/
theorem findUsableGeneratedRecursorBlock_wf
    {I : TcState .anon → Prop} (hfault : TcM.LazyFaultPreserves I)
    (snapshot : RecursorMemberDeclarationSnapshot .anon)
    (indId : KId .anon) (methods : Methods .anon)
    (state : TcState .anon) :
    TcM.WF I state
      ((findUsableGeneratedRecursorBlock snapshot indId).run methods)
      (fun _ _ => True) := by
  unfold findUsableGeneratedRecursorBlock
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (TcM.tryGetConst_wf hfault indId state)
  intro declaration afterLookup _
  cases declaration with
  | none => exact TcM.WF.pure (fun _ => trivial)
  | some declaration =>
      cases declaration <;> simp only
      all_goals first
        | exact TcM.WF.pure (fun _ => trivial)
        | rw [ReaderT.run_bind]
          apply TcM.WF.bind
              (Q₁ := fun read after => read = after)
              (E := fun _ _ => True)
              (TcM.WF.get (fun _ => rfl))
          intro current afterRead hread
          subst current
          rw [ReaderT.run_bind]
          apply TcM.WF.bind
              (Q₁ := fun read final => read = final)
              (E := fun _ _ => True)
              (TcM.WF.get (fun _ => rfl))
          intro cacheState final hcacheState
          subst cacheState
          split
          · split <;>
              exact TcM.WF.pure (I := I) (s := final)
                (Q := fun _ _ => True) (E := fun _ _ => True)
                (fun _ => trivial)
          · exact TcM.WF.pure (I := I) (s := final)
              (Q := fun _ _ => True) (E := fun _ _ => True)
              (fun _ => trivial)

/-- A physically loaded inductive and an adequately sized generated cache
entry make the fast-path query an exact state-preserving hit.  This is the
operational fact used by concrete member fixtures; it does not authorize the
lazy-ingress or cache-miss branches. -/
theorem findUsableGeneratedRecursorBlock_loaded_run
    {state : TcState .anon} {snapshot : RecursorMemberDeclarationSnapshot .anon}
    {indId block : KId .anon} {cached : Array (GeneratedRecursor .anon)}
    {lvls params indices memberIdx : UInt64} {isUnsafe : Bool}
    {ty : KExpr .anon} {ctors : Array (KId .anon)}
    (methods : Methods .anon)
    (loaded : state.env.get? indId = some
      (.indc () () lvls params indices isUnsafe block memberIdx ty ctors ()))
    (cache : state.env.recursorCache[block]? = some cached)
    (largeEnough : snapshot.motives ≤ cached.size.toUInt64) :
    (findUsableGeneratedRecursorBlock snapshot indId).run methods state =
      .ok (some block) state := by
  unfold findUsableGeneratedRecursorBlock
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.tryGetConst indId) _ state = _
  unfold EStateM.bind
  rw [TcM.tryGetConst_loaded_run loaded]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) state =
    .ok state state from rfl]
  simp only [cache]
  rw [if_pos largeEnough]
  rfl

/-- The successful usable-cache branch of block resolution performs no work
after its query and returns that query's exact state. -/
theorem resolveRecursorMemberBlock_cached_run
    {snapshot : RecursorMemberDeclarationSnapshot .anon}
    {indId block : KId .anon} {methods : Methods .anon}
    {state afterQuery : TcState .anon}
    (hit : (findUsableGeneratedRecursorBlock snapshot indId).run methods
      state = .ok (some block) afterQuery) :
    (resolveRecursorMemberBlock snapshot indId).run methods state =
      .ok block afterQuery := by
  unfold resolveRecursorMemberBlock
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((findUsableGeneratedRecursorBlock snapshot indId).run methods) _ state = _
  unfold EStateM.bind
  rw [hit]
  rfl

/-- A witnessed usable-cache hit closes block resolution without granting any
authority over the peer-major generation fallback. -/
theorem resolveRecursorMemberBlock_cached_wf
    {I : TcState .anon → Prop} (hfault : TcM.LazyFaultPreserves I)
    (snapshot : RecursorMemberDeclarationSnapshot .anon)
    (indId block : KId .anon) (methods : Methods .anon)
    (state afterQuery : TcState .anon)
    (hit : (findUsableGeneratedRecursorBlock snapshot indId).run methods
      state = .ok (some block) afterQuery) :
    TcM.WF I state ((resolveRecursorMemberBlock snapshot indId).run methods)
      (fun _ _ => True) := by
  unfold resolveRecursorMemberBlock
  rw [ReaderT.run_bind]
  have query : TcM.WF I state
      ((findUsableGeneratedRecursorBlock snapshot indId).run methods)
      (fun result after => result = some block ∧ after = afterQuery) := by
    intro hI
    have hpost :=
      findUsableGeneratedRecursorBlock_wf hfault snapshot indId methods state
        hI
    rw [hit] at hpost ⊢
    exact ⟨hpost.1, rfl, rfl⟩
  apply TcM.WF.bind query
  intro result after hresult
  rcases hresult with ⟨rfl, rfl⟩
  exact TcM.WF.pure (fun _ => trivial)

/-- The declared/computed K comparison is pure.  All state authority remains
with the separately stated production `computeKTarget` obligation. -/
theorem validateRecursorMemberKTarget_wf
    {I : TcState .anon → Prop}
    (snapshot : RecursorMemberDeclarationSnapshot .anon)
    (indId : KId .anon) (methods : Methods .anon)
    (state : TcState .anon)
    (compute : ∀ before,
      TcM.WF I before ((computeKTarget indId).run methods)
        (fun _ _ => True)) :
    TcM.WF I state
      ((validateRecursorMemberKTarget snapshot indId).run methods)
      (fun _ _ => True) := by
  unfold validateRecursorMemberKTarget
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (compute state)
  intro computedK afterCompute _
  split
  · exact TcM.WF.throw (fun _ => trivial)
  · exact TcM.WF.pure (fun _ => trivial)

/-- The transactional generated-rule commit preserves the complete scoped
checker invariant whenever the exact batch it may install already has cache
provenance.  All validation failures are read-only; the sole successful write
is discharged by `ScopedWhnfStateInv.insertRecursor`. -/
theorem commitGeneratedRecursorRulesAt_scoped_wf
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {Delta : KVLCtx}
    (indBlockId : KId .anon)
    (expected generatedWithRules : Array (GeneratedRecursor .anon))
    (methods : Methods .anon) (state : TcState .anon)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.recursor indBlockId
        (expected.zipWith
          (fun header generated => header.withRules generated.rules)
          generatedWithRules))) :
    TcM.WF (ScopedWhnfStateInv model layer semantics support Delta) state
      ((commitGeneratedRecursorRulesAt indBlockId expected
        generatedWithRules).run methods)
      (fun _ _ => True) := by
  intro hI
  cases hrun :
      (commitGeneratedRecursorRulesAt indBlockId expected
        generatedWithRules).run methods state with
  | error err final =>
      have hfinal : final = state := by
        unfold commitGeneratedRecursorRulesAt at hrun
        rw [ReaderT.run_bind] at hrun
        change EStateM.bind (get : TcM .anon (TcState .anon)) _ state =
          .error err final at hrun
        unfold EStateM.bind at hrun
        rw [show (get : TcM .anon (TcState .anon)) state =
          .ok state state from rfl] at hrun
        simp only at hrun
        cases hcache : state.env.recursorCache[indBlockId]? with
        | none =>
            rw [hcache] at hrun
            cases hrun
            rfl
        | some cached =>
            rw [hcache] at hrun
            simp only at hrun
            split at hrun
            · cases hrun
              rfl
            · split at hrun
              · split at hrun
                · cases hrun
                  rfl
                · simp only [modify, ReaderT.run] at hrun
                  contradiction
              · cases hrun
                rfl
      subst final
      exact ⟨hI, trivial⟩
  | ok result final =>
      have hfinal : final =
          { state with env := { state.env with
            recursorCache := state.env.recursorCache.insert indBlockId
              (expected.zipWith
                (fun header generated => header.withRules generated.rules)
                generatedWithRules) } } := by
        unfold commitGeneratedRecursorRulesAt at hrun
        rw [ReaderT.run_bind] at hrun
        change EStateM.bind (get : TcM .anon (TcState .anon)) _ state =
          .ok result final at hrun
        unfold EStateM.bind at hrun
        rw [show (get : TcM .anon (TcState .anon)) state =
          .ok state state from rfl] at hrun
        simp only at hrun
        cases hcache : state.env.recursorCache[indBlockId]? with
        | none =>
            rw [hcache] at hrun
            contradiction
        | some cached =>
            rw [hcache] at hrun
            simp only at hrun
            split at hrun
            · contradiction
            · split at hrun
              · split at hrun
                · contradiction
                · simp only [modify, ReaderT.run] at hrun
                  cases hrun
                  rfl
              · contradiction
      subst final
      exact ⟨ScopedWhnfStateInv.insertRecursor hnew hI, trivial⟩

/-- Active coordinated-block form of the transactional commit theorem.  The
installed recursive rules may name a recursor in `members`; that dependency
is valid only under `CacheAuthority.coordinatedBlock` until successful atomic
admission closes the block.  Every rejection branch remains state-neutral. -/
theorem commitGeneratedRecursorRulesAt_activeScoped_wf
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)} {Delta : KVLCtx}
    (indBlockId : KId .anon)
    (expected generatedWithRules : Array (GeneratedRecursor .anon))
    (methods : Methods .anon) (state : TcState .anon)
    (hnew : CacheProvenance semantics
      (CacheAuthority.coordinatedBlock world members) support
      (.recursor indBlockId
        (expected.zipWith
          (fun header generated => header.withRules generated.rules)
          generatedWithRules))) :
    TcM.WF
      (ScopedActiveWhnfStateInv model layer semantics support members Delta)
      state
      ((commitGeneratedRecursorRulesAt indBlockId expected
        generatedWithRules).run methods)
      (fun _ _ => True) := by
  intro hI
  cases hrun :
      (commitGeneratedRecursorRulesAt indBlockId expected
        generatedWithRules).run methods state with
  | error err final =>
      have hfinal : final = state := by
        unfold commitGeneratedRecursorRulesAt at hrun
        rw [ReaderT.run_bind] at hrun
        change EStateM.bind (get : TcM .anon (TcState .anon)) _ state =
          .error err final at hrun
        unfold EStateM.bind at hrun
        rw [show (get : TcM .anon (TcState .anon)) state =
          .ok state state from rfl] at hrun
        simp only at hrun
        cases hcache : state.env.recursorCache[indBlockId]? with
        | none =>
            rw [hcache] at hrun
            cases hrun
            rfl
        | some cached =>
            rw [hcache] at hrun
            simp only at hrun
            split at hrun
            · cases hrun
              rfl
            · split at hrun
              · split at hrun
                · cases hrun
                  rfl
                · simp only [modify, ReaderT.run] at hrun
                  contradiction
              · cases hrun
                rfl
      subst final
      exact ⟨hI, trivial⟩
  | ok result final =>
      have hfinal : final =
          { state with env := { state.env with
            recursorCache := state.env.recursorCache.insert indBlockId
              (expected.zipWith
                (fun header generated => header.withRules generated.rules)
                generatedWithRules) } } := by
        unfold commitGeneratedRecursorRulesAt at hrun
        rw [ReaderT.run_bind] at hrun
        change EStateM.bind (get : TcM .anon (TcState .anon)) _ state =
          .ok result final at hrun
        unfold EStateM.bind at hrun
        rw [show (get : TcM .anon (TcState .anon)) state =
          .ok state state from rfl] at hrun
        simp only at hrun
        cases hcache : state.env.recursorCache[indBlockId]? with
        | none =>
            rw [hcache] at hrun
            contradiction
        | some cached =>
            rw [hcache] at hrun
            simp only at hrun
            split at hrun
            · contradiction
            · split at hrun
              · split at hrun
                · contradiction
                · simp only [modify, ReaderT.run] at hrun
                  cases hrun
                  rfl
              · contradiction
      subst final
      exact ⟨ScopedActiveWhnfStateInv.insertRecursor hnew hI, trivial⟩

/-- Transactional rule-population composition.  Reading the ingress batch is
proved locally; construction and the self-framing final commit remain distinct
obligations tied to the exact snapshotted and returned arrays. -/
theorem populateRecursorRulesFromBlock_wf
    {I : TcState .anon → Prop}
    (indBlockId recBlockId : KId .anon)
    (methods : Methods .anon) (state : TcState .anon)
    (core : ∀ generatedSnapshot before,
      TcM.WF I before
        ((populateRecursorRulesFromBlockCore indBlockId recBlockId
          generatedSnapshot).run methods)
        (fun _ _ => True))
    (commit : ∀ generatedSnapshot generatedWithRules before,
      TcM.WF I before
        ((commitGeneratedRecursorRulesAt indBlockId generatedSnapshot
          generatedWithRules).run methods)
        (fun _ _ => True)) :
    TcM.WF I state
      ((populateRecursorRulesFromBlock indBlockId recBlockId).run methods)
      (fun _ _ => True) := by
  unfold populateRecursorRulesFromBlock
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
      (Q₁ := fun read after => read = after)
      (E := fun _ _ => True)
      (TcM.WF.get (fun _ => rfl))
  intro current after hread
  subst current
  split
  · rename_i generatedSnapshot hfound
    rw [ReaderT.run_bind]
    apply TcM.WF.bind (core generatedSnapshot after)
    intro generatedWithRules afterCore _
    exact commit generatedSnapshot generatedWithRules afterCore
  · exact TcM.WF.pure (fun _ => trivial)

/-- Compose operation-level preservation facts for the four stateful middle
stages with the proved declaration snapshot and final cache freeze.  Keeping
the four premises separate prevents this theorem from becoming a disguised
whole-prelude oracle: each callback-bearing production operation remains an
independent proof obligation, including all of its partial-error states. -/
theorem prepareRecursorMemberCheck_wf
    {I : TcState .anon → Prop} (hfault : TcM.LazyFaultPreserves I)
    (id : KId .anon) (methods : Methods .anon) (state : TcState .anon)
    (major : ∀ snapshot afterSnapshot,
      TcM.WF I afterSnapshot
        ((validateRecursorMemberMajor snapshot).run methods)
        (fun _ _ => True))
    (resolution : ∀ snapshot indId afterMajor,
      TcM.WF I afterMajor
        ((resolveRecursorMemberBlock snapshot indId).run methods)
        (fun _ _ => True))
    (kTarget : ∀ snapshot indId afterResolution,
      TcM.WF I afterResolution
        ((validateRecursorMemberKTarget snapshot indId).run methods)
        (fun _ _ => True))
    (population : ∀ resolvedBlock recBlock afterK,
      TcM.WF I afterK
        ((populateRecursorRulesFromBlock resolvedBlock recBlock).run methods)
        (fun _ _ => True)) :
    TcM.WF I state ((prepareRecursorMemberCheck id).run methods)
      (fun _ _ => True) := by
  unfold prepareRecursorMemberCheck
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (snapshotRecursorMemberDeclaration_wf hfault id methods state)
  intro snapshot afterSnapshot _
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (major snapshot afterSnapshot)
  intro indId afterMajor _
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (resolution snapshot indId afterMajor)
  intro resolvedBlock afterResolution _
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (kTarget snapshot indId afterResolution)
  intro computedK afterK _
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (population resolvedBlock snapshot.recBlock afterK)
  intro unitValue afterPopulation _
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (snapshotGeneratedRecursors_wf resolvedBlock methods afterPopulation)
  intro generated final _
  exact TcM.WF.pure (I := I) (s := final)
    (Q := fun _ _ => True) (E := fun _ _ => True) (fun _ => trivial)

/-- Reachability-indexed form of `prepareRecursorMemberCheck_wf`.  Each
middle-stage contract is demanded only after the exact preceding production
execution succeeded.  This is the form used by finite fixtures: it avoids a
spurious global claim about arbitrary snapshots and states while still
requiring each reached stage to preserve the invariant on both success and
partial error. -/
theorem prepareRecursorMemberCheck_reachable_wf
    {I : TcState .anon → Prop} (hfault : TcM.LazyFaultPreserves I)
    (id : KId .anon) (methods : Methods .anon) (state : TcState .anon)
    (major : ∀ snapshot afterSnapshot,
      (snapshotRecursorMemberDeclaration id).run methods state =
          .ok snapshot afterSnapshot →
      TcM.WF I afterSnapshot
        ((validateRecursorMemberMajor snapshot).run methods)
        (fun _ _ => True))
    (resolution : ∀ snapshot afterSnapshot indId afterMajor,
      (snapshotRecursorMemberDeclaration id).run methods state =
          .ok snapshot afterSnapshot →
      (validateRecursorMemberMajor snapshot).run methods afterSnapshot =
          .ok indId afterMajor →
      TcM.WF I afterMajor
        ((resolveRecursorMemberBlock snapshot indId).run methods)
        (fun _ _ => True))
    (kTarget : ∀ snapshot afterSnapshot indId afterMajor resolvedBlock
        afterResolution,
      (snapshotRecursorMemberDeclaration id).run methods state =
          .ok snapshot afterSnapshot →
      (validateRecursorMemberMajor snapshot).run methods afterSnapshot =
          .ok indId afterMajor →
      (resolveRecursorMemberBlock snapshot indId).run methods afterMajor =
          .ok resolvedBlock afterResolution →
      TcM.WF I afterResolution
        ((validateRecursorMemberKTarget snapshot indId).run methods)
        (fun _ _ => True))
    (population : ∀ snapshot afterSnapshot indId afterMajor resolvedBlock
        afterResolution computedK afterK,
      (snapshotRecursorMemberDeclaration id).run methods state =
          .ok snapshot afterSnapshot →
      (validateRecursorMemberMajor snapshot).run methods afterSnapshot =
          .ok indId afterMajor →
      (resolveRecursorMemberBlock snapshot indId).run methods afterMajor =
          .ok resolvedBlock afterResolution →
      (validateRecursorMemberKTarget snapshot indId).run methods
          afterResolution = .ok computedK afterK →
      TcM.WF I afterK
        ((populateRecursorRulesFromBlock resolvedBlock snapshot.recBlock).run
          methods)
        (fun _ _ => True)) :
    TcM.WF I state ((prepareRecursorMemberCheck id).run methods)
      (fun _ _ => True) := by
  unfold prepareRecursorMemberCheck
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (wf_with_success_run_eq
    (snapshotRecursorMemberDeclaration_wf hfault id methods state))
  intro snapshot afterSnapshot hsnapshot
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (wf_with_success_run_eq
    (major snapshot afterSnapshot hsnapshot.2))
  intro indId afterMajor hmajor
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (wf_with_success_run_eq
    (resolution snapshot afterSnapshot indId afterMajor hsnapshot.2
      hmajor.2))
  intro resolvedBlock afterResolution hresolution
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (wf_with_success_run_eq
    (kTarget snapshot afterSnapshot indId afterMajor resolvedBlock
      afterResolution hsnapshot.2 hmajor.2 hresolution.2))
  intro computedK afterK hkTarget
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (population snapshot afterSnapshot indId afterMajor
    resolvedBlock afterResolution computedK afterK hsnapshot.2 hmajor.2
      hresolution.2 hkTarget.2)
  intro _ afterPopulation _
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (snapshotGeneratedRecursors_wf resolvedBlock methods afterPopulation)
  intro _ final _
  exact TcM.WF.pure (I := I) (s := final)
    (Q := fun _ _ => True) (E := fun _ _ => True) (fun _ => trivial)

/-- Every successful production member check reaches one concrete frozen
preparation result and then succeeds through exactly the exhaustive checker
tail applied to that result. -/
theorem checkRecursorMemberImpl_success
    {id : KId m} {methods : Methods m} {initial final : TcState m}
    (run : (checkRecursorMemberImpl id).run methods initial = .ok () final) :
    GeneratedRecursorMemberCheckTrace id methods initial final := by
  unfold checkRecursorMemberImpl at run
  rw [ReaderT.run_bind, runTcBind] at run
  generalize hpreparation :
      (prepareRecursorMemberCheck id).run methods initial = result at run
  cases result with
  | error error afterPreparation => contradiction
  | ok prepared afterPreparation =>
      exact ⟨prepared, afterPreparation, hpreparation, run⟩

/-- Every successful preparation run visits all six named production stages
in order and returns exactly the data frozen by those executions. -/
theorem prepareRecursorMemberCheck_success
    {id : KId m} {methods : Methods m} {initial final : TcState m}
    {prepared : PreparedRecursorMemberCheck m}
    (run : (prepareRecursorMemberCheck id).run methods initial =
      .ok prepared final) :
    RecursorMemberPreparationTrace id methods initial prepared final := by
  unfold prepareRecursorMemberCheck at run
  rw [ReaderT.run_bind, runTcBind] at run
  generalize hsnapshot :
      (snapshotRecursorMemberDeclaration id).run methods initial =
        snapshotResult at run
  cases snapshotResult with
  | error error afterSnapshot => contradiction
  | ok snapshot afterSnapshot =>
      simp only at run
      rw [ReaderT.run_bind, runTcBind] at run
      generalize hmajor :
          (validateRecursorMemberMajor snapshot).run methods afterSnapshot =
            majorResult at run
      cases majorResult with
      | error error afterMajor => contradiction
      | ok indId afterMajor =>
          simp only at run
          rw [ReaderT.run_bind, runTcBind] at run
          generalize hresolution :
              (resolveRecursorMemberBlock snapshot indId).run methods
                afterMajor = resolutionResult at run
          cases resolutionResult with
          | error error afterResolution => contradiction
          | ok resolvedBlock afterResolution =>
              simp only at run
              rw [ReaderT.run_bind, runTcBind] at run
              generalize hk :
                  (validateRecursorMemberKTarget snapshot indId).run methods
                    afterResolution = kResult at run
              cases kResult with
              | error error afterK => contradiction
              | ok computedK afterK =>
                  simp only at run
                  rw [ReaderT.run_bind, runTcBind] at run
                  generalize hpopulation :
                      (populateRecursorRulesFromBlock resolvedBlock
                        snapshot.recBlock).run methods afterK =
                          populationResult at run
                  cases populationResult with
                  | error error afterPopulation => contradiction
                  | ok unitValue afterPopulation =>
                      cases unitValue
                      simp only at run
                      rw [ReaderT.run_bind, runTcBind] at run
                      generalize hgenerated :
                          (snapshotGeneratedRecursors resolvedBlock).run
                            methods afterPopulation = generatedResult at run
                      cases generatedResult with
                      | error error afterGenerated => contradiction
                      | ok generated afterGenerated =>
                          simp only at run
                          simp only [ReaderT.run_pure] at run
                          cases run
                          exact ⟨snapshot, afterSnapshot, hsnapshot, indId,
                            afterMajor, hmajor, resolvedBlock,
                            afterResolution, hresolution, computedK, afterK,
                            hk, afterPopulation, hpopulation, generated,
                            hgenerated, rfl⟩

/-- The second phase is definitionally the already verified frozen-cache
checker.  This wrapper keeps theorem statements tied to the production
member-check seam instead of manually projecting all fields at each caller. -/
theorem checkPreparedRecursorMember_canonicalScoped
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {calls : Methods.CallDomain}
    {source : Lean4Lean.VInductDecl}
    {generation : source.GenerationChecked}
    {id : KId .anon} {prepared : PreparedRecursorMemberCheck .anon}
    {methods : Methods .anon} {initial final : TcState .anon}
    (uvars : generation.recursor.uvars = model.keys.uvars)
    (run : (checkPreparedRecursorMember id prepared).run methods initial =
      .ok () final)
    (canonicalAt : ∀ {index : Nat} {selected : GeneratedRecursor .anon},
      prepared.generated[index]? = some selected →
        CanonicalArtifactsS world.venv world.nameOf trProj generation selected)
    (translations : StoredArtifactTranslationPlan world.venv
      generation.recursor.uvars world.nameOf trProj prepared.ty
      prepared.storedRules)
    (callPlanAt : ∀ {index : Nat} {selected : GeneratedRecursor .anon},
      prepared.generated[index]? = some selected →
        GeneratedArtifactCallPlan calls selected prepared.ty
          prepared.storedRules)
    (selectionInvariant : ∀ {index : Nat}
        {selected : GeneratedRecursor .anon} {afterSelection : TcState .anon},
      (selectGeneratedRecursorIndex prepared.recBlock id prepared.ty
        prepared.params prepared.motives prepared.minors prepared.indId
        prepared.generated).run methods initial =
          .ok (some index) afterSelection →
      prepared.generated[index]? = some selected →
        ScopedWhnfStateInv model layer semantics support [] afterSelection)
    (successor : Methods.ScopedWFAtOn model layer semantics support calls
      (Methods.next methods)) :
    CanonicalCacheAcceptance world.venv world.nameOf trProj generation
      prepared.recBlock id prepared.ty prepared.declaredLvls
      prepared.declaredIsUnsafe prepared.params prepared.motives
      prepared.minors prepared.indices prepared.indId prepared.storedRules
      prepared.generated methods
        (ScopedWhnfStateInv model layer semantics support []) initial final := by
  unfold checkPreparedRecursorMember at run
  exact checkGeneratedRecursorFromCache_canonicalScoped uvars run canonicalAt
    translations callPlanAt selectionInvariant successor

/-- Active coordinated-block spelling of the prepared-tail wrapper. -/
theorem checkPreparedRecursorMember_canonicalActiveScoped
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {calls : Methods.CallDomain}
    {source : Lean4Lean.VInductDecl}
    {generation : source.GenerationChecked}
    {id : KId .anon} {prepared : PreparedRecursorMemberCheck .anon}
    {methods : Methods .anon} {initial final : TcState .anon}
    (uvars : generation.recursor.uvars = model.keys.uvars)
    (run : (checkPreparedRecursorMember id prepared).run methods initial =
      .ok () final)
    (canonicalAt : ∀ {index : Nat} {selected : GeneratedRecursor .anon},
      prepared.generated[index]? = some selected →
        CanonicalArtifactsS world.venv world.nameOf trProj generation selected)
    (translations : StoredArtifactTranslationPlan world.venv
      generation.recursor.uvars world.nameOf trProj prepared.ty
      prepared.storedRules)
    (callPlanAt : ∀ {index : Nat} {selected : GeneratedRecursor .anon},
      prepared.generated[index]? = some selected →
        GeneratedArtifactCallPlan calls selected prepared.ty
          prepared.storedRules)
    (selectionInvariant : ∀ {index : Nat}
        {selected : GeneratedRecursor .anon} {afterSelection : TcState .anon},
      (selectGeneratedRecursorIndex prepared.recBlock id prepared.ty
        prepared.params prepared.motives prepared.minors prepared.indId
        prepared.generated).run methods initial =
          .ok (some index) afterSelection →
      prepared.generated[index]? = some selected →
        ScopedActiveWhnfStateInv model layer semantics support members []
          afterSelection)
    (successor : Methods.ActiveScopedWFAtOn model layer semantics support
      members calls (Methods.next methods)) :
    CanonicalCacheAcceptance world.venv world.nameOf trProj generation
      prepared.recBlock id prepared.ty prepared.declaredLvls
      prepared.declaredIsUnsafe prepared.params prepared.motives
      prepared.minors prepared.indices prepared.indId prepared.storedRules
      prepared.generated methods
        (ScopedActiveWhnfStateInv model layer semantics support members [])
        initial final := by
  unfold checkPreparedRecursorMember at run
  exact checkGeneratedRecursorFromCache_canonicalActiveScoped uvars run
    canonicalAt translations callPlanAt selectionInvariant successor

end RecM

end Ix.Tc
