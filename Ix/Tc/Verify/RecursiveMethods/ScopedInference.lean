import Ix.Tc.Verify.Infer.CacheSoundness
import Ix.Tc.Verify.RecursiveMethods.ScopedCallDomains

/-!
# Run-scoped call-domain inference

This is the finite-suffix-state counterpart of `RecursiveMethods.Inference`.
The production cache shell is proved directly over `ScopedWhnfStateInv`:
key construction advances the suffix scope through its memo update, while
interning and cache insertion use the exact digest-neutral state frame.

No theorem in this module converts a `ScopedKernelSuffixModel` to the legacy
globally quantified `KernelSuffixModel`.
-/

namespace Ix.Tc

namespace InternTable

/-- Expressions newly present in `after` at keys absent from `before`.  This
is the exact finite support delta needed by an intern-only checker phase. -/
def NewExpr (before after : InternTable .anon) (e : KExpr .anon) : Prop :=
  ∃ address : Address, after.exprs[address]? = some e ∧
    before.exprs[address]? = none

/-- The range newly introduced by one concrete intern-table transition is
constructively finite. -/
theorem newExpr_finite (before after : InternTable .anon) :
    FiniteSupport (NewExpr before after) := by
  refine ⟨after.exprs.toList.map Prod.snd, ?_⟩
  rintro e ⟨address, hafter, _⟩
  apply List.mem_map.mpr
  exact ⟨(address, e),
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hafter, rfl⟩

/-- Every old expression binding remains physically present in the new
table.  This is stronger than range inclusion and rules out callback-driven
replacement at an already occupied digest. -/
def ExprExtends (before after : InternTable .anon) : Prop :=
  ∀ {address : Address} {expression : KExpr .anon},
    before.exprs[address]? = some expression →
    after.exprs[address]? = some expression

/-- A finite `toList` certificate establishes physical expression-map
extension. -/
theorem ExprExtends.of_toList {before after : InternTable .anon}
    (h : ∀ address expression,
      (address, expression) ∈ before.exprs.toList →
        after.exprs[address]? = some expression) :
    ExprExtends before after := by
  unfold ExprExtends
  intro address expression hbefore
  exact h address expression
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hbefore)

/-- Finite key-coherence certificates reconstruct the ordinary intern-table
well-formedness predicate.  Concrete execution fixtures can discharge these
two list predicates by evaluation without postulating a state invariant. -/
theorem WF.of_toList {it : InternTable .anon}
    (hunivs : ∀ (address : Address) (univ : KUniv .anon),
      (address, univ) ∈ it.univs.toList → univ.addr = address)
    (hexprs : ∀ (address : Address) (expression : KExpr .anon),
      (address, expression) ∈ it.exprs.toList →
        expression.internKey = address) :
    it.WF := by
  constructor
  · intro address univ hlookup
    exact hunivs address univ
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hlookup)
  · intro address expression hlookup
    exact hexprs address expression
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hlookup)

end InternTable

namespace RunSupport.CoversIntern

/-- Extend run support across a concrete expression-only intern transition.
Old bindings are retained, universe bindings frame exactly, and the caller
supplies support only for the finite `InternTable.NewExpr` delta. -/
theorem of_expr_extension {support : RunSupport}
    {before after : InternTable .anon}
    (hbefore : support.CoversIntern before)
    (hunivs : after.univs = before.univs)
    (hextends : before.ExprExtends after)
    (hnew : ∀ expression, before.NewExpr after expression →
      support expression) :
    support.CoversIntern after := by
  constructor
  · intro expression hsupport
    obtain ⟨address, hafter⟩ := hsupport
    cases hbeforeLookup : before.exprs[address]? with
    | none => exact hnew expression ⟨address, hafter, hbeforeLookup⟩
    | some old =>
        unfold InternTable.ExprExtends at hextends
        have hold := hextends hbeforeLookup
        rw [hafter] at hold
        cases hold
        exact hbefore.expr expression ⟨address, hbeforeLookup⟩
  · intro univ hsupport
    apply hbefore.univ univ
    simpa only [InternTable.UnivSupport, hunivs] using hsupport

end RunSupport.CoversIntern

namespace ScopedWhnfStateInv

/-- The extensional state projection needed to transport the ordinary WHNF
invariant across rule-building intern effects.  Binder traversal may consume
fresh-variable ids and truncate the local-context index back to an
extensionally equal declaration stack, so neither exact `KEnv` equality nor
exact `LocalContext` representation equality belongs here.

The physical cache and loaded-constant fields are framed by lookup transfer,
the mutable equivalence manager by preservation of its semantic invariant,
and the local context by declaration-array equality plus preservation of its
extensional index invariant.  Diagnostic counters and fuel are intentionally
absent. -/
structure InternSemanticFrame (before after : TcState .anon) : Prop where
  consts : ∀ {id constant}, after.env.get? id = some constant →
    before.env.get? id = some constant
  blocks : ∀ {block : KId .anon} {members : Array (KId .anon)},
    after.env.blocks[block]? = some members →
    before.env.blocks[block]? = some members
  cacheEntries : ∀ {entry}, after.env.HasCacheEntry entry →
    before.env.HasCacheEntry entry
  equivalences : ∀ {relation},
    EquivManager.WF relation before.equivManager →
    EquivManager.WF relation after.equivManager
  primitiveAddresses : after.prims.addressTable = before.prims.addressTable
  noAccel : after.noAccel = before.noAccel
  ctx : after.ctx = before.ctx
  letVals : after.letVals = before.letVals
  numLetBindings : after.numLetBindings = before.numLetBindings
  lctxDecls : after.lctx.decls = before.lctx.decls
  lctxWF : before.lctx.WF → after.lctx.WF
  nextFVarId : before.env.nextFVarId.toNat ≤ after.env.nextFVarId.toNat

/-- Rebuild the complete run-scoped invariant from the smallest exact state
projection it consumes. -/
theorem of_internSemanticFrame
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {Delta : KVLCtx}
    {before after : TcState .anon}
    (hframe : InternSemanticFrame before after)
    (hintern : after.env.intern.WF)
    (hcover : support.CoversIntern after.env.intern)
    (hscope : model.StateInScope before → model.StateInScope after)
    (hI : ScopedWhnfStateInv model layer semantics support Delta before) :
    ScopedWhnfStateInv model layer semantics support Delta after := by
  have hkernel : KernelStateWF semantics trProj world support after := {
    core := {
      trustedCatalog := hI.1.1.core.trustedCatalog
      loaded := fun hget => hI.1.1.core.loaded (hframe.consts hget)
      intern := hintern }
    internSupport := hcover
    caches := fun {_} hentry => hI.1.1.caches (hframe.cacheEntries hentry)
    equivalences := hframe.equivalences hI.1.1.equivalences }
  have hbase : WhnfStateInv layer semantics trProj world support
      model.keys.uvars Delta after := by
    refine ⟨hkernel, ?_, ?_⟩
    · exact {
        size_eq := by
          rw [hframe.ctx, hframe.letVals]
          exact hI.1.2.1.size_eq
        recon := by
          rw [hframe.ctx, hframe.letVals, hframe.lctxDecls]
          exact hI.1.2.1.recon
        lwf := hframe.lctxWF hI.1.2.1.lwf
        incr := by
          rw [hframe.lctxDecls]
          exact hI.1.2.1.incr
        fresh := by
          rw [hframe.lctxDecls]
          exact fun declaration hmem =>
            Nat.lt_of_lt_of_le (hI.1.2.1.fresh declaration hmem)
              hframe.nextFVarId
        lets := by
          rw [hframe.numLetBindings]
          exact hI.1.2.1.lets }
    · cases layer with
      | structuralNoAccel =>
          simpa [WhnfLayer.StateOK, hframe.noAccel] using hI.1.2.2
      | noAccel =>
          rcases hI.1.2.2 with ⟨hnoAccel, hcanonical⟩
          refine ⟨by simpa only [hframe.noAccel] using hnoAccel, ?_⟩
          unfold Primitives.CanonicalAnon at hcanonical ⊢
          simpa only [hframe.primitiveAddresses] using hcanonical
      | accelerated =>
          change after.prims.CanonicalAnon
          have hcanonical : before.prims.CanonicalAnon := hI.1.2.2
          unfold Primitives.CanonicalAnon at hcanonical ⊢
          simpa only [hframe.primitiveAddresses] using hcanonical
  exact ⟨hbase, hscope hI.2⟩

/-- Rebuild the complete run-scoped invariant after an expression-only intern
transition.  The ordinary WHNF invariant uses the supplied key coherence and
range coverage; the suffix witness advances through the same digest-neutral
frame. -/
theorem of_internUpdateFrame
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {Delta : KVLCtx}
    {before after : TcState .anon}
    (hframe : InternUpdateFrame before after)
    (hintern : after.env.intern.WF)
    (hcover : support.CoversIntern after.env.intern)
    (hI : ScopedWhnfStateInv model layer semantics support Delta before) :
    ScopedWhnfStateInv model layer semantics support Delta after := by
  apply of_internSemanticFrame (hintern := hintern) (hcover := hcover)
    (hscope := fun hscope => model.preservesFrame hscope
      (ContextDigestFrame.ofInternUpdateFrame hframe)) (hI := hI)
  rw [hframe]
  exact {
    consts := fun hget => hget
    blocks := fun hget => hget
    cacheEntries := by
      intro entry hentry
      cases hentry with
      | whnf hget => exact .whnf hget
      | whnfNoDelta hget => exact .whnfNoDelta hget
      | whnfNoDeltaCheap hget => exact .whnfNoDeltaCheap hget
      | whnfCore hget => exact .whnfCore hget
      | whnfCoreCheap hget => exact .whnfCoreCheap hget
      | infer hget => exact .infer hget
      | inferOnly hget => exact .inferOnly hget
      | defEq hget => exact .defEq hget
      | defEqCheap hget => exact .defEqCheap hget
      | defEqFailure hmem => exact .defEqFailure hmem
      | unfold hget => exact .unfold hget
      | natSuccStuck hmem => exact .natSuccStuck hmem
      | isProp hget => exact .isProp hget
      | isRec hget => exact .isRec hget
      | recursor hget => exact .recursor hget
      | recMajors hget => exact .recMajors hget
      | blockPeer hmem => exact .blockPeer hmem
      | blockResult hget => exact .blockResult hget
    equivalences := fun h => h
    primitiveAddresses := rfl
    noAccel := rfl
    ctx := rfl
    letVals := rfl
    numLetBindings := rfl
    lctxDecls := rfl
    lctxWF := fun h => h
    nextFVarId := Nat.le_refl _ }

end ScopedWhnfStateInv

namespace TcM

/-- Direct interning preserves a run-scoped suffix model because its exact
state frame changes only the intern table.  The successful result and frame
remain exposed for syntax-specific leaf proofs. -/
theorem intern_scoped_wf
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {Delta : KVLCtx}
    {e : KExpr .anon} {s : TcState .anon}
    (hcollision : support.CollisionFree) (hsupport : support e) :
    TcM.WF (ScopedWhnfStateInv model layer semantics support Delta) s
      (TcM.intern e)
      (fun result after => result = e ∧ InternUpdateFrame s after) := by
  intro hI
  obtain ⟨after, hrun, hbase, hframe⟩ :=
    TcM.intern_whnf_eval hcollision hsupport hI.1
  rw [hrun]
  exact ⟨⟨hbase, model.preservesFrame hI.2
    (ContextDigestFrame.ofInternUpdateFrame hframe)⟩, rfl, hframe⟩

/-- Lift any exact, support-preserving `InternM` computation to the run-scoped
suffix invariant.  Unlike direct `intern_scoped_wf`, this form covers the
finite lift/substitution/instantiation walkers used while constructing
generated recursor rules. -/
theorem runIntern_scoped_wf
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {Delta : KVLCtx}
    {x : InternM .anon α} {expected : α} {s : TcState .anon}
    (hspec : ∀ it : InternTable .anon, it.WF →
      support.CoversIntern it →
      (x it).1 = expected ∧ (x it).2.WF ∧
        support.CoversIntern (x it).2) :
    TcM.WF (ScopedWhnfStateInv model layer semantics support Delta) s
      (TcM.runIntern x)
      (fun result after =>
        result = expected ∧ InternUpdateFrame s after) := by
  intro hI
  obtain ⟨after, hrun, hbase, hframe⟩ :=
    TcM.runIntern_whnf_eval hspec hI.1
  rw [hrun]
  exact ⟨⟨hbase, model.preservesFrame hI.2
    (ContextDigestFrame.ofInternUpdateFrame hframe)⟩, rfl, hframe⟩

end TcM

/-- Per-layer inference resources whose uncached body preserves the finite
suffix-state domain as well as the ordinary checker invariant. -/
structure ScopedInferenceCallDomainContext
    {trProj : RawProjRel} {world : VerifyWorld} (scope : RunSupport)
    (model : ScopedKernelSuffixModel trProj world)
    (current predecessor : Methods.CallDomain) : Type where
  collisionFree : scope.CollisionFree
  currentWithin : current.Within scope
  theory : WhnfTheory trProj world model.keys.uvars
  references : RecM.TrustedReferences world scope
  uncached : ∀ {Delta : KVLCtx} {s : TcState .anon} {inferOnly : Bool}
      {source : KExpr .anon} {sourceV : Lean4Lean.VExpr},
    current.infer source →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    RecM.ScopedWFOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor Delta s
      (RecM.inferUncached RecM.inferCall inferOnly source)
      (fun result _ => scope result ∧
        InferPost trProj world model.keys.uvars Delta sourceV result)

namespace ScopedInferenceCallDomainContext

private theorem cacheReferences
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : ScopedInferenceCallDomainContext scope model current
      predecessor)
    {kind : ExprCacheKind} {key : Address × Address}
    {ty : KExpr .anon} (hty : scope ty) :
    (CacheEntry.expr kind key ty).ReferencesAuthorized
      (CacheAuthority.stable world) scope := by
  intro id href
  apply Or.inl
  rcases href with href | href
  · obtain ⟨source, hsource, _, hreference⟩ := href
    exact context.references hsource hreference
  · exact context.references hty href

/-- A validated inference-cache insertion changes no suffix-digest input
field, so it preserves both halves of the scoped invariant. -/
private theorem cacheWriteFull_scopedWFOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {predecessor : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {key : Address × Address} {ty : KExpr .anon}
    (hnew : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) scope (.expr .infer key ty)) :
    RecM.ScopedWFOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor Delta s
      (RecM.cacheInferResult false key ty) (fun _ _ => True) := by
  intro methods _ hI
  rw [RecM.cacheInferResult_full_run]
  refine ⟨⟨RecM.InferCacheUpdate.full_whnfStateInv hI.1 hnew,
    model.preservesFrame hI.2 ?_⟩, trivial⟩
  constructor <;> rfl

/-- An infer-only cache insertion has the same digest-neutral state frame. -/
private theorem cacheWriteInferOnly_scopedWFOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {predecessor : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {key : Address × Address} {ty : KExpr .anon}
    (hnew : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) scope (.expr .inferOnly key ty)) :
    RecM.ScopedWFOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor Delta s
      (RecM.cacheInferResult true key ty) (fun _ _ => True) := by
  intro methods _ hI
  rw [RecM.cacheInferResult_inferOnly_run]
  refine ⟨⟨RecM.InferCacheUpdate.inferOnly_whnfStateInv hI.1 hnew,
    model.preservesFrame hI.2 ?_⟩, trivial⟩
  constructor <;> rfl

/-- Execute one admitted uncached source and install its result without ever
leaving the model's finite suffix-state domain. -/
private theorem missTail_scopedWFOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : ScopedInferenceCallDomainContext scope model current
      predecessor)
    {Delta : KVLCtx} {before s : TcState .anon} {inferOnly : Bool}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    {key : Address × Address}
    (hmatch : model.keys.Matches trProj world before Delta source key)
    (hcall : current.infer source)
    (hsource : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
      source sourceV) :
    RecM.ScopedWFOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor Delta s
      (do
        let ty ← RecM.inferUncached RecM.inferCall inferOnly source
        RecM.cacheInferResult inferOnly key ty
        pure ty)
      (fun result _ => scope result ∧
        InferPost trProj world model.keys.uvars Delta sourceV result) := by
  have hsourceSupport := context.currentWithin.infer hcall
  cases inferOnly with
  | false =>
      apply RecM.ScopedWFOn.bind
        (RecM.ScopedWFOn.withInv (context.uncached hcall hsource))
      intro ty afterBody hbody
      rcases hbody with ⟨_, hty, hpost⟩
      have hprovenance := model.transports.inferProvenance
        context.collisionFree .infer hsourceSupport hty hmatch
        (InferMeaning.of_post hsource hpost)
        (context.cacheReferences hty)
      apply RecM.ScopedWFOn.bind
        (Q1 := fun _ _ => True)
        (cacheWriteFull_scopedWFOn (predecessor := predecessor) hprovenance)
      intro _ afterWrite _
      exact RecM.ScopedWFOn.pure fun _ => ⟨hty, hpost⟩
  | true =>
      apply RecM.ScopedWFOn.bind
        (RecM.ScopedWFOn.withInv (context.uncached hcall hsource))
      intro ty afterBody hbody
      rcases hbody with ⟨_, hty, hpost⟩
      have hprovenance := model.transports.inferProvenance
        context.collisionFree .inferOnly hsourceSupport hty hmatch
        (InferMeaning.of_post hsource hpost)
        (context.cacheReferences hty)
      apply RecM.ScopedWFOn.bind
        (Q1 := fun _ _ => True)
        (cacheWriteInferOnly_scopedWFOn (predecessor := predecessor)
          hprovenance)
      intro _ afterWrite _
      exact RecM.ScopedWFOn.pure fun _ => ⟨hty, hpost⟩

/-- Production `inferWith` over one admitted source, with scope preserved on
key errors, cache hits, uncached errors, and both cache-write partitions. -/
theorem inferWith_scopedWFOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : ScopedInferenceCallDomainContext scope model current
      predecessor)
    {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hcall : current.infer source)
    (hsource : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
      source sourceV) :
    RecM.ScopedWFOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor Delta s
      (RecM.inferWith RecM.inferCall source)
      (fun result _ => scope result ∧
        InferPost trProj world model.keys.uvars Delta sourceV result) := by
  have hsourceSupport := context.currentWithin.infer hcall
  unfold RecM.inferWith
  apply RecM.ScopedWFOn.bind
    (Q1 := fun observed after => observed = s ∧ after = s)
    (RecM.ScopedWFOn.get fun _ => ⟨rfl, rfl⟩)
  intro observed after hread
  rcases hread with ⟨hObserved, hAfter⟩
  subst observed
  subst after
  apply RecM.ScopedWFOn.bind
    (Q1 := fun key _ =>
      model.keys.Matches trProj world s Delta source key)
  · apply RecM.ScopedWFOn.liftTcM
    exact TcM.WF.mono (TcM.inferKey_scoped_model_matches_wf model)
      (fun _ _ h => h.1) (fun _ _ h => h)
  · intro key afterKey hmatch
    apply RecM.ScopedWFOn.bind
      (Q1 := fun currentState after =>
        currentState = afterKey ∧ after = afterKey)
      (RecM.ScopedWFOn.get fun _ => ⟨rfl, rfl⟩)
    intro currentState afterRead hread
    rcases hread with ⟨hCurrent, hAfterRead⟩
    subst currentState
    subst afterRead
    let fullFound := afterKey.env.inferCache[key]?
    cases hfullFound : fullFound with
    | some cached =>
        have hhit : afterKey.env.inferCache[key]? = some cached := by
          simpa [fullFound] using hfullFound
        simp only [hhit]
        exact RecM.ScopedWFOn.pure fun hI => by
          have hprovenance := hI.1.1.caches.hit (.infer hhit)
          have hmeaning := hprovenance.kernelInferMeaningOfMatches
            .infer hsourceSupport hmatch hsource.contextScoped
          exact ⟨hprovenance.supported.2,
            hmeaning.post context.theory hI.1.2.1.wf hsource⟩
    | none =>
        have hfullMiss : afterKey.env.inferCache[key]? = none := by
          simpa [fullFound] using hfullFound
        simp only [hfullMiss]
        cases hpolicy : s.inferOnly with
        | false =>
            simp only [Bool.false_eq_true, if_false]
            exact context.missTail_scopedWFOn hmatch hcall hsource
        | true =>
            simp only [pure_bind, if_true]
            apply RecM.ScopedWFOn.bind
              (Q1 := fun currentState after =>
                currentState = afterKey ∧ after = afterKey)
              (RecM.ScopedWFOn.get fun _ => ⟨rfl, rfl⟩)
            intro currentState afterInferOnlyRead hread
            rcases hread with ⟨hCurrent, hAfterRead⟩
            subst currentState
            subst afterInferOnlyRead
            let inferOnlyFound := afterKey.env.inferOnlyCache[key]?
            cases hinferOnlyFound : inferOnlyFound with
            | some cached =>
                have hhit : afterKey.env.inferOnlyCache[key]? = some cached :=
                  by simpa [inferOnlyFound] using hinferOnlyFound
                simp only [hhit]
                exact RecM.ScopedWFOn.pure fun hI => by
                  have hprovenance := hI.1.1.caches.hit (.inferOnly hhit)
                  have hmeaning := hprovenance.kernelInferMeaningOfMatches
                    .inferOnly hsourceSupport hmatch hsource.contextScoped
                  exact ⟨hprovenance.supported.2,
                    hmeaning.post context.theory hI.1.2.1.wf hsource⟩
            | none =>
                have hmiss : afterKey.env.inferOnlyCache[key]? = none := by
                  simpa [inferOnlyFound] using hinferOnlyFound
                simp only [hmiss]
                exact context.missTail_scopedWFOn hmatch hcall hsource

/-- The inference field of one unfolded method-table layer, now directly
proved over the run-scoped suffix model. -/
theorem nextInfer_scopedWFAtOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : ScopedInferenceCallDomainContext scope model current
      predecessor)
    (predecessorMethods : Methods .anon)
    (predecessorWF : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor
      predecessorMethods) :
    ∀ {Delta : KVLCtx} {s : TcState .anon}
        {source : KExpr .anon} {sourceV : Lean4Lean.VExpr},
      current.infer source →
      TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
        sourceV →
      TcM.WF
        (ScopedWhnfStateInv model .noAccel
          (kernelCacheSemantics model.keys trProj) scope Delta) s
        ((Methods.next predecessorMethods).infer source)
        (fun result _ => scope result ∧
          InferPost trProj world model.keys.uvars Delta sourceV result) := by
  intro Delta s source sourceV hcall hsource
  simpa [Methods.next, RecM.infer] using
    (context.inferWith_scopedWFOn hcall hsource) predecessorMethods
      predecessorWF

end ScopedInferenceCallDomainContext

end Ix.Tc
