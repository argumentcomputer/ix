import Ix.Tc.Verify.Check.BlockTransaction
import Ix.Tc.Verify.Inductive.StructuralCacheSemantics
import Ix.Tc.Verify.RecursiveMethods.ScopedInference

/-!
# Run-scoped recursive methods inside an active coordinated block

`ScopedWhnfStateInv` deliberately describes stable checker boundaries.  An
inductive or recursor block is different: structural cache entries may refer
to the exact physical members currently being checked.  Recursive generated
rules make this distinction unavoidable because their right-hand sides name
the recursor before that recursor can be promoted to stable trust.

This module combines `ActiveBlockStateWF` with context reconstruction and the
finite suffix-model domain.  It does not grant active authority to ordinary
WHNF, inference, or DefEq cache entries; that restriction remains enforced by
`CacheEntry.ReferencesAuthorized`.  Only subject-scoped structural entries
can consume the active-member disjunct.
-/

namespace Ix.Tc

/-- The complete K1/K2 state invariant while one exact coordinated block is
active, refined by membership in a finite suffix-model state domain. -/
structure ScopedActiveWhnfStateInv
    {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (support : RunSupport) (members : Array (KId .anon))
    (Delta : KVLCtx) (state : TcState .anon) : Prop where
  active : ActiveBlockStateWF semantics trProj world support members state
  context : CtxRecon world.venv model.keys.uvars world.nameOf trProj state
    Delta
  layer : layer.StateOK state
  inScope : model.StateInScope state

namespace ScopedActiveWhnfStateInv

/-- Enter exact active-block authority from an ordinary stable scoped state.
No cache is created at this boundary; already-valid stable entries are merely
viewed under the larger coordinated-block authority. -/
theorem ofScoped
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {Delta : KVLCtx} {state : TcState .anon}
    (blocks : LoadedBlocksAgrees world.blocks state.env)
    (h : ScopedWhnfStateInv model layer semantics support Delta state) :
    ScopedActiveWhnfStateInv model layer semantics support members Delta
      state where
  active := ActiveBlockStateWF.ofKernel h.1.1 blocks
  context := h.1.2.1
  layer := h.1.2.2
  inScope := h.2

/-- Transport the active invariant across the extensional intern/binder frame
used by generated-rule construction.  The block-map projection is explicit:
unlike the stable kernel invariant, active authority must retain exact loaded
block identity. -/
theorem of_internSemanticFrame
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {Delta : KVLCtx} {before after : TcState .anon}
    (frame : ScopedWhnfStateInv.InternSemanticFrame before after)
    (intern : after.env.intern.WF)
    (cover : support.CoversIntern after.env.intern)
    (scope : model.StateInScope before → model.StateInScope after)
    (h : ScopedActiveWhnfStateInv model layer semantics support members
      Delta before) :
    ScopedActiveWhnfStateInv model layer semantics support members Delta
      after := by
  refine ⟨?_, ?_, ?_, scope h.inScope⟩
  · exact {
      blockState := {
        core := {
          trustedCatalog := h.active.blockState.core.trustedCatalog
          loaded := fun hget =>
            h.active.blockState.core.loaded (frame.consts hget)
          intern := intern }
        loadedBlocks := fun hget =>
          h.active.blockState.loadedBlocks (frame.blocks hget) }
      internSupport := cover
      caches := fun {_} hentry => h.active.caches (frame.cacheEntries hentry)
      equivalences := frame.equivalences h.active.equivalences }
  · exact {
      size_eq := by
        rw [frame.ctx, frame.letVals]
        exact h.context.size_eq
      recon := by
        rw [frame.ctx, frame.letVals, frame.lctxDecls]
        exact h.context.recon
      lwf := frame.lctxWF h.context.lwf
      incr := by
        rw [frame.lctxDecls]
        exact h.context.incr
      fresh := by
        rw [frame.lctxDecls]
        exact fun declaration hmem =>
          Nat.lt_of_lt_of_le (h.context.fresh declaration hmem)
            frame.nextFVarId
      lets := by
        rw [frame.numLetBindings]
        exact h.context.lets }
  · cases layer with
    | structuralNoAccel =>
        simpa [WhnfLayer.StateOK, frame.noAccel] using h.layer
    | noAccel =>
        rcases h.layer with ⟨hnoAccel, hcanonical⟩
        refine ⟨by simpa only [frame.noAccel] using hnoAccel, ?_⟩
        unfold Primitives.CanonicalAnon at hcanonical ⊢
        simpa only [frame.primitiveAddresses] using hcanonical
    | accelerated =>
        change after.prims.CanonicalAnon
        have hcanonical : before.prims.CanonicalAnon := h.layer
        unfold Primitives.CanonicalAnon at hcanonical ⊢
        simpa only [frame.primitiveAddresses] using hcanonical

/-- Changing only operational bookkeeping fields preserves the complete
active scoped invariant.  The suffix-domain frame is separate from the
semantic-state equations because context-digest scope also observes memo and
fault fields which ordinary K1 cache provenance intentionally ignores. -/
theorem of_semantic_fields_eq
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {Delta : KVLCtx} {before after : TcState .anon}
    (h : ScopedActiveWhnfStateInv model layer semantics support members
      Delta before)
    (henv : after.env = before.env)
    (hctx : after.ctx = before.ctx)
    (hlet : after.letVals = before.letVals)
    (hnum : after.numLetBindings = before.numLetBindings)
    (hlctx : after.lctx = before.lctx)
    (hprims : after.prims = before.prims)
    (hnoAccel : after.noAccel = before.noAccel)
    (hequiv : after.equivManager = before.equivManager)
    (hdigest : ContextDigestFrame before after) :
    ScopedActiveWhnfStateInv model layer semantics support members Delta
      after := by
  refine ⟨?_, ?_, ?_, model.preservesFrame h.inScope hdigest⟩
  · exact {
      blockState := h.active.blockState.of_env_eq henv
      internSupport := by simpa only [henv] using h.active.internSupport
      caches := h.active.caches.of_env_eq henv
      equivalences := by simpa only [hequiv] using h.active.equivalences }
  · exact h.context.of_fields_eq hctx hlet hnum hlctx (by simp [henv])
  · cases layer with
    | structuralNoAccel =>
        simpa only [WhnfLayer.StateOK, hnoAccel] using h.layer
    | noAccel =>
        simpa only [WhnfLayer.StateOK, hprims, hnoAccel] using h.layer
    | accelerated =>
        simpa only [WhnfLayer.StateOK, hprims] using h.layer

/-- Insert or replace a generated-recursor batch under exact active-block
authority.  This is the active counterpart of
`ScopedWhnfStateInv.insertRecursor`; the provenance authority is not silently
weakened to the stable world. -/
theorem insertRecursor
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {Delta : KVLCtx} {state : TcState .anon} {block : KId .anon}
    {generated : Array (GeneratedRecursor .anon)}
    (newEntry : CacheProvenance semantics
      (CacheAuthority.coordinatedBlock world members) support
      (.recursor block generated))
    (h : ScopedActiveWhnfStateInv model layer semantics support members
      Delta state) :
    ScopedActiveWhnfStateInv model layer semantics support members Delta
      { state with env := { state.env with
        recursorCache := state.env.recursorCache.insert block generated } } := by
  refine ⟨?_, ?_, ?_, model.preservesFrame h.inScope ?_⟩
  · exact {
      blockState := {
        core := h.active.blockState.core.of_consts_eq rfl (by
          simpa using h.active.blockState.core.intern)
        loadedBlocks := by
          intro foundBlock foundMembers hget
          exact h.active.blockState.loadedBlocks hget }
      internSupport := by simpa using h.active.internSupport
      caches := CacheInvariant.insertRecursor h.active.caches newEntry
      equivalences := by simpa using h.active.equivalences }
  · exact h.context.of_fields_eq rfl rfl rfl rfl (Nat.le_refl _)
  · cases layer <;> exact h.layer
  · constructor <;> rfl

end ScopedActiveWhnfStateInv

namespace TcM

/-- Optional step journaling is state-pure for the active scoped invariant. -/
theorem stepTrace_activeScoped_wf
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {Delta : KVLCtx} (tag : String) (payload : Unit → String)
    (state : TcState .anon) :
    TcM.WF (ScopedActiveWhnfStateInv model layer semantics support members
      Delta) state (TcM.stepTrace tag payload) (fun _ _ => True) := by
  unfold TcM.stepTrace
  apply TcM.WF.bind
    (Q₁ := fun read after => read = state ∧ after = state)
    (TcM.WF.get fun _ => ⟨rfl, rfl⟩)
  rintro read after ⟨rfl, rfl⟩
  simp only
  split <;> exact TcM.WF.pure (fun _ => trivial)

/-- A statistics-only record update preserves active scoped authority and the
finite suffix domain. -/
theorem bumpStats_activeScoped_wf
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {Delta : KVLCtx} (f : TcState .anon → TcState .anon)
    (henv : ∀ state, (f state).env = state.env)
    (hctx : ∀ state, (f state).ctx = state.ctx)
    (hlet : ∀ state, (f state).letVals = state.letVals)
    (hnum : ∀ state,
      (f state).numLetBindings = state.numLetBindings)
    (hlctx : ∀ state, (f state).lctx = state.lctx)
    (hprims : ∀ state, (f state).prims = state.prims)
    (hnoAccel : ∀ state, (f state).noAccel = state.noAccel)
    (hequiv : ∀ state,
      (f state).equivManager = state.equivManager)
    (hdigest : ∀ state, ContextDigestFrame state (f state))
    (state : TcState .anon) :
    TcM.WF (ScopedActiveWhnfStateInv model layer semantics support members
      Delta) state (TcM.bumpStats f) (fun _ _ => True) := by
  unfold TcM.bumpStats
  apply TcM.WF.bind
    (Q₁ := fun read after => read = state ∧ after = state)
    (TcM.WF.get fun _ => ⟨rfl, rfl⟩)
  rintro read after ⟨rfl, rfl⟩
  split
  · exact TcM.WF.modifyGet
      (fun hI => hI.of_semantic_fields_eq (henv after) (hctx after)
        (hlet after) (hnum after) (hlctx after) (hprims after)
        (hnoAccel after) (hequiv after) (hdigest after))
      (fun _ => trivial)
  · exact TcM.WF.pure (fun _ => trivial)

end TcM

namespace RecM

/-- The real production DefEq entry point is sound under active block
authority when its two concrete inputs are literally equal.  This is stronger
than an address collision argument and exactly matches frozen generated
artifacts retained by the transactional commit. -/
theorem isDefEq_eq_activeScoped_wf
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {members : Array (KId .anon)}
    {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon}
    {leftV rightV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world model.keys.uvars)
    (same : left = right)
    (leftTranslation : TrKExprS world.venv model.keys.uvars world.nameOf
      trProj Delta left leftV)
    (rightTranslation : TrKExprS world.venv model.keys.uvars world.nameOf
      trProj Delta right rightV)
    (methods : Methods .anon) :
    TcM.WF (ScopedActiveWhnfStateInv model layer semantics support members
      Delta) state ((isDefEq left right).run methods)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx leftV rightV) := by
  subst right
  unfold isDefEq
  simp only [ReaderT.run_bind]
  apply TcM.WF.bind
  · exact TcM.stepTrace_activeScoped_wf "deq"
      (fun _ => s!"{TcM.addr8 left.addr} ~ {TcM.addr8 left.addr}") state
  · intro _ afterTrace _
    apply TcM.WF.bind
    · exact TcM.bumpStats_activeScoped_wf
        (fun current => { current with deqCalls := current.deqCalls + 1 })
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => by constructor <;> rfl)
        afterTrace
    · intro _ _ _
      simp only [beq_self_eq_true, if_true]
      apply TcM.WF.pure
      intro hI answerTrue
      apply DefEqMeaning.of_translations theory hI.context.wf
        leftTranslation rightTranslation _ answerTrue
      intro _
      exact ⟨leftV, leftV, leftTranslation, leftTranslation,
        Lean4Lean.VEnv.IsDefEqU.refl
          (theory.exprWF hI.context leftTranslation)⟩

end RecM

namespace Methods

/-- Six-field finite call-domain contract under exact active-block authority.
The semantic conclusions are unchanged; only the physical cache invariant is
allowed to carry subject-scoped references to `members`. -/
structure ActiveScopedWFAtOn
    {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (support : RunSupport) (members : Array (KId .anon))
    (calls : CallDomain) (methods : Methods .anon) : Prop where
  within : calls.Within support
  whnf : ∀ {Delta state source sourceV},
    calls.whnf source →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    TcM.WF (ScopedActiveWhnfStateInv model layer semantics support members
      Delta) state (methods.whnf source)
      (fun result _ => support result ∧
        WhnfPost trProj world model.keys.uvars Delta sourceV result)
  whnfCore : ∀ {Delta state source sourceV},
    calls.whnfCore source →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    TcM.WF (ScopedActiveWhnfStateInv model layer semantics support members
      Delta) state (methods.whnfCore source)
      (fun result _ => support result ∧
        WhnfPost trProj world model.keys.uvars Delta sourceV result)
  whnfMode : ∀ {Delta state source sourceV} {mode : NatSuccMode},
    calls.whnfMode source mode →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    TcM.WF (ScopedActiveWhnfStateInv model layer semantics support members
      Delta) state (methods.whnfMode source mode)
      (fun result _ => support result ∧
        WhnfPost trProj world model.keys.uvars Delta sourceV result)
  whnfCoreFlags : ∀ {Delta state source sourceV} {flags : WhnfFlags},
    calls.whnfCoreFlags source flags →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    TcM.WF (ScopedActiveWhnfStateInv model layer semantics support members
      Delta) state (methods.whnfCoreFlags source flags)
      (fun result _ => support result ∧
        WhnfPost trProj world model.keys.uvars Delta sourceV result)
  infer : ∀ {Delta state source sourceV},
    calls.infer source →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    TcM.WF (ScopedActiveWhnfStateInv model layer semantics support members
      Delta) state (methods.infer source)
      (fun type _ => support type ∧
        InferPost trProj world model.keys.uvars Delta sourceV type)
  isDefEq : ∀ {Delta state left right leftV rightV},
    calls.isDefEq left right →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta left
      leftV →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta right
      rightV →
    TcM.WF (ScopedActiveWhnfStateInv model layer semantics support members
      Delta) state (methods.isDefEq left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx leftV rightV)

/-- The exhausted table changes no state, so it preserves every active finite
suffix domain on its error outcome. -/
theorem methodsOut_activeScopedWFAtOn
    {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (support : RunSupport) (members : Array (KId .anon))
    (calls : CallDomain) (within : calls.Within support) :
    ActiveScopedWFAtOn model layer semantics support members calls
      (methodsOut : Methods .anon) where
  within := within
  whnf _ _ := TcM.WF.throw (fun _ => trivial)
  whnfCore _ _ := TcM.WF.throw (fun _ => trivial)
  whnfMode _ _ := TcM.WF.throw (fun _ => trivial)
  whnfCoreFlags _ _ := TcM.WF.throw (fun _ => trivial)
  infer _ _ := TcM.WF.throw (fun _ => trivial)
  isDefEq _ _ _ := TcM.WF.throw (fun _ => trivial)

end Methods

end Ix.Tc
