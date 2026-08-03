import Ix.Tc.Verify.Infer.Callbacks

/-!
# Scoped local contexts for inference

Binder inference temporarily extends the concrete local context.  The
production `withLctxScope` combinator removes that extension on both success
and failure.  This module connects the operational cleanup to the ghost
context used by the verification invariant.
-/

namespace Ix.Tc

@[simp] theorem LocalContext.truncate_size (lctx : LocalContext m) :
    lctx.truncate lctx.size = lctx := by
  simp [LocalContext.truncate, LocalContext.size]

namespace KEnv

/-- A successful checked allocation advances the concrete fvar counter
strictly.  The explicit bound is exactly the guard in `TcM.freshFVarId`. -/
theorem freshFVarId_next (env : KEnv .anon)
    (hbound : env.nextFVarId.toNat + 1 < UInt64.size) :
    env.nextFVarId.toNat < env.freshFVarId.2.nextFVarId.toNat := by
  simp only [KEnv.freshFVarId]
  rw [UInt64.toNat_add]
  have hone : (1 : UInt64).toNat = 1 := by decide
  rw [hone, Nat.mod_eq_of_lt]
  · omega
  · simpa [UInt64.size] using hbound

end KEnv

namespace RunAssumptions

/-- The verified binder-opening walker preserves the complete reducer
invariant.  Its only state effect is intern-table growth. -/
theorem instRev_whnf_wf {alpha : Type} {initial : TcState .anon}
    {program : TcM .anon alpha} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {body : KExpr .anon}
    {fvars : Array (KExpr .anon)}
    (hmem : WalkerRequest.instRev body fvars ∈ requests)
    {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.runIntern (instantiateRev body fvars))
      (fun result after =>
        result = KExpr.instantiateRevSpec body fvars 0 ∧
          InternUpdateFrame s after) :=
  TcM.runIntern_whnf_wf fun _ hwf hsupport =>
    h.instRev_spec hmem hwf hsupport

/-- Executable form of `instRev_whnf_wf`. -/
theorem instRev_whnf_eval {alpha : Type} {initial : TcState .anon}
    {program : TcM .anon alpha} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {body : KExpr .anon}
    {fvars : Array (KExpr .anon)}
    (hmem : WalkerRequest.instRev body fvars ∈ requests)
    {s : TcState .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s) :
    ∃ after,
      TcM.runIntern (instantiateRev body fvars) s =
        .ok (KExpr.instantiateRevSpec body fvars 0) after ∧
      WhnfStateInv layer semantics trProj world support uvars Delta after ∧
      InternUpdateFrame s after :=
  TcM.runIntern_whnf_eval
    (fun _ hwf hsupport => h.instRev_spec hmem hwf hsupport) hI

end RunAssumptions

namespace WhnfStateInv

/-- Advancing only the fvar mint counter preserves the outer semantic state.
The strict bound ensures the counter has not wrapped. -/
theorem advanceFVarCounter
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    (h : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hbound : s.env.nextFVarId.toNat + 1 < UInt64.size) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with env := s.env.freshFVarId.2} := by
  rcases h with ⟨hkernel, hctx, hlayer⟩
  have hnext := s.env.freshFVarId_next hbound
  refine ⟨?_, hctx.of_fields_eq rfl rfl rfl rfl
    (Nat.le_of_lt hnext), ?_⟩
  · exact {
      core := hkernel.core.of_consts_eq rfl (by
        simpa [KEnv.freshFVarId] using hkernel.core.intern)
      internSupport := by
        simpa [KEnv.freshFVarId] using hkernel.internSupport
      caches := by
        intro entry hentry
        apply hkernel.caches
        cases hentry <;> constructor <;> assumption
      equivalences := hkernel.equivalences }
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

/-- Fuse the counter advance, declaration push, and ghost-context extension.
The target kernel invariant is supplied separately because interning the fvar
may grow the intern table between the initial state and the push. -/
theorem openFVar
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {before after : TcState .anon}
    {d : LocalDecl .anon} {vd : Lean4Lean.VLocalDecl}
    {deps : List FVarId}
    (hbefore : WhnfStateInv layer semantics trProj world support uvars
      Delta before)
    (hkernel : KernelStateWF semantics trProj world support after)
    (htr : TrKLocalDecl world.venv uvars world.nameOf trProj Delta d vd)
    (hdeps : deps ⊆ Delta.fvars)
    (hctx : after.ctx = before.ctx)
    (hlet : after.letVals = before.letVals)
    (hnum : after.numLetBindings = before.numLetBindings)
    (hlctx : after.lctx =
      before.lctx.push ⟨before.env.nextFVarId⟩ d)
    (hnext : before.env.nextFVarId.toNat <
      after.env.nextFVarId.toNat)
    (hprims : after.prims = before.prims)
    (hnoAccel : after.noAccel = before.noAccel) :
    WhnfStateInv layer semantics trProj world support uvars
      ((some (⟨before.env.nextFVarId⟩, deps), vd) :: Delta) after := by
  refine ⟨hkernel, hbefore.2.1.openFVar htr hdeps hctx hlet hnum hlctx
    hnext, ?_⟩
  cases layer <;>
    simpa [WhnfLayer.StateOK, hprims, hnoAccel] using hbefore.2.2

/-- Closing one tagged ghost local and truncating the matching concrete local
context preserves the complete reducer state invariant. -/
theorem closeFVar
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {fv : FVarId} {deps : List FVarId}
    {vd : Lean4Lean.VLocalDecl} {saved : Nat}
    (h : WhnfStateInv layer semantics trProj world support uvars
      ((some (fv, deps), vd) :: Delta) s)
    (hsaved : saved = Delta.fvars.length) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with lctx := s.lctx.truncate saved} := by
  rcases h with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, hctx.closeFVar hsaved, ?_⟩
  · exact {
      core := hkernel.core.of_env_eq rfl
      internSupport := hkernel.internSupport
      caches := hkernel.caches
      equivalences := hkernel.equivalences }
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

/-- Restore the concrete local-context depth saved at entry to a one-fvar
scope.  The outer invariant supplies the equality between that concrete
depth and the outer ghost fvar count. -/
theorem closeFVarAtEntry
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {before after : TcState .anon}
    {fv : FVarId} {deps : List FVarId}
    {vd : Lean4Lean.VLocalDecl}
    (hbefore : WhnfStateInv layer semantics trProj world support uvars
      Delta before)
    (hafter : WhnfStateInv layer semantics trProj world support uvars
      ((some (fv, deps), vd) :: Delta) after) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {after with lctx := after.lctx.truncate before.lctx.size} := by
  apply hafter.closeFVar
  simpa only [LocalContext.size] using hbefore.2.1.fvars_length.symm

end WhnfStateInv

namespace TcM

/-- Checked fvar allocation either returns the old counter and advances it
strictly, or reports exhaustion without changing state.  Both outcomes
preserve the outer reducer invariant. -/
theorem freshFVarId_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.freshFVarId (m := .anon))
      (fun fv after =>
        fv = ⟨s.env.nextFVarId⟩ ∧
          after = {s with env := s.env.freshFVarId.2} ∧
          s.env.nextFVarId.toNat < after.env.nextFVarId.toNat)
      (fun err after =>
        err = .other "free-variable id space exhausted" ∧ after = s) := by
  intro hI
  by_cases hbound : s.env.nextFVarId.toNat + 1 < UInt64.size
  · simp only [TcM.freshFVarId, hbound, ↓reduceIte, KEnv.freshFVarId]
    refine ⟨hI.advanceFVarCounter hbound, trivial, trivial, ?_⟩
    exact s.env.freshFVarId_next hbound
  · simp only [TcM.freshFVarId, hbound, ↓reduceIte]
    exact ⟨hI, trivial, trivial⟩

end TcM

namespace RecM

/-- Exact operational equation for `withLctxScope`: the body runs first, then
the local context is restored to its entry length without discarding any
other state changes, regardless of whether the body succeeds or fails. -/
theorem withLctxScope_eq (x : RecM .anon α)
    (methods : Methods .anon) (s : TcState .anon) :
    (withLctxScope x).run methods s =
      match x.run methods s with
      | .ok value after =>
          .ok value {after with lctx := after.lctx.truncate s.lctx.size}
      | .error err after =>
          .error err {after with lctx := after.lctx.truncate s.lctx.size} := by
  unfold withLctxScope
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only
  unfold tryFinally
  change EStateM.map (fun pair : α × PUnit => pair.1)
    (tryFinally' (x.run methods) (fun _ =>
      (modify (fun after : TcState .anon =>
        {after with lctx := after.lctx.truncate s.lctx.size}) :
        TcM .anon PUnit))) s = _
  unfold EStateM.map MonadFinally.tryFinally' EStateM.instMonadFinally
  cases hrun : x.run methods s with
  | ok value after =>
      simp only [hrun]
      rfl
  | error err after =>
      simp only [hrun]
      rfl

end RecM

end Ix.Tc
