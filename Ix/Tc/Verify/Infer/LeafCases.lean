import Ix.Tc.Verify.Infer.CacheShell

/-!
# Non-recursive inference cases

This module verifies the syntax-directed inference branches that do not call
the recursive inference or definitional-equality methods.  Keeping these
proofs separate makes the semantic boundary explicit: each branch must
produce a supported concrete type together with a Theory typing derivation.
-/

namespace Ix.Tc

namespace TcM

/-- Exact successful execution of the legacy bound-variable lookup once its
array bound and verified lift execution are known. -/
theorem lookupVar_eval {idx : UInt64} {ty result : KExpr .anon}
    {s s' : TcState .anon}
    (hidx : idx.toNat < s.ctx.size)
    (hty : s.ctx[s.ctx.size - 1 - idx.toNat]! = ty)
    (hlift : TcM.runIntern (lift ty (idx + 1) 0) s = .ok result s') :
    TcM.lookupVar idx s = .ok result s' := by
  unfold TcM.lookupVar
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only
  rw [if_neg (by omega)]
  simp only [pure_bind]
  rw [hty]
  exact hlift

end TcM

namespace RecM

/-- Runtime safety required by production's unchanged free-variable type
return.  A declaration type may have been stored at an older mixed-context
depth; closing it over legacy de Bruijn variables is what makes the omitted
lift semantically valid. -/
def FVarInferSafety (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) : Prop :=
  ∀ {s : TcState .anon} {fv : FVarId} {d : LocalDecl .anon},
    WhnfStateInv layer semantics trProj world support uvars Delta s →
    s.lctx.find? fv = some d →
    support d.ty ∧ KExpr.Constructed d.ty ∧ d.ty.lbr = 0 ∧
      Delta.bvars + d.ty.size < UInt64.size

/-- Inferring a sort returns the next sort, preserves the complete checker
invariant, and realizes the Theory's sort typing rule. -/
theorem inferUncached_sort_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {u : KUniv .anon} {info : ExprInfo .anon}
    {sourceV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hresultSupport : support (KExpr.mkSort (KUniv.mkSucc u)))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.sort u info) sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.sort u info))
      (fun ty _ => support ty ∧
        InferPost trProj world uvars Delta sourceV ty) := by
  cases hsource with
  | sort hu =>
      unfold inferUncached
      apply RecM.WF.mono
        (RecM.WF.withInv <| RecM.WF.liftTcM <|
          TcM.intern_whnf_wf hcollision hresultSupport)
      · intro result after hresult
        rcases hresult with ⟨hI, rfl, _⟩
        refine ⟨hresultSupport, ?_⟩
        refine ⟨.sort (KUniv.toVLevel (KUniv.mkSucc u)), ?_, ?_⟩
        · exact (TrKExprS.sort (KUniv.toVLevel_mkSucc_wf hu)).trKExpr
            world.venvWF.ordered theory.literalWF theory.projections.wf
            hI.2.1.wf
        · simpa only [KUniv.toVLevel_mkSucc] using
            (Lean4Lean.VEnv.HasType.sort hu)
      · intro _ _ _
        trivial

/-- Legacy variables are inferred by lifting the stored concrete type to the
current depth.  Context reconciliation identifies that lifted expression
with the variable's Theory type. -/
theorem inferUncached_var_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {idx : UInt64} {name : Mode.anon.F Name}
    {info : ExprInfo .anon} {sourceV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.var idx name info) sourceV)
    (hmem : WalkerRequest.lift
      s.ctx[s.ctx.size - 1 - idx.toNat]! (idx + 1) 0 ∈ requests)
    (hbig : Delta.bvars +
      s.ctx[s.ctx.size - 1 - idx.toNat]!.size < UInt64.size) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.var idx name info))
      (fun ty _ => support ty ∧
        InferPost trProj world uvars Delta sourceV ty) := by
  cases hsource with
  | var hfind =>
      unfold inferUncached
      apply RecM.WF.liftTcM
      intro hI
      have hidx : idx.toNat < s.ctx.size := by
        rw [← hI.2.1.bvars_eq]
        exact KVLCtx.find?_inl_lt hfind
      let level := s.ctx.size - 1 - idx.toNat
      let ty := s.ctx[level]!
      have hlevel : level < s.ctx.size := by
        dsimp only [level]
        omega
      have htyOpt : s.ctx[level]? = some ty := by
        apply getElem?_eq_some_iff.mpr
        exact ⟨hlevel, by simp only [ty, getElem!_pos s.ctx level hlevel]⟩
      have hletLevel : level < s.letVals.size := by
        rw [← hI.2.1.size_eq]
        exact hlevel
      let ov := s.letVals[level]!
      have hov : s.letVals[level]? = some ov := by
        apply getElem?_eq_some_iff.mpr
        exact ⟨hletLevel,
          by simp only [ov, getElem!_pos s.letVals level hletLevel]⟩
      have hmem' : WalkerRequest.lift ty (idx + 1) 0 ∈ requests := by
        simpa only [ty, level] using hmem
      obtain ⟨after, hlift, hIafter, _⟩ :=
        hrun.lift_whnf_eval hmem' hI
      have hlookup : TcM.lookupVar idx s =
          .ok (KExpr.liftSpec ty (idx + 1) 0) after := by
        apply TcM.lookupVar_eval hidx
        · rfl
        · exact hlift
      rw [hlookup]
      refine ⟨hIafter, ?_, ?_⟩
      · exact hrun.coverage.lift hmem' _
          (KExpr.LiftReach.spec (idx + 1) ty 0)
      · have hsz : s.ctx.size < UInt64.size := by
          rw [← hI.2.1.bvars_eq]
          omega
        obtain ⟨sourceV', typeV, hfind', hresult⟩ :=
          hI.2.1.lookupVar world.venvWF.ordered theory.projections
            hidx hsz (by simpa only [level, ty] using htyOpt)
            (by simpa only [level, ov] using hov)
            (by simpa only [ty, level] using hbig)
        rw [hfind] at hfind'
        cases hfind'
        refine ⟨_, ?_,
          hI.2.1.wf.find?_wf world.venvWF.ordered hfind⟩
        exact TrKExprS.trKExpr world.venvWF.ordered theory.literalWF
          theory.projections.wf
          (by simpa only [ty, level] using hresult) hIafter.2.1.wf

/-- A free variable returns its stored declaration type.  The explicit
`FVarInferSafety` premise is the production-specific reason that returning
the type unchanged remains valid in an interleaved bvar/fvar context. -/
theorem inferUncached_fvar_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {fv : FVarId} {name : Mode.anon.F Name}
    {info : ExprInfo .anon} {sourceV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hsafe : FVarInferSafety layer semantics trProj world support uvars
      Delta)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.fvar fv name info) sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.fvar fv name info))
      (fun ty _ => support ty ∧
        InferPost trProj world uvars Delta sourceV ty) := by
  cases hsource with
  | fvar hsourceFind =>
      unfold inferUncached
      apply RecM.WF.bind
        (Q₁ := fun read after => read = s ∧ after = s)
        (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
      intro read after hread
      rcases hread with ⟨rfl, rfl⟩
      cases hfind : after.lctx.find? fv with
      | none =>
          exact RecM.WF.throw fun _ => trivial
      | some d =>
          apply RecM.WF.pure
          intro hI
          obtain ⟨hsupport, hcon, hclosed, hbig⟩ := hsafe hI hfind
          obtain ⟨sourceV', typeV, hfind', htype⟩ :=
            hI.2.1.lctxFindType world.venvWF.ordered theory.projections
              hfind hcon hclosed hbig
          rw [hsourceFind] at hfind'
          cases hfind'
          refine ⟨hsupport, _, ?_,
            hI.2.1.wf.find?_wf world.venvWF.ordered hsourceFind⟩
          exact htype.trKExpr world.venvWF.ordered theory.literalWF
            theory.projections.wf hI.2.1.wf

end RecM

end Ix.Tc
