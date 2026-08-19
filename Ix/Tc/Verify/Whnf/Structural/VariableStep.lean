import Ix.Tc.Verify.Whnf.Structural.BasicStep

/-!
# Legacy-variable structural-step closure

The legacy `.var` branch reads a de Bruijn let value and rebases it with the
verified lift walker.  BasicStep's fvar branch needed an unchanged-value safety
invariant; legacy zeta instead gets all construction and no-wrap facts from
the exact finite lift request.  `CtxRecon.lookupLetVal_liftBounds` connects
those walker-tight bounds to the semantic context without introducing the
older, stronger `Δ.bvars + val.size` assumption.
-/

namespace Ix.Tc

namespace TcM

/-- An in-range non-let entry makes `lookupLetVal` return `none` without
changing state or invoking the lift walker. -/
theorem lookupLetVal_noLet
    {idx : UInt64} {s : TcState .anon}
    (hidx : idx.toNat < s.ctx.size)
    (hval : s.letVals[s.ctx.size - 1 - idx.toNat]! = none) :
    TcM.lookupLetVal idx s = .ok none s := by
  unfold TcM.lookupLetVal
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only
  rw [if_neg (by omega)]
  rw [hval]
  rfl

end TcM

namespace WhnfMeaning

/-- Legacy zeta meaning from the exact lift-walker arithmetic contract. -/
theorem zetaVar_liftBounds
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {s : TcState .anon} {Delta : KVLCtx}
    {idx : UInt64} {name : Mode.anon.F Name} {info : ExprInfo .anon}
    {ty val : KExpr .anon}
    (hctx : CtxRecon world.venv uvars world.nameOf trProj s Delta)
    (htp : TrProjOK world.venv uvars trProj)
    (hidx : idx.toNat < s.ctx.size)
    (hshift : (idx + 1).toNat = idx.toNat + 1)
    (hty : s.ctx[s.ctx.size - 1 - idx.toNat]? = some ty)
    (hov : s.letVals[s.ctx.size - 1 - idx.toNat]? = some (some val))
    (hcon : KExpr.Constructed val)
    (hcut : (0 : UInt64).toNat + val.size < UInt64.size)
    (hlift : val.lbr.toNat + val.size + (idx + 1).toNat < UInt64.size) :
    WhnfMeaning trProj world uvars Delta (.var idx name info)
      (KExpr.liftSpec val (idx + 1) 0) := by
  obtain ⟨e, A, hfind, hresult⟩ := hctx.lookupLetVal_liftBounds
    world.venvWF.ordered htp hidx hshift hty hov hcon hcut hlift
  have hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.var idx name info) e := .var hfind
  have hwf : Lean4Lean.VExpr.WF world.venv uvars Delta.toCtx e :=
    ⟨A, hctx.wf.find?_wf world.venvWF.ordered hfind⟩
  exact ⟨e, e, hsource, hresult, hwf⟩

end WhnfMeaning

namespace RecM

/-- Every supported legacy variable that resolves to a concrete let value
must have its exact lift request in the finite run census.  Misses need no
request. -/
def LegacyZetaRequestCensus
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (requests : List WalkerRequest) : Prop :=
  ∀ {s : TcState .anon} {idx : UInt64} {name : Mode.anon.F Name}
      {info : ExprInfo .anon} {val : KExpr .anon},
    WhnfStateInv layer semantics trProj world support uvars Delta s →
    support (.var idx name info) →
    idx.toNat < s.ctx.size →
    s.letVals[s.ctx.size - 1 - idx.toNat]! = some val →
    idx.toNat + 1 < UInt64.size ∧
      WalkerRequest.lift val (idx + 1) 0 ∈ requests

/-- Exhaustive legacy-variable step closure.  Source translation proves that
the index is in range; the concrete let-value observation selects either the
state-pure miss or the request-certified zeta step. -/
theorem whnfCoreWithFlagsStep_var_wf
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {idx : UInt64} {name : Mode.anon.F Name}
    {info : ExprInfo .anon} {flags : WhnfFlags}
    {stepError : TcError .anon → TcState .anon → Prop}
    (theory : WhnfTheory trProj world uvars)
    (hcensus : LegacyZetaRequestCensus layer semantics trProj world support
      uvars Delta requests) :
    ∀ s,
      WhnfStep.Source trProj world support uvars Delta id
        (.var idx name info) →
      RecM.WF layer semantics trProj world support uvars Delta s
        (whnfCoreWithFlagsStep (.var idx name info) flags)
        (fun action _ => WhnfStep.Meaning trProj world support uvars Delta id
          (.var idx name info) action)
        stepError := by
  intro s hsource methods hmethods hI
  obtain ⟨hsourceSupport, sourceV, hsourceTr⟩ := hsource
  have hidx : idx.toNat < s.ctx.size := by
    rw [← hI.2.1.bvars_eq]
    cases hsourceTr with
    | var hsourceFind => exact KVLCtx.find?_inl_lt hsourceFind
  let level := s.ctx.size - 1 - idx.toNat
  have hlevel : level < s.ctx.size := by
    dsimp only [level]
    omega
  have hletLevel : level < s.letVals.size := by
    rw [← hI.2.1.size_eq]
    exact hlevel
  let ty := s.ctx[level]
  have hty : s.ctx[level]? = some ty := by
    apply getElem?_eq_some_iff.mpr
    exact ⟨hlevel, rfl⟩
  cases hbang : s.letVals[level]! with
  | none =>
      have hlookup : TcM.lookupLetVal idx s = .ok none s := by
        apply TcM.lookupLetVal_noLet hidx
        simpa only [level] using hbang
      rw [whnfCoreWithFlagsStep_varDone hlookup]
      exact ⟨hI, hsourceSupport,
        WhnfMeaning.refl hsourceTr
          (theory.exprWF hI.2.1 hsourceTr)⟩
  | some val =>
      have hov : s.letVals[level]? = some (some val) := by
        apply getElem?_eq_some_iff.mpr
        refine ⟨hletLevel, ?_⟩
        have hbang' := hbang
        rw [getElem!_pos s.letVals level hletLevel] at hbang'
        exact hbang'
      obtain ⟨hidxNoWrap, hmem⟩ :=
        hcensus hI hsourceSupport hidx
          (by simpa only [level] using hbang)
      have hshift : (idx + 1).toNat = idx.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt hidxNoWrap
      obtain ⟨hcon, hcut, hliftBound⟩ := hrun.requestBounds hmem
      obtain ⟨s', hliftRun, hI', hframe⟩ :=
        hrun.lift_whnf_eval hmem hI
      have hlookup : TcM.lookupLetVal idx s =
          .ok (some (KExpr.liftSpec val (idx + 1) 0)) s' :=
        TcM.lookupLetVal_eval hidx
          (by simpa only [level] using hbang) hliftRun
      rw [whnfCoreWithFlagsStep_varZeta hlookup]
      have hresultSupport :
          support (KExpr.liftSpec val (idx + 1) 0) :=
        hrun.coverage.lift hmem _ (KExpr.LiftReach.spec (idx + 1) val 0)
      have hmeaning := WhnfMeaning.zetaVar_liftBounds
        (name := name) (info := info) hI.2.1
        theory.projections hidx hshift (by simpa only [level] using hty)
        (by simpa only [level] using hov) hcon hcut hliftBound
      exact ⟨hI', hresultSupport, hmeaning⟩

/-- Basic structural cases extended with the complete legacy-variable split. -/
inductive WhnfCoreBasicVar : KExpr .anon → Prop
  | basic {e} : WhnfCoreBasic e → WhnfCoreBasicVar e
  | var {idx name info} : WhnfCoreBasicVar (.var idx name info)

theorem whnfCoreWithFlagsStep_basicVar_wf
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (hlet : LetSubstRequestCensus requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {source : KExpr .anon} {flags : WhnfFlags}
    {stepError : TcError .anon → TcState .anon → Prop}
    (theory : WhnfTheory trProj world uvars)
    (hfvar : FVarZetaSafety layer semantics trProj world support uvars Delta)
    (hvar : LegacyZetaRequestCensus layer semantics trProj world support
      uvars Delta requests)
    (hbasic : WhnfCoreBasicVar source) :
    ∀ s,
      WhnfStep.Source trProj world support uvars Delta id source →
      RecM.WF layer semantics trProj world support uvars Delta s
        (whnfCoreWithFlagsStep source flags)
        (fun action _ => WhnfStep.Meaning trProj world support uvars Delta id
          source action)
        stepError := by
  cases hbasic with
  | basic h =>
      exact whnfCoreWithFlagsStep_basic_wf hrun hlet theory hfvar h
  | var =>
      exact whnfCoreWithFlagsStep_var_wf hrun theory hvar

end RecM
end Ix.Tc
