import Ix.Tc.Verify.Whnf.Structural.RecursiveCallbacks

/-!
# Exhaustive projection-step closure

RecursiveCallbacks derives the policy-selected projection-value callback from the smaller
method table.  The remaining helper has its own effects: String expansion
interns a constructor spine and invokes full WHNF, the accelerated layer may
rewrite `Fin.val` through `Decidable.rec`, and constructor lookup may invoke
lazy ingress.

`ProjectionHelper.WF` records exactly that remaining implementation boundary:
for a supported callback result, the actual `tryProjReduce` computation
preserves the fixed K1 state invariant on hits, misses, and errors, and any
successful result remains in finite run support.  The step theorem below then
proves every concrete projection outcome.  Semantic authority for a hit stays
with `InductiveReductionOracle`; a syntax-directed helper execution alone is
not treated as a Theory projection equation.
-/

namespace Ix.Tc
namespace RecM

namespace ProjectionHelper

/-- State and finite-result closure of the exact production projection
helper.  This is intentionally indexed by supported inputs rather than all
raw expressions, so it can be instantiated by a finite execution census. -/
def WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport) : Prop :=
  forall {uvars Delta methods s id field value},
    Methods.WFAt layer semantics trProj world support uvars methods ->
    support value ->
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((tryProjReduce id field value).run methods)
      (fun result _ => match result with
        | none => True
        | some reduced => support reduced)

end ProjectionHelper

/-- Exhaustive local `WhnfStep.WF` contract for a projection.  Callback and
helper errors preserve the invariant and are admitted by the structural
loop's ordinary error relation; a helper miss returns the original source
with reflexive meaning; a helper hit combines finite result support with the
projection oracle's semantic certificate. -/
theorem whnfCoreWithFlagsStep_projection_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    {id : KId .anon} {field : UInt64} {value : KExpr .anon}
    {info : ExprInfo .anon} {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hinputs : WhnfCoreInputSupport support)
    (hhelper : ProjectionHelper.WF layer semantics trProj world support)
    (horacle : InductiveReductionOracle layer semantics trProj world
      support) :
    forall s,
      WhnfStep.Source trProj world support uvars Delta (fun e => e)
        (KExpr.prj id field value info) ->
      RecM.WF layer semantics trProj world support uvars Delta s
        (whnfCoreWithFlagsStep (.prj id field value info) flags)
        (fun action _ => WhnfStep.Meaning trProj world support uvars Delta
          (fun e => e) (KExpr.prj id field value info) action)
        (fun _ _ => True) := by
  intro s hsource methods hmethods hI
  obtain ⟨hsourceSupport, sourceV, hsourceTr⟩ := hsource
  obtain ⟨valueV, hvalueTr, hcallbackWF⟩ :=
    projectionValueCallback_wf (s := s) (flags := flags) hinputs
      hsourceSupport hsourceTr
  have hcallbackPost := hcallbackWF methods hmethods hI
  match hcallbackRun :
      ((if flags.cheapProj then whnfCoreFlagsRec value flags
        else whnfRec value).run methods s) with
  | .error err s1 =>
      rw [hcallbackRun] at hcallbackPost
      have hwhnf :
          (if flags.cheapProj then
              (whnfCoreFlagsRec value flags).run methods s
            else (whnfRec value).run methods s) = .error err s1 := by
        cases hcheap : flags.cheapProj
        · simpa only [hcheap, Bool.false_eq_true, if_false] using hcallbackRun
        · simpa only [hcheap, if_true] using hcallbackRun
      rw [whnfCoreWithFlagsStep_projectionWhnfError hwhnf]
      exact ⟨hcallbackPost.1, trivial⟩
  | .ok wvalue s1 =>
      rw [hcallbackRun] at hcallbackPost
      have hwhnf :
          (if flags.cheapProj then
              (whnfCoreFlagsRec value flags).run methods s
            else (whnfRec value).run methods s) = .ok wvalue s1 := by
        cases hcheap : flags.cheapProj
        · simpa only [hcheap, Bool.false_eq_true, if_false] using hcallbackRun
        · simpa only [hcheap, if_true] using hcallbackRun
      have hhelperPost :=
        hhelper (id := id) (field := field) hmethods
          hcallbackPost.2.1 hcallbackPost.1
      match hreduce : (tryProjReduce id field wvalue).run methods s1 with
      | .error err s2 =>
          rw [hreduce] at hhelperPost
          rw [whnfCoreWithFlagsStep_projectionReduceError hwhnf hreduce]
          exact ⟨hhelperPost.1, trivial⟩
      | .ok none s2 =>
          rw [hreduce] at hhelperPost
          rw [whnfCoreWithFlagsStep_projectionDone hwhnf hreduce]
          exact ⟨hhelperPost.1, hsourceSupport,
            WhnfMeaning.refl hsourceTr
              (theory.exprWF hI.2.1 hsourceTr)⟩
      | .ok (some result) s2 =>
          rw [hreduce] at hhelperPost
          have hsemantic :=
            horacle.projection hmethods hsourceTr hI hwhnf hreduce
          rw [whnfCoreWithFlagsStep_projection hwhnf hreduce]
          exact ⟨hsemantic.1, hhelperPost.2, hsemantic.2⟩

/-- VariableStep's basic/legacy cases extended with the complete projection split. -/
inductive WhnfCoreBasicVarProjection : KExpr .anon -> Prop
  | basicVar {e} :
      WhnfCoreBasicVar e -> WhnfCoreBasicVarProjection e
  | projection {id field value info} :
      WhnfCoreBasicVarProjection (.prj id field value info)

theorem whnfCoreWithFlagsStep_basicVarProjection_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (hlet : LetSubstRequestCensus requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {source : KExpr .anon} {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hfvar : FVarZetaSafety layer semantics trProj world support uvars Delta)
    (hvar : LegacyZetaRequestCensus layer semantics trProj world support
      uvars Delta requests)
    (hinputs : WhnfCoreInputSupport support)
    (hhelper : ProjectionHelper.WF layer semantics trProj world support)
    (horacle : InductiveReductionOracle layer semantics trProj world support)
    (hcase : WhnfCoreBasicVarProjection source) :
    forall s,
      WhnfStep.Source trProj world support uvars Delta id source ->
      RecM.WF layer semantics trProj world support uvars Delta s
        (whnfCoreWithFlagsStep source flags)
        (fun action _ => WhnfStep.Meaning trProj world support uvars Delta id
          source action)
        (fun _ _ => True) := by
  cases hcase with
  | basicVar hbasic =>
      exact whnfCoreWithFlagsStep_basicVar_wf hrun hlet theory hfvar hvar
        hbasic
  | projection =>
      exact whnfCoreWithFlagsStep_projection_wf theory hinputs hhelper
        horacle

end RecM
end Ix.Tc
