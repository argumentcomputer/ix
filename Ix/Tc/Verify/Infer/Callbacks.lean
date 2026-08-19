import Ix.Tc.Verify.Infer.Literals

/-!
# Inference callback contracts

These adapters expose the three recursive services used by the uncached
inference dispatcher: predecessor-layer inference, predecessor-layer DefEq,
and the already-closed direct WHNF implementation used by `ensureSortDirect`
and `ensureForallDirect`.
-/

namespace Ix.Tc

namespace DirectWhnf

/-- Semantic contract for the direct `RecM.whnf` body at one universe count.
K1's fixed-universe closure constructs this contract when K2 assembles the
joint layer. -/
def WFAt (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  forall {Delta s source sourceV},
    support source ->
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV ->
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (RecM.whnf source)
      (fun result _ => support result /\
        WhnfPost trProj world uvars Delta sourceV result)

end DirectWhnf

namespace RecM

/-- The ordinary recursive inference edge is exactly the predecessor
method-table field. -/
theorem inferCall_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsource : support source)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inferCall source)
      (fun ty _ => support ty /\
        InferPost trProj world uvars Delta sourceV ty) := by
  intro methods hmethods
  exact hmethods.infer hsource htr

/-- The ordinary recursive DefEq edge is exactly the predecessor table's
soundness contract. -/
theorem isDefEqCall_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {a b : KExpr .anon} {va vb : Lean4Lean.VExpr}
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv uvars world.nameOf trProj Delta b vb) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (isDefEqCall a b)
      (fun answer _ => answer = true ->
        world.venv.IsDefEqU uvars Delta.toCtx va vb) := by
  intro methods hmethods
  exact hmethods.isDefEq haSupport hbSupport ha hb

end RecM

end Ix.Tc
