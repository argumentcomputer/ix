import Ix.Tc.Verify.Infer.Callbacks

/-!
# Function-type exposure for inference

Application inference first turns the inferred function type into a concrete
Pi.  This module proves that the syntactic fast path and the direct-WHNF
fallback expose the same semantic view, while retaining finite support for
the returned domain and codomain.
-/

namespace Ix.Tc

/-- Finite-support descent needed after a supported Pi is exposed.  Run
support is intentionally not globally constructor-closed. -/
def ForallComponentSupport (support : RunSupport) : Prop :=
  forall {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {dom cod : KExpr .anon} {info : ExprInfo .anon},
    support (.all name bi dom cod info) -> support dom /\ support cod

/-- Semantic result of exposing a concrete Pi.  The final equality connects
the caller's quotient translation of the original inferred type to the exact
structural translations of the returned concrete components. -/
def ForallView (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx)
    (inputV : Lean4Lean.VExpr) (dom cod : KExpr .anon) : Prop :=
  exists domV codV,
    support dom /\ support cod /\
    world.venv.IsType uvars Delta.toCtx domV /\
    world.venv.IsType uvars (domV :: Delta.toCtx) codV /\
    TrKExprS world.venv uvars world.nameOf trProj Delta dom domV /\
    TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam domV) :: Delta) cod codV /\
    world.venv.IsDefEqU uvars Delta.toCtx inputV (.forallE domV codV)

namespace RecM

private theorem ensureForallWhnf_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon} {input : KExpr .anon}
    {inputCoreV inputV : Lean4Lean.VExpr}
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hinputSupport : support input)
    (hinputCore : TrKExprS world.venv uvars world.nameOf trProj Delta input
      inputCoreV)
    (hinputEq : world.venv.IsDefEqU uvars Delta.toCtx inputCoreV inputV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (ensureForallWhnf input)
      (fun result _ => ForallView trProj world support uvars Delta inputV
        result.1 result.2) := by
  unfold ensureForallWhnf
  apply RecM.WF.bind (hwhnf hinputSupport hinputCore)
  intro reduced after hred
  rcases hred with
    ⟨hreducedSupport, reducedV, hreducedTr, hcoreReduced⟩
  cases reduced <;> simp only
  case all name bi dom cod info =>
    apply RecM.WF.pure
    intro hI
    obtain ⟨hdomSupport, hcodSupport⟩ := hcomponents hreducedSupport
    cases hreducedTr with
    | all hdomType hcodType hdomTr hcodTr =>
        exact ⟨_, _, hdomSupport, hcodSupport, hdomType, hcodType,
          hdomTr, hcodTr,
          hinputEq.symm.trans world.venvWF hI.2.1.wf.toCtx
            hcoreReduced⟩
  all_goals
    exact RecM.WF.throw fun _ => trivial

/-- Both production paths through `ensureForallDirect` return a supported
concrete Pi whose structural Theory view is definitionally equal to the
caller's translation of the input type. -/
theorem ensureForallDirect_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon} {input : KExpr .anon}
    {inputV : Lean4Lean.VExpr}
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hinputSupport : support input)
    (hinput : TrKExpr world.venv uvars world.nameOf trProj Delta input
      inputV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (ensureForallDirect input)
      (fun result _ => ForallView trProj world support uvars Delta inputV
        result.1 result.2) := by
  obtain ⟨inputCoreV, hinputCore, hinputEq⟩ := hinput
  cases input <;> simp only [ensureForallDirect]
  case all name bi dom cod info =>
    apply RecM.WF.pure
    intro _
    obtain ⟨hdomSupport, hcodSupport⟩ := hcomponents hinputSupport
    cases hinputCore with
    | all hdomType hcodType hdomTr hcodTr =>
        exact ⟨_, _, hdomSupport, hcodSupport, hdomType, hcodType,
          hdomTr, hcodTr, hinputEq.symm⟩
  all_goals
    exact
      (ensureForallWhnf_wf (s := s) hwhnf hcomponents hinputSupport
        hinputCore hinputEq)

end RecM

end Ix.Tc
