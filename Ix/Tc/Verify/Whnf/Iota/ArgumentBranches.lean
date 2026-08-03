import Ix.Tc.Verify.Whnf.Iota.Substitution

/-!
# Remaining production iota-argument branches

Substitution identifies transient lambda application with verified beta
substitution.  Production `applyIotaArg` has two other behaviors: transient
non-lambdas are rebuilt directly with `KExpr.mkApp`, while ordinary iota
applications intern that same rebuilt node.

This slice gives both branches exact execution theorems and a shared semantic
application lemma.  The non-transient theorem records the precise intern-only
state frame and preserves the full WHNF invariant.  These per-argument
contracts are the branch-local inputs needed for the subsequent proof of the
three production application loops.
-/

namespace Ix.Tc

/-- Every expression shape that bypasses transient beta in `applyIotaArg`.
Unlike `WhnfCoreNonLambda`, this includes `app`: an intermediate recursor RHS
may itself be an application. -/
inductive IotaArgNonLambda : KExpr .anon → Prop
  | var {idx name info} : IotaArgNonLambda (.var idx name info)
  | fvar {id name info} : IotaArgNonLambda (.fvar id name info)
  | sort {u info} : IotaArgNonLambda (.sort u info)
  | const {id us info} : IotaArgNonLambda (.const id us info)
  | app {f arg info} : IotaArgNonLambda (.app f arg info)
  | all {name bi ty body info} : IotaArgNonLambda (.all name bi ty body info)
  | letE {name ty val body nondep info} :
      IotaArgNonLambda (.letE name ty val body nondep info)
  | prj {id field val info} : IotaArgNonLambda (.prj id field val info)
  | nat {value blob info} : IotaArgNonLambda (.nat value blob info)
  | str {value blob info} : IotaArgNonLambda (.str value blob info)

namespace IotaArgNonLambda

/-- Exact transient execution equation for every non-lambda shape. -/
theorem applyIotaArg_true
    {result : KExpr .anon} (h : IotaArgNonLambda result)
    (arg : KExpr .anon) :
    RecM.applyIotaArg result arg true = pure (KExpr.mkApp result arg) := by
  cases h <;> rfl

/-- State-level form of `applyIotaArg_true`: direct rebuilding performs no
monadic effect. -/
theorem applyIotaArg_true_run
    {result : KExpr .anon} (h : IotaArgNonLambda result)
    (arg : KExpr .anon) (methods : Methods .anon) (s : TcState .anon) :
    (RecM.applyIotaArg result arg true).run methods s =
      .ok (KExpr.mkApp result arg) s := by
  rw [h.applyIotaArg_true arg]
  rfl

end IotaArgNonLambda

namespace WhnfMeaning

/-- Rebuilding an application with smart-constructor metadata preserves its
Theory meaning.  Both concrete terms translate to the same typed Theory
application; no address equality is used. -/
theorem appRebuild
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {result arg : KExpr .anon}
    {sourceInfo : ExprInfo .anon}
    {resultV argV A B : Lean4Lean.VExpr}
    (hresultTy : world.venv.HasType uvars Delta.toCtx resultV
      (.forallE A B))
    (hargTy : world.venv.HasType uvars Delta.toCtx argV A)
    (hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      result resultV)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV) :
    WhnfMeaning trProj world uvars Delta
      (.app result arg sourceInfo) (KExpr.mkApp result arg) := by
  have hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app result arg sourceInfo) (.app resultV argV) :=
    .app hresultTy hargTy hresultTr hargTr
  have hrebuilt : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.mkApp result arg) (.app resultV argV) := by
    rw [KExpr.mkApp_shape]
    exact .app hresultTy hargTy hresultTr hargTr
  exact ⟨_, _, hsource, hrebuilt,
    Lean4Lean.VEnv.IsDefEqU.refl
      ⟨_, Lean4Lean.VEnv.HasType.app hresultTy hargTy⟩⟩

end WhnfMeaning

namespace RecM

/-- Transient non-lambda application combines exact production execution
with the semantic smart-constructor rebuild theorem. -/
theorem applyIotaArg_true_nonlam_semantic
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {result arg : KExpr .anon}
    {sourceInfo : ExprInfo .anon}
    (hnonlam : IotaArgNonLambda result)
    (methods : Methods .anon) (s : TcState .anon)
    {resultV argV A B : Lean4Lean.VExpr}
    (hresultTy : world.venv.HasType uvars Delta.toCtx resultV
      (.forallE A B))
    (hargTy : world.venv.HasType uvars Delta.toCtx argV A)
    (hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      result resultV)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV) :
    (RecM.applyIotaArg result arg true).run methods s =
        .ok (KExpr.mkApp result arg) s ∧
      WhnfMeaning trProj world uvars Delta
        (.app result arg sourceInfo) (KExpr.mkApp result arg) :=
  ⟨hnonlam.applyIotaArg_true_run arg methods s,
    WhnfMeaning.appRebuild hresultTy hargTy hresultTr hargTr⟩

/-- Non-transient application is exactly one direct-intern request.  The
finite support premise is deliberately about the rebuilt node production
passes to the intern table. -/
theorem applyIotaArg_false_eval
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {result arg : KExpr .anon}
    {s : TcState .anon}
    (hcollision : support.CollisionFree)
    (hsupport : support (KExpr.mkApp result arg))
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (methods : Methods .anon) :
    ∃ s',
      (RecM.applyIotaArg result arg false).run methods s =
          .ok (KExpr.mkApp result arg) s' ∧
        WhnfStateInv layer semantics trProj world support uvars Delta s' ∧
        InternUpdateFrame s s' := by
  obtain ⟨s', hintern, hI', hframe⟩ :=
    TcM.intern_whnf_eval hcollision hsupport hI
  refine ⟨s', ?_, hI', hframe⟩
  rw [Ix.Tc.RecM.applyIotaArg_false]
  exact hintern

/-- Full non-transient per-argument contract: execution is intern-only, the
WHNF invariant is preserved, and the returned smart application has the
expected Theory meaning. -/
theorem applyIotaArg_false_semantic
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {result arg : KExpr .anon}
    {sourceInfo : ExprInfo .anon} {s : TcState .anon}
    (hcollision : support.CollisionFree)
    (hsupport : support (KExpr.mkApp result arg))
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (methods : Methods .anon)
    {resultV argV A B : Lean4Lean.VExpr}
    (hresultTy : world.venv.HasType uvars Delta.toCtx resultV
      (.forallE A B))
    (hargTy : world.venv.HasType uvars Delta.toCtx argV A)
    (hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      result resultV)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV) :
    ∃ s',
      (RecM.applyIotaArg result arg false).run methods s =
          .ok (KExpr.mkApp result arg) s' ∧
        WhnfStateInv layer semantics trProj world support uvars Delta s' ∧
        InternUpdateFrame s s' ∧
        WhnfMeaning trProj world uvars Delta
          (.app result arg sourceInfo) (KExpr.mkApp result arg) := by
  obtain ⟨s', hrun, hI', hframe⟩ :=
    applyIotaArg_false_eval hcollision hsupport hI methods
  exact ⟨s', hrun, hI', hframe,
    WhnfMeaning.appRebuild hresultTy hargTy hresultTr hargTr⟩

end RecM

end Ix.Tc
