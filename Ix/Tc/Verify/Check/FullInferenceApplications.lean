import Ix.Tc.Verify.Check.FullInferenceLeaves
import Ix.Tc.Verify.Check.InferencePolicy

/-!
# Full inference for applications

K2 proves application inference from an already typed `TrKExprS` source.
That premise is circular at checker ingress: the application constructor of
`TrKExprS` already says that the function and argument have compatible
types.

This file proves the corresponding K3 branch from `PreTrKExprS`.  Its
callback context deliberately records the additional operational fact needed
by full checking: recursive inference, Pi exposure, and DefEq all restore
`inferOnly = false`, including on partial errors.  The later concrete-knot
proof must construct this context; an arbitrary `Methods.WFAt` table cannot,
because its semantic contract does not constrain that policy bit.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Strong recursive services used while reconstructing a typed translation
from successful full inference.  These are properties of one concrete
smaller method table, rather than consequences of the ordinary K2 method
contract. -/
structure FullInferenceStepContext
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (methods : Methods .anon) : Prop where
  infer : ∀ {Delta : KVLCtx} {s : TcState .anon}
      {source : KExpr .anon} {sourceV : VExpr},
    s.inferOnly = false →
    support source →
    PreTrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      (methods.infer source)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta
            source sourceV result)
      (fun _ after => after.inferOnly = false)
  ensureForall : ∀ {Delta : KVLCtx} {s : TcState .anon}
      {source : KExpr .anon} {sourceV : VExpr},
    s.inferOnly = false →
    support source →
    TrKExpr world.venv uvars world.nameOf trProj Delta source sourceV →
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((RecM.ensureForallDirect source).run methods)
      (fun result after =>
        after.inferOnly = false ∧
          ForallView trProj world support uvars Delta sourceV
            result.1 result.2)
      (fun _ after => after.inferOnly = false)
  ensureSort : ∀ {Delta : KVLCtx} {s : TcState .anon}
      {source : KExpr .anon} {sourceV : VExpr},
    s.inferOnly = false →
    support source →
    TrKExpr world.venv uvars world.nameOf trProj Delta source sourceV →
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((RecM.ensureSortDirect source).run methods)
      (fun result after =>
        after.inferOnly = false ∧
          SortView world support uvars Delta sourceV result)
      (fun _ after => after.inferOnly = false)
  isDefEq : ∀ {Delta : KVLCtx} {s : TcState .anon}
      {left right : KExpr .anon} {leftV rightV : VExpr},
    s.inferOnly = false →
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      (methods.isDefEq left right)
      (fun answer after =>
        after.inferOnly = false ∧
          (answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV))
      (fun _ after => after.inferOnly = false)

namespace FullInferenceStepContext

/-- Assemble the strong K3 callback record from independent semantic proofs
and the outcome-sensitive operational policy frame.  The separation matters:
ordinary K2 soundness does not mention `inferOnly`, while the policy audit
does not claim typing. -/
theorem of_semantic_and_policy
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {methods : Methods .anon}
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars
      methods)
    (hpolicy : methods.PreservesInferOnly)
    (hwhnfPolicy : ∀ source,
      ((RecM.whnf source).run methods).PreservesInferOnly)
    (hinfer : ∀ {Delta : KVLCtx} {s : TcState .anon}
        {source : KExpr .anon} {sourceV : VExpr},
      s.inferOnly = false →
      support source →
      PreTrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
      TcM.WF
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
        (methods.infer source)
        (fun result _ =>
          FullInferPost trProj world support uvars Delta
            source sourceV result))
    (hforall : ∀ {Delta : KVLCtx} {s : TcState .anon}
        {source : KExpr .anon} {sourceV : VExpr},
      support source →
      TrKExpr world.venv uvars world.nameOf trProj Delta source sourceV →
      TcM.WF
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
        ((RecM.ensureForallDirect source).run methods)
        (fun result _ =>
          ForallView trProj world support uvars Delta sourceV
            result.1 result.2))
    (hsort : ∀ {Delta : KVLCtx} {s : TcState .anon}
        {source : KExpr .anon} {sourceV : VExpr},
      support source →
      TrKExpr world.venv uvars world.nameOf trProj Delta source sourceV →
      TcM.WF
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
        ((RecM.ensureSortDirect source).run methods)
        (fun result _ => SortView world support uvars Delta sourceV result)) :
    FullInferenceStepContext semantics trProj world support uvars methods := by
  refine { infer := ?_, ensureForall := ?_, ensureSort := ?_, isDefEq := ?_ }
  · intro Delta s source sourceV hbefore hsourceSupport hsource
    apply TcM.WF.mono
      (TcM.PreservesInferOnly.strengthenWFValue
        (hinfer hbefore hsourceSupport hsource) (hpolicy.infer source) hbefore)
    · intro _ _ post
      exact post
    · intro _ _ post
      exact post.1
  · intro Delta s source sourceV hbefore hsourceSupport hsource
    apply TcM.WF.mono
      (TcM.PreservesInferOnly.strengthenWFValue
        (hforall hsourceSupport hsource)
        (RecM.ensureForallDirect_preservesInferOnly hwhnfPolicy) hbefore)
    · intro _ _ post
      exact post
    · intro _ _ post
      exact post.1
  · intro Delta s source sourceV hbefore hsourceSupport hsource
    apply TcM.WF.mono
      (TcM.PreservesInferOnly.strengthenWFValue
        (hsort hsourceSupport hsource)
        (RecM.ensureSortDirect_preservesInferOnly hwhnfPolicy) hbefore)
    · intro _ _ post
      exact post
    · intro _ _ post
      exact post.1
  · intro Delta s left right leftV rightV hbefore hleftSupport
      hrightSupport hleft hright
    exact hpolicy.isDefEq_full_wf hmethods hbefore hleftSupport
      hrightSupport hleft hright

end FullInferenceStepContext

namespace TcM

/-- The eager-reduction classifier is state-pure and therefore cannot change
the full-inference policy bit on either outcome. -/
private theorem isEagerReduce_full_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    (source : KExpr .anon) (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      (TcM.isEagerReduce source)
      (fun _ after => after = s ∧ after.inferOnly = false)
      (fun _ after => after.inferOnly = false) := by
  intro hI
  rcases hspine : source.collectSpine with ⟨head, args⟩
  cases hsize : args.size != 2 <;>
    cases head <;>
    simp [TcM.isEagerReduce, hspine, hsize, hI, hpolicy]
  change WhnfStateInv .noAccel semantics trProj world support uvars Delta s ∧
    s = s ∧ s.inferOnly = false
  exact ⟨hI, rfl, hpolicy⟩

end TcM

namespace RecM

/-- Toggling the eager-reduction marker leaves the full-inference policy bit
unchanged. -/
private theorem setEagerReduce_full_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    (value : Bool) (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      (modify fun state => { state with eagerReduce := value })
      (fun _ after => after.inferOnly = false)
      (fun _ after => after.inferOnly = false) := by
  exact TcM.WF.modifyGet
    (fun hI => hI.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl rfl)
    (fun _ => hpolicy)

/-- The production mismatch path reads the context depth, throws, and never
reaches its following substitution.  Stating this before running the reader
avoids losing the error-state policy fact while simplifying nested
`ReaderT` binds. -/
private theorem throwApplicationMismatch_full_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {aTy dom : KExpr .anon} {rest : RecM .anon α}
    {Q : α → TcState .anon → Prop}
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars
      methods)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((do
        let read ← (get : RecM .anon (TcState .anon))
        throw (TcError.appTypeMismatch aTy dom read.ctx.size)
        rest).run methods)
      Q (fun _ after => after.inferOnly = false) := by
  have hrec : RecM.WF .noAccel semantics trProj world support uvars Delta s
      (do
        let read ← (get : RecM .anon (TcState .anon))
        throw (TcError.appTypeMismatch aTy dom read.ctx.size)
        rest)
      Q (fun _ after => after.inferOnly = false) := by
    apply RecM.WF.bind
      (Q₁ := fun read state =>
        read = state ∧ state.inferOnly = false)
      (RecM.WF.get fun _ => ⟨rfl, hpolicy⟩)
    intro _ state hread
    apply RecM.WF.bind
      (Q₁ := fun _ _ => False)
      (RecM.WF.throw fun _ => hread.2)
    intro _ _ impossible
    exact impossible.elim
  exact hrec methods hmethods

/-- Semantic reconstruction for a fully checked application.  In contrast
to K2's application lemma, argument compatibility is obtained from the
actual recursive inference and true DefEq result, not from the source
translation premise. -/
private theorem fullApplicationResult
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx}
    (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    {f a cod : KExpr .anon} {info : ExprInfo .anon}
    {fV aV fTyV aTyV aTyCoreV domV codV : VExpr}
    (hfunTr : TrKExprS world.venv uvars world.nameOf trProj Delta f fV)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta a aV)
    (hfTy : world.venv.HasType uvars Delta.toCtx fV fTyV)
    (hview : world.venv.IsDefEqU uvars Delta.toCtx fTyV
      (.forallE domV codV))
    (haTy : world.venv.HasType uvars Delta.toCtx aV aTyV)
    (haTyEq : world.venv.IsDefEqU uvars Delta.toCtx aTyCoreV aTyV)
    (haccepted : world.venv.IsDefEqU uvars Delta.toCtx aTyCoreV domV)
    (hcodTr : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam domV) :: Delta) cod codV)
    (hbounds : WalkerRequest.Bounds (.subst cod a 0)) :
    TrKExprS world.venv uvars world.nameOf trProj Delta
        (.app f a info) (.app fV aV) ∧
      InferPost trProj world uvars Delta (.app fV aV)
        (KExpr.substSpec cod a 0) := by
  have hfunAtForall : world.venv.HasType uvars Delta.toCtx fV
      (.forallE domV codV) :=
    hfTy.defeqU_r world.venvWF hDelta hview
  have hargAtDom : world.venv.HasType uvars Delta.toCtx aV domV :=
    haTy.defeqU_r world.venvWF hDelta <|
      haTyEq.symm.trans world.venvWF hDelta haccepted
  have hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app f a info) (.app fV aV) :=
    .app hfunAtForall hargAtDom hfunTr hargTr
  have hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.substSpec cod a 0) (codV.inst aV) :=
    TrKExprS.instN_lbr world.venvWF.ordered theory.projections.weakN
      theory.projections.instN hbounds.2.1 hargTr hargAtDom hcodTr
        (.zero : KVLCtx.KInstN Delta aV domV 0 0
          ((none, .vlam domV) :: Delta) Delta)
        rfl hbounds.2.2.2.2
  exact ⟨hsource, codV.inst aV,
    hresultTr.trKExpr world.venvWF.ordered theory.literalWF
      theory.projections.wf hDelta,
    Lean4Lean.VEnv.HasType.app hfunAtForall hargAtDom⟩

/-- Execute the final dependent-codomain substitution after a successful
full application check.  `runIntern` cannot throw and its exact frame proves
that `inferOnly` remains false. -/
private theorem finishFullApplication_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {s : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    {f a cod : KExpr .anon}
    {info : ExprInfo .anon}
    {fV aV fTyV aTyV aTyCoreV domV codV : VExpr}
    (hpolicy : s.inferOnly = false)
    (hfunTr : TrKExprS world.venv uvars world.nameOf trProj Delta f fV)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta a aV)
    (hfTy : world.venv.HasType uvars Delta.toCtx fV fTyV)
    (hview : world.venv.IsDefEqU uvars Delta.toCtx fTyV
      (.forallE domV codV))
    (haTy : world.venv.HasType uvars Delta.toCtx aV aTyV)
    (haTyEq : world.venv.IsDefEqU uvars Delta.toCtx aTyCoreV aTyV)
    (haccepted : world.venv.IsDefEqU uvars Delta.toCtx aTyCoreV domV)
    (hcodTr : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam domV) :: Delta) cod codV)
    (hmem : WalkerRequest.subst cod a 0 ∈ requests) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      (TcM.runIntern (subst cod a 0))
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta
            (.app f a info) (.app fV aV) result)
      (fun _ after => after.inferOnly = false) := by
  intro hI
  obtain ⟨after, hrunSubst, hIafter, hframe⟩ :=
    hrun.subst_whnf_eval hmem hI
  rw [hrunSubst]
  have hpolicyAfter : after.inferOnly = false := by
    have hsame : after.inferOnly = s.inferOnly := by
      simpa [InternUpdateFrame] using congrArg TcState.inferOnly hframe
    exact hsame.trans hpolicy
  have hsemantic := fullApplicationResult (info := info) theory
    hIafter.2.1.wf
    hfunTr hargTr hfTy hview haTy haTyEq haccepted hcodTr
    (hrun.requestBounds hmem)
  have hresultSupport : support (KExpr.substSpec cod a 0) :=
    hrun.coverage.subst hmem _ (KExpr.SubstReach.spec a cod 0)
  simp only
  exact ⟨hIafter, hpolicyAfter, hresultSupport, hsemantic.1, hsemantic.2⟩

/-- The full-mode application branch, starting from an untyped structural
translation.  This theorem is deliberately indexed by one concrete smaller
method table and its stronger K3 callback context. -/
theorem inferUncached_app_full_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {methods : Methods .anon} {s : TcState .anon}
    {f a : KExpr .anon} {info : ExprInfo .anon}
    {sourceV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (callbacks : FullInferenceStepContext semantics trProj world support
      uvars methods)
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars
      methods)
    (hcensus : ApplicationInferCensus support requests)
    (hsourceSupport : support (.app f a info))
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta
      (.app f a info) sourceV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((inferUncached inferCall false (.app f a info)).run methods)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta
            (.app f a info) sourceV result)
      (fun _ after => after.inferOnly = false) := by
  cases hsource with
  | app hfunPre hargPre =>
      rename_i fV aV
      obtain ⟨hfunSupport, hargSupport, hsubst⟩ :=
        hcensus hsourceSupport
      unfold inferUncached
      simp only [Bool.not_false, if_true, ReaderT.run_bind,
        ReaderT.run_monadLift, pure_bind]
      apply TcM.WF.bind
        (callbacks.infer hpolicy hfunSupport hfunPre)
      intro fTy afterFun hfunPost
      rcases hfunPost with
        ⟨hpolicyFun, hfTySupport, hfunTr, fTyV, hfTyTr, hfTy⟩
      apply TcM.WF.bind
        (callbacks.ensureForall hpolicyFun hfTySupport hfTyTr)
      intro exposed afterForall hforallPost
      rcases exposed with ⟨dom, cod⟩
      rcases hforallPost with
        ⟨hpolicyForall, domV, codV, hdomSupport, hcodSupport, _, _,
          hdomTr, hcodTr, hview⟩
      apply TcM.WF.bind
        (callbacks.infer hpolicyForall hargSupport hargPre)
      intro aTy afterArg hargPost
      rcases hargPost with
        ⟨hpolicyArg, haTySupport, hargTr, aTyV, haTyTr, haTy⟩
      obtain ⟨aTyCoreV, haTyCoreTr, haTyEq⟩ := haTyTr
      apply TcM.WF.bind
        (TcM.isEagerReduce_full_wf a hpolicyArg)
      intro eager afterEager heager
      rcases heager with ⟨rfl, hpolicyEager⟩
      cases eager with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          apply TcM.WF.bind
            (callbacks.isDefEq hpolicyEager haTySupport hdomSupport
              haTyCoreTr hdomTr)
          intro equal afterEq hequal
          rcases hequal with ⟨hpolicyEq, heq⟩
          cases equal with
          | false =>
              simp only [Bool.not_false, if_true]
              exact throwApplicationMismatch_full_wf
                (α := KExpr .anon) (aTy := aTy) (dom := dom)
                (rest := liftM (TcM.runIntern (subst cod a 0)))
                (Q := fun result after =>
                  after.inferOnly = false ∧
                    FullInferPost trProj world support uvars Delta
                      (.app f a info) (.app fV aV) result)
                hmethods hpolicyEq
          | true =>
              simp only [Bool.not_true, Bool.false_eq_true, if_false]
              exact finishFullApplication_wf hrun theory hpolicyEq hfunTr
                hargTr hfTy hview haTy haTyEq (heq rfl) hcodTr
                (hsubst hcodSupport)
      | true =>
          simp only [if_true, ReaderT.run_bind]
          apply TcM.WF.bind
            (setEagerReduce_full_wf true hpolicyEager)
          intro _ afterSet hpolicySet
          apply TcM.WF.bind
            (callbacks.isDefEq hpolicySet haTySupport hdomSupport
              haTyCoreTr hdomTr)
          intro equal afterEq hequal
          rcases hequal with ⟨hpolicyEq, heq⟩
          apply TcM.WF.bind
            (setEagerReduce_full_wf false hpolicyEq)
          intro _ afterReset hpolicyReset
          cases equal with
          | false =>
              simp only [Bool.not_false, if_true, ReaderT.run_bind,
                ReaderT.run_monadLift]
              exact throwApplicationMismatch_full_wf
                (α := KExpr .anon) (aTy := aTy) (dom := dom)
                (rest := liftM (TcM.runIntern (subst cod a 0)))
                (Q := fun result after =>
                  after.inferOnly = false ∧
                    FullInferPost trProj world support uvars Delta
                      (.app f a info) (.app fV aV) result)
                hmethods hpolicyReset
          | true =>
              simp only [Bool.not_true, Bool.false_eq_true, if_false]
              exact finishFullApplication_wf hrun theory hpolicyReset
                hfunTr hargTr hfTy hview haTy haTyEq (heq rfl) hcodTr
                (hsubst hcodSupport)

end RecM

end Ix.Tc
