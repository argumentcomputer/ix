import Ix.Tc.Verify.Check.FullInferenceCache
import Ix.Tc.Verify.Check.RecursiveMethodPolicy
import Ix.Tc.Verify.RecursiveMethods.Closure

/-!
# Full-inference closure of the production recursion knot

K2 closes the ordinary six-field semantic contract from an already typed
source.  K3 needs a stronger contract for the inference field: when the
caller is in full mode, successful inference must construct the typed source
translation from `PreTrKExprS`, and both success and partial errors must
restore full mode.

This module ties that stronger contract through the same finite `methodsN`
approximations used by production.  The induction remains well founded:
one outer `RecM.infer` layer uses only the semantic, operational, and strong
full-inference contracts of its strictly smaller callback table.
-/

namespace Ix.Tc

namespace Methods

/-- Strong K3 contract for the inference field of one fixed method table.
Unlike ordinary K2 inference, this starts from untyped structural ingress and
records the full-mode frame on both outcomes. -/
def FullInferenceWFAt
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (methods : Methods .anon) : Prop :=
  ∀ {Delta : KVLCtx} {s : TcState .anon}
      {source : KExpr .anon} {sourceV : Lean4Lean.VExpr},
    s.inferOnly = false →
    support source →
    PreTrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      (methods.infer source)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta source sourceV
            result)
      (fun _ after => after.inferOnly = false)

end Methods

namespace RecursiveMethodClosureContext

/-- Assemble every resource needed by one full-inference body over a fixed
smaller method table.  Ordinary semantic closure, the independent policy
frame, and the stronger recursive-inference induction hypothesis remain
separate premises. -/
def fullInferenceContext
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (context : RecursiveMethodClosureContext initial program requests support
      proposition eligible)
    (methods : Methods .anon)
    (hmethods : Methods.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars methods)
    (hpolicy : methods.PreservesInferOnly)
    (hfull : Methods.FullInferenceWFAt
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars methods) :
    FullUncachedInference.Context initial program requests
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars methods := by
  let hnextPolicy := Methods.next_preservesInferOnly methods hpolicy
  refine {
    base := context.inferDefEq.inference
    methodSemantics := hmethods
    callbacks := FullInferenceStepContext.of_semantic_and_policy
      hmethods hpolicy hnextPolicy.whnf ?_ ?_ ?_
    uncachedPolicy := ?_
    projectionPolicy := ?_ }
  · intro Delta s source sourceV hbefore hsourceSupport hsource
    apply TcM.WF.mono (hfull hbefore hsourceSupport hsource)
    · intro _ _ post
      exact post.2
    · intro _ _ _
      trivial
  · intro Delta s source sourceV hsourceSupport hsource
    exact
      (RecM.ensureForallDirect_wf
        context.inferDefEq.inference.projection.whnf
        context.inferDefEq.inference.projection.components
        hsourceSupport hsource) methods hmethods
  · intro Delta s source sourceV hsourceSupport hsource
    exact
      (RecM.ensureSortDirect_wf
        context.inferDefEq.inference.projection.whnf
        context.inferDefEq.inference.projection.sorts
        hsourceSupport hsource) methods hmethods
  · intro inferOnly source
    exact RecM.inferUncached_preservesInferOnly_of_whnf methods hpolicy
      hnextPolicy.whnf inferOnly source
  · exact ProjectionInference.preservesInferOnlyAt methods hpolicy
      hnextPolicy.whnf

/-- One unfolded production inference layer satisfies K3 whenever its
strictly smaller callback table satisfies the three independent premises. -/
theorem next_fullInferenceWFAt
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (context : RecursiveMethodClosureContext initial program requests support
      proposition eligible)
    (methods : Methods .anon)
    (hmethods : Methods.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars methods)
    (hpolicy : methods.PreservesInferOnly)
    (hfull : Methods.FullInferenceWFAt
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars methods) :
    Methods.FullInferenceWFAt
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars (Methods.next methods) := by
  intro Delta s source sourceV hbefore hsourceSupport hsource
  simpa [Methods.next] using
    (RecM.infer_full_wf
      (context.fullInferenceContext methods hmethods hpolicy hfull)
      hsourceSupport hsource hbefore)

end RecursiveMethodClosureContext

namespace Methods

/-- The exhausted callback table satisfies the strong contract vacuously:
its inference field throws `maxRecFuel` without changing state. -/
theorem methodsOut_fullInferenceWFAt
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) :
    FullInferenceWFAt semantics trProj world support uvars
      (methodsOut : Methods .anon) := by
  intro Delta s source sourceV hbefore _ _
  exact TcM.WF.throw (fun _ => hbefore)

end Methods

namespace RecursiveMethodClosureContext

/-- Every finite callback table selected by production satisfies the strong
full-inference contract. -/
theorem methodsN_fullInferenceWFAt
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (context : RecursiveMethodClosureContext initial program requests support
      proposition eligible) (depth : Nat) :
    Methods.FullInferenceWFAt
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars
      (Ix.Tc.methodsN (m := .anon) depth) := by
  induction depth with
  | zero =>
      exact Methods.methodsOut_fullInferenceWFAt
        (kernelCacheSemantics proposition.model.keys trProj) trProj world
        support proposition.model.keys.uvars
  | succ depth ih =>
      intro Delta s source sourceV hbefore hsourceSupport hsource
      change TcM.WF
        (WhnfStateInv .noAccel
          (kernelCacheSemantics proposition.model.keys trProj) trProj world
          support proposition.model.keys.uvars Delta) s
        ((Methods.next (Ix.Tc.methodsN depth)).infer source)
        (fun result after =>
          after.inferOnly = false ∧
            FullInferPost trProj world support proposition.model.keys.uvars
              Delta source sourceV result)
        (fun _ after => after.inferOnly = false)
      exact
        (context.next_fullInferenceWFAt (Ix.Tc.methodsN depth)
          (context.methodsN depth)
          (Methods.methodsN_concrete_preservesInferOnly depth) ih)
          hbefore hsourceSupport hsource

/-- The public inference action executes one full body over the finite table
selected from the caller's current recursive fuel. -/
theorem publicInfer_full_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (context : RecursiveMethodClosureContext initial program requests support
      proposition eligible)
    {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hbefore : s.inferOnly = false)
    (hsourceSupport : support source)
    (hsource : PreTrKExprS world.venv proposition.model.keys.uvars
      world.nameOf trProj Delta source sourceV) :
    TcM.WF
      (WhnfStateInv .noAccel
        (kernelCacheSemantics proposition.model.keys trProj) trProj world
        support proposition.model.keys.uvars Delta) s
      (TcM.infer source)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support proposition.model.keys.uvars
            Delta source sourceV result)
      (fun _ after => after.inferOnly = false) := by
  let methods := Ix.Tc.methodsN (m := .anon) s.recFuel.toNat
  have hmethods : Methods.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars methods :=
    context.methodsN s.recFuel.toNat
  have hpolicy : methods.PreservesInferOnly :=
    Methods.methodsN_concrete_preservesInferOnly s.recFuel.toNat
  have hfull : Methods.FullInferenceWFAt
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars methods :=
    context.methodsN_fullInferenceWFAt s.recFuel.toNat
  exact
    (RecM.infer_full_wf
      (context.fullInferenceContext methods hmethods hpolicy hfull)
      hsourceSupport hsource hbefore)

end RecursiveMethodClosureContext

end Ix.Tc
