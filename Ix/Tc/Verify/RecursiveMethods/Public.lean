import Ix.Tc.Verify.RecursiveMethods.CallDomains
import Ix.Tc.Verify.RecursiveMethods.Closure
import Ix.Tc.Verify.RecursiveMethods.ScopedCallDomains

/-!
# Public recursive-method soundness over run-scoped bounded call domains

The production entry points execute one method body over the finite callback
table selected by the caller's `recFuel`.  Their proof certificate therefore
contains call domains only through `recFuel + 1`: depths through `recFuel`
justify the callback table, and the final successor layer justifies the outer
body itself.

`RunSupport` remains the finite collision, cache, state, and result footprint
of the concrete run.  It is deliberately not reused as the input domain of
every recursive method at every depth.  This separation is what permits a
finite run to infer a sort and return its successor sort without demanding an
infinite successor-sort closure.
-/

namespace Ix.Tc

/-- Legacy globally quantified evidence for one public recursive-method run.
New public roots consume `ScopedRecursiveMethodRunContext` below.  This type
remains only so already-proved global-model clients can migrate separately.

`calls n`
describes only method calls possible at table depth `n`; `support` separately
describes all syntax values whose addresses/results occur during the run. -/
structure RecursiveMethodRunContext
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) where
  run : RunAssumptions initial program requests support
  proposition : PropositionClassifierContext trProj world support
  calls : Nat → Methods.CallDomain
  schedule : Methods.CallScheduleAt .noAccel
    (kernelCacheSemantics proposition.model.keys trProj)
    trProj world support proposition.model.keys.uvars calls
    (initial.recFuel.toNat + 1)

namespace RecursiveMethodRunContext

/-- The exact invariant shared by the bounded public adapters. -/
def Inv
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : RecursiveMethodRunContext initial program requests trProj
      world support) (Delta : KVLCtx) : TcState .anon → Prop :=
  WhnfStateInv .noAccel
    (kernelCacheSemantics context.proposition.model.keys trProj)
    trProj world support context.proposition.model.keys.uvars Delta

end RecursiveMethodRunContext

/-- Complete finite-run evidence for one public recursive-method entry.  The
method schedule preserves the concrete state-domain witness carried by the
run-scoped suffix model at every success and partial-error transition. -/
structure ScopedRecursiveMethodRunContext
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) where
  run : RunAssumptions initial program requests support
  model : ScopedKernelSuffixModel trProj world
  calls : Nat → Methods.CallDomain
  schedule : Methods.ScopedCallScheduleAt model .noAccel
    (kernelCacheSemantics model.keys trProj) support calls
    (initial.recFuel.toNat + 1)

namespace ScopedRecursiveMethodRunContext

/-- The checker invariant and finite suffix-state domain shared by all three
public recursive adapters. -/
def Inv
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : ScopedRecursiveMethodRunContext initial program requests
      trProj world support) (Delta : KVLCtx) : TcState .anon → Prop :=
  ScopedWhnfStateInv context.model .noAccel
    (kernelCacheSemantics context.model.keys trProj) support Delta

end ScopedRecursiveMethodRunContext

namespace TcM.whnf

/-- Public full-WHNF soundness from the exact finite successor-layer call
domain used by this run. -/
theorem wf_legacy
    {initial : TcState .anon} {e : KExpr .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : RecursiveMethodRunContext initial (TcM.whnf e) requests
      trProj world support)
    {Delta : KVLCtx} {sourceV : Lean4Lean.VExpr}
    (hcall : (context.calls (initial.recFuel.toNat + 1)).whnf e)
    (hsource : TrKExprS world.venv
      context.proposition.model.keys.uvars world.nameOf trProj Delta e
      sourceV) :
    TcM.WF (context.Inv Delta) initial (TcM.whnf e)
      (fun result _ => support result ∧
        WhnfPost trProj world context.proposition.model.keys.uvars Delta
          sourceV result) := by
  have hnext := context.schedule.nextSelected
  exact hnext.whnf hcall hsource

/-- Public full-WHNF soundness over one finite suffix-state domain. -/
theorem wf
    {initial : TcState .anon} {e : KExpr .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : ScopedRecursiveMethodRunContext initial (TcM.whnf e) requests
      trProj world support)
    {Delta : KVLCtx} {sourceV : Lean4Lean.VExpr}
    (hcall : (context.calls (initial.recFuel.toNat + 1)).whnf e)
    (hsource : TrKExprS world.venv context.model.keys.uvars world.nameOf
      trProj Delta e sourceV) :
    TcM.WF (context.Inv Delta) initial (TcM.whnf e)
      (fun result _ => support result ∧
        WhnfPost trProj world context.model.keys.uvars Delta sourceV
          result) := by
  have hnext := context.schedule.nextSelected
  exact hnext.whnf hcall hsource

end TcM.whnf

namespace TcM.infer

/-- Public inference soundness from the exact finite successor-layer call
domain used by this run. -/
theorem wf_legacy
    {initial : TcState .anon} {e : KExpr .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : RecursiveMethodRunContext initial (TcM.infer e) requests
      trProj world support)
    {Delta : KVLCtx} {sourceV : Lean4Lean.VExpr}
    (hcall : (context.calls (initial.recFuel.toNat + 1)).infer e)
    (hsource : TrKExprS world.venv
      context.proposition.model.keys.uvars world.nameOf trProj Delta e
      sourceV) :
    TcM.WF (context.Inv Delta) initial (TcM.infer e)
      (fun ty _ => support ty ∧
        InferPost trProj world context.proposition.model.keys.uvars Delta
          sourceV ty) := by
  have hnext := context.schedule.nextSelected
  exact hnext.infer hcall hsource

/-- Public inference soundness over one finite suffix-state domain. -/
theorem wf
    {initial : TcState .anon} {e : KExpr .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : ScopedRecursiveMethodRunContext initial (TcM.infer e) requests
      trProj world support)
    {Delta : KVLCtx} {sourceV : Lean4Lean.VExpr}
    (hcall : (context.calls (initial.recFuel.toNat + 1)).infer e)
    (hsource : TrKExprS world.venv context.model.keys.uvars world.nameOf
      trProj Delta e sourceV) :
    TcM.WF (context.Inv Delta) initial (TcM.infer e)
      (fun ty _ => support ty ∧
        InferPost trProj world context.model.keys.uvars Delta sourceV ty) := by
  have hnext := context.schedule.nextSelected
  exact hnext.infer hcall hsource

end TcM.infer

namespace TcM.isDefEq

/-- Public definitional-equality soundness from the exact finite
successor-layer call domain used by this run.  Only a true answer has semantic
content. -/
theorem wf_legacy
    {initial : TcState .anon} {a b : KExpr .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : RecursiveMethodRunContext initial (TcM.isDefEq a b) requests
      trProj world support)
    {Delta : KVLCtx} {va vb : Lean4Lean.VExpr}
    (hcall : (context.calls (initial.recFuel.toNat + 1)).isDefEq a b)
    (ha : TrKExprS world.venv context.proposition.model.keys.uvars
      world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv context.proposition.model.keys.uvars
      world.nameOf trProj Delta b vb) :
    TcM.WF (context.Inv Delta) initial (TcM.isDefEq a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU context.proposition.model.keys.uvars Delta.toCtx
          va vb) := by
  have hnext := context.schedule.nextSelected
  exact hnext.isDefEq hcall ha hb

/-- Public definitional-equality soundness over one finite suffix-state
domain.  Scope preservation holds on both answers and on partial errors. -/
theorem wf
    {initial : TcState .anon} {a b : KExpr .anon}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (context : ScopedRecursiveMethodRunContext initial (TcM.isDefEq a b)
      requests trProj world support)
    {Delta : KVLCtx} {va vb : Lean4Lean.VExpr}
    (hcall : (context.calls (initial.recFuel.toNat + 1)).isDefEq a b)
    (ha : TrKExprS world.venv context.model.keys.uvars world.nameOf trProj
      Delta a va)
    (hb : TrKExprS world.venv context.model.keys.uvars world.nameOf trProj
      Delta b vb) :
    TcM.WF (context.Inv Delta) initial (TcM.isDefEq a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU context.model.keys.uvars Delta.toCtx va vb) := by
  have hnext := context.schedule.nextSelected
  exact hnext.isDefEq hcall ha hb

end TcM.isDefEq

end Ix.Tc
