import Ix.Tc.Verify.Infer.Applications
import Ix.Tc.Verify.Infer.Constants
import Ix.Tc.Verify.Infer.ForallTypes
import Ix.Tc.Verify.Infer.LambdaTypes
import Ix.Tc.Verify.Infer.LeafCases
import Ix.Tc.Verify.Infer.LetTypes
import Ix.Tc.Verify.Infer.Literals
import Ix.Tc.Verify.Infer.ProjectionTypes

/-!
# Uncached inference dispatcher

This module assembles the constructor-local inference proofs into one
exhaustive contract for the production `inferUncached` dispatcher.  The
assembly context contains finite-run support, walker, and catalog resources;
it does not contain a semantic result callback for the dispatcher itself.

The legacy de Bruijn-variable request is indexed by the concrete entry state.
Its resource is consequently guarded by the complete state invariant, unlike
the syntax-only census facts.  This avoids requiring facts about arbitrary
invalid states merely to state recursive inference closure.
-/

namespace Ix.Tc

/-- State-indexed resources for the legacy de Bruijn-variable inference
branch.  The translated source establishes that the lookup is in range; this
resource records the finite walker request and the arithmetic bound needed by
the verified lift. -/
def VariableInferenceResources (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (requests : List WalkerRequest) (uvars : Nat) : Prop :=
  forall {Delta : KVLCtx} {s : TcState .anon} {idx : UInt64}
      {name : Mode.anon.F Name} {info : ExprInfo .anon},
    WhnfStateInv .noAccel semantics trProj world support uvars Delta s ->
    support (.var idx name info) ->
      WalkerRequest.lift
          s.ctx[s.ctx.size - 1 - idx.toNat]! (idx + 1) 0 ∈ requests /\
        Delta.bvars +
          s.ctx[s.ctx.size - 1 - idx.toNat]!.size < UInt64.size

/-- Syntax-directed finite support needed by lambda, forall, let, and sort
inference.  Each premise restricts the obligation to a source already present
in the finite run support. -/
structure SyntaxInferenceResources (support : RunSupport) : Prop where
  sortResult : forall {u : KUniv .anon} {info : ExprInfo .anon},
    support (.sort u info) -> support (KExpr.mkSort (KUniv.mkSucc u))
  lambda : forall {name : Mode.anon.F Name}
      {bi : Mode.anon.F Lean.BinderInfo} {ty body : KExpr .anon}
      {info : ExprInfo .anon},
    support (.lam name bi ty body info) ->
      support ty /\ BinderOpeningResources support name body /\
        LambdaResultSupport support ty
  forallE : forall {name : Mode.anon.F Name}
      {bi : Mode.anon.F Lean.BinderInfo} {ty body : KExpr .anon}
      {info : ExprInfo .anon},
    support (.all name bi ty body info) ->
      support ty /\ BinderOpeningResources support name body
  letE : forall {name : Mode.anon.F Name} {ty val body : KExpr .anon}
      {nondep : Bool} {info : ExprInfo .anon},
    support (.letE name ty val body nondep info) ->
      support ty /\ support val /\ BinderOpeningResources support name body

namespace UncachedInference

/-- All shared resources needed to assemble the concrete constructor proofs.
Projection helper execution is supplied through its concrete context, whose
only semantic boundary is `ProjectionInference.DeclarationOracle`. -/
structure Context
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Type where
  projection : ProjectionInference.Context initial program requests semantics
    trProj world support uvars
  variables : VariableInferenceResources semantics trProj world support
    requests uvars
  fvars : forall Delta : KVLCtx,
    RecM.FVarInferSafety .noAccel semantics trProj world support uvars Delta
  structural : SyntaxInferenceResources support
  references : RecM.TrustedReferences world support
  constTypes : TrustedConstTypes trProj world
  constants : ConstInferCensus world support requests
  literals : LiteralInferContext world support
  applications : ApplicationInferCensus support requests
  cheapBeta : CheapBetaResources support
  abstraction : SingletonAbstractionResources support
  forallResults : ForallResultSupport support
  projectionValues : ProjectionValueSupport support

end UncachedInference

namespace RecM

/-- Exhaustive correctness of the production uncached syntax dispatcher.
Every successful result remains in finite run support and is a Theory type of
the translated source; every partial error preserves the complete checker
invariant through the constructor-local `RecM.WF` proofs. -/
theorem inferUncached_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (context : UncachedInference.Context initial program requests semantics
      trProj world support uvars)
    {Delta : KVLCtx} {s : TcState .anon} {inferOnly : Bool}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferUncached inferCall inferOnly source)
      (fun result _ => support result /\
        InferPost trProj world uvars Delta sourceV result) := by
  cases source with
  | var idx name info =>
      intro methods hmethods hI
      obtain ⟨hrequest, hbound⟩ :=
        context.variables hI hsourceSupport
      exact (RecM.inferUncached_var_wf context.projection.run
        context.projection.theory hsource hrequest hbound) methods hmethods hI
  | fvar fv name info =>
      exact RecM.inferUncached_fvar_wf context.projection.theory
        (context.fvars Delta) hsource
  | sort u info =>
      exact RecM.inferUncached_sort_wf context.projection.theory
        context.projection.run.collisionFree
        (context.structural.sortResult hsourceSupport) hsource
  | const id levels info =>
      exact RecM.inferUncached_const_wf context.projection.run
        context.projection.theory (context.projection.fault Delta)
        context.references context.constTypes context.constants
        hsourceSupport hsource
  | app f a info =>
      exact RecM.inferUncached_app_wf context.projection.run
        context.projection.theory context.projection.whnf
        context.projection.components context.applications hsourceSupport
        hsource
  | lam name bi ty body info =>
      obtain ⟨hty, hbinder, hresult⟩ :=
        context.structural.lambda hsourceSupport
      exact RecM.inferUncached_lam_wf context.projection.run
        context.projection.theory context.projection.whnf
        context.projection.sorts context.cheapBeta context.abstraction
        hresult hty hbinder hsource
  | all name bi ty body info =>
      obtain ⟨hty, hbinder⟩ := context.structural.forallE hsourceSupport
      exact RecM.inferUncached_all_wf context.projection.run
        context.projection.theory context.projection.whnf
        context.projection.sorts context.forallResults hty hbinder hsource
  | letE name ty val body nondep info =>
      obtain ⟨hty, hval, hbinder⟩ := context.structural.letE hsourceSupport
      exact RecM.inferUncached_let_wf context.projection.run
        context.projection.theory context.projection.whnf
        context.projection.sorts context.abstraction
        context.projection.substitution context.cheapBeta hty hval hbinder
        hsource
  | prj structId field val info =>
      exact RecM.inferUncached_prj_wf context.projectionValues
        context.projection.wf hsourceSupport hsource
  | nat n blob info =>
      exact RecM.inferUncached_nat_wf context.literals
        context.projection.theory hsource
  | str value blob info =>
      exact RecM.inferUncached_str_wf context.literals
        context.projection.theory hsource

end RecM

end Ix.Tc
