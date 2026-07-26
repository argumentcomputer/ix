import Ix.Tc.Verify.Support

/-!
# G3b: execution-indexed finite run assumptions

An explicit request list is not evidence that it describes a checker run:
choosing `[]` would make coverage and bounds vacuous. `ExecutionRequests` is
therefore indexed by the actual `TcM` computation *and its concrete initial
state*. Its atomic constructors are the audited interning operations, its
composition constructors follow the actual success/error state transition,
and it deliberately has no constructor for an arbitrary silent computation.

This module intentionally imports no translation/world layer. Statement
skeletons can use its concrete execution and support boundary without
colliding with their temporary translation-relation placeholders.
-/

namespace Ix.Tc

/-- A proof-level decomposition of a `TcM` computation into audited
interning operations. Lists conservatively include all continuation/handler
branches and may be finitely weakened. -/
inductive ExecutionRequests : {α : Type} →
    TcM .anon α → TcState .anon → List WalkerRequest → Prop where
  | pure (s : TcState .anon) (a : α) :
      ExecutionRequests (Pure.pure a : TcM .anon α) s []
  | throw (s : TcState .anon) (err : TcError .anon) :
      ExecutionRequests (throw err : TcM .anon α) s []
  | get (s : TcState .anon) :
      ExecutionRequests (get : TcM .anon (TcState .anon)) s []
  | set (initial target : TcState .anon) :
      ExecutionRequests (set target : TcM .anon PUnit) initial []
  | modifyGet (s : TcState .anon)
      (f : TcState .anon → α × TcState .anon) :
      ExecutionRequests (modifyGet f : TcM .anon α) s []
  | internExpr (s : TcState .anon) (e : KExpr .anon) :
      ExecutionRequests (TcM.intern e) s [.internExpr e]
  | internUniv (s : TcState .anon) (u : KUniv .anon) :
      ExecutionRequests (TcM.internUniv u) s [.internUniv u]
  | lift (s : TcState .anon) (e : KExpr .anon)
      (shift cutoff : UInt64) :
      ExecutionRequests (TcM.runIntern (lift e shift cutoff)) s
        [.lift e shift cutoff]
  | subst (s : TcState .anon) (body arg : KExpr .anon) (depth : UInt64) :
      ExecutionRequests (TcM.runIntern (subst body arg depth)) s
        [.subst body arg depth]
  | simulSubst (s : TcState .anon) (body : KExpr .anon)
      (substs : Array (KExpr .anon)) (depth : UInt64) :
      ExecutionRequests (TcM.runIntern (simulSubst body substs depth)) s
        [.simulSubst body substs depth]
  | instRev (s : TcState .anon) (body : KExpr .anon)
      (fvars : Array (KExpr .anon)) :
      ExecutionRequests (TcM.runIntern (instantiateRev body fvars)) s
        [.instRev body fvars]
  | abstractFVars (s : TcState .anon) (body : KExpr .anon)
      (fvars : Array FVarId) :
      ExecutionRequests (TcM.runIntern (abstractFVars body fvars)) s
        [.abstractFVars body fvars]
  | instUniv (s : TcState .anon) (e : KExpr .anon)
      (us : Array (KUniv .anon)) :
      ExecutionRequests (TcM.instantiateUnivParams e us) s
        [.instUniv e us]
  | bind {s : TcState .anon} {x : TcM .anon α}
      {f : α → TcM .anon β}
      {before after : List WalkerRequest}
      (hx : ExecutionRequests x s before)
      (hf : ∀ a s', x s = .ok a s' →
        ExecutionRequests (f a) s' after) :
      ExecutionRequests (x >>= f) s (before ++ after)
  | tryCatch {s : TcState .anon} {x : TcM .anon α}
      {handler : TcError .anon → TcM .anon α}
      {body caught : List WalkerRequest}
      (hx : ExecutionRequests x s body)
      (hh : ∀ err s', x s = .error err s' →
        ExecutionRequests (handler err) s' caught) :
      ExecutionRequests (EStateM.tryCatch x handler) s (body ++ caught)
  | weaken {s : TcState .anon} {x : TcM .anon α}
      {used planned : List WalkerRequest}
      (hx : ExecutionRequests x s used)
      (hsub : ∀ request, request ∈ used → request ∈ planned) :
      ExecutionRequests x s planned
  | of_eq {s : TcState .anon} {x y : TcM .anon α}
      {requests : List WalkerRequest}
      (hxy : x = y) (hy : ExecutionRequests y s requests) :
      ExecutionRequests x s requests

namespace ExecutionRequests

theorem pure_weaken (s : TcState .anon) (a : α)
    (requests : List WalkerRequest) :
    ExecutionRequests (Pure.pure a : TcM .anon α) s requests :=
  .weaken (.pure s a) (by simp)

theorem throw_weaken (s : TcState .anon) (err : TcError .anon)
    (requests : List WalkerRequest) :
    ExecutionRequests (MonadExcept.throw err : TcM .anon α) s requests :=
  .weaken (ExecutionRequests.throw s err) (by
    intro request h
    simp at h)

end ExecutionRequests

/-- All finite-support assumptions for one concrete computation. The exact
same request-list index occurs in every field. -/
structure RunAssumptions {α : Type} (initial : TcState .anon)
    (program : TcM .anon α) (requests : List WalkerRequest)
    (support : RunSupport) : Prop where
  execution : ExecutionRequests program initial requests
  collisionFree : support.CollisionFree
  coverage : CheckConstSupport initial.env.intern requests support
  bounds : ResourceBounds requests

namespace RunAssumptions

theorem initial {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support) :
    support.CoversIntern initial.env.intern :=
  h.coverage.initial

theorem requestBounds {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {request : WalkerRequest} (hmem : request ∈ requests) :
    request.Bounds :=
  h.bounds.request request hmem

end RunAssumptions

end Ix.Tc
