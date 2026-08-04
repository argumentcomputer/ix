import Ix.Tc.Verify.Support

/-!
# G3b: execution-indexed finite run assumptions

An explicit request list is not evidence that it describes a checker run:
choosing `[]` would make coverage and bounds vacuous. `ExecutionRequests` is
therefore indexed by the actual `TcM` computation *and its concrete initial
state*. Its atomic constructors are the audited interning operations, its
composition constructors follow the actual success/error state transition,
and its silent constructors (`set`, `modifyGet`) each require the state
transition to preserve the intern table. The resulting guarantee: every
constructor path that changes the intern table records a request, so a
certificate confines the run's interning to the audited operations in its
request list, and a `[]`-certificate exists only for runs that leave the
intern table untouched. Reads, cache writes, fuel, and scratch state stay
silent by design — their obligations are carried by the Hoare layer
(Verify/Monad.lean, cache provenance in Verify/Cache.lean), not by request
coverage.

This module intentionally imports no translation/world layer. Statement
skeletons can use its concrete execution and support boundary without
colliding with their temporary translation-relation placeholders.
-/

namespace Ix.Tc

/-- A proof-level decomposition of a `TcM` computation into audited
interning operations. Lists conservatively include all continuation/handler
branches and may be finitely weakened. Silent state transitions are
admissible only when they preserve the intern table, so the request list is
an upper bound on the run's interning. -/
inductive ExecutionRequests : {α : Type} →
    TcM .anon α → TcState .anon → List WalkerRequest → Prop where
  | pure (s : TcState .anon) (a : α) :
      ExecutionRequests (Pure.pure a : TcM .anon α) s []
  | throw (s : TcState .anon) (err : TcError .anon) :
      ExecutionRequests (throw err : TcM .anon α) s []
  | get (s : TcState .anon) :
      ExecutionRequests (get : TcM .anon (TcState .anon)) s []
  | set (initial target : TcState .anon)
      (hintern : target.env.intern = initial.env.intern) :
      ExecutionRequests (set target : TcM .anon PUnit) initial []
  | modifyGet (s : TcState .anon)
      (f : TcState .anon → α × TcState .anon)
      (hintern : (f s).2.env.intern = s.env.intern) :
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
  | cheapBeta (s : TcState .anon) (e : KExpr .anon) :
      ExecutionRequests (TcM.runIntern (cheapBetaReduce e)) s
        [.cheapBeta e]
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
  | runRec {s : TcState .anon} {x : RecM .anon α}
      {requests : List WalkerRequest}
      (hx : ExecutionRequests
        (x.run (methodsN s.recFuel.toNat)) s requests) :
      ExecutionRequests (TcM.runRec x) s requests
  | isolateCheckErrors {s : TcState .anon} {x : TcM .anon α}
      {requests : List WalkerRequest}
      (hx : ExecutionRequests x s requests) :
      ExecutionRequests (TcM.isolateCheckErrors x) s requests
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

/-- Ordinary state modification is a silent execution step when its exact
state transformer leaves the intern table unchanged. -/
theorem modify (s : TcState .anon) (f : TcState .anon → TcState .anon)
    (hintern : (f s).env.intern = s.env.intern) :
    ExecutionRequests (modify f : TcM .anon Unit) s [] := by
  exact .of_eq (by rfl)
    (.modifyGet s (fun state => (PUnit.unit, f state)) hintern)

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

/-- The non-laundering guarantee, `[]` case: a certificate with an empty
request list forces the run to leave the intern table untouched on both
outcomes.  Silent constructors preserve the table by hypothesis, atomic
constructors record a request, and composition follows the actual state
transitions, so no intern-extending computation admits an empty
certificate. -/
theorem intern_eq_of_nil {α : Type} {x : TcM .anon α}
    {s : TcState .anon} {requests : List WalkerRequest}
    (h : ExecutionRequests x s requests) (hnil : requests = []) :
    match x s with
    | .ok _ s' => s'.env.intern = s.env.intern
    | .error _ s' => s'.env.intern = s.env.intern := by
  induction h with
  | pure s a => exact rfl
  | throw s err => exact rfl
  | get s => exact rfl
  | set initial target hintern => exact hintern
  | modifyGet s f hintern => exact hintern
  | internExpr | internUniv | lift | subst | simulSubst | instRev |
      abstractFVars | instUniv | cheapBeta =>
    exact absurd hnil (by simp)
  | bind hx hf ihx ihf =>
    rename_i s x f before after
    obtain ⟨hbefore, hafter⟩ := List.append_eq_nil_iff.mp hnil
    have hx' := ihx hbefore
    show (match EStateM.bind x f s with
      | .ok _ s' => s'.env.intern = s.env.intern
      | .error _ s' => s'.env.intern = s.env.intern)
    unfold EStateM.bind
    match hxs : x s with
    | .ok a s₁ =>
      simp only [hxs] at hx'
      have hf' := ihf a s₁ hxs hafter
      show (match f a s₁ with
        | .ok _ s' => s'.env.intern = s.env.intern
        | .error _ s' => s'.env.intern = s.env.intern)
      match hfs : f a s₁ with
      | .ok b s₂ =>
        simp only [hfs] at hf'
        exact hf'.trans hx'
      | .error err s₂ =>
        simp only [hfs] at hf'
        exact hf'.trans hx'
    | .error err s₁ =>
      simp only [hxs] at hx'
      exact hx'
  | tryCatch hx hh ihx ihh =>
    rename_i s x handler body caught
    obtain ⟨hbody, hcaught⟩ := List.append_eq_nil_iff.mp hnil
    have hx' := ihx hbody
    show (match EStateM.tryCatch x handler s with
      | .ok _ s' => s'.env.intern = s.env.intern
      | .error _ s' => s'.env.intern = s.env.intern)
    unfold EStateM.tryCatch
    match hxs : x s with
    | .ok a s₁ =>
      simp only [hxs] at hx'
      exact hx'
    | .error err s₁ =>
      simp only [hxs] at hx'
      have hh' := ihh err s₁ hxs hcaught
      show (match handler err s₁ with
        | .ok _ s' => s'.env.intern = s.env.intern
        | .error _ s' => s'.env.intern = s.env.intern)
      match hhs : handler err s₁ with
      | .ok b s₂ =>
        simp only [hhs] at hh'
        exact hh'.trans hx'
      | .error err' s₂ =>
        simp only [hhs] at hh'
        exact hh'.trans hx'
  | runRec hx ihx =>
    simpa [TcM.runRec] using ihx hnil
  | isolateCheckErrors hx ihx =>
    rename_i s x requests
    have hx' := ihx hnil
    unfold TcM.isolateCheckErrors
    match hxs : x s with
    | .ok a s' =>
      simp only [hxs] at hx' ⊢
      exact hx'
    | .error err s' =>
      simp only [hxs] at hx' ⊢
      exact hx'
  | weaken hx hsub ihx =>
    subst hnil
    exact ihx (List.eq_nil_iff_forall_not_mem.mpr
      fun request hmem => by simpa using hsub request hmem)
  | of_eq hxy hy ihy =>
    subst hxy
    exact ihy hnil

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
