import Ix.Tc.Verify.Whnf.StructEta.RebuildRequests

/-!
# Finite request closure for K-synthesis

The positive K branch builds a constructor application before ordinary iota
processing.  Its generated syntax is finite and completely determined by the
selected constructor, normalized major-type spine, and parameter count.  This
slice packages those exact intern requests and composes the remaining
stateful prefix:

* optional infer-only and WHNF callbacks;
* lazy recursor/inductive catalog reads;
* the bounded major-inductive scan;
* both K-synthesis statistics updates; and
* the final, uncaught DefEq callback.

The last item remains an explicit callback authority because its inputs need
finite support and structural translations before `Methods.WF.isDefEq` can
instantiate it.  No catalog, walker, or generated-expression effect remains
abstract.
-/

namespace Ix.Tc
namespace RecM

/-- State-only contract for the actual DefEq back-edge, including production's
dispatch-depth entry and balanced exit on both success and error. -/
def IsDefEqCallbackPreserves (I : TcState .anon → Prop)
    (methods : Methods .anon) : Prop :=
  ∀ a b s,
    TcM.WF I s ((callIsDefEq a b).run methods) (fun _ _ => True)

/-- Entering an instrumented predecessor-table dispatch changes only the
operational depth counter.  Exhaustion throws before the write, so both
outcomes preserve the complete fixed-world invariant. -/
theorem enterDispatch_whnf_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (enterDispatch (m := .anon)) (fun _ _ => True) := by
  unfold enterDispatch
  apply TcM.WF.bind
    (Q₁ := fun observed after => observed = s ∧ after = s)
    (TcM.WF.get fun _ => ⟨rfl, rfl⟩)
  intro observed after hread
  rcases hread with ⟨rfl, rfl⟩
  simp only
  split
  · exact TcM.WF.throw (fun _ => trivial)
  · apply TcM.WF.set
    · intro hI
      exact hI.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl rfl
    · exact fun _ => trivial

/-- The balanced dispatch exit is likewise pure operational bookkeeping. -/
theorem exitDispatch_whnf_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (exitDispatch (m := .anon)) (fun _ _ => True) := by
  unfold exitDispatch modify
  exact TcM.WF.modifyGet
    (fun hI => hI.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl rfl)
    (fun _ => trivial)

/-- At certified inputs, the production `callIsDefEq` wrapper is constructed
directly from the predecessor table's semantic field.  The `finally` exit
runs after both callback outcomes and cannot erase partial callback state. -/
theorem callIsDefEq_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    {a b : KExpr .anon} {va vb : Lean4Lean.VExpr}
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv uvars world.nameOf trProj Delta b vb)
    {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((callIsDefEq a b).run methods)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx va vb) := by
  unfold callIsDefEq
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.WF.bind enterDispatch_whnf_wf
  intro _ afterEnter _
  change TcM.WF
    (WhnfStateInv layer semantics trProj world support uvars Delta)
    afterEnter
    (tryFinally (methods.isDefEq a b) (exitDispatch (m := .anon)))
    (fun answer _ => answer = true →
      world.venv.IsDefEqU uvars Delta.toCtx va vb)
  apply TcM.WF.tryFinally_const
  · exact hmethods.isDefEq haSupport hbSupport ha hb
  · intro after
    exact exitDispatch_whnf_wf

/-- Exact finite requests made while constructing one K-synthesis candidate.
The nested extract is the literal input observed by `FinishAppRequests.eval`
for production's `finishAppResult ... 0` call. -/
structure KSynthCandidateRequests (requests : List WalkerRequest)
    (ctorId : KId .anon) (tyUs : Array (KUniv .anon))
    (tyArgs : Array (KExpr .anon)) (params : Nat) : Type where
  ctorHead :
    WalkerRequest.internExpr (KExpr.mkConst ctorId tyUs) ∈ requests
  ctorApp : KExpr .anon
  ctorApps :
    FinishAppRequests requests
      ((tyArgs.extract 0 (min params tyArgs.size)).extract 0
        (tyArgs.extract 0 (min params tyArgs.size)).size).toList
      (KExpr.mkConst ctorId tyUs) ctorApp

/-- Run-wide census for every candidate that a loaded inductive may select. -/
structure KSynthCandidateRequestCensus
    (requests : List WalkerRequest) : Type where
  plan : ∀ (ctorId : KId .anon) (tyUs : Array (KUniv .anon))
      (tyArgs : Array (KExpr .anon)) (params : Nat),
    KSynthCandidateRequests requests ctorId tyUs tyArgs params

/-- Exact semantic input retained for one generated K-synthesis candidate.

The finite request plan determines the raw constructor application.  This
record adds only the structural translations needed to instantiate the
predecessor table's `infer` and `isDefEq` fields at that concrete candidate;
it is deliberately indexed by the selected plan rather than quantifying over
arbitrary callback inputs. -/
def KSynthCandidateInputs
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx)
    {requests : List WalkerRequest} {ctorId : KId .anon}
    {tyUs : Array (KUniv .anon)} {tyArgs : Array (KExpr .anon)}
    {params : Nat}
    (plan : KSynthCandidateRequests requests ctorId tyUs tyArgs params)
    (majorTyW : KExpr .anon) : Prop :=
  ∃ majorTyWV ctorAppV : Lean4Lean.VExpr,
    support majorTyW ∧
      TrKExprS world.venv uvars world.nameOf trProj Delta
        majorTyW majorTyWV ∧
      TrKExprS world.venv uvars world.nameOf trProj Delta
        plan.ctorApp ctorAppV

/-- Admission-owned structural translation for the one constructor candidate
actually selected by a successful K-synthesis catalog transaction.

Every premise is tied to production's observed spine, trusted scan result,
address guard, lazy lookup equation, first-constructor selection, and finite
request plan.  This is strictly narrower than an arbitrary inference callback
oracle: it provides no state fact and can be used only to instantiate
`Methods.WF` at the generated expression that production really built. -/
structure KSynthCandidateInputOracle
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  candidate :
    ∀ {uvars : Nat} {Delta : KVLCtx}
      {majorTyW : KExpr .anon} {majorTyWV : Lean4Lean.VExpr}
      {tyHeadId indId ctorId : KId .anon}
      {tyUs : Array (KUniv .anon)} {tyInfo : ExprInfo .anon}
      {tyArgs : Array (KExpr .anon)} {params : Nat}
      {requests : List WalkerRequest}
      {before after : TcState .anon} {entry : KConst .anon}
      (plan : KSynthCandidateRequests requests ctorId tyUs tyArgs params),
    support majorTyW →
    TrKExprS world.venv uvars world.nameOf trProj Delta
      majorTyW majorTyWV →
    majorTyW.collectSpine = (.const tyHeadId tyUs tyInfo, tyArgs) →
    world.trusted indId →
    (tyHeadId.addr != indId.addr) = false →
    TcM.tryGetConst indId before = .ok (some entry) after →
    (match entry with
      | .indc (ctors := ctors) .. => ctors[0]? = some ctorId
      | _ => False) →
    KSynthCandidateInputs trProj world support uvars Delta plan majorTyW

/-- Retain the concrete execution equation selected by either outcome of a
verified `TcM` computation. -/
private theorem wf_with_run_eq
    {I : TcState .anon → Prop} {s : TcState .anon} {x : TcM .anon α}
    {Q : α → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hx : TcM.WF I s x Q E) :
    TcM.WF I s x
      (fun value after => Q value after ∧ x s = .ok value after)
      (fun err after => E err after ∧ x s = .error err after) := by
  intro hI
  have hpost := hx hI
  cases hrun : x s with
  | ok value after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, rfl⟩
  | error err after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, rfl⟩

namespace FinishAppRequests

/-- Hoare wrapper around the exact finite evaluator. -/
theorem state_wf
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    {args : Array (KExpr .anon)} {consumed : Nat}
    {start final : KExpr .anon}
    (h : FinishAppRequests requests
      (args.extract consumed args.size).toList start final)
    (s : TcState .anon) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((finishAppResult start args consumed).run methods)
      (fun result _ => result = final) := by
  intro hI
  obtain ⟨sf, heval, hIf, _⟩ := h.eval hrun hI
  rw [heval]
  exact ⟨hIf, rfl⟩

end FinishAppRequests

/-- Candidate construction preserves the complete K1 invariant from the
finite intern plan plus the two exact callback authorities. -/
theorem verifyKSynthCandidate_state_wf_of_requests
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    (hinfer : InferOnlyCallbackPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods)
    (hdefeq : IsDefEqCallbackPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods)
    {majorTyW : KExpr .anon} {ctorId : KId .anon}
    {tyUs : Array (KUniv .anon)} {tyArgs : Array (KExpr .anon)}
    {params : Nat}
    (plan : KSynthCandidateRequests requests ctorId tyUs tyArgs params)
    (s : TcState .anon) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((verifyKSynthCandidate majorTyW ctorId tyUs tyArgs params).run methods)
      (fun _ _ => True) := by
  unfold verifyKSynthCandidate
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.WF.bind
    (Q₁ := fun result _ => result = KExpr.mkConst ctorId tyUs)
  · exact TcM.WF.mono
      (TcM.intern_whnf_wf hrun.collisionFree
        (hrun.coverage.internExpr plan.ctorHead))
      (fun _ _ hpost => hpost.1)
      (fun _ _ _ => trivial)
  · intro ctorHead afterHead hhead
    subst ctorHead
    rw [ReaderT.run_bind]
    apply TcM.WF.bind (plan.ctorApps.state_wf hrun afterHead)
    intro actualApp afterApps hactual
    subst actualApp
    rw [ReaderT.run_bind]
    apply TcM.WF.bind
      (tryOptional_state_wf (hinfer plan.ctorApp afterApps))
    intro foundTy afterInfer _
    cases foundTy with
    | none =>
        exact TcM.WF.pure (fun _ => trivial)
    | some ctorTy =>
        rw [ReaderT.run_bind, ReaderT.run_monadLift]
        apply TcM.WF.bind
          (TcM.bumpStats_whnf_wf
            (fun st : TcState .anon =>
              { st with kSynthAttempts := st.kSynthAttempts + 1 })
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) (fun _ => rfl) afterInfer)
        intro _ afterAttempt _
        rw [ReaderT.run_bind]
        apply TcM.WF.bind (hdefeq majorTyW ctorTy afterAttempt)
        intro equal afterDefEq _
        cases equal with
        | false =>
            simp only [Bool.not_false, if_true]
            rw [ReaderT.run_bind, ReaderT.run_monadLift]
            apply TcM.WF.bind
              (TcM.bumpStats_whnf_wf
                (fun st : TcState .anon =>
                  { st with kSynthRejects := st.kSynthRejects + 1 })
                (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                (fun _ => rfl) (fun _ => rfl) afterDefEq)
            intro _ afterReject _
            exact TcM.WF.pure (fun _ => trivial)
        | true =>
            exact TcM.WF.pure (fun _ => trivial)

/-- Candidate construction with both predecessor-table callbacks derived at
their exact certified inputs.

Unlike `verifyKSynthCandidate_state_wf_of_requests`, this theorem accepts no
state-only inference or DefEq callback oracle.  The generated constructor
application is covered by the finite request plan, its translation is
supplied by `KSynthCandidateInputs`, successful inference exposes a
structural translation of the returned type, and `callIsDefEq_wf` then
instantiates `Methods.WF.isDefEq` directly. -/
theorem verifyKSynthCandidate_state_wf_of_inputs
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    {majorTyW : KExpr .anon} {ctorId : KId .anon}
    {tyUs : Array (KUniv .anon)} {tyArgs : Array (KExpr .anon)}
    {params : Nat}
    (plan : KSynthCandidateRequests requests ctorId tyUs tyArgs params)
    (inputs : KSynthCandidateInputs trProj world support uvars Delta plan
      majorTyW)
    (s : TcState .anon) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((verifyKSynthCandidate majorTyW ctorId tyUs tyArgs params).run methods)
      (fun result _ =>
        OptionalGeneratedInput trProj world support uvars Delta result) := by
  rcases inputs with
    ⟨majorTyWV, ctorAppV, hmajorTyWSupport, hmajorTyWTr, hctorAppTr⟩
  have hctorHeadSupport :
      support (KExpr.mkConst ctorId tyUs) :=
    hrun.coverage.internExpr plan.ctorHead
  have hctorAppSupport : support plan.ctorApp :=
    plan.ctorApps.support hrun hctorHeadSupport
  unfold verifyKSynthCandidate
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.WF.bind
    (Q₁ := fun result _ => result = KExpr.mkConst ctorId tyUs)
  · exact TcM.WF.mono
      (TcM.intern_whnf_wf hrun.collisionFree
        (hrun.coverage.internExpr plan.ctorHead))
      (fun _ _ hpost => hpost.1)
      (fun _ _ _ => trivial)
  · intro ctorHead afterHead hhead
    subst ctorHead
    rw [ReaderT.run_bind]
    apply TcM.WF.bind (plan.ctorApps.state_wf hrun afterHead)
    intro actualApp afterApps hactual
    subst actualApp
    rw [ReaderT.run_bind]
    apply TcM.WF.bind
      ((tryOptionalInferOnlyRec_wf
        (s := afterApps) hctorAppSupport hctorAppTr) methods hmethods)
    intro foundTy afterInfer hfound
    cases foundTy with
    | none =>
        exact TcM.WF.pure (fun _ => trivial)
    | some ctorTy =>
        obtain ⟨hctorTySupport, ctorTyV, hctorTy, _⟩ := hfound
        obtain ⟨ctorTyStructuralV, hctorTyTr, _⟩ := hctorTy
        rw [ReaderT.run_bind, ReaderT.run_monadLift]
        apply TcM.WF.bind
          (TcM.bumpStats_whnf_wf
            (fun st : TcState .anon =>
              { st with kSynthAttempts := st.kSynthAttempts + 1 })
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
            (fun _ => rfl) (fun _ => rfl) afterInfer)
        intro _ afterAttempt _
        rw [ReaderT.run_bind]
        apply TcM.WF.bind
          (callIsDefEq_wf hmethods hmajorTyWSupport hctorTySupport
            hmajorTyWTr hctorTyTr)
        intro equal afterDefEq _
        cases equal with
        | false =>
            simp only [Bool.not_false, if_true]
            rw [ReaderT.run_bind, ReaderT.run_monadLift]
            apply TcM.WF.bind
              (TcM.bumpStats_whnf_wf
                (fun st : TcState .anon =>
                  { st with kSynthRejects := st.kSynthRejects + 1 })
                (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                (fun _ => rfl) (fun _ => rfl) afterDefEq)
            intro _ afterReject _
            exact TcM.WF.pure (fun _ => trivial)
        | true =>
            exact TcM.WF.pure (fun _ =>
              ⟨ctorAppV, hctorAppSupport, hctorAppTr⟩)

/-- Defensive catalog selection preserves state on mismatch, every lazy
lookup outcome, malformed inductives, and the selected candidate transaction.
-/
theorem selectKSynthCandidate_state_wf_of_requests
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : KSynthCandidateRequestCensus requests)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hinfer : InferOnlyCallbackPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods)
    (hdefeq : IsDefEqCallbackPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods)
    (majorTyW : KExpr .anon) (tyHeadId : KId .anon)
    (tyUs : Array (KUniv .anon)) (tyArgs : Array (KExpr .anon))
    (indId : KId .anon) (params : Nat) (s : TcState .anon) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((selectKSynthCandidate majorTyW tyHeadId tyUs tyArgs indId params).run
        methods)
      (fun _ _ => True) := by
  unfold selectKSynthCandidate
  split
  · exact TcM.WF.pure (fun _ => trivial)
  · simp only [pure_bind]
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    apply TcM.WF.bind (TcM.tryGetConst_wf hfault indId s)
    intro found afterLookup _
    cases found with
    | none =>
        exact TcM.WF.pure (fun _ => trivial)
    | some entry =>
        cases entry <;> simp only
        all_goals try
          exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)
        case indc name levelParams lvls indParams indices isUnsafe block
            memberIdx indTy ctors leanAll =>
          cases hfirst : ctors[0]? with
          | none =>
              exact TcM.WF.pure (fun _ => trivial)
          | some ctorId =>
              simp only
              exact verifyKSynthCandidate_state_wf_of_requests hrun hinfer
                hdefeq (census.plan ctorId tyUs tyArgs params) afterLookup

/-- Defensive catalog selection with the candidate inference and DefEq
callbacks instantiated from `Methods.WF` at the exact selected input. -/
theorem selectKSynthCandidate_state_wf_of_inputs
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : KSynthCandidateRequestCensus requests)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (candidateInputs : KSynthCandidateInputOracle trProj world support)
    {majorTyW : KExpr .anon} {majorTyWV : Lean4Lean.VExpr}
    {tyHeadId : KId .anon} {tyUs : Array (KUniv .anon)}
    {tyInfo : ExprInfo .anon} {tyArgs : Array (KExpr .anon)}
    {indId : KId .anon} {params : Nat}
    (hmajorSupport : support majorTyW)
    (hmajorTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      majorTyW majorTyWV)
    (hspine :
      majorTyW.collectSpine = (.const tyHeadId tyUs tyInfo, tyArgs))
    (htrusted : world.trusted indId)
    (s : TcState .anon) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((selectKSynthCandidate majorTyW tyHeadId tyUs tyArgs indId params).run
        methods)
      (fun result _ =>
        OptionalGeneratedInput trProj world support uvars Delta result) := by
  unfold selectKSynthCandidate
  split
  · exact TcM.WF.pure (fun _ => trivial)
  · rename_i hsame
    simp only [pure_bind]
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    apply TcM.WF.bind
      (Q₁ := fun found after =>
        TcM.tryGetConst indId s = .ok found after)
      (TcM.WF.mono
        (wf_with_run_eq (TcM.tryGetConst_wf hfault indId s))
        (fun _ _ hpost => hpost.2)
        (fun _ _ _ => trivial))
    intro found afterLookup hlookup
    cases found with
    | none =>
        exact TcM.WF.pure (fun _ => trivial)
    | some entry =>
        cases entry <;> simp only
        all_goals try
          exact TcM.WF.pure (fun _ => by
            simp [OptionalGeneratedInput])
        case indc name levelParams lvls indParams indices isUnsafe block
            memberIdx indTy ctors leanAll =>
          cases hfirst : ctors[0]? with
          | none =>
              exact TcM.WF.pure (fun _ => trivial)
          | some ctorId =>
              simp only
              let plan := census.plan ctorId tyUs tyArgs params
              have hselected :
                  (match
                    KConst.indc name levelParams lvls indParams indices
                      isUnsafe block memberIdx indTy ctors leanAll with
                    | .indc (ctors := selected) .. =>
                        selected[0]? = some ctorId
                    | _ => False) := by
                exact hfirst
              have hinputs :=
                candidateInputs.candidate plan hmajorSupport hmajorTr hspine
                  htrusted (by
                    cases hguard :
                        (tyHeadId.addr != indId.addr) with
                    | false => rfl
                    | true => exact False.elim (hsame hguard))
                  hlookup hselected
              exact verifyKSynthCandidate_state_wf_of_inputs hrun hmethods
                plan hinputs afterLookup

/-- The complete K-synthesis helper preserves state through its three caught
probes and the selected finite candidate transaction. -/
theorem synthCtorWhenK_state_wf_of_requests
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : KSynthCandidateRequestCensus requests)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : MajorTelescopeInputSupport support)
    (hrecInputs : StructEtaRecursorInputOracle trProj world support)
    (hfault : ∀ {current : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars current))
    (hreferences : TrustedReferences world support)
    (hinfer : InferOnlyCallbackPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods)
    (hwhnf : WhnfCallbackPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods)
    (hdefeq : IsDefEqCallbackPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods)
    (major : KExpr .anon) (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon))
    (s : TcState .anon) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((synthCtorWhenK major recId recr recUs).run methods)
      (fun _ _ => True) := by
  unfold synthCtorWhenK
  by_cases hlevels : (recUs.size.toUInt64 != recr.lvls) = true
  · simp only [hlevels, if_true]
    exact TcM.WF.pure fun _ => trivial
  · simp only [hlevels, Bool.false_eq_true, if_false]
    rw [ReaderT.run_bind]
    apply TcM.WF.bind (tryOptional_state_wf (hinfer major s))
    intro foundTy afterInfer _
    cases foundTy with
    | none =>
        exact TcM.WF.pure (fun _ => trivial)
    | some majorTy =>
        simp only
        change TcM.WF _ afterInfer
          (EStateM.bind ((tryOptional (whnfRec majorTy)).run methods) _) _
        apply TcM.WF.bind (tryOptional_state_wf (hwhnf majorTy afterInfer))
        intro foundWhnf afterWhnf _
        cases foundWhnf with
        | none =>
            exact TcM.WF.pure (fun _ => trivial)
        | some majorTyW =>
            rcases hspine : majorTyW.collectSpine with ⟨tyHead, tyArgs⟩
            simp only [hspine]
            cases tyHead <;>
              try exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)
            next tyHeadId tyUs info =>
              simp only
              change TcM.WF _ afterWhnf
                (EStateM.bind (TcM.tryGetConst recId) _) _
              apply TcM.WF.bind
                (Q₁ := fun found after =>
                  TcM.tryGetConst recId afterWhnf = .ok found after)
                (TcM.WF.mono
                  (TcM.WF.with_run_eq
                    (TcM.tryGetConst_wf (hfault (current := Delta)) recId
                      afterWhnf))
                  (fun _ _ h => h.2) (fun _ _ _ => trivial))
              intro foundRecursor afterRecursor hlookup
              cases foundRecursor with
              | none =>
                  exact TcM.WF.pure (fun _ => trivial)
              | some recursor =>
                  simp only [pure_bind]
                  change TcM.WF _ afterRecursor
                    (EStateM.bind
                      ((tryOptional (do
                        let recTy ← liftM
                          (TcM.instantiateUnivParams recursor.ty recUs)
                        getMajorInductiveId recTy
                          (recr.params + recr.motives + recr.minors +
                            recr.indices).toUInt64)).run methods) _) _
                  apply TcM.WF.bind (tryOptional_state_wf (by
                    rw [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
                    apply TcM.WF.bind (hrecInputs.instantiate hlookup)
                    intro recTy afterInst hrecTy
                    obtain ⟨hrecSupport, recTyV, hrecTr⟩ := hrecTy
                    exact TcM.WF.mono
                      (getMajorInductiveId_wf hmethods hinputs hfault
                        hreferences
                        (recr.params + recr.motives + recr.minors +
                          recr.indices).toUInt64
                        hrecSupport hrecTr)
                      (fun _ _ _ => trivial) (fun _ _ _ => trivial)))
                  intro foundInd afterScan _
                  cases foundInd with
                  | none =>
                      exact TcM.WF.pure (fun _ => trivial)
                  | some indId =>
                      exact selectKSynthCandidate_state_wf_of_requests
                        hrun census (hfault (current := Delta)) hinfer hdefeq
                        majorTyW tyHeadId tyUs tyArgs indId recr.params afterScan

/-- Complete K-synthesis state closure with its ordinary inference, WHNF, and
final DefEq back-edges derived from the predecessor method table.

Only the bounded recursor-type scan still uses the dedicated support-retaining
WHNF frame; that scan traverses open declaration telescope bodies rather than
an expression structurally translated in the caller's `Delta`. -/
theorem synthCtorWhenK_state_wf_of_inputs
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : KSynthCandidateRequestCensus requests)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : MajorTelescopeInputSupport support)
    (hrecInputs : StructEtaRecursorInputOracle trProj world support)
    (hfault : ∀ {current : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars current))
    (hreferences : TrustedReferences world support)
    (candidateInputs : KSynthCandidateInputOracle trProj world support)
    {major : KExpr .anon} {majorV : Lean4Lean.VExpr}
    (hmajorSupport : support major)
    (hmajorTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      major majorV)
    (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon))
    (s : TcState .anon) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((synthCtorWhenK major recId recr recUs).run methods)
      (fun result _ =>
        OptionalGeneratedInput trProj world support uvars Delta result) := by
  unfold synthCtorWhenK
  by_cases hlevels : (recUs.size.toUInt64 != recr.lvls) = true
  · simp only [hlevels, if_true]
    exact TcM.WF.pure fun _ => trivial
  · simp only [hlevels, Bool.false_eq_true, if_false]
    rw [ReaderT.run_bind]
    apply TcM.WF.bind
      ((tryOptionalInferOnlyRec_wf
        (s := s) hmajorSupport hmajorTr) methods hmethods)
    intro foundTy afterInfer hfoundTy
    cases foundTy with
    | none =>
        exact TcM.WF.pure (fun _ => trivial)
    | some majorTy =>
        simp only
        obtain ⟨hmajorTySupport, majorTyV, hmajorTy, _⟩ := hfoundTy
        obtain ⟨majorTyStructuralV, hmajorTyTr, _⟩ := hmajorTy
        change TcM.WF _ afterInfer
          (EStateM.bind ((tryOptional (whnfRec majorTy)).run methods) _) _
        apply TcM.WF.bind
          ((tryOptionalWhnfRec_wf
            (s := afterInfer) hmajorTySupport hmajorTyTr) methods hmethods)
        intro foundWhnf afterWhnf hfoundWhnf
        cases foundWhnf with
        | none =>
            exact TcM.WF.pure (fun _ => trivial)
        | some majorTyW =>
            obtain ⟨hmajorTyWSupport, majorTyWPost⟩ := hfoundWhnf
            obtain ⟨majorTyWV, hmajorTyWTr, _⟩ := majorTyWPost
            rcases hspine : majorTyW.collectSpine with ⟨tyHead, tyArgs⟩
            simp only [hspine]
            cases tyHead <;>
              try exact TcM.WF.pure (fun _ => by
                simp [OptionalGeneratedInput])
            next tyHeadId tyUs tyInfo =>
              simp only
              change TcM.WF _ afterWhnf
                (EStateM.bind (TcM.tryGetConst recId) _) _
              apply TcM.WF.bind
                (Q₁ := fun found after =>
                  TcM.tryGetConst recId afterWhnf = .ok found after)
                (TcM.WF.mono
                  (TcM.WF.with_run_eq
                    (TcM.tryGetConst_wf (hfault (current := Delta)) recId
                      afterWhnf))
                  (fun _ _ h => h.2) (fun _ _ _ => trivial))
              intro foundRecursor afterRecursor hlookup
              cases foundRecursor with
              | none =>
                  exact TcM.WF.pure (fun _ => trivial)
              | some recursor =>
                  simp only [pure_bind]
                  change TcM.WF _ afterRecursor
                    (EStateM.bind
                      ((tryOptional (do
                        let recTy ← liftM
                          (TcM.instantiateUnivParams recursor.ty recUs)
                        getMajorInductiveId recTy
                          (recr.params + recr.motives + recr.minors +
                            recr.indices).toUInt64)).run methods) _) _
                  apply TcM.WF.bind (tryOptional_fixed_wf (by
                    rw [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
                    apply TcM.WF.bind (hrecInputs.instantiate hlookup)
                    intro recTy afterInst hrecTy
                    obtain ⟨hrecSupport, recTyV, hrecTr⟩ := hrecTy
                    exact getMajorInductiveId_trusted_wf hmethods hinputs hfault
                      hreferences
                      (recr.params + recr.motives + recr.minors +
                        recr.indices).toUInt64
                      hrecSupport hrecTr))
                  intro foundInd afterScan htrusted
                  cases foundInd with
                  | none =>
                      exact TcM.WF.pure (fun _ => trivial)
                  | some indId =>
                      exact selectKSynthCandidate_state_wf_of_inputs
                        hrun census hmethods (hfault (current := Delta))
                        candidateInputs
                        hmajorTyWSupport hmajorTyWTr hspine htrusted
                        afterScan

end RecM
end Ix.Tc
