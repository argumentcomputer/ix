import Ix.Tc.Verify.Whnf.Iota.NatOffset

/-!
# Finite request closure for ordinary iota application

`NatOffset` leaves the selected ordinary-constructor tail behind the state-only
`TryApplyIotaCtorPreserves` boundary.  This slice replaces that whole-helper
premise with the finite requests actually made by production:

* one universe-instantiation request for the selected rule RHS;
* one expression-intern request for each non-transient application; and
* no request at all for transient application, which is state-pure even when
  it performs `substNoIntern`.

The census is indexed by the exact three production argument slices.  Thus a
certificate for a convenient argument order cannot justify the real helper.
-/

namespace Ix.Tc
namespace RecM

/-- Exact non-transient intern requests for one left-to-right iota argument
fold.  The final expression is an index, so the next production segment must
start from the actual result of the preceding segment. -/
inductive IotaArgsInternRequests (requests : List WalkerRequest) :
    KExpr .anon → List (KExpr .anon) → KExpr .anon → Prop
  | nil (result : KExpr .anon) :
      IotaArgsInternRequests requests result [] result
  | cons {result arg final : KExpr .anon}
      {rest : List (KExpr .anon)}
      (request :
        WalkerRequest.internExpr (KExpr.mkApp result arg) ∈ requests)
      (tail : IotaArgsInternRequests requests
        (KExpr.mkApp result arg) rest final) :
      IotaArgsInternRequests requests result (arg :: rest) final

namespace IotaArgsInternRequests

/-- A certified non-transient list fold preserves the complete K1 invariant
and returns its indexed final application. -/
theorem wfList
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    {start final : KExpr .anon} {args : List (KExpr .anon)}
    (h : IotaArgsInternRequests requests start args final)
    (s : TcState .anon) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((args.foldlM (m := RecM .anon)
        (fun result arg => applyIotaArg result arg false) start).run methods)
      (fun result _ => result = final) := by
  induction h generalizing s with
  | nil result =>
      exact TcM.WF.pure (fun _ => rfl)
  | @cons result arg final rest request tail ih =>
      rw [List.foldlM_cons, ReaderT.run_bind]
      apply TcM.WF.bind
        (Q₁ := fun next _ => next = KExpr.mkApp result arg)
      · rw [Ix.Tc.RecM.applyIotaArg_false, ReaderT.run_monadLift]
        exact TcM.WF.mono
          (TcM.intern_whnf_wf hrun.collisionFree
            (hrun.coverage.internExpr request))
          (fun _ _ hpost => hpost.1)
          (fun _ _ _ => trivial)
      · intro next after hnext
        subst next
        exact ih after

/-- Array wrapper matching production's extracted `applyIotaArgs`. -/
theorem wfArray
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    {start final : KExpr .anon} {args : Array (KExpr .anon)}
    (h : IotaArgsInternRequests requests start args.toList final)
    (s : TcState .anon) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((applyIotaArgs start args false).run methods)
      (fun result _ => result = final) := by
  rw [applyIotaArgs_eq_foldlM]
  simpa only [← Array.foldlM_toList] using h.wfList hrun s

end IotaArgsInternRequests

/-- One transient argument application performs no checker-state effect.
This statement intentionally imposes no construction or arithmetic premise:
those are needed for semantic identification, not state preservation. -/
theorem applyIotaArg_true_state_wf
    {I : TcState .anon → Prop} (methods : Methods .anon)
    (result arg : KExpr .anon) (s : TcState .anon) :
    TcM.WF I s ((applyIotaArg result arg true).run methods)
      (fun _ _ => True) := by
  unfold applyIotaArg
  cases result <;> exact TcM.WF.pure (fun _ => trivial)

private theorem applyIotaArgsTrueList_state_wf
    {I : TcState .anon → Prop} (methods : Methods .anon) :
    ∀ (args : List (KExpr .anon)) (start : KExpr .anon)
      (s : TcState .anon),
      TcM.WF I s
        ((args.foldlM (m := RecM .anon)
          (fun result arg => applyIotaArg result arg true) start).run methods)
        (fun _ _ => True)
  | [], start, s => TcM.WF.pure (fun _ => trivial)
  | arg :: rest, start, s => by
      rw [List.foldlM_cons, ReaderT.run_bind]
      apply TcM.WF.bind (applyIotaArg_true_state_wf methods start arg s)
      intro next after _
      exact applyIotaArgsTrueList_state_wf methods rest next after

/-- Every transient production argument fold is state-safe without a request
census because it never enters the intern table. -/
theorem applyIotaArgs_true_state_wf
    {I : TcState .anon → Prop} (methods : Methods .anon)
    (start : KExpr .anon) (args : Array (KExpr .anon))
    (s : TcState .anon) :
    TcM.WF I s ((applyIotaArgs start args true).run methods)
      (fun _ _ => True) := by
  rw [applyIotaArgs_eq_foldlM]
  simpa only [← Array.foldlM_toList] using
    applyIotaArgsTrueList_state_wf methods args.toList start s

/-- Finite request plan for one exact selected production rule.  Successful
universe instantiation determines the starting RHS for the three chained
application plans. -/
structure IotaRuleRequests (requests : List WalkerRequest)
    (rule : RecRule .anon) (recUs : Array (KUniv .anon))
    (recr : IotaInfo .anon) (spine ctorArgs : Array (KExpr .anon))
    (ctorFields : Nat) : Prop where
  instantiate : WalkerRequest.instUniv rule.rhs recUs ∈ requests
  nonTransient : ∀ {rhs},
    KExpr.instantiateUnivParamsSpec rule.rhs recUs = .ok rhs →
    ∃ middle₁ middle₂ final,
      IotaArgsInternRequests requests rhs
          (iotaPrefixArgs recr spine).toList middle₁ ∧
        IotaArgsInternRequests requests middle₁
          (iotaFieldArgs ctorArgs ctorFields).toList middle₂ ∧
        IotaArgsInternRequests requests middle₂
          (iotaTrailingArgs recr spine).toList final

/-- Run-wide finite census at the precise successful rule-selection point.
Guard failures require no plan because production returns before executing
`applyIotaRule`. -/
structure IotaRuleRequestCensus (requests : List WalkerRequest) : Prop where
  selected : ∀ {recr : IotaInfo .anon}
      {recUs : Array (KUniv .anon)}
      {spine ctorArgs : Array (KExpr .anon)}
      {cidx ctorFields : Nat} {rule : RecRule .anon},
    recr.rules[cidx]? = some rule →
    IotaRuleRequests requests rule recUs recr spine ctorArgs ctorFields

/-- State closure of the exact three-segment production rule helper. -/
theorem applyIotaRule_state_wf_of_requests
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    {rule : RecRule .anon} {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool}
    (plan : IotaRuleRequests requests rule recUs recr spine ctorArgs
      ctorFields)
    (s : TcState .anon) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((applyIotaRule rule recUs recr spine ctorArgs ctorFields transient).run
        methods)
      (fun _ _ => True) := by
  unfold applyIotaRule
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.WF.bind
    (TcM.instantiateUnivParams_whnf_wf hrun.collisionFree
      (hrun.coverage.instUniv plan.instantiate))
  intro rhs afterInst hrhs
  cases transient with
  | false =>
      obtain ⟨middle₁, middle₂, final, hfirst, hsecond, hthird⟩ :=
        plan.nonTransient hrhs.1
      rw [ReaderT.run_bind]
      apply TcM.WF.bind (hfirst.wfArray hrun afterInst)
      intro actual₁ afterFirst hactual₁
      subst actual₁
      rw [ReaderT.run_bind]
      apply TcM.WF.bind (hsecond.wfArray hrun afterFirst)
      intro actual₂ afterSecond hactual₂
      subst actual₂
      exact TcM.WF.mono (hthird.wfArray hrun afterSecond)
        (fun _ _ _ => trivial) (fun _ _ _ => trivial)
  | true =>
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (applyIotaArgs_true_state_wf methods rhs
          (iotaPrefixArgs recr spine) afterInst)
      intro middle₁ afterFirst _
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (applyIotaArgs_true_state_wf methods middle₁
          (iotaFieldArgs ctorArgs ctorFields) afterFirst)
      intro middle₂ afterSecond _
      exact applyIotaArgs_true_state_wf methods middle₂
        (iotaTrailingArgs recr spine) afterSecond

/-- Exhaustive rule lookup and both production guards, with the successful
tail discharged from the finite request census. -/
theorem tryApplyIotaCtor_state_wf_of_requests
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : IotaRuleRequestCensus requests)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    (recr : IotaInfo .anon) (recUs : Array (KUniv .anon))
    (spine ctorArgs : Array (KExpr .anon)) (cidx ctorFields : Nat)
    (transient : Bool) (s : TcState .anon) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields
        transient).run methods)
      (fun _ _ => True) := by
  unfold tryApplyIotaCtor
  cases hselected : recr.rules[cidx]? with
  | none =>
      exact TcM.WF.pure (fun _ => trivial)
  | some rule =>
      simp only [pure_bind]
      by_cases hlevels : (recUs.size.toUInt64 != recr.lvls) = true
      · simp only [hlevels, if_true]
        exact TcM.WF.pure (fun _ => trivial)
      · simp only [hlevels, Bool.false_eq_true, if_false]
        by_cases hfields : ctorFields > ctorArgs.size
        · simp only [hfields, if_pos]
          exact TcM.WF.pure (fun _ => trivial)
        · simp only [hfields, if_false]
          rw [ReaderT.run_bind]
          apply TcM.WF.bind
            (applyIotaRule_state_wf_of_requests hrun
              (census.selected hselected) s)
          intro result after _
          exact TcM.WF.pure (fun _ => trivial)

namespace TryApplyIotaCtorPreserves

/-- NatOffset's ordinary-constructor boundary is fully constructed from a finite
run request census. -/
theorem of_requests
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : IotaRuleRequestCensus requests)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} :
    TryApplyIotaCtorPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods := by
  intro recr recUs spine ctorArgs cidx ctorFields transient s
  exact tryApplyIotaCtor_state_wf_of_requests hrun census recr recUs spine
    ctorArgs cidx ctorFields transient s

end TryApplyIotaCtorPreserves

end RecM
end Ix.Tc
