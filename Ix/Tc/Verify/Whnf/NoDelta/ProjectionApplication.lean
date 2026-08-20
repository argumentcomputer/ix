import Ix.Tc.Verify.Whnf.Structural.Reducer

/-!
# Projection-application no-delta field

The first reducer after structural WHNF recognizes an application whose
collected head is a projection.  It normalizes the projected value, runs the
ordinary projection helper, and then rebuilds the complete trailing
application spine.

This slice keeps those three effects separate.  The recursive callback and
projection helper preserve every partial state; the inductive projection
boundary supplies meaning for the changed head; and the finite application
census certifies the exact left-to-right suffix rebuilt by production.
-/

namespace Ix.Tc
namespace RecM

/-! ## Exact raw-helper equations -/

theorem tryProjAppReduce_empty
    {methods : Methods .anon} {s : TcState .anon}
    {source head : KExpr .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags}
    (hspine : source.collectSpine = (head, args))
    (hempty : args.isEmpty = true) :
    (tryProjAppReduce source flags).run methods s = .ok none s := by
  unfold tryProjAppReduce
  simp only [hspine, hempty, if_true]
  rfl

theorem tryProjAppReduce_notProjection
    {methods : Methods .anon} {s : TcState .anon}
    {source head : KExpr .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags}
    (hspine : source.collectSpine = (head, args))
    (hnonempty : args.isEmpty = false)
    (hnonprojection : ∀ id field value info,
      head ≠ KExpr.prj id field value info) :
    (tryProjAppReduce source flags).run methods s = .ok none s := by
  unfold tryProjAppReduce
  simp only [hspine, hnonempty, Bool.false_eq_true, if_false]
  cases head <;> simp_all

theorem tryProjAppReduce_projectionWhnfError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {source : KExpr .anon} {args : Array (KExpr .anon)}
    {id : KId .anon} {field : UInt64} {value : KExpr .anon}
    {info : ExprInfo .anon} {flags : WhnfFlags} {err : TcError .anon}
    (hspine : source.collectSpine = (.prj id field value info, args))
    (hnonempty : args.isEmpty = false)
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .error err s₁) :
    (tryProjAppReduce source flags).run methods s = .error err s₁ := by
  unfold tryProjAppReduce
  simp only [hspine, hnonempty, Bool.false_eq_true, if_false]
  cases hcheap : flags.cheapProj <;>
      simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hwhnf ⊢
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind _ _ s = _
    unfold EStateM.bind
    rw [hwhnf]

theorem tryProjAppReduce_projectionReduceError
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {source : KExpr .anon} {args : Array (KExpr .anon)}
    {id : KId .anon} {field : UInt64} {value wvalue : KExpr .anon}
    {info : ExprInfo .anon} {flags : WhnfFlags} {err : TcError .anon}
    (hspine : source.collectSpine = (.prj id field value info, args))
    (hnonempty : args.isEmpty = false)
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .ok wvalue s₁)
    (hreduce : (tryProjReduce id field wvalue).run methods s₁ =
      .error err s₂) :
    (tryProjAppReduce source flags).run methods s = .error err s₂ := by
  unfold tryProjAppReduce
  simp only [hspine, hnonempty, Bool.false_eq_true, if_false]
  cases hcheap : flags.cheapProj <;>
      simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hwhnf ⊢
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind _ _ s = _
    unfold EStateM.bind
    rw [hwhnf]
    simp only
    rw [ReaderT.run_bind]
    change EStateM.bind
      (ReaderT.run (tryProjReduce id field wvalue) methods) _ s₁ = _
    unfold EStateM.bind
    rw [hreduce]

theorem tryProjAppReduce_projectionNone
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {source : KExpr .anon} {args : Array (KExpr .anon)}
    {id : KId .anon} {field : UInt64} {value wvalue : KExpr .anon}
    {info : ExprInfo .anon} {flags : WhnfFlags}
    (hspine : source.collectSpine = (.prj id field value info, args))
    (hnonempty : args.isEmpty = false)
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .ok wvalue s₁)
    (hreduce : (tryProjReduce id field wvalue).run methods s₁ =
      .ok none s₂) :
    (tryProjAppReduce source flags).run methods s = .ok none s₂ := by
  unfold tryProjAppReduce
  simp only [hspine, hnonempty, Bool.false_eq_true, if_false]
  cases hcheap : flags.cheapProj <;>
      simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hwhnf ⊢
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind _ _ s = _
    unfold EStateM.bind
    rw [hwhnf]
    simp only
    rw [ReaderT.run_bind]
    change EStateM.bind
      (ReaderT.run (tryProjReduce id field wvalue) methods) _ s₁ = _
    unfold EStateM.bind
    rw [hreduce]
    rfl

theorem tryProjAppReduce_projectionSome
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {source : KExpr .anon} {args : Array (KExpr .anon)}
    {id : KId .anon} {field : UInt64}
    {value wvalue result : KExpr .anon}
    {info : ExprInfo .anon} {flags : WhnfFlags}
    (hspine : source.collectSpine = (.prj id field value info, args))
    (hnonempty : args.isEmpty = false)
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .ok wvalue s₁)
    (hreduce : (tryProjReduce id field wvalue).run methods s₁ =
      .ok (some result) s₂) :
    (tryProjAppReduce source flags).run methods s =
      .ok (some (result, args)) s₂ := by
  unfold tryProjAppReduce
  simp only [hspine, hnonempty, Bool.false_eq_true, if_false]
  cases hcheap : flags.cheapProj <;>
      simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hwhnf ⊢
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind _ _ s = _
    unfold EStateM.bind
    rw [hwhnf]
    simp only
    rw [ReaderT.run_bind]
    change EStateM.bind
      (ReaderT.run (tryProjReduce id field wvalue) methods) _ s₁ = _
    unfold EStateM.bind
    rw [hreduce]
    rfl

/-! ## Semantic assembly -/

/-- Empty collected spines make the helper a state-transparent miss. -/
theorem tryProjAppReduceFinished_empty_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {source head : KExpr .anon}
    {args : Array (KExpr .anon)}
    {flags : WhnfFlags} {s : TcState .anon}
    (hspine : source.collectSpine = (head, args))
    (hempty : args.isEmpty = true) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (tryProjAppReduceFinished source flags)
      (fun result _ => match result with
        | none => True
        | some reduced =>
            support reduced ∧
              WhnfMeaning trProj world uvars Delta source reduced) := by
  intro methods hmethods hI
  have hproj :=
    tryProjAppReduce_empty (methods := methods) (s := s) (flags := flags)
      hspine hempty
  rw [tryProjAppReduceFinished_none hproj]
  exact ⟨hI, trivial⟩

/-- Complete no-delta contract for application-headed projection reduction.

The Theory premise is uniform in the universe count because
`OptionalReduction.WF` itself is uniform; no cache entry or callback meaning
is replayed across universe counts. -/
theorem tryProjAppReduceFinished_app_optional_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (hfinish : ApplicationFinishRequestCensus requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld}
    (theory : ∀ uvars, WhnfTheory trProj world uvars)
    (hinputs : WhnfCoreInputSupport support)
    (hhelper : ProjectionHelper.WF .noAccel semantics trProj world support)
    (horacle : InductiveReductionOracle .noAccel semantics trProj world
      support)
    {f arg : KExpr .anon} {info : ExprInfo .anon} {flags : WhnfFlags}
    {uvars : Nat} {Delta : KVLCtx} {sourceV : Lean4Lean.VExpr}
    {s : TcState .anon}
    (hsourceSupport : support (.app f arg info))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app f arg info) sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryProjAppReduceFinished (.app f arg info) flags)
      (fun result _ => match result with
        | none => True
        | some reduced =>
            support reduced ∧
              WhnfMeaning trProj world uvars Delta
                (.app f arg info) reduced) := by
  intro methods hmethods hI
  generalize hspine :
      (.app f arg info : KExpr .anon).collectSpine = spine
  rcases spine with ⟨head, args⟩
  cases hempty : args.isEmpty with
  | true =>
      have hproj := tryProjAppReduce_empty
        (methods := methods) (s := s) (flags := flags) hspine hempty
      rw [tryProjAppReduceFinished_none hproj]
      exact ⟨hI, trivial⟩
  | false =>
      cases head with
      | prj id field value headInfo =>
          have htyped := trAppSpine_of_collectSpine hsource hspine
          obtain ⟨headV, hheadTr, hsuffix⟩ := htyped.toSuffix
          have hheadSupport :=
            (hinputs.app hsourceSupport hspine).1
          obtain ⟨valueV, hvalueTr, hcallbackWF⟩ :=
            projectionValueCallback_wf
              (s := s) (flags := flags) hinputs hheadSupport hheadTr
          have hcallbackPost := hcallbackWF methods hmethods hI
          match hcallbackRun :
              (if flags.cheapProj then
                  (whnfCoreFlagsRec value flags).run methods s
                else (whnfRec value).run methods s) with
          | .error err s₁ =>
              have hcallbackRunReader :
                  (if flags.cheapProj then whnfCoreFlagsRec value flags
                    else whnfRec value).run methods s =
                    .error err s₁ := by
                cases hcheap : flags.cheapProj <;>
                  simp only [hcheap, Bool.false_eq_true, if_false, if_true]
                    at hcallbackRun ⊢ <;>
                  exact hcallbackRun
              rw [hcallbackRunReader] at hcallbackPost
              have hproj :=
                tryProjAppReduce_projectionWhnfError hspine hempty
                  hcallbackRun
              rw [tryProjAppReduceFinished_projError hproj]
              exact ⟨hcallbackPost.1, trivial⟩
          | .ok wvalue s₁ =>
              have hcallbackRunReader :
                  (if flags.cheapProj then whnfCoreFlagsRec value flags
                    else whnfRec value).run methods s =
                    .ok wvalue s₁ := by
                cases hcheap : flags.cheapProj <;>
                  simp only [hcheap, Bool.false_eq_true, if_false, if_true]
                    at hcallbackRun ⊢ <;>
                  exact hcallbackRun
              rw [hcallbackRunReader] at hcallbackPost
              have hhelperPost :=
                hhelper (id := id) (field := field) hmethods
                  hcallbackPost.2.1 hcallbackPost.1
              match hreduce :
                  (tryProjReduce id field wvalue).run methods s₁ with
              | .error err s₂ =>
                  rw [hreduce] at hhelperPost
                  have hproj :=
                    tryProjAppReduce_projectionReduceError hspine hempty
                      hcallbackRun hreduce
                  rw [tryProjAppReduceFinished_projError hproj]
                  exact ⟨hhelperPost.1, trivial⟩
              | .ok none s₂ =>
                  rw [hreduce] at hhelperPost
                  have hproj :=
                    tryProjAppReduce_projectionNone hspine hempty
                      hcallbackRun hreduce
                  rw [tryProjAppReduceFinished_none hproj]
                  exact ⟨hhelperPost.1, trivial⟩
              | .ok (some projResult) s₂ =>
                  rw [hreduce] at hhelperPost
                  have hsemantic :=
                    horacle.projection hmethods hheadTr hI hcallbackRun
                      hreduce
                  have hheadPost :
                      WhnfPost trProj world uvars Delta headV projResult :=
                    WhnfPost.transMeaning (theory uvars) hI.2.1.wf
                      (WhnfPost.refl hheadTr
                        ((theory uvars).exprWF hI.2.1 hheadTr))
                      hsemantic.2
                  obtain ⟨rebuilt, s₃, hrequest, hfinishRun, hI₃, hframe,
                      hrebuiltSupport, hmeaning⟩ :=
                    changedHeadFinish_acceptance hrun hfinish
                      (methods := methods) hsourceSupport hsource hspine
                      hsuffix hhelperPost.2 hheadPost hsemantic.1
                  have hproj :=
                    tryProjAppReduce_projectionSome hspine hempty
                      hcallbackRun hreduce
                  rw [tryProjAppReduceFinished_some hproj hfinishRun]
                  exact ⟨hI₃, hrebuiltSupport, hmeaning⟩
      | var | fvar | sort | const | app | lam | all | letE | nat | str =>
          have hproj := tryProjAppReduce_notProjection
            (methods := methods) (s := s) (flags := flags)
            hspine hempty (by simp)
          rw [tryProjAppReduceFinished_none hproj]
          exact ⟨hI, trivial⟩

/-- The application theorem plus the definitional empty-spine behavior of
all ten non-application constructors yields the uniform optional-reducer
field consumed by `NoDeltaBaseOracle`. -/
theorem tryProjAppReduceFinished_optional_wf_of_contexts
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (hfinish : ApplicationFinishRequestCensus requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld}
    (theory : ∀ uvars, WhnfTheory trProj world uvars)
    (hinputs : WhnfCoreInputSupport support)
    (hhelper : ProjectionHelper.WF .noAccel semantics trProj world support)
    (horacle : InductiveReductionOracle .noAccel semantics trProj world
      support)
    (flags : WhnfFlags) :
    OptionalReduction.WF .noAccel semantics trProj world support
      (fun source => tryProjAppReduceFinished source flags) := by
  intro uvars Delta source sourceV s hsourceSupport hsource
  cases source with
  | app =>
      exact tryProjAppReduceFinished_app_optional_wf hrun hfinish theory
        hinputs hhelper horacle hsourceSupport hsource
  | var | fvar | sort | const | lam | all | letE | prj | nat | str =>
      exact tryProjAppReduceFinished_empty_wf (hspine := rfl)
        (hempty := rfl)

end RecM
end Ix.Tc
