import Ix.Tc.Verify.Check.WhnfDriverPolicy

/-!
# Operational inference-policy frame for WHNF reduction steps

This module decomposes each production WHNF loop iteration into explicit
helper frames.  It proves the structural dispatcher, the ordered no-delta
tail, and the full-WHNF iteration—including every success, miss, and partial
error path—without assuming the outer driver.

`WhnfHelperPolicyAt` is the remaining local acceptance surface.  Once its
helper fields are discharged, `reductionPolicy` supplies the complete step
contract consumed by `WhnfDriverPolicy`.
-/

namespace Ix.Tc

namespace RecM

private theorem prims_preservesInferOnly (methods : Methods .anon) :
    ((prims : RecM .anon (Primitives .anon)).run methods).PreservesInferOnly := by
  unfold prims
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  exact TcM.PreservesInferOnly.pure state.prims

theorem whnfRec_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) :
    ((whnfRec source).run methods).PreservesInferOnly := by
  unfold whnfRec
  exact hmethods.whnf source

theorem whnfModeRec_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) (mode : NatSuccMode) :
    ((whnfModeRec source mode).run methods).PreservesInferOnly := by
  unfold whnfModeRec
  exact hmethods.whnfMode source mode

theorem whnfCoreFlagsRec_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) (flags : WhnfFlags) :
    ((whnfCoreFlagsRec source flags).run methods).PreservesInferOnly := by
  unfold whnfCoreFlagsRec
  exact hmethods.whnfCoreFlags source flags

theorem inferOnlyRec_preservesInferOnly
    {methods : Methods .anon} (_hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) :
    ((inferOnlyRec source).run methods).PreservesInferOnly := by
  unfold inferOnlyRec
  simp only [ReaderT.run_bind]
  exact TcM.PreservesInferOnly.withInferOnly (methods.infer source)

private theorem tryQuestion_preservesInferOnly
    {methods : Methods .anon} {x : RecM .anon alpha}
    (hx : (x.run methods).PreservesInferOnly) :
    ((try? x).run methods).PreservesInferOnly := by
  unfold try?
  exact TcM.PreservesInferOnly.tryCatch
    (TcM.PreservesInferOnly.bind hx
      (fun value => TcM.PreservesInferOnly.pure (some value)))
    (fun _ => TcM.PreservesInferOnly.pure none)

theorem tryOptional_preservesInferOnly
    {methods : Methods .anon} {x : RecM .anon alpha}
    (hx : (x.run methods).PreservesInferOnly) :
    ((tryOptional x).run methods).PreservesInferOnly := by
  simpa only [tryOptional] using tryQuestion_preservesInferOnly hx

theorem isNatLiteralRecursorApp_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((isNatLiteralRecursorApp source).run methods).PreservesInferOnly := by
  unfold isNatLiteralRecursorApp
  simp only []
  rcases hspine : source.collectSpine with ⟨head, spine⟩
  cases head with
  | const id levels info =>
      simp only [ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind (prims_preservesInferOnly methods)
      intro p
      split
      · exact TcM.PreservesInferOnly.pure false
      · apply TcM.PreservesInferOnly.bind
          (TcM.PreservesInferOnly.tryGetConst id)
        intro found
        cases found with
        | none => exact TcM.PreservesInferOnly.pure false
        | some info =>
            cases info <;> simp only
            case recr name levelParams k isUnsafe lvls params indices motives
                minors block memberIdx ty rules leanAll =>
              cases hmajor :
                  spine[(params + motives + minors + indices).toNat]? with
              | none => exact TcM.PreservesInferOnly.pure false
              | some major =>
                  cases major <;> exact TcM.PreservesInferOnly.pure _
            all_goals exact TcM.PreservesInferOnly.pure false
  | var idx name info => exact TcM.PreservesInferOnly.pure false
  | fvar id name info => exact TcM.PreservesInferOnly.pure false
  | sort u info => exact TcM.PreservesInferOnly.pure false
  | app f a info => exact TcM.PreservesInferOnly.pure false
  | lam name bi ty body info => exact TcM.PreservesInferOnly.pure false
  | all name bi ty body info => exact TcM.PreservesInferOnly.pure false
  | letE name ty val body nondep info => exact TcM.PreservesInferOnly.pure false
  | prj id field val info => exact TcM.PreservesInferOnly.pure false
  | nat value blob info => exact TcM.PreservesInferOnly.pure false
  | str value blob info => exact TcM.PreservesInferOnly.pure false

theorem isTransientNatLiteralWork_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((isTransientNatLiteralWork source).run methods).PreservesInferOnly := by
  unfold isTransientNatLiteralWork
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (isNatLiteralRecursorApp_preservesInferOnly source)
  intro direct
  cases direct with
  | true => exact TcM.PreservesInferOnly.pure true
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      rcases hspine : source.collectSpine with ⟨head, args⟩
      cases head with
      | const id levels info =>
          simp only [ReaderT.run_bind]
          apply TcM.PreservesInferOnly.bind (prims_preservesInferOnly methods)
          intro p
          split
          · exact isNatLiteralRecursorApp_preservesInferOnly args[0]!
          · exact TcM.PreservesInferOnly.pure false
      | var idx name info => exact TcM.PreservesInferOnly.pure false
      | fvar id name info => exact TcM.PreservesInferOnly.pure false
      | sort u info => exact TcM.PreservesInferOnly.pure false
      | app f a info => exact TcM.PreservesInferOnly.pure false
      | lam name bi ty body info => exact TcM.PreservesInferOnly.pure false
      | all name bi ty body info => exact TcM.PreservesInferOnly.pure false
      | letE name ty val body nondep info => exact TcM.PreservesInferOnly.pure false
      | prj id field val info => exact TcM.PreservesInferOnly.pure false
      | nat value blob info => exact TcM.PreservesInferOnly.pure false
      | str value blob info => exact TcM.PreservesInferOnly.pure false

private theorem tryProjAppReduce_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hproj : ∀ id field value,
      ((tryProjReduce id field value).run methods).PreservesInferOnly)
    (source : KExpr .anon) (flags : WhnfFlags) :
    TcM.PreservesInferOnly
      ((tryProjAppReduce source flags).run methods) := by
  unfold tryProjAppReduce
  rcases hspine : source.collectSpine with ⟨head, args⟩
  cases hempty : args.isEmpty with
  | true =>
      simp only [hempty, if_true]
      exact TcM.PreservesInferOnly.pure none
  | false =>
      simp only [hempty, Bool.false_eq_true, if_false, pure_bind]
      cases head with
      | prj id field value info =>
          cases hcheap : flags.cheapProj with
          | true =>
              simp only [if_true, ReaderT.run_bind]
              apply TcM.PreservesInferOnly.bind
                (whnfCoreFlagsRec_preservesInferOnly hmethods value flags)
              intro reduced
              apply TcM.PreservesInferOnly.bind (hproj id field reduced)
              intro projection
              cases projection <;> exact TcM.PreservesInferOnly.pure _
          | false =>
              simp only [Bool.false_eq_true, if_false, ReaderT.run_bind]
              apply TcM.PreservesInferOnly.bind
                (whnfRec_preservesInferOnly hmethods value)
              intro reduced
              apply TcM.PreservesInferOnly.bind (hproj id field reduced)
              intro projection
              cases projection <;> exact TcM.PreservesInferOnly.pure _
      | var | fvar | sort | const | app | lam | all | letE | nat | str =>
          exact TcM.PreservesInferOnly.pure none

/-- The projection-application reducer is a composition of the recursive
WHNF edge, the ordinary projection helper, and the shared application
finisher.  It therefore needs no independent policy assumption. -/
theorem tryProjAppReduceFinished_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hproj : ∀ id field value,
      ((tryProjReduce id field value).run methods).PreservesInferOnly)
    (hfinish : ∀ base args start,
      ((finishAppResult base args start).run methods).PreservesInferOnly)
    (source : KExpr .anon) (flags : WhnfFlags) :
    TcM.PreservesInferOnly
      ((tryProjAppReduceFinished source flags).run methods) := by
  unfold tryProjAppReduceFinished
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (tryProjAppReduce_preservesInferOnly hmethods hproj source flags)
  intro projection
  cases projection with
  | none => exact TcM.PreservesInferOnly.pure none
  | some pair =>
      rcases pair with ⟨base, args⟩
      simp only [ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind (hfinish base args 0)
      intro rebuilt
      exact TcM.PreservesInferOnly.pure (some rebuilt)

/-- Outcome-sensitive frames for the reduction helpers called by the three
WHNF step seams.  Driver control and bounded iteration are not assumptions. -/
structure WhnfHelperPolicyAt (methods : Methods .anon) : Prop where
  proj : ∀ id field value,
    ((tryProjReduce id field value).run methods).PreservesInferOnly
  finishApp : ∀ base args start,
    ((finishAppResult base args start).run methods).PreservesInferOnly
  iota : ∀ source flags,
    ((tryIotaWithFlags source flags).run methods).PreservesInferOnly
  bitvec : ∀ source,
    ((tryReduceBitvec source).run methods).PreservesInferOnly
  nat : ∀ source mode,
    ((tryReduceNatWithSuccMode source mode).run methods).PreservesInferOnly
  native : ∀ source,
    ((tryReduceNative source).run methods).PreservesInferOnly
  string : ∀ source,
    ((tryReduceString source).run methods).PreservesInferOnly
  projectionDefinition : ∀ source,
    ((tryReduceProjectionDefinition source).run methods).PreservesInferOnly
  quot : ∀ source,
    ((tryQuotReduce source).run methods).PreservesInferOnly
  decidable : ∀ source,
    ((tryReduceDecidable source).run methods).PreservesInferOnly
  natOffset : ∀ source,
    ((tryNatOffsetStuck source).run methods).PreservesInferOnly
  delta : ∀ source,
    ((deltaUnfoldOne source).run methods).PreservesInferOnly

theorem whnfCoreWithFlagsStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (helpers : WhnfHelperPolicyAt methods)
    (source : KExpr .anon) (flags : WhnfFlags) :
    ((whnfCoreWithFlagsStep source flags).run methods).PreservesInferOnly := by
  cases source with
  | var idx name info =>
      unfold whnfCoreWithFlagsStep
      simp only [ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.lookupLetVal idx)
      intro found
      cases found <;> exact TcM.PreservesInferOnly.pure _
  | fvar id name info =>
      unfold whnfCoreWithFlagsStep
      simp only [ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
      intro state
      cases hfound : state.lctx.find? id with
      | none => exact TcM.PreservesInferOnly.pure _
      | some decl =>
          cases decl <;> exact TcM.PreservesInferOnly.pure _
  | sort u info => exact TcM.PreservesInferOnly.pure _
  | const id levels info => exact TcM.PreservesInferOnly.pure _
  | lam name bi ty body info => exact TcM.PreservesInferOnly.pure _
  | all name bi ty body info => exact TcM.PreservesInferOnly.pure _
  | letE name ty value body nondep info =>
      unfold whnfCoreWithFlagsStep
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.runIntern (subst body value 0))
      intro reduced
      exact TcM.PreservesInferOnly.pure (BoundedStep.next reduced)
  | prj id field value info =>
      unfold whnfCoreWithFlagsStep
      simp only []
      split
      · apply TcM.PreservesInferOnly.bind
          (whnfCoreFlagsRec_preservesInferOnly hmethods value flags)
        intro reducedValue
        apply TcM.PreservesInferOnly.bind
          (helpers.proj id field reducedValue)
        intro result
        cases result <;> exact TcM.PreservesInferOnly.pure _
      · apply TcM.PreservesInferOnly.bind
          (whnfRec_preservesInferOnly hmethods value)
        intro reducedValue
        apply TcM.PreservesInferOnly.bind
          (helpers.proj id field reducedValue)
        intro result
        cases result <;> exact TcM.PreservesInferOnly.pure _
  | nat value blob info => exact TcM.PreservesInferOnly.pure _
  | str value blob info => exact TcM.PreservesInferOnly.pure _
  | app fn arg info =>
      unfold whnfCoreWithFlagsStep
      simp only [ReaderT.run_bind]
      generalize hspine : (KExpr.app fn arg info).collectSpine = spine
      rcases spine with ⟨head, args⟩
      apply TcM.PreservesInferOnly.bind
        (whnfCoreFlagsRec_preservesInferOnly hmethods head flags)
      intro reducedHead
      cases reducedHead with
      | lam name bi ty body info =>
          generalize hconsume :
            consumeBetaLams (.lam name bi ty body info) args = consumed
          rcases consumed with ⟨body0, consumedArgs⟩
          simp only []
          split
          · simp only [ReaderT.run_bind, ReaderT.run_monadLift, pure_bind]
            apply TcM.PreservesInferOnly.bind
              (TcM.PreservesInferOnly.runIntern
                (simulSubst body0 consumedArgs.reverse 0))
            intro substituted
            apply TcM.PreservesInferOnly.bind
              (helpers.finishApp substituted args consumedArgs.size)
            intro rebuilt
            exact TcM.PreservesInferOnly.pure (BoundedStep.next rebuilt)
          · simp only [ReaderT.run_bind, pure_bind]
            apply TcM.PreservesInferOnly.bind
              (helpers.finishApp body0 args consumedArgs.size)
            intro rebuilt
            exact TcM.PreservesInferOnly.pure (BoundedStep.next rebuilt)
      | var idx name info =>
          simp only
          split
          · apply TcM.PreservesInferOnly.bind
              (helpers.finishApp (.var idx name info) args 0)
            intro rebuilt
            apply TcM.PreservesInferOnly.bind (helpers.iota rebuilt flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
          · apply TcM.PreservesInferOnly.bind
              (helpers.iota (.app fn arg info) flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
      | fvar id name info =>
          simp only
          split
          · apply TcM.PreservesInferOnly.bind
              (helpers.finishApp (.fvar id name info) args 0)
            intro rebuilt
            apply TcM.PreservesInferOnly.bind (helpers.iota rebuilt flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
          · apply TcM.PreservesInferOnly.bind
              (helpers.iota (.app fn arg info) flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
      | sort u info =>
          simp only
          split
          · apply TcM.PreservesInferOnly.bind
              (helpers.finishApp (.sort u info) args 0)
            intro rebuilt
            apply TcM.PreservesInferOnly.bind (helpers.iota rebuilt flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
          · apply TcM.PreservesInferOnly.bind
              (helpers.iota (.app fn arg info) flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
      | const id levels info =>
          simp only
          split
          · apply TcM.PreservesInferOnly.bind
              (helpers.finishApp (.const id levels info) args 0)
            intro rebuilt
            apply TcM.PreservesInferOnly.bind (helpers.iota rebuilt flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
          · apply TcM.PreservesInferOnly.bind
              (helpers.iota (.app fn arg info) flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
      | app f a info =>
          simp only
          split
          · apply TcM.PreservesInferOnly.bind
              (helpers.finishApp (.app f a info) args 0)
            intro rebuilt
            apply TcM.PreservesInferOnly.bind (helpers.iota rebuilt flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
          · apply TcM.PreservesInferOnly.bind
              (helpers.iota (.app fn arg info) flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
      | all name bi ty body info =>
          simp only
          split
          · apply TcM.PreservesInferOnly.bind
              (helpers.finishApp (.all name bi ty body info) args 0)
            intro rebuilt
            apply TcM.PreservesInferOnly.bind (helpers.iota rebuilt flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
          · apply TcM.PreservesInferOnly.bind
              (helpers.iota (.app fn arg info) flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
      | letE name ty value body nondep info =>
          simp only
          split
          · apply TcM.PreservesInferOnly.bind
              (helpers.finishApp (.letE name ty value body nondep info) args 0)
            intro rebuilt
            apply TcM.PreservesInferOnly.bind (helpers.iota rebuilt flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
          · apply TcM.PreservesInferOnly.bind
              (helpers.iota (.app fn arg info) flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
      | prj id field value info =>
          simp only
          split
          · apply TcM.PreservesInferOnly.bind
              (helpers.finishApp (.prj id field value info) args 0)
            intro rebuilt
            apply TcM.PreservesInferOnly.bind (helpers.iota rebuilt flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
          · apply TcM.PreservesInferOnly.bind
              (helpers.iota (.app fn arg info) flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
      | nat value blob info =>
          simp only
          split
          · apply TcM.PreservesInferOnly.bind
              (helpers.finishApp (.nat value blob info) args 0)
            intro rebuilt
            apply TcM.PreservesInferOnly.bind (helpers.iota rebuilt flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
          · apply TcM.PreservesInferOnly.bind
              (helpers.iota (.app fn arg info) flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
      | str value blob info =>
          simp only
          split
          · apply TcM.PreservesInferOnly.bind
              (helpers.finishApp (.str value blob info) args 0)
            intro rebuilt
            apply TcM.PreservesInferOnly.bind (helpers.iota rebuilt flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _
          · apply TcM.PreservesInferOnly.bind
              (helpers.iota (.app fn arg info) flags)
            intro result
            cases result <;> exact TcM.PreservesInferOnly.pure _

theorem whnfNoDeltaReducersStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (helpers : WhnfHelperPolicyAt methods)
    (flags : WhnfFlags) (mode : NatSuccMode) (source : KExpr .anon) :
    ((whnfNoDeltaReducersStep flags mode source).run methods).PreservesInferOnly := by
  unfold whnfNoDeltaReducersStep
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (tryProjAppReduceFinished_preservesInferOnly hmethods helpers.proj
      helpers.finishApp source flags)
  intro projection
  cases projection with
  | some reduced =>
      exact TcM.PreservesInferOnly.pure (BoundedStep.next reduced)
  | none =>
      apply TcM.PreservesInferOnly.bind (helpers.bitvec source)
      intro bitvec
      cases bitvec with
      | some reduced =>
          exact TcM.PreservesInferOnly.pure (BoundedStep.next reduced)
      | none =>
          apply TcM.PreservesInferOnly.bind (helpers.nat source mode)
          intro nat
          cases nat with
          | some reduced =>
              exact TcM.PreservesInferOnly.pure (BoundedStep.next reduced)
          | none =>
              apply TcM.PreservesInferOnly.bind (helpers.native source)
              intro native
              cases native with
              | some reduced =>
                  exact TcM.PreservesInferOnly.pure (BoundedStep.next reduced)
              | none =>
                  apply TcM.PreservesInferOnly.bind (helpers.string source)
                  intro string
                  cases string with
                  | some reduced =>
                      exact TcM.PreservesInferOnly.pure
                        (BoundedStep.next reduced)
                  | none =>
                      cases hfull : flags.isFull with
                      | true =>
                          simp only [if_true]
                          apply TcM.PreservesInferOnly.bind
                            (helpers.projectionDefinition source)
                          intro projectionDefinition
                          cases projectionDefinition with
                          | some reduced =>
                              exact TcM.PreservesInferOnly.pure
                                (BoundedStep.next reduced)
                          | none =>
                              apply TcM.PreservesInferOnly.bind
                                (helpers.quot source)
                              intro quotient
                              cases quotient <;>
                                exact TcM.PreservesInferOnly.pure _
                      | false =>
                          simp only [Bool.false_eq]
                          apply TcM.PreservesInferOnly.bind
                            (helpers.quot source)
                          intro quotient
                          cases quotient <;> exact TcM.PreservesInferOnly.pure _

def WhnfHelperPolicyAt.noDeltaPolicy
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (helpers : WhnfHelperPolicyAt methods) :
    WhnfNoDeltaPolicyAt methods where
  transient := isTransientNatLiteralWork_preservesInferOnly
  coreStep := whnfCoreWithFlagsStep_preservesInferOnly hmethods helpers
  noDeltaReducers :=
    whnfNoDeltaReducersStep_preservesInferOnly hmethods helpers

theorem whnfWithNatSuccModeStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (helpers : WhnfHelperPolicyAt methods)
    (mode : NatSuccMode)
    (state : KExpr .anon × Std.HashSet Address) :
    ((whnfWithNatSuccModeStep mode state).run methods).PreservesInferOnly := by
  rcases state with ⟨source, seen⟩
  unfold whnfWithNatSuccModeStep
  simp only [ReaderT.run_bind]
  let noDeltaPolicy := helpers.noDeltaPolicy hmethods
  apply TcM.PreservesInferOnly.bind
    (whnfNoDeltaImpl_preservesInferOnly noDeltaPolicy source .FULL mode)
  intro reduced
  split
  · exact TcM.PreservesInferOnly.pure (BoundedStep.done reduced)
  · apply TcM.PreservesInferOnly.bind (helpers.native reduced)
    intro native
    cases native with
    | some result =>
        exact TcM.PreservesInferOnly.pure (BoundedStep.next (result, _))
    | none =>
        apply TcM.PreservesInferOnly.bind (helpers.bitvec reduced)
        intro bitvec
        cases bitvec with
        | some result =>
            exact TcM.PreservesInferOnly.pure (BoundedStep.next (result, _))
        | none =>
            apply TcM.PreservesInferOnly.bind (helpers.nat reduced mode)
            intro nat
            cases nat with
            | some result =>
                exact TcM.PreservesInferOnly.pure
                  (BoundedStep.next (result, _))
            | none =>
                apply TcM.PreservesInferOnly.bind (helpers.decidable reduced)
                intro decidable
                cases decidable with
                | some result =>
                    exact TcM.PreservesInferOnly.pure
                      (BoundedStep.next (result, _))
                | none =>
                    apply TcM.PreservesInferOnly.bind (helpers.string reduced)
                    intro string
                    cases string with
                    | some result =>
                        exact TcM.PreservesInferOnly.pure
                          (BoundedStep.next (result, _))
                    | none =>
                        apply TcM.PreservesInferOnly.bind
                          (helpers.natOffset reduced)
                        intro offset
                        cases offset with
                        | some result =>
                            exact TcM.PreservesInferOnly.pure
                              (BoundedStep.done result)
                        | none =>
                            apply TcM.PreservesInferOnly.bind
                              (helpers.delta reduced)
                            intro delta
                            cases delta with
                            | some result =>
                                exact TcM.PreservesInferOnly.pure
                                  (BoundedStep.next (result, _))
                            | none =>
                                exact TcM.PreservesInferOnly.pure
                                  (BoundedStep.done reduced)

def WhnfHelperPolicyAt.reductionPolicy
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (helpers : WhnfHelperPolicyAt methods) :
    WhnfReductionPolicyAt methods where
  toWhnfNoDeltaPolicyAt := helpers.noDeltaPolicy hmethods
  fullStep := whnfWithNatSuccModeStep_preservesInferOnly hmethods helpers

end RecM

end Ix.Tc
