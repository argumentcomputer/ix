import Ix.Tc.Verify.Check.WhnfReductionPolicy

/-!
# Operational policy for non-recursive WHNF helpers

This module discharges the inference-policy frame for the shared application
finisher, cached delta unfolding, projection definitions, String primitives,
and quotient reduction.  Projection applications are derived in
`WhnfReductionPolicy` from their ordinary projection, WHNF callback, and
application-finisher components rather than retained as an independent
assumption.
-/

namespace Ix.Tc

namespace RecM

/-- Lift an already established checker-state policy through the recursive
method reader. -/
theorem liftTcM_preservesInferOnly
    {methods : Methods .anon} {x : TcM .anon alpha}
    (hx : x.PreservesInferOnly) :
    ((liftM x : RecM .anon alpha).run methods).PreservesInferOnly := by
  simpa only [ReaderT.run_monadLift] using hx

/-- Compose two recursive-method actions without exposing the reader
implementation at each helper proof. -/
theorem bind_preservesInferOnly
    {methods : Methods .anon} {x : RecM .anon alpha}
    {next : alpha → RecM .anon beta}
    (hx : (x.run methods).PreservesInferOnly)
    (hnext : ∀ value, ((next value).run methods).PreservesInferOnly) :
    ((do let value ← x; next value).run methods).PreservesInferOnly := by
  simp only [ReaderT.run_bind]
  exact TcM.PreservesInferOnly.bind hx hnext

/-- Compose one checker action with a recursive-method continuation. -/
theorem bindTcM_preservesInferOnly
    {methods : Methods .anon} {x : TcM .anon alpha}
    {next : alpha → RecM .anon beta}
    (hx : x.PreservesInferOnly)
    (hnext : ∀ value, ((next value).run methods).PreservesInferOnly) :
    TcM.PreservesInferOnly
      ((do
        let value ← x
        next value : RecM .anon beta).run methods) := by
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  change TcM.PreservesInferOnly
    (x >>= fun value => ReaderT.run (next value) methods)
  exact TcM.PreservesInferOnly.bind hx hnext

/-- Interning changes only the intern table. -/
theorem intern_preservesInferOnly (request : KExpr .anon) :
    (TcM.intern request).PreservesInferOnly := by
  exact TcM.PreservesInferOnly.runIntern (internExprM request)

/-- Common one-intern recursive-method prefix. -/
theorem bindIntern_preservesInferOnly
    {methods : Methods .anon} (request : KExpr .anon)
    {next : KExpr .anon → RecM .anon alpha}
    (hnext : ∀ result, ((next result).run methods).PreservesInferOnly) :
    TcM.PreservesInferOnly
      ((do
        let result ← TcM.intern request
        next result : RecM .anon alpha).run methods) := by
  exact bindTcM_preservesInferOnly
    (intern_preservesInferOnly request) hnext

/-- Reify a recursive-method exception as a value without changing the
inference-policy frame. -/
theorem captureErrors_preservesInferOnly
    {methods : Methods .anon} {x : RecM .anon alpha}
    (hx : (x.run methods).PreservesInferOnly) :
    TcM.PreservesInferOnly
      ((try
          let value ← x
          pure (Except.ok value)
        catch error =>
          pure (Except.error error) :
        RecM .anon (Except (TcError .anon) alpha)).run methods) := by
  exact TcM.PreservesInferOnly.tryCatch
    (TcM.PreservesInferOnly.bind hx fun value =>
      TcM.PreservesInferOnly.pure (Except.ok value))
    (fun error => TcM.PreservesInferOnly.pure (Except.error error))

private theorem prims_preservesInferOnly (methods : Methods .anon) :
    ((prims : RecM .anon (Primitives .anon)).run methods).PreservesInferOnly := by
  unfold prims
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  exact TcM.PreservesInferOnly.pure state.prims


theorem finishAppResult_preservesInferOnly
    {methods : Methods .anon} (base : KExpr .anon)
    (args : Array (KExpr .anon)) (consumed : Nat) :
    ((finishAppResult base args consumed).run methods).PreservesInferOnly := by
  rw [finishAppResult_eq_foldlM, ← Array.foldlM_toList]
  generalize hitems : (args.extract consumed args.size).toList = items
  clear hitems
  induction items generalizing base with
  | nil => exact TcM.PreservesInferOnly.pure base
  | cons arg rest ih =>
      rw [List.foldlM_cons, ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.runIntern
          (internExprM (KExpr.mkApp base arg)))
      intro result
      exact ih result

theorem unfoldConstValue_preservesInferOnly
    {methods : Methods .anon} (head value : KExpr .anon)
    (levels : Array (KUniv .anon)) :
    ((unfoldConstValue head value levels).run methods).PreservesInferOnly := by
  unfold unfoldConstValue
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  split
  · exact TcM.PreservesInferOnly.pure _
  · apply TcM.PreservesInferOnly.bind
      (TcM.PreservesInferOnly.instantiateUnivParams value levels)
    intro result
    show ((do
      modify fun state : TcState .anon => { state with env := { state.env with
        unfoldCache := state.env.unfoldCache.insert head.addr result } }
      pure result : RecM .anon (KExpr .anon)).run methods).PreservesInferOnly
    simp only [ReaderT.run_bind]
    apply TcM.PreservesInferOnly.bind
      (TcM.PreservesInferOnly.modify
        (f := fun state : TcState .anon => { state with env := { state.env with
          unfoldCache := state.env.unfoldCache.insert head.addr result } })
        (fun _ => rfl))
    intro _
    exact TcM.PreservesInferOnly.pure result

private theorem deltaFinish_eq (base : KExpr m)
    (args : Array (KExpr m)) :
    (forIn args base fun arg result => do
      let result ← TcM.intern (KExpr.mkApp result arg)
      pure (.yield result) : RecM m (KExpr m)) =
      finishAppResult base args 0 := by
  rw [finishAppResult_eq_foldlM]
  simp [Array.forIn_yield_eq_foldlM]

theorem tryDeltaUnfold_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((tryDeltaUnfold source).run methods).PreservesInferOnly := by
  unfold tryDeltaUnfold
  rcases hspine : source.collectSpine with ⟨head, args⟩
  cases head with
  | const id levels info =>
      simp only [pure_bind, ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.tryGetConst id)
      intro found
      cases found with
      | none => exact TcM.PreservesInferOnly.pure none
      | some declaration =>
          cases declaration
          case defn name levelParams kind safety hints lvls ty value leanAll
              block =>
            cases kind with
            | opaq => exact TcM.PreservesInferOnly.pure none
            | defn | thm =>
                simp only [ReaderT.run_bind]
                apply TcM.PreservesInferOnly.bind
                  (unfoldConstValue_preservesInferOnly
                    (.const id levels info) value levels)
                intro base
                rw [deltaFinish_eq]
                apply TcM.PreservesInferOnly.bind
                  (finishAppResult_preservesInferOnly base args 0)
                intro result
                exact TcM.PreservesInferOnly.pure (some result)
          all_goals exact TcM.PreservesInferOnly.pure none
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure none

theorem deltaUnfoldOne_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((deltaUnfoldOne source).run methods).PreservesInferOnly := by
  unfold deltaUnfoldOne
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (tryDeltaUnfold_preservesInferOnly source)
  intro unfolded
  cases unfolded with
  | some result => exact TcM.PreservesInferOnly.pure (some result)
  | none =>
      cases source with
      | const id levels info =>
          simp only [pure_bind, ReaderT.run_bind]
          apply TcM.PreservesInferOnly.bind
            (TcM.PreservesInferOnly.tryGetConst id)
          intro found
          cases found with
          | none => exact TcM.PreservesInferOnly.pure none
          | some declaration =>
              cases declaration
              case defn name levelParams kind safety hints lvls ty value
                  leanAll block =>
                cases kind with
                | opaq => exact TcM.PreservesInferOnly.pure none
                | defn | thm =>
                    simp only [ReaderT.run_bind]
                    apply TcM.PreservesInferOnly.bind
                      (unfoldConstValue_preservesInferOnly
                        (.const id levels info) value levels)
                    intro result
                    exact TcM.PreservesInferOnly.pure (some result)
              all_goals exact TcM.PreservesInferOnly.pure none
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          exact TcM.PreservesInferOnly.pure none

theorem tryReduceProjectionDefinition_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((tryReduceProjectionDefinition source).run methods).PreservesInferOnly := by
  unfold tryReduceProjectionDefinition
  rcases hspine : source.collectSpine with ⟨head, args⟩
  cases head with
  | const id levels info =>
      simp only [ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.tryGetConst id)
      intro found
      cases found with
      | none => exact TcM.PreservesInferOnly.pure none
      | some declaration =>
          cases declaration
          case defn name levelParams kind safety hints lvls ty value leanAll block =>
            cases kind with
            | opaq =>
                simp only
                exact TcM.PreservesInferOnly.pure none
            | thm =>
                simp only
                exact TcM.PreservesInferOnly.pure none
            | defn =>
                simp only [pure_bind]
                cases hinfo : projectionDefinitionInfo value with
                | none =>
                    simp only []
                    exact TcM.PreservesInferOnly.pure none
                | some projection =>
                    rcases projection with ⟨arity, structId, field,
                      structArgIdx⟩
                    simp only []
                    split
                    · exact TcM.PreservesInferOnly.pure none
                    · simp only [ReaderT.run_bind, ReaderT.run_monadLift]
                      apply TcM.PreservesInferOnly.bind
                        (TcM.PreservesInferOnly.runIntern
                          (internExprM (KExpr.mkPrj structId field
                            args[structArgIdx]!)))
                      intro base
                      simp only [projectionDefinitionFinish_eq]
                      apply TcM.PreservesInferOnly.bind
                        (finishAppResult_preservesInferOnly base args arity)
                      intro result
                      exact TcM.PreservesInferOnly.pure (some result)
          all_goals exact TcM.PreservesInferOnly.pure none
  | var idx name info => exact TcM.PreservesInferOnly.pure none
  | fvar id name info => exact TcM.PreservesInferOnly.pure none
  | sort u info => exact TcM.PreservesInferOnly.pure none
  | app f a info => exact TcM.PreservesInferOnly.pure none
  | lam name bi ty body info => exact TcM.PreservesInferOnly.pure none
  | all name bi ty body info => exact TcM.PreservesInferOnly.pure none
  | letE name ty value body nondep info =>
      exact TcM.PreservesInferOnly.pure none
  | prj id field value info => exact TcM.PreservesInferOnly.pure none
  | nat value blob info => exact TcM.PreservesInferOnly.pure none
  | str value blob info => exact TcM.PreservesInferOnly.pure none

theorem charOfNatExpr_preservesInferOnly
    {methods : Methods .anon} (value : Nat) :
    ((charOfNatExpr value).run methods).PreservesInferOnly := by
  unfold charOfNatExpr
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.PreservesInferOnly.bind (prims_preservesInferOnly methods)
  intro p
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.runIntern
      (internExprM (KExpr.mkConst p.charOfNat #[])))
  intro charOfNat
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.runIntern
      (internExprM (natExprFromValue value : KExpr .anon)))
  intro natLiteral
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.runIntern
      (internExprM (KExpr.mkApp charOfNat natLiteral)))
  intro result
  exact TcM.PreservesInferOnly.pure (some result)

theorem tryReduceStringLiteral_preservesInferOnly
    {methods : Methods .anon} (p : Primitives .anon) (id : KId .anon)
    (value : String) :
    ((tryReduceStringLiteral p id value).run methods).PreservesInferOnly := by
  unfold tryReduceStringLiteral
  cases hutf8 : id.addr == p.stringUtf8ByteSize.addr with
  | true =>
      simp only [if_true]
      change (TcM.runIntern
        (internExprM
          (natExprFromValue value.utf8ByteSize : KExpr .anon)) >>= fun result =>
            pure (some result)).PreservesInferOnly
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.runIntern
          (internExprM
            (natExprFromValue value.utf8ByteSize : KExpr .anon)))
      intro result
      exact TcM.PreservesInferOnly.pure (some result)
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      cases hbytes : id.addr == p.stringToByteArray.addr with
      | true =>
          simp only [if_true]
          cases hempty : value.isEmpty with
          | true =>
              simp only [if_true]
              change (TcM.runIntern
                (internExprM (KExpr.mkConst p.byteArrayEmpty #[])) >>=
                  fun result => pure (some result)).PreservesInferOnly
              apply TcM.PreservesInferOnly.bind
                (TcM.PreservesInferOnly.runIntern
                  (internExprM (KExpr.mkConst p.byteArrayEmpty #[])))
              intro result
              exact TcM.PreservesInferOnly.pure (some result)
          | false =>
              simp only [Bool.false_eq_true, if_false]
              exact TcM.PreservesInferOnly.pure none
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact charOfNatExpr_preservesInferOnly (methods := methods) _

theorem tryReduceString_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((tryReduceString source).run methods).PreservesInferOnly := by
  unfold tryReduceString
  rcases hspine : source.collectSpine with ⟨head, args⟩
  cases hsize : args.size != 1 with
  | true =>
      simp only [hsize, if_true]
      exact TcM.PreservesInferOnly.pure none
  | false =>
      simp only [hsize, Bool.false_eq_true, if_false]
      cases head with
      | const id levels info =>
          simp only [pure_bind, ReaderT.run_bind]
          apply TcM.PreservesInferOnly.bind
            (prims_preservesInferOnly methods)
          intro p
          cases hguard :
              (!(id.addr == p.stringBack.addr ||
                  id.addr == p.stringLegacyBack.addr) &&
                !(id.addr == p.stringUtf8ByteSize.addr) &&
                !(id.addr == p.stringToByteArray.addr)) with
          | true =>
              simp only [if_true]
              exact TcM.PreservesInferOnly.pure none
          | false =>
              simp only [Bool.false_eq_true, if_false]
              cases args[0]! with
              | str value blob info =>
                  exact tryReduceStringLiteral_preservesInferOnly
                    (methods := methods) p id value
              | var | fvar | sort | const | app | lam | all | letE | prj |
                    nat =>
                  exact TcM.PreservesInferOnly.pure none
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          simp only [pure_bind]
          exact TcM.PreservesInferOnly.pure none

theorem tryQuotReduceSelected_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (p : Primitives .anon) (args : Array (KExpr .anon))
    (functionIndex majorIndex : Nat) :
    TcM.PreservesInferOnly
      ((tryQuotReduceSelected p args functionIndex majorIndex).run methods) := by
  unfold tryQuotReduceSelected
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (whnfRec_preservesInferOnly hmethods args[majorIndex]!)
  intro major
  rcases hspine : major.collectSpine with ⟨head, majorArgs⟩
  cases head with
  | const id levels info =>
      cases hctor : id.addr != p.quotCtor.addr with
      | true =>
          simp only [hctor, if_true]
          exact TcM.PreservesInferOnly.pure none
      | false =>
          simp only [hctor, Bool.false_eq_true, if_false]
          cases hsize : majorArgs.size != 3 with
          | true =>
              simp only [if_true]
              exact TcM.PreservesInferOnly.pure none
          | false =>
              simp only [Bool.false_eq_true, if_false, pure_bind,
                ReaderT.run_bind, ReaderT.run_monadLift]
              apply TcM.PreservesInferOnly.bind
                (TcM.PreservesInferOnly.runIntern
                  (internExprM
                    (KExpr.mkApp args[functionIndex]! majorArgs[2]!)))
              intro base
              rw [projectionDefinitionFinish_eq]
              apply TcM.PreservesInferOnly.bind
                (finishAppResult_preservesInferOnly base args
                  (majorIndex + 1))
              intro result
              exact TcM.PreservesInferOnly.pure (some result)
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      simp only
      exact TcM.PreservesInferOnly.pure none

theorem tryQuotReduce_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) :
    ((tryQuotReduce source).run methods).PreservesInferOnly := by
  unfold tryQuotReduce
  rcases hspine : source.collectSpine with ⟨head, args⟩
  cases head with
  | const id levels info =>
      simp only [pure_bind, ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind (prims_preservesInferOnly methods)
      intro p
      cases hlift : id.addr == p.quotLift.addr with
      | true =>
          simp only [if_true]
          by_cases hsize : args.size < 6
          · simp only [hsize, if_pos]
            exact TcM.PreservesInferOnly.pure none
          · simp only [hsize, if_false]
            simpa only [tryQuotReduceSelected] using
              tryQuotReduceSelected_preservesInferOnly hmethods p args 3 5
      | false =>
          simp only [Bool.false_eq_true, if_false]
          cases hind : id.addr == p.quotInd.addr with
          | true =>
              simp only [if_true]
              by_cases hsize : args.size < 5
              · simp only [hsize, if_pos]
                exact TcM.PreservesInferOnly.pure none
              · simp only [hsize, if_false]
                simpa only [tryQuotReduceSelected] using
                  tryQuotReduceSelected_preservesInferOnly hmethods p args 3 4
          | false =>
              simp only [Bool.false_eq_true, if_false]
              exact TcM.PreservesInferOnly.pure none
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      simp only
      exact TcM.PreservesInferOnly.pure none

end RecM

end Ix.Tc
