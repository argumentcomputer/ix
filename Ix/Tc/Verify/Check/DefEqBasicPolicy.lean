import Ix.Tc.DefEq
import Ix.Tc.Verify.Check.WhnfHelperPolicy

/-!
# Operational policy for basic definitional-equality helpers

This module establishes the inference-policy frame for the non-recursive
DefEq substrate: recursive method calls, caught errors, cheap-reduction
scopes, primitive classifiers, Nat peeling, binder comparison, and finite
application-spine recursion.  Later DefEq phase proofs build exclusively on
these concrete lemmas.
-/

namespace Ix.Tc

namespace TcM.PreservesInferOnly

/-- The let-opening variant which also returns its fresh-variable expression
has the same policy frame as ordinary let opening. -/
theorem openLetWithFV
    (name : Mode.anon.F Name) (type value body : KExpr .anon) :
    (TcM.openLetWithFV name type value body).PreservesInferOnly := by
  unfold TcM.openLetWithFV
  apply bind freshFVarId
  intro fvId
  apply bind (runIntern _)
  intro fv
  apply bind (modify
    (f := fun state =>
      { state with lctx := state.lctx.push fvId (.ldecl name type value) })
    fun _ => rfl)
  intro _
  apply bind (runIntern (instantiateRev body #[fv]))
  intro bodyOpen
  exact pure (bodyOpen, fv, fvId)

end TcM.PreservesInferOnly

namespace RecM

theorem prims_preservesInferOnly (methods : Methods .anon) :
    ((prims : RecM .anon (Primitives .anon)).run methods).PreservesInferOnly := by
  unfold prims
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  exact TcM.PreservesInferOnly.pure state.prims

/-- A recursive DefEq edge is exactly the predecessor table's framed
callback. -/
theorem isDefEqCall_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqCall left right).run methods).PreservesInferOnly := by
  unfold isDefEqCall
  simpa using hmethods.isDefEq left right

/-- Infer-only validation restores the policy value which was in force at
the call site, irrespective of the callback outcome. -/
theorem inferOnlyCall_preservesInferOnly
    {methods : Methods .anon} (_hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) :
    ((inferOnlyCall source).run methods).PreservesInferOnly := by
  unfold inferOnlyCall
  simp only [ReaderT.run_bind]
  exact TcM.PreservesInferOnly.withInferOnly (methods.infer source)

/-- DefEq's caught-error operator retains all inner state changes but still
preserves the flag whenever its body does. -/
theorem tryQuestion_preservesInferOnly
    {methods : Methods .anon} {x : RecM .anon alpha}
    (hx : (x.run methods).PreservesInferOnly) :
    ((try? x).run methods).PreservesInferOnly := by
  unfold try?
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
  · exact TcM.PreservesInferOnly.tryCatch
      (TcM.PreservesInferOnly.bind hx
        (fun value => TcM.PreservesInferOnly.pure (some value)))
      (fun _ => TcM.PreservesInferOnly.pure none)
  · intro result
    exact TcM.PreservesInferOnly.pure result

/-- Cheap-recursion depth is balanced by `finally`, including on errors. -/
theorem withCheapRecursionDepth_preservesInferOnly
    {methods : Methods .anon} {x : RecM .anon alpha}
    (hx : (x.run methods).PreservesInferOnly) :
    ((withCheapRecursionDepth x).run methods).PreservesInferOnly := by
  unfold withCheapRecursionDepth
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.modify
      (f := fun state : TcState .anon => { state with
        cheapRecursionDepth := state.cheapRecursionDepth + 1 })
      (fun _ => rfl))
  intro _
  change (tryFinally (x.run methods)
    (modify (fun state : TcState .anon => { state with
      cheapRecursionDepth := state.cheapRecursionDepth - 1 }) :
      TcM .anon PUnit)).PreservesInferOnly
  exact TcM.PreservesInferOnly.tryFinally hx
    (TcM.PreservesInferOnly.modify fun _ => rfl)

theorem whnfCoreForDefEq_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) :
    ((whnfCoreForDefEq source).run methods).PreservesInferOnly := by
  unfold whnfCoreForDefEq
  exact withCheapRecursionDepth_preservesInferOnly
    (whnfCoreWithFlags_preservesInferOnly policy source .DEF_EQ_CORE)

theorem whnfNoDeltaForDefEq_preservesInferOnly
    {methods : Methods .anon} (policy : WhnfNoDeltaPolicyAt methods)
    (source : KExpr .anon) :
    ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly := by
  unfold whnfNoDeltaForDefEq
  exact withCheapRecursionDepth_preservesInferOnly
    (whnfNoDeltaImpl_preservesInferOnly policy source .DEF_EQ_CORE .collapse)

theorem isNatLike_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((isNatLike source).run methods).PreservesInferOnly := by
  unfold isNatLike
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro primitives
  cases source with
  | app function argument info =>
      cases function <;> exact TcM.PreservesInferOnly.pure _
  | var | fvar | sort | const | lam | all | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure _

theorem isNatZero_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((isNatZero source).run methods).PreservesInferOnly := by
  unfold isNatZero
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro primitives
  cases source <;> exact TcM.PreservesInferOnly.pure _

theorem natSuccOf_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((natSuccOf source).run methods).PreservesInferOnly := by
  unfold natSuccOf
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro primitives
  cases source with
  | nat value blob info =>
      simp only
      split
      · exact TcM.PreservesInferOnly.pure none
      · simp only [pure_bind]
        refine bindIntern_preservesInferOnly
          (natExprFromValue (value - 1) : KExpr .anon) ?_
        intro result
        simpa using TcM.PreservesInferOnly.pure (some result)
  | app function argument info =>
      cases function with
      | const id universes headInfo =>
          simp only
          split <;> exact TcM.PreservesInferOnly.pure _
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          exact TcM.PreservesInferOnly.pure none
  | var | fvar | sort | const | lam | all | letE | prj | str =>
      exact TcM.PreservesInferOnly.pure none

theorem isBoolTrue_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((isBoolTrue source).run methods).PreservesInferOnly := by
  unfold isBoolTrue
  cases source with
  | const id universes info =>
      simp only [ReaderT.run_bind]
      apply TcM.PreservesInferOnly.bind (prims_preservesInferOnly methods)
      intro primitives
      exact TcM.PreservesInferOnly.pure _
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure false

theorem boolTrueReductionAllowed_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((boolTrueReductionAllowed source).run methods).PreservesInferOnly := by
  unfold boolTrueReductionAllowed
  simp only
  split
  · exact TcM.PreservesInferOnly.pure true
  · simp only [ReaderT.run_bind]
    apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
    intro state
    exact TcM.PreservesInferOnly.pure state.eagerReduce

theorem whnfIsBoolTrue_preservesInferOnly
    {methods : Methods .anon}
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (source : KExpr .anon) :
    ((whnfIsBoolTrue source).run methods).PreservesInferOnly := by
  unfold whnfIsBoolTrue
  refine bind_preservesInferOnly (hwhnf source) ?_
  exact fun normalized => isBoolTrue_preservesInferOnly normalized

theorem isDelta_preservesInferOnly
    {methods : Methods .anon} (id : KId .anon) :
    ((isDelta id).run methods).PreservesInferOnly := by
  unfold isDelta
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.tryGetConst id) ?_
  intro declaration
  cases declaration with
  | none => exact TcM.PreservesInferOnly.pure false
  | some declaration =>
      cases declaration with
      | defn name levelParams kind safety hints levels type value leanAll block =>
          cases kind <;> exact TcM.PreservesInferOnly.pure _
      | recr | axio | quot | indc | ctor =>
          exact TcM.PreservesInferOnly.pure false

theorem classifyDeltaHead_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((classifyDeltaHead source).run methods).PreservesInferOnly := by
  unfold classifyDeltaHead
  cases headConstId source with
  | none => exact TcM.PreservesInferOnly.pure false
  | some id => exact isDelta_preservesInferOnly id

theorem isRegular_preservesInferOnly
    {methods : Methods .anon} (id : KId .anon) :
    ((isRegular id).run methods).PreservesInferOnly := by
  unfold isRegular
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.tryGetConst id) ?_
  intro declaration
  cases declaration with
  | none => exact TcM.PreservesInferOnly.pure false
  | some declaration =>
      cases declaration with
      | defn name levelParams kind safety hints levels type value leanAll block =>
          cases hints <;> exact TcM.PreservesInferOnly.pure _
      | recr | axio | quot | indc | ctor =>
          exact TcM.PreservesInferOnly.pure false

theorem defRankId_preservesInferOnly
    {methods : Methods .anon} (id : KId .anon) :
    ((defRankId id).run methods).PreservesInferOnly := by
  unfold defRankId
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.tryGetConst id) ?_
  intro declaration
  cases declaration with
  | none => exact TcM.PreservesInferOnly.pure (0, 0)
  | some declaration =>
      cases declaration with
      | defn name levelParams kind safety hints levels type value leanAll block =>
          cases kind with
          | opaq | thm => exact TcM.PreservesInferOnly.pure (0, 0)
          | defn =>
              cases hints <;> exact TcM.PreservesInferOnly.pure _
      | recr | axio | quot | indc | ctor =>
          exact TcM.PreservesInferOnly.pure (0, 0)

theorem rankDeltaHead_preservesInferOnly
    {methods : Methods .anon} (head : Option (KId .anon)) :
    ((rankDeltaHead head).run methods).PreservesInferOnly := by
  cases head with
  | none => exact TcM.PreservesInferOnly.pure _
  | some id => exact defRankId_preservesInferOnly id

theorem quickBinder_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (ty1 body1 ty2 body2 : KExpr .anon) :
    ((quickBinder name bi ty1 body1 ty2 body2).run
      methods).PreservesInferOnly := by
  unfold quickBinder
  refine bind_preservesInferOnly
    (isDefEqCall_preservesInferOnly hmethods ty1 ty2) ?_
  intro typesEqual
  cases typesEqual with
  | false => exact TcM.PreservesInferOnly.pure false
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      apply withLctxScope_preservesInferOnly
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.openBinder name bi ty1 body1)
      intro opened
      rcases opened with ⟨body1Open, fvId⟩
      apply TcM.PreservesInferOnly.bind
        (intern_preservesInferOnly (.mkFVar fvId name))
      intro fv
      apply TcM.PreservesInferOnly.bind
        (TcM.PreservesInferOnly.runIntern
          (instantiateRev body2 #[fv]))
      intro body2Open
      exact isDefEqCall_preservesInferOnly hmethods body1Open body2Open

theorem quickDefEq_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((quickDefEq left right).run methods).PreservesInferOnly := by
  cases left <;> cases right <;> simp only [quickDefEq]
  all_goals
    first
    | exact TcM.PreservesInferOnly.pure _
    | exact quickBinder_preservesInferOnly hmethods _ _ _ _ _ _

theorem allDefEqSpineArgsList_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly) :
    ∀ pairs,
      ((allDefEqSpineArgsList pairs).run methods).PreservesInferOnly
  | [] => TcM.PreservesInferOnly.pure true
  | (left, right) :: rest => by
      rw [allDefEqSpineArgsList]
      refine bind_preservesInferOnly
        (isDefEqCall_preservesInferOnly hmethods left right) ?_
      intro equal
      cases equal with
      | false => exact TcM.PreservesInferOnly.pure false
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          exact allDefEqSpineArgsList_preservesInferOnly hmethods rest

theorem allDefEqSpineArgs_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (pairs : Array (KExpr .anon × KExpr .anon)) :
    ((allDefEqSpineArgs pairs).run methods).PreservesInferOnly := by
  unfold allDefEqSpineArgs
  exact allDefEqSpineArgsList_preservesInferOnly hmethods pairs.toList

theorem trySameHeadSpine_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((trySameHeadSpine left right).run methods).PreservesInferOnly := by
  rcases hleft : left.collectSpine with ⟨leftHead, leftArgs⟩
  rcases hright : right.collectSpine with ⟨rightHead, rightArgs⟩
  unfold trySameHeadSpine
  simp only [hleft, hright]
  cases leftHead <;>
    try exact TcM.PreservesInferOnly.pure none
  case const leftId leftLevels leftInfo =>
    cases rightHead <;>
      try exact TcM.PreservesInferOnly.pure none
    case const rightId rightLevels rightInfo =>
      cases hshape :
          (leftId.addr != rightId.addr || leftArgs.size != rightArgs.size) with
      | true =>
          simp only [hshape, if_true]
          exact TcM.PreservesInferOnly.pure none
      | false =>
        simp only [hshape, Bool.false_eq_true, if_false, pure_bind]
        cases huniverses : sameDefEqUniverses leftLevels rightLevels with
        | false =>
          simp only [Bool.not_false, if_true]
          exact TcM.PreservesInferOnly.pure none
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          refine bind_preservesInferOnly
            (allDefEqSpineArgs_preservesInferOnly hmethods
              (leftArgs.zip rightArgs)) ?_
          intro accepted
          cases accepted with
          | false => exact TcM.PreservesInferOnly.pure none
          | true =>
              simp only [Bool.not_true, Bool.false_eq_true, if_false]
              exact TcM.PreservesInferOnly.pure (some true)

/-- The narrow same-head rejection cache updates only the environment. -/
theorem trySameHeadSpineCached_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((trySameHeadSpineCached left right).run
      methods).PreservesInferOnly := by
  unfold trySameHeadSpineCached
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.defEqCtxKey left right) ?_
  intro contextAddress
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  split
  · exact TcM.PreservesInferOnly.pure none
  · simp only [pure_bind]
    apply TcM.PreservesInferOnly.bind
      (trySameHeadSpine_preservesInferOnly hmethods left right)
    intro result
    cases result with
    | some accepted => exact TcM.PreservesInferOnly.pure (some accepted)
    | none =>
        intro before
        rfl

theorem tryDefEqWhnfApp_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (functionLeft argumentLeft functionRight argumentRight : KExpr .anon) :
    ((tryDefEqWhnfApp functionLeft argumentLeft functionRight argumentRight).run
      methods).PreservesInferOnly := by
  unfold tryDefEqWhnfApp
  refine bind_preservesInferOnly
    (isDefEqCall_preservesInferOnly hmethods functionLeft functionRight) ?_
  intro functionsEqual
  cases functionsEqual with
  | false => exact TcM.PreservesInferOnly.pure none
  | true =>
      simp only [if_true]
      refine bind_preservesInferOnly
        (isDefEqCall_preservesInferOnly hmethods argumentLeft argumentRight) ?_
      intro argumentsEqual
      cases argumentsEqual <;> exact TcM.PreservesInferOnly.pure _

end RecM

end Ix.Tc
