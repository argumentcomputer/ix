import Ix.Tc.Verify.Check.DefEqEtaPolicy

/-!
# Operational policy for final-WHNF definitional equality

The final comparison is an ordered fallback chain: constructor-directed
structural comparison, Nat bridging, lambda eta, String expansion,
structure eta, unit-like classification, and proof irrelevance.  These
lemmas preserve that exact production order while framing every success and
partial error state.
-/

namespace Ix.Tc

namespace RecM

theorem tryDefEqWhnfLet_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (name : Mode.anon.F Name)
    (typeLeft valueLeft bodyLeft typeRight valueRight bodyRight :
      KExpr .anon) :
    ((tryDefEqWhnfLet name typeLeft valueLeft bodyLeft typeRight valueRight
      bodyRight).run methods).PreservesInferOnly := by
  unfold tryDefEqWhnfLet
  refine bind_preservesInferOnly
    (isDefEqCall_preservesInferOnly hmethods typeLeft typeRight) ?_
  intro typesEqual
  cases typesEqual with
  | false => exact TcM.PreservesInferOnly.pure none
  | true =>
      simp only [if_true]
      refine bind_preservesInferOnly
        (isDefEqCall_preservesInferOnly hmethods valueLeft valueRight) ?_
      intro valuesEqual
      cases valuesEqual with
      | false => exact TcM.PreservesInferOnly.pure none
      | true =>
          simp only [if_true]
          have hbody :
              ((withLctxScope do
                let (leftOpen, fresh, _) ←
                  (liftM (TcM.openLetWithFV name typeLeft valueLeft bodyLeft) :
                    RecM .anon (KExpr .anon × KExpr .anon × FVarId))
                let rightOpen ←
                  (liftM (TcM.runIntern (instantiateRev bodyRight #[fresh])) :
                    RecM .anon (KExpr .anon))
                isDefEqCall leftOpen rightOpen).run
                methods).PreservesInferOnly := by
            apply withLctxScope_preservesInferOnly
            simp only [ReaderT.run_bind, ReaderT.run_monadLift]
            apply TcM.PreservesInferOnly.bind
              (TcM.PreservesInferOnly.openLetWithFV name typeLeft valueLeft
                bodyLeft)
            intro opened
            rcases opened with ⟨leftOpen, fresh, freshId⟩
            apply TcM.PreservesInferOnly.bind
              (TcM.PreservesInferOnly.runIntern
                (instantiateRev bodyRight #[fresh]))
            intro rightOpen
            exact isDefEqCall_preservesInferOnly hmethods leftOpen rightOpen
          refine bind_preservesInferOnly hbody ?_
          intro bodiesEqual
          cases bodiesEqual <;> exact TcM.PreservesInferOnly.pure _

theorem tryDefEqWhnfStructural_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqWhnfStructural left right).run
      methods).PreservesInferOnly := by
  cases left with
  | sort leftUniverse leftInfo =>
      cases right <;> simp only [tryDefEqWhnfStructural] <;>
        exact TcM.PreservesInferOnly.pure _
  | var leftIndex leftName leftInfo =>
      cases right with
      | var rightIndex rightName rightInfo =>
          simp only [tryDefEqWhnfStructural]
          split
          · exact TcM.PreservesInferOnly.pure (some true)
          · intro before
            rfl
      | fvar | sort | const | app | lam | all | letE | prj | nat | str =>
          exact TcM.PreservesInferOnly.pure none
  | fvar leftId leftName leftInfo =>
      cases right <;> simp only [tryDefEqWhnfStructural] <;>
        exact TcM.PreservesInferOnly.pure none
  | const leftId leftUniverses leftInfo =>
      cases right with
      | const rightId rightUniverses rightInfo =>
          simp only [tryDefEqWhnfStructural]
          split
          · exact TcM.PreservesInferOnly.pure (some true)
          · intro before
            rfl
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          exact TcM.PreservesInferOnly.pure none
  | app leftFunction leftArgument leftInfo =>
      cases right with
      | app rightFunction rightArgument rightInfo =>
          simp only [tryDefEqWhnfStructural]
          exact tryDefEqWhnfApp_preservesInferOnly hmethods leftFunction
            leftArgument rightFunction rightArgument
      | var | fvar | sort | const | lam | all | letE | prj | nat | str =>
          simp only [tryDefEqWhnfStructural]
          exact TcM.PreservesInferOnly.pure none
  | lam name binderInfo leftType leftBody leftInfo =>
      cases right with
      | lam rightName rightBinderInfo rightType rightBody rightInfo =>
          simp only [tryDefEqWhnfStructural]
          refine bind_preservesInferOnly
            (quickBinder_preservesInferOnly hmethods name binderInfo leftType
              leftBody rightType rightBody) ?_
          intro equal
          cases equal <;> exact TcM.PreservesInferOnly.pure _
      | var | fvar | sort | const | app | all | letE | prj | nat | str =>
          simp only [tryDefEqWhnfStructural]
          exact TcM.PreservesInferOnly.pure none
  | all name binderInfo leftType leftBody leftInfo =>
      cases right with
      | all rightName rightBinderInfo rightType rightBody rightInfo =>
          simp only [tryDefEqWhnfStructural]
          refine bind_preservesInferOnly
            (quickBinder_preservesInferOnly hmethods name binderInfo leftType
              leftBody rightType rightBody) ?_
          intro equal
          cases equal <;> exact TcM.PreservesInferOnly.pure _
      | var | fvar | sort | const | app | lam | letE | prj | nat | str =>
          simp only [tryDefEqWhnfStructural]
          exact TcM.PreservesInferOnly.pure none
  | letE name leftType leftValue leftBody leftNonDependent leftInfo =>
      cases right with
      | letE rightName rightType rightValue rightBody rightNonDependent
          rightInfo =>
          simp only [tryDefEqWhnfStructural]
          exact tryDefEqWhnfLet_preservesInferOnly hmethods name leftType
            leftValue leftBody rightType rightValue rightBody
      | var | fvar | sort | const | app | lam | all | prj | nat | str =>
          simp only [tryDefEqWhnfStructural]
          exact TcM.PreservesInferOnly.pure none
  | prj leftId leftField leftValue leftInfo =>
      cases right <;> simp only [tryDefEqWhnfStructural] <;>
        exact TcM.PreservesInferOnly.pure none
  | nat leftValue leftBlob leftInfo =>
      cases right <;> simp only [tryDefEqWhnfStructural] <;>
        exact TcM.PreservesInferOnly.pure _
  | str leftValue leftBlob leftInfo =>
      cases right <;> simp only [tryDefEqWhnfStructural] <;>
        exact TcM.PreservesInferOnly.pure _

theorem tryDefEqWhnfNat_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqWhnfNat left right).run methods).PreservesInferOnly := by
  unfold tryDefEqWhnfNat
  refine bind_preservesInferOnly (isNatLike_preservesInferOnly left) ?_
  intro leftNat
  refine bind_preservesInferOnly (isNatLike_preservesInferOnly right) ?_
  intro rightNat
  cases hboth : (leftNat && rightNat) with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact TcM.PreservesInferOnly.pure none
  | true =>
      simp only [if_true]
      refine bind_preservesInferOnly
        (isDefEqNat_preservesInferOnly hmethods left right) ?_
      intro answer
      exact TcM.PreservesInferOnly.pure (some answer)

theorem tryDefEqWhnfEtaAfterGuard_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqWhnfEtaAfterGuard left right).run
      methods).PreservesInferOnly := by
  unfold tryDefEqWhnfEtaAfterGuard
  refine bind_preservesInferOnly
    (tryEtaExpansion_preservesInferOnly hmethods hwhnf left right) ?_
  intro firstAccepted
  cases firstAccepted with
  | true => exact TcM.PreservesInferOnly.pure (some true)
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      refine bind_preservesInferOnly
        (tryEtaExpansion_preservesInferOnly hmethods hwhnf right left) ?_
      intro secondAccepted
      cases secondAccepted <;> exact TcM.PreservesInferOnly.pure _

theorem tryDefEqWhnfEta_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqWhnfEta left right).run methods).PreservesInferOnly := by
  cases left <;> cases right <;> simp only [tryDefEqWhnfEta]
  all_goals first
    | exact TcM.PreservesInferOnly.pure none
    | exact tryDefEqWhnfEtaAfterGuard_preservesInferOnly hmethods hwhnf _ _

theorem tryDefEqWhnfStringAfterGuard_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqWhnfStringAfterGuard left right).run
      methods).PreservesInferOnly := by
  unfold tryDefEqWhnfStringAfterGuard
  refine bind_preservesInferOnly
    (tryStringLitExpansion_preservesInferOnly hmethods left right) ?_
  intro firstAccepted
  cases firstAccepted with
  | true => exact TcM.PreservesInferOnly.pure (some true)
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      refine bind_preservesInferOnly
        (tryStringLitExpansion_preservesInferOnly hmethods right left) ?_
      intro secondAccepted
      cases secondAccepted <;> exact TcM.PreservesInferOnly.pure _

theorem tryDefEqWhnfString_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqWhnfString left right).run methods).PreservesInferOnly := by
  unfold tryDefEqWhnfString
  split
  · exact tryDefEqWhnfStringAfterGuard_preservesInferOnly hmethods left right
  · exact TcM.PreservesInferOnly.pure none

theorem tryDefEqWhnfStructEta_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqWhnfStructEta left right).run
      methods).PreservesInferOnly := by
  unfold tryDefEqWhnfStructEta
  refine bind_preservesInferOnly
    (tryEtaStruct_preservesInferOnly hmethods hnoDelta left right) ?_
  intro firstAccepted
  cases firstAccepted with
  | true => exact TcM.PreservesInferOnly.pure (some true)
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      refine bind_preservesInferOnly
        (tryEtaStruct_preservesInferOnly hmethods hnoDelta right left) ?_
      intro secondAccepted
      cases secondAccepted <;> exact TcM.PreservesInferOnly.pure _

theorem isDefEqWhnfAfterUnit_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqWhnfAfterUnit left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqWhnfAfterUnit
  exact tryProofIrrel_preservesInferOnly hmethods hwhnf left right

theorem isDefEqWhnfAfterStructEta_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqWhnfAfterStructEta left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqWhnfAfterStructEta
  refine bind_preservesInferOnly
    (tryDefEqUnit_preservesInferOnly hmethods hwhnf left right) ?_
  intro accepted
  cases accepted with
  | true => exact TcM.PreservesInferOnly.pure true
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      exact isDefEqWhnfAfterUnit_preservesInferOnly hmethods hwhnf left right

theorem isDefEqWhnfAfterString_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqWhnfAfterString left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqWhnfAfterString
  refine bind_preservesInferOnly
    (tryDefEqWhnfStructEta_preservesInferOnly hmethods hnoDelta left right) ?_
  intro result
  cases result with
  | some answer => exact TcM.PreservesInferOnly.pure answer
  | none =>
      exact isDefEqWhnfAfterStructEta_preservesInferOnly hmethods hwhnf left
        right

theorem isDefEqWhnfAfterEta_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqWhnfAfterEta left right).run methods).PreservesInferOnly := by
  unfold isDefEqWhnfAfterEta
  refine bind_preservesInferOnly
    (tryDefEqWhnfString_preservesInferOnly hmethods left right) ?_
  intro result
  cases result with
  | some answer => exact TcM.PreservesInferOnly.pure answer
  | none =>
      exact isDefEqWhnfAfterString_preservesInferOnly hmethods hwhnf hnoDelta
        left right

theorem isDefEqWhnfAfterNat_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqWhnfAfterNat left right).run methods).PreservesInferOnly := by
  unfold isDefEqWhnfAfterNat
  refine bind_preservesInferOnly
    (tryDefEqWhnfEta_preservesInferOnly hmethods hwhnf left right) ?_
  intro result
  cases result with
  | some answer => exact TcM.PreservesInferOnly.pure answer
  | none =>
      exact isDefEqWhnfAfterEta_preservesInferOnly hmethods hwhnf hnoDelta left
        right

theorem isDefEqWhnfAfterStructural_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqWhnfAfterStructural left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqWhnfAfterStructural
  refine bind_preservesInferOnly
    (tryDefEqWhnfNat_preservesInferOnly hmethods left right) ?_
  intro result
  cases result with
  | some answer => exact TcM.PreservesInferOnly.pure answer
  | none =>
      exact isDefEqWhnfAfterNat_preservesInferOnly hmethods hwhnf hnoDelta left
        right

theorem isDefEqWhnf_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqWhnf left right).run methods).PreservesInferOnly := by
  unfold isDefEqWhnf
  refine bind_preservesInferOnly
    (tryDefEqWhnfStructural_preservesInferOnly hmethods left right) ?_
  intro result
  cases result with
  | some answer => exact TcM.PreservesInferOnly.pure answer
  | none =>
      exact isDefEqWhnfAfterStructural_preservesInferOnly hmethods hwhnf
        hnoDelta left right

end RecM

end Ix.Tc
