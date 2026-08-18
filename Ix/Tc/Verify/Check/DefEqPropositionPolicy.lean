import Ix.Tc.Verify.Check.DefEqNatPolicy

/-!
# Operational policy for DefEq proposition and unit classifiers

Proof irrelevance and the final unit-like fallback both perform infer-only
queries under caught-error semantics.  This module proves that their cache
shells, lazy declaration lookups, WHNF calls, and recursive equality edges
restore the caller's exact inference policy.
-/

namespace Ix.Tc

namespace RecM

theorem classifyPropTypeUncached_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (type : KExpr .anon) :
    ((classifyPropTypeUncached type).run
      methods).PreservesInferOnly := by
  unfold classifyPropTypeUncached
  refine bind_preservesInferOnly
    (tryQuestion_preservesInferOnly
      (inferOnlyCall_preservesInferOnly hmethods type)) ?_
  intro inferred
  cases inferred with
  | none => exact TcM.PreservesInferOnly.pure false
  | some sort =>
      simp only
      refine bind_preservesInferOnly
        (tryQuestion_preservesInferOnly (hwhnf sort)) ?_
      intro normalized
      cases normalized with
      | some expression =>
          cases expression <;> exact TcM.PreservesInferOnly.pure _
      | none => exact TcM.PreservesInferOnly.pure false

theorem isPropType_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (type : KExpr .anon) :
    ((isPropType type).run methods).PreservesInferOnly := by
  unfold isPropType
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.ctxAddrForLbr type.lbr) ?_
  intro contextAddress
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  split
  · exact TcM.PreservesInferOnly.pure _
  · apply TcM.PreservesInferOnly.bind
      (classifyPropTypeUncached_preservesInferOnly hmethods hwhnf type)
    intro result
    intro before
    rfl

theorem tryProofIrrel_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryProofIrrel left right).run methods).PreservesInferOnly := by
  unfold tryProofIrrel
  refine bind_preservesInferOnly
    (tryQuestion_preservesInferOnly
      (inferOnlyCall_preservesInferOnly hmethods left)) ?_
  intro leftTypeResult
  cases leftTypeResult with
  | none => exact TcM.PreservesInferOnly.pure false
  | some leftType =>
      simp only
      refine bind_preservesInferOnly
        (isPropType_preservesInferOnly hmethods hwhnf leftType) ?_
      intro isProposition
      cases isProposition with
      | false => exact TcM.PreservesInferOnly.pure false
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
          refine bind_preservesInferOnly
            (tryQuestion_preservesInferOnly
              (inferOnlyCall_preservesInferOnly hmethods right)) ?_
          intro rightTypeResult
          cases rightTypeResult with
          | none => exact TcM.PreservesInferOnly.pure false
          | some rightType =>
              exact isDefEqCall_preservesInferOnly hmethods leftType rightType

theorem isUnitLikeInductive_preservesInferOnly
    {methods : Methods .anon} (inductiveId : KId .anon) :
    ((isUnitLikeInductive inductiveId).run
      methods).PreservesInferOnly := by
  unfold isUnitLikeInductive
  refine bindTcM_preservesInferOnly
    (TcM.PreservesInferOnly.tryGetConst inductiveId) ?_
  intro declaration
  cases declaration with
  | none => exact TcM.PreservesInferOnly.pure false
  | some declaration =>
      cases declaration with
      | indc name levelParams levels params indices isUnsafe block memberIdx
          type constructors leanAll =>
          simp only
          split
          · exact TcM.PreservesInferOnly.pure false
          · refine bindTcM_preservesInferOnly
              (TcM.PreservesInferOnly.tryGetConst constructors[0]!) ?_
            intro constructorDeclaration
            cases constructorDeclaration with
            | none => exact TcM.PreservesInferOnly.pure false
            | some constructorDeclaration =>
                cases constructorDeclaration <;>
                  exact TcM.PreservesInferOnly.pure _
      | defn | recr | axio | quot | ctor =>
          exact TcM.PreservesInferOnly.pure false

theorem tryDefEqUnit_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqUnit left right).run methods).PreservesInferOnly := by
  unfold tryDefEqUnit
  refine bind_preservesInferOnly
    (tryQuestion_preservesInferOnly
      (inferOnlyCall_preservesInferOnly hmethods left)) ?_
  intro leftTypeResult
  cases leftTypeResult with
  | none => exact TcM.PreservesInferOnly.pure false
  | some leftType =>
      simp only
      refine bind_preservesInferOnly
        (tryQuestion_preservesInferOnly (hwhnf leftType)) ?_
      intro normalizedTypeResult
      cases normalizedTypeResult with
      | none => exact TcM.PreservesInferOnly.pure false
      | some normalizedType =>
          simp only
          rcases hspine : normalizedType.collectSpine with ⟨head, arguments⟩
          cases head with
          | const inductiveId universes info =>
              refine bind_preservesInferOnly
                (isUnitLikeInductive_preservesInferOnly inductiveId) ?_
              intro isUnitLike
              cases isUnitLike with
              | false => exact TcM.PreservesInferOnly.pure false
              | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, if_false,
                    pure_bind]
                  refine bind_preservesInferOnly
                    (tryQuestion_preservesInferOnly
                      (inferOnlyCall_preservesInferOnly hmethods right)) ?_
                  intro rightTypeResult
                  cases rightTypeResult with
                  | none => exact TcM.PreservesInferOnly.pure false
                  | some rightType =>
                      exact isDefEqCall_preservesInferOnly hmethods
                        normalizedType rightType
          | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
              exact TcM.PreservesInferOnly.pure false

end RecM

end Ix.Tc
