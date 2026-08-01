import Ix.Tc.Verify.Check.DefEqBasicPolicy

/-!
# Operational policy for DefEq Nat and String bridges

These proofs cover literal/constructor peeling, generalized Nat-offset
decomposition and reconstruction, and String-literal expansion.  Every
successful recursive comparison is routed through the framed predecessor
method table; all misses and allocation errors preserve the same policy.
-/

namespace Ix.Tc

namespace RecM

attribute [local irreducible] strLitToConstructor

theorem natOffsetDecompose_preservesInferOnly
    {methods : Methods .anon} (source : KExpr .anon) :
    ((natOffsetDecompose source).run methods).PreservesInferOnly := by
  unfold natOffsetDecompose
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro primitives
  split
  · exact TcM.PreservesInferOnly.pure _
  · simp only [pure_bind]
    refine bind_preservesInferOnly
      (natOffset_preservesInferOnly source 0) ?_
    intro result
    cases result with
    | none => exact TcM.PreservesInferOnly.pure none
    | some offsetResult =>
        rcases offsetResult with ⟨base, offset⟩
        simp only
        split
        · exact TcM.PreservesInferOnly.pure none
        · refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
          intro currentPrimitives
          split <;> exact TcM.PreservesInferOnly.pure _

theorem natOffsetRebuild_preservesInferOnly
    {methods : Methods .anon} (base : Option (KExpr .anon)) (offset : Nat) :
    ((natOffsetRebuild base offset).run methods).PreservesInferOnly := by
  unfold natOffsetRebuild
  cases base with
  | none => exact TcM.PreservesInferOnly.pure _
  | some source =>
      cases hzero : (offset == 0) with
      | true =>
        simp only [if_true]
        exact TcM.PreservesInferOnly.pure source
      | false =>
        simp only [Bool.false_eq_true, if_false, pure_bind]
        exact mkNatAdd_preservesInferOnly source (natExprFromValue offset)

theorem isDefEqNatAfterLiteral_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqNatAfterLiteral left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqNatAfterLiteral
  refine bind_preservesInferOnly (isNatZero_preservesInferOnly left) ?_
  intro leftZero
  refine bind_preservesInferOnly (isNatZero_preservesInferOnly right) ?_
  intro rightZero
  cases hzero : (leftZero && rightZero) with
  | true =>
      simp only [if_true]
      exact TcM.PreservesInferOnly.pure true
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      refine bind_preservesInferOnly (natSuccOf_preservesInferOnly left) ?_
      intro leftPredecessor
      refine bind_preservesInferOnly (natSuccOf_preservesInferOnly right) ?_
      intro rightPredecessor
      cases leftPredecessor with
      | none => exact TcM.PreservesInferOnly.pure false
      | some leftPred =>
          cases rightPredecessor with
          | none => exact TcM.PreservesInferOnly.pure false
          | some rightPred =>
              exact isDefEqCall_preservesInferOnly hmethods leftPred rightPred

theorem isDefEqNat_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqNat left right).run methods).PreservesInferOnly := by
  unfold isDefEqNat
  cases left <;> cases right <;>
    first
    | exact TcM.PreservesInferOnly.pure _
    | exact isDefEqNatAfterLiteral_preservesInferOnly hmethods _ _

theorem tryDefEqOffsetAfterCandidates_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqOffsetAfterCandidates left right).run
      methods).PreservesInferOnly := by
  unfold tryDefEqOffsetAfterCandidates
  refine bind_preservesInferOnly
    (natOffsetDecompose_preservesInferOnly left) ?_
  intro leftResult
  cases leftResult with
  | none => exact TcM.PreservesInferOnly.pure none
  | some leftParts =>
      rcases leftParts with ⟨leftBase, leftOffset⟩
      simp only
      refine bind_preservesInferOnly
        (natOffsetDecompose_preservesInferOnly right) ?_
      intro rightResult
      cases rightResult with
      | none => exact TcM.PreservesInferOnly.pure none
      | some rightParts =>
          rcases rightParts with ⟨rightBase, rightOffset⟩
          simp only
          cases hshared : (min leftOffset rightOffset == 0) with
          | true =>
            simp only [if_true]
            exact TcM.PreservesInferOnly.pure none
          | false =>
            simp only [Bool.false_eq_true, if_false, pure_bind]
            refine bind_preservesInferOnly
              (natOffsetRebuild_preservesInferOnly leftBase
                (leftOffset - min leftOffset rightOffset)) ?_
            intro leftRemainder
            refine bind_preservesInferOnly
              (natOffsetRebuild_preservesInferOnly rightBase
                (rightOffset - min leftOffset rightOffset)) ?_
            intro rightRemainder
            refine bind_preservesInferOnly
              (isDefEqCall_preservesInferOnly hmethods leftRemainder
                rightRemainder) ?_
            intro answer
            exact TcM.PreservesInferOnly.pure (some answer)

theorem tryDefEqOffsetAfterZeroMiss_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqOffsetAfterZeroMiss left right).run
      methods).PreservesInferOnly := by
  unfold tryDefEqOffsetAfterZeroMiss
  refine bind_preservesInferOnly (prims_preservesInferOnly methods) ?_
  intro primitives
  split
  · exact TcM.PreservesInferOnly.pure none
  · simp only [pure_bind]
    exact tryDefEqOffsetAfterCandidates_preservesInferOnly hmethods left right

theorem tryDefEqOffsetAfterLiteral_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqOffsetAfterLiteral left right).run
      methods).PreservesInferOnly := by
  unfold tryDefEqOffsetAfterLiteral
  refine bind_preservesInferOnly (isNatZero_preservesInferOnly left) ?_
  intro leftZero
  refine bind_preservesInferOnly (isNatZero_preservesInferOnly right) ?_
  intro rightZero
  cases hzero : (leftZero && rightZero) with
  | true =>
      simp only [if_true]
      exact TcM.PreservesInferOnly.pure (some true)
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      exact tryDefEqOffsetAfterZeroMiss_preservesInferOnly hmethods left right

theorem tryDefEqOffset_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqOffset left right).run methods).PreservesInferOnly := by
  unfold tryDefEqOffset
  cases left <;> cases right <;> simp only [pure_bind]
  all_goals
    first
    | exact TcM.PreservesInferOnly.pure _
    | exact tryDefEqOffsetAfterLiteral_preservesInferOnly hmethods _ _

theorem tryStringLitExpansion_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (literal other : KExpr .anon) :
    ((tryStringLitExpansion literal other).run
      methods).PreservesInferOnly := by
  cases literal <;> simp only [tryStringLitExpansion]
  case str value blob info =>
    refine bind_preservesInferOnly (methods := methods)
      (strLitToConstructor_preservesInferOnly (methods := methods) value) ?_
    intro expanded
    exact isDefEqCall_preservesInferOnly hmethods expanded other
  all_goals exact TcM.PreservesInferOnly.pure false

end RecM

end Ix.Tc
