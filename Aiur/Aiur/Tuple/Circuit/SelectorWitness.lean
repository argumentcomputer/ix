import Aiur.Tuple.Circuit.PatternWitness
import Aiur.Scalar.Circuit.WitnessBasic

namespace Aiur.Tuple.Circuit.Compiler

private theorem excludeHead_complete [Field F] {calls : CallRelation F}
    (selector : ArithExpr F) (rest : List (ArithExpr F)) {before after : BuildState F}
    (compiled : (forIn rest PUnit.unit (fun other _ => do
      constrain (.mul selector other)
      pure (ForInStep.yield PUnit.unit)) : Build F PUnit) before = .ok (PUnit.unit, after)) {assignment : Var → F}
    (layout : before.WellFormed) (valid : before.Valid calls assignment)
    (headBound : selector.inBounds before.nextVar = true)
    (tailBound : ∀ other ∈ rest, other.inBounds before.nextVar = true)
    (zero : ∀ other ∈ rest, selector.denote assignment * other.denote assignment = 0) :
    Extension calls before after assignment assignment := by
  induction rest generalizing before with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, Except.pure] using compiled
      subst after
      exact .refl layout valid
  | cons other rest ih =>
      simp only [List.forIn_cons] at compiled
      simp [StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
      have hb : (ArithExpr.mul selector other).inBounds before.nextVar = true := by
        simp [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] at headBound ⊢
        exact ⟨headBound, tailBound other (by simp)⟩
      have extension := ih compiled (layout.constrain hb)
        (valid.constrain (zero other (by simp))) headBound
        (fun p h => tailBound p (by simp [h])) (fun p h => zero p (by simp [h]))
      exact ⟨extension.increase, extension.agree, extension.layout, extension.valid⟩

theorem excludePairs_complete [Field F] {calls : CallRelation F}
    {selectors : List (ArithExpr F)} {before after : BuildState F}
    (compiled : excludePairs selectors before = .ok ((), after)) {assignment : Var → F}
    (layout : before.WellFormed) (valid : before.Valid calls assignment)
    (bounded : ∀ selector ∈ selectors, selector.inBounds before.nextVar = true)
    (exclusive : (selectors.map (ArithExpr.denote assignment)).Pairwise (fun x y => x * y = 0)) :
    Extension calls before after assignment assignment := by
  induction selectors generalizing before with
  | nil =>
      simp only [excludePairs, pure_ok, true_and] at compiled
      subst after
      exact .refl layout valid
  | cons selector rest ih =>
      simp only [excludePairs] at compiled
      obtain ⟨finished, middle, pairs, restRun⟩ := bind_ok.mp compiled
      cases finished
      simp only [List.map_cons, List.pairwise_cons, List.forall_mem_map] at exclusive
      have headExt := excludeHead_complete selector rest pairs layout valid
        (bounded selector (by simp)) (fun p h => bounded p (by simp [h])) exclusive.1
      have tailExt := ih restRun headExt.layout headExt.valid
        (fun p h => headExt.bound (bounded p (by simp [h]))) exclusive.2
      exact headExt.trans tailExt

theorem sum_complete [Field F] {calls : CallRelation F}
    {selectors : List (ArithExpr F)} {enable : ArithExpr F} {before after : BuildState F}
    (compiled : constrain (.sub (selectors.foldl ArithExpr.add (.const 0)) enable) before = .ok ((), after))
    {assignment : Var → F} (layout : before.WellFormed) (valid : before.Valid calls assignment)
    (bounded : ∀ selector ∈ selectors, selector.inBounds before.nextVar = true)
    (enableBound : enable.inBounds before.nextVar = true)
    (sum : (selectors.map (ArithExpr.denote assignment)).sum = enable.denote assignment) :
    Extension calls before after assignment assignment := by
  apply constrain_complete compiled layout valid
  · simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
      And.intro (Scalar.Circuit.Compiler.foldl_add_inBounds (initial := .const (0 : F)) rfl bounded) enableBound
  · simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote,
      Scalar.Circuit.ArithExpr.denote_foldl_add, zero_add, sub_eq_zero]
    exact sum

end Aiur.Tuple.Circuit.Compiler
