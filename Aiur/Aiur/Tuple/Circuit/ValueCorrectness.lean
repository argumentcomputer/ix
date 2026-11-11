import Aiur.Tuple.Circuit.BuildFacts

namespace Aiur.Tuple.Circuit.Compiler

mutual
  /-- Guarded leaf equalities imply equality of the complete structured values. -/
  theorem constrainValue_sound [Field F] {enable : ArithExpr F} {left right : Symbolic F}
      {before after : BuildState F}
      (compiled : constrainValue enable left right before = .ok ((), after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
      before.Valid calls assignment ∧ (enable.denote assignment = 1 →
        left.map (ArithExpr.denote assignment) = right.map (ArithExpr.denote assignment)) := by
    cases left with
    | field left =>
        cases right with
        | tuple => simp [constrainValue] at compiled
        | field right =>
            simp only [constrainValue, guarded] at compiled
            obtain ⟨beforeValid, equation⟩ := constrain_valid compiled valid
            refine ⟨beforeValid, fun active => ?_⟩
            change enable.denote assignment * (left.denote assignment - right.denote assignment) = 0
              at equation
            simp only [active, one_mul, sub_eq_zero] at equation
            simp [Value.map, equation]
    | tuple left =>
        cases right with
        | field => simp [constrainValue] at compiled
        | tuple right =>
            simp only [constrainValue] at compiled
            obtain ⟨beforeValid, equal⟩ := constrainValues_sound compiled valid
            exact ⟨beforeValid, fun active => by simp only [Value.map, equal active]⟩
  termination_by sizeOf left

  theorem constrainValues_sound [Field F] {enable : ArithExpr F}
      {left right : List (Symbolic F)} {before after : BuildState F}
      (compiled : constrainValues enable left right before = .ok ((), after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
      before.Valid calls assignment ∧ (enable.denote assignment = 1 →
        left.map (Value.map (ArithExpr.denote assignment)) =
          right.map (Value.map (ArithExpr.denote assignment))) := by
    cases left with
    | nil =>
        cases right with
        | nil =>
            simp only [constrainValues, pure_ok, true_and] at compiled
            subst after
            exact ⟨valid, fun _ => rfl⟩
        | cons => simp [constrainValues] at compiled
    | cons left ls =>
        cases right with
        | nil => simp [constrainValues] at compiled
        | cons right rs =>
            simp only [constrainValues] at compiled
            obtain ⟨finished, middle, headRun, tailRun⟩ := bind_ok.mp compiled
            cases finished
            obtain ⟨middleValid, tailEq⟩ := constrainValues_sound tailRun valid
            obtain ⟨beforeValid, headEq⟩ := constrainValue_sound headRun middleValid
            exact ⟨beforeValid, fun active => by simp [headEq active, tailEq active]⟩
  termination_by sizeOf left
end

/-- Exclusion equations only add constraints, so earlier validity can be recovered. -/
theorem excludePairs_valid [Field F] {selectors : List (ArithExpr F)}
    {before after : BuildState F}
    (compiled : excludePairs selectors before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
    before.Valid calls assignment := by
  induction selectors generalizing before with
  | nil =>
      simp only [excludePairs, pure_ok, true_and] at compiled
      subst after
      exact valid
  | cons selector rest ih =>
      simp only [excludePairs] at compiled
      obtain ⟨finished, middle, pairs, restRun⟩ := bind_ok.mp compiled
      cases finished
      have middleValid := ih restRun
      clear ih restRun compiled valid
      induction rest generalizing before with
      | nil =>
          simpa [List.forIn_nil, pure, StateT.pure, Except.pure] using
            (show before.Valid calls assignment from by
              have same : before = middle := by simpa [List.forIn_nil, pure, StateT.pure, Except.pure] using pairs
              simpa [same] using middleValid)
      | cons other rest ih =>
          simp only [List.forIn_cons] at pairs
          simp [StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at pairs
          have previous := ih pairs
          exact previous.of_subset (fun _ member => by simp [member]) (fun _ member => member)

end Aiur.Tuple.Circuit.Compiler
