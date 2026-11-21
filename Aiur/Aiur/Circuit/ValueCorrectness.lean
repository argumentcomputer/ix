import Aiur.Circuit.BuildFacts

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

theorem constrainWords_sound [Field F] {enable : ArithExpr F}
    {left right : List (ArithExpr F)} {before after : BuildState F}
    (compiled : constrainWords enable left right before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment ∧ (enable.denote assignment = 1 →
      left.map (ArithExpr.denote assignment) = right.map (ArithExpr.denote assignment)) := by
  induction left generalizing right before with
  | nil =>
      cases right with
      | nil =>
          obtain ⟨_, rfl⟩ := pure_ok.mp compiled
          exact ⟨valid, fun _ => rfl⟩
      | cons => simp [constrainWords] at compiled
  | cons x xs ih =>
      cases right with
      | nil => simp [constrainWords] at compiled
      | cons y ys =>
          simp only [constrainWords] at compiled
          obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
          obtain ⟨middleValid, tailEq⟩ := ih tailRun
          obtain ⟨beforeValid, headEq⟩ := constrain_valid headRun middleValid
          refine ⟨beforeValid, fun active => ?_⟩
          change enable.denote assignment * (x.denote assignment - y.denote assignment) = 0 at headEq
          simp only [active, one_mul, sub_eq_zero] at headEq
          simp [headEq, tailEq active]

/-- Guarded equations equate every tag, payload and padding column. -/
theorem constrainValue_sound [Field F] {enable : ArithExpr F} {left right : Symbolic F}
    {before after : BuildState F}
    (compiled : constrainValue enable left right before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment ∧ (enable.denote assignment = 1 →
      left.map (ArithExpr.denote assignment) = right.map (ArithExpr.denote assignment)) := by
  simp only [constrainValue] at compiled
  split at compiled
  · simp [StateT.bind, bind, Except.bind] at compiled
  · rename_i same
    obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
    obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
    have same : left.type = right.type := by simpa using same
    obtain ⟨previous, equal⟩ := constrainWords_sound rest valid
    exact ⟨previous, fun active => by cases left; cases right; simp_all [WireValue.map]⟩

/-- Exclusion equations only add constraints, so earlier validity can be recovered. -/
theorem excludePairs_valid [Field F] {selectors : List (ArithExpr F)}
    {before after : BuildState F}
    (compiled : excludePairs selectors before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment := by
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
            (show before.Valid rom calls assignment from by
              have same : before = middle := by simpa [List.forIn_nil, pure, StateT.pure, Except.pure] using pairs
              simpa [same] using middleValid)
      | cons other rest ih =>
          simp only [List.forIn_cons] at pairs
          simp [StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at pairs
          have previous := ih pairs
          exact previous.of_subset (fun _ member => by simp [member]) (fun _ member => member) (fun _ member => member)

end Aiur.Circuit.Compiler
