import Aiur.Tuple.Circuit.BuildFacts
import Aiur.Tuple.Circuit.PatternFacts

namespace Aiur.Tuple.Circuit.Compiler

theorem equalIndicator_sound [Field F] [DecidableEq F]
    {difference test : ArithExpr F} {before after : BuildState F}
    (compiled : equalIndicator difference before = .ok (test, after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
    before.Valid calls assignment ∧
      test.denote assignment = if difference.denote assignment = 0 then 1 else 0 := by
  simp [equalIndicator, StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
  obtain ⟨rfl, rfl⟩ := compiled
  refine ⟨valid.of_subset (fun _ member => by simp [member]) (fun _ member => member), ?_⟩
  apply equality_indicator_sound
  · exact valid.constraints (.mul difference (.var before.nextVar)) (by simp)
  · exact valid.constraints
      (.sub (.mul difference (.var (before.nextVar + 1)))
        (.sub (.const 1) (.var before.nextVar))) (by simp)

/-- A test records both exact matching and the environment collected by the pattern. -/
def PatternTest [Field F] (matched : Option (Environment F)) (test : F)
    (bindings : Environment F) : Prop :=
  (matched = some bindings ∧ test = 1) ∨ (matched = none ∧ test = 0)

mutual
  /-- The actual recursive lowering computes the whole pattern's exact indicator and bindings. -/
  theorem lowerPattern_sound [Field F] [DecidableEq F]
      {pattern : Pattern F} {value : Symbolic F} {test : ArithExpr F} {bindings : Locals F}
      {before after : BuildState F}
      (compiled : lowerPattern pattern value before = .ok ((test, bindings), after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
      before.Valid calls assignment ∧ PatternTest
        (pattern.bindings (value.map (ArithExpr.denote assignment)))
        (test.denote assignment) (localsEnvironment bindings assignment) := by
    cases pattern with
    | wildcard =>
        simp only [lowerPattern, pure_ok, Prod.mk.injEq] at compiled
        rcases compiled with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨valid, Or.inl ⟨by simp [Pattern.bindings, localsEnvironment], rfl⟩⟩
    | bind name =>
        simp only [lowerPattern, pure_ok, Prod.mk.injEq] at compiled
        rcases compiled with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨valid, Or.inl ⟨by simp [Pattern.bindings, localsEnvironment], rfl⟩⟩
    | literal literal =>
        cases value with
        | tuple values => simp [lowerPattern] at compiled
        | field value =>
            simp only [lowerPattern] at compiled
            obtain ⟨test, middle, tested, finished⟩ := bind_ok.mp compiled
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
            obtain ⟨valid, exactTest⟩ := equalIndicator_sound tested valid
            refine ⟨valid, ?_⟩
            by_cases same : literal = value.denote assignment
            · exact Or.inl ⟨by simp [Value.map, Pattern.bindings, same, localsEnvironment],
                by simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, same] using exactTest⟩
            · exact Or.inr ⟨by simp [Value.map, Pattern.bindings, same],
                by simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote,
                  sub_eq_zero, Ne.symm same] using exactTest⟩
    | tuple patterns =>
        cases value with
        | field value => simp [lowerPattern] at compiled
        | tuple values =>
            simp only [lowerPattern] at compiled
            simpa only [Value.map, Pattern.bindings] using lowerPatterns_sound compiled valid
  termination_by sizeOf pattern

  theorem lowerPatterns_sound [Field F] [DecidableEq F]
      {patterns : List (Pattern F)} {values : List (Symbolic F)}
      {test : ArithExpr F} {bindings : Locals F} {before after : BuildState F}
      (compiled : lowerPatterns patterns values before = .ok ((test, bindings), after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid calls assignment) :
      before.Valid calls assignment ∧ PatternTest
        (Pattern.bindingsList patterns (values.map (Value.map (ArithExpr.denote assignment))))
        (test.denote assignment) (localsEnvironment bindings assignment) := by
    cases patterns with
    | nil =>
        cases values with
        | nil =>
            simp only [lowerPatterns, pure_ok, Prod.mk.injEq] at compiled
            rcases compiled with ⟨⟨rfl, rfl⟩, rfl⟩
            exact ⟨valid, Or.inl ⟨by simp [Pattern.bindingsList, localsEnvironment], rfl⟩⟩
        | cons => simp [lowerPatterns] at compiled
    | cons pattern patterns =>
        cases values with
        | nil => simp [lowerPatterns] at compiled
        | cons value values =>
            simp only [lowerPatterns] at compiled
            obtain ⟨⟨head, headBindings⟩, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨⟨tail, tailBindings⟩, last, tailRun, finished⟩ := bind_ok.mp rest
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
            obtain ⟨middleValid, tailTest⟩ := lowerPatterns_sound tailRun valid
            obtain ⟨beforeValid, headTest⟩ := lowerPattern_sound headRun middleValid
            refine ⟨beforeValid, ?_⟩
            rcases headTest with ⟨headMatch, headOne⟩ | ⟨headMatch, headZero⟩ <;>
              rcases tailTest with ⟨tailMatch, tailOne⟩ | ⟨tailMatch, tailZero⟩ <;>
              simp [PatternTest, Pattern.bindingsList, ArithExpr.denote,
                Scalar.Circuit.ArithExpr.denote, localsEnvironment_append, *]
  termination_by sizeOf patterns
end

end Aiur.Tuple.Circuit.Compiler
