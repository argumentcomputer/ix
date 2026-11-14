import Aiur.Tuple.Circuit.ValueWitness

namespace Aiur.Tuple.Circuit.Compiler

theorem equalIndicator_complete [Field F] [DecidableEq F]
    {difference test : ArithExpr F} {before after : BuildState F}
    (compiled : equalIndicator difference before = .ok (test, after))
    {calls : CallRelation F} {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid calls initial)
    (bounded : difference.inBounds before.nextVar = true) :
    ∃ assignment, Extension calls before after initial assignment ∧
      test.inBounds after.nextVar = true := by
  simp [equalIndicator, StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
  obtain ⟨rfl, rfl⟩ := compiled
  let equal : F := if difference.denote initial = 0 then 1 else 0
  let assignment := Function.update (Function.update initial before.nextVar equal)
    (before.nextVar + 1) (difference.denote initial)⁻¹
  have agree : ∀ id < before.nextVar, assignment id = initial id := by
    intro id bound
    simp [assignment, Function.update_of_ne (by omega : id ≠ before.nextVar + 1),
      Function.update_of_ne (by omega : id ≠ before.nextVar)]
  have dEq : difference.denote assignment = difference.denote initial :=
    Scalar.Circuit.ArithExpr.denote_eq_of_agree agree bounded
  have eEq : assignment before.nextVar = equal := by simp [assignment]
  have uEq : assignment (before.nextVar + 1) = (difference.denote initial)⁻¹ := by simp [assignment]
  have equations := equality_indicator_complete (difference.denote initial)
  have grown := layout.grow (by omega : before.nextVar ≤ before.nextVar + 1 + 1)
  have db := Scalar.Circuit.ArithExpr.inBounds_mono
    (by omega : before.nextVar ≤ before.nextVar + 1 + 1) bounded
  have lo : before.nextVar < before.nextVar + 1 + 1 := by omega
  have hi : before.nextVar + 1 < before.nextVar + 1 + 1 := by omega
  have firstBound : (ArithExpr.mul (.var before.nextVar)
      (.sub (.var before.nextVar) (.const (1 : F)))).inBounds (before.nextVar + 1 + 1) = true := by
    simp [Scalar.Circuit.ArithExpr.inBounds, lo]
  have secondBound : (ArithExpr.mul difference (.var before.nextVar)).inBounds
      (before.nextVar + 1 + 1) = true := by
    simp [Scalar.Circuit.ArithExpr.inBounds, lo, db]
  have thirdBound : (ArithExpr.sub (.mul difference (.var (before.nextVar + 1)))
      (.sub (.const 1) (.var before.nextVar))).inBounds (before.nextVar + 1 + 1) = true := by
    simp [Scalar.Circuit.ArithExpr.inBounds, lo, hi, db]
  have grownValid : ({ before with nextVar := before.nextVar + 1 + 1 } : BuildState F).Valid calls assignment :=
    ⟨(valid.of_agree layout agree).constraints, (valid.of_agree layout agree).calls⟩
  have firstZero : (ArithExpr.mul (.var before.nextVar)
      (.sub (.var before.nextVar) (.const (1 : F)))).denote assignment = 0 := by
    simpa only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, eEq, equal] using equations.1
  have secondZero : (ArithExpr.mul difference (.var before.nextVar)).denote assignment = 0 := by
    change difference.denote assignment * assignment before.nextVar = 0
    simpa only [dEq, eEq, equal] using equations.2.1
  have thirdZero : (ArithExpr.sub (.mul difference (.var (before.nextVar + 1)))
      (.sub (.const 1) (.var before.nextVar))).denote assignment = 0 := by
    change difference.denote assignment * assignment (before.nextVar + 1) - (1 - assignment before.nextVar) = 0
    simpa only [dEq, uEq, eEq, equal] using equations.2.2
  exact ⟨assignment, ⟨by dsimp; omega, agree,
    ((grown.constrain firstBound).constrain secondBound).constrain thirdBound,
    ((grownValid.constrain firstZero).constrain secondZero).constrain thirdZero⟩,
    by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using lo⟩

mutual
  theorem lowerPattern_complete [Field F] [DecidableEq F]
      {pattern : Pattern F} {value : Symbolic F} {test : ArithExpr F} {bindings : Locals F}
      {before after : BuildState F}
      (compiled : lowerPattern pattern value before = .ok ((test, bindings), after))
      {calls : CallRelation F} {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls initial)
      (bounded : Bounded before.nextVar value) :
      ∃ assignment, Extension calls before after initial assignment ∧
        test.inBounds after.nextVar = true ∧ LocalsBounded after.nextVar bindings := by
    cases pattern with
    | wildcard =>
        simp only [lowerPattern, pure_ok, Prod.mk.injEq] at compiled
        rcases compiled with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨initial, .refl layout valid, rfl, by simp [LocalsBounded]⟩
    | bind name =>
        simp only [lowerPattern, pure_ok, Prod.mk.injEq] at compiled
        rcases compiled with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨initial, .refl layout valid, rfl, by simpa [LocalsBounded] using bounded⟩
    | literal literal =>
        cases value with
        | tuple values => simp [lowerPattern] at compiled
        | field value =>
            simp only [lowerPattern] at compiled
            obtain ⟨test, middle, tested, finished⟩ := bind_ok.mp compiled
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
            obtain ⟨assignment, extension, bound⟩ := equalIndicator_complete tested layout valid
              (by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using bounded_field.mp bounded)
            exact ⟨assignment, extension, bound, by simp [LocalsBounded]⟩
    | tuple patterns =>
        cases value with
        | field value => simp [lowerPattern] at compiled
        | tuple values =>
            simp only [lowerPattern] at compiled
            exact lowerPatterns_complete compiled layout valid (bounded_tuple.mp bounded)
  termination_by sizeOf pattern

  theorem lowerPatterns_complete [Field F] [DecidableEq F]
      {patterns : List (Pattern F)} {values : List (Symbolic F)}
      {test : ArithExpr F} {bindings : Locals F} {before after : BuildState F}
      (compiled : lowerPatterns patterns values before = .ok ((test, bindings), after))
      {calls : CallRelation F} {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls initial)
      (bounded : ∀ value ∈ values, Bounded before.nextVar value) :
      ∃ assignment, Extension calls before after initial assignment ∧
        test.inBounds after.nextVar = true ∧ LocalsBounded after.nextVar bindings := by
    cases patterns with
    | nil =>
        cases values with
        | nil =>
            simp only [lowerPatterns, pure_ok, Prod.mk.injEq] at compiled
            rcases compiled with ⟨⟨rfl, rfl⟩, rfl⟩
            exact ⟨initial, .refl layout valid, rfl, by simp [LocalsBounded]⟩
        | cons => simp [lowerPatterns] at compiled
    | cons pattern patterns =>
        cases values with
        | nil => simp [lowerPatterns] at compiled
        | cons value values =>
            simp only [lowerPatterns] at compiled
            obtain ⟨⟨head, headBindings⟩, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨⟨tail, tailBindings⟩, last, tailRun, finished⟩ := bind_ok.mp rest
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
            obtain ⟨a, headExt, headBound, headLocals⟩ :=
              lowerPattern_complete headRun layout valid (bounded value (by simp))
            obtain ⟨b, tailExt, tailBound, tailLocals⟩ := lowerPatterns_complete tailRun
              headExt.layout headExt.valid
              (fun value member => (bounded value (by simp [member])).mono headExt.increase)
            exact ⟨b, headExt.trans tailExt, by
              simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
                And.intro (Scalar.Circuit.ArithExpr.inBounds_mono tailExt.increase headBound) tailBound,
              localsBounded_append.mpr ⟨headLocals.mono tailExt.increase, tailLocals⟩⟩
  termination_by sizeOf patterns
end

mutual
  theorem lowerPattern_irrefutable [Field F] {pattern : Pattern F} {value : Symbolic F}
      {test : ArithExpr F} {bindings : Locals F} {before after : BuildState F}
      (compiled : lowerPattern pattern value before = .ok ((test, bindings), after))
      (irrefutable : pattern.irrefutable = true) (assignment : Var → F) : test.denote assignment = 1 := by
    cases pattern with
    | wildcard | bind =>
        simp only [lowerPattern, pure_ok, Prod.mk.injEq] at compiled
        rcases compiled with ⟨⟨rfl, rfl⟩, rfl⟩
        rfl
    | literal => simp [Pattern.irrefutable] at irrefutable
    | tuple patterns =>
        cases value with
        | field => simp [lowerPattern] at compiled
        | tuple values =>
            simp only [lowerPattern] at compiled
            exact lowerPatterns_irrefutable compiled (by simpa [Pattern.irrefutable] using irrefutable) assignment
  termination_by sizeOf pattern

  theorem lowerPatterns_irrefutable [Field F] {patterns : List (Pattern F)} {values : List (Symbolic F)}
      {test : ArithExpr F} {bindings : Locals F} {before after : BuildState F}
      (compiled : lowerPatterns patterns values before = .ok ((test, bindings), after))
      (irrefutable : ∀ pattern ∈ patterns, pattern.irrefutable = true) (assignment : Var → F) :
      test.denote assignment = 1 := by
    cases patterns with
    | nil =>
        cases values with
        | nil =>
            simp only [lowerPatterns, pure_ok, Prod.mk.injEq] at compiled
            rcases compiled with ⟨⟨rfl, rfl⟩, rfl⟩
            rfl
        | cons => simp [lowerPatterns] at compiled
    | cons pattern patterns =>
        cases values with
        | nil => simp [lowerPatterns] at compiled
        | cons value values =>
            simp only [lowerPatterns] at compiled
            obtain ⟨⟨head, headBindings⟩, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨⟨tail, tailBindings⟩, last, tailRun, finished⟩ := bind_ok.mp rest
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
            have headOne := lowerPattern_irrefutable headRun (irrefutable pattern (by simp)) assignment
            have tailOne := lowerPatterns_irrefutable tailRun (fun p h => irrefutable p (by simp [h])) assignment
            change head.denote assignment * tail.denote assignment = 1
            rw [headOne, tailOne, one_mul]
  termination_by sizeOf patterns
end

end Aiur.Tuple.Circuit.Compiler
