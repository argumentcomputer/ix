import Aiur.Circuit.PatternCorrectness
import Aiur.Circuit.IndicatorWitness

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

mutual
  /-- Exact pattern tests have witnesses for every payload view, including inactive views. -/
  theorem lowerPattern_complete [Field F] [DecidableEq F] {decls : Declarations}
      {pattern : Pattern F} {wire : Symbolic F} {test : ArithExpr F} {bindings : Locals F}
      {before after : BuildState F}
      (compiled : lowerPattern decls pattern wire before = .ok ((test, bindings), after))
      {calls : CallRelation F} {initial : Var → F}
      (stateLayout : before.WellFormed) (valid : before.Valid rom calls initial)
      (bounded : Bounded before.nextVar wire) :
      ∃ assignment, Extension rom calls before after initial assignment ∧
        test.inBounds after.nextVar = true ∧ LocalsBounded after.nextVar bindings := by
    cases pattern with
    | wildcard =>
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [lowerPattern] using compiled)
        exact ⟨initial, .refl stateLayout valid, rfl, by simp [LocalsBounded]⟩
    | bind name =>
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [lowerPattern] using compiled)
        exact ⟨initial, .refl stateLayout valid, rfl, by simpa [LocalsBounded] using bounded⟩
    | literal literal =>
        rcases wire with ⟨type, words⟩
        cases type with
        | tuple | ptr | enum => simp [lowerPattern] at compiled
        | field =>
            cases words with
            | nil => simp [lowerPattern] at compiled
            | cons word rest => cases rest with
              | cons => simp [lowerPattern] at compiled
              | nil =>
                  simp only [lowerPattern] at compiled
                  obtain ⟨indicator, middle, indicatorRun, finished⟩ := bind_ok.mp compiled
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
                  obtain ⟨a, ext, bound⟩ := equalIndicator_complete indicatorRun stateLayout valid
                    (by simpa [Scalar.Circuit.ArithExpr.inBounds] using bounded word (by simp))
                  exact ⟨a, ext, bound, by simp [LocalsBounded]⟩
    | tuple patterns =>
        rcases wire with ⟨type, words⟩
        cases type with
        | field | ptr | enum => simp [lowerPattern] at compiled
        | tuple types =>
            simp only [lowerPattern] at compiled
            obtain ⟨wires, middle, splitRun, patternRun⟩ := bind_ok.mp compiled
            have unchanged := (splitValues_spec splitRun).1
            subst middle
            exact lowerPatterns_complete patternRun stateLayout valid (splitValues_bounded splitRun bounded)
    | construct name ctor patterns =>
        simp only [lowerPattern] at compiled
        split at compiled
        · simp [StateT.bind, bind, Except.bind] at compiled
        · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
          obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
          cases found : decls.findEnum? name with
          | none => simp [found] at rest
          | some definition =>
              simp only [found] at rest
              cases atIndex : definition.constructors[definition.constructors.findIdx (·.name == ctor)]? with
              | none => simp [atIndex] at rest
              | some constructor =>
                  simp only [atIndex] at rest
                  rcases wire with ⟨type, words⟩
                  cases parts : Layout.enumParts definition.constructors.length (.const 0) words with
                  | none => simp [parts] at rest
                  | some pair =>
                      rcases pair with ⟨tag, payload⟩
                      simp only [parts] at rest
                      obtain ⟨headBound, tailBound⟩ := Layout.enumParts_all parts (by rfl) bounded
                      obtain ⟨layout, s₁, layoutRun, rest⟩ := bind_ok.mp rest
                      obtain ⟨_, rfl⟩ := getLayout_eq layoutRun
                      obtain ⟨values, s₂, splitRun, rest⟩ := bind_ok.mp rest
                      have unchanged := (splitValues_spec splitRun).1
                      subst s₂
                      obtain ⟨tagTest, s₃, tagRun, rest⟩ := bind_ok.mp rest
                      obtain ⟨⟨payloadTest, payloadBindings⟩, s₄, payloadRun, finished⟩ := bind_ok.mp rest
                      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
                      obtain ⟨a, tagExt, tagBound⟩ := equalIndicator_complete tagRun stateLayout valid
                        (by simpa [Scalar.Circuit.ArithExpr.inBounds] using headBound)
                      have valuesBound := splitValues_bounded splitRun (bound := before.nextVar)
                        (fun p h => tailBound p (List.mem_of_mem_take h))
                      obtain ⟨b, payloadExt, payloadBound, localsBound⟩ := lowerPatterns_complete payloadRun
                        tagExt.layout tagExt.valid (fun w h => (valuesBound w h).mono tagExt.increase)
                      exact ⟨b, tagExt.trans payloadExt, by
                        simpa [Scalar.Circuit.ArithExpr.inBounds] using
                          And.intro (payloadExt.bound tagBound) payloadBound, localsBound⟩
  termination_by sizeOf pattern

  theorem lowerPatterns_complete [Field F] [DecidableEq F] {decls : Declarations}
      {patterns : List (Pattern F)} {values : List (Symbolic F)}
      {test : ArithExpr F} {bindings : Locals F} {before after : BuildState F}
      (compiled : lowerPatterns decls patterns values before = .ok ((test, bindings), after))
      {calls : CallRelation F} {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid rom calls initial)
      (bounded : ∀ value ∈ values, Bounded before.nextVar value) :
      ∃ assignment, Extension rom calls before after initial assignment ∧
        test.inBounds after.nextVar = true ∧ LocalsBounded after.nextVar bindings := by
    cases patterns with
    | nil =>
        cases values with
        | nil =>
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [lowerPatterns] using compiled)
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
                And.intro (tailExt.bound headBound) tailBound,
              localsBounded_append.mpr ⟨headLocals.mono tailExt.increase, tailLocals⟩⟩
  termination_by sizeOf patterns
end

end Aiur.Circuit.Compiler
