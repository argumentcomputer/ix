import Aiur.Optimized.PrimitiveWitness
import Aiur.Optimized.PatternCorrectness

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
open Circuit.Compiler (Bounded LocalsBounded)

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem splitValues_bounded {decls : Declarations} {types : List Ty} {words : List (Polynomial F)}
    {values : List (Symbolic F)} {before after : State F}
    (compiled : splitValues decls types words before = .ok (values, after)) {bound : Nat}
    (bounded : ∀ word ∈ words, word.inBounds bound = true) :
    ∀ value ∈ values, Bounded bound value :=
  Circuit.Compiler.splitValues_bounded ((splitValues_reference compiled).2 {}) bounded

mutual
  /-- Optimized patterns are static polynomial views and allocate no witnesses. -/
  theorem pattern_bounded {decls : Declarations} {pat : Pattern F} {wire : Symbolic F}
      {conditions : List (Polynomial F)} {bindings : Locals F} {before after : State F}
      (compiled : pattern decls pat wire before = .ok ((conditions, bindings), after))
      {bound : Nat} (bounded : Bounded bound wire) :
      after = before ∧ (∀ condition ∈ conditions, condition.inBounds bound = true) ∧
        LocalsBounded bound bindings := by
    cases pat with
    | wildcard =>
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [pattern] using compiled)
        exact ⟨rfl, by simp, by simp [LocalsBounded]⟩
    | bind name =>
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [pattern] using compiled)
        exact ⟨rfl, by simp, by simpa [LocalsBounded] using bounded⟩
    | literal literal =>
        rcases wire with ⟨type, words⟩
        cases type with
        | tuple | ptr | enum => simp [pattern] at compiled
        | field =>
            cases words with
            | nil => simp [pattern] at compiled
            | cons word rest => cases rest with
              | cons => simp [pattern] at compiled
              | nil =>
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [pattern] using compiled)
                  exact ⟨rfl, by simpa [Scalar.Circuit.ArithExpr.inBounds] using bounded word (by simp),
                    by simp [LocalsBounded]⟩
    | tuple patterns =>
        rcases wire with ⟨type, words⟩
        cases type with
        | field | ptr | enum => simp [pattern] at compiled
        | tuple types =>
            simp only [pattern] at compiled
            obtain ⟨wires, middle, splitRun, patternRun⟩ := bind_ok.mp compiled
            obtain ⟨rfl, _⟩ := splitValues_reference splitRun
            exact patternList_bounded patternRun (splitValues_bounded splitRun bounded)
    | construct name ctor patterns =>
        simp only [pattern] at compiled
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
                      obtain ⟨layout, afterLayout, layoutRun, afterLayoutBind⟩ := bind_ok.mp rest
                      obtain ⟨_, stateEq⟩ := getLayout_eq layoutRun
                      subst afterLayout
                      obtain ⟨values, afterSplit, splitRun, afterSplitBind⟩ := bind_ok.mp afterLayoutBind
                      obtain ⟨stateEq, _⟩ := splitValues_reference splitRun
                      subst afterSplit
                      obtain ⟨⟨payloadConditions, payloadBindings⟩, afterPatterns, payloadRun, finished⟩ :=
                        bind_ok.mp afterSplitBind
                      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
                      obtain ⟨unchanged, payloadBound, bindingsBound⟩ := patternList_bounded payloadRun
                        (splitValues_bounded splitRun
                          (fun p member => tailBound p (List.mem_of_mem_take member)))
                      refine ⟨unchanged, ?_, bindingsBound⟩
                      intro p member
                      rcases List.mem_cons.mp member with rfl | member
                      · simpa [Scalar.Circuit.ArithExpr.inBounds] using headBound
                      · exact payloadBound p member
  termination_by sizeOf pat

  theorem patternList_bounded {decls : Declarations} {patterns : List (Pattern F)}
      {values : List (Symbolic F)} {conditions : List (Polynomial F)} {bindings : Locals F}
      {before after : State F}
      (compiled : patternList decls patterns values before = .ok ((conditions, bindings), after))
      {bound : Nat} (bounded : ∀ value ∈ values, Bounded bound value) :
      after = before ∧ (∀ condition ∈ conditions, condition.inBounds bound = true) ∧
        LocalsBounded bound bindings := by
    cases patterns with
    | nil =>
        cases values with
        | nil =>
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [patternList] using compiled)
            exact ⟨rfl, by simp, by simp [LocalsBounded]⟩
        | cons => simp [patternList] at compiled
    | cons pat patterns =>
        cases values with
        | nil => simp [patternList] at compiled
        | cons value values =>
            simp only [patternList] at compiled
            obtain ⟨⟨head, headBindings⟩, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨⟨tail, tailBindings⟩, last, tailRun, finished⟩ := bind_ok.mp rest
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
            obtain ⟨rfl, headBound, headLocals⟩ := pattern_bounded headRun (bounded value (by simp))
            obtain ⟨rfl, tailBound, tailLocals⟩ := patternList_bounded tailRun
              (fun value member => bounded value (by simp [member]))
            exact ⟨rfl, by simpa only [List.forall_mem_append] using And.intro headBound tailBound,
              Circuit.Compiler.localsBounded_append.mpr ⟨headLocals, tailLocals⟩⟩
  termination_by sizeOf patterns
end

end Aiur.Optimized.Compiler
