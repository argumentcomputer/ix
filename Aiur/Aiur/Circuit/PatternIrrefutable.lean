import Aiur.Circuit.PatternCorrectness

namespace Aiur.Circuit.Compiler

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

mutual
  /-- An irrefutable pattern lowered for a canonical input always collects bindings. -/
  theorem lowerPattern_matches [Field F] [DecidableEq F] {decls : Declarations}
      (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
      {pattern : Pattern F} {wire : Symbolic F} {test : ArithExpr F} {bindings : Locals F}
      {before after : BuildState F}
      (compiled : lowerPattern decls pattern wire before = .ok ((test, bindings), after))
      (irrefutable : pattern.irrefutable decls = true) {assignment : Var → F} {value : Value F}
      (decoded : (wire.map (ArithExpr.denote assignment)).decode decls = some value) :
      ∃ values, pattern.bindings value = some values := by
    cases pattern with
    | wildcard => exact ⟨[], by simp [Pattern.bindings]⟩
    | bind name => exact ⟨[(name, value)], by simp [Pattern.bindings]⟩
    | literal => simp [Pattern.irrefutable] at irrefutable
    | tuple patterns =>
        rcases wire with ⟨type, words⟩
        cases type with
        | field | ptr | enum => simp [lowerPattern] at compiled
        | tuple types =>
            simp only [lowerPattern] at compiled
            obtain ⟨wires, middle, splitRun, patternRun⟩ := bind_ok.mp compiled
            obtain ⟨values, rfl, valuesDecoded⟩ := splitValues_decode checked splitRun decoded
            simpa only [Pattern.bindings] using lowerPatterns_matches checked tags patternRun
              (by simpa [Pattern.irrefutable] using irrefutable) valuesDecoded
    | construct name ctor patterns =>
        simp only [lowerPattern] at compiled
        split at compiled
        · simp [StateT.bind, bind, Except.bind] at compiled
        · rename_i typeEq
          have typeEq : wire.type = .enum name := by simpa using typeEq
          obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
          obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
          cases found : decls.findEnum? name with
          | none => simp [found] at rest
          | some definition =>
              simp only [found] at rest
              cases atIndex : definition.constructors[definition.constructors.findIdx (·.name == ctor)]? with
              | none => simp [atIndex] at rest
              | some constructor =>
                  simp only [atIndex] at rest
                  have ctorName : constructor.name = ctor := by simpa using List.findIdx_of_getElem?_eq_some atIndex
                  have only : definition.constructors = [constructor] ∧
                      (∀ p ∈ patterns, p.irrefutable decls = true) := by
                    rcases definition with ⟨defName, ctors⟩
                    cases ctors with
                    | nil => simp [Pattern.irrefutable, found] at irrefutable
                    | cons first others =>
                        cases others with
                        | cons => simp [Pattern.irrefutable, found] at irrefutable
                        | nil =>
                            simp only [Pattern.irrefutable, found, Bool.and_eq_true, beq_iff_eq,
                              List.all_eq_true, List.mem_map, forall_exists_index, and_imp] at irrefutable
                            have same : first = constructor := by
                              simpa [List.findIdx_cons, irrefutable.1] using atIndex
                            subst first
                            exact ⟨rfl, by simpa using irrefutable.2⟩
                  rcases wire with ⟨type, words⟩
                  dsimp only at typeEq
                  subst type
                  cases parts : Layout.enumParts definition.constructors.length (.const 0) words with
                  | none => simp [parts] at rest
                  | some pair =>
                      rcases pair with ⟨tag, payload⟩
                      simp only [parts] at rest
                      obtain ⟨layout, s₁, layoutRun, rest⟩ := bind_ok.mp rest
                      obtain ⟨expansion, rfl⟩ := getLayout_eq layoutRun
                      obtain ⟨values, s₂, splitRun, rest⟩ := bind_ok.mp rest
                      obtain ⟨tagTest, s₃, tagRun, rest⟩ := bind_ok.mp rest
                      obtain ⟨⟨payloadTest, payloadBindings⟩, s₄, payloadRun, finished⟩ := bind_ok.mp rest
                      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
                      obtain ⟨actual, args, rfl, _, payloadDecoded⟩ :=
                        enum_payload_decoded checked tags found atIndex expansion parts splitRun decoded
                      have formed := (WireValue.decode_spec decoded).2.1
                      have same : actual = ctor := by
                        by_contra different
                        simp [Value.wellFormed, Declarations.findConstructor?, found, only.1,
                          ctorName, Ne.symm different] at formed
                      obtain ⟨values, matched⟩ := lowerPatterns_matches checked tags payloadRun only.2
                        (payloadDecoded (same.trans ctorName.symm))
                      exact ⟨values, by simpa [Pattern.bindings, same] using matched⟩
  termination_by sizeOf pattern

  theorem lowerPatterns_matches [Field F] [DecidableEq F] {decls : Declarations}
      (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
      {patterns : List (Pattern F)} {wires : List (Symbolic F)}
      {test : ArithExpr F} {bindings : Locals F} {before after : BuildState F}
      (compiled : lowerPatterns decls patterns wires before = .ok ((test, bindings), after))
      (irrefutable : ∀ pattern ∈ patterns, pattern.irrefutable decls = true)
      {assignment : Var → F} {values : List (Value F)}
      (decoded : DecodesValues decls (wires.map (WireValue.map (ArithExpr.denote assignment))) values) :
      ∃ bindings, Pattern.bindingsList patterns values = some bindings := by
    cases patterns with
    | nil =>
        cases wires with
        | cons => simp [lowerPatterns] at compiled
        | nil => cases decoded; exact ⟨[], by simp [Pattern.bindingsList]⟩
    | cons pattern patterns =>
        cases wires with
        | nil => simp [lowerPatterns] at compiled
        | cons wire wires =>
            simp only [lowerPatterns] at compiled
            obtain ⟨⟨head, headBindings⟩, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨⟨tail, tailBindings⟩, last, tailRun, finished⟩ := bind_ok.mp rest
            cases decoded with
            | cons headDecode tailDecode =>
                obtain ⟨head, matchedHead⟩ := lowerPattern_matches checked tags headRun (irrefutable _ (by simp)) headDecode
                obtain ⟨tail, matchedTail⟩ := lowerPatterns_matches checked tags tailRun
                  (fun p h => irrefutable p (by simp [h])) tailDecode
                exact ⟨head ++ tail, by simp [Pattern.bindingsList, matchedHead, matchedTail]⟩
  termination_by sizeOf patterns
end

theorem lowerPattern_irrefutable [Field F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
    {pattern : Pattern F} {wire : Symbolic F} {test : ArithExpr F} {bindings : Locals F}
    {before after : BuildState F}
    (compiled : lowerPattern decls pattern wire before = .ok ((test, bindings), after))
    (irrefutable : pattern.irrefutable decls = true) {rom : WireROM F} {calls : CallRelation F}
    {assignment : Var → F} (valid : after.Valid rom calls assignment) {value : Value F}
    (decoded : (wire.map (ArithExpr.denote assignment)).decode decls = some value) : test.denote assignment = 1 := by
  obtain ⟨values, matched⟩ := lowerPattern_matches checked tags compiled irrefutable decoded
  have exactTest := (lowerPattern_sound checked tags compiled valid).2.2 value decoded
  rcases exactTest with ⟨_, _, one, _⟩ | ⟨absent, _⟩
  · exact one
  · rw [matched] at absent; cases absent

end Aiur.Circuit.Compiler
