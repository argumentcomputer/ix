import Aiur.Circuit.PatternEncoding
import Aiur.Circuit.Indicator

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

/-- On a match, the symbolic bindings decode to exactly the source bindings. -/
def PatternTest [Field F] [DecidableEq F] (decls : Declarations)
    (matched : Option (Environment F)) (test : F) (bindings : WireEnvironment F) : Prop :=
  (∃ values, matched = some values ∧ test = 1 ∧ DecodesEnvironment decls bindings values) ∨
    (matched = none ∧ test = 0)

mutual
  /-- Pattern tests are Boolean even for inactive, noncanonical payload views. -/
  theorem lowerPattern_sound [Field F] [DecidableEq F] {decls : Declarations}
      (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
      {pattern : Pattern F} {wire : Symbolic F} {test : ArithExpr F} {bindings : Locals F}
      {before after : BuildState F}
      (compiled : lowerPattern decls pattern wire before = .ok ((test, bindings), after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
      before.Valid rom calls assignment ∧ (test.denote assignment = 0 ∨ test.denote assignment = 1) ∧
        ∀ value, (wire.map (ArithExpr.denote assignment)).decode decls = some value →
          PatternTest decls (pattern.bindings value) (test.denote assignment)
            (localsEnvironment bindings assignment) := by
    cases pattern with
    | wildcard =>
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [lowerPattern] using compiled)
        exact ⟨valid, Or.inr rfl, fun value _ => Or.inl ⟨[], by simp [Pattern.bindings], rfl, .nil⟩⟩
    | bind name =>
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [lowerPattern] using compiled)
        exact ⟨valid, Or.inr rfl, fun value decoded => Or.inl
          ⟨[(name, value)], by simp [Pattern.bindings], rfl, .cons ⟨rfl, decoded⟩ .nil⟩⟩
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
                  obtain ⟨previous, exactTest⟩ := equalIndicator_sound indicatorRun valid
                  have exactTest : test.denote assignment =
                      if literal = word.denote assignment then 1 else 0 := by
                    change test.denote assignment =
                      (if word.denote assignment - literal = 0 then 1 else 0) at exactTest
                    simp only [sub_eq_zero] at exactTest
                    simpa only [eq_comm] using exactTest
                  refine ⟨previous, ?_, ?_⟩
                  · rw [exactTest]; split <;> simp
                  · intro value decoded
                    have same : Value.field (word.denote assignment) = value := by
                      change (WireValue.field (word.denote assignment)).decode decls = some value at decoded
                      simpa only [WireValue.decode_field, Option.some.injEq] using decoded
                    subst value
                    by_cases matched : literal = word.denote assignment
                    · exact Or.inl ⟨[], by simp [Pattern.bindings, matched], by simp [exactTest, matched], .nil⟩
                    · exact Or.inr ⟨by simp [Pattern.bindings, matched], by simp [exactTest, matched]⟩
    | tuple patterns =>
        rcases wire with ⟨type, words⟩
        cases type with
        | field | ptr | enum => simp [lowerPattern] at compiled
        | tuple types =>
            simp only [lowerPattern] at compiled
            obtain ⟨wires, middle, splitRun, patternRun⟩ := bind_ok.mp compiled
            have unchanged := (splitValues_spec splitRun).1
            subst middle
            obtain ⟨previous, boolean, matched⟩ := lowerPatterns_sound checked tags patternRun valid
            refine ⟨previous, boolean, fun value decoded => ?_⟩
            obtain ⟨values, rfl, valuesDecoded⟩ := splitValues_decode checked splitRun decoded
            simpa only [Pattern.bindings] using matched values valuesDecoded
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
                  have ctorName : constructor.name = ctor := by
                    simpa using List.findIdx_of_getElem?_eq_some atIndex
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
                      have unchanged := (splitValues_spec splitRun).1
                      subst s₂
                      obtain ⟨tagTest, s₃, tagRun, rest⟩ := bind_ok.mp rest
                      obtain ⟨⟨payloadTest, payloadBindings⟩, s₄, payloadRun, finished⟩ := bind_ok.mp rest
                      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
                      obtain ⟨s₃valid, payloadBoolean, payloadMatched⟩ := lowerPatterns_sound checked tags payloadRun valid
                      obtain ⟨previous, tagEq⟩ := equalIndicator_sound tagRun s₃valid
                      have tagEq : tagTest.denote assignment =
                          if tag.denote assignment = ((definition.constructors.findIdx (·.name == ctor) : Nat) : F)
                          then 1 else 0 := by
                        simpa [Scalar.Circuit.ArithExpr.denote, sub_eq_zero] using tagEq
                      refine ⟨previous, ?_, ?_⟩
                      · change tagTest.denote assignment * payloadTest.denote assignment = 0 ∨
                          tagTest.denote assignment * payloadTest.denote assignment = 1
                        rw [tagEq]
                        split <;> simpa using payloadBoolean
                      · intro value decoded
                        obtain ⟨actual, args, rfl, tagMatch, payloadDecoded⟩ :=
                          enum_payload_decoded checked tags found atIndex expansion parts splitRun decoded
                        rw [ctorName] at tagMatch payloadDecoded
                        by_cases same : actual = ctor
                        · have selected := tagMatch.mpr same
                          have matched := payloadMatched args (payloadDecoded same)
                          subst actual
                          simpa [PatternTest, Pattern.bindings, tagEq, selected, Scalar.Circuit.ArithExpr.denote]
                            using matched
                        · exact Or.inr ⟨by simp [Pattern.bindings, Ne.symm same],
                            by simp [Scalar.Circuit.ArithExpr.denote, tagEq, mt tagMatch.mp same]⟩
  termination_by sizeOf pattern

  theorem lowerPatterns_sound [Field F] [DecidableEq F] {decls : Declarations}
      (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
      {patterns : List (Pattern F)} {wires : List (Symbolic F)}
      {test : ArithExpr F} {bindings : Locals F} {before after : BuildState F}
      (compiled : lowerPatterns decls patterns wires before = .ok ((test, bindings), after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
      before.Valid rom calls assignment ∧ (test.denote assignment = 0 ∨ test.denote assignment = 1) ∧
        ∀ values, DecodesValues decls (wires.map (WireValue.map (ArithExpr.denote assignment))) values →
          PatternTest decls (Pattern.bindingsList patterns values) (test.denote assignment)
            (localsEnvironment bindings assignment) := by
    cases patterns with
    | nil =>
        cases wires with
        | nil =>
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [lowerPatterns] using compiled)
            refine ⟨valid, Or.inr rfl, fun values decoded => ?_⟩
            cases decoded
            exact Or.inl ⟨[], by simp [Pattern.bindingsList], rfl, .nil⟩
        | cons => simp [lowerPatterns] at compiled
    | cons pattern patterns =>
        cases wires with
        | nil => simp [lowerPatterns] at compiled
        | cons wire wires =>
            simp only [lowerPatterns] at compiled
            obtain ⟨⟨head, headBindings⟩, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨⟨tail, tailBindings⟩, last, tailRun, finished⟩ := bind_ok.mp rest
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
            obtain ⟨middleValid, tailBoolean, tailTest⟩ := lowerPatterns_sound checked tags tailRun valid
            obtain ⟨beforeValid, headBoolean, headTest⟩ := lowerPattern_sound checked tags headRun middleValid
            refine ⟨beforeValid, ?_, ?_⟩
            · change head.denote assignment * tail.denote assignment = 0 ∨
                head.denote assignment * tail.denote assignment = 1
              rcases headBoolean with zero | one
              · simp [zero]
              · simpa [one] using tailBoolean
            · intro values decoded
              cases decoded with
              | cons headDecode tailDecode =>
                  rcases headTest _ headDecode with ⟨headValues, headMatch, headOne, headDecoded⟩ | ⟨headMatch, headZero⟩ <;>
                    rcases tailTest _ tailDecode with ⟨tailValues, tailMatch, tailOne, tailDecoded⟩ | ⟨tailMatch, tailZero⟩
                  · exact Or.inl ⟨headValues ++ tailValues, by simp [Pattern.bindingsList, headMatch, tailMatch],
                      by simp [Scalar.Circuit.ArithExpr.denote, headOne, tailOne],
                      by simpa only [localsEnvironment_append] using headDecoded.append tailDecoded⟩
                  · exact Or.inr ⟨by simp [Pattern.bindingsList, headMatch, tailMatch],
                      by simp [Scalar.Circuit.ArithExpr.denote, tailZero]⟩
                  · exact Or.inr ⟨by simp [Pattern.bindingsList, headMatch],
                      by simp [Scalar.Circuit.ArithExpr.denote, headZero]⟩
                  · exact Or.inr ⟨by simp [Pattern.bindingsList, headMatch],
                      by simp [Scalar.Circuit.ArithExpr.denote, headZero]⟩
  termination_by sizeOf patterns
end

end Aiur.Circuit.Compiler
