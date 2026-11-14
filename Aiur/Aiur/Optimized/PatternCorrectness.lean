import Aiur.Optimized.BuildFacts
import Aiur.Optimized.BranchFacts

namespace Aiur.Optimized.Compiler

open Circuit.Compiler (localsEnvironment localsEnvironment_append)

variable {F : Type} [Field F] [DecidableEq F]
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def AllZero (conditions : List (Polynomial F)) (assignment : Witness → F) : Prop :=
  ∀ condition ∈ conditions, condition.denote assignment = 0

@[simp] theorem allZero_append (left right : List (Polynomial F)) (assignment : Witness → F) :
    AllZero (left ++ right) assignment ↔ AllZero left assignment ∧ AllZero right assignment := by
  simp only [AllZero, List.forall_mem_append]

/-- Conditions are a conjunction, so a failed constructor tag suffices without
interpreting a payload using the wrong constructor's layout. -/
def PatternMeaning (decls : Declarations) (matched : Option (Environment F))
    (conditions : List (Polynomial F)) (bindings : Locals F) (assignment : Witness → F) : Prop :=
  (∃ environment, matched = some environment ∧ AllZero conditions assignment ∧
    DecodesEnvironment decls (localsEnvironment bindings assignment) environment) ∨
  (matched = none ∧ ¬ AllZero conditions assignment)

mutual
  theorem pattern_correct {decls : Declarations} (checked : checkDeclarations decls = .ok ())
      (tags : decls.tagsValid F = true) {pat : Pattern F} {wire : Symbolic F}
      {conditions : List (Polynomial F)} {bindings : Locals F} {before after : State F}
      (compiled : pattern decls pat wire before = .ok ((conditions, bindings), after)) :
      after = before ∧ ∀ assignment value,
        (wire.map (Circuit.ArithExpr.denote assignment)).decode decls = some value →
        PatternMeaning decls (pat.bindings value) conditions bindings assignment := by
    cases pat with
    | wildcard =>
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [pattern] using compiled)
        exact ⟨rfl, fun _ _ _ => Or.inl ⟨[], by simp [Pattern.bindings], by simp [AllZero], .nil⟩⟩
    | bind name =>
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [pattern] using compiled)
        exact ⟨rfl, fun _ value decoded => Or.inl
          ⟨[(name, value)], by simp [Pattern.bindings], by simp [AllZero], .cons ⟨rfl, decoded⟩ .nil⟩⟩
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
                  refine ⟨rfl, fun assignment value decoded => ?_⟩
                  have same : Value.field (word.denote assignment) = value := by
                    change (WireValue.field (word.denote assignment)).decode decls = some value at decoded
                    simpa only [WireValue.decode_field, Option.some.injEq] using decoded
                  subst value
                  by_cases matched : literal = word.denote assignment
                  · exact Or.inl ⟨[], by simp [Pattern.bindings, matched],
                      by simp [AllZero, Scalar.Circuit.ArithExpr.denote, ← matched], .nil⟩
                  · refine Or.inr ⟨by simp [Pattern.bindings, matched], ?_⟩
                    intro allZero
                    exact matched (sub_eq_zero.mp (allZero _ (List.mem_singleton_self _))).symm
    | tuple patterns =>
        rcases wire with ⟨type, words⟩
        cases type with
        | field | ptr | enum => simp [pattern] at compiled
        | tuple types =>
            simp only [pattern] at compiled
            obtain ⟨wires, middle, splitRun, patternRun⟩ := bind_ok.mp compiled
            obtain ⟨rfl, reference⟩ := splitValues_reference splitRun
            obtain ⟨unchanged, meaning⟩ := patternList_correct checked tags patternRun
            refine ⟨unchanged, fun assignment value decoded => ?_⟩
            obtain ⟨values, rfl, valuesDecoded⟩ := Circuit.Compiler.splitValues_decode checked (reference {}) decoded
            simpa only [Pattern.bindings] using meaning assignment values valuesDecoded
    | construct name ctor patterns =>
        simp only [pattern] at compiled
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
                      obtain ⟨layout, s₁, layoutRun, afterLayout⟩ := bind_ok.mp rest
                      obtain ⟨expansion, stateEq⟩ := getLayout_eq layoutRun
                      subst s₁
                      obtain ⟨values, s₂, splitRun, afterSplit⟩ := bind_ok.mp afterLayout
                      obtain ⟨stateEq, reference⟩ := splitValues_reference splitRun
                      subst s₂
                      obtain ⟨⟨payloadConditions, payloadBindings⟩, s₃, payloadRun, finished⟩ := bind_ok.mp afterSplit
                      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
                      obtain ⟨unchanged, payloadMeaning⟩ := patternList_correct checked tags payloadRun
                      refine ⟨unchanged, fun assignment value decoded => ?_⟩
                      obtain ⟨actual, args, rfl, tagMatch, payloadDecoded⟩ :=
                        Circuit.Compiler.enum_payload_decoded checked tags found atIndex expansion parts (reference {}) decoded
                      rw [ctorName] at tagMatch payloadDecoded
                      by_cases same : actual = ctor
                      · have selected := tagMatch.mpr same
                        have meaning := payloadMeaning assignment args (payloadDecoded same)
                        subst actual
                        simpa [PatternMeaning, Pattern.bindings, AllZero, selected,
                          Scalar.Circuit.ArithExpr.denote] using meaning
                      · refine Or.inr ⟨by simp [Pattern.bindings, Ne.symm same], ?_⟩
                        intro allZero
                        have tagZero := allZero _ (List.mem_cons_self ..)
                        change tag.denote assignment - _ = 0 at tagZero
                        exact same (tagMatch.mp (sub_eq_zero.mp tagZero))
  termination_by sizeOf pat

  theorem patternList_correct {decls : Declarations} (checked : checkDeclarations decls = .ok ())
      (tags : decls.tagsValid F = true) {patterns : List (Pattern F)} {wires : List (Symbolic F)}
      {conditions : List (Polynomial F)} {bindings : Locals F} {before after : State F}
      (compiled : patternList decls patterns wires before = .ok ((conditions, bindings), after)) :
      after = before ∧ ∀ assignment values,
        DecodesValues decls (wires.map (WireValue.map (Circuit.ArithExpr.denote assignment))) values →
        PatternMeaning decls (Pattern.bindingsList patterns values) conditions bindings assignment := by
    cases patterns with
    | nil =>
        cases wires with
        | nil =>
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp (by simpa only [patternList] using compiled)
            refine ⟨rfl, fun _ values decoded => ?_⟩
            cases decoded
            exact Or.inl ⟨[], by simp [Pattern.bindingsList], by simp [AllZero], .nil⟩
        | cons => simp [patternList] at compiled
    | cons pat patterns =>
        cases wires with
        | nil => simp [patternList] at compiled
        | cons wire wires =>
            simp only [patternList] at compiled
            obtain ⟨⟨head, headBindings⟩, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨⟨tail, tailBindings⟩, last, tailRun, finished⟩ := bind_ok.mp rest
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
            obtain ⟨rfl, headMeaning⟩ := pattern_correct checked tags headRun
            obtain ⟨rfl, tailMeaning⟩ := patternList_correct checked tags tailRun
            refine ⟨rfl, fun assignment values decoded => ?_⟩
            cases decoded with
            | cons headDecoded tailDecoded =>
              rcases headMeaning assignment _ headDecoded with
                ⟨headValues, headMatch, headZero, headBindingsDecode⟩ | ⟨headMatch, headNonzero⟩ <;>
                rcases tailMeaning assignment _ tailDecoded with
                  ⟨tailValues, tailMatch, tailZero, tailBindingsDecode⟩ | ⟨tailMatch, tailNonzero⟩
              · exact Or.inl ⟨headValues ++ tailValues, by simp [Pattern.bindingsList, headMatch, tailMatch],
                  (allZero_append _ _ _).mpr ⟨headZero, tailZero⟩,
                  by simpa only [localsEnvironment_append] using headBindingsDecode.append tailBindingsDecode⟩
              · exact Or.inr ⟨by simp [Pattern.bindingsList, headMatch, tailMatch],
                  fun allZero => tailNonzero ((allZero_append _ _ _).mp allZero).2⟩
              · exact Or.inr ⟨by simp [Pattern.bindingsList, headMatch],
                  fun allZero => headNonzero ((allZero_append _ _ _).mp allZero).1⟩
              · exact Or.inr ⟨by simp [Pattern.bindingsList, headMatch],
                  fun allZero => headNonzero ((allZero_append _ _ _).mp allZero).1⟩
  termination_by sizeOf patterns
end

/-- Exact rejection of an earlier pattern by the optimized linear failure
certificate, including nested tuples and enum patterns. -/
theorem pattern_failure_iff {decls : Declarations} (checked : checkDeclarations decls = .ok ())
    (tags : decls.tagsValid F = true) {pat : Pattern F} {wire : Symbolic F}
    {conditions : List (Polynomial F)} {bindings : Locals F} {before after : State F}
    (compiled : pattern decls pat wire before = .ok ((conditions, bindings), after))
    {assignment : Witness → F} {value : Value F}
    (decoded : (wire.map (Circuit.ArithExpr.denote assignment)).decode decls = some value) :
    (∃ coefficients, coefficients.length = conditions.length ∧
      combination (conditions.map (Circuit.ArithExpr.denote assignment)) coefficients = 1) ↔
      pat.bindings value = none := by
  have algebra := failure_certificate_iff (conditions.map (Circuit.ArithExpr.denote assignment))
  simp only [List.length_map, List.forall_mem_map] at algebra
  rw [algebra]
  rcases (pattern_correct checked tags compiled).2 assignment value decoded with
    ⟨environment, matched, allZero, _⟩ | ⟨matched, nonzero⟩
  · simp only [matched, Option.some_ne_none, iff_false]
    exact not_not_intro allZero
  · simp only [matched, iff_true]
    exact nonzero

end Aiur.Optimized.Compiler
