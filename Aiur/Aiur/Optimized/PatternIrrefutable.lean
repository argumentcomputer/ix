import Aiur.Optimized.PatternCorrectness

namespace Aiur.Optimized.Compiler

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

mutual
  /-- An irrefutable pattern lowered for a canonical input always collects bindings. -/
  theorem pattern_matches [Field F] [DecidableEq F] {decls : Declarations}
      (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
      {pattern : Pattern F} {wire : Symbolic F} {test : List (Polynomial F)} {bindings : Locals F}
      {before after : State F}
      (compiled : Compiler.pattern decls pattern wire before = .ok ((test, bindings), after))
      (irrefutable : pattern.irrefutable decls = true) {assignment : Witness → F} {value : Value F}
      (decoded : (wire.map (Circuit.ArithExpr.denote assignment)).decode decls = some value) :
      ∃ values, pattern.bindings value = some values := by
    cases pattern with
    | wildcard => exact ⟨[], by simp [Pattern.bindings]⟩
    | bind name => exact ⟨[(name, value)], by simp [Pattern.bindings]⟩
    | literal => simp [Pattern.irrefutable] at irrefutable
    | tuple patterns =>
        rcases wire with ⟨type, words⟩
        cases type with
        | field | ptr | enum => simp [Compiler.pattern] at compiled
        | tuple types =>
            simp only [Compiler.pattern] at compiled
            obtain ⟨wires, middle, splitRun, patternRun⟩ := bind_ok.mp compiled
            obtain ⟨_, splitReference⟩ := splitValues_reference splitRun
            obtain ⟨values, rfl, valuesDecoded⟩ := Circuit.Compiler.splitValues_decode checked (splitReference {}) decoded
            simpa only [Pattern.bindings] using patternList_matches checked tags patternRun
              (by simpa [Pattern.irrefutable] using irrefutable) valuesDecoded
    | construct name ctor patterns =>
        simp only [Compiler.pattern] at compiled
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
                      obtain ⟨_, splitReference⟩ := splitValues_reference splitRun
                      obtain ⟨⟨payloadTest, payloadBindings⟩, s₄, payloadRun, finished⟩ := bind_ok.mp rest
                      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp finished
                      obtain ⟨actual, args, rfl, _, payloadDecoded⟩ :=
                        Circuit.Compiler.enum_payload_decoded checked tags found atIndex expansion parts (splitReference {}) decoded
                      have formed := (WireValue.decode_spec decoded).2.1
                      have same : actual = ctor := by
                        by_contra different
                        simp [Value.wellFormed, Declarations.findConstructor?, found, only.1,
                          ctorName, Ne.symm different] at formed
                      obtain ⟨values, matched⟩ := patternList_matches checked tags payloadRun only.2
                        (payloadDecoded (same.trans ctorName.symm))
                      exact ⟨values, by simpa [Pattern.bindings, same] using matched⟩
  termination_by sizeOf pattern

  theorem patternList_matches [Field F] [DecidableEq F] {decls : Declarations}
      (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
      {patterns : List (Pattern F)} {wires : List (Symbolic F)}
      {test : List (Polynomial F)} {bindings : Locals F} {before after : State F}
      (compiled : patternList decls patterns wires before = .ok ((test, bindings), after))
      (irrefutable : ∀ pattern ∈ patterns, pattern.irrefutable decls = true)
      {assignment : Witness → F} {values : List (Value F)}
      (decoded : DecodesValues decls (wires.map (WireValue.map (Circuit.ArithExpr.denote assignment))) values) :
      ∃ bindings, Pattern.bindingsList patterns values = some bindings := by
    cases patterns with
    | nil =>
        cases wires with
        | cons => simp [patternList] at compiled
        | nil => cases decoded; exact ⟨[], by simp [Pattern.bindingsList]⟩
    | cons pattern patterns =>
        cases wires with
        | nil => simp [patternList] at compiled
        | cons wire wires =>
            simp only [patternList] at compiled
            obtain ⟨⟨head, headBindings⟩, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨⟨tail, tailBindings⟩, last, tailRun, finished⟩ := bind_ok.mp rest
            cases decoded with
            | cons headDecode tailDecode =>
                obtain ⟨head, matchedHead⟩ := pattern_matches checked tags headRun (irrefutable _ (by simp)) headDecode
                obtain ⟨tail, matchedTail⟩ := patternList_matches checked tags tailRun
                  (fun p h => irrefutable p (by simp [h])) tailDecode
                exact ⟨head ++ tail, by simp [Pattern.bindingsList, matchedHead, matchedTail]⟩
  termination_by sizeOf patterns
end

/-- First successful source pattern, counted in source order. The value on a
list with no matching arm is irrelevant to successful compilation witnesses. -/
def armIndex [DecidableEq F] (input : Value F) : List (Pattern F × Expr F) → Nat
  | [] => 0
  | (pat, _) :: rest => if (pat.bindings input).isSome then 0 else armIndex input rest + 1

@[simp] theorem armIndex_cons_some [DecidableEq F] {input : Value F} {pat : Pattern F}
    {body : Expr F} {rest : List (Pattern F × Expr F)} {bindings : Environment F}
    (matched : pat.bindings input = some bindings) : armIndex input ((pat, body) :: rest) = 0 := by
  simp [armIndex, matched]

@[simp] theorem armIndex_cons_none [DecidableEq F] {input : Value F} {pat : Pattern F}
    {body : Expr F} {rest : List (Pattern F × Expr F)}
    (unmatched : pat.bindings input = none) :
    armIndex input ((pat, body) :: rest) = armIndex input rest + 1 := by
  simp [armIndex, unmatched]

/-- A successful source match selects one of the scopes actually emitted by
the compiler. Truncation after an irrefutable arm cannot hide this selection. -/
theorem lowerArms_index_lt [Field F] [DecidableEq F] {program : Program F}
    (checked : checkDeclarations program.enums = .ok ()) (tags : program.enums.tagsValid F = true)
    {function : String} {locals : Locals F} {scrutinee : Symbolic F} {result : WireValue Witness}
    {scopes : List ScopeId} {arms : List (Pattern F × Expr F)} {previous : List (List (Polynomial F))}
    {before after : State F}
    (compiled : lowerArms program function locals scrutinee result scopes arms previous before = .ok ((), after))
    {assignment : Witness → F} {input : Value F}
    (decoded : (scrutinee.map (Circuit.ArithExpr.denote assignment)).decode program.enums = some input)
    {bindings : Environment F} {body : Expr F}
    (selected : selectArm input arms = some (bindings, body)) : armIndex input arms < scopes.length := by
  induction arms generalizing scopes previous before with
  | nil => simp [selectArm] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pat, headBody⟩
      cases scopes with
      | nil => simp [lowerArms] at compiled
      | cons scope scopes =>
          simp only [lowerArms] at compiled
          obtain ⟨⟨conditions, patternBindings⟩, s₁, patternRun, guardsBind⟩ := bind_ok.mp compiled
          obtain ⟨⟨⟩, s₂, _, failuresBind⟩ := bind_ok.mp guardsBind
          obtain ⟨⟨⟩, s₃, _, bodyBind⟩ := bind_ok.mp failuresBind
          obtain ⟨_, s₄, _, rest⟩ := bind_ok.mp bodyBind
          cases matched : pat.bindings input with
          | some matchedBindings => simp [armIndex, matched]
          | none =>
              split at rest
              · rename_i irrefutable
                obtain ⟨_, matchSome⟩ := pattern_matches checked tags patternRun irrefutable decoded
                rw [matched] at matchSome
                cases matchSome
              · have tailSelected : selectArm input arms = some (bindings, body) := by
                  simpa only [selectArm, matched] using selected
                have bound := ih rest tailSelected
                simpa [armIndex, matched] using Nat.succ_lt_succ bound

end Aiur.Optimized.Compiler
