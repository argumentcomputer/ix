import Aiur.Optimized.ValidationCorrectness
import Aiur.Optimized.CompileFacts
import Aiur.Circuit.ExpressionCorrectness
import Aiur.Memory.WireProvenance

namespace Aiur.Optimized.Compiler

open Circuit.Compiler (ExpressionMeaning localsEnvironment localsEnvironment_append)

variable {F : Type} [Field F] [DecidableEq F]
/-- Call premises are needed only for arguments whose pointers originate in
stores. This is the invariant supplied by finite entrypoint derivations. -/
def CallsSound (decls : Declarations) (rom : WireROM F)
    (calls : Circuit.CallRelation F) (sourceCalls : Aiur.CallRelation F) : Prop :=
  ∀ name args result, calls name args result → ∀ values,
    DecodesValues decls args values →
    (∀ v ∈ values, (rom.decode decls).Provenance v) →
    ∃ value, result.decode decls = some value ∧ sourceCalls name values value

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem lift_eq_ok {computation : Except String α} {value : α} {before after : State F}
    (compiled : (liftM computation : Build F α) before = .ok (value, after)) :
    computation = .ok value ∧ before = after := by
  cases computation with
  | error error => simp [lift_error] at compiled
  | ok result =>
      simp only [lift_ok, Except.ok.injEq, Prod.mk.injEq] at compiled
      obtain ⟨rfl, rfl⟩ := compiled
      exact ⟨rfl, rfl⟩

theorem equalValue_extends {scope : ScopeId} {left right : Symbolic F} {before after : State F}
    (compiled : equalValue scope left right before = .ok ((), after)) : before.Extends after := by
  simp only [equalValue] at compiled
  split at compiled
  · simp [StateT.bind, bind, Except.bind] at compiled
  · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
    obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
    subst middle
    apply equations_extends (conditions := (left.words.zip right.words).map (fun (a, b) => Polynomial.sub a b))
    simpa only [List.forIn_map] using rest

private theorem failure_terms_extends {scope : ScopeId} {conditions terms : List (Polynomial F)}
    {before after : State F}
    (compiled : (conditions.mapM fun difference => do
      return Polynomial.mul difference (.var (← fresh (.auxiliary scope))) : Build F (List (Polynomial F)))
        before = .ok (terms, after)) : before.Extends after := by
  induction conditions generalizing terms before with
  | nil =>
      obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [List.mapM_nil] using compiled)
      exact .refl _
  | cons difference conditions ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨term, s₁, headRun, tailBind⟩ := bind_ok.mp compiled
      obtain ⟨tail, s₂, tailRun, finished⟩ := bind_ok.mp tailBind
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      obtain ⟨id, s₃, freshRun, finished⟩ := bind_ok.mp headRun
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      exact (fresh_extends freshRun).trans (ih tailRun)

theorem failure_extends {scope : ScopeId} {conditions : List (Polynomial F)} {before after : State F}
    (compiled : failure scope conditions before = .ok ((), after)) : before.Extends after := by
  simp only [failure] at compiled
  obtain ⟨terms, middle, termsRun, equationRun⟩ := bind_ok.mp compiled
  exact (failure_terms_extends termsRun).trans (equation_extends equationRun)

theorem failures_sound {scope : ScopeId} {previous : List (List (Polynomial F))} {before after : State F}
    (compiled : (do for earlier in previous do failure scope earlier : Build F Unit)
      before = .ok ((), after)) :
    before.Extends after ∧ ∀ {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F},
      after.Valid rom calls assignment → before.Valid rom calls assignment ∧
      ((before.activation scope).denote assignment = 1 → ∀ earlier ∈ previous, ¬AllZero earlier assignment) := by
  induction previous generalizing before with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, StateT.bind, bind, Except.bind, Except.pure] using compiled
      subst after
      exact ⟨.refl _, fun valid => ⟨valid, by simp⟩⟩
  | cons earlier previous ih =>
      simp only [List.forIn_cons, bind_assoc, pure_bind] at compiled
      obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
      have extension := failure_extends headRun
      obtain ⟨tailExtension, tailMeaning⟩ := ih tailRun
      refine ⟨extension.trans tailExtension, fun valid => ?_⟩
      obtain ⟨middleValid, tail⟩ := tailMeaning valid
      obtain ⟨beforeValid, head⟩ := failure_sound headRun middleValid
      exact ⟨beforeValid, fun active => by
        simpa using And.intro (head active) (tail (extension.active active))⟩

theorem finish_sound {scope : ScopeId} {target : Option (WireValue Witness)} {value output : Symbolic F}
    {before after : State F}
    (compiled : (do
      if let some result := target then
        equalValue scope (result.map Polynomial.var) value
        return result.map Polynomial.var
      return value : Build F (Symbolic F)) before = .ok (output, after)) :
    before.Extends after ∧ ∀ {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F},
      after.Valid rom calls assignment → before.Valid rom calls assignment ∧
      ((before.activation scope).denote assignment = 1 →
        output.map (Circuit.ArithExpr.denote assignment) = value.map (Circuit.ArithExpr.denote assignment)) := by
  cases target with
  | none =>
      obtain ⟨rfl, rfl⟩ := pure_ok.mp compiled
      exact ⟨.refl _, fun valid => ⟨valid, fun _ => rfl⟩⟩
  | some result =>
      obtain ⟨⟨⟩, middle, equated, finished⟩ := bind_ok.mp compiled
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      exact ⟨equalValue_extends equated, fun valid => equalValue_sound equated valid⟩

theorem cell_sound {cell : Cell F} {before after : State F}
    (compiled : (modify (fun state => {state with cells := state.cells.push cell}) : Build F Unit)
      before = .ok ((), after)) :
    before.Extends after ∧ ∀ {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F},
      after.Valid rom calls assignment → before.Valid rom calls assignment ∧
      ((before.activation cell.scope).denote assignment = 1 →
        (cell.address.denote assignment, cell.value.map (Circuit.ArithExpr.denote assignment)) ∈ rom.entries) := by
  change Except.ok ((), {before with cells := before.cells.push cell}) = Except.ok ((), after) at compiled
  have stateEq := congrArg Prod.snd (Except.ok.inj compiled)
  dsimp only at stateEq
  subst after
  have extension : before.Extends {before with cells := before.cells.push cell} :=
    ⟨fun _ _ => id, fun _ => id, fun _ => id, by simp⟩
  exact ⟨extension, fun valid => ⟨valid.of_extends extension, valid.2.2 cell (by simp)⟩⟩

theorem call_sound {call : Call F} {before after : State F}
    (compiled : (modify (fun state => {state with calls := state.calls.push call}) : Build F Unit)
      before = .ok ((), after)) :
    before.Extends after ∧ ∀ {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F},
      after.Valid rom calls assignment → before.Valid rom calls assignment ∧
      ((before.activation call.scope).denote assignment = 1 →
        calls call.channel (call.message assignment).args (call.message assignment).result) := by
  change Except.ok ((), {before with calls := before.calls.push call}) = Except.ok ((), after) at compiled
  have stateEq := congrArg Prod.snd (Except.ok.inj compiled)
  dsimp only at stateEq
  subst after
  have extension : before.Extends {before with calls := before.calls.push call} :=
    ⟨fun _ _ => id, fun _ => id, by simp, fun _ => id⟩
  exact ⟨extension, fun valid => ⟨valid.of_extends extension, valid.2.1 call (by simp)⟩⟩

mutual
  theorem lower_sound {program : Program F} (checked : checkDeclarations program.enums = .ok ())
      (tags : program.enums.tagsValid F = true)
      {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
      {rom : WireROM F} (romValid : rom.Valid)
      (callSound : CallsSound program.enums rom calls sourceCalls)
      (callProvenance : ∀ name args result, sourceCalls name args result →
        (∀ v ∈ args, (rom.decode program.enums).Provenance v) →
        (rom.decode program.enums).Provenance result)
      {function : String} {locals : Locals F} {scope : ScopeId} {expr : Expr F}
      {target : Option (WireValue Witness)} {output : Symbolic F} {before after : State F}
      (compiled : lower program function locals scope expr target before = .ok (output, after)) :
      before.Extends after ∧ ∀ (assignment : Witness → F),
        (before.activation 0).denote assignment = 1 → after.Valid rom calls assignment →
        before.Valid rom calls assignment ∧ ((before.activation scope).denote assignment = 1 → ∀ environment,
          DecodesEnvironment program.enums (localsEnvironment locals assignment) environment →
          environment.Provenance (rom.decode program.enums) →
          ExpressionMeaning program.enums rom sourceCalls environment expr
            (output.map (Circuit.ArithExpr.denote assignment))) := by
    rw [lower.eq_def] at compiled
    obtain ⟨value, middle, valueRun, finishRun⟩ := bind_ok.mp compiled
    obtain ⟨finishExtension, finishMeaning⟩ := finish_sound finishRun
    have body : before.Extends middle ∧ ∀ (assignment : Witness → F),
        (before.activation 0).denote assignment = 1 → middle.Valid rom calls assignment →
        before.Valid rom calls assignment ∧ ((before.activation scope).denote assignment = 1 → ∀ environment,
          DecodesEnvironment program.enums (localsEnvironment locals assignment) environment →
          environment.Provenance (rom.decode program.enums) →
          ExpressionMeaning program.enums rom sourceCalls environment expr
            (value.map (Circuit.ArithExpr.denote assignment))) := by
      cases expr with
      | literal literal =>
          obtain ⟨rfl, rfl⟩ := pure_ok.mp valueRun
          exact ⟨.refl _, fun _ _ valid => ⟨valid, fun _ _ _ _ =>
            ⟨.field literal, by simp [Scalar.Circuit.ArithExpr.denote], .literal⟩⟩⟩
      | var name =>
          cases found : locals.find? (·.1 == name) with
          | none => simp [found] at valueRun
          | some binding =>
              rcases binding with ⟨bindingName, wire⟩
              have same : bindingName = name := by simpa using List.find?_some found
              subst bindingName
              obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [found] using valueRun)
              refine ⟨.refl _, fun assignment _ valid => ⟨valid, fun _ environment decoded _ => ?_⟩⟩
              obtain ⟨value, lookup, valueDecode⟩ := decoded.find name
                (wire := (name, wire.map (Circuit.ArithExpr.denote assignment)))
                (by simp [localsEnvironment, List.find?_map, Function.comp_def, found])
              exact ⟨value, valueDecode, .var lookup⟩
      | tuple items =>
          obtain ⟨wires, last, argsRun, finished⟩ := bind_ok.mp valueRun
          obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
          obtain ⟨extension, meaning⟩ := lowerArgs_sound checked tags romValid callSound callProvenance argsRun
          refine ⟨extension, fun assignment root valid => ?_⟩
          obtain ⟨previous, evaluated⟩ := meaning assignment root valid
          refine ⟨previous, fun active environment decoded trusted => ?_⟩
          obtain ⟨values, decodedValues, evaluations⟩ := evaluated active environment decoded trusted
          exact ⟨.tuple values, by
            simpa only [WireValue.map_tuple] using WireValue.decode_tuple checked tags decodedValues,
            .tuple evaluations⟩
      | construct name ctor args =>
          cases found : program.enums.findEnum? name with
          | none => simp [found] at valueRun
          | some definition =>
              cases atIndex : definition.constructors[definition.constructors.findIdx (·.name == ctor)]? with
              | none => simp [found, atIndex] at valueRun
              | some constructor =>
                  simp only [found, atIndex] at valueRun
                  obtain ⟨wires, s₁, argsRun, rest⟩ := bind_ok.mp valueRun
                  split at rest
                  · simp [StateT.bind, bind, Except.bind] at rest
                  · rename_i types
                    obtain ⟨⟨⟩, unchangedState, unchanged, layoutBind⟩ := bind_ok.mp rest
                    obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                    subst unchangedState
                    obtain ⟨layout, layoutState, layoutRun, shapeBind⟩ := bind_ok.mp layoutBind
                    obtain ⟨expansion, stateEq⟩ := getLayout_eq layoutRun
                    subst layoutState
                    split at shapeBind
                    · simp [StateT.bind, bind, Except.bind] at shapeBind
                    · obtain ⟨⟨⟩, unchangedState, unchanged, finished⟩ := bind_ok.mp shapeBind
                      obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                      subst unchangedState
                      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                      obtain ⟨extension, meaning⟩ := lowerArgs_sound checked tags romValid callSound callProvenance argsRun
                      refine ⟨extension, fun assignment root valid => ?_⟩
                      obtain ⟨previous, evaluated⟩ := meaning assignment root valid
                      refine ⟨previous, fun active environment decoded trusted => ?_⟩
                      obtain ⟨values, argsDecode, argsEval⟩ := evaluated active environment decoded trusted
                      have ctorName : constructor.name = ctor := by
                        simpa using List.findIdx_of_getElem?_eq_some atIndex
                      refine ⟨.construct name ctor values, ?_, .construct argsEval⟩
                      have constructed := WireValue.decode_construct checked tags found atIndex argsDecode
                        (by simpa [Function.comp_def, WireValue.map] using (not_ne_iff.mp types)) expansion
                      simpa [ctorName, WireValue.map, List.map_flatMap, List.flatMap_map,
                        List.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using constructed
      | project operand index =>
          obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp valueRun
          rcases input with ⟨type, words⟩
          cases type with
          | field | ptr | enum => simp at rest
          | tuple types =>
              dsimp only at rest
              obtain ⟨wires, s₂, splitRun, resultBind⟩ := bind_ok.mp rest
              obtain ⟨stateEq, reference⟩ := splitValues_reference splitRun
              subst s₂
              cases projected : wires[index]? with
              | none => simp [projected] at resultBind
              | some result =>
                  obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [projected] using resultBind)
                  obtain ⟨extension, meaning⟩ := lower_sound checked tags romValid callSound callProvenance inputRun
                  refine ⟨extension, fun assignment root valid => ?_⟩
                  obtain ⟨previous, evaluated⟩ := meaning assignment root valid
                  refine ⟨previous, fun active environment decoded trusted => ?_⟩
                  obtain ⟨value, inputDecode, inputEval⟩ := evaluated active environment decoded trusted
                  obtain ⟨values, rfl, decodedValues⟩ := Circuit.Compiler.splitValues_decode checked (reference {}) inputDecode
                  obtain ⟨value, valueAt, valueDecode⟩ := decodedValues.getElem (index := index)
                    (wire := result.map (Circuit.ArithExpr.denote assignment))
                    (by simp [List.getElem?_map, projected])
                  exact ⟨value, valueDecode, .project inputEval (by simp [projectValue, valueAt, pure, Except.pure])⟩
      | letValue pat operand body =>
          obtain ⟨input, s₁, inputRun, patternBind⟩ := bind_ok.mp valueRun
          obtain ⟨⟨conditions, bindings⟩, s₂, patternRun, guardBind⟩ := bind_ok.mp patternBind
          obtain ⟨stateEq, matched⟩ := pattern_correct checked tags patternRun
          subst s₂
          obtain ⟨⟨⟩, s₃, guardRun, bodyRun⟩ := bind_ok.mp guardBind
          have guardRun' : (do for condition in conditions do equation scope condition : Build F Unit)
              s₁ = .ok ((), s₃) := bind_ok.mpr ⟨(), s₃, guardRun, rfl⟩
          obtain ⟨inputExtension, inputMeaning⟩ := lower_sound checked tags romValid callSound callProvenance inputRun
          have guardExtension := equations_extends guardRun'
          obtain ⟨bodyExtension, bodyMeaning⟩ := lower_sound checked tags romValid callSound callProvenance bodyRun
          have beforeBody := inputExtension.trans guardExtension
          refine ⟨beforeBody.trans bodyExtension, fun assignment root valid => ?_⟩
          obtain ⟨s₃valid, bodyEval⟩ := bodyMeaning assignment (beforeBody.active root) valid
          obtain ⟨s₁valid, equations⟩ := equations_sound guardRun' s₃valid
          obtain ⟨previous, inputEval⟩ := inputMeaning assignment root s₁valid
          refine ⟨previous, fun active environment decoded trusted => ?_⟩
          obtain ⟨inputValue, inputDecode, inputEval⟩ := inputEval active environment decoded trusted
          have zeros : AllZero conditions assignment := fun condition member => by
            simpa only [inputExtension.active active, one_mul] using equations condition member
          rcases matched assignment inputValue inputDecode with
            ⟨values, matched, _, decodedBindings⟩ | ⟨_, failed⟩
          · obtain ⟨value, resultDecode, evaluated⟩ := bodyEval (beforeBody.active active) (values ++ environment)
              (by simpa only [localsEnvironment_append] using decodedBindings.append decoded)
              (by
                intro binding member
                rcases List.mem_append.mp member with member | member
                · exact Pattern.bindings_provenance
                    (inputEval.provenance (WireROM.decode_valid romValid) callProvenance trusted) matched binding member
                · exact trusted binding member)
            exact ⟨value, resultDecode, .letValue inputEval matched evaluated⟩
          · exact (failed zeros).elim
      | store operand =>
          obtain ⟨input, s₁, inputRun, destBind⟩ := bind_ok.mp valueRun
          obtain ⟨result, s₂, destRun, shapeBind⟩ := bind_ok.mp destBind
          have resultType := (destination_spec destRun).2.2
          rcases result with ⟨resultType', resultWords⟩
          dsimp only at resultType
          subst resultType'
          cases resultWords with
          | nil => simp at shapeBind
          | cons address words =>
              cases words with
              | cons => simp at shapeBind
              | nil =>
                  dsimp only at shapeBind
                  obtain ⟨⟨⟩, s₃, cellRun, finished⟩ := bind_ok.mp shapeBind
                  obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                  obtain ⟨inputExtension, inputMeaning⟩ := lower_sound checked tags romValid callSound callProvenance inputRun
                  have beforeCell := inputExtension.trans (destination_extends destRun)
                  obtain ⟨cellExtension, cellMeaning⟩ := cell_sound cellRun
                  refine ⟨beforeCell.trans cellExtension, fun assignment root valid => ?_⟩
                  obtain ⟨s₂valid, cell⟩ := cellMeaning valid
                  obtain ⟨previous, evaluated⟩ := inputMeaning assignment root (destination_valid destRun s₂valid)
                  refine ⟨previous, fun active environment decoded trusted => ?_⟩
                  obtain ⟨value, valueDecode, valueEval⟩ := evaluated active environment decoded trusted
                  obtain ⟨type, _, layout, expansion, _⟩ := WireValue.decode_spec valueDecode
                  have names := (Declarations.layout_parts expansion).1
                  refine ⟨.ptr value.type (assignment address), ?_, .store valueEval ?_⟩
                  · simpa only [WireValue.map_ptr, Scalar.Circuit.ArithExpr.denote, type, WireValue.map, WireValue.ptr, List.map_cons, List.map_nil] using
                      WireValue.decode_ptr names (assignment address)
                  · exact WireROM.mem_decode.mpr ⟨_, cell (beforeCell.active active), valueDecode⟩
      | load operand =>
          obtain ⟨input, s₁, inputRun, shapeBind⟩ := bind_ok.mp valueRun
          rcases input with ⟨type, words⟩
          cases type with
          | field | tuple | enum => simp at shapeBind
          | ptr pointerType =>
              cases words with
              | nil => simp at shapeBind
              | cons address words =>
                  cases words with
                  | cons => simp at shapeBind
                  | nil =>
                      dsimp only at shapeBind
                      obtain ⟨result, s₂, destRun, cellBind⟩ := bind_ok.mp shapeBind
                      obtain ⟨⟨⟩, s₃, cellRun, finished⟩ := bind_ok.mp cellBind
                      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                      obtain ⟨inputExtension, inputMeaning⟩ :=
                        lower_sound checked tags romValid callSound callProvenance inputRun
                      have beforeCell := inputExtension.trans (destination_extends destRun)
                      obtain ⟨cellExtension, cellMeaning⟩ := cell_sound cellRun
                      refine ⟨beforeCell.trans cellExtension, fun assignment root valid => ?_⟩
                      obtain ⟨s₂valid, cell⟩ := cellMeaning valid
                      obtain ⟨previous, evaluated⟩ := inputMeaning assignment root (destination_valid destRun s₂valid)
                      refine ⟨previous, fun active environment decoded trusted => ?_⟩
                      obtain ⟨value, valueDecode, valueEval⟩ := evaluated active environment decoded trusted
                      have same := WireValue.ptr_decoded_eq valueDecode
                      subst value
                      have pointerTrusted := valueEval.provenance (WireROM.decode_valid romValid) callProvenance trusted
                      obtain ⟨value, resultDecode, resultType, _⟩ :=
                        WireROM.load_of_provenance romValid pointerTrusted (cell (beforeCell.active active))
                          (by simpa only [WireValue.map] using (destination_spec destRun).2.2)
                      exact ⟨value, resultDecode, .load valueEval
                        (WireROM.mem_decode.mpr ⟨_, cell (beforeCell.active active), resultDecode⟩) resultType⟩
      | neg operand =>
          obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp valueRun
          obtain ⟨polynomial, s₂, fieldRun, finished⟩ := bind_ok.mp rest
          obtain ⟨rfl, rfl⟩ := asField_eq fieldRun
          obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
          obtain ⟨extension, meaning⟩ := lower_sound checked tags romValid callSound callProvenance inputRun
          refine ⟨extension, fun assignment root valid => ?_⟩
          obtain ⟨previous, evaluated⟩ := meaning assignment root valid
          refine ⟨previous, fun active environment decoded trusted => ?_⟩
          obtain ⟨value, valueDecode, valueEval⟩ := evaluated active environment decoded trusted
          simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq] at valueDecode
          subst value
          exact ⟨.field (0 - polynomial.denote assignment), by simp [Scalar.Circuit.ArithExpr.denote],
            .neg valueEval (by simp [evalNeg])⟩
      | hint type key channel =>
          obtain ⟨input, s₁, keyRun, rest⟩ := bind_ok.mp valueRun
          split at rest
          · simp [StateT.bind, bind, Except.bind] at rest
          · rename_i free
            have free : type.pointerFree program.enums = true := by simpa using free
            obtain ⟨⟨⟩, unchangedState, unchanged, destBind⟩ := bind_ok.mp rest
            obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
            subst unchangedState
            obtain ⟨result, s₂, destRun, validationBind⟩ := bind_ok.mp destBind
            obtain ⟨⟨⟩, s₃, validationRun, finished⟩ := bind_ok.mp validationBind
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨keyExtension, keyMeaning⟩ := lower_sound checked tags romValid callSound callProvenance keyRun
            have destExtension := destination_extends destRun
            obtain ⟨validationExtension, validationMeaning⟩ := validateValue_sound checked tags validationRun
            have beforeValidation := keyExtension.trans destExtension
            refine ⟨beforeValidation.trans validationExtension, fun assignment root valid => ?_⟩
            obtain ⟨s₂valid, resultDecoded⟩ := validationMeaning rom calls assignment (beforeValidation.active root) valid
            obtain ⟨previous, keyEval⟩ := keyMeaning assignment root (destination_valid destRun s₂valid)
            refine ⟨previous, fun active environment decoded trusted => ?_⟩
            obtain ⟨keyValue, _, keyEval⟩ := keyEval active environment decoded trusted
            obtain ⟨value, resultDecode⟩ := resultDecoded (beforeValidation.active active)
            have spec := WireValue.decode_spec resultDecode
            have shape : value.type = type := spec.1.trans (destination_spec destRun).2.2
            have valueFree := Value.pointerFree_of_type (shape ▸ free) spec.2.1
            obtain ⟨constant, same⟩ := value.exists_constant valueFree
            subst value
            exact ⟨_, resultDecode, .hint keyEval (by
              simpa [Value.WellTyped, Value.hasType] using And.intro shape spec.2.1)⟩
      | assertEq message left right =>
          obtain ⟨leftWire, s₁, leftRun, rest⟩ := bind_ok.mp valueRun
          obtain ⟨rightWire, s₂, rightRun, rest⟩ := bind_ok.mp rest
          split at rest
          · simp [StateT.bind, bind, Except.bind] at rest
          · rename_i free
            obtain ⟨⟨⟩, unchangedState, unchanged, eqBind⟩ := bind_ok.mp rest
            obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
            subst unchangedState
            obtain ⟨⟨⟩, last, equated, finished⟩ := bind_ok.mp eqBind
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨leftExtension, leftMeaning⟩ := lower_sound checked tags romValid callSound callProvenance leftRun
            obtain ⟨rightExtension, rightMeaning⟩ := lower_sound checked tags romValid callSound callProvenance rightRun
            have beforeEq := leftExtension.trans rightExtension
            refine ⟨beforeEq.trans (equalValue_extends equated), fun assignment root valid => ?_⟩
            obtain ⟨valid₂, equal⟩ := equalValue_sound equated valid
            obtain ⟨valid₁, rightEval⟩ := rightMeaning assignment (leftExtension.active root) valid₂
            obtain ⟨previous, leftEval⟩ := leftMeaning assignment root valid₁
            refine ⟨previous, fun active environment decoded trusted => ?_⟩
            obtain ⟨x, xDecode, xEval⟩ := leftEval active environment decoded trusted
            obtain ⟨y, yDecode, yEval⟩ := rightEval (leftExtension.active active) environment decoded trusted
            have same : x = y := Option.some.inj (xDecode.symm.trans ((equal (beforeEq.active active)) ▸ yDecode))
            have data := WireValue.decode_spec xDecode
            have pointerFree : x.pointerFree = true := Value.pointerFree_of_type
              (by simpa [data.1, WireValue.type_map] using free) data.2.1
            exact ⟨.tuple [], by simpa only [WireValue.map_tuple, List.map_nil] using
              WireValue.decode_tuple checked tags (.nil : DecodesValues program.enums [] []),
              .assertEq xEval yEval (evalAssertEq_ok.mpr ⟨pointerFree, same, rfl⟩)⟩
      | binary op left right =>
          obtain ⟨leftWire, s₁, leftRun, leftBind⟩ := bind_ok.mp valueRun
          obtain ⟨leftPoly, s₂, leftField, rightBind⟩ := bind_ok.mp leftBind
          obtain ⟨rfl, rfl⟩ := asField_eq leftField
          obtain ⟨rightWire, s₃, rightRun, rightFieldBind⟩ := bind_ok.mp rightBind
          obtain ⟨rightPoly, s₄, rightField, rest⟩ := bind_ok.mp rightFieldBind
          obtain ⟨rfl, rfl⟩ := asField_eq rightField
          obtain ⟨leftExtension, leftMeaning⟩ := lower_sound checked tags romValid callSound callProvenance leftRun
          obtain ⟨rightExtension, rightMeaning⟩ := lower_sound checked tags romValid callSound callProvenance rightRun
          have beforeOperation := leftExtension.trans rightExtension
          cases op with
          | add | sub | mul =>
              obtain ⟨rfl, rfl⟩ := pure_ok.mp rest
              refine ⟨beforeOperation, fun assignment root valid => ?_⟩
              obtain ⟨s₁valid, rightEval⟩ := rightMeaning assignment (leftExtension.active root) valid
              obtain ⟨previous, leftEval⟩ := leftMeaning assignment root s₁valid
              refine ⟨previous, fun active environment decoded trusted => ?_⟩
              obtain ⟨x, xDecode, xEval⟩ := leftEval active environment decoded trusted
              obtain ⟨y, yDecode, yEval⟩ := rightEval (leftExtension.active active) environment decoded trusted
              simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq] at xDecode yDecode
              subst x; subst y
              exact ⟨_, WireValue.decode_field _ _, .binary xEval yEval (by
                simp [evalBinOp, Scalar.Circuit.ArithExpr.denote])⟩
          | div =>
              cases folded : rightPoly.constantInverse? with
              | some inverse =>
                  simp only [folded] at rest
                  obtain ⟨rfl, rfl⟩ := pure_ok.mp rest
                  refine ⟨beforeOperation, fun assignment root valid => ?_⟩
                  obtain ⟨s₁valid, rightEval⟩ := rightMeaning assignment (leftExtension.active root) valid
                  obtain ⟨previous, leftEval⟩ := leftMeaning assignment root s₁valid
                  refine ⟨previous, fun active environment decoded trusted => ?_⟩
                  obtain ⟨x, xDecode, xEval⟩ := leftEval active environment decoded trusted
                  obtain ⟨y, yDecode, yEval⟩ := rightEval (leftExtension.active active) environment decoded trusted
                  simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq] at xDecode yDecode
                  subst x; subst y
                  have known := Polynomial.constantInverse?_sound folded assignment
                  exact ⟨_, WireValue.decode_field _ _, .binary xEval yEval (by
                    simp [evalBinOp, Scalar.Circuit.ArithExpr.denote, known.1, known.2, div_eq_mul_inv])⟩
              | none =>
                  simp only [folded] at rest
                  obtain ⟨inverse, s₅, inverseRun, inverseBind⟩ := bind_ok.mp rest
                  obtain ⟨⟨⟩, s₆, equationRun, finished⟩ := bind_ok.mp inverseBind
                  obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                  have beforeEquation := beforeOperation.trans (fresh_extends inverseRun)
                  refine ⟨beforeEquation.trans (equation_extends equationRun), fun assignment root valid => ?_⟩
                  obtain ⟨s₅valid, equation⟩ := equation_valid equationRun valid
                  have s₃valid := fresh_valid inverseRun s₅valid
                  obtain ⟨s₁valid, rightEval⟩ := rightMeaning assignment (leftExtension.active root) s₃valid
                  obtain ⟨previous, leftEval⟩ := leftMeaning assignment root s₁valid
                  refine ⟨previous, fun active environment decoded trusted => ?_⟩
                  obtain ⟨x, xDecode, xEval⟩ := leftEval active environment decoded trusted
                  obtain ⟨y, yDecode, yEval⟩ := rightEval (leftExtension.active active) environment decoded trusted
                  simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq] at xDecode yDecode
                  subst x; subst y
                  change (s₅.activation scope).denote assignment *
                    (rightPoly.denote assignment * assignment inverse - 1) = 0 at equation
                  rw [beforeEquation.active active, one_mul] at equation
                  exact ⟨_, WireValue.decode_field _ _, .binary xEval yEval (by
                    simp [evalBinOp, Scalar.Circuit.ArithExpr.denote, Scalar.Circuit.inverse_nonzero equation,
                      Scalar.Circuit.inverse_eq equation, div_eq_mul_inv])⟩
      | call name args =>
          cases found : program.findSignature? name with
          | none => simp [found] at valueRun
          | some callee =>
              simp only [found] at valueRun
              obtain ⟨arguments, s₁, argsRun, guardBind⟩ := bind_ok.mp valueRun
              split at guardBind
              · simp [StateT.bind, bind, Except.bind] at guardBind
              · obtain ⟨⟨⟩, unchangedState, unchanged, destBind⟩ := bind_ok.mp guardBind
                obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                subst unchangedState
                obtain ⟨result, s₂, destRun, callBind⟩ := bind_ok.mp destBind
                obtain ⟨⟨⟩, s₃, callRun, finished⟩ := bind_ok.mp callBind
                obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                obtain ⟨argsExtension, argsMeaning⟩ := lowerArgs_sound checked tags romValid callSound callProvenance argsRun
                have beforeCall := argsExtension.trans (destination_extends destRun)
                obtain ⟨callExtension, callMeaning⟩ := call_sound callRun
                refine ⟨beforeCall.trans callExtension, fun assignment root valid => ?_⟩
                obtain ⟨s₂valid, callValid⟩ := callMeaning valid
                obtain ⟨previous, argsEval⟩ := argsMeaning assignment root (destination_valid destRun s₂valid)
                refine ⟨previous, fun active environment decoded trusted => ?_⟩
                obtain ⟨values, argsDecode, argsEval⟩ := argsEval active environment decoded trusted
                obtain ⟨value, resultDecode, calleeEval⟩ :=
                  callSound name _ _ (callValid (beforeCall.active active)) values argsDecode
                  (argsEval.provenance (WireROM.decode_valid romValid) callProvenance trusted)
                exact ⟨value, by simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote, Call.message] using resultDecode, .call argsEval calleeEval⟩
      | matchValue scrutinee arms =>
          obtain ⟨⟨⟩, checkState, checkRun, typeBind⟩ := bind_ok.mp valueRun
          obtain ⟨_, stateEq⟩ := lift_eq_ok checkRun
          subst checkState
          obtain ⟨type, typeState, typeRun, scrutineeBind⟩ := bind_ok.mp typeBind
          obtain ⟨_, stateEq⟩ := lift_eq_ok typeRun
          subst typeState
          obtain ⟨input, s₁, scrutineeRun, destBind⟩ := bind_ok.mp scrutineeBind
          obtain ⟨result, s₂, destRun, choiceBind⟩ := bind_ok.mp destBind
          obtain ⟨branches, s₄, choiceRun, armsBind⟩ := bind_ok.mp choiceBind
          obtain ⟨⟨⟩, s₅, armsRun, finished⟩ := bind_ok.mp armsBind
          obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
          obtain ⟨inputExtension, inputMeaning⟩ := lower_sound checked tags romValid callSound callProvenance scrutineeRun
          have beforeChoice := inputExtension.trans (destination_extends destRun)
          have choiceExtension := choice_extends choiceRun
          have beforeArms := beforeChoice.trans choiceExtension
          obtain ⟨armsExtension, armsMeaning⟩ := lowerArms_sound checked tags romValid callSound callProvenance
            (choice_length choiceRun) armsRun
          refine ⟨beforeArms.trans armsExtension, fun assignment root valid => ?_⟩
          obtain ⟨s₄valid, armsEval⟩ := armsMeaning assignment (beforeArms.active root) valid
          have s₂valid := s₄valid.of_extends choiceExtension
          obtain ⟨previous, inputEval⟩ := inputMeaning assignment root (destination_valid destRun s₂valid)
          refine ⟨previous, fun active environment decoded trusted => ?_⟩
          obtain ⟨inputValue, inputDecode, evaluated⟩ := inputEval active environment decoded trusted
          obtain ⟨branch, member, enabled⟩ := choice_active choiceRun s₄valid (beforeChoice.active root)
            (beforeChoice.active active)
          obtain ⟨_, bindings, body, selected, value, valueDecode, bodyEval⟩ :=
            armsEval environment decoded trusted inputValue inputDecode
              (evaluated.provenance (WireROM.decode_valid romValid) callProvenance trusted) branch member enabled
          exact ⟨value, by simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote, Call.message] using valueDecode,
            .matchValue evaluated selected bodyEval⟩
    refine ⟨body.1.trans finishExtension, fun assignment root valid => ?_⟩
    obtain ⟨middleValid, equal⟩ := finishMeaning valid
    obtain ⟨beforeValid, evaluated⟩ := body.2 assignment root middleValid
    refine ⟨beforeValid, fun active environment decoded trusted => ?_⟩
    rw [equal (body.1.active active)]
    exact evaluated active environment decoded trusted
  termination_by sizeOf expr

  theorem lowerArgs_sound {program : Program F} (checked : checkDeclarations program.enums = .ok ())
      (tags : program.enums.tagsValid F = true)
      {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
      {rom : WireROM F} (romValid : rom.Valid)
      (callSound : CallsSound program.enums rom calls sourceCalls)
      (callProvenance : ∀ name args result, sourceCalls name args result →
        (∀ v ∈ args, (rom.decode program.enums).Provenance v) →
        (rom.decode program.enums).Provenance result)
      {function : String} {locals : Locals F} {scope : ScopeId} {args : List (Expr F)}
      {outputs : List (Symbolic F)} {before after : State F}
      (compiled : lowerArgs program function locals scope args before = .ok (outputs, after)) :
      before.Extends after ∧ ∀ (assignment : Witness → F),
        (before.activation 0).denote assignment = 1 → after.Valid rom calls assignment →
        before.Valid rom calls assignment ∧ ((before.activation scope).denote assignment = 1 → ∀ environment,
          DecodesEnvironment program.enums (localsEnvironment locals assignment) environment →
          environment.Provenance (rom.decode program.enums) → ∃ values,
          DecodesValues program.enums (outputs.map (WireValue.map (Circuit.ArithExpr.denote assignment))) values ∧
          ROMEvalArgsWith program.enums (rom.decode program.enums) sourceCalls environment args values) := by
    cases args with
    | nil =>
        obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [lowerArgs] using compiled)
        exact ⟨.refl _, fun _ _ valid => ⟨valid, fun _ _ _ _ => ⟨[], .nil, .nil⟩⟩⟩
    | cons arg args =>
        simp only [lowerArgs] at compiled
        obtain ⟨head, middle, headRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨headExtension, headMeaning⟩ := lower_sound checked tags romValid callSound callProvenance headRun
        obtain ⟨tailExtension, tailMeaning⟩ := lowerArgs_sound checked tags romValid callSound callProvenance tailRun
        refine ⟨headExtension.trans tailExtension, fun assignment root valid => ?_⟩
        obtain ⟨middleValid, tailEval⟩ := tailMeaning assignment (headExtension.active root) valid
        obtain ⟨previous, headEval⟩ := headMeaning assignment root middleValid
        refine ⟨previous, fun active environment decoded trusted => ?_⟩
        obtain ⟨head, headDecode, headEval⟩ := headEval active environment decoded trusted
        obtain ⟨tail, tailDecode, tailEval⟩ := tailEval (headExtension.active active) environment decoded trusted
        exact ⟨head :: tail, .cons headDecode tailDecode, .cons headEval tailEval⟩
  termination_by sizeOf args

  theorem lowerArms_sound {program : Program F} (checked : checkDeclarations program.enums = .ok ())
      (tags : program.enums.tagsValid F = true)
      {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
      {rom : WireROM F} (romValid : rom.Valid)
      (callSound : CallsSound program.enums rom calls sourceCalls)
      (callProvenance : ∀ name args result, sourceCalls name args result →
        (∀ v ∈ args, (rom.decode program.enums).Provenance v) →
        (rom.decode program.enums).Provenance result)
      {function : String} {locals : Locals F} {scrutinee : Symbolic F} {result : WireValue Witness}
      {scopes : List ScopeId} {arms : List (Pattern F × Expr F)} {previous : List (List (Polynomial F))}
      (length : scopes.length = (retainArms program.enums arms).length) {before after : State F}
      (compiled : lowerArms program function locals scrutinee result scopes arms previous before = .ok ((), after)) :
      before.Extends after ∧ ∀ (assignment : Witness → F),
        (before.activation 0).denote assignment = 1 → after.Valid rom calls assignment →
        before.Valid rom calls assignment ∧ ∀ environment,
          DecodesEnvironment program.enums (localsEnvironment locals assignment) environment →
          environment.Provenance (rom.decode program.enums) → ∀ input,
          (scrutinee.map (Circuit.ArithExpr.denote assignment)).decode program.enums = some input →
          (rom.decode program.enums).Provenance input →
          ∀ scope ∈ scopes, (before.activation scope).denote assignment = 1 →
            (∀ earlier ∈ previous, ¬AllZero earlier assignment) ∧ ∃ bindings body,
              selectArm input arms = some (bindings, body) ∧
              ExpressionMeaning program.enums rom sourceCalls (bindings ++ environment) body
                (result.map assignment) := by
    cases arms with
    | nil =>
        cases scopes with
        | nil =>
            obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [lowerArms] using compiled)
            exact ⟨.refl _, fun _ _ valid => ⟨valid, by simp⟩⟩
        | cons => simp [lowerArms] at compiled
    | cons arm arms =>
        rcases hArm : arm with ⟨pat, body⟩
        rw [hArm] at compiled length
        cases scopes with
        | nil => simp [lowerArms] at compiled
        | cons scope scopes =>
            simp only [lowerArms] at compiled
            obtain ⟨⟨conditions, bindings⟩, patternState, patternRun, guardBind⟩ := bind_ok.mp compiled
            obtain ⟨stateEq, patternMeaning⟩ := pattern_correct checked tags patternRun
            subst patternState
            obtain ⟨⟨⟩, s₁, guardRun, failuresBind⟩ := bind_ok.mp guardBind
            obtain ⟨⟨⟩, s₂, failuresRun, bodyBind⟩ := bind_ok.mp failuresBind
            obtain ⟨bodyWire, s₃, bodyRun, rest⟩ := bind_ok.mp bodyBind
            have guardRun' : (do for condition in conditions do equation scope condition : Build F Unit)
                before = .ok ((), s₁) := bind_ok.mpr ⟨(), s₁, guardRun, rfl⟩
            have failuresRun' : (do for earlier in previous do failure scope earlier : Build F Unit)
                s₁ = .ok ((), s₂) := bind_ok.mpr ⟨(), s₂, failuresRun, rfl⟩
            have guardExtension := equations_extends guardRun'
            obtain ⟨failuresExtension, failuresMeaning⟩ := failures_sound failuresRun'
            have beforeBody := guardExtension.trans failuresExtension
            obtain ⟨bodyExtension, bodyMeaning⟩ := lower_sound checked tags romValid callSound callProvenance bodyRun
            have headExtension := beforeBody.trans bodyExtension
            have headFacts (assignment : Witness → F)
                (root : (before.activation 0).denote assignment = 1)
                (valid : s₃.Valid rom calls assignment) :
                before.Valid rom calls assignment ∧ ∀ environment,
                  DecodesEnvironment program.enums (localsEnvironment locals assignment) environment →
                  environment.Provenance (rom.decode program.enums) → ∀ input,
                  (scrutinee.map (Circuit.ArithExpr.denote assignment)).decode program.enums = some input →
                  (rom.decode program.enums).Provenance input →
                  (before.activation scope).denote assignment = 1 →
                  (∀ earlier ∈ previous, ¬AllZero earlier assignment) ∧ ∃ values,
                    pat.bindings input = some values ∧
                    ExpressionMeaning program.enums rom sourceCalls (values ++ environment) body
                      (result.map assignment) := by
              obtain ⟨s₂valid, evaluated⟩ := bodyMeaning assignment (beforeBody.active root) valid
              obtain ⟨s₁valid, failed⟩ := failuresMeaning s₂valid
              obtain ⟨beforeValid, equations⟩ := equations_sound guardRun' s₁valid
              refine ⟨beforeValid, fun environment decoded trusted input inputDecoded inputTrusted active => ?_⟩
              have allZero : AllZero conditions assignment := fun condition member => by
                simpa only [active, one_mul] using equations condition member
              refine ⟨failed (guardExtension.active active), ?_⟩
              rcases patternMeaning assignment input inputDecoded with
                ⟨values, matched, _, bindingsDecoded⟩ | ⟨_, unmatched⟩
              · refine ⟨values, matched, ?_⟩
                have resultMeaning := evaluated (beforeBody.active active) (values ++ environment)
                  (by simpa only [localsEnvironment_append] using bindingsDecoded.append decoded)
                  (by
                    intro binding member
                    rcases List.mem_append.mp member with member | member
                    · exact Pattern.bindings_provenance inputTrusted matched binding member
                    · exact trusted binding member)
                simpa only [lower_target bodyRun, WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultMeaning
              · exact (unmatched allZero).elim
            split at rest
            · rename_i irrefutable
              obtain ⟨_, rfl⟩ := pure_ok.mp rest
              have empty : scopes = [] := by
                have zero : scopes.length = 0 := by simpa [retainArms, irrefutable] using length
                exact List.length_eq_zero_iff.mp zero
              subst scopes
              refine ⟨headExtension, fun assignment root valid => ?_⟩
              obtain ⟨beforeValid, selected⟩ := headFacts assignment root valid
              refine ⟨beforeValid, fun environment decoded trusted input inputDecoded inputTrusted selectedScope member active => ?_⟩
              obtain rfl := List.mem_singleton.mp member
              obtain ⟨failed, values, matched, evaluated⟩ := selected environment decoded trusted input inputDecoded inputTrusted active
              exact ⟨failed, values, body, by simp [selectArm, matched], evaluated⟩
            · rename_i refutable
              simp only [pure_bind] at rest
              have tailLength : scopes.length = (retainArms program.enums arms).length := by
                simpa [retainArms, refutable] using length
              obtain ⟨tailExtension, tailMeaning⟩ := lowerArms_sound checked tags romValid callSound callProvenance tailLength rest
              refine ⟨headExtension.trans tailExtension, fun assignment root valid => ?_⟩
              obtain ⟨s₃valid, tails⟩ := tailMeaning assignment (headExtension.active root) valid
              obtain ⟨beforeValid, head⟩ := headFacts assignment root s₃valid
              refine ⟨beforeValid, fun environment decoded trusted input inputDecoded inputTrusted selected member active => ?_⟩
              rcases List.mem_cons.mp member with rfl | member
              · obtain ⟨failed, values, matched, evaluated⟩ := head environment decoded trusted input inputDecoded inputTrusted active
                exact ⟨failed, values, body, by simp [selectArm, matched], evaluated⟩
              · obtain ⟨failed, values, selectedBody, matched, evaluated⟩ :=
                  tails environment decoded trusted input inputDecoded inputTrusted selected member (headExtension.active active)
                have conditionFailed : ¬AllZero conditions assignment := failed conditions (by simp)
                have noMatch : pat.bindings input = none := by
                  rcases patternMeaning assignment input inputDecoded with
                    ⟨_, _, conditionsZero, _⟩ | ⟨noMatch, _⟩
                  · exact (conditionFailed conditionsZero).elim
                  · exact noMatch
                exact ⟨fun earlier member => failed earlier (List.mem_append_left _ member),
                  values, selectedBody, by simpa [selectArm, noMatch] using matched, evaluated⟩
  termination_by sizeOf arms
  decreasing_by
    all_goals simp_all only [Prod.mk.sizeOf_spec, List.cons.sizeOf_spec]
    all_goals omega
end

end Aiur.Optimized.Compiler
