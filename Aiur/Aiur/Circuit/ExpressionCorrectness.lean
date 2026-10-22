import Aiur.Circuit.PatternCorrectness
import Aiur.Circuit.ValueCorrectness
import Aiur.Circuit.ValidationCorrectness
import Aiur.WireComposition
import Aiur.WireMemory
import Aiur.InputTypes

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Interpreting decoded call premises suffices for local compiler soundness. -/
def CallsSound [Field F] [DecidableEq F] (decls : Declarations)
    (calls : Circuit.CallRelation F) (sourceCalls : Aiur.CallRelation F) : Prop :=
  ∀ name args result, calls name args result → ∀ values value,
    DecodesValues decls args values → result.decode decls = some value → sourceCalls name values value

/-- The output's canonical encoding and its evaluation are proved together. -/
def ExpressionMeaning [Field F] [DecidableEq F] (decls : Declarations)
    (rom : WireROM F) (calls : Aiur.CallRelation F) (locals : Environment F)
    (expr : Expr F) (output : WireValue F) : Prop :=
  ∃ value, output.decode decls = some value ∧ ROMEvalExprWith decls (rom.decode decls) calls locals expr value

mutual
  theorem lowerExpr_sound [Field F] [DecidableEq F]
      {program : Program F} (checked : checkDeclarations program.enums = .ok ())
      (tags : program.enums.tagsValid F = true)
      {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
      (callSound : CallsSound program.enums calls sourceCalls)
      {function : String} {locals : Locals F} {enable : ArithExpr F} {expr : Expr F} {output : Symbolic F}
      {before after : BuildState F}
      (compiled : lowerExpr program function locals enable expr before = .ok (output, after))
      {assignment : Var → F} (valid : after.Valid rom calls assignment) :
      before.Valid rom calls assignment ∧ (enable.denote assignment = 1 → ∀ environment,
        DecodesEnvironment program.enums (localsEnvironment locals assignment) environment →
        ExpressionMeaning program.enums rom sourceCalls environment expr
          (output.map (ArithExpr.denote assignment))) := by
    cases expr with
    | literal value =>
        obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [lowerExpr] using compiled)
        exact ⟨valid, fun _ _ _ => ⟨.field value, by simp [Scalar.Circuit.ArithExpr.denote], .literal⟩⟩
    | var name =>
        cases found : locals.find? (·.1 == name) with
        | none => simp [lowerExpr, found] at compiled
        | some binding =>
            rcases binding with ⟨bindingName, wire⟩
            have same : bindingName = name := by simpa using List.find?_some found
            subst bindingName
            obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [lowerExpr, found] using compiled)
            refine ⟨valid, fun _ environment decoded => ?_⟩
            obtain ⟨value, lookup, valueDecode⟩ := decoded.find name (wire := (name, wire.map (ArithExpr.denote assignment)))
              (by simp [localsEnvironment, List.find?_map, Function.comp_def, found])
            exact ⟨value, valueDecode, .var lookup⟩
    | tuple items =>
        simp only [lowerExpr] at compiled
        obtain ⟨wires, middle, argsRun, finished⟩ := bind_ok.mp compiled
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨previous, evaluated⟩ := lowerArgs_sound checked tags callSound argsRun valid
        refine ⟨previous, fun active environment decoded => ?_⟩
        obtain ⟨values, decodedValues, evaluations⟩ := evaluated active environment decoded
        exact ⟨.tuple values, by
          simpa only [WireValue.map_tuple] using WireValue.decode_tuple checked tags decodedValues,
          .tuple evaluations⟩
    | construct name ctor args =>
        cases found : program.enums.findEnum? name with
        | none => simp [lowerExpr, found] at compiled
        | some definition =>
            cases atIndex : definition.constructors[definition.constructors.findIdx (·.name == ctor)]? with
            | none => simp [lowerExpr, found, atIndex] at compiled
            | some constructor =>
                simp only [lowerExpr, found, atIndex] at compiled
                obtain ⟨wires, s₁, argsRun, rest⟩ := bind_ok.mp compiled
                split at rest
                · simp [StateT.bind, bind, Except.bind] at rest
                · rename_i types
                  obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp rest
                  obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
                  obtain ⟨layout, middle, layoutRun, rest⟩ := bind_ok.mp rest
                  obtain ⟨expansion, rfl⟩ := getLayout_eq layoutRun
                  split at rest
                  · simp [StateT.bind, bind, Except.bind] at rest
                  · obtain ⟨⟨⟩, middle, unchanged, finished⟩ := bind_ok.mp rest
                    obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
                    obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                    obtain ⟨previous, evaluated⟩ := lowerArgs_sound checked tags callSound argsRun valid
                    refine ⟨previous, fun active environment decoded => ?_⟩
                    obtain ⟨values, argsDecode, argsEval⟩ := evaluated active environment decoded
                    have ctorName : constructor.name = ctor := by
                      simpa using List.findIdx_of_getElem?_eq_some atIndex
                    refine ⟨.construct name ctor values, ?_, .construct argsEval⟩
                    have constructed := WireValue.decode_construct checked tags found atIndex argsDecode
                      (by simpa [Function.comp_def, WireValue.map] using (not_ne_iff.mp types)) expansion
                    simpa [ctorName, WireValue.map, List.map_flatMap, List.flatMap_map,
                      List.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using constructed
    | project operand index =>
        simp only [lowerExpr] at compiled
        obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp compiled
        rcases input with ⟨type, words⟩
        cases type with
        | field | ptr | enum => simp at rest
        | tuple types =>
            dsimp only at rest
            obtain ⟨wires, s₂, splitRun, rest⟩ := bind_ok.mp rest
            have unchanged := (splitValues_spec splitRun).1
            subst s₂
            cases projected : wires[index]? with
            | none => simp [projected] at rest
            | some result =>
                obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [projected] using rest)
                obtain ⟨previous, evaluated⟩ := lowerExpr_sound checked tags callSound inputRun valid
                refine ⟨previous, fun active environment decoded => ?_⟩
                obtain ⟨value, inputDecode, inputEval⟩ := evaluated active environment decoded
                obtain ⟨values, rfl, decodedValues⟩ := splitValues_decode checked splitRun inputDecode
                obtain ⟨value, valueAt, valueDecode⟩ := decodedValues.getElem (index := index)
                  (wire := result.map (ArithExpr.denote assignment))
                  (by simp [List.getElem?_map, projected])
                exact ⟨value, valueDecode, .project inputEval (by simp [projectValue, valueAt, pure, Except.pure])⟩
    | letValue pattern operand body =>
        simp only [lowerExpr] at compiled
        obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨⟨test, bindings⟩, s₂, patternRun, rest⟩ := bind_ok.mp rest
        obtain ⟨⟨⟩, s₃, guardRun, bodyRun⟩ := bind_ok.mp rest
        obtain ⟨s₃valid, bodyEval⟩ := lowerExpr_sound checked tags callSound bodyRun valid
        obtain ⟨s₂valid, equation⟩ := constrain_valid guardRun s₃valid
        obtain ⟨s₁valid, _, matched⟩ := lowerPattern_sound checked tags patternRun s₂valid
        obtain ⟨previous, inputEval⟩ := lowerExpr_sound checked tags callSound inputRun s₁valid
        refine ⟨previous, fun active environment decoded => ?_⟩
        obtain ⟨inputValue, inputDecode, inputEval⟩ := inputEval active environment decoded
        have testOne : test.denote assignment = 1 := by
          change enable.denote assignment * (test.denote assignment - 1) = 0 at equation
          simpa [active, sub_eq_zero] using equation
        rcases matched inputValue inputDecode with ⟨values, matched, _, decodedBindings⟩ | ⟨_, zero⟩
        · obtain ⟨value, resultDecode, evaluated⟩ := bodyEval active (values ++ environment)
            (by simpa only [localsEnvironment_append] using decodedBindings.append decoded)
          exact ⟨value, resultDecode, .letValue inputEval matched evaluated⟩
        · exact (zero_ne_one (zero.symm.trans testOne)).elim
    | store operand =>
        simp only [lowerExpr] at compiled
        obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨address, s₂, addressRun, rest⟩ := bind_ok.mp rest
        obtain ⟨⟨⟩, s₃, booleanRun, rest⟩ := bind_ok.mp rest
        obtain ⟨⟨⟩, s₄, validationRun, rest⟩ := bind_ok.mp rest
        obtain ⟨⟨⟩, s₅, cellRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨s₄valid, cell⟩ := requireCell_valid cellRun valid
        have s₃valid := (validateValue_sound checked validationRun s₄valid).1
        have s₂valid := (boolean_valid booleanRun s₃valid).1
        have s₁valid := fresh_valid addressRun s₂valid
        obtain ⟨previous, evaluated⟩ := lowerExpr_sound checked tags callSound inputRun s₁valid
        refine ⟨previous, fun active environment decoded => ?_⟩
        obtain ⟨value, valueDecode, valueEval⟩ := evaluated active environment decoded
        obtain ⟨type, _, layout, expansion, _⟩ := WireValue.decode_spec valueDecode
        have names := (Declarations.layout_parts expansion).1
        refine ⟨.ptr value.type (assignment address), ?_, .store valueEval ?_⟩
        · simpa only [WireValue.map_ptr, Scalar.Circuit.ArithExpr.denote, type, WireValue.map, WireValue.ptr, List.map_cons, List.map_nil] using
            WireValue.decode_ptr names (assignment address)
        · exact WireROM.mem_decode.mpr ⟨_, cell active, valueDecode⟩
    | load operand =>
        simp only [lowerExpr] at compiled
        obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp compiled
        rcases input with ⟨type, words⟩
        cases type with
        | field | tuple | enum => simp at rest
        | ptr target =>
            cases words with
            | nil => simp at rest
            | cons address words => cases words with
              | cons => simp at rest
              | nil =>
                  dsimp only at rest
                  obtain ⟨result, s₂, resultRun, rest⟩ := bind_ok.mp rest
                  obtain ⟨⟨⟩, s₃, booleanRun, rest⟩ := bind_ok.mp rest
                  obtain ⟨⟨⟩, s₄, validationRun, rest⟩ := bind_ok.mp rest
                  obtain ⟨⟨⟩, s₅, cellRun, finished⟩ := bind_ok.mp rest
                  obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                  obtain ⟨s₄valid, cell⟩ := requireCell_valid cellRun valid
                  obtain ⟨s₃valid, resultDecoded⟩ := validateValue_sound checked validationRun s₄valid
                  have s₂valid := (boolean_valid booleanRun s₃valid).1
                  have s₁valid := freshValue_valid resultRun s₂valid
                  obtain ⟨previous, evaluated⟩ := lowerExpr_sound checked tags callSound inputRun s₁valid
                  refine ⟨previous, fun active environment decoded => ?_⟩
                  obtain ⟨value, valueDecode, valueEval⟩ := evaluated active environment decoded
                  have same := WireValue.ptr_decoded_eq valueDecode
                  subst value
                  obtain ⟨value, resultDecode⟩ := resultDecoded active
                  refine ⟨value, resultDecode, .load valueEval (WireROM.mem_decode.mpr ⟨_, cell active, resultDecode⟩) ?_⟩
                  exact (WireValue.decode_spec resultDecode).1.trans (freshValue_spec resultRun).2.2.1
    | hint type key channel =>
        simp only [lowerExpr] at compiled
        obtain ⟨input, s₁, keyRun, rest⟩ := bind_ok.mp compiled
        split at rest
        · simp [StateT.bind, bind, Except.bind] at rest
        · rename_i free
          have free : type.pointerFree program.enums = true := by simpa using free
          obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp rest
          obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
          obtain ⟨result, s₂, freshRun, rest⟩ := bind_ok.mp rest
          obtain ⟨⟨⟩, s₃, validationRun, finished⟩ := bind_ok.mp rest
          obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
          obtain ⟨s₂valid, resultDecoded⟩ := validateValue_sound checked validationRun valid
          have s₁valid := freshValue_valid freshRun s₂valid
          obtain ⟨previous, keyMeaning⟩ := lowerExpr_sound checked tags callSound keyRun s₁valid
          refine ⟨previous, fun active environment decoded => ?_⟩
          obtain ⟨keyValue, _, keyEval⟩ := keyMeaning active environment decoded
          obtain ⟨value, resultDecode⟩ := resultDecoded active
          have spec := WireValue.decode_spec resultDecode
          have shape : value.type = type := spec.1.trans (freshValue_spec freshRun).2.2.1
          have valueFree := Value.pointerFree_of_type (shape ▸ free) spec.2.1
          obtain ⟨constant, same⟩ := value.exists_constant valueFree
          subst value
          exact ⟨_, resultDecode, .hint keyEval (by
            simpa [Value.WellTyped, Value.hasType] using And.intro shape spec.2.1)⟩
    | neg operand =>
        simp only [lowerExpr] at compiled
        obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨polynomial, s₂, fieldRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := asField_ok fieldRun
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨previous, evaluated⟩ := lowerExpr_sound checked tags callSound inputRun valid
        refine ⟨previous, fun active environment decoded => ?_⟩
        obtain ⟨value, valueDecode, valueEval⟩ := evaluated active environment decoded
        simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq] at valueDecode
        subst value
        exact ⟨.field (0 - polynomial.denote assignment), by simp [Scalar.Circuit.ArithExpr.denote],
          .neg valueEval (by simp [evalNeg])⟩
    | assertEq message left right =>
        simp only [lowerExpr] at compiled
        obtain ⟨leftWire, s₁, leftRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨rightWire, s₂, rightRun, rest⟩ := bind_ok.mp rest
        split at rest
        · simp [StateT.bind, bind, Except.bind] at rest
        · rename_i free
          obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp rest
          obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
          obtain ⟨⟨⟩, last, equated, finished⟩ := bind_ok.mp rest
          obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
          obtain ⟨valid₂, equal⟩ := constrainValue_sound equated valid
          obtain ⟨valid₁, rightEval⟩ := lowerExpr_sound checked tags callSound rightRun valid₂
          obtain ⟨previous, leftEval⟩ := lowerExpr_sound checked tags callSound leftRun valid₁
          refine ⟨previous, fun active environment decoded => ?_⟩
          obtain ⟨x, xDecode, xEval⟩ := leftEval active environment decoded
          obtain ⟨y, yDecode, yEval⟩ := rightEval active environment decoded
          have same : x = y := Option.some.inj (xDecode.symm.trans ((equal active) ▸ yDecode))
          have data := WireValue.decode_spec xDecode
          have pointerFree : x.pointerFree = true := Value.pointerFree_of_type
            (by simpa [data.1, WireValue.type_map] using free) data.2.1
          exact ⟨.tuple [], by simpa only [WireValue.map_tuple, List.map_nil] using
            WireValue.decode_tuple checked tags (.nil : DecodesValues program.enums [] []),
            .assertEq xEval yEval (evalAssertEq_ok.mpr ⟨pointerFree, same, rfl⟩)⟩
    | binary op left right =>
        simp only [lowerExpr] at compiled
        obtain ⟨leftWire, s₁, leftRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨leftPoly, s₂, leftField, rest⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := asField_ok leftField
        obtain ⟨rightWire, s₃, rightRun, rest⟩ := bind_ok.mp rest
        obtain ⟨rightPoly, s₄, rightField, rest⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := asField_ok rightField
        cases op with
        | add | sub | mul =>
            obtain ⟨rfl, rfl⟩ := pure_ok.mp rest
            obtain ⟨s₁valid, rightEval⟩ := lowerExpr_sound checked tags callSound rightRun valid
            obtain ⟨previous, leftEval⟩ := lowerExpr_sound checked tags callSound leftRun s₁valid
            refine ⟨previous, fun active environment decoded => ?_⟩
            obtain ⟨x, xDecode, xEval⟩ := leftEval active environment decoded
            obtain ⟨y, yDecode, yEval⟩ := rightEval active environment decoded
            simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq] at xDecode yDecode
            subst x; subst y
            exact ⟨_, WireValue.decode_field _ _, .binary xEval yEval (by
              simp [evalBinOp, Scalar.Circuit.ArithExpr.denote])⟩
        | div =>
            obtain ⟨inverse, s₅, inverseRun, rest⟩ := bind_ok.mp rest
            obtain ⟨⟨⟩, s₆, equationRun, finished⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨s₅valid, equation⟩ := constrain_valid equationRun valid
            have s₃valid := fresh_valid inverseRun s₅valid
            obtain ⟨s₁valid, rightEval⟩ := lowerExpr_sound checked tags callSound rightRun s₃valid
            obtain ⟨previous, leftEval⟩ := lowerExpr_sound checked tags callSound leftRun s₁valid
            refine ⟨previous, fun active environment decoded => ?_⟩
            obtain ⟨x, xDecode, xEval⟩ := leftEval active environment decoded
            obtain ⟨y, yDecode, yEval⟩ := rightEval active environment decoded
            simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq] at xDecode yDecode
            subst x; subst y
            change enable.denote assignment * (rightPoly.denote assignment * assignment inverse - 1) = 0 at equation
            rw [active, one_mul] at equation
            exact ⟨_, WireValue.decode_field _ _, .binary xEval yEval (by
              simp [evalBinOp, Scalar.Circuit.ArithExpr.denote, Scalar.Circuit.inverse_nonzero equation, Scalar.Circuit.inverse_eq equation,
                div_eq_mul_inv])⟩
    | call name args =>
        cases found : program.findSignature? name with
        | none => simp [lowerExpr, found] at compiled
        | some callee =>
            simp only [lowerExpr, found] at compiled
            obtain ⟨arguments, s₁, argsRun, rest⟩ := bind_ok.mp compiled
            split at rest
            · simp [StateT.bind, bind, Except.bind] at rest
            · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp rest
              obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
              obtain ⟨result, s₂, resultRun, rest⟩ := bind_ok.mp rest
              obtain ⟨⟨⟩, s₃, booleanRun, rest⟩ := bind_ok.mp rest
              obtain ⟨⟨⟩, s₄, argsValidation, rest⟩ := bind_ok.mp rest
              obtain ⟨⟨⟩, s₅, resultValidation, rest⟩ := bind_ok.mp rest
              simp [StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at rest
              obtain ⟨rfl, rfl⟩ := rest
              have s₅valid : s₅.Valid rom calls assignment := valid.of_subset
                (fun _ h => h) (fun _ h => by simp [h]) (fun _ h => h)
              obtain ⟨s₄valid, resultDecoded⟩ := validateValue_sound checked resultValidation s₅valid
              have s₃valid := (validateValues_sound checked argsValidation s₄valid).1
              have s₂valid := (boolean_valid booleanRun s₃valid).1
              have s₁valid := freshValue_valid resultRun s₂valid
              obtain ⟨previous, argsEval⟩ := lowerArgs_sound checked tags callSound argsRun s₁valid
              refine ⟨previous, fun active environment decoded => ?_⟩
              obtain ⟨values, argsDecode, argsEval⟩ := argsEval active environment decoded
              obtain ⟨value, resultDecode⟩ := resultDecoded active
              refine ⟨value, resultDecode, .call argsEval ?_⟩
              exact callSound name _ _ (valid.calls ⟨name, arguments, result, enable⟩ (by simp) active)
                values value argsDecode (by simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultDecode)
    | matchValue scrutinee arms =>
        simp only [lowerExpr] at compiled
        obtain ⟨⟨⟩, s₁, checkRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨_, rfl⟩ := lift_eq_ok checkRun
        obtain ⟨type, s₂, typeRun, rest⟩ := bind_ok.mp rest
        obtain ⟨_, rfl⟩ := lift_eq_ok typeRun
        obtain ⟨input, s₃, scrutineeRun, rest⟩ := bind_ok.mp rest
        obtain ⟨result, s₄, resultRun, rest⟩ := bind_ok.mp rest
        obtain ⟨⟨⟩, s₅, validationRun, rest⟩ := bind_ok.mp rest
        obtain ⟨selectors, s₆, armsRun, rest⟩ := bind_ok.mp rest
        obtain ⟨⟨⟩, s₇, exclusionRun, rest⟩ := bind_ok.mp rest
        obtain ⟨⟨⟩, s₈, sumRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨s₇valid, equation⟩ := constrain_valid sumRun valid
        have s₆valid := excludePairs_valid exclusionRun s₇valid
        obtain ⟨s₅valid, armsEval⟩ := lowerArms_sound checked tags callSound armsRun s₆valid
        have s₄valid := (validateValue_sound checked validationRun s₅valid).1
        have s₃valid := freshValue_valid resultRun s₄valid
        obtain ⟨previous, inputEval⟩ := lowerExpr_sound checked tags callSound scrutineeRun s₃valid
        refine ⟨previous, fun active environment decoded => ?_⟩
        obtain ⟨inputValue, inputDecode, evaluated⟩ := inputEval active environment decoded
        have sum : (selectors.map (ArithExpr.denote assignment)).sum = 1 := by
          simpa [Scalar.Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote_foldl_add,
            active, sub_eq_zero] using equation
        have nonzero : ∃ selector ∈ selectors, selector.denote assignment ≠ 0 := by
          by_contra absent
          push Not at absent
          have zero : (selectors.map (ArithExpr.denote assignment)).sum = 0 :=
            List.sum_eq_zero (by simpa using absent)
          exact zero_ne_one (zero.symm.trans sum)
        obtain ⟨selector, member, nonzero⟩ := nonzero
        obtain ⟨_, bindings, body, selected, value, valueDecode, bodyEval⟩ :=
          armsEval environment decoded inputValue inputDecode selector member nonzero
        exact ⟨value, valueDecode, .matchValue evaluated selected bodyEval⟩
  termination_by sizeOf expr

  theorem lowerArgs_sound [Field F] [DecidableEq F]
      {program : Program F} (checked : checkDeclarations program.enums = .ok ())
      (tags : program.enums.tagsValid F = true)
      {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
      (callSound : CallsSound program.enums calls sourceCalls)
      {function : String} {locals : Locals F} {enable : ArithExpr F}
      {args : List (Expr F)} {outputs : List (Symbolic F)} {before after : BuildState F}
      (compiled : lowerArgs program function locals enable args before = .ok (outputs, after))
      {assignment : Var → F} (valid : after.Valid rom calls assignment) :
      before.Valid rom calls assignment ∧ (enable.denote assignment = 1 → ∀ environment,
        DecodesEnvironment program.enums (localsEnvironment locals assignment) environment → ∃ values,
          DecodesValues program.enums (outputs.map (WireValue.map (ArithExpr.denote assignment))) values ∧
          ROMEvalArgsWith program.enums (rom.decode program.enums) sourceCalls environment args values) := by
    cases args with
    | nil =>
        obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [lowerArgs] using compiled)
        exact ⟨valid, fun _ _ _ => ⟨[], .nil, .nil⟩⟩
    | cons arg args =>
        simp only [lowerArgs] at compiled
        obtain ⟨head, middle, headRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨middleValid, tailEval⟩ := lowerArgs_sound checked tags callSound tailRun valid
        obtain ⟨previous, headEval⟩ := lowerExpr_sound checked tags callSound headRun middleValid
        refine ⟨previous, fun active environment decoded => ?_⟩
        obtain ⟨head, headDecode, headEval⟩ := headEval active environment decoded
        obtain ⟨tail, tailDecode, tailEval⟩ := tailEval active environment decoded
        exact ⟨head :: tail, .cons headDecode tailDecode, .cons headEval tailEval⟩
  termination_by sizeOf args

  /-- A selected branch is exactly the first matching source arm, with decoded bindings. -/
  theorem lowerArms_sound [Field F] [DecidableEq F]
      {program : Program F} (checked : checkDeclarations program.enums = .ok ())
      (tags : program.enums.tagsValid F = true)
      {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
      (callSound : CallsSound program.enums calls sourceCalls)
      {function : String} {locals : Locals F} {scrutinee result : Symbolic F} {remaining : ArithExpr F}
      {arms : List (Pattern F × Expr F)} {selectors : List (ArithExpr F)} {before after : BuildState F}
      (compiled : lowerArms program function locals scrutinee result remaining arms before = .ok (selectors, after))
      {assignment : Var → F} (valid : after.Valid rom calls assignment) :
      before.Valid rom calls assignment ∧ ∀ environment,
        DecodesEnvironment program.enums (localsEnvironment locals assignment) environment → ∀ input,
        (scrutinee.map (ArithExpr.denote assignment)).decode program.enums = some input →
        ∀ selector ∈ selectors, selector.denote assignment ≠ 0 →
          remaining.denote assignment ≠ 0 ∧ ∃ bindings body,
            selectArm input arms = some (bindings, body) ∧
            ExpressionMeaning program.enums rom sourceCalls (bindings ++ environment) body
              (result.map (ArithExpr.denote assignment)) := by
    cases arms with
    | nil =>
        obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [lowerArms] using compiled)
        exact ⟨valid, by simp⟩
    | cons arm arms =>
        rcases hArm : arm with ⟨pattern, body⟩
        simp only [hArm, lowerArms] at compiled
        obtain ⟨⟨test, bindings⟩, s₁, patternRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨selector, s₂, selectorRun, rest⟩ := bind_ok.mp rest
        obtain ⟨⟨⟩, s₃, booleanRun, rest⟩ := bind_ok.mp rest
        obtain ⟨⟨⟩, s₄, equationRun, rest⟩ := bind_ok.mp rest
        obtain ⟨bodyWire, s₅, bodyRun, rest⟩ := bind_ok.mp rest
        obtain ⟨⟨⟩, s₆, valueRun, rest⟩ := bind_ok.mp rest
        have headFacts (endValid : s₆.Valid rom calls assignment) :
            before.Valid rom calls assignment ∧
            (∀ input, (scrutinee.map (ArithExpr.denote assignment)).decode program.enums = some input →
              PatternTest program.enums (pattern.bindings input) (test.denote assignment)
                (localsEnvironment bindings assignment)) ∧
            assignment selector = remaining.denote assignment * test.denote assignment ∧
            (assignment selector = 0 ∨ assignment selector = 1) ∧
            (assignment selector = 1 → ∀ environment,
              DecodesEnvironment program.enums (localsEnvironment (bindings ++ locals) assignment) environment →
              ExpressionMeaning program.enums rom sourceCalls environment body
                (result.map (ArithExpr.denote assignment))) := by
          obtain ⟨s₅valid, resultEq⟩ := constrainValue_sound valueRun endValid
          obtain ⟨s₄valid, evaluated⟩ := lowerExpr_sound checked tags callSound bodyRun s₅valid
          obtain ⟨s₃valid, equation⟩ := constrain_valid equationRun s₄valid
          obtain ⟨s₂valid, boolean⟩ := boolean_valid booleanRun s₃valid
          have s₁valid := fresh_valid selectorRun s₂valid
          obtain ⟨previous, _, matched⟩ := lowerPattern_sound checked tags patternRun s₁valid
          refine ⟨previous, matched, sub_eq_zero.mp equation, boolean, fun active environment decoded => ?_⟩
          rw [resultEq active]
          exact evaluated active environment decoded
        have headSelected (endValid : s₆.Valid rom calls assignment) (active : assignment selector ≠ 0)
            (environment : Environment F)
            (decoded : DecodesEnvironment program.enums (localsEnvironment locals assignment) environment)
            (input : Value F) (inputDecode : (scrutinee.map (ArithExpr.denote assignment)).decode program.enums = some input) :
            remaining.denote assignment ≠ 0 ∧ ∃ matched body',
              selectArm input ((pattern, body) :: arms) = some (matched, body') ∧
              ExpressionMeaning program.enums rom sourceCalls (matched ++ environment) body'
                (result.map (ArithExpr.denote assignment)) := by
          obtain ⟨_, matched, equation, boolean, evaluated⟩ := headFacts endValid
          have one := boolean.resolve_left active
          have remainingNonzero : remaining.denote assignment ≠ 0 := by
            intro zero
            exact active (by simpa [zero] using equation)
          rcases matched input inputDecode with ⟨values, matched, _, bindingsDecode⟩ | ⟨_, zero⟩
          · refine ⟨remainingNonzero, values, body, by simp [selectArm, matched], ?_⟩
            exact evaluated one (values ++ environment)
              (by simpa only [localsEnvironment_append] using bindingsDecode.append decoded)
          · exact (active (by simpa [zero] using equation)).elim
        split at rest
        · obtain ⟨rfl, rfl⟩ := pure_ok.mp rest
          refine ⟨(headFacts valid).1, ?_⟩
          intro environment decoded input inputDecode chosen member active
          obtain rfl := List.mem_singleton.mp member
          exact headSelected valid active environment decoded input inputDecode
        · simp only [pure_bind] at rest
          obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
          obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
          obtain ⟨s₆valid, tailEval⟩ := lowerArms_sound checked tags callSound tailRun valid
          obtain ⟨previous, matched, _, _, _⟩ := headFacts s₆valid
          refine ⟨previous, ?_⟩
          intro environment decoded input inputDecode chosen member active
          rcases List.mem_cons.mp member with same | member
          · subst chosen
            exact headSelected s₆valid active environment decoded input inputDecode
          · obtain ⟨remainingNonzero, selectedBindings, selectedBody, selected, evaluated⟩ :=
              tailEval environment decoded input inputDecode chosen member active
            change remaining.denote assignment * (1 - test.denote assignment) ≠ 0 at remainingNonzero
            have nonzero := (mul_ne_zero_iff.mp remainingNonzero).1
            refine ⟨nonzero, selectedBindings, selectedBody, ?_, evaluated⟩
            rcases matched input inputDecode with ⟨_, _, one, _⟩ | ⟨unmatched, _⟩
            · exact (remainingNonzero (by simp [one])).elim
            · simpa only [selectArm, unmatched] using selected
  termination_by sizeOf arms
  decreasing_by
    all_goals simp_all only [Prod.mk.sizeOf_spec, List.cons.sizeOf_spec]
    all_goals omega
end

end Aiur.Circuit.Compiler
