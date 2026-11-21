import Aiur.Optimized.ValidationWitness
import Aiur.Optimized.FailureWitness
import Aiur.Optimized.PatternIrrefutable
import Aiur.Optimized.ParameterWitness
import Aiur.Optimized.WitnessContext
import Aiur.Optimized.ArmWitness
import Aiur.Optimized.ExpressionCorrectness
import Aiur.Circuit.ExpressionWitness

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
open Circuit.Compiler (Bounded LocalsBounded CallsComplete localsEnvironment localsEnvironment_append)

set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

mutual
  /-- Source evaluation supplies witnesses for the actual scoped compiler,
  including a caller-supplied destination for branch results. -/
  theorem lower_complete {program : Program F} (checked : checkDeclarations program.enums = .ok ())
      (tags : program.enums.tagsValid F = true)
      {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
      (typed : CallsTyped program sourceCalls) (callComplete : CallsComplete program.enums sourceCalls calls)
      {function : String} {locals : Locals F} {scope : ScopeId} {expr : Expr F}
      {target : Option (WireValue Witness)} {output : Symbolic F} {before after : State F}
      (compiled : lower program function locals scope expr target before = .ok (output, after))
      {rom : WireROM F} {initial : Witness → F}
      (stateLayout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
      (valid : before.Valid rom calls initial) (scopeValid : scope < before.scopes.size)
      (localsBound : LocalsBounded before.roles.size locals)
      (targetBound : TargetBound (F := F) before.roles.size target)
      (active : (before.activation scope).denote initial = 1) {environment : Environment F}
      (decoded : DecodesEnvironment program.enums (localsEnvironment locals initial) environment)
      {value : Value F} (targetDecode : TargetDecodes program.enums target initial value)
      (evaluated : ROMEvalExprWith program.enums (rom.decode program.enums) sourceCalls environment expr value) :
      ∃ assignment, Extension rom calls before after initial assignment ∧ Bounded after.roles.size output ∧
        (output.map (Circuit.ArithExpr.denote assignment)).decode program.enums = some value := by
    have allStructure := (lower_scoped compiled scopeLayout scopeValid).1
    rw [lower.eq_def] at compiled
    obtain ⟨wire, middle, valueRun, finishRun⟩ := bind_ok.mp compiled
    have sameScopes := finish_scopes finishRun
    have scopeEq : middle.activation scope = before.activation scope := by
      rw [← allStructure.activation_eq scopeValid]
      simp only [State.activation, sameScopes]
    have body : ∃ assignment, Extension rom calls before middle initial assignment ∧ Bounded middle.roles.size wire ∧
        (wire.map (Circuit.ArithExpr.denote assignment)).decode program.enums = some value := by
      cases exprEq : expr with
      | literal literal =>
          rw [exprEq] at evaluated valueRun
          cases evaluated
          obtain ⟨rfl, rfl⟩ := pure_ok.mp valueRun
          exact ⟨initial, .refl stateLayout ((before.valid_iff_reference rom calls initial).mp valid),
            Circuit.Compiler.bounded_field.mpr rfl, WireValue.decode_field _ _⟩
      | var name =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | var lookup =>
              cases found : locals.find? (·.1 == name) with
              | none => simp [found] at valueRun
              | some binding =>
                  rcases binding with ⟨bindingName, result⟩
                  have same : bindingName = name := by simpa using List.find?_some found
                  subst bindingName
                  obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [found] using valueRun)
                  obtain ⟨actual, actualFound, valueDecode⟩ := decoded.find name
                    (wire := (name, result.map (Circuit.ArithExpr.denote initial)))
                    (by simp [localsEnvironment, List.find?_map, Function.comp_def, found])
                  have equal := (Prod.mk.inj (Option.some.inj (actualFound.symm.trans lookup))).2
                  exact ⟨initial, .refl stateLayout ((before.valid_iff_reference rom calls initial).mp valid),
                    localsBound _ (List.mem_of_find?_eq_some found), equal ▸ valueDecode⟩
      | tuple items =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | tuple itemsEval =>
              obtain ⟨wires, last, argsRun, finished⟩ := bind_ok.mp valueRun
              obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
              obtain ⟨a, ext, bounds, valuesDecode⟩ := lowerArgs_complete checked tags typed callComplete argsRun
                stateLayout scopeLayout valid scopeValid localsBound active decoded itemsEval
              exact ⟨a, ext, Circuit.Compiler.bounded_tuple.mpr bounds, by
                simpa only [WireValue.map_tuple] using WireValue.decode_tuple checked tags valuesDecode⟩
      | construct name ctor args =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | construct argsEval =>
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
                        obtain ⟨typeLayout, layoutState, layoutRun, shapeBind⟩ := bind_ok.mp layoutBind
                        obtain ⟨expansion, stateEq⟩ := getLayout_eq layoutRun
                        subst layoutState
                        split at shapeBind
                        · simp [StateT.bind, bind, Except.bind] at shapeBind
                        · obtain ⟨⟨⟩, unchangedState, unchanged, finished⟩ := bind_ok.mp shapeBind
                          obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                          subst unchangedState
                          obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                          obtain ⟨a, ext, valuesBound, argsDecode⟩ := lowerArgs_complete checked tags typed callComplete
                            argsRun stateLayout scopeLayout valid scopeValid localsBound active decoded argsEval
                          refine ⟨a, ext, ?_, ?_⟩
                          · unfold Bounded
                            refine Layout.enumWords_all _ _ _ ?_ ?_
                            · rfl
                            · intro polynomial member
                              simp only [List.mem_append] at member
                              rcases member with member | member
                              · obtain ⟨item, member, leaf⟩ := List.mem_flatMap.mp member
                                exact valuesBound item member polynomial leaf
                              · have zero : polynomial = .const 0 := List.eq_of_mem_replicate member
                                subst polynomial; rfl
                          · have ctorName : constructor.name = ctor := by
                              simpa using List.findIdx_of_getElem?_eq_some atIndex
                            have constructed := WireValue.decode_construct checked tags found atIndex argsDecode
                              (by simpa [Function.comp_def, WireValue.map] using not_ne_iff.mp types) expansion
                            simpa [ctorName, WireValue.map, List.map_flatMap, List.flatMap_map,
                              List.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using constructed
      | project operand index =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | project inputEval projected =>
              obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp valueRun
              rcases input with ⟨type, words⟩
              cases type with
              | field | ptr | enum => simp at rest
              | tuple types =>
                  dsimp only at rest
                  obtain ⟨items, last, splitRun, tailBind⟩ := bind_ok.mp rest
                  obtain ⟨stateEq, reference⟩ := splitValues_reference splitRun
                  subst last
                  cases found : items[index]? with
                  | none => simp [found] at tailBind
                  | some result =>
                      obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [found] using tailBind)
                      obtain ⟨a, ext, bounds, inputDecode⟩ := lower_complete checked tags typed callComplete inputRun
                        stateLayout scopeLayout valid scopeValid localsBound (by simp [TargetBound]) active decoded
                        (by simp [TargetDecodes]) inputEval
                      obtain ⟨values, rfl, valuesDecode⟩ := Circuit.Compiler.splitValues_decode checked (reference {}) inputDecode
                      obtain ⟨actual, atValue, valueDecode⟩ := valuesDecode.getElem (index := index)
                        (wire := result.map (Circuit.ArithExpr.denote a)) (by simp [List.getElem?_map, found])
                      have same : actual = value := by simpa [projectValue, atValue, pure, Except.pure] using projected
                      exact ⟨a, ext, splitValues_bounded splitRun bounds result (List.mem_of_getElem? found), same ▸ valueDecode⟩
      | letValue pat operand body =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | letValue inputEval matched bodyEval =>
              obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp valueRun
              obtain ⟨⟨conditions, bindings⟩, s₂, patternRun, restBind⟩ := bind_ok.mp rest
              obtain ⟨⟨⟩, s₃, conditionsRun, bodyRun⟩ := bind_ok.mp restBind
              obtain ⟨a, inputExt, inputBound, inputDecode⟩ := lower_complete checked tags typed callComplete inputRun
                stateLayout scopeLayout valid scopeValid localsBound (by simp [TargetBound]) active decoded
                (by simp [TargetDecodes]) inputEval
              obtain ⟨inputStructure, inputScoped⟩ := lower_scoped inputRun scopeLayout scopeValid
              obtain ⟨stateEq, conditionBound, bindingsBound⟩ := pattern_bounded patternRun inputBound
              subst s₂
              have meaning := (pattern_correct checked tags patternRun).2 a _ inputDecode
              obtain ⟨bindingDecode, conditionZero⟩ :
                  DecodesEnvironment program.enums (localsEnvironment bindings a) _ ∧ AllZero conditions a := by
                rcases meaning with ⟨environment, actual, zeros, bindingsDecode⟩ | ⟨absent, _⟩
                · have same := Option.some.inj (actual.symm.trans matched)
                  exact ⟨same ▸ bindingsDecode, zeros⟩
                · rw [matched] at absent; cases absent
              have conditionsRun' : (do for c in conditions do equation scope c : Build F Unit)
                  s₁ = .ok ((), s₃) := bind_ok.mpr ⟨PUnit.unit, s₃, conditionsRun, rfl⟩
              have equationsExt := equations_complete conditionsRun' inputExt.layout inputExt.validAssignment
                (inputScoped.activation_bound scope) conditionBound (Or.inr conditionZero)
              have equationsScoped := equations_scoped conditionsRun' inputScoped (inputStructure.scopeValid scopeValid)
              have equationsScopes := equations_scopes conditionsRun'
              have untilBody := inputExt.trans equationsExt
              have currentActive : (s₃.activation scope).denote a = 1 := by
                simpa only [State.activation, equationsScopes] using
                  (inputExt.activation inputStructure scopeLayout scopeValid).trans active
              have currentScope : scope < s₃.scopes.size := by
                rw [equationsScopes]; exact inputStructure.scopeValid scopeValid
              obtain ⟨b, bodyExt, bodyBound, resultDecode⟩ := lower_complete checked tags typed callComplete bodyRun
                equationsExt.layout equationsScoped equationsExt.validAssignment currentScope
                (Circuit.Compiler.localsBounded_append.mpr
                  ⟨bindingsBound.mono equationsExt.increase, localsBound.mono untilBody.increase⟩)
                (targetBound.mono untilBody.increase) currentActive
                (by simpa only [localsEnvironment_append] using bindingDecode.append (untilBody.environment localsBound decoded))
                (Extension.targetDecode untilBody targetBound targetDecode) bodyEval
              exact ⟨b, untilBody.trans bodyExt, bodyBound, resultDecode⟩
      | store operand =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | @store _ _ stored address operandEval cell =>
              obtain ⟨input, s₁, inputRun, destBind⟩ := bind_ok.mp valueRun
              obtain ⟨result, s₂, destRun, shapeBind⟩ := bind_ok.mp destBind
              have resultType := (destination_spec destRun).2.2
              rcases result with ⟨resultType', resultWords⟩
              dsimp only at resultType
              subst resultType'
              cases resultWords with
              | nil => simp at shapeBind
              | cons addressVar words => cases words with
                | cons => simp at shapeBind
                | nil =>
                    dsimp only at shapeBind
                    obtain ⟨⟨⟩, s₃, cellRun, finished⟩ := bind_ok.mp shapeBind
                    obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                    obtain ⟨a, inputExt, inputBound, inputDecode⟩ := lower_complete checked tags typed callComplete inputRun
                      stateLayout scopeLayout valid scopeValid localsBound (by simp [TargetBound]) active decoded
                      (by simp [TargetDecodes]) operandEval
                    obtain ⟨inputStructure, inputScoped⟩ := lower_scoped inputRun scopeLayout scopeValid
                    obtain ⟨b, destExt, resultBound, resultDecode⟩ := destination_decoded_complete checked tags destRun
                      inputExt.layout inputExt.validAssignment (.ptr stored.type address)
                      (by simp only [Value.type]; exact congrArg Ty.ptr (WireValue.decode_spec inputDecode).1)
                      (by simp) (targetBound.mono inputExt.increase)
                      (Extension.targetDecode inputExt targetBound targetDecode)
                    have destScoped := destination_scoped destRun inputScoped
                    have initialExt := inputExt.trans destExt
                    have resultDecodeB : ((WireValue.mk (.ptr input.type) [addressVar]).map Polynomial.var |>.map
                        (Circuit.ArithExpr.denote b)).decode program.enums = some (.ptr stored.type address) := by
                      simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultDecode
                    have addressEq : b addressVar = address :=
                      (Value.ptr.inj (WireValue.ptr_decoded_eq resultDecode)).2.symm
                    have ab : (Polynomial.var addressVar : Polynomial F).inBounds s₂.roles.size = true :=
                      resultBound _ (by simp)
                    have inputDecodeB := destExt.decoded_value inputBound inputDecode
                    have cellExt := cell_complete cellRun destExt.layout destExt.validAssignment
                      (destScoped.activation_bound scope) ab
                      (inputBound.mono destExt.increase) (by
                        intro _
                        obtain ⟨wireValue, rawCell, storedDecode⟩ := WireROM.mem_decode.mp cell
                        have same := WireValue.decode_injective checked inputDecodeB storedDecode
                        change (b addressVar, input.map (Circuit.ArithExpr.denote b)) ∈ rom.entries
                        rw [addressEq, same]
                        exact rawCell)
                    exact ⟨b, initialExt.trans cellExt, resultBound.mono cellExt.increase, resultDecodeB⟩
      | load operand =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | load pointerEval cell sourceType =>
              obtain ⟨input, s₁, inputRun, shapeBind⟩ := bind_ok.mp valueRun
              rcases input with ⟨type, words⟩
              cases type with
              | field | tuple | enum => simp at shapeBind
              | ptr pointerType =>
                  cases words with
                  | nil => simp at shapeBind
                  | cons address words => cases words with
                    | cons => simp at shapeBind
                    | nil =>
                        dsimp only at shapeBind
                        obtain ⟨result, s₂, destRun, cellBind⟩ := bind_ok.mp shapeBind
                        obtain ⟨⟨⟩, s₃, cellRun, finished⟩ := bind_ok.mp cellBind
                        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                        obtain ⟨a, inputExt, inputBound, pointerDecode⟩ := lower_complete checked tags typed callComplete inputRun
                          stateLayout scopeLayout valid scopeValid localsBound (by simp [TargetBound]) active decoded
                          (by simp [TargetDecodes]) pointerEval
                        obtain ⟨inputStructure, inputScoped⟩ := lower_scoped inputRun scopeLayout scopeValid
                        have pointerEq := WireValue.ptr_decoded_eq pointerDecode
                        rcases Value.ptr.inj pointerEq with ⟨rfl, addressEq⟩
                        rw [addressEq] at cell
                        obtain ⟨wireValue, rawCell, valueDecode⟩ := WireROM.mem_decode.mp cell
                        obtain ⟨b, destExt, resultBound, resultDecode⟩ := destination_decoded_complete checked tags destRun
                          inputExt.layout inputExt.validAssignment value sourceType (WireValue.decode_spec valueDecode).2.1
                          (targetBound.mono inputExt.increase) (Extension.targetDecode inputExt targetBound targetDecode)
                        have resultDecodeB : ((result.map Polynomial.var).map (Circuit.ArithExpr.denote b)).decode
                            program.enums = some value := by simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultDecode
                        have destScoped := destination_scoped destRun inputScoped
                        have initialExt := inputExt.trans destExt
                        have ab := inputBound address (by simp)
                        have cellExt := cell_complete cellRun destExt.layout destExt.validAssignment
                          (destScoped.activation_bound scope) (destExt.bound ab) resultBound (by
                            intro _
                            have same := WireValue.decode_injective checked resultDecodeB valueDecode
                            change (address.denote b, (result.map Polynomial.var).map (Circuit.ArithExpr.denote b)) ∈ rom.entries
                            rw [same, destExt.polynomial ab]
                            exact rawCell)
                        exact ⟨b, initialExt.trans cellExt, resultBound.mono cellExt.increase, resultDecodeB⟩
      | hint type key channel =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | hint keyEval valueTyped =>
              rename_i constant
              obtain ⟨input, s₁, keyRun, rest⟩ := bind_ok.mp valueRun
              split at rest
              · simp [StateT.bind, bind, Except.bind] at rest
              · obtain ⟨⟨⟩, unchangedState, unchanged, destBind⟩ := bind_ok.mp rest
                obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                subst unchangedState
                obtain ⟨result, s₂, destRun, validationBind⟩ := bind_ok.mp destBind
                obtain ⟨⟨⟩, s₃, validationRun, finished⟩ := bind_ok.mp validationBind
                obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                obtain ⟨a, keyExt, _, _⟩ := lower_complete checked tags typed callComplete keyRun
                  stateLayout scopeLayout valid scopeValid localsBound (by simp [TargetBound]) active decoded
                  (by simp [TargetDecodes]) keyEval
                obtain ⟨keyStructure, keyScoped⟩ := lower_scoped keyRun scopeLayout scopeValid
                have valueTyped : constant.type = type ∧ constant.wellFormed program.enums = true := by
                  simpa [Value.WellTyped, Value.hasType] using valueTyped
                obtain ⟨b, destExt, resultBound, resultDecode⟩ := destination_decoded_complete checked tags destRun
                  keyExt.layout keyExt.validAssignment constant.toValue (by simpa using valueTyped.1)
                  (by simpa using valueTyped.2) (targetBound.mono keyExt.increase)
                  (Extension.targetDecode keyExt targetBound targetDecode)
                have destScoped := destination_scoped destRun keyScoped
                have beforeValidation := keyStructure.trans (destination_extends destRun)
                have initialExt := keyExt.trans destExt
                have resultDecodeB : ((result.map Polynomial.var).map (Circuit.ArithExpr.denote b)).decode
                    program.enums = some constant.toValue := by simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultDecode
                obtain ⟨c, validationExt⟩ := validateValue_complete tags validationRun destExt.layout destScoped
                  destExt.validAssignment (beforeValidation.scopeValid scopeValid) resultBound
                  (Or.inr ⟨(Extension.activation initialExt beforeValidation scopeLayout scopeValid).trans active,
                    constant.toValue, resultDecodeB⟩)
                exact ⟨c, initialExt.trans validationExt, resultBound.mono validationExt.increase,
                  validationExt.decoded_value resultBound resultDecodeB⟩
      | neg operand =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | neg inputEval operation =>
              obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp valueRun
              obtain ⟨polynomial, s₂, fieldRun, finished⟩ := bind_ok.mp rest
              obtain ⟨rfl, rfl⟩ := asField_eq fieldRun
              obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
              obtain ⟨a, ext, bounded, inputDecode⟩ := lower_complete checked tags typed callComplete inputRun
                stateLayout scopeLayout valid scopeValid localsBound (by simp [TargetBound]) active decoded
                (by simp [TargetDecodes]) inputEval
              simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq] at inputDecode
              rw [← inputDecode] at operation
              exact ⟨a, ext, by simpa [Scalar.Circuit.ArithExpr.inBounds, State.toReference] using bounded,
                by simpa [evalNeg, Scalar.Circuit.ArithExpr.denote] using operation⟩
      | assertEq message left right =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | assertEq leftEval rightEval operation =>
              obtain ⟨_, same, rfl⟩ := evalAssertEq_ok.mp operation
              obtain ⟨leftWire, s₁, leftRun, rest⟩ := bind_ok.mp valueRun
              obtain ⟨rightWire, s₂, rightRun, restBind⟩ := bind_ok.mp rest
              split at restBind
              · simp [StateT.bind, bind, Except.bind] at restBind
              · obtain ⟨⟨⟩, unchangedState, unchanged, restBind⟩ := bind_ok.mp restBind
                obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                subst unchangedState
                obtain ⟨⟨⟩, last, equated, finished⟩ := bind_ok.mp restBind
                obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                obtain ⟨a, leftExt, leftBound, leftDecode⟩ := lower_complete checked tags typed callComplete leftRun
                  stateLayout scopeLayout valid scopeValid localsBound (by simp [TargetBound]) active decoded
                  (by simp [TargetDecodes]) leftEval
                obtain ⟨leftStructure, leftScoped⟩ := lower_scoped leftRun scopeLayout scopeValid
                obtain ⟨b, rightExt, rightBound, rightDecode⟩ := lower_complete checked tags typed callComplete rightRun
                  leftExt.layout leftScoped leftExt.validAssignment (leftStructure.scopeValid scopeValid)
                  (localsBound.mono leftExt.increase) (by simp [TargetBound])
                  ((leftExt.activation leftStructure scopeLayout scopeValid).trans active)
                  (leftExt.environment localsBound decoded) (by simp [TargetDecodes]) rightEval
                obtain ⟨_, rightScoped⟩ := lower_scoped rightRun leftScoped (leftStructure.scopeValid scopeValid)
                have leftDecodeB := rightExt.decoded_value leftBound leftDecode
                rw [same] at leftDecodeB
                have equal := WireValue.decode_injective checked leftDecodeB rightDecode
                have finalExt := equalValue_complete equated rightExt.layout rightExt.validAssignment
                  (rightScoped.activation_bound scope) (leftBound.mono rightExt.increase) rightBound (Or.inr equal)
                exact ⟨b, (leftExt.trans rightExt).trans finalExt, Circuit.Compiler.bounded_tuple.mpr (by simp), by
                  simpa only [WireValue.map_tuple, List.map_nil] using
                    WireValue.decode_tuple checked tags (.nil : DecodesValues program.enums [] [])⟩
      | binary op left right =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | binary leftEval rightEval operation =>
              obtain ⟨leftWire, s₁, leftRun, rest⟩ := bind_ok.mp valueRun
              obtain ⟨leftPoly, s₂, leftField, restBind⟩ := bind_ok.mp rest
              obtain ⟨rfl, rfl⟩ := asField_eq leftField
              obtain ⟨rightWire, s₃, rightRun, rest⟩ := bind_ok.mp restBind
              obtain ⟨rightPoly, s₄, rightField, restBind⟩ := bind_ok.mp rest
              obtain ⟨rfl, rfl⟩ := asField_eq rightField
              obtain ⟨a, leftExt, leftBound, leftDecode⟩ := lower_complete checked tags typed callComplete leftRun
                stateLayout scopeLayout valid scopeValid localsBound (by simp [TargetBound]) active decoded
                (by simp [TargetDecodes]) leftEval
              obtain ⟨leftStructure, leftScoped⟩ := lower_scoped leftRun scopeLayout scopeValid
              obtain ⟨b, rightExt, rightBound, rightDecode⟩ := lower_complete checked tags typed callComplete rightRun
                leftExt.layout leftScoped leftExt.validAssignment (leftStructure.scopeValid scopeValid)
                (localsBound.mono leftExt.increase) (by simp [TargetBound])
                ((leftExt.activation leftStructure scopeLayout scopeValid).trans active)
                (leftExt.environment localsBound decoded) (by simp [TargetDecodes]) rightEval
              obtain ⟨_, rightScoped⟩ := lower_scoped rightRun leftScoped (leftStructure.scopeValid scopeValid)
              have chainExt := leftExt.trans rightExt
              have lb := Circuit.Compiler.bounded_field.mp (leftBound.mono rightExt.increase)
              have rb := Circuit.Compiler.bounded_field.mp rightBound
              have leftDecodeB := rightExt.decoded_value leftBound leftDecode
              simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq] at leftDecodeB rightDecode
              rw [← leftDecodeB, ← rightDecode] at operation
              cases op with
              | add | sub | mul =>
                  obtain ⟨rfl, rfl⟩ := pure_ok.mp restBind
                  exact ⟨b, chainExt, by simpa [Scalar.Circuit.ArithExpr.inBounds, State.toReference] using And.intro lb rb,
                    by simpa [evalBinOp, Scalar.Circuit.ArithExpr.denote] using operation⟩
              | div =>
                  have nonzero : rightPoly.denote b ≠ 0 := by
                    intro zero
                    simp [evalBinOp, zero] at operation
                  have quotient : Value.field (leftPoly.denote b / rightPoly.denote b) = value := by
                    simpa [evalBinOp, nonzero] using operation
                  cases folded : rightPoly.constantInverse? with
                  | some inverse =>
                      simp only [folded] at restBind
                      obtain ⟨rfl, rfl⟩ := pure_ok.mp restBind
                      refine ⟨b, chainExt, ?_, ?_⟩
                      · simpa [Scalar.Circuit.ArithExpr.inBounds, State.toReference] using lb
                      · simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq]
                        change Value.field (leftPoly.denote b * inverse) = value
                        rw [(Polynomial.constantInverse?_sound folded b).2, ← div_eq_mul_inv]
                        exact quotient
                  | none =>
                      simp only [folded] at restBind
                      obtain ⟨inverse, s₅, freshRun, rest⟩ := bind_ok.mp restBind
                      obtain ⟨⟨⟩, s₆, inverseRun, finished⟩ := bind_ok.mp rest
                      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                      obtain ⟨c, freshExt, inverseBound, inverseEq⟩ := fresh_complete freshRun rightExt.layout
                        rightExt.validAssignment (rightPoly.denote b)⁻¹
                      have freshScoped := fresh_scoped freshRun rightScoped
                      have ib : (Polynomial.var inverse : Polynomial F).inBounds s₅.roles.size = true := by
                        simpa [Scalar.Circuit.ArithExpr.inBounds, State.toReference] using inverseBound
                      have inverseExt := equation_complete inverseRun freshExt.layout freshExt.validAssignment (by
                        simpa only [Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true, and_true, State.toReference] using
                          And.intro (freshScoped.activation_bound scope) (And.intro (freshExt.bound rb) ib)) (by
                          change (s₅.activation scope).denote c * (rightPoly.denote c * c inverse - 1) = 0
                          rw [freshExt.polynomial rb, inverseEq]
                          simp [nonzero])
                      refine ⟨c, (chainExt.trans freshExt).trans inverseExt, ?_, ?_⟩
                      · simpa [Scalar.Circuit.ArithExpr.inBounds, State.toReference] using
                          And.intro ((freshExt.trans inverseExt).bound lb) (inverseExt.bound ib)
                      · simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq]
                        change Value.field (leftPoly.denote c * c inverse) = value
                        rw [freshExt.polynomial lb, inverseEq, ← div_eq_mul_inv]
                        exact quotient
      | call name args =>
          rw [exprEq] at evaluated valueRun
          cases evaluated with
          | call argsEval calleeEval =>
              cases found : program.findSignature? name with
              | none => simp [found] at valueRun
              | some callee =>
                  simp only [found] at valueRun
                  obtain ⟨arguments, s₁, argsRun, rest⟩ := bind_ok.mp valueRun
                  split at rest
                  · simp [StateT.bind, bind, Except.bind] at rest
                  · obtain ⟨⟨⟩, unchangedState, unchanged, destBind⟩ := bind_ok.mp rest
                    obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                    subst unchangedState
                    obtain ⟨result, s₂, destRun, callBind⟩ := bind_ok.mp destBind
                    obtain ⟨⟨⟩, s₅, callRun, finished⟩ := bind_ok.mp callBind
                    obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                    obtain ⟨a, argsExt, argsBound, argsDecode⟩ := lowerArgs_complete checked tags typed callComplete argsRun
                      stateLayout scopeLayout valid scopeValid localsBound active decoded argsEval
                    obtain ⟨argsStructure, argsScoped⟩ := lowerArgs_scoped argsRun scopeLayout scopeValid
                    have resultType := typed _ _ _ calleeEval callee found
                    obtain ⟨b, destExt, resultBound, resultDecode⟩ := destination_decoded_complete checked tags destRun
                      argsExt.layout argsExt.validAssignment value resultType.1 resultType.2
                      (targetBound.mono argsExt.increase) (Extension.targetDecode argsExt targetBound targetDecode)
                    have resultDecodeB : ((result.map Polynomial.var).map (Circuit.ArithExpr.denote b)).decode program.enums =
                        some value := by simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultDecode
                    have destScoped := destination_scoped destRun argsScoped
                    have initialExt := argsExt.trans destExt
                    have callExt := call_complete callRun destExt.layout destExt.validAssignment
                      (destScoped.activation_bound scope)
                      (fun arg member => (argsBound arg member).mono destExt.increase)
                      resultBound (by
                        intro _
                        exact callComplete name _ value calleeEval _ _
                          (destExt.decoded_values argsBound argsDecode) resultDecode)
                    exact ⟨b, initialExt.trans callExt, resultBound.mono callExt.increase, resultDecodeB⟩
      | matchValue scrutinee arms =>
          rw [exprEq] at evaluated valueRun
          have allEval := evaluated
          cases evaluated with
          | matchValue inputEval selected branchEval =>
              obtain ⟨⟨⟩, checkState, checkRun, typeBind⟩ := bind_ok.mp valueRun
              obtain ⟨_, stateEq⟩ := lift_eq_ok checkRun
              subst checkState
              obtain ⟨type, typeState, typeRun, inputBind⟩ := bind_ok.mp typeBind
              obtain ⟨inferred, stateEq⟩ := lift_eq_ok typeRun
              subst typeState
              have typeChecked : inferType program function (environmentTypes environment)
                  (.matchValue scrutinee arms) = .ok type := by
                rw [Circuit.Compiler.decoded_environment_types decoded]
                cases h : inferType program function (locals.map fun (name, value) => (name, value.type))
                  (.matchValue scrutinee arms) <;> simp_all [Except.mapError]
              have resultType := allEval.wellTyped typed (WireROM.decode_wellFormed program.enums rom)
                decoded.wellFormed function type typeChecked
              obtain ⟨input, s₁, inputRun, destBind⟩ := bind_ok.mp inputBind
              obtain ⟨result, s₂, destRun, choiceBind⟩ := bind_ok.mp destBind
              obtain ⟨branches, s₄, choiceRun, armsBind⟩ := bind_ok.mp choiceBind
              obtain ⟨⟨⟩, s₅, armsRun, finished⟩ := bind_ok.mp armsBind
              obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
              obtain ⟨a, inputExt, inputBound, inputDecode⟩ := lower_complete checked tags typed callComplete inputRun
                stateLayout scopeLayout valid scopeValid localsBound (by simp [TargetBound]) active decoded
                (by simp [TargetDecodes]) inputEval
              obtain ⟨inputStructure, inputScoped⟩ := lower_scoped inputRun scopeLayout scopeValid
              obtain ⟨b, destExt, resultBound, resultDecode⟩ := destination_decoded_complete checked tags destRun
                inputExt.layout inputExt.validAssignment value resultType.1 resultType.2
                (targetBound.mono inputExt.increase) (Extension.targetDecode inputExt targetBound targetDecode)
              have resultDecodeB : ((result.map Polynomial.var).map (Circuit.ArithExpr.denote b)).decode program.enums =
                  some value := by simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultDecode
              have destScoped := destination_scoped destRun inputScoped
              have beforeChoice := inputStructure.trans (destination_extends destRun)
              have untilChoice := inputExt.trans destExt
              have inputDecodeC := destExt.decoded_value inputBound inputDecode
              have indexBound := lowerArms_index_lt checked tags armsRun inputDecodeC selected
              let chosen : Fin (retainArms program.enums arms).length := ⟨_, by
                rw [← choice_length choiceRun]
                exact indexBound⟩
              obtain ⟨d, choiceExt, choices⟩ := choice_complete choiceRun destExt.layout destScoped
                destExt.validAssignment (some chosen) (by
                  simpa using (Extension.activation untilChoice beforeChoice scopeLayout scopeValid).trans active)
              have untilArms := untilChoice.trans choiceExt
              have bodyCompletes : ∀ arm ∈ arms, ExprComplete program sourceCalls calls function arm.2 := by
                intro arm member
                have smaller : sizeOf arm.2 < sizeOf (Expr.matchValue scrutinee arms) := by
                  have bound := List.sizeOf_lt_of_mem member
                  cases arm
                  simp_all only [Prod.mk.sizeOf_spec, Expr.matchValue.sizeOf_spec]
                  omega
                intro branchLocals branchScope branchTarget branchOutput first last branchRun branchROM branchInitial
                  branchLayout branchScoped branchValid branchScopeValid branchLocalsBound branchTargetBound
                  branchActive branchEnvironment branchEnvironmentDecode branchValue branchTargetDecode branchEval
                exact lower_complete checked tags typed callComplete branchRun branchLayout branchScoped branchValid
                  branchScopeValid branchLocalsBound branchTargetBound branchActive branchEnvironmentDecode
                  branchTargetDecode branchEval
              obtain ⟨e, armsExt⟩ := lowerArms_complete checked tags bodyCompletes armsRun choiceExt.layout
                (choice_scoped choiceRun destScoped) choiceExt.validAssignment (choice_child_bound choiceRun)
                (localsBound.mono untilArms.increase)
                (inputBound.mono (destExt.trans choiceExt).increase)
                (resultBound.mono choiceExt.increase) (by simp)
                (untilArms.environment localsBound decoded)
                ((destExt.trans choiceExt).decoded_value inputBound inputDecode)
                (by simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using
                  choiceExt.decoded_value resultBound resultDecodeB)
                selected branchEval (by
                  intro i
                  simpa only [choiceSelected, Option.map_some, Option.some.injEq, chosen, eq_comm] using choices i)
                (by simp)
              exact ⟨e, untilArms.trans armsExt, resultBound.mono (choiceExt.trans armsExt).increase,
                (choiceExt.trans armsExt).decoded_value resultBound resultDecodeB⟩
    obtain ⟨assignment, ext, bounded, decodedWire⟩ := body
    cases target with
    | none =>
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finishRun
        exact ⟨assignment, ext, bounded, decodedWire⟩
    | some candidate =>
        obtain ⟨⟨⟩, last, equalRun, finished⟩ := bind_ok.mp finishRun
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        have candidateBound := (targetBound candidate rfl).mono ext.increase
        have candidateDecoded := Extension.targetDecode ext targetBound targetDecode candidate rfl
        have canonical : ((candidate.map Polynomial.var).map (Circuit.ArithExpr.denote assignment)).decode program.enums = some value := by
          simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using candidateDecoded
        have equality := WireValue.decode_injective checked canonical decodedWire
        have finishExt := equalValue_complete equalRun ext.layout ext.validAssignment
          (by rw [scopeEq]; exact ext.bound (scopeLayout.activation_bound scope))
          candidateBound bounded (Or.inr equality)
        exact ⟨assignment, ext.trans finishExt, candidateBound.mono finishExt.increase, canonical⟩
  termination_by sizeOf expr
  decreasing_by
    all_goals subst expr
    all_goals simp_wf
    all_goals try simp only [Expr.matchValue.sizeOf_spec] at smaller
    all_goals omega

  theorem lowerArgs_complete {program : Program F} (checked : checkDeclarations program.enums = .ok ())
      (tags : program.enums.tagsValid F = true)
      {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
      (typed : CallsTyped program sourceCalls) (callComplete : CallsComplete program.enums sourceCalls calls)
      {function : String} {locals : Locals F} {scope : ScopeId} {args : List (Expr F)}
      {outputs : List (Symbolic F)} {before after : State F}
      (compiled : lowerArgs program function locals scope args before = .ok (outputs, after))
      {rom : WireROM F} {initial : Witness → F}
      (stateLayout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
      (valid : before.Valid rom calls initial) (scopeValid : scope < before.scopes.size)
      (localsBound : LocalsBounded before.roles.size locals)
      (active : (before.activation scope).denote initial = 1) {environment : Environment F}
      (decoded : DecodesEnvironment program.enums (localsEnvironment locals initial) environment)
      {values : List (Value F)}
      (evaluated : ROMEvalArgsWith program.enums (rom.decode program.enums) sourceCalls environment args values) :
      ∃ assignment, Extension rom calls before after initial assignment ∧
        (∀ output ∈ outputs, Bounded after.roles.size output) ∧
        DecodesValues program.enums (outputs.map (WireValue.map (Circuit.ArithExpr.denote assignment))) values := by
    cases args with
    | nil =>
        cases evaluated
        obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [lowerArgs] using compiled)
        exact ⟨initial, .refl stateLayout ((before.valid_iff_reference rom calls initial).mp valid), by simp, .nil⟩
    | cons arg args =>
        cases evaluated with
        | cons headEval tailEval =>
            simp only [lowerArgs] at compiled
            obtain ⟨head, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨a, headExt, headBound, headDecode⟩ := lower_complete checked tags typed callComplete headRun
              stateLayout scopeLayout valid scopeValid localsBound (by simp [TargetBound]) active decoded
              (by simp [TargetDecodes]) headEval
            obtain ⟨headStructure, headScoped⟩ := lower_scoped headRun scopeLayout scopeValid
            obtain ⟨b, tailExt, tailBound, tailDecode⟩ := lowerArgs_complete checked tags typed callComplete tailRun
              headExt.layout headScoped headExt.validAssignment (headStructure.scopeValid scopeValid)
              (localsBound.mono headExt.increase) ((headExt.activation headStructure scopeLayout scopeValid).trans active)
              (headExt.environment localsBound decoded) tailEval
            refine ⟨b, headExt.trans tailExt, ?_, .cons (tailExt.decoded_value headBound headDecode) tailDecode⟩
            intro output member
            rcases List.mem_cons.mp member with rfl | member
            · exact headBound.mono tailExt.increase
            · exact tailBound output member
  termination_by sizeOf args
end

end Aiur.Optimized.Compiler
