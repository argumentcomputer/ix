import Aiur.Circuit.EncodingWitness
import Aiur.Circuit.PatternIrrefutable

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- Correct source calls supply the corresponding canonical circuit premises. -/
def CallsComplete [Field F] [DecidableEq F] (decls : Declarations)
    (sourceCalls : Aiur.CallRelation F) (calls : Circuit.CallRelation F) : Prop :=
  ∀ name values value, sourceCalls name values value → ∀ args result,
    DecodesValues decls args values → result.decode decls = some value → calls name args result

theorem decoded_environment_types [Field F] [DecidableEq F] {decls : Declarations}
    {locals : Locals F} {assignment : Var → F} {environment : Environment F}
    (decoded : DecodesEnvironment decls (localsEnvironment locals assignment) environment) :
    environmentTypes environment = locals.map (fun binding => (binding.1, binding.2.type)) := by
  simpa [localsEnvironment, List.map_map, Function.comp_def] using decoded.types

mutual
  /-- Finite source evaluation supplies canonical witnesses for every active expression. -/
  theorem lowerExpr_complete [Field F] [DecidableEq F]
      {program : Program F} (checked : checkDeclarations program.enums = .ok ())
      (tags : program.enums.tagsValid F = true)
      {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
      (typed : CallsTyped program sourceCalls) (callComplete : CallsComplete program.enums sourceCalls calls)
      {function : String} {locals : Locals F} {enable : ArithExpr F} {expr : Expr F} {output : Symbolic F}
      {before after : BuildState F}
      (compiled : lowerExpr program function locals enable expr before = .ok (output, after))
      {initial : Var → F} (layout : before.WellFormed) (valid : before.Valid rom calls initial)
      (localsBound : LocalsBounded before.nextVar locals) (enableBound : enable.inBounds before.nextVar = true)
      (active : enable.denote initial = 1) {environment : Environment F}
      (decoded : DecodesEnvironment program.enums (localsEnvironment locals initial) environment)
      {value : Value F} (evaluated : ROMEvalExprWith program.enums (rom.decode program.enums) sourceCalls environment expr value) :
      ∃ assignment, Extension rom calls before after initial assignment ∧ Bounded after.nextVar output ∧
        (output.map (ArithExpr.denote assignment)).decode program.enums = some value := by
    cases expr with
    | literal literal =>
        cases evaluated
        obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [lowerExpr] using compiled)
        exact ⟨initial, .refl layout valid, bounded_field.mpr rfl, WireValue.decode_field _ _⟩
    | var name =>
        cases evaluated with
        | var lookup =>
            cases found : locals.find? (·.1 == name) with
            | none => simp [lowerExpr, found] at compiled
            | some binding =>
                rcases binding with ⟨bindingName, result⟩
                have same : bindingName = name := by simpa using List.find?_some found
                subst bindingName
                obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [lowerExpr, found] using compiled)
                obtain ⟨actual, actualFound, valueDecode⟩ := decoded.find name
                  (wire := (name, result.map (ArithExpr.denote initial)))
                  (by simp [localsEnvironment, List.find?_map, Function.comp_def, found])
                have equal := (Prod.mk.inj (Option.some.inj (actualFound.symm.trans lookup))).2
                exact ⟨initial, .refl layout valid, localsBound _ (List.mem_of_find?_eq_some found), equal ▸ valueDecode⟩
    | tuple items =>
        cases evaluated with
        | tuple itemsEval =>
            simp only [lowerExpr] at compiled
            obtain ⟨wires, middle, argsRun, finished⟩ := bind_ok.mp compiled
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨a, ext, bounds, valuesDecode⟩ := lowerArgs_complete checked tags typed callComplete argsRun
              layout valid localsBound enableBound active decoded itemsEval
            exact ⟨a, ext, bounded_tuple.mpr bounds, by
              simpa only [WireValue.map_tuple] using WireValue.decode_tuple checked tags valuesDecode⟩
    | construct name ctor args =>
        cases evaluated with
        | construct argsEval =>
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
                      obtain ⟨typeLayout, middle, layoutRun, rest⟩ := bind_ok.mp rest
                      obtain ⟨expansion, rfl⟩ := getLayout_eq layoutRun
                      split at rest
                      · simp [StateT.bind, bind, Except.bind] at rest
                      · obtain ⟨⟨⟩, middle, unchanged, finished⟩ := bind_ok.mp rest
                        obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
                        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                        obtain ⟨a, ext, valuesBound, argsDecode⟩ := lowerArgs_complete checked tags typed callComplete
                          argsRun layout valid localsBound enableBound active decoded argsEval
                        refine ⟨a, ext, ?_, ?_⟩
                        · unfold Bounded
                          refine Layout.enumWords_all _ _ _ ?_ ?_
                          · rfl
                          · intro polynomial member
                            simp only [List.mem_append] at member
                            rcases member with member | member
                            · obtain ⟨wire, member, leaf⟩ := List.mem_flatMap.mp member
                              exact valuesBound wire member polynomial leaf
                            · have zero : polynomial = .const 0 := List.eq_of_mem_replicate member
                              subst polynomial; rfl
                        · have ctorName : constructor.name = ctor := by
                            simpa using List.findIdx_of_getElem?_eq_some atIndex
                          have constructed := WireValue.decode_construct checked tags found atIndex argsDecode
                            (by simpa [Function.comp_def, WireValue.map] using not_ne_iff.mp types) expansion
                          simpa [ctorName, WireValue.map, List.map_flatMap, List.flatMap_map,
                            List.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using constructed
    | project operand index =>
        cases evaluated with
        | project inputEval projected =>
            simp only [lowerExpr] at compiled
            obtain ⟨input, middle, inputRun, rest⟩ := bind_ok.mp compiled
            rcases input with ⟨type, words⟩
            cases type with
            | field | ptr | enum => simp at rest
            | tuple types =>
                dsimp only at rest
                obtain ⟨wires, last, splitRun, rest⟩ := bind_ok.mp rest
                have unchanged := (splitValues_spec splitRun).1
                subst last
                cases found : wires[index]? with
                | none => simp [found] at rest
                | some result =>
                    obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [found] using rest)
                    obtain ⟨a, ext, bounds, inputDecode⟩ := lowerExpr_complete checked tags typed callComplete inputRun
                      layout valid localsBound enableBound active decoded inputEval
                    obtain ⟨values, rfl, valuesDecode⟩ := splitValues_decode checked splitRun inputDecode
                    obtain ⟨actual, atValue, valueDecode⟩ := valuesDecode.getElem (index := index)
                      (wire := result.map (ArithExpr.denote a)) (by simp [List.getElem?_map, found])
                    have same : actual = value := by simpa [projectValue, atValue, pure, Except.pure] using projected
                    exact ⟨a, ext, splitValues_bounded splitRun bounds result (List.mem_of_getElem? found), same ▸ valueDecode⟩
    | letValue pattern operand body =>
        cases evaluated with
        | letValue inputEval matched bodyEval =>
            simp only [lowerExpr] at compiled
            obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨⟨test, bindings⟩, s₂, patternRun, rest⟩ := bind_ok.mp rest
            obtain ⟨⟨⟩, s₃, guardRun, bodyRun⟩ := bind_ok.mp rest
            obtain ⟨a, e₁, inputBound, inputDecode⟩ := lowerExpr_complete checked tags typed callComplete inputRun
              layout valid localsBound enableBound active decoded inputEval
            obtain ⟨b, e₂, testBound, bindingsBound⟩ := lowerPattern_complete patternRun e₁.layout e₁.valid inputBound
            have chainExt := e₁.trans e₂
            have patternTest := (lowerPattern_sound checked tags patternRun e₂.valid).2.2 _
              (e₂.decoded_value inputBound inputDecode)
            obtain ⟨bindingsDecode, testOne⟩ : DecodesEnvironment program.enums
                (localsEnvironment bindings b) _ ∧ test.denote b = 1 := by
              rcases patternTest with ⟨values, actualMatch, one, formed⟩ | ⟨absent, _⟩
              · have same := Option.some.inj (actualMatch.symm.trans matched)
                exact ⟨same ▸ formed, one⟩
              · rw [matched] at absent; cases absent
            have e₃ := guarded_complete guardRun e₂.layout e₂.valid (chainExt.bound enableBound)
              (by simpa [Scalar.Circuit.ArithExpr.inBounds] using testBound)
              (Or.inr (by change test.denote b - 1 = 0; simp [testOne]))
            obtain ⟨c, e₄, bodyBound, resultDecode⟩ := lowerExpr_complete checked tags typed callComplete bodyRun
              e₃.layout e₃.valid
              (localsBounded_append.mpr ⟨bindingsBound.mono e₃.increase, localsBound.mono (chainExt.trans e₃).increase⟩)
              ((chainExt.trans e₃).bound enableBound) (((chainExt.trans e₃).polynomial enableBound).trans active)
              (by simpa only [localsEnvironment_append] using bindingsDecode.append (chainExt.environment localsBound decoded)) bodyEval
            exact ⟨c, (chainExt.trans e₃).trans e₄, bodyBound, resultDecode⟩
    | store operand =>
        cases evaluated with
        | @store _ _ stored address operandEval cell =>
            simp only [lowerExpr] at compiled
            obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨id, s₂, addressRun, rest⟩ := bind_ok.mp rest
            obtain ⟨⟨⟩, s₃, booleanRun, rest⟩ := bind_ok.mp rest
            obtain ⟨⟨⟩, s₄, validationRun, rest⟩ := bind_ok.mp rest
            obtain ⟨⟨⟩, s₅, cellRun, finished⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨a, e₁, inputBound, inputDecode⟩ := lowerExpr_complete checked tags typed callComplete inputRun
              layout valid localsBound enableBound active decoded operandEval
            obtain ⟨b, e₂, addressBound, addressEq⟩ := fresh_complete addressRun e₁.layout e₁.valid address
            have chainExt := e₁.trans e₂
            have e₃ := boolean_complete booleanRun e₂.layout e₂.valid (chainExt.bound enableBound)
              (Or.inr ((chainExt.polynomial enableBound).trans active))
            have ab : (ArithExpr.var id : ArithExpr F).inBounds s₂.nextVar = true := by
              simpa [Scalar.Circuit.ArithExpr.inBounds] using addressBound
            have throughBoolean := chainExt.trans e₃
            obtain ⟨c, e₄⟩ := validateValue_complete tags validationRun e₃.layout e₃.valid
              (throughBoolean.bound enableBound) (inputBound.mono (e₂.trans e₃).increase)
              (Or.inr ⟨stored, (e₂.trans e₃).decoded_value inputBound inputDecode⟩)
            have throughValidation := throughBoolean.trans e₄
            have addressEqC : c id = address := ((e₃.trans e₄).polynomial ab).trans addressEq
            have inputDecodeC := ((e₂.trans e₃).trans e₄).decoded_value inputBound inputDecode
            have e₅ := requireCell_complete cellRun e₄.layout e₄.valid
              (throughValidation.bound enableBound) ((e₃.trans e₄).bound ab)
              (inputBound.mono ((e₂.trans e₃).trans e₄).increase) (by
                intro _
                obtain ⟨wire, rawCell, storedDecode⟩ := WireROM.mem_decode.mp cell
                have same := WireValue.decode_injective checked inputDecodeC storedDecode
                change (c id, input.map (ArithExpr.denote c)) ∈ rom.entries
                rw [addressEqC, same]
                exact rawCell)
            refine ⟨c, throughValidation.trans e₅, by
              simpa only [bounded_ptr] using ((e₃.trans e₄).trans e₅).bound ab, ?_⟩
            obtain ⟨shape, _, typeLayout, expanded, _⟩ := WireValue.decode_spec inputDecode
            have names := (Declarations.layout_parts expanded).1
            simpa only [WireValue.map_ptr, Scalar.Circuit.ArithExpr.denote, addressEqC, shape, WireValue.map, WireValue.ptr, List.map_cons, List.map_nil] using
              WireValue.decode_ptr names address
    | load operand =>
        cases evaluated with
        | load pointerEval cell sourceType =>
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
                      obtain ⟨a, e₁, inputBound, pointerDecode⟩ := lowerExpr_complete checked tags typed callComplete inputRun
                        layout valid localsBound enableBound active decoded pointerEval
                      have pointerEq := WireValue.ptr_decoded_eq pointerDecode
                      rcases Value.ptr.inj pointerEq with ⟨rfl, addressEq⟩
                      rw [addressEq] at cell
                      obtain ⟨wire, rawCell, valueDecode⟩ := WireROM.mem_decode.mp cell
                      obtain ⟨b, e₂, resultBound, assigned⟩ := freshValue_complete resultRun e₁.layout e₁.valid wire
                        ((WireValue.decode_spec valueDecode).1.symm.trans sourceType) (WireValue.decode_sized checked valueDecode)
                      have resultDecodeB : ((result.map ArithExpr.var).map (ArithExpr.denote b)).decode program.enums = some value := by
                        simp only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote]
                        change (result.map b).decode program.enums = some value
                        rw [assigned]; exact valueDecode
                      have chainExt := e₁.trans e₂
                      have e₃ := boolean_complete booleanRun e₂.layout e₂.valid (chainExt.bound enableBound)
                        (Or.inr ((chainExt.polynomial enableBound).trans active))
                      have throughBoolean := chainExt.trans e₃
                      obtain ⟨c, e₄⟩ := validateValue_complete tags validationRun e₃.layout e₃.valid
                        (throughBoolean.bound enableBound) (resultBound.mono e₃.increase) (Or.inr ⟨value, resultDecodeB⟩)
                      have throughValidation := throughBoolean.trans e₄
                      have ab := inputBound address (by simp)
                      have outputEq : result.map c = wire := ((e₃.trans e₄).variables resultBound).trans assigned
                      have e₅ := requireCell_complete cellRun e₄.layout e₄.valid
                        (throughValidation.bound enableBound) (((e₂.trans e₃).trans e₄).bound ab)
                        (resultBound.mono (e₃.trans e₄).increase) (by
                          intro _
                          simp only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote]
                          change (address.denote c, result.map c) ∈ rom.entries
                          rw [outputEq, ((e₂.trans e₃).trans e₄).polynomial ab]
                          exact rawCell)
                      exact ⟨c, throughValidation.trans e₅, resultBound.mono ((e₃.trans e₄).trans e₅).increase,
                        by simp only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote]; change (result.map c).decode program.enums = some value
                           rw [outputEq]; exact valueDecode⟩
    | hint type key channel =>
        cases evaluated with
        | hint keyEval valueTyped =>
            rename_i constant
            simp only [lowerExpr] at compiled
            obtain ⟨input, s₁, keyRun, rest⟩ := bind_ok.mp compiled
            split at rest
            · simp [StateT.bind, bind, Except.bind] at rest
            · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp rest
              obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
              obtain ⟨result, s₂, freshRun, rest⟩ := bind_ok.mp rest
              obtain ⟨⟨⟩, s₃, validationRun, finished⟩ := bind_ok.mp rest
              obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
              obtain ⟨a, e₁, _, _⟩ := lowerExpr_complete checked tags typed callComplete keyRun
                layout valid localsBound enableBound active decoded keyEval
              have valueTyped : constant.type = type ∧ constant.wellFormed program.enums = true := by
                simpa [Value.WellTyped, Value.hasType] using valueTyped
              obtain ⟨b, e₂, resultBound, resultDecode⟩ := freshValue_decoded_complete checked tags freshRun
                e₁.layout e₁.valid constant.toValue (by simpa using valueTyped.1)
                (by simpa using valueTyped.2)
              have ext := e₁.trans e₂
              have decodedResult : ((result.map ArithExpr.var).map (ArithExpr.denote b)).decode program.enums =
                  some constant.toValue := by simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultDecode
              obtain ⟨c, e₃⟩ := validateValue_complete tags validationRun e₂.layout e₂.valid
                (ext.bound enableBound) resultBound (Or.inr ⟨constant.toValue, decodedResult⟩)
              exact ⟨c, ext.trans e₃, resultBound.mono e₃.increase, e₃.decoded_value resultBound decodedResult⟩
    | neg operand =>
        cases evaluated with
        | neg inputEval operation =>
            simp only [lowerExpr] at compiled
            obtain ⟨input, s₁, inputRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨polynomial, s₂, fieldRun, finished⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := asField_ok fieldRun
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨a, ext, bounded, inputDecode⟩ := lowerExpr_complete checked tags typed callComplete inputRun
              layout valid localsBound enableBound active decoded inputEval
            simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq] at inputDecode
            rw [← inputDecode] at operation
            refine ⟨a, ext, by simpa [Scalar.Circuit.ArithExpr.inBounds] using bounded, ?_⟩
            simpa [evalNeg, Scalar.Circuit.ArithExpr.denote] using operation
    | assertEq message left right =>
        cases evaluated with
        | assertEq leftEval rightEval operation =>
            obtain ⟨_, same, rfl⟩ := evalAssertEq_ok.mp operation
            simp only [lowerExpr] at compiled
            obtain ⟨leftWire, s₁, leftRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨rightWire, s₂, rightRun, rest⟩ := bind_ok.mp rest
            split at rest
            · simp [StateT.bind, bind, Except.bind] at rest
            · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp rest
              obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
              obtain ⟨⟨⟩, last, equated, finished⟩ := bind_ok.mp rest
              obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
              obtain ⟨a, e₁, leftBound, leftDecode⟩ := lowerExpr_complete checked tags typed callComplete leftRun
                layout valid localsBound enableBound active decoded leftEval
              obtain ⟨b, e₂, rightBound, rightDecode⟩ := lowerExpr_complete checked tags typed callComplete rightRun
                e₁.layout e₁.valid (localsBound.mono e₁.increase) (e₁.bound enableBound)
                ((e₁.polynomial enableBound).trans active) (e₁.environment localsBound decoded) rightEval
              have chainExt := e₁.trans e₂
              have leftDecodeB := e₂.decoded_value leftBound leftDecode
              rw [same] at leftDecodeB
              have equal := WireValue.decode_injective checked leftDecodeB rightDecode
              have e₃ := constrainValue_complete equated e₂.layout e₂.valid (chainExt.bound enableBound)
                (leftBound.mono e₂.increase) rightBound (Or.inr equal)
              exact ⟨b, chainExt.trans e₃, bounded_tuple.mpr (by simp), by
                simpa only [WireValue.map_tuple, List.map_nil] using
                  WireValue.decode_tuple checked tags (.nil : DecodesValues program.enums [] [])⟩
    | binary op left right =>
        cases evaluated with
        | binary leftEval rightEval operation =>
            simp only [lowerExpr] at compiled
            obtain ⟨leftWire, s₁, leftRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨leftPoly, s₂, leftField, rest⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := asField_ok leftField
            obtain ⟨rightWire, s₃, rightRun, rest⟩ := bind_ok.mp rest
            obtain ⟨rightPoly, s₄, rightField, rest⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := asField_ok rightField
            obtain ⟨a, e₁, leftBound, leftDecode⟩ := lowerExpr_complete checked tags typed callComplete leftRun
              layout valid localsBound enableBound active decoded leftEval
            obtain ⟨b, e₂, rightBound, rightDecode⟩ := lowerExpr_complete checked tags typed callComplete rightRun
              e₁.layout e₁.valid (localsBound.mono e₁.increase) (e₁.bound enableBound)
              ((e₁.polynomial enableBound).trans active) (e₁.environment localsBound decoded) rightEval
            have chainExt := e₁.trans e₂
            have lb := bounded_field.mp (leftBound.mono e₂.increase)
            have rb := bounded_field.mp rightBound
            have leftDecodeB := e₂.decoded_value leftBound leftDecode
            simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq] at leftDecodeB rightDecode
            rw [← leftDecodeB, ← rightDecode] at operation
            cases op with
            | add | sub | mul =>
                obtain ⟨rfl, rfl⟩ := pure_ok.mp rest
                exact ⟨b, chainExt, by
                  simpa [Scalar.Circuit.ArithExpr.inBounds] using And.intro lb rb,
                  by simpa [evalBinOp, Scalar.Circuit.ArithExpr.denote] using operation⟩
            | div =>
                have nonzero : rightPoly.denote b ≠ 0 := by
                  intro zero
                  simp [evalBinOp, zero] at operation
                have quotient : Value.field (leftPoly.denote b / rightPoly.denote b) = value := by
                  simpa [evalBinOp, nonzero] using operation
                obtain ⟨inverse, s₅, freshRun, rest⟩ := bind_ok.mp rest
                obtain ⟨⟨⟩, s₆, inverseRun, finished⟩ := bind_ok.mp rest
                obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
                obtain ⟨c, e₃, invBound, invEq⟩ := fresh_complete freshRun e₂.layout e₂.valid (rightPoly.denote b)⁻¹
                have ib : (ArithExpr.var inverse : ArithExpr F).inBounds s₅.nextVar = true := by
                  simpa [Scalar.Circuit.ArithExpr.inBounds] using invBound
                have e₄ := guarded_complete inverseRun e₃.layout e₃.valid ((chainExt.trans e₃).bound enableBound)
                  (by simpa [Scalar.Circuit.ArithExpr.inBounds] using And.intro (e₃.bound rb) ib)
                  (Or.inr (by
                    change rightPoly.denote c * c inverse - 1 = 0
                    rw [e₃.polynomial rb, invEq]
                    simp [nonzero]))
                refine ⟨c, (chainExt.trans e₃).trans e₄, ?_, ?_⟩
                · simpa [Scalar.Circuit.ArithExpr.inBounds] using And.intro ((e₃.trans e₄).bound lb) (e₄.bound ib)
                · simp only [WireValue.map_field, WireValue.decode_field, Option.some.injEq]
                  change Value.field (leftPoly.denote c * c inverse) = value
                  rw [e₃.polynomial lb, invEq, ← div_eq_mul_inv]
                  exact quotient
    | call name args =>
        cases evaluated with
        | call argsEval calleeEval =>
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
                  obtain ⟨a, e₁, argsBound, argsDecode⟩ := lowerArgs_complete checked tags typed callComplete argsRun
                    layout valid localsBound enableBound active decoded argsEval
                  have resultType := typed _ _ _ calleeEval callee found
                  obtain ⟨b, e₂, resultBound, resultDecode⟩ := freshValue_decoded_complete checked tags resultRun
                    e₁.layout e₁.valid value resultType.1 resultType.2
                  have resultDecodeB : ((result.map ArithExpr.var).map (ArithExpr.denote b)).decode program.enums = some value := by
                    simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultDecode
                  have chainExt := e₁.trans e₂
                  have e₃ := boolean_complete booleanRun e₂.layout e₂.valid (chainExt.bound enableBound)
                    (Or.inr ((chainExt.polynomial enableBound).trans active))
                  have throughBoolean := chainExt.trans e₃
                  obtain ⟨c, e₄⟩ := validateValues_complete tags argsValidation e₃.layout e₃.valid
                    (throughBoolean.bound enableBound) (fun w h => (argsBound w h).mono (e₂.trans e₃).increase)
                    (Or.inr (fun wire member => ((e₂.trans e₃).decoded_values argsBound argsDecode).each
                      (wire.map (ArithExpr.denote b)) (List.mem_map.mpr ⟨wire, member, rfl⟩)))
                  have throughArgs := throughBoolean.trans e₄
                  obtain ⟨d, e₅⟩ := validateValue_complete tags resultValidation e₄.layout e₄.valid
                    (throughArgs.bound enableBound) (resultBound.mono (e₃.trans e₄).increase)
                    (Or.inr ⟨value, (e₃.trans e₄).decoded_value resultBound resultDecodeB⟩)
                  have throughResult := throughArgs.trans e₅
                  have resultDecodeD := ((e₃.trans e₄).trans e₅).decoded_value resultBound resultDecodeB
                  have e₆ := send_complete e₅.layout e₅.valid ⟨name, arguments, result, enable⟩
                    (send_bounded (fun w h => (argsBound w h).mono (((e₂.trans e₃).trans e₄).trans e₅).increase)
                      (resultBound.mono ((e₃.trans e₄).trans e₅).increase) (throughResult.bound enableBound)) (by
                        intro _
                        exact callComplete name _ value calleeEval _ _
                          ((((e₂.trans e₃).trans e₄).trans e₅).decoded_values argsBound argsDecode)
                          (by simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultDecodeD))
                  exact ⟨d, throughResult.trans e₆, resultBound.mono (((e₃.trans e₄).trans e₅).trans e₆).increase,
                    resultDecodeD⟩
    | matchValue scrutinee arms =>
        have allEval := evaluated
        cases evaluated with
        | matchValue inputEval selected branchEval =>
            simp only [lowerExpr] at compiled
            obtain ⟨⟨⟩, s₁, checkRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨_, rfl⟩ := lift_eq_ok checkRun
            obtain ⟨type, s₂, typeRun, rest⟩ := bind_ok.mp rest
            obtain ⟨inferred, rfl⟩ := lift_eq_ok typeRun
            have typeChecked : inferType program function (environmentTypes environment)
                (.matchValue scrutinee arms) = .ok type := by
              rw [decoded_environment_types decoded]
              cases h : inferType program function (locals.map fun (name, value) => (name, value.type))
                (.matchValue scrutinee arms) <;> simp_all [Except.mapError]
            have resultType := allEval.wellTyped typed (WireROM.decode_wellFormed program.enums rom)
              decoded.wellFormed function type typeChecked
            obtain ⟨input, s₃, inputRun, rest⟩ := bind_ok.mp rest
            obtain ⟨result, s₄, resultRun, rest⟩ := bind_ok.mp rest
            obtain ⟨⟨⟩, s₅, validationRun, rest⟩ := bind_ok.mp rest
            obtain ⟨selectors, s₆, armsRun, rest⟩ := bind_ok.mp rest
            obtain ⟨⟨⟩, s₇, exclusionRun, rest⟩ := bind_ok.mp rest
            obtain ⟨⟨⟩, s₈, sumRun, finished⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨a, e₁, inputBound, inputDecode⟩ := lowerExpr_complete checked tags typed callComplete inputRun
              layout valid localsBound enableBound active decoded inputEval
            obtain ⟨b, e₂, resultBound, resultDecode⟩ := freshValue_decoded_complete checked tags resultRun
              e₁.layout e₁.valid value resultType.1 resultType.2
            have resultDecodeB : ((result.map ArithExpr.var).map (ArithExpr.denote b)).decode program.enums = some value := by
              simpa only [WireValue.map_map, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using resultDecode
            have initialExt := e₁.trans e₂
            obtain ⟨v, validationExt⟩ := validateValue_complete tags validationRun e₂.layout e₂.valid
              (initialExt.bound enableBound) resultBound (Or.inr ⟨value, resultDecodeB⟩)
            have chainExt := initialExt.trans validationExt
            obtain ⟨c, e₃, selectorsBound, selection⟩ := lowerArms_complete checked tags typed callComplete armsRun
              validationExt.layout validationExt.valid (localsBound.mono chainExt.increase)
              (inputBound.mono (e₂.trans validationExt).increase) (resultBound.mono validationExt.increase)
              (chainExt.bound enableBound) ((chainExt.polynomial enableBound).trans active)
              (chainExt.environment localsBound decoded) ((e₂.trans validationExt).decoded_value inputBound inputDecode)
              (validationExt.decoded_value resultBound resultDecodeB) selected branchEval
            have e₄ := excludePairs_complete exclusionRun e₃.layout e₃.valid selectorsBound selection.exclusive
            have e₅ := sum_complete sumRun e₄.layout e₄.valid
              (fun p h => e₄.bound (selectorsBound p h)) (((chainExt.trans e₃).trans e₄).bound enableBound)
              (by rw [((chainExt.trans e₃).trans e₄).polynomial enableBound, active]; exact selection.sum)
            exact ⟨c, ((chainExt.trans e₃).trans e₄).trans e₅,
              resultBound.mono (((validationExt.trans e₃).trans e₄).trans e₅).increase,
              (validationExt.trans e₃).decoded_value resultBound resultDecodeB⟩
  termination_by sizeOf expr

  theorem lowerArgs_complete [Field F] [DecidableEq F]
      {program : Program F} (checked : checkDeclarations program.enums = .ok ())
      (tags : program.enums.tagsValid F = true)
      {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
      (typed : CallsTyped program sourceCalls) (callComplete : CallsComplete program.enums sourceCalls calls)
      {function : String} {locals : Locals F} {enable : ArithExpr F}
      {args : List (Expr F)} {outputs : List (Symbolic F)} {before after : BuildState F}
      (compiled : lowerArgs program function locals enable args before = .ok (outputs, after))
      {initial : Var → F} (layout : before.WellFormed) (valid : before.Valid rom calls initial)
      (localsBound : LocalsBounded before.nextVar locals) (enableBound : enable.inBounds before.nextVar = true)
      (active : enable.denote initial = 1) {environment : Environment F}
      (decoded : DecodesEnvironment program.enums (localsEnvironment locals initial) environment)
      {values : List (Value F)} (evaluated : ROMEvalArgsWith program.enums (rom.decode program.enums) sourceCalls environment args values) :
      ∃ assignment, Extension rom calls before after initial assignment ∧
        (∀ wire ∈ outputs, Bounded after.nextVar wire) ∧
        DecodesValues program.enums (outputs.map (WireValue.map (ArithExpr.denote assignment))) values := by
    cases args with
    | nil =>
        cases evaluated
        obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [lowerArgs] using compiled)
        exact ⟨initial, .refl layout valid, by simp, .nil⟩
    | cons arg args =>
        cases evaluated with
        | cons headEval tailEval =>
            simp only [lowerArgs] at compiled
            obtain ⟨head, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨a, e₁, headBound, headDecode⟩ := lowerExpr_complete checked tags typed callComplete headRun
              layout valid localsBound enableBound active decoded headEval
            obtain ⟨b, e₂, tailBound, tailDecode⟩ := lowerArgs_complete checked tags typed callComplete tailRun
              e₁.layout e₁.valid (localsBound.mono e₁.increase) (e₁.bound enableBound)
              ((e₁.polynomial enableBound).trans active) (e₁.environment localsBound decoded) tailEval
            refine ⟨b, e₁.trans e₂, ?_, .cons (e₂.decoded_value headBound headDecode) tailDecode⟩
            intro wire member
            rcases List.mem_cons.mp member with rfl | member
            · exact headBound.mono e₂.increase
            · exact tailBound wire member
  termination_by sizeOf args

  theorem lowerArms_complete [Field F] [DecidableEq F]
      {program : Program F} (checked : checkDeclarations program.enums = .ok ())
      (tags : program.enums.tagsValid F = true)
      {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F}
      (typed : CallsTyped program sourceCalls) (callComplete : CallsComplete program.enums sourceCalls calls)
      {function : String} {locals : Locals F} {scrutinee result : Symbolic F} {remaining : ArithExpr F}
      {arms : List (Pattern F × Expr F)} {selectors : List (ArithExpr F)} {before after : BuildState F}
      (compiled : lowerArms program function locals scrutinee result remaining arms before = .ok (selectors, after))
      {initial : Var → F} (layout : before.WellFormed) (valid : before.Valid rom calls initial)
      (localsBound : LocalsBounded before.nextVar locals)
      (inputBound : Bounded before.nextVar scrutinee) (resultBound : Bounded before.nextVar result)
      (remainingBound : remaining.inBounds before.nextVar = true) (active : remaining.denote initial = 1)
      {environment : Environment F}
      (decoded : DecodesEnvironment program.enums (localsEnvironment locals initial) environment)
      {input value : Value F}
      (inputDecode : (scrutinee.map (ArithExpr.denote initial)).decode program.enums = some input)
      (resultDecode : (result.map (ArithExpr.denote initial)).decode program.enums = some value)
      {matched : Environment F} {body : Expr F} (selected : selectArm input arms = some (matched, body))
      (evaluated : ROMEvalExprWith program.enums (rom.decode program.enums) sourceCalls (matched ++ environment) body value) :
      ∃ assignment, Extension rom calls before after initial assignment ∧
        (∀ selector ∈ selectors, selector.inBounds after.nextVar = true) ∧
        Scalar.Circuit.SelectorsValid (1 : F) (selectors.map (ArithExpr.denote assignment)) := by
    cases arms with
    | nil => simp [selectArm] at selected
    | cons arm arms =>
        rcases hArm : arm with ⟨pattern, branch⟩
        simp only [hArm, lowerArms] at compiled
        obtain ⟨⟨test, bindings⟩, s₁, patternRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨selector, s₂, freshRun, rest⟩ := bind_ok.mp rest
        obtain ⟨finished, s₃, booleanRun, rest⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨finished, s₄, equationRun, rest⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨bodyValue, s₅, bodyRun, rest⟩ := bind_ok.mp rest
        obtain ⟨finished, s₆, valueRun, armsRest⟩ := bind_ok.mp rest
        cases finished
        obtain ⟨a, e₁, testBound, bindingsBound⟩ := lowerPattern_complete patternRun layout valid inputBound
        have patternSound := lowerPattern_sound checked tags patternRun e₁.valid
        have patternTest := patternSound.2.2 input (e₁.decoded_value inputBound inputDecode)
        have testBool := patternSound.2.1
        obtain ⟨b, e₂, idBound, selEq⟩ := fresh_complete freshRun e₁.layout e₁.valid (test.denote a)
        have selectorBound : (ArithExpr.var selector : ArithExpr F).inBounds s₂.nextVar = true := by
          simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using idBound
        have e₃ := boolean_complete booleanRun e₂.layout e₂.valid selectorBound (by
          change b selector = 0 ∨ b selector = 1; rw [selEq]; exact testBool)
        have chainExt := (e₁.trans e₂).trans e₃
        have e₄ := constrain_complete equationRun e₃.layout e₃.valid
          (by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
            And.intro (e₃.bound selectorBound) (And.intro (chainExt.bound remainingBound) ((e₂.trans e₃).bound testBound)))
          (by change b selector - remaining.denote b * test.denote b = 0
              rw [selEq, chainExt.polynomial remainingBound, active, e₂.polynomial testBound]; simp)
        have localsBound' : LocalsBounded s₄.nextVar (bindings ++ locals) :=
          localsBounded_append.mpr ⟨bindingsBound.mono ((e₂.trans e₃).trans e₄).increase,
            localsBound.mono (chainExt.trans e₄).increase⟩
        rcases patternTest with ⟨headValues, matchedHead, testOne, bindingsDecode⟩ | ⟨unmatchedHead, testZero⟩
        · have selectedHead : matched = headValues ∧ body = branch := by
            simpa only [hArm, selectArm, matchedHead, Option.some.injEq, Prod.mk.injEq] using selected.symm
          obtain ⟨rfl, rfl⟩ := selectedHead
          have selOne : (ArithExpr.var selector : ArithExpr F).denote b = 1 := selEq.trans testOne
          obtain ⟨c, e₅, bodyBound, bodyDecode⟩ := lowerExpr_complete checked tags typed callComplete bodyRun
            e₄.layout e₄.valid localsBound' ((e₃.trans e₄).bound selectorBound) selOne
            (by simpa only [localsEnvironment_append] using
              (DecodesEnvironment.append (((e₂.trans e₃).trans e₄).environment bindingsBound bindingsDecode)
                ((chainExt.trans e₄).environment localsBound decoded))) evaluated
          have headExt := (chainExt.trans e₄).trans e₅
          have selOneC := (((e₃.trans e₄).trans e₅).polynomial selectorBound).trans selOne
          have e₆ := constrainValue_decoded_complete checked valueRun e₅.layout e₅.valid
            (((e₃.trans e₄).trans e₅).bound selectorBound) (resultBound.mono headExt.increase) bodyBound
            (headExt.decoded_value resultBound resultDecode) bodyDecode
          have total := headExt.trans e₆
          have finalBound := (((e₃.trans e₄).trans e₅).trans e₆).bound selectorBound
          split at armsRest
          · obtain ⟨rfl, rfl⟩ := pure_ok.mp armsRest
            refine ⟨c, total, by simpa using finalBound, ?_⟩
            simpa only [List.map_cons, List.map_nil, selOneC, List.nil_append] using
              (Scalar.Circuit.SelectorsValid.single (before := []) (after := []) (by simp) (by simp) :
                Scalar.Circuit.SelectorsValid (1 : F) [1])
          · simp only [pure_bind] at armsRest
            obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp armsRest
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            have testFinal := ((((e₂.trans e₃).trans e₄).trans e₅).trans e₆).bound testBound
            have nextBound : (ArithExpr.mul remaining (.sub (.const 1) test)).inBounds s₆.nextVar = true := by
              simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
                And.intro (total.bound remainingBound) testFinal
            have nextZero : (ArithExpr.mul remaining (.sub (.const 1) test)).denote c = 0 := by
              change remaining.denote c * (1 - test.denote c) = 0
              rw [((((e₂.trans e₃).trans e₄).trans e₅).trans e₆).polynomial testBound, testOne]
              simp
            obtain ⟨d, tailExt, tailBound, tailZero⟩ := lowerArms_inactive tailRun total.layout total.valid
              (localsBound.mono total.increase) (inputBound.mono total.increase) (resultBound.mono total.increase)
              nextBound nextZero
            refine ⟨d, total.trans tailExt, ?_, ?_⟩
            · intro p member
              rcases List.mem_cons.mp member with rfl | member
              · exact tailExt.bound finalBound
              · exact tailBound p member
            · have one := (tailExt.polynomial finalBound).trans selOneC
              simp only [List.map_cons, one]
              exact Scalar.Circuit.SelectorsValid.single (before := []) (by simp)
                (by simpa only [List.forall_mem_map] using tailZero)
        · have selectedTail : selectArm input arms = some (matched, body) := by
            simpa only [hArm, selectArm, unmatchedHead] using selected
          have selZero : (ArithExpr.var selector : ArithExpr F).denote b = 0 := selEq.trans testZero
          obtain ⟨c, e₅, bodyBound⟩ := lowerExpr_inactive bodyRun e₄.layout e₄.valid localsBound'
            ((e₃.trans e₄).bound selectorBound) selZero
          have headExt := (chainExt.trans e₄).trans e₅
          have selZeroC := (((e₃.trans e₄).trans e₅).polynomial selectorBound).trans selZero
          have e₆ := constrainValue_complete valueRun e₅.layout e₅.valid
            (((e₃.trans e₄).trans e₅).bound selectorBound) (resultBound.mono headExt.increase) bodyBound (Or.inl selZeroC)
          have total := headExt.trans e₆
          have finalBound := (((e₃.trans e₄).trans e₅).trans e₆).bound selectorBound
          split at armsRest
          · rename_i irrefutable
            have one := lowerPattern_irrefutable checked tags patternRun irrefutable e₁.valid
              (e₁.decoded_value inputBound inputDecode)
            exact (zero_ne_one (testZero.symm.trans one)).elim
          · simp only [pure_bind] at armsRest
            obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp armsRest
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            have testFinal := ((((e₂.trans e₃).trans e₄).trans e₅).trans e₆).bound testBound
            have nextBound : (ArithExpr.mul remaining (.sub (.const 1) test)).inBounds s₆.nextVar = true := by
              simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
                And.intro (total.bound remainingBound) testFinal
            have nextOne : (ArithExpr.mul remaining (.sub (.const 1) test)).denote c = 1 := by
              change remaining.denote c * (1 - test.denote c) = 1
              rw [total.polynomial remainingBound, active,
                ((((e₂.trans e₃).trans e₄).trans e₅).trans e₆).polynomial testBound, testZero]
              simp
            obtain ⟨d, tailExt, tailBound, selection⟩ := lowerArms_complete checked tags typed callComplete tailRun
              total.layout total.valid (localsBound.mono total.increase)
              (inputBound.mono total.increase) (resultBound.mono total.increase) nextBound nextOne
              (total.environment localsBound decoded) (total.decoded_value inputBound inputDecode)
              (total.decoded_value resultBound resultDecode) selectedTail evaluated
            refine ⟨d, total.trans tailExt, ?_, ?_⟩
            · intro p member
              rcases List.mem_cons.mp member with rfl | member
              · exact tailExt.bound finalBound
              · exact tailBound p member
            · have zero := (tailExt.polynomial finalBound).trans selZeroC
              simpa only [List.map_cons, zero] using selection.zero_cons
  termination_by sizeOf arms
  decreasing_by
    all_goals simp only [*, Prod.mk.sizeOf_spec, List.cons.sizeOf_spec]
    all_goals omega
end

end Aiur.Circuit.Compiler
