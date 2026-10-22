import Aiur.Optimized.InactiveBasics

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

mutual
  /-- Every disabled expression admits all fresh witnesses, including the
unconditional Boolean/coverage equations introduced by nested choices. -/
  theorem lower_inactive {program : Program F} {function : String} {locals : Locals F}
      {scope : ScopeId} {expr : Expr F} {target : Option (WireValue Witness)} {output : Symbolic F}
      {before after : State F}
      (compiled : lower program function locals scope expr target before = .ok (output, after))
      {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
      (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
      (valid : before.Valid rom calls initial) (scopeValid : scope < before.scopes.size)
      (localsBound : Circuit.Compiler.LocalsBounded before.roles.size locals)
      (targetBound : ∀ candidate, target = some candidate →
        Circuit.Compiler.Bounded (F := F) before.roles.size (candidate.map Polynomial.var))
      (inactive : (before.activation scope).denote initial = 0) :
      ∃ assignment, Extension rom calls before after initial assignment ∧
        Circuit.Compiler.Bounded after.roles.size output := by
    let start : InactiveContext rom calls scope before initial := ⟨layout, scopeLayout, valid, scopeValid, inactive⟩
    rw [lower.eq_def] at compiled
    obtain ⟨value, middle, stepRun, finished⟩ := bind_ok.mp compiled
    have step : ∃ assignment, Extension rom calls before middle initial assignment ∧
        InactiveContext rom calls scope middle assignment ∧ Circuit.Compiler.Bounded middle.roles.size value := by
      cases expr with
      | literal literal =>
          obtain ⟨rfl, stateEq⟩ := pure_ok.mp stepRun
          subst middle
          exact ⟨initial, start.refl, start, Circuit.Compiler.bounded_field.mpr rfl⟩
      | var name =>
          cases found : locals.find? (·.1 == name) with
          | none => simp [found] at stepRun
          | some binding =>
              rcases binding with ⟨key, wire⟩
              simp only [found] at stepRun
              obtain ⟨rfl, stateEq⟩ := pure_ok.mp stepRun
              subst middle
              exact ⟨initial, start.refl, start, localsBound _ (List.mem_of_find?_eq_some found)⟩
      | tuple items =>
          obtain ⟨values, s₁, argsRun, pureRun⟩ := bind_ok.mp stepRun
          obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
          subst middle
          obtain ⟨a, extension, bounded⟩ := lowerArgs_inactive argsRun layout scopeLayout valid scopeValid localsBound inactive
          exact ⟨a, extension, start.afterArgs argsRun extension, Circuit.Compiler.bounded_tuple.mpr bounded⟩
      | construct name ctor args =>
          cases found : program.enums.findEnum? name with
          | none => simp [found] at stepRun
          | some definition =>
              simp only [found] at stepRun
              cases atIndex : definition.constructors[definition.constructors.findIdx (·.name == ctor)]? with
              | none => simp [atIndex] at stepRun
              | some constructor =>
                  simp only [atIndex] at stepRun
                  obtain ⟨values, s₁, argsRun, checkBind⟩ := bind_ok.mp stepRun
                  split at checkBind
                  · simp [StateT.bind, bind, Except.bind] at checkBind
                  · obtain ⟨⟨⟩, s₂, unchanged, layoutBind⟩ := bind_ok.mp checkBind
                    obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                    subst s₂
                    obtain ⟨typeLayout, s₃, layoutRun, widthBind⟩ := bind_ok.mp layoutBind
                    obtain ⟨_, stateEq⟩ := getLayout_eq layoutRun
                    subst s₃
                    split at widthBind
                    · simp [StateT.bind, bind, Except.bind] at widthBind
                    · obtain ⟨⟨⟩, s₄, unchanged, pureRun⟩ := bind_ok.mp widthBind
                      obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                      subst s₄
                      obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
                      subst middle
                      obtain ⟨a, extension, bounded⟩ := lowerArgs_inactive argsRun layout scopeLayout valid scopeValid localsBound inactive
                      refine ⟨a, extension, start.afterArgs argsRun extension, ?_⟩
                      unfold Circuit.Compiler.Bounded
                      refine Layout.enumWords_all _ _ _ ?_ ?_
                      · rfl
                      · intro polynomial member
                        simp only [List.mem_append] at member
                        rcases member with member | member
                        · obtain ⟨wire, member, leaf⟩ := List.mem_flatMap.mp member
                          exact bounded wire member polynomial leaf
                        · have same : polynomial = .const 0 := List.eq_of_mem_replicate member
                          subst polynomial
                          rfl
      | project operand index =>
          obtain ⟨wire, s₁, operandRun, projectBind⟩ := bind_ok.mp stepRun
          cases typeEq : wire.type with
          | field | ptr | enum => simp [typeEq] at projectBind
          | tuple types =>
              simp only [typeEq] at projectBind
              obtain ⟨items, s₂, splitRun, resultRun⟩ := bind_ok.mp projectBind
              obtain ⟨stateEq, _⟩ := splitValues_reference splitRun
              subst s₂
              cases found : items[index]? with
              | none => simp [found] at resultRun
              | some result =>
                  simp only [found] at resultRun
                  obtain ⟨rfl, stateEq⟩ := pure_ok.mp resultRun
                  subst middle
                  obtain ⟨a, extension, bounded⟩ := lower_inactive operandRun layout scopeLayout valid scopeValid localsBound
                    (by simp) inactive
                  exact ⟨a, extension, start.afterLower operandRun extension,
                    splitValues_bounded splitRun bounded result (List.mem_of_getElem? found)⟩
      | letValue pat operand body =>
          obtain ⟨wire, s₁, operandRun, patternBind⟩ := bind_ok.mp stepRun
          obtain ⟨⟨conditions, bindings⟩, s₂, patternRun, equationsBind⟩ := bind_ok.mp patternBind
          obtain ⟨⟨⟩, s₃, equationRun, bodyRun⟩ := bind_ok.mp equationsBind
          have stateEq := pattern_unchanged patternRun
          subst s₂
          have equationRun' : (do for condition in conditions do equation scope condition : Build F Unit)
              s₁ = .ok ((), s₃) := bind_ok.mpr ⟨PUnit.unit, s₃, equationRun, rfl⟩
          obtain ⟨a, e₁, wireBound⟩ := lower_inactive operandRun layout scopeLayout valid scopeValid localsBound (by simp) inactive
          have c₁ := start.afterLower operandRun e₁
          obtain ⟨_, conditionsBound, bindingsBound⟩ := pattern_bounded patternRun wireBound
          obtain ⟨e₂, c₂⟩ := c₁.equations equationRun' conditionsBound
          have chain := e₁.trans e₂
          obtain ⟨b, e₃, bodyBound⟩ := lower_inactive bodyRun c₂.layout c₂.scopeLayout c₂.valid c₂.scopeValid
            (Circuit.Compiler.localsBounded_append.mpr ⟨bindingsBound.mono e₂.increase, localsBound.mono chain.increase⟩)
            (fun candidate equal => (targetBound candidate equal).mono chain.increase) c₂.inactive
          exact ⟨b, chain.trans e₃, c₂.afterLower bodyRun e₃, bodyBound⟩
      | store operand =>
          obtain ⟨wire, s₁, operandRun, destinationBind⟩ := bind_ok.mp stepRun
          obtain ⟨result, s₂, destinationRun, pointerBind⟩ := bind_ok.mp destinationBind
          cases wordsEq : result.words with
          | nil => simp [wordsEq] at pointerBind
          | cons address rest =>
              cases rest with
              | cons => simp [wordsEq] at pointerBind
              | nil =>
                  simp only [wordsEq] at pointerBind
                  obtain ⟨⟨⟩, s₃, storeRun, pureRun⟩ := bind_ok.mp pointerBind
                  obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
                  subst middle
                  obtain ⟨a, e₁, wireBound⟩ := lower_inactive operandRun layout scopeLayout valid scopeValid localsBound (by simp) inactive
                  have c₁ := start.afterLower operandRun e₁
                  obtain ⟨b, e₂, c₂, resultBound⟩ := c₁.destination destinationRun
                    (fun candidate equal => (targetBound candidate equal).mono e₁.increase)
                  have addressBound := resultBound (.var address) (by simp [WireValue.words_map, wordsEq])
                  obtain ⟨e₃, c₃⟩ := c₂.cell storeRun addressBound (wireBound.mono e₂.increase)
                  exact ⟨b, (e₁.trans e₂).trans e₃, c₃, resultBound.mono e₃.increase⟩
      | load operand =>
          obtain ⟨pointer, s₁, operandRun, pointerBind⟩ := bind_ok.mp stepRun
          rcases pointer with ⟨type, words⟩
          cases type with
          | field | tuple | enum => simp at pointerBind
          | ptr type =>
              cases words with
              | nil => simp at pointerBind
              | cons address rest =>
                  cases rest with
                  | cons => simp at pointerBind
                  | nil =>
                      dsimp only at pointerBind
                      obtain ⟨result, s₂, destinationRun, loadBind⟩ := bind_ok.mp pointerBind
                      obtain ⟨⟨⟩, s₃, loadRun, pureRun⟩ := bind_ok.mp loadBind
                      obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
                      subst middle
                      obtain ⟨a, e₁, pointerBound⟩ := lower_inactive operandRun layout scopeLayout valid scopeValid localsBound (by simp) inactive
                      have c₁ := start.afterLower operandRun e₁
                      obtain ⟨b, e₂, c₂, resultBound⟩ := c₁.destination destinationRun
                        (fun candidate equal => (targetBound candidate equal).mono e₁.increase)
                      have addressBound := pointerBound address (by simp)
                      obtain ⟨e₃, c₃⟩ := c₂.cell loadRun (e₂.bound addressBound) resultBound
                      exact ⟨b, (e₁.trans e₂).trans e₃, c₃, resultBound.mono e₃.increase⟩
      | neg operand =>
          obtain ⟨wire, s₁, operandRun, fieldBind⟩ := bind_ok.mp stepRun
          obtain ⟨polynomial, s₂, fieldRun, pureRun⟩ := bind_ok.mp fieldBind
          obtain ⟨shape, stateEq⟩ := asField_eq fieldRun
          subst s₂
          obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
          subst middle
          obtain ⟨a, extension, bounded⟩ := lower_inactive operandRun layout scopeLayout valid scopeValid localsBound (by simp) inactive
          have scalarBound : polynomial.inBounds s₁.roles.size = true := by
            simpa only [shape, Circuit.Compiler.bounded_field] using bounded
          exact ⟨a, extension, start.afterLower operandRun extension,
            Circuit.Compiler.bounded_field.mpr (by simp [Scalar.Circuit.ArithExpr.inBounds, scalarBound])⟩
      | hint type key channel =>
          obtain ⟨keyWire, s₁, keyRun, pointerCheck⟩ := bind_ok.mp stepRun
          split at pointerCheck
          · simp [StateT.bind, bind, Except.bind] at pointerCheck
          · obtain ⟨⟨⟩, s₂, unchanged, destinationBind⟩ := bind_ok.mp pointerCheck
            obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
            subst s₂
            obtain ⟨result, s₃, destinationRun, validationBind⟩ := bind_ok.mp destinationBind
            obtain ⟨⟨⟩, s₄, validationRun, pureRun⟩ := bind_ok.mp validationBind
            obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
            subst middle
            obtain ⟨a, e₁, _⟩ := lower_inactive keyRun layout scopeLayout valid scopeValid localsBound (by simp) inactive
            have c₁ := start.afterLower keyRun e₁
            obtain ⟨b, e₂, c₂, resultBound⟩ := c₁.destination destinationRun
              (fun candidate equal => (targetBound candidate equal).mono e₁.increase)
            obtain ⟨c, e₃, c₃⟩ := c₂.validate validationRun resultBound
            exact ⟨c, (e₁.trans e₂).trans e₃, c₃, resultBound.mono e₃.increase⟩
      | assertEq message left right =>
          obtain ⟨leftWire, s₁, leftRun, rightBind⟩ := bind_ok.mp stepRun
          obtain ⟨rightWire, s₂, rightRun, pointerCheck⟩ := bind_ok.mp rightBind
          split at pointerCheck
          · simp [StateT.bind, bind, Except.bind] at pointerCheck
          · obtain ⟨⟨⟩, s₃, unchanged, equalityBind⟩ := bind_ok.mp pointerCheck
            obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
            subst s₃
            obtain ⟨⟨⟩, s₄, equalityRun, pureRun⟩ := bind_ok.mp equalityBind
            obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
            subst middle
            obtain ⟨a, e₁, leftBound⟩ := lower_inactive leftRun layout scopeLayout valid scopeValid localsBound (by simp) inactive
            have c₁ := start.afterLower leftRun e₁
            obtain ⟨b, e₂, rightBound⟩ := lower_inactive rightRun c₁.layout c₁.scopeLayout c₁.valid c₁.scopeValid
              (localsBound.mono e₁.increase) (by simp) c₁.inactive
            have c₂ := c₁.afterLower rightRun e₂
            obtain ⟨e₃, c₃⟩ := c₂.equal equalityRun (leftBound.mono e₂.increase) rightBound
            exact ⟨b, (e₁.trans e₂).trans e₃, c₃, Circuit.Compiler.bounded_tuple.mpr (by simp)⟩
      | binary op left right =>
          obtain ⟨leftWire, s₁, leftRun, leftFieldBind⟩ := bind_ok.mp stepRun
          obtain ⟨leftWord, s₂, leftFieldRun, rightBind⟩ := bind_ok.mp leftFieldBind
          obtain ⟨leftShape, stateEq⟩ := asField_eq leftFieldRun
          subst s₂
          obtain ⟨rightWire, s₃, rightRun, rightFieldBind⟩ := bind_ok.mp rightBind
          obtain ⟨rightWord, s₄, rightFieldRun, operatorRun⟩ := bind_ok.mp rightFieldBind
          obtain ⟨rightShape, stateEq⟩ := asField_eq rightFieldRun
          subst s₄
          obtain ⟨a, e₁, leftBound⟩ := lower_inactive leftRun layout scopeLayout valid scopeValid localsBound (by simp) inactive
          have c₁ := start.afterLower leftRun e₁
          obtain ⟨b, e₂, rightBound⟩ := lower_inactive rightRun c₁.layout c₁.scopeLayout c₁.valid c₁.scopeValid
            (localsBound.mono e₁.increase) (by simp) c₁.inactive
          have c₂ := c₁.afterLower rightRun e₂
          have leftWordBound : leftWord.inBounds s₃.roles.size = true := by
            simpa only [leftShape, Circuit.Compiler.bounded_field, State.toReference] using leftBound.mono e₂.increase
          have rightWordBound : rightWord.inBounds s₃.roles.size = true := by
            simpa only [rightShape, Circuit.Compiler.bounded_field] using rightBound
          cases op with
          | add | sub | mul =>
              obtain ⟨rfl, stateEq⟩ := pure_ok.mp operatorRun
              subst middle
              refine ⟨b, e₁.trans e₂, c₂, Circuit.Compiler.bounded_field.mpr ?_⟩
              simp [Scalar.Circuit.ArithExpr.inBounds, leftWordBound, rightWordBound]
          | div =>
              cases folded : rightWord.constantInverse? with
              | some inverse =>
                  simp only [folded] at operatorRun
                  obtain ⟨rfl, stateEq⟩ := pure_ok.mp operatorRun
                  subst middle
                  refine ⟨b, e₁.trans e₂, c₂, Circuit.Compiler.bounded_field.mpr ?_⟩
                  simpa [Scalar.Circuit.ArithExpr.inBounds] using leftWordBound
              | none =>
                  simp only [folded] at operatorRun
                  obtain ⟨inverse, s₅, inverseRun, equationBind⟩ := bind_ok.mp operatorRun
                  obtain ⟨⟨⟩, s₆, equationRun, pureRun⟩ := bind_ok.mp equationBind
                  obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
                  subst middle
                  obtain ⟨c, e₃, c₃, inverseBound⟩ := c₂.fresh inverseRun
                  have inversePolyBound : (Polynomial.var inverse : Polynomial F).inBounds s₅.roles.size = true := by
                    simpa [Scalar.Circuit.ArithExpr.inBounds] using inverseBound
                  obtain ⟨e₄, c₄⟩ := c₃.equation equationRun (by
                    simp only [Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true, and_true]
                    exact ⟨e₃.bound rightWordBound, inversePolyBound⟩)
                  refine ⟨c, ((e₁.trans e₂).trans e₃).trans e₄, c₄, Circuit.Compiler.bounded_field.mpr ?_⟩
                  simpa only [Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true, State.toReference] using
                    And.intro ((e₃.trans e₄).bound leftWordBound) (e₄.bound inversePolyBound)
      | call name args =>
          cases found : program.findSignature? name with
          | none => simp [found] at stepRun
          | some callee =>
              simp only [found] at stepRun
              obtain ⟨argValues, s₁, argsRun, checkBind⟩ := bind_ok.mp stepRun
              split at checkBind
              · simp [StateT.bind, bind, Except.bind] at checkBind
              · obtain ⟨⟨⟩, s₂, unchanged, destinationBind⟩ := bind_ok.mp checkBind
                obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                subst s₂
                obtain ⟨result, s₃, destinationRun, callBind⟩ := bind_ok.mp destinationBind
                obtain ⟨⟨⟩, s₆, callRun, pureRun⟩ := bind_ok.mp callBind
                obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
                subst middle
                obtain ⟨a, e₁, argsBound⟩ := lowerArgs_inactive argsRun layout scopeLayout valid scopeValid localsBound inactive
                have c₁ := start.afterArgs argsRun e₁
                obtain ⟨b, e₂, c₂, resultBound⟩ := c₁.destination destinationRun
                  (fun candidate equal => (targetBound candidate equal).mono e₁.increase)
                obtain ⟨e₃, c₃⟩ := c₂.call callRun
                  (fun arg member => (argsBound arg member).mono e₂.increase) resultBound
                exact ⟨b, (e₁.trans e₂).trans e₃, c₃, resultBound.mono e₃.increase⟩
      | matchValue scrutinee arms =>
          obtain ⟨checked, s₁, checkRun, typeBind⟩ := bind_ok.mp stepRun
          have stateEq := lift_unchanged checkRun
          subst s₁
          obtain ⟨type, s₂, typeRun, scrutineeBind⟩ := bind_ok.mp typeBind
          have stateEq := lift_unchanged typeRun
          subst s₂
          obtain ⟨scrutineeWire, s₃, scrutineeRun, destinationBind⟩ := bind_ok.mp scrutineeBind
          obtain ⟨result, s₄, destinationRun, choiceBind⟩ := bind_ok.mp destinationBind
          obtain ⟨branches, s₆, choiceRun, armsBind⟩ := bind_ok.mp choiceBind
          obtain ⟨⟨⟩, s₇, armsRun, pureRun⟩ := bind_ok.mp armsBind
          obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
          subst middle
          obtain ⟨a, e₁, scrutineeBound⟩ := lower_inactive scrutineeRun layout scopeLayout valid scopeValid localsBound (by simp) inactive
          have c₁ := start.afterLower scrutineeRun e₁
          obtain ⟨b, e₂, c₂, resultBound⟩ := c₁.destination destinationRun
            (fun candidate equal => (targetBound candidate equal).mono e₁.increase)
          obtain ⟨d, e₄, selected⟩ := choice_complete choiceRun c₂.layout c₂.scopeLayout c₂.valid none (by simpa using c₂.inactive)
          have c₄ := c₂.advance ⟨choice_extends choiceRun, choice_scoped choiceRun c₂.scopeLayout⟩ e₄
          have branchesInactive : ∀ branch ∈ branches, (s₆.activation branch).denote d = 0 := by
            intro branch member
            obtain ⟨i, bounded, equal⟩ := List.getElem_of_mem member
            simpa [choiceSelected, equal] using selected ⟨i, bounded⟩
          have chain := (e₁.trans e₂).trans e₄
          obtain ⟨e, e₅⟩ := lowerArms_inactive armsRun c₄.layout c₄.scopeLayout c₄.valid
            (choice_child_bound choiceRun) (localsBound.mono chain.increase)
            (scrutineeBound.mono (e₂.trans e₄).increase)
            (resultBound.mono e₄.increase) (by simp) branchesInactive
          have c₅ := c₄.advance (lowerArms_scoped armsRun c₄.scopeLayout (choice_child_bound choiceRun)) e₅
          exact ⟨e, chain.trans e₅, c₅, resultBound.mono (e₄.trans e₅).increase⟩
    obtain ⟨a, extension, context, bounded⟩ := step
    cases target with
    | none =>
        obtain ⟨rfl, stateEq⟩ := pure_ok.mp finished
        subst after
        exact ⟨a, extension, bounded⟩
    | some target =>
        obtain ⟨⟨⟩, last, equalRun, pureRun⟩ := bind_ok.mp finished
        obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
        subst after
        obtain ⟨equalExt, _⟩ := context.equal equalRun ((targetBound target rfl).mono extension.increase) bounded
        exact ⟨a, extension.trans equalExt, (targetBound target rfl).mono (extension.trans equalExt).increase⟩
  termination_by sizeOf expr

  theorem lowerArgs_inactive {program : Program F} {function : String} {locals : Locals F}
      {scope : ScopeId} {args : List (Expr F)} {output : List (Symbolic F)} {before after : State F}
      (compiled : lowerArgs program function locals scope args before = .ok (output, after))
      {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
      (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
      (valid : before.Valid rom calls initial) (scopeValid : scope < before.scopes.size)
      (localsBound : Circuit.Compiler.LocalsBounded before.roles.size locals)
      (inactive : (before.activation scope).denote initial = 0) :
      ∃ assignment, Extension rom calls before after initial assignment ∧
        ∀ value ∈ output, Circuit.Compiler.Bounded after.roles.size value := by
    cases args with
    | nil =>
        obtain ⟨rfl, stateEq⟩ := pure_ok.mp (by simpa only [lowerArgs] using compiled)
        subst after
        exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid), by simp⟩
    | cons arg rest =>
        simp only [lowerArgs] at compiled
        obtain ⟨head, s₁, headRun, tailBind⟩ := bind_ok.mp compiled
        obtain ⟨tail, s₂, tailRun, pureRun⟩ := bind_ok.mp tailBind
        obtain ⟨rfl, stateEq⟩ := pure_ok.mp pureRun
        subst after
        obtain ⟨a, e₁, headBound⟩ := lower_inactive headRun layout scopeLayout valid scopeValid localsBound (by simp) inactive
        have start : InactiveContext rom calls scope before initial := ⟨layout, scopeLayout, valid, scopeValid, inactive⟩
        have context := start.afterLower headRun e₁
        obtain ⟨b, e₂, tailBound⟩ := lowerArgs_inactive tailRun context.layout context.scopeLayout context.valid
          context.scopeValid (localsBound.mono e₁.increase) context.inactive
        refine ⟨b, e₁.trans e₂, ?_⟩
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact headBound.mono e₂.increase
        · exact tailBound value member
  termination_by sizeOf args

  theorem lowerArms_inactive {program : Program F} {function : String} {locals : Locals F}
      {scrutinee : Symbolic F} {result : WireValue Witness} {branches : List ScopeId}
      {arms : List (Pattern F × Expr F)} {previous : List (List (Polynomial F))} {before after : State F}
      (compiled : lowerArms program function locals scrutinee result branches arms previous before = .ok ((), after))
      {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
      (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
      (valid : before.Valid rom calls initial) (branchesValid : ∀ branch ∈ branches, branch < before.scopes.size)
      (localsBound : Circuit.Compiler.LocalsBounded before.roles.size locals)
      (scrutineeBound : Circuit.Compiler.Bounded before.roles.size scrutinee)
      (resultBound : Circuit.Compiler.Bounded (F := F) before.roles.size (result.map Polynomial.var))
      (previousBound : ∀ conditions ∈ previous, ∀ condition ∈ conditions, condition.inBounds before.roles.size = true)
      (inactive : ∀ branch ∈ branches, (before.activation branch).denote initial = 0) :
      ∃ assignment, Extension rom calls before after initial assignment := by
    cases branches with
    | nil =>
        cases arms with
        | nil =>
            obtain ⟨_, stateEq⟩ := pure_ok.mp (by simpa only [lowerArms] using compiled)
            subst after
            exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid)⟩
        | cons => simp [lowerArms] at compiled
    | cons branch branches =>
        cases arms with
        | nil => simp [lowerArms] at compiled
        | cons arm rest =>
            cases armEq : arm with
            | mk pat body =>
                simp only [armEq, lowerArms] at compiled
                obtain ⟨⟨conditions, bindings⟩, s₁, patternRun, equationsBind⟩ := bind_ok.mp compiled
                have stateEq := pattern_unchanged patternRun
                subst s₁
                obtain ⟨⟨⟩, s₂, equationsRun, failuresBind⟩ := bind_ok.mp equationsBind
                obtain ⟨⟨⟩, s₃, failuresRun, bodyBind⟩ := bind_ok.mp failuresBind
                obtain ⟨value, s₄, bodyRun, tailRun⟩ := bind_ok.mp bodyBind
                let start : InactiveContext rom calls branch before initial :=
                  ⟨layout, scopeLayout, valid, branchesValid branch (by simp), inactive branch (by simp)⟩
                obtain ⟨_, conditionsBound, bindingsBound⟩ := pattern_bounded patternRun scrutineeBound
                have equationsRun' : (do for condition in conditions do equation branch condition : Build F Unit)
                    before = .ok ((), s₂) := bind_ok.mpr ⟨PUnit.unit, s₂, equationsRun, rfl⟩
                obtain ⟨e₁, c₁⟩ := start.equations equationsRun' conditionsBound
                obtain ⟨a, e₂, c₂⟩ := c₁.failures failuresRun
                  (fun conditions member condition inside => e₁.bound (previousBound conditions member condition inside))
                have chain := e₁.trans e₂
                obtain ⟨b, e₃, _⟩ := lower_inactive bodyRun c₂.layout c₂.scopeLayout c₂.valid c₂.scopeValid
                  (Circuit.Compiler.localsBounded_append.mpr
                    ⟨bindingsBound.mono chain.increase, localsBound.mono chain.increase⟩)
                  (fun candidate equal => by cases equal; exact resultBound.mono chain.increase) c₂.inactive
                have c₃ := c₂.afterLower bodyRun e₃
                have full := chain.trans e₃
                split at tailRun
                · obtain ⟨_, stateEq⟩ := pure_ok.mp tailRun
                  subst after
                  exact ⟨b, full⟩
                · have failureStructure := forIn_scoped failuresRun c₁.scopeLayout c₁.scopeValid
                    (fun _ _ {_ _} run stateShape bound => failure_scoped run stateShape bound)
                  have structurePreserved := ((equations_grow equationsRun').trans failureStructure.1).trans
                    (lower_scoped bodyRun c₂.scopeLayout c₂.scopeValid).1
                  obtain ⟨c, tailExt⟩ := lowerArms_inactive tailRun c₃.layout c₃.scopeLayout c₃.valid
                    (fun child member => structurePreserved.scopeValid (branchesValid child (by simp [member])))
                    (localsBound.mono full.increase) (scrutineeBound.mono full.increase) (resultBound.mono full.increase)
                    (by
                      intro earlier member condition inside
                      rcases List.mem_append.mp member with old | last
                      · exact full.bound (previousBound earlier old condition inside)
                      · obtain rfl := List.mem_singleton.mp last
                        exact full.bound (conditionsBound condition inside))
                    (by
                      intro child member
                      rw [Extension.activation full structurePreserved scopeLayout (branchesValid child (by simp [member]))]
                      exact inactive child (by simp [member]))
                  exact ⟨c, full.trans tailExt⟩
  termination_by sizeOf arms
  decreasing_by all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
end

end Aiur.Optimized.Compiler
