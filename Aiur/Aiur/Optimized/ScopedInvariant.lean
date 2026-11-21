import Aiur.Optimized.ScopedWitness

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem equation_grow {scope : ScopeId} {polynomial : Polynomial F} {before after : State F}
    (compiled : equation scope polynomial before = .ok ((), after)) : before.Extends after := by
  obtain rfl := equation_eq compiled
  exact ⟨fun _ _ => id, by simp, fun _ => id, fun _ => id⟩

theorem equations_grow {scope : ScopeId} {conditions : List (Polynomial F)} {before after : State F}
    (compiled : (do for condition in conditions do equation scope condition : Build F Unit)
      before = .ok ((), after)) : before.Extends after := by
  induction conditions generalizing before with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, StateT.bind, bind, Except.bind, Except.pure] using compiled
      subst after
      exact .refl before
  | cons condition conditions ih =>
      simp [List.forIn_cons, equation, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
      exact (equation_grow (scope := scope) (polynomial := condition) rfl).trans (ih compiled)

mutual
  theorem validate_scoped {layout : Layout} {scope : ScopeId} {words : List (Polynomial F)}
      {before after : State F} (compiled : validate scope layout words before = .ok ((), after))
      (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size) :
      before.Extends after ∧ after.Scoped := by
    cases layout with
    | field =>
        cases words with
        | nil => simp [validate] at compiled
        | cons word rest =>
            cases rest with
            | cons => simp [validate] at compiled
            | nil =>
                obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validate] using compiled)
                exact ⟨.refl _, scopeLayout⟩
    | ptr target =>
        cases words with
        | nil => simp [validate] at compiled
        | cons word rest =>
            cases rest with
            | cons => simp [validate] at compiled
            | nil =>
                obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validate] using compiled)
                exact ⟨.refl _, scopeLayout⟩
    | tuple layouts => exact validateList_scoped (by simpa only [validate] using compiled) scopeLayout scopeValid
    | enum name constructors =>
        simp only [validate] at compiled
        cases parts : Layout.enumParts constructors.length (.const 0) words with
        | none => simp [parts] at compiled
        | some pair =>
            rcases pair with ⟨tag, payload⟩
            simp only [parts] at compiled
            split at compiled
            · simp [StateT.bind, bind, Except.bind] at compiled
            · obtain ⟨⟨⟩, unchangedState, unchanged, choiceBind⟩ := bind_ok.mp compiled
              obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
              subst unchangedState
              obtain ⟨branches, middle, choiceRun, ctorRun⟩ := bind_ok.mp choiceBind
              obtain ⟨ctorExtension, finalLayout⟩ := validateConstructors_scoped ctorRun
                (choice_scoped choiceRun scopeLayout) (choice_child_bound choiceRun)
              exact ⟨(choice_extends choiceRun).trans ctorExtension, finalLayout⟩
  termination_by sizeOf layout

  theorem validateList_scoped {layouts : List Layout} {scope : ScopeId} {words : List (Polynomial F)}
      {before after : State F} (compiled : validateList scope layouts words before = .ok ((), after))
      (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size) :
      before.Extends after ∧ after.Scoped := by
    cases layouts with
    | nil =>
        cases words with
        | nil =>
            obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validateList] using compiled)
            exact ⟨.refl _, scopeLayout⟩
        | cons => simp [validateList] at compiled
    | cons layout layouts =>
        simp only [validateList] at compiled
        split at compiled
        · simp [StateT.bind, bind, Except.bind] at compiled
        · obtain ⟨⟨⟩, unchangedState, unchanged, validationBind⟩ := bind_ok.mp compiled
          obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
          subst unchangedState
          obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp validationBind
          obtain ⟨headExtension, middleLayout⟩ := validate_scoped headRun scopeLayout scopeValid
          obtain ⟨tailExtension, finalLayout⟩ := validateList_scoped tailRun middleLayout
            (headExtension.scopeValid scopeValid)
          exact ⟨headExtension.trans tailExtension, finalLayout⟩
  termination_by sizeOf layouts

  theorem validateConstructors_scoped {constructors : List (String × Layout)} {branches : List ScopeId}
      {tag : Polynomial F} {payload : List (Polynomial F)} {index : Nat} {before after : State F}
      (compiled : validateConstructors constructors branches tag payload index before = .ok ((), after))
      (scopeLayout : before.Scoped) (branchesValid : ∀ branch ∈ branches, branch < before.scopes.size) :
      before.Extends after ∧ after.Scoped := by
    cases constructors with
    | nil =>
        cases branches with
        | nil =>
            obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validateConstructors] using compiled)
            exact ⟨.refl _, scopeLayout⟩
        | cons => simp [validateConstructors] at compiled
    | cons ctor rest =>
        cases hctor : ctor with
        | mk ctorName ctorLayout =>
            cases branches with
            | nil => simp [validateConstructors] at compiled
            | cons branch branches =>
                simp only [hctor, validateConstructors] at compiled
                obtain ⟨⟨⟩, s₁, tagRun, payloadBind⟩ := bind_ok.mp compiled
                obtain ⟨⟨⟩, s₂, payloadRun, paddingBind⟩ := bind_ok.mp payloadBind
                obtain ⟨⟨⟩, s₃, paddingRun, tailRun⟩ := bind_ok.mp paddingBind
                have tagExtension := equation_grow tagRun
                have branchValid := branchesValid branch (by simp)
                obtain ⟨payloadExtension, payloadLayout⟩ := validate_scoped payloadRun
                  (equation_scoped tagRun scopeLayout branchValid) (tagExtension.scopeValid branchValid)
                have paddingRun' : (do for word in payload.drop ctorLayout.width do equation branch word : Build F Unit)
                    s₂ = .ok ((), s₃) := bind_ok.mpr ⟨PUnit.unit, s₃, paddingRun, rfl⟩
                have paddingExtension := equations_grow paddingRun'
                have prefixExtension := (tagExtension.trans payloadExtension).trans paddingExtension
                have paddingLayout := equations_scoped paddingRun' payloadLayout
                  (payloadExtension.scopeValid (tagExtension.scopeValid branchValid))
                obtain ⟨tailExtension, finalLayout⟩ := validateConstructors_scoped tailRun paddingLayout
                  (fun child member => prefixExtension.scopeValid (branchesValid child (by simp [member])))
                exact ⟨prefixExtension.trans tailExtension, finalLayout⟩
  termination_by sizeOf constructors
  decreasing_by all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
end

theorem validateValue_scoped {decls : Declarations} {scope : ScopeId} {value : Symbolic F}
    {before after : State F} (compiled : validateValue decls scope value before = .ok ((), after))
    (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size) :
    before.Extends after ∧ after.Scoped := by
  simp only [validateValue] at compiled
  obtain ⟨layout, middle, layoutRun, validationRun⟩ := bind_ok.mp compiled
  obtain ⟨_, stateEq⟩ := getLayout_eq layoutRun
  subst middle
  exact validate_scoped validationRun scopeLayout scopeValid

private theorem polynomial_has_bound (polynomial : Polynomial F) :
    ∃ bound, polynomial.inBounds bound = true := by
  induction polynomial with
  | const value => exact ⟨0, rfl⟩
  | var id => exact ⟨id + 1, by simp [Circuit.ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds]⟩
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
      obtain ⟨left, leftBound⟩ := ha
      obtain ⟨right, rightBound⟩ := hb
      refine ⟨max left right, ?_⟩
      simpa only [Circuit.ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true] using
        And.intro (Scalar.Circuit.ArithExpr.inBounds_mono (Nat.le_max_left _ _) leftBound)
          (Scalar.Circuit.ArithExpr.inBounds_mono (Nat.le_max_right _ _) rightBound)

private theorem words_have_bound (words : List (Polynomial F)) :
    ∃ bound, ∀ polynomial ∈ words, polynomial.inBounds bound = true := by
  induction words with
  | nil => exact ⟨0, by simp⟩
  | cons polynomial rest ih =>
      obtain ⟨left, leftBound⟩ := polynomial_has_bound polynomial
      obtain ⟨right, rightBound⟩ := ih
      refine ⟨max left right, ?_⟩
      intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact Scalar.Circuit.ArithExpr.inBounds_mono (Nat.le_max_left _ _) leftBound
      · exact Scalar.Circuit.ArithExpr.inBounds_mono (Nat.le_max_right _ _) (rightBound p member)

theorem pattern_unchanged {decls : Declarations} {pat : Pattern F} {value : Symbolic F}
    {conditions : List (Polynomial F)} {bindings : Locals F} {before after : State F}
    (compiled : pattern decls pat value before = .ok ((conditions, bindings), after)) : after = before := by
  obtain ⟨bound, bounded⟩ := words_have_bound value.words
  exact (pattern_bounded compiled (bound := bound) bounded).1

private theorem failure_terms_scoped {scope : ScopeId} {conditions terms : List (Polynomial F)}
    {before after : State F}
    (compiled : (conditions.mapM fun difference => do
      return Polynomial.mul difference (.var (← fresh (.auxiliary scope)))) before = .ok (terms, after))
    (scopeLayout : before.Scoped) : before.Extends after ∧ after.Scoped := by
  induction conditions generalizing terms before with
  | nil =>
      obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [List.mapM_nil] using compiled)
      exact ⟨.refl _, scopeLayout⟩
  | cons condition conditions ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨term, s₁, headRun, tailBind⟩ := bind_ok.mp compiled
      obtain ⟨tail, s₂, tailRun, finished⟩ := bind_ok.mp tailBind
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      obtain ⟨id, middle, freshRun, headFinish⟩ := bind_ok.mp headRun
      obtain ⟨_, stateEq⟩ := pure_ok.mp headFinish
      subst s₁
      obtain ⟨tailExtension, finalLayout⟩ := ih tailRun (fresh_scoped freshRun scopeLayout)
      exact ⟨(fresh_extends freshRun).trans tailExtension, finalLayout⟩

theorem failure_scoped {scope : ScopeId} {conditions : List (Polynomial F)} {before after : State F}
    (compiled : failure scope conditions before = .ok ((), after))
    (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size) :
    before.Extends after ∧ after.Scoped := by
  simp only [failure] at compiled
  obtain ⟨terms, middle, termsRun, equationRun⟩ := bind_ok.mp compiled
  obtain ⟨termsExtension, middleLayout⟩ := failure_terms_scoped termsRun scopeLayout
  exact ⟨termsExtension.trans (equation_grow equationRun),
    equation_scoped equationRun middleLayout (termsExtension.scopeValid scopeValid)⟩

theorem forIn_scoped {α : Type} {items : List α} {action : α → Build F Unit}
    {scope : ScopeId} {before after : State F}
    (compiled : (forIn items PUnit.unit (fun item _ => do
      action item
      pure (ForInStep.yield PUnit.unit)) : Build F PUnit) before = .ok (PUnit.unit, after))
    (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size)
    (each : ∀ item ∈ items, ∀ {first last : State F}, action item first = .ok ((), last) →
      first.Scoped → scope < first.scopes.size → first.Extends last ∧ last.Scoped) :
    before.Extends after ∧ after.Scoped := by
  induction items generalizing before with
  | nil =>
      obtain ⟨_, stateEq⟩ := pure_ok.mp (by simpa only [List.forIn_nil] using compiled)
      subst after
      exact ⟨.refl _, scopeLayout⟩
  | cons item rest ih =>
      simp only [List.forIn_cons] at compiled
      obtain ⟨step, middle, stepRun, restRun⟩ := bind_ok.mp compiled
      obtain ⟨⟨⟩, s₁, actionRun, stepFinish⟩ := bind_ok.mp stepRun
      obtain ⟨rfl, stateEq⟩ := pure_ok.mp stepFinish
      subst middle
      obtain ⟨headExtension, middleLayout⟩ := each item (by simp) actionRun scopeLayout scopeValid
      obtain ⟨tailExtension, finalLayout⟩ := ih restRun middleLayout
        (headExtension.scopeValid scopeValid) (fun item member => each item (by simp [member]))
      exact ⟨headExtension.trans tailExtension, finalLayout⟩

theorem equalValue_structural {scope : ScopeId} {left right : Symbolic F} {before after : State F}
    (compiled : equalValue scope left right before = .ok ((), after))
    (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size) :
    before.Extends after ∧ after.Scoped := by
  refine ⟨?_, equalValue_scoped compiled scopeLayout scopeValid⟩
  simp only [equalValue] at compiled
  split at compiled
  · simp [StateT.bind, bind, Except.bind] at compiled
  · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
    obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
    subst middle
    apply equations_grow (conditions := (left.words.zip right.words).map fun (a, b) => Polynomial.sub a b)
    simpa only [List.forIn_map] using rest

theorem lift_unchanged {α : Type} {computation : Except String α} {value : α} {before after : State F}
    (compiled : (liftM computation : Build F α) before = .ok (value, after)) : before = after := by
  cases computation with
  | error message => cases compiled
  | ok output => exact (Prod.mk.inj (Except.ok.inj compiled)).2

theorem pushCell_scoped {state : State F} (scopeLayout : state.Scoped) (cell : Cell F)
    (scopeValid : cell.scope < state.scopes.size) :
    state.Extends {state with cells := state.cells.push cell} ∧
      ({state with cells := state.cells.push cell} : State F).Scoped := by
  refine ⟨⟨fun _ _ => id, fun _ => id, fun _ => id, by simp⟩,
    ⟨scopeLayout.equations, scopeLayout.calls, ?_, scopeLayout.activations⟩⟩
  intro next member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact scopeLayout.cells next old
  · exact scopeValid

theorem pushCall_scoped {state : State F} (scopeLayout : state.Scoped) (call : Call F)
    (scopeValid : call.scope < state.scopes.size) :
    state.Extends {state with calls := state.calls.push call} ∧
      ({state with calls := state.calls.push call} : State F).Scoped := by
  refine ⟨⟨fun _ _ => id, fun _ => id, by simp, fun _ => id⟩,
    ⟨scopeLayout.equations, ?_, scopeLayout.cells, scopeLayout.activations⟩⟩
  intro next member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact scopeLayout.calls next old
  · exact scopeValid

mutual
  theorem lower_scoped {program : Program F} {function : String} {locals : Locals F}
      {scope : ScopeId} {expr : Expr F} {target : Option (WireValue Witness)} {output : Symbolic F}
      {before after : State F}
      (compiled : lower program function locals scope expr target before = .ok (output, after))
      (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size) :
      before.Extends after ∧ after.Scoped := by
    rw [lower.eq_def] at compiled
    obtain ⟨value, middle, stepRun, finished⟩ := bind_ok.mp compiled
    have step : before.Extends middle ∧ middle.Scoped := by
      cases expr with
      | literal literal =>
          obtain ⟨_, stateEq⟩ := pure_ok.mp stepRun
          subst middle
          exact ⟨.refl _, scopeLayout⟩
      | var name =>
          cases found : locals.find? (·.1 == name) with
          | none => simp [found] at stepRun
          | some binding =>
              rcases binding with ⟨key, wire⟩
              simp only [found] at stepRun
              obtain ⟨_, stateEq⟩ := pure_ok.mp stepRun
              subst middle
              exact ⟨.refl _, scopeLayout⟩
      | tuple items =>
          obtain ⟨values, s₁, argsRun, pureRun⟩ := bind_ok.mp stepRun
          obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
          subst middle
          exact lowerArgs_scoped argsRun scopeLayout scopeValid
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
                  obtain ⟨argExtension, argLayout⟩ := lowerArgs_scoped argsRun scopeLayout scopeValid
                  split at checkBind
                  · simp [StateT.bind, bind, Except.bind] at checkBind
                  · obtain ⟨⟨⟩, s₂, unchanged, layoutBind⟩ := bind_ok.mp checkBind
                    obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                    subst s₂
                    obtain ⟨layout, s₃, layoutRun, widthBind⟩ := bind_ok.mp layoutBind
                    obtain ⟨_, stateEq⟩ := getLayout_eq layoutRun
                    subst s₃
                    split at widthBind
                    · simp [StateT.bind, bind, Except.bind] at widthBind
                    · obtain ⟨⟨⟩, s₄, unchanged, pureRun⟩ := bind_ok.mp widthBind
                      obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
                      subst s₄
                      obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
                      subst middle
                      exact ⟨argExtension, argLayout⟩
      | project operand index =>
          obtain ⟨wire, s₁, operandRun, projectBind⟩ := bind_ok.mp stepRun
          obtain ⟨operandExtension, operandLayout⟩ := lower_scoped operandRun scopeLayout scopeValid
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
                  obtain ⟨_, stateEq⟩ := pure_ok.mp resultRun
                  subst middle
                  exact ⟨operandExtension, operandLayout⟩
      | letValue pat operand body =>
          obtain ⟨wire, s₁, operandRun, patternBind⟩ := bind_ok.mp stepRun
          obtain ⟨⟨conditions, bindings⟩, s₂, patternRun, equationsBind⟩ := bind_ok.mp patternBind
          obtain ⟨⟨⟩, s₃, equationRun, bodyRun⟩ := bind_ok.mp equationsBind
          have stateEq := pattern_unchanged patternRun
          subst s₂
          have equationRun' : (do for condition in conditions do equation scope condition : Build F Unit)
              s₁ = .ok ((), s₃) := bind_ok.mpr ⟨PUnit.unit, s₃, equationRun, rfl⟩
          obtain ⟨operandExtension, operandLayout⟩ := lower_scoped operandRun scopeLayout scopeValid
          have equationExtension := equations_grow equationRun'
          have prefixExtension := operandExtension.trans equationExtension
          have equationLayout := equations_scoped equationRun' operandLayout (operandExtension.scopeValid scopeValid)
          obtain ⟨bodyExtension, finalLayout⟩ := lower_scoped bodyRun equationLayout
            (prefixExtension.scopeValid scopeValid)
          exact ⟨prefixExtension.trans bodyExtension, finalLayout⟩
      | store operand =>
          obtain ⟨wire, s₁, operandRun, destinationBind⟩ := bind_ok.mp stepRun
          obtain ⟨result, s₂, destinationRun, pointerBind⟩ := bind_ok.mp destinationBind
          obtain ⟨operandExtension, operandLayout⟩ := lower_scoped operandRun scopeLayout scopeValid
          have destinationExtension := destination_extends destinationRun
          have prefixExtension := operandExtension.trans destinationExtension
          have destinationLayout := destination_scoped destinationRun operandLayout
          cases wordsEq : result.words with
          | nil => simp [wordsEq] at pointerBind
          | cons address rest =>
              cases rest with
              | cons => simp [wordsEq] at pointerBind
              | nil =>
                  simp only [wordsEq] at pointerBind
                  obtain ⟨⟨⟩, s₃, storeRun, pureRun⟩ := bind_ok.mp pointerBind
                  obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
                  subst middle
                  change Except.ok ((), {s₂ with cells := s₂.cells.push ⟨scope, .var address, wire⟩}) = .ok ((), s₃) at storeRun
                  have stateEq := (Prod.mk.inj (Except.ok.inj storeRun)).2
                  subst s₃
                  obtain ⟨cellExtension, finalLayout⟩ := pushCell_scoped destinationLayout
                    ⟨scope, .var address, wire⟩ (prefixExtension.scopeValid scopeValid)
                  exact ⟨prefixExtension.trans cellExtension, finalLayout⟩
      | load operand =>
          obtain ⟨pointer, s₁, operandRun, pointerBind⟩ := bind_ok.mp stepRun
          obtain ⟨operandExtension, operandLayout⟩ := lower_scoped operandRun scopeLayout scopeValid
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
                      obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
                      subst middle
                      have prefixExtension := operandExtension.trans (destination_extends destinationRun)
                      change Except.ok ((), {s₂ with cells := s₂.cells.push ⟨scope, address, result.map Polynomial.var⟩}) =
                        .ok ((), s₃) at loadRun
                      have stateEq := (Prod.mk.inj (Except.ok.inj loadRun)).2
                      subst s₃
                      obtain ⟨cellExtension, finalLayout⟩ := pushCell_scoped
                        (destination_scoped destinationRun operandLayout)
                        ⟨scope, address, result.map Polynomial.var⟩ (prefixExtension.scopeValid scopeValid)
                      exact ⟨prefixExtension.trans cellExtension, finalLayout⟩
      | neg operand =>
          obtain ⟨wire, s₁, operandRun, fieldBind⟩ := bind_ok.mp stepRun
          obtain ⟨polynomial, s₂, fieldRun, pureRun⟩ := bind_ok.mp fieldBind
          obtain ⟨_, stateEq⟩ := asField_eq fieldRun
          subst s₂
          obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
          subst middle
          exact lower_scoped operandRun scopeLayout scopeValid
      | hint type key channel =>
          obtain ⟨keyWire, s₁, keyRun, pointerCheck⟩ := bind_ok.mp stepRun
          split at pointerCheck
          · simp [StateT.bind, bind, Except.bind] at pointerCheck
          · obtain ⟨⟨⟩, s₂, unchanged, destinationBind⟩ := bind_ok.mp pointerCheck
            obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
            subst s₂
            obtain ⟨result, s₃, destinationRun, validationBind⟩ := bind_ok.mp destinationBind
            obtain ⟨⟨⟩, s₄, validationRun, pureRun⟩ := bind_ok.mp validationBind
            obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
            subst middle
            obtain ⟨keyExtension, keyLayout⟩ := lower_scoped keyRun scopeLayout scopeValid
            have prefixExtension := keyExtension.trans (destination_extends destinationRun)
            obtain ⟨validationExtension, finalLayout⟩ := validateValue_scoped validationRun
              (destination_scoped destinationRun keyLayout) (prefixExtension.scopeValid scopeValid)
            exact ⟨prefixExtension.trans validationExtension, finalLayout⟩
      | assertEq message left right =>
          obtain ⟨leftWire, s₁, leftRun, rightBind⟩ := bind_ok.mp stepRun
          obtain ⟨rightWire, s₂, rightRun, pointerCheck⟩ := bind_ok.mp rightBind
          split at pointerCheck
          · simp [StateT.bind, bind, Except.bind] at pointerCheck
          · obtain ⟨⟨⟩, s₃, unchanged, equalityBind⟩ := bind_ok.mp pointerCheck
            obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
            subst s₃
            obtain ⟨⟨⟩, s₄, equalityRun, pureRun⟩ := bind_ok.mp equalityBind
            obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
            subst middle
            obtain ⟨leftExtension, leftLayout⟩ := lower_scoped leftRun scopeLayout scopeValid
            obtain ⟨rightExtension, rightLayout⟩ := lower_scoped rightRun leftLayout
              (leftExtension.scopeValid scopeValid)
            have prefixExtension := leftExtension.trans rightExtension
            obtain ⟨equalityExtension, finalLayout⟩ := equalValue_structural equalityRun rightLayout
              (prefixExtension.scopeValid scopeValid)
            exact ⟨prefixExtension.trans equalityExtension, finalLayout⟩
      | binary op left right =>
          obtain ⟨leftWire, s₁, leftRun, leftFieldBind⟩ := bind_ok.mp stepRun
          obtain ⟨leftWord, s₂, leftFieldRun, rightBind⟩ := bind_ok.mp leftFieldBind
          obtain ⟨_, stateEq⟩ := asField_eq leftFieldRun
          subst s₂
          obtain ⟨rightWire, s₃, rightRun, rightFieldBind⟩ := bind_ok.mp rightBind
          obtain ⟨rightWord, s₄, rightFieldRun, operatorRun⟩ := bind_ok.mp rightFieldBind
          obtain ⟨_, stateEq⟩ := asField_eq rightFieldRun
          subst s₄
          obtain ⟨leftExtension, leftLayout⟩ := lower_scoped leftRun scopeLayout scopeValid
          obtain ⟨rightExtension, rightLayout⟩ := lower_scoped rightRun leftLayout
            (leftExtension.scopeValid scopeValid)
          have prefixExtension := leftExtension.trans rightExtension
          cases op with
          | add | sub | mul =>
              obtain ⟨_, stateEq⟩ := pure_ok.mp operatorRun
              subst middle
              exact ⟨prefixExtension, rightLayout⟩
          | div =>
              cases folded : rightWord.constantInverse? with
              | some inverse =>
                  simp only [folded] at operatorRun
                  obtain ⟨_, stateEq⟩ := pure_ok.mp operatorRun
                  subst middle
                  exact ⟨prefixExtension, rightLayout⟩
              | none =>
                  simp only [folded] at operatorRun
                  obtain ⟨inverse, s₅, inverseRun, equationBind⟩ := bind_ok.mp operatorRun
                  obtain ⟨⟨⟩, s₆, equationRun, pureRun⟩ := bind_ok.mp equationBind
                  obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
                  subst middle
                  have inverseExtension := prefixExtension.trans (fresh_extends inverseRun)
                  exact ⟨inverseExtension.trans (equation_grow equationRun),
                    equation_scoped equationRun (fresh_scoped inverseRun rightLayout)
                      (inverseExtension.scopeValid scopeValid)⟩
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
                obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
                subst middle
                obtain ⟨argsExtension, argsLayout⟩ := lowerArgs_scoped argsRun scopeLayout scopeValid
                have destinationExtension := argsExtension.trans (destination_extends destinationRun)
                change Except.ok ((), {s₃ with calls := s₃.calls.push ⟨scope, name, argValues, result⟩}) = .ok ((), s₆) at callRun
                have stateEq := (Prod.mk.inj (Except.ok.inj callRun)).2
                subst s₆
                obtain ⟨callExtension, finalLayout⟩ := pushCall_scoped (destination_scoped destinationRun argsLayout)
                  ⟨scope, name, argValues, result⟩ (destinationExtension.scopeValid scopeValid)
                exact ⟨destinationExtension.trans callExtension, finalLayout⟩
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
          obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
          subst middle
          obtain ⟨scrutineeExtension, scrutineeLayout⟩ := lower_scoped scrutineeRun scopeLayout scopeValid
          have prefixExtension := scrutineeExtension.trans (destination_extends destinationRun)
          have choicesExtension := prefixExtension.trans (choice_extends choiceRun)
          obtain ⟨armsExtension, finalLayout⟩ := lowerArms_scoped armsRun
            (choice_scoped choiceRun (destination_scoped destinationRun scrutineeLayout)) (choice_child_bound choiceRun)
          exact ⟨choicesExtension.trans armsExtension, finalLayout⟩
    cases target with
    | none =>
        obtain ⟨_, stateEq⟩ := pure_ok.mp finished
        subst after
        exact step
    | some target =>
        obtain ⟨⟨⟩, last, equalRun, pureRun⟩ := bind_ok.mp finished
        obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
        subst after
        obtain ⟨equalExtension, finalLayout⟩ := equalValue_structural equalRun step.2 (step.1.scopeValid scopeValid)
        exact ⟨step.1.trans equalExtension, finalLayout⟩
  termination_by sizeOf expr

  theorem lowerArgs_scoped {program : Program F} {function : String} {locals : Locals F}
      {scope : ScopeId} {args : List (Expr F)} {output : List (Symbolic F)} {before after : State F}
      (compiled : lowerArgs program function locals scope args before = .ok (output, after))
      (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size) :
      before.Extends after ∧ after.Scoped := by
    cases args with
    | nil =>
        obtain ⟨_, stateEq⟩ := pure_ok.mp (by simpa only [lowerArgs] using compiled)
        subst after
        exact ⟨.refl _, scopeLayout⟩
    | cons arg rest =>
        simp only [lowerArgs] at compiled
        obtain ⟨head, s₁, headRun, tailBind⟩ := bind_ok.mp compiled
        obtain ⟨tail, s₂, tailRun, pureRun⟩ := bind_ok.mp tailBind
        obtain ⟨_, stateEq⟩ := pure_ok.mp pureRun
        subst after
        obtain ⟨headExtension, headLayout⟩ := lower_scoped headRun scopeLayout scopeValid
        obtain ⟨tailExtension, finalLayout⟩ := lowerArgs_scoped tailRun headLayout (headExtension.scopeValid scopeValid)
        exact ⟨headExtension.trans tailExtension, finalLayout⟩
  termination_by sizeOf args

  theorem lowerArms_scoped {program : Program F} {function : String} {locals : Locals F}
      {scrutinee : Symbolic F} {result : WireValue Witness} {branches : List ScopeId}
      {arms : List (Pattern F × Expr F)} {previous : List (List (Polynomial F))} {before after : State F}
      (compiled : lowerArms program function locals scrutinee result branches arms previous before = .ok ((), after))
      (scopeLayout : before.Scoped) (branchesValid : ∀ branch ∈ branches, branch < before.scopes.size) :
      before.Extends after ∧ after.Scoped := by
    cases branches with
    | nil =>
        cases arms with
        | nil =>
            obtain ⟨_, stateEq⟩ := pure_ok.mp (by simpa only [lowerArms] using compiled)
            subst after
            exact ⟨.refl _, scopeLayout⟩
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
                have branchValid := branchesValid branch (by simp)
                have equationsRun' : (do for condition in conditions do equation branch condition : Build F Unit)
                    before = .ok ((), s₂) := bind_ok.mpr ⟨PUnit.unit, s₂, equationsRun, rfl⟩
                have equationExtension := equations_grow equationsRun'
                have equationLayout := equations_scoped equationsRun' scopeLayout branchValid
                obtain ⟨failuresExtension, failuresLayout⟩ := forIn_scoped failuresRun equationLayout
                  (equationExtension.scopeValid branchValid)
                  (fun earlier _ {_ _} run layout bound => failure_scoped run layout bound)
                have prefixExtension := equationExtension.trans failuresExtension
                obtain ⟨bodyExtension, bodyLayout⟩ := lower_scoped bodyRun failuresLayout
                  (prefixExtension.scopeValid branchValid)
                have armsExtension := prefixExtension.trans bodyExtension
                split at tailRun
                · obtain ⟨_, stateEq⟩ := pure_ok.mp tailRun
                  subst after
                  exact ⟨armsExtension, bodyLayout⟩
                · obtain ⟨tailExtension, finalLayout⟩ := lowerArms_scoped tailRun bodyLayout
                    (fun child member => armsExtension.scopeValid (branchesValid child (by simp [member])))
                  exact ⟨armsExtension.trans tailExtension, finalLayout⟩
  termination_by sizeOf arms
  decreasing_by all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
end

end Aiur.Optimized.Compiler
