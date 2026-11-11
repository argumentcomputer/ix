import Aiur.Generic.PatternLowering
import Aiur.Generic.OpenCore
import Aiur.Generic.PatternBindingsFacts

namespace Aiur.Generic.PatternLowering

variable {calls : CallRelation F}


/-- Removing one pointer-pattern layer is exactly an ordinary load, even when
the remaining pattern contains further loads. -/
@[simp] theorem lowerLet_load (env) (pat : Pattern α) (value body : Aiur.Expr α) :
    lowerLet env (.load pat) value body = lowerLet env pat (.load value) body := by
  rw [lowerLet]

@[simp] theorem lowerLet_load_bind (env) (name : String) (value body : Aiur.Expr α) :
    lowerLet env (.load (.bind name)) value body =
      .letValue (.bind name) (.load value) body := by
  simp [lowerLet, Pattern.toCore?]

/-- Read-only execution of a pattern plan. A failed test stops the attempt;
a bad load has no successful derivation and does not select a fallback. Only
temporary bindings have been installed when a test fails. -/
inductive Attempt [DecidableEq F] (heap : Heap F) :
    List (Step F) → Environment F Nat → Bool → Environment F Nat → Prop where
  | done : Attempt heap [] locals true locals
  | testHit
      (lookup : locals.find? (·.1 == input) = some (input, value))
      (matched : pat.bindings value = some bindings)
      (rest : Attempt heap steps (bindings ++ locals) accepted final) :
      Attempt heap (.test pat input :: steps) locals accepted final
  | testMiss
      (lookup : locals.find? (·.1 == input) = some (input, value))
      (missed : pat.bindings value = none) :
      Attempt heap (.test pat input :: steps) locals false locals
  | load
      (lookup : locals.find? (·.1 == input) = some (input, pointer))
      (loaded : loadValue heap pointer = .ok value)
      (rest : Attempt heap steps ((name, value) :: locals) accepted final) :
      Attempt heap (.load name input :: steps) locals accepted final

  | choiceLeft
      (selected : Attempt heap left locals true middle)
      (aligned : choiceLinks outputs leftBindings (List.range outputs.length) = some links)
      (copied : resolveBindings links middle = some installed)
      (rest : Attempt heap steps (installed ++ middle) accepted final) :
      Attempt heap (.choice outputs left leftBindings right rightBindings order :: steps) locals accepted final
  | choiceRight
      (missed : Attempt heap left locals false rejected)
      (selected : Attempt heap right rejected true middle)
      (aligned : choiceLinks outputs rightBindings order = some links)
      (copied : resolveBindings links middle = some installed)
      (rest : Attempt heap steps (installed ++ middle) accepted final) :
      Attempt heap (.choice outputs left leftBindings right rightBindings order :: steps) locals accepted final
  | choiceMiss
      (leftMissed : Attempt heap left locals false rejected)
      (rightMissed : Attempt heap right rejected false final) :
      Attempt heap (.choice outputs left leftBindings right rightBindings order :: steps) locals false final

variable [Field F] [DecidableEq F] {world : Engine.World F}

theorem choiceBody_iff {outputs bindings positions} {body : Aiur.Expr F}
    {locals : Environment F Nat} {before after : Heap F} {result : SourceValue F} :
    OpenCore.EvalExpr world calls locals (choiceBody outputs bindings positions body) before result after ↔
      ∃ links installed, choiceLinks outputs bindings positions = some links ∧
        resolveBindings links locals = some installed ∧
        OpenCore.EvalExpr world calls (installed ++ locals) body before result after := by
  cases aligned : choiceLinks outputs bindings positions with
  | none =>
      simp only [choiceBody, aligned]
      constructor
      · intro h; cases h with
        | matchValue _ selected _ => simp [selectArm] at selected
      · rintro ⟨_, _, h, _⟩; contradiction
  | some links =>
      simp only [choiceBody, aligned]
      rw [bindUsers_resolved_iff]
      simp

/-- `let &name = pointer; body` evaluates the pointer once, reads its cell,
and evaluates the body with the contents bound to `name`. -/
theorem load_bind_iff {env} {name : String} {locals : Environment F Nat}
    {pointer body : Aiur.Expr F} {before after : Heap F} {result : SourceValue F} :
    OpenCore.EvalExpr world calls locals (lowerLet env (.load (.bind name)) pointer body) before result after ↔
      ∃ address middle value,
        OpenCore.EvalExpr world calls locals pointer before address middle ∧
        loadValue middle address = .ok value ∧
        OpenCore.EvalExpr world calls ((name, value) :: locals) body middle result after := by
  rw [lowerLet_load_bind]
  constructor
  · intro h
    cases h with
    | letValue value matched body =>
        cases value with
        | load pointer loaded =>
            simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
            subst_vars
            exact ⟨_, _, _, pointer, loaded, body⟩
  · rintro ⟨address, middle, value, pointer, loaded, body⟩
    exact .letValue (bindings := [(name, value)]) (.load pointer loaded)
      (by simp [Aiur.Pattern.bindings]) body

/-- The selected continuation of a match attempt; no fallback means a partial
match cannot finish after a failed test. -/
def Continuation (world : Engine.World F) (calls : CallRelation F) (accepted : Bool) (locals : Environment F Nat)
    (body : Aiur.Expr F) (failure : Option (Aiur.Expr F))
    (before : Heap F) (result : SourceValue F) (after : Heap F) : Prop :=
  if accepted then OpenCore.EvalExpr world calls locals body before result after
  else ∃ fallback, failure = some fallback ∧ OpenCore.EvalExpr world calls locals fallback before result after

/-- Ordered match desugaring executes exactly the chosen plan continuation.
In particular, a failed earlier test bypasses all subsequent loads. -/
theorem matchSteps_iff {steps : List (Step F)} {locals : Environment F Nat}
    {body : Aiur.Expr F} {failure : Option (Aiur.Expr F)}
    {before after : Heap F} {result : SourceValue F} :
    OpenCore.EvalExpr world calls locals (matchSteps steps body failure) before result after ↔
      ∃ accepted final, Attempt before steps locals accepted final ∧
        Continuation world calls accepted final body failure before result after := by
  have sub (ss : List (Step F)) (smaller : sizeOf ss < sizeOf steps)
      (body : Aiur.Expr F) (failure : Option (Aiur.Expr F)) (locals : Environment F Nat) :=
    matchSteps_iff (steps := ss) (locals := locals) (body := body) (failure := failure) (before := before) (after := after) (result := result)
  cases steps with
  | nil =>
      rw [matchSteps]
      constructor
      · intro h; exact ⟨true, locals, .done, h⟩
      · rintro ⟨_, _, h, body⟩; cases h; exact body
  | cons step tail =>
      have ih := sub tail (by simp_wf; omega) body failure
      cases step with
      | load name input =>
          rw [matchSteps]
          constructor
          · intro h
            cases h with
            | letValue value matched body =>
                cases value with
                | load pointer loaded =>
                    cases pointer with
                    | var lookup =>
                        simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
                        subst_vars
                        obtain ⟨accepted, final, rest, body⟩ := (ih _).mp body
                        exact ⟨accepted, final, .load lookup loaded rest, body⟩
          · rintro ⟨accepted, final, h, body⟩
            cases h with
            | load lookup loaded rest =>
                exact .letValue (bindings := [(name, _)]) (.load (.var lookup) loaded) (by simp [Aiur.Pattern.bindings]) ((ih _).mpr ⟨accepted, final, rest, body⟩)
      | test pat input =>
          rw [matchSteps]
          constructor
          · intro h
            cases h with
            | matchValue value selected branch =>
                cases value with
                | var lookup =>
                    rename_i inputValue bindings selectedBody
                    cases matched : pat.bindings inputValue with
                    | some bindings =>
                        simp only [selectArm, matched, Option.some.injEq, Prod.mk.injEq] at selected
                        obtain ⟨rfl, rfl⟩ := selected
                        obtain ⟨accepted, final, rest, body⟩ := (ih _).mp branch
                        exact ⟨accepted, final, .testHit lookup matched rest, body⟩
                    | none =>
                        cases failure with
                        | none => simp [selectArm, matched] at selected
                        | some fallback =>
                            simp only [selectArm, matched, Option.toList_some, List.map_cons,
                              List.map_nil, Aiur.Pattern.bindings, Option.some.injEq, Prod.mk.injEq] at selected
                            obtain ⟨rfl, rfl⟩ := selected
                            exact ⟨false, _, .testMiss lookup matched, fallback, rfl, branch⟩
          · rintro ⟨accepted, final, h, body⟩
            cases h with
            | testHit lookup matched rest =>
                exact .matchValue (.var lookup) (by simp [selectArm, matched, matchSteps])
                  ((ih _).mpr ⟨accepted, final, rest, body⟩)
            | testMiss lookup missed =>
                obtain ⟨fallback, rfl, branch⟩ := body
                exact .matchValue (bindings := []) (body := fallback) (.var lookup)
                  (by simp [selectArm, missed, Aiur.Pattern.bindings]) branch

      | choice outputs left lbs right rbs order =>
          rw [matchSteps]
          rw [sub left (by simp_wf; omega)]
          constructor
          · rintro ⟨accepted, middle, attempted, cont⟩
            cases accepted with
            | true =>
                obtain ⟨links, installed, aligned, copied, rest⟩ := choiceBody_iff.mp cont
                obtain ⟨accepted, final, rest, cont⟩ := (ih _).mp rest
                exact ⟨accepted, final, .choiceLeft attempted aligned copied rest, cont⟩
            | false =>
                obtain ⟨fallback, eq, next⟩ := cont
                cases Option.some.inj eq
                obtain ⟨accepted, middle, rightAttempt, cont⟩ :=
                  (sub right (by simp_wf; omega) _ _ _).mp next
                cases accepted with
                | true =>
                    obtain ⟨links, installed, aligned, copied, rest⟩ := choiceBody_iff.mp cont
                    obtain ⟨accepted, final, rest, cont⟩ := (ih _).mp rest
                    exact ⟨accepted, final, .choiceRight attempted rightAttempt aligned copied rest, cont⟩
                | false => exact ⟨false, middle, .choiceMiss attempted rightAttempt, cont⟩
          · rintro ⟨accepted, final, attempted, cont⟩
            cases attempted with
            | choiceLeft selected aligned copied rest =>
                exact ⟨true, _, selected, choiceBody_iff.mpr ⟨_, _, aligned, copied,
                  (ih _).mpr ⟨accepted, final, rest, cont⟩⟩⟩
            | choiceRight missed selected aligned copied rest =>
                refine ⟨false, _, missed, _, rfl, ?_⟩
                exact (sub right (by simp_wf; omega) _ _ _).mpr ⟨true, _, selected,
                  choiceBody_iff.mpr ⟨_, _, aligned, copied,
                    (ih _).mpr ⟨accepted, final, rest, cont⟩⟩⟩
            | choiceMiss missed selected =>
                exact ⟨false, _, missed, _, rfl,
                  (sub right (by simp_wf; omega) _ _ _).mpr ⟨false, final, selected, cont⟩⟩
termination_by sizeOf steps
decreasing_by exact smaller

/-- Let desugaring succeeds exactly when all pattern tests and loads succeed,
followed by evaluation of the body. Pattern steps do not change the heap. -/
theorem letSteps_iff {steps : List (Step F)} {locals : Environment F Nat}
    {body : Aiur.Expr F} {before after : Heap F} {result : SourceValue F} :
    OpenCore.EvalExpr world calls locals (letSteps steps body) before result after ↔
      ∃ final, Attempt before steps locals true final ∧
        OpenCore.EvalExpr world calls final body before result after := by
  induction steps generalizing locals with
  | nil =>
      rw [letSteps]
      constructor
      · intro h; exact ⟨locals, .done, h⟩
      · rintro ⟨_, h, body⟩; cases h; exact body
  | cons step steps ih =>
      cases step with
      | test pat input =>
          rw [letSteps]
          constructor
          · intro h
            cases h with
            | letValue value matched body =>
                cases value with
                | var lookup =>
                    obtain ⟨final, rest, body⟩ := ih.mp body
                    exact ⟨final, .testHit lookup matched rest, body⟩
          · rintro ⟨final, h, body⟩
            cases h with
            | testHit lookup matched rest =>
                exact .letValue (.var lookup) matched (ih.mpr ⟨final, rest, body⟩)
      | load name input =>
          rw [letSteps]
          constructor
          · intro h
            cases h with
            | letValue value matched body =>
                cases value with
                | load pointer loaded =>
                    cases pointer with
                    | var lookup =>
                        simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
                        subst_vars
                        obtain ⟨final, rest, body⟩ := ih.mp body
                        exact ⟨final, .load lookup loaded rest, body⟩
          · rintro ⟨final, h, body⟩
            cases h with
            | load lookup loaded rest =>
                exact .letValue (bindings := [(name, _)]) (.load (.var lookup) loaded) (by simp [Aiur.Pattern.bindings]) (ih.mpr ⟨final, rest, body⟩)

      | choice outputs left lbs right rbs order =>
          rw [letSteps, matchSteps_iff]
          constructor
          · rintro ⟨accepted, middle, attempted, cont⟩
            cases accepted with
            | true =>
                obtain ⟨links, installed, aligned, copied, rest⟩ := choiceBody_iff.mp cont
                obtain ⟨final, rest, body⟩ := ih.mp rest
                exact ⟨final, .choiceLeft attempted aligned copied rest, body⟩
            | false =>
                obtain ⟨fallback, eq, next⟩ := cont
                cases Option.some.inj eq
                obtain ⟨accepted, middle, rightAttempt, cont⟩ := matchSteps_iff.mp next
                cases accepted with
                | true =>
                    obtain ⟨links, installed, aligned, copied, rest⟩ := choiceBody_iff.mp cont
                    obtain ⟨final, rest, body⟩ := ih.mp rest
                    exact ⟨final, .choiceRight attempted rightAttempt aligned copied rest, body⟩
                | false => obtain ⟨fallback, eq, _⟩ := cont; contradiction
          · rintro ⟨final, attempted, body⟩
            cases attempted with
            | choiceLeft selected aligned copied rest =>
                exact ⟨true, _, selected, choiceBody_iff.mpr ⟨_, _, aligned, copied,
                  ih.mpr ⟨final, rest, body⟩⟩⟩
            | choiceRight missed selected aligned copied rest =>
                exact ⟨false, _, missed, _, rfl, matchSteps_iff.mpr ⟨true, _, selected,
                  choiceBody_iff.mpr ⟨_, _, aligned, copied, ih.mpr ⟨final, rest, body⟩⟩⟩⟩

end Aiur.Generic.PatternLowering
