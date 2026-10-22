import Aiur.Optimized.WitnessContext
import Aiur.Optimized.InactiveWitness
import Aiur.Optimized.FailureWitness
import Aiur.Optimized.PatternIrrefutable

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
open Circuit.Compiler (Bounded LocalsBounded localsEnvironment localsEnvironment_append localsBounded_append)
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

/-- The selected source arm receives the only enabled scope. Other arms can
be witnessed without evaluation, while previous-pattern failures enforce order. -/
theorem lowerArms_complete {program : Program F} (checked : checkDeclarations program.enums = .ok ())
    (tags : program.enums.tagsValid F = true)
    {calls : Circuit.CallRelation F} {sourceCalls : Aiur.CallRelation F} {function : String}
    {locals : Locals F} {scrutinee : Symbolic F} {result : WireValue Witness}
    {scopes : List ScopeId} {arms : List (Pattern F × Expr F)} {previous : List (List (Polynomial F))}
    (bodyCompletes : ∀ arm ∈ arms, ExprComplete program sourceCalls calls function arm.2)
    {before after : State F}
    (compiled : lowerArms program function locals scrutinee result scopes arms previous before = .ok ((), after))
    {rom : WireROM F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
    (valid : before.Valid rom calls initial) (scopesValid : ∀ scope ∈ scopes, scope < before.scopes.size)
    (localsBound : LocalsBounded before.roles.size locals) (scrutineeBound : Bounded before.roles.size scrutinee)
    (resultBound : Bounded (F := F) before.roles.size (result.map Polynomial.var))
    (previousBound : ∀ conditions ∈ previous, ∀ condition ∈ conditions, condition.inBounds before.roles.size = true)
    {environment : Environment F}
    (decoded : DecodesEnvironment program.enums (localsEnvironment locals initial) environment)
    {input value : Value F}
    (inputDecode : (scrutinee.map (Circuit.ArithExpr.denote initial)).decode program.enums = some input)
    (resultDecode : (result.map initial).decode program.enums = some value)
    {bindings : Environment F} {body : Expr F}
    (selected : selectArm input arms = some (bindings, body))
    (evaluated : ROMEvalExprWith program.enums (rom.decode program.enums) sourceCalls
      (bindings ++ environment) body value)
    (selectors : ∀ i : Fin scopes.length, (before.activation scopes[i]).denote initial =
      if i.val = armIndex input arms then 1 else 0)
    (previousFailed : ∀ conditions ∈ previous, ¬AllZero conditions initial) :
    ∃ assignment, Extension rom calls before after initial assignment := by
  induction arms generalizing scopes previous before initial with
  | nil => simp [selectArm] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pat, headBody⟩
      cases scopes with
      | nil => simp [lowerArms] at compiled
      | cons scope scopes =>
          simp only [lowerArms] at compiled
          obtain ⟨⟨conditions, patternBindings⟩, patternState, patternRun, guardsBind⟩ := bind_ok.mp compiled
          obtain ⟨stateEq, conditionsBound, bindingsBound⟩ := pattern_bounded patternRun scrutineeBound
          subst patternState
          obtain ⟨⟨⟩, s₁, equationsRun, failuresBind⟩ := bind_ok.mp guardsBind
          obtain ⟨⟨⟩, s₂, failuresRun, bodyBind⟩ := bind_ok.mp failuresBind
          obtain ⟨bodyWire, s₃, bodyRun, tailRun⟩ := bind_ok.mp bodyBind
          have scopeValid := scopesValid scope (by simp)
          have equationsRun' : (do for condition in conditions do equation scope condition : Build F Unit)
              before = .ok ((), s₁) := bind_ok.mpr ⟨(), s₁, equationsRun, rfl⟩
          have failuresRun' : (do for earlier in previous do failure scope earlier : Build F Unit)
              s₁ = .ok ((), s₂) := bind_ok.mpr ⟨(), s₂, failuresRun, rfl⟩
          have equationStructure := equations_grow equationsRun'
          have equationScoped := equations_scoped equationsRun' scopeLayout scopeValid
          have scopeValid₁ := equationStructure.scopeValid scopeValid
          obtain ⟨failureStructure, failureScoped⟩ := forIn_scoped failuresRun equationScoped scopeValid₁
            (fun _ _ {_ _} run stateShape bound => failure_scoped run stateShape bound)
          have beforeBody := equationStructure.trans failureStructure
          have scopeValid₂ := beforeBody.scopeValid scopeValid
          obtain ⟨bodyStructure, bodyScoped⟩ := lower_scoped bodyRun failureScoped scopeValid₂
          have throughHead := beforeBody.trans bodyStructure
          have patternMeaning := (pattern_correct checked tags patternRun).2 initial input inputDecode
          have combinedBound : LocalsBounded before.roles.size (patternBindings ++ locals) :=
            localsBounded_append.mpr ⟨bindingsBound, localsBound⟩
          have headSelector := selectors ⟨0, by simp⟩
          cases matched : pat.bindings input with
          | some matchedBindings =>
              have selection : matchedBindings = bindings ∧ headBody = body := by
                simpa [selectArm, matched] using selected
              obtain ⟨bindingsEq, bodyEq⟩ := selection
              subst bindings
              subst body
              have active : (before.activation scope).denote initial = 1 := by
                simpa [armIndex, matched] using headSelector
              rcases patternMeaning with ⟨sourceBindings, sourceMatched, zero, bindingsDecode⟩ | ⟨absent, _⟩
              · have bindingsEq : sourceBindings = matchedBindings :=
                  Option.some.inj (sourceMatched.symm.trans matched)
                subst sourceBindings
                have equationExt := equations_complete equationsRun' layout valid
                  (scopeLayout.activation_bound scope) conditionsBound (Or.inr zero)
                obtain ⟨a, failureExt⟩ := failures_complete failuresRun' equationExt.layout equationScoped
                  equationExt.validAssignment scopeValid₁
                  (fun earlier member condition inside => equationExt.bound (previousBound earlier member condition inside))
                  (Or.inr previousFailed)
                have prefixExt := equationExt.trans failureExt
                have active₂ := (Extension.activation prefixExt beforeBody scopeLayout scopeValid).trans active
                have envDecode : DecodesEnvironment program.enums
                    (localsEnvironment (patternBindings ++ locals) initial) (matchedBindings ++ environment) := by
                  simpa only [localsEnvironment_append] using bindingsDecode.append decoded
                obtain ⟨b, bodyExt, _, _⟩ := bodyCompletes (pat, headBody) (by simp) bodyRun
                  prefixExt.layout failureScoped (Extension.validAssignment prefixExt) scopeValid₂
                  (combinedBound.mono prefixExt.increase)
                  (fun candidate equal => by cases equal; exact resultBound.mono prefixExt.increase)
                  active₂ (prefixExt.environment combinedBound envDecode)
                  (fun candidate equal => by
                    cases equal
                    rw [prefixExt.variables resultBound]
                    exact resultDecode) evaluated
                have full := prefixExt.trans bodyExt
                split at tailRun
                · obtain ⟨_, stateEq⟩ := pure_ok.mp tailRun
                  subst after
                  exact ⟨b, full⟩
                · obtain ⟨c, tailExt⟩ := lowerArms_inactive tailRun full.layout bodyScoped (Extension.validAssignment full)
                    (fun child member => throughHead.scopeValid (scopesValid child (by simp [member])))
                    (localsBound.mono full.increase) (scrutineeBound.mono full.increase) (resultBound.mono full.increase)
                    (by
                      intro earlier member condition inside
                      rcases List.mem_append.mp member with old | last
                      · exact full.bound (previousBound earlier old condition inside)
                      · obtain rfl := List.mem_singleton.mp last
                        exact full.bound (conditionsBound condition inside))
                    (by
                      intro child member
                      rw [Extension.activation full throughHead scopeLayout (scopesValid child (by simp [member]))]
                      obtain ⟨i, bound, rfl⟩ := List.mem_iff_getElem.mp member
                      have old := selectors ⟨i + 1, by simp; omega⟩
                      simpa [armIndex, matched] using old)
                  exact ⟨c, full.trans tailExt⟩
              · rw [matched] at absent
                cases absent
          | none =>
              have inactive : (before.activation scope).denote initial = 0 := by
                simpa [armIndex, matched] using headSelector
              have conditionFailed : ¬AllZero conditions initial := by
                rcases patternMeaning with ⟨_, present, _, _⟩ | ⟨_, failed⟩
                · rw [matched] at present
                  cases present
                · exact failed
              let start : InactiveContext rom calls scope before initial :=
                ⟨layout, scopeLayout, valid, scopeValid, inactive⟩
              obtain ⟨equationExt, equationContext⟩ := start.equations equationsRun' conditionsBound
              obtain ⟨a, failureExt, failureContext⟩ := equationContext.failures failuresRun
                (fun earlier member condition inside => equationExt.bound (previousBound earlier member condition inside))
              have prefixExt := equationExt.trans failureExt
              obtain ⟨b, bodyExt, _⟩ := lower_inactive bodyRun failureContext.layout failureContext.scopeLayout
                failureContext.valid failureContext.scopeValid (combinedBound.mono prefixExt.increase)
                (fun candidate equal => by cases equal; exact resultBound.mono prefixExt.increase) failureContext.inactive
              have full := prefixExt.trans bodyExt
              split at tailRun
              · rename_i irrefutable
                obtain ⟨_, present⟩ := pattern_matches checked tags patternRun irrefutable inputDecode
                rw [matched] at present
                cases present
              · have tailSelected : selectArm input arms = some (bindings, body) := by
                  simpa only [selectArm, matched] using selected
                obtain ⟨c, tailExt⟩ := ih (fun arm member => bodyCompletes arm (by simp [member])) tailRun
                  full.layout bodyScoped (Extension.validAssignment full)
                  (fun child member => throughHead.scopeValid (scopesValid child (by simp [member])))
                  (localsBound.mono full.increase) (scrutineeBound.mono full.increase) (resultBound.mono full.increase)
                  (by
                    intro earlier member condition inside
                    rcases List.mem_append.mp member with old | last
                    · exact full.bound (previousBound earlier old condition inside)
                    · obtain rfl := List.mem_singleton.mp last
                      exact full.bound (conditionsBound condition inside))
                  (full.environment localsBound decoded) (full.decoded_value scrutineeBound inputDecode)
                  (by rw [full.variables resultBound]; exact resultDecode) tailSelected
                  (by
                    intro i
                    rw [Extension.activation full throughHead scopeLayout (scopesValid scopes[i] (by simp))]
                    have old := selectors ⟨i.val + 1, by simpa using Nat.succ_lt_succ i.isLt⟩
                    simpa [armIndex, matched] using old)
                  (by
                    intro earlier member zero
                    rcases List.mem_append.mp member with old | last
                    · apply previousFailed earlier old
                      intro condition inside
                      rw [← full.polynomial (previousBound earlier old condition inside)]
                      exact zero condition inside
                    · obtain rfl := List.mem_singleton.mp last
                      apply conditionFailed
                      intro condition inside
                      rw [← full.polynomial (conditionsBound condition inside)]
                      exact zero condition inside)
                exact ⟨c, full.trans tailExt⟩

end Aiur.Optimized.Compiler
