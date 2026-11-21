import Aiur.Generic.PatternTreeCompleteness

namespace Aiur.Generic.PatternLowering

variable {calls : CallRelation F}

open SourceSemantics

variable [DecidableEq F]

theorem PlanTree.success_iff (tree : PlanTree F) (input : String)
    (safe : (input :: tree.temps).Nodup)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (heap : Heap F) (value : SourceValue F) (locals : Environment F Nat)
    (found : locals.find? (·.1 == input) = some (input, value)) :
    matchPatternWith constant depth [] heap tree.erase value = .ok (some bindings) ↔
      ∃ final, Attempt heap (tree.toPlan input).steps locals true final ∧
        resolveBindings (tree.toPlan input).bindings final = some bindings := by
  constructor
  · intro matched
    obtain ⟨final, attempted⟩ := tree.attempt_complete input safe constant depth heap value locals found matched
    obtain ⟨bs, matched', produced⟩ := tree.attempt_sound input safe constant depth heap value locals found attempted
    have same := Option.some.inj (Except.ok.inj (matched'.symm.trans matched))
    subst bs
    exact ⟨final, attempted, produced⟩
  · rintro ⟨final, attempted, produced⟩
    obtain ⟨bs, matched, produced'⟩ := tree.attempt_sound input safe constant depth heap value locals found attempted
    have same := Option.some.inj (produced'.symm.trans produced)
    subst bs
    exact matched

theorem PlanTree.failure_iff (tree : PlanTree F) (input : String)
    (safe : (input :: tree.temps).Nodup)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (heap : Heap F) (value : SourceValue F) (locals : Environment F Nat)
    (found : locals.find? (·.1 == input) = some (input, value)) :
    matchPatternWith constant depth [] heap tree.erase value = .ok none ↔
      ∃ final, Attempt heap (tree.toPlan input).steps locals false final := by
  constructor
  · exact tree.attempt_complete input safe constant depth heap value locals found
  · rintro ⟨final, attempted⟩
    exact tree.attempt_sound input safe constant depth heap value locals found attempted

theorem PlanTree.untouched (tree : PlanTree F) {locals final : Environment F Nat}
    (attempted : Attempt heap (tree.toPlan input).steps locals accepted final)
    (fresh : ∀ n ∈ names, n ∉ tree.temps) : Engine.EnvAgrees names final locals := by
  intro n hn
  apply attempted.unchanged
  rw [tree.written]
  exact fresh n hn

variable [Field F] {world : Engine.World F}

/-- A generated let plan performs the native read-only match and then runs the
body in precisely the source binding scope. All temporary bindings are hidden. -/
theorem PlanTree.let_iff (tree : PlanTree F) (input : String)
    (safe : (input :: tree.temps).Nodup)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (heap : Heap F) (value : SourceValue F) (locals : Environment F Nat)
    (found : locals.find? (·.1 == input) = some (input, value))
    (body : Aiur.Expr F) (fresh : ∀ n ∈ exprNames body, n ∉ tree.temps) :
    OpenCore.EvalExpr world calls locals (letSteps (tree.toPlan input).steps
      (bindUsers (tree.toPlan input).bindings body)) heap result after ↔
      ∃ bindings, matchPatternWith constant depth [] heap tree.erase value = .ok (some bindings) ∧
        OpenCore.EvalExpr world calls (bindings ++ locals) body heap result after := by
  rw [letSteps_iff]
  constructor
  · rintro ⟨final, attempted, bodyEval⟩
    obtain ⟨bindings, produced, evaluated⟩ := bindUsers_resolved_iff.mp bodyEval
    exact ⟨bindings, (tree.success_iff input safe constant depth heap value locals found).mpr
      ⟨final, attempted, produced⟩,
      evaluated.changeLocals _ ((tree.untouched attempted fresh).prepend bindings)⟩
  · rintro ⟨bindings, matched, evaluated⟩
    obtain ⟨final, attempted, produced⟩ := (tree.success_iff input safe constant depth heap value locals found).mp matched
    exact ⟨final, attempted, bindUsers_resolved_iff.mpr ⟨bindings, produced,
      evaluated.changeLocals _ ((tree.untouched attempted fresh).symm.prepend bindings)⟩⟩

/-- The failure continuation runs with the unchanged caller scope. Only the
successful continuation receives user bindings from this pattern. -/
theorem PlanTree.match_iff (tree : PlanTree F) (input : String)
    (safe : (input :: tree.temps).Nodup)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (heap : Heap F) (value : SourceValue F) (locals : Environment F Nat)
    (found : locals.find? (·.1 == input) = some (input, value))
    (body : Aiur.Expr F) (failure : Option (Aiur.Expr F))
    (freshBody : ∀ n ∈ exprNames body, n ∉ tree.temps)
    (freshFailure : ∀ fallback, failure = some fallback → ∀ n ∈ exprNames fallback, n ∉ tree.temps) :
    OpenCore.EvalExpr world calls locals (matchSteps (tree.toPlan input).steps
      (bindUsers (tree.toPlan input).bindings body) failure) heap result after ↔
      (∃ bindings, matchPatternWith constant depth [] heap tree.erase value = .ok (some bindings) ∧
        OpenCore.EvalExpr world calls (bindings ++ locals) body heap result after) ∨
      (matchPatternWith constant depth [] heap tree.erase value = .ok none ∧
        ∃ fallback, failure = some fallback ∧ OpenCore.EvalExpr world calls locals fallback heap result after) := by
  rw [matchSteps_iff]
  constructor
  · rintro ⟨accepted, final, attempted, continued⟩
    cases accepted with
    | true =>
        obtain ⟨bindings, produced, evaluated⟩ := bindUsers_resolved_iff.mp continued
        exact Or.inl ⟨bindings, (tree.success_iff input safe constant depth heap value locals found).mpr
          ⟨final, attempted, produced⟩,
          evaluated.changeLocals _ ((tree.untouched attempted freshBody).prepend bindings)⟩
    | false =>
        obtain ⟨fallback, present, evaluated⟩ := continued
        exact Or.inr ⟨(tree.failure_iff input safe constant depth heap value locals found).mpr ⟨final, attempted⟩,
          fallback, present, evaluated.changeLocals _ (tree.untouched attempted (freshFailure fallback present))⟩
  · rintro (⟨bindings, matched, evaluated⟩ | ⟨matched, fallback, present, evaluated⟩)
    · obtain ⟨final, attempted, produced⟩ := (tree.success_iff input safe constant depth heap value locals found).mp matched
      refine ⟨true, final, attempted, ?_⟩
      exact bindUsers_resolved_iff.mpr ⟨bindings, produced,
        evaluated.changeLocals _ ((tree.untouched attempted freshBody).symm.prepend bindings)⟩
    · obtain ⟨final, attempted⟩ := (tree.failure_iff input safe constant depth heap value locals found).mp matched
      exact ⟨false, final, attempted, fallback, present,
        evaluated.changeLocals _ (tree.untouched attempted (freshFailure fallback present)).symm⟩

end Aiur.Generic.PatternLowering
