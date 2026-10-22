import Aiur.Generic.PatternLowering
import Aiur.Generic.OpenCore

namespace Aiur.Generic.Engine

/-- An overapproximation of the names an expression may inspect is enough for
environment independence. Including bound names keeps this certificate simple. -/
def EnvAgrees (names : List String) (left right : Environment F Nat) : Prop :=
  ∀ name ∈ names, left.find? (·.1 == name) = right.find? (·.1 == name)

variable {F : Type} {names fewer : List String} {left right : Environment F Nat}

theorem EnvAgrees.mono (h : EnvAgrees names left right)
    (subset : ∀ n ∈ fewer, n ∈ names) : EnvAgrees fewer left right :=
  fun n hn => h n (subset n hn)

theorem EnvAgrees.prepend (h : EnvAgrees names left right) (bindings : Environment F Nat) :
    EnvAgrees names (bindings ++ left) (bindings ++ right) := by
  intro n hn
  simp only [List.find?_append, h n hn]

theorem EnvAgrees.symm (h : EnvAgrees names left right) : EnvAgrees names right left :=
  fun n hn => (h n hn).symm

private theorem selected_member [DecidableEq F] {arms : List (Aiur.Pattern F × Aiur.Expr F)}
    (selected : Aiur.selectArm input arms = some (bindings, body)) :
    ∃ pat, (pat, body) ∈ arms := by
  induction arms with
  | nil => simp [Aiur.selectArm] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pat, expr⟩
      cases h : pat.bindings input with
      | none =>
          obtain ⟨p, hp⟩ := ih (by simpa [Aiur.selectArm, h] using selected)
          exact ⟨p, by simp [hp]⟩
      | some bs =>
          have same : expr = body := by
            have pair : bs = bindings ∧ expr = body := by
              simpa only [Aiur.selectArm, h, Option.some.injEq, Prod.mk.injEq] using selected
            exact pair.2
          subst expr
          exact ⟨pat, by simp⟩

end Aiur.Generic.Engine

namespace Aiur.Generic.OpenCore
open Engine
variable [Field F] [DecidableEq F] {world : Engine.World F} {calls : CallRelation F}

/-- Compiler temporaries cannot affect an expression whose names they do not
shadow. Calls start in their own environments, and the heap is unchanged by
this change of local bindings. -/
theorem EvalExpr.changeLocals (ev : EvalExpr world calls locals expr before value after) :
    ∀ other, EnvAgrees (PatternLowering.exprNames expr) locals other →
      EvalExpr world calls other expr before value after := by
  induction ev using EvalExpr.rec
    (motive_2 := fun ls es b vs h _ => ∀ other,
      EnvAgrees (es.flatMap PatternLowering.exprNames) ls other → EvalArgs world calls other es b vs h) with
  | literal => intro _ _; exact .literal
  | var lookup =>
      intro other agree
      exact .var (by rw [← agree _ (by simp [PatternLowering.exprNames])]; exact lookup)
  | tuple _ ih => intro other agree; exact .tuple (ih other (by simpa only [PatternLowering.exprNames] using agree))
  | construct _ ih => intro other agree; exact .construct (ih other (by simpa only [PatternLowering.exprNames] using agree))
  | project _ projected ih => intro other agree; exact .project (ih other (by simpa only [PatternLowering.exprNames] using agree)) projected
  | letValue _ matched _ ih1 ih2 =>
      intro other agree
      apply EvalExpr.letValue (ih1 other (agree.mono ?_)) matched
      · apply ih2 _ ((agree.mono ?_).prepend _)
        intro n hn
        simp [PatternLowering.exprNames, hn]
      · intro n hn
        simp [PatternLowering.exprNames, hn]
  | store _ ih => intro other agree; exact .store (ih other (by simpa only [PatternLowering.exprNames] using agree))
  | load _ loaded ih => intro other agree; exact .load (ih other (by simpa only [PatternLowering.exprNames] using agree)) loaded
  | hint _ typed ih => intro other agree; exact .hint (ih other (by simpa only [PatternLowering.exprNames] using agree)) typed
  | neg _ op ih => intro other agree; exact .neg (ih other (by simpa only [PatternLowering.exprNames] using agree)) op
  | assertEq _ _ op ih1 ih2 =>
      intro other agree
      exact .assertEq (ih1 other (agree.mono (by intros; simp [PatternLowering.exprNames, *])))
        (ih2 other (agree.mono (by intros; simp [PatternLowering.exprNames, *]))) op
  | binary _ _ op ih1 ih2 =>
      intro other agree
      exact .binary (ih1 other (agree.mono (by intros; simp [PatternLowering.exprNames, *])))
        (ih2 other (agree.mono (by intros; simp [PatternLowering.exprNames, *]))) op
  | call _ callee ih => intro other agree; exact .call (ih other (by simpa only [PatternLowering.exprNames] using agree)) callee
  | matchValue _ selected _ ih1 ih2 =>
      intro other agree
      apply EvalExpr.matchValue
        (ih1 other (agree.mono (by intros; simp [PatternLowering.exprNames, *]))) selected
      apply ih2 _ ((agree.mono ?_).prepend _)
      intro n hn
      obtain ⟨pat, member⟩ := selected_member selected
      simp only [PatternLowering.exprNames, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨(pat, _), member, by simp [hn]⟩
  | nil => exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i other agree
      exact .cons (ih1 other (agree.mono (by intros; simp [*])))
        (ih2 other (agree.mono (by intros; simp [*])))

theorem evalExpr_env_iff (agree : EnvAgrees (PatternLowering.exprNames expr) locals other) :
    EvalExpr world calls locals expr before value after ↔ EvalExpr world calls other expr before value after :=
  ⟨fun h => h.changeLocals other agree, fun h => h.changeLocals locals agree.symm⟩

end Aiur.Generic.OpenCore
