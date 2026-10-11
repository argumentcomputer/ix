import Ix.CompileCert.ExpressionCache
import Ix.CompileCert.ExpressionFrame

/-! Cache correctness for actual compiler runs, including error states.
The constructor transitions and the chosen source/target interpretation remain
explicit obligations. Structural induction composes those local transitions
with exact memo lookup/insertion; it does not assume a correct whole run. -/

namespace Ix.CompileCert.ExpressionCacheRun

open Ix.CompileM Ix.CompileCert.ExpressionCache Ix.CompileCert.HeadWriterFrame

abbrev Value := Ixon.Expr × UInt64
abbrev Meaning := BlockState → Ix.Expr → Value → Prop

def Valid (meaning : Meaning) (state : BlockState) : Prop :=
  Sound (meaning state) state.exprCache

theorem valid_empty (meaning : Meaning) (state : BlockState) :
    Valid meaning { state with exprCache := {} } := sound_empty _

/-- Includes the cache remaining after an error, as well as successful results. -/
def CorrectResult (meaning : Meaning) (expr : Ix.Expr)
    (result : Except CompileError Value × BlockState) : Prop :=
  Valid meaning result.2 ∧ ∀ value, result.1 = .ok value → meaning result.2 expr value

/-- Interpreting an output reads tables and source/target bindings, not the
compiler's memo. This premise will be discharged by that interpretation. -/
def CacheBlind (meaning : Meaning) : Prop :=
  ∀ state cache, meaning { state with exprCache := cache } = meaning state

theorem cached_run_correct (meaning : Meaning) (blind : CacheBlind meaning)
    (compile : Ix.Expr → CompileM Value) (expr : Ix.Expr)
    (context : CompileEnv × BlockEnv) (before : BlockState)
    (valid : Valid meaning before)
    (step : before.exprCache.get? expr = none →
      CorrectResult meaning expr (rawRun (compile expr) context before)) :
    CorrectResult meaning expr (rawRun (ExpressionRuntime.cached compile expr) context before) := by
  simp only [ExpressionRuntime.cached, rawRun_bind, rawRun_get]
  cases found : before.exprCache.get? expr with
  | some value =>
    simp only [rawRun_pure]
    refine ⟨valid, ?_⟩
    intro result equal
    cases Except.ok.inj equal
    exact valid expr value found
  | none =>
    simp only [rawRun_bind]
    have checked := step found
    cases ran : rawRun (compile expr) context before with
    | mk outcome after =>
      rw [ran] at checked
      cases outcome with
      | error error =>
        exact checked
      | ok value =>
        rcases value with ⟨value, root⟩
        simp only [rawRun_modify, rawRun_pure]
        obtain ⟨keeps, correct⟩ := checked
        have valueCorrect := correct (value, root) rfl
        have updated := ExpressionCache.Sound.insert keeps expr (value, root) valueCorrect
        unfold CorrectResult Valid
        rw [blind]
        exact ⟨updated, by intro result equal; cases Except.ok.inj equal; exact valueCorrect⟩

/-- The same rule for the actual direct compiler. The uncached constructor
step, including its recursively compiled children, remains to be justified. -/
theorem partial_run_correct (meaning : Meaning) (blind : CacheBlind meaning)
    (expr : Ix.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (valid : Valid meaning before)
    (step : before.exprCache.get? expr = none → CorrectResult meaning expr
      (rawRun (compileExprTotalStep compileExprPartial expr) context before)) :
    CorrectResult meaning expr (rawRun (compileExprPartial expr) context before) := by
  rw [ExpressionRuntime.partial_unfold]
  exact cached_run_correct meaning blind (compileExprTotalStep compileExprPartial)
    expr context before valid step

/-- Structural induction closes the recursive cache obligation once each actual
constructor transition is justified from strictly smaller source expressions.
The remaining premise is local to a cache miss; it does not assume correctness
of the whole expression compiler. Other established runtime frame laws remain
available when proving the constructor transitions. -/
theorem partial_run_correct_of_step
    (meaning : (CompileEnv × BlockEnv) → Meaning)
    (blind : ∀ context, CacheBlind (meaning context))
    (step : ∀ expr,
      (∀ child, exprCompileDepth child < exprCompileDepth expr →
        ∀ context before, Valid (meaning context) before →
          CorrectResult (meaning context) child
            (rawRun (compileExprPartial child) context before)) →
      ∀ context before, Valid (meaning context) before →
        before.exprCache.get? expr = none →
        CorrectResult (meaning context) expr
          (rawRun (compileExprTotalStep compileExprPartial expr) context before)) :
    ∀ expr context before, Valid (meaning context) before →
      CorrectResult (meaning context) expr
        (rawRun (compileExprPartial expr) context before) := by
  intro expr
  induction expr using (measure exprCompileDepth).wf.induction with
  | h expr ih =>
    intro context before valid
    exact partial_run_correct (meaning context) (blind context) expr context before
      valid (step expr ih context before valid)

/-- The same induction rule for the reference entry point, using its exact
checked equality with the direct compiler. -/
theorem total_run_correct_of_step
    (meaning : (CompileEnv × BlockEnv) → Meaning)
    (blind : ∀ context, CacheBlind (meaning context))
    (step : ∀ expr,
      (∀ child, exprCompileDepth child < exprCompileDepth expr →
        ∀ context before, Valid (meaning context) before →
          CorrectResult (meaning context) child
            (rawRun (compileExprPartial child) context before)) →
      ∀ context before, Valid (meaning context) before →
        before.exprCache.get? expr = none →
        CorrectResult (meaning context) expr
          (rawRun (compileExprTotalStep compileExprPartial expr) context before))
    (expr : Ix.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (valid : Valid (meaning context) before) :
    CorrectResult (meaning context) expr (rawRun (compileExprTotal expr) context before) := by
  rw [compileExprTotal_eq_partial]
  exact partial_run_correct_of_step meaning blind step expr context before valid

end Ix.CompileCert.ExpressionCacheRun
