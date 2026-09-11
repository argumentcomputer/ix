import Ix.Compiler.X86.ScalarSourceSyntax

namespace Ix.Compiler.X86.Scalar.Source
open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR0.Recursion
open Ix.Compiler.IxIR0.NatArithmetic (Represents)

/-- Every expression accepted by the source shape checker implements the
unbounded scalar semantics in the existing IxIR₀ evaluator. -/
theorem raw_evaluates {checked : Checked} {ctx : IxIR0.Ctx} {primitives : Primitives} {entries : Array Address}
    (matched : ProgramMatches ctx primitives entries checked.program)
    {expr : Expr} {values : Array Nat} {number : Nat}
    (evaluated : NatEvaluates checked.program.functions expr values number) :
    ∀ current, expr.valid checked.program.functions current values.size = true →
      ∀ environment bindings, BindingsRepresent primitives.arithmetic environment bindings values →
      ∃ result, IxIR0.Recursion.Evaluates ctx environment (expression primitives entries bindings expr) result ∧
        Represents primitives.arithmetic result number := by
  induction evaluated with
  | atom found =>
      intro current valid environment bindings represented
      exact represented.atom found
  | add leftValue rightValue =>
      intro current valid environment bindings represented
      obtain ⟨left, leftRun, leftRep⟩ := represented.atom leftValue
      obtain ⟨right, rightRun, rightRep⟩ := represented.atom rightValue
      obtain ⟨closure, result, first, second, resultRep⟩ := IxIR0.NatArithmetic.body_applies matched.matched.arithmetic leftRep rightRep
      exact ⟨result, evaluatesApp
        (evaluatesApp (evaluatesDef matched.matched.addition (evaluatesLam _ _ _ _)) leftRun first)
        rightRun second, resultRep⟩
  | sub leftValue rightValue =>
      intro current valid environment bindings represented
      obtain ⟨left, leftRun, leftRep⟩ := represented.atom leftValue
      obtain ⟨right, rightRun, rightRep⟩ := represented.atom rightValue
      obtain ⟨closure, result, first, second, resultRep⟩ := IxIR0.NatArithmetic.sub_applies
        matched.matched.arithmetic matched.matched.predecessor leftRep rightRep
      exact ⟨result, evaluatesApp
        (evaluatesApp (evaluatesDef matched.matched.subtraction (evaluatesLam _ _ _ _)) leftRun first)
        rightRun second, resultRep⟩
  | letE first rest ihFirst ihRest =>
      intro current valid environment bindings represented
      simp only [Expr.valid, Bool.and_eq_true] at valid
      obtain ⟨bound, boundRun, boundRep⟩ := ihFirst current valid.1.2 environment bindings represented
      obtain ⟨result, resultRun, resultRep⟩ := ihRest current (by simpa using valid.2) _ _ (represented.push boundRep)
      exact ⟨result, evaluatesLet boundRun resultRun, resultRep⟩
  | @zero values scrutinee zero successor result scrutineeValue taken ih =>
      intro current valid environment bindings represented
      simp only [Expr.valid, Bool.and_eq_true] at valid
      obtain ⟨major, majorRun, majorRep⟩ := represented.atom scrutineeValue
      obtain ⟨result, takenRun, resultRep⟩ := ih current valid.1.2 _ _ (represented.lift (.lit (.nat 0)))
      have selected := IxIR0.NatArithmetic.case_zero
        (successor := .clos .many environment (expression primitives entries (lift bindings) successor))
        matched.matched.caseRecursor majorRep (appliesClosure (u := .many) takenRun)
      exact ⟨result, evaluatesApp
        (evaluatesApp (evaluatesApp (evaluatesDef matched.matched.caseAlias (evaluatesRecursor matched.matched.caseRecursor))
          (evaluatesLam _ _ _ _) (IxIR0.NatArithmetic.appliesRecursorFirst _ _ _))
          (evaluatesLam _ _ _ _) (IxIR0.NatArithmetic.appliesRecursorSecond _ _ _ _))
        majorRun selected, resultRep⟩
  | @successor values scrutinee zero successor value result scrutineeValue positive taken ih =>
      intro current valid environment bindings represented
      simp only [Expr.valid, Bool.and_eq_true] at valid
      obtain ⟨major, majorRun, majorRep⟩ := represented.atom scrutineeValue
      obtain ⟨predecessor, view, predecessorRep⟩ := majorRep.successor_view positive
      obtain ⟨result, takenRun, resultRep⟩ := ih current valid.2 _ _ (represented.lift predecessor)
      have selected := IxIR0.NatArithmetic.case_successor
        (zero := .clos .many environment (expression primitives entries (lift bindings) zero))
        matched.matched.caseRecursor view (appliesClosure (u := .many) takenRun)
      exact ⟨result, evaluatesApp
        (evaluatesApp (evaluatesApp (evaluatesDef matched.matched.caseAlias (evaluatesRecursor matched.matched.caseRecursor))
          (evaluatesLam _ _ _ _) (IxIR0.NatArithmetic.appliesRecursorFirst _ _ _))
          (evaluatesLam _ _ _ _) (IxIR0.NatArithmetic.appliesRecursorSecond _ _ _ _))
        majorRun selected, resultRep⟩
  | @call values supplied function arguments callee number found argumentsAt arity evaluated ih =>
      intro current valid environment bindings represented
      simp only [Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
      obtain ⟨address, entryFound, declaration⟩ := matched.functions function callee found
      have bodyValid := (checked.function_valid found).2
      rcases array_le_two arguments valid.1.1.2 with rfl | ⟨first, rfl⟩ | ⟨first, second, rfl⟩
      · simp [Array.mapM_eq_mapM_toList] at argumentsAt
        subst supplied
        have parametersZero : callee.parameters = 0 := arity.symm
        obtain ⟨result, bodyRun, resultRep⟩ := ih function (by simpa [parametersZero] using bodyValid) [] _ (bindings_empty _)
        have declared : ctx.env address = some (.defn .shared (expression primitives entries (parameters 0) callee.body)) := by
          simpa only [functionBody, parametersZero, lambda] using declaration
        refine ⟨result, ?_, resultRep⟩
        simpa [expression, entryFound] using evaluatesDef (env := environment) declared bodyRun
      · cases firstValue : first.natEval values with
        | none => simp [Array.mapM_eq_mapM_toList, firstValue] at argumentsAt
        | some a =>
            simp [Array.mapM_eq_mapM_toList, firstValue] at argumentsAt
            subst supplied
            have parametersOne : callee.parameters = 1 := arity.symm
            obtain ⟨left, leftRun, leftRep⟩ := represented.atom firstValue
            obtain ⟨result, bodyRun, resultRep⟩ := ih function (by simpa [parametersOne] using bodyValid) _ _ (bindings_one leftRep)
            have declared : ctx.env address = some (.defn .shared (.lam .many (expression primitives entries (parameters 1) callee.body))) := by
              simpa only [functionBody, parametersOne, lambda] using declaration
            refine ⟨result, ?_, resultRep⟩
            simpa [expression, entryFound] using evaluatesApp
              (evaluatesDef declared (evaluatesLam _ _ _ _)) leftRun (appliesClosure bodyRun)
      · cases firstValue : first.natEval values with
        | none => simp [Array.mapM_eq_mapM_toList, firstValue] at argumentsAt
        | some a =>
            cases secondValue : second.natEval values with
            | none => simp [Array.mapM_eq_mapM_toList, firstValue, secondValue] at argumentsAt
            | some b =>
                simp [Array.mapM_eq_mapM_toList, firstValue, secondValue] at argumentsAt
                subst supplied
                have parametersTwo : callee.parameters = 2 := arity.symm
                obtain ⟨left, leftRun, leftRep⟩ := represented.atom firstValue
                obtain ⟨right, rightRun, rightRep⟩ := represented.atom secondValue
                obtain ⟨result, bodyRun, resultRep⟩ := ih function (by simpa [parametersTwo] using bodyValid) _ _ (bindings_two leftRep rightRep)
                have declared : ctx.env address = some (.defn .shared (.lam .many (.lam .many
                    (expression primitives entries (parameters 2) callee.body)))) := by
                  simpa only [functionBody, parametersTwo, lambda] using declaration
                refine ⟨result, ?_, resultRep⟩
                simpa [expression, entryFound] using evaluatesApp
                  (evaluatesApp (evaluatesDef declared (evaluatesLam _ _ _ _)) leftRun (appliesClosure (evaluatesLam _ _ _ _)))
                  rightRun (appliesClosure bodyRun)

end Ix.Compiler.X86.Scalar.Source
