import Aiur.Generic.ControlEval

namespace Aiur.Generic.SourceSemantics

set_option linter.unusedSimpArgs false

namespace FlowEvaluation

theorem pure_ok {value : A} {before after : Heap F} :
    (pure value : FlowEvaluation F A).run before = .ok (outcome, after) ↔
      outcome = .ok value ∧ after = before := by
  change Except.ok (.ok value, before) = Except.ok (outcome, after) ↔ _
  simp [eq_comm]

theorem bind_ok {first : FlowEvaluation F A} {next : A → FlowEvaluation F B}
    {before after : Heap F} :
    (first >>= next).run before = .ok (outcome, after) ↔
      (∃ value middle, first.run before = .ok (.ok value, middle) ∧
        (next value).run middle = .ok (outcome, after)) ∨
      (∃ exit, first.run before = .ok (.error exit, after) ∧ outcome = .error exit) := by
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.run, StateT.bind,
    ExceptT.bindCont, pure, StateT.pure, Except.pure, Except.bind]
  cases h : first before with
  | error e => simp [h, Except.bind]
  | ok pair =>
      rcases pair with ⟨result, heap⟩
      cases result with
      | error exit => cases exit; simp [h, pure, StateT.pure, Except.pure, Prod.mk.injEq, eq_comm, and_comm]
      | ok value => simp [h, Prod.mk.injEq]

theorem lift_ok {action : Except EvalError A} {before after : Heap F} :
    (liftM action : FlowEvaluation F A).run before = .ok (outcome, after) ↔
      ∃ value, action = .ok value ∧ outcome = .ok value ∧ after = before := by
  cases action with
  | error e =>
      change (Except.error e : Except EvalError _) = .ok (outcome, after) ↔ _
      simp
  | ok value =>
      change Except.ok (.ok value, before) = Except.ok (outcome, after) ↔ _
      simp [eq_comm]

theorem throw_ok {exit : ExitTarget × SourceValue F} {before after : Heap F} :
    (throw exit : FlowEvaluation F A).run before = .ok (outcome, after) ↔
      outcome = .error exit ∧ after = before := by
  change Except.ok (.error exit, before) = Except.ok (outcome, after) ↔ _
  simp [eq_comm]

@[simp] theorem get_apply (heap : Heap F) :
    (get : FlowEvaluation F (Heap F)).run heap = .ok (.ok heap, heap) := rfl

@[simp] theorem set_apply (next heap : Heap F) :
    (set next : FlowEvaluation F Unit).run heap = .ok (.ok (), next) := rfl

@[simp] theorem error_apply (error : EvalError) (heap : Heap F) :
    (flowError error : FlowEvaluation F A).run heap = .error error := rfl

theorem liftEvaluation_apply (action : Evaluation F A) (heap : Heap F) :
    (liftM action : FlowEvaluation F A).run heap =
      (action heap).map (fun (value, after) => (.ok value, after)) := by
  rfl

theorem liftEvaluation_ok {action : Evaluation F A} {before after : Heap F} :
    (liftM action : FlowEvaluation F A).run before = .ok (outcome, after) ↔
      ∃ value, action before = .ok (value, after) ∧ outcome = .ok value := by
  rw [liftEvaluation_apply]
  cases action before with
  | error => simp [Except.map]
  | ok pair => cases pair; simp [Except.map, eq_comm, and_comm]

end FlowEvaluation

theorem catchExit_ok {body : FlowEvaluation F (SourceValue F)} {before after : Heap F} :
    (catchExit target body).run before = .ok (outcome, after) ↔
      ∃ input, body.run before = .ok (input, after) ∧ Outcome.catch target input = outcome := by
  change (body.run >>= fun input => pure (Outcome.catch target input)) before = .ok (outcome, after) ↔ _
  simp only [Evaluation.bind_ok, Evaluation.pure_ok]
  constructor
  · rintro ⟨input, middle, run, result, rfl⟩; exact ⟨input, run, result⟩
  · rintro ⟨input, run, result⟩; exact ⟨input, after, run, result, rfl⟩

theorem finishFunction_ok {body : FlowEvaluation F (SourceValue F)} {before after : Heap F} :
    finishFunction body before = .ok (value, after) ↔
      body.run before = .ok (.ok value, after) ∨
      body.run before = .ok (.error (.function, value), after) := by
  cases h : body before with
  | error error => simp [finishFunction, catchExit, Outcome.catch, ExceptT.run, ExceptT.mk,
      bind, StateT.bind, Except.bind, h]
  | ok pair =>
      rcases pair with ⟨result, heap⟩
      cases result with
      | ok v => simp [finishFunction, catchExit, Outcome.catch, ExceptT.run, ExceptT.mk,
          bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, h, Prod.mk.injEq]
      | error exit =>
          rcases exit with ⟨target, v⟩
          cases target <;> simp [finishFunction, catchExit, Outcome.catch, ExceptT.run, ExceptT.mk,
            bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, h,
            throw, throwThe, MonadExceptOf.throw, StateT.lift, Prod.mk.injEq]

theorem finishExpression_ok {body : FlowEvaluation F (SourceValue F)} {before after : Heap F} :
    finishExpression body before = .ok (value, after) ↔
      body.run before = .ok (.ok value, after) := by
  cases h : body before with
  | error error => simp [finishExpression, ExceptT.run, bind, StateT.bind, Except.bind, h]
  | ok pair =>
      rcases pair with ⟨result, heap⟩
      cases result <;> simp [finishExpression, ExceptT.run, bind, StateT.bind,
        Except.bind, pure, StateT.pure, Except.pure, h,
        throw, throwThe, MonadExceptOf.throw, StateT.lift, Prod.mk.injEq]

def Outcome.Evaluates [Field F] [DecidableEq F] (world : World F) (types : Types)
    (locals : Environment F Nat) (expr : Expr F) (before : Heap F) : Outcome F → Heap F → Prop
  | .ok value, after => EvalExpr world types locals expr before value after
  | .error (target, value), after => EvalExit world types locals expr before target value after

def ArgsOutcome [Field F] [DecidableEq F] (world : World F) (types : Types)
    (locals : Environment F Nat) (exprs : List (Expr F)) (before : Heap F) :
    Except (ExitTarget × SourceValue F) (List (SourceValue F)) → Heap F → Prop
  | .ok values, after => EvalArgs world types locals exprs before values after
  | .error (target, value), after => EvalArgsExit world types locals exprs before target value after

end Aiur.Generic.SourceSemantics
