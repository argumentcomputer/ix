import Aiur.Generic.TraceEval
import Aiur.Generic.ControlEvalSpec

namespace Aiur.Generic.Traced
open SourceSemantics

def Agrees (traced : Eval F A) (plain : Evaluation F A) : Prop :=
  ∀ heap events, (traced heap events).1 = plain heap

theorem agrees_pure (value : A) : Agrees (pure value : Eval F A) (pure value) := by
  intro heap events; rfl

theorem agrees_bind {first : Eval F A} {first' : Evaluation F A}
    {next : A → Eval F B} {next' : A → Evaluation F B}
    (head : Agrees first first') (tail : ∀ value, Agrees (next value) (next' value)) :
    Agrees (first >>= next) (first' >>= next') := by
  intro heap events
  have h := head heap events
  cases run : first heap events with
  | mk outcome trace =>
      rw [run] at h
      cases outcome with
      | error err =>
          simp only [bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
            ExceptT.run, pure, StateT.pure, Except.pure, Except.bind, run, ← h]
      | ok pair =>
          rcases pair with ⟨value, middle⟩
          simpa only [bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
            ExceptT.run, pure, StateT.pure, Except.pure, Except.bind, run, ← h] using tail value middle trace

theorem agrees_lift (action : Except EvalError A) :
    Agrees (liftM action : Eval F A) (liftM action) := by
  intro heap events; cases action <;> rfl

theorem agrees_get : Agrees (get : Eval F (Heap F)) get := by intro heap events; rfl
theorem agrees_set (heap : Heap F) : Agrees (set heap : Eval F Unit) (set heap) := by intro heap events; rfl
theorem agrees_throw (err : EvalError) : Agrees (throw err : Eval F A) (throw err) := by intro heap events; rfl

abbrev FlowAgrees (traced : Flow F A) (plain : FlowEvaluation F A) := Agrees traced.run plain.run

theorem flow_pure (value : A) : FlowAgrees (pure value : Flow F A) (pure value) := agrees_pure _
theorem flow_throw (exit : ExitTarget × SourceValue F) :
    FlowAgrees (throw exit : Flow F A) (throw exit) := agrees_pure _

theorem flow_bind {first : Flow F A} {first' : FlowEvaluation F A}
    {next : A → Flow F B} {next' : A → FlowEvaluation F B}
    (head : FlowAgrees first first') (tail : ∀ value, FlowAgrees (next value) (next' value)) :
    FlowAgrees (first >>= next) (first' >>= next') := by
  apply agrees_bind head
  intro outcome
  cases outcome with
  | error exit => exact agrees_pure _
  | ok value => exact tail value

theorem flow_lift_eval {action : Eval F A} {plain : Evaluation F A} (h : Agrees action plain) :
    FlowAgrees (liftM action : Flow F A) (liftM plain) :=
  agrees_bind h (fun value => agrees_pure _)

theorem flow_lift (action : Except EvalError A) :
    FlowAgrees (liftM action : Flow F A) (liftM action) :=
  flow_lift_eval (agrees_lift action)

theorem flow_error (err : EvalError) : FlowAgrees (error err : Flow F A) (flowError err) := agrees_throw _
theorem flow_get : FlowAgrees (get : Flow F (Heap F)) get := flow_lift_eval agrees_get
theorem flow_set (heap : Heap F) : FlowAgrees (set heap : Flow F Unit) (set heap) := flow_lift_eval (agrees_set heap)
theorem flow_emit (event : TraceEvent F) : FlowAgrees (emit event) (pure ()) := by intro heap events; rfl

theorem flow_catch {body : Flow F (SourceValue F)} {plain : FlowEvaluation F (SourceValue F)}
    (h : FlowAgrees body plain) : FlowAgrees (catchExit target body) (SourceSemantics.catchExit target plain) :=
  agrees_bind h (fun value => agrees_pure _)

theorem agrees_finish {body : Flow F (SourceValue F)} {plain : FlowEvaluation F (SourceValue F)}
    (h : FlowAgrees body plain) : Agrees (finishFunction body) (SourceSemantics.finishFunction plain) := by
  apply agrees_bind (flow_catch h)
  intro outcome
  cases outcome with
  | ok value => exact agrees_pure _
  | error exit => exact agrees_throw _

theorem flow_mapM {traced : A → Flow F B} {plain : A → FlowEvaluation F B}
    (same : ∀ value, FlowAgrees (traced value) (plain value)) (values : List A) :
    FlowAgrees (values.mapM traced) (values.mapM plain) := by
  induction values with
  | nil => exact flow_pure _
  | cons value values ih =>
      simp only [List.mapM_cons]
      exact flow_bind (same value) (fun v => flow_bind ih (fun vs => flow_pure _))

theorem emit_then {traced : Flow F A} {plain : FlowEvaluation F A}
    (event : TraceEvent F) (h : FlowAgrees traced plain) :
    FlowAgrees (emit event >>= fun _ => traced) plain := by
  simpa only [pure_bind] using flow_bind (flow_emit event) (fun _ => h)

/-- Instrumentation preserves the complete result, including errors and fuel
exhaustion, for every initial trace. It does not call a hint provider twice. -/
theorem eval_agrees [Field F] [DecidableEq F] (world : World F)
    (hints : SourceSemantics.HintProvider world) (types locals fuel expr) :
    FlowAgrees (evalWithTrace world hints types locals fuel expr)
      (evalOutcomeWith world hints types locals fuel expr) := by
  induction fuel generalizing types locals expr with
  | zero => exact flow_error _
  | succ fuel ih =>
      have args (types locals) (items : List (Expr F)) :=
        flow_mapM (fun expr => ih types locals expr) items
      cases expr with
      | control kind body =>
          cases kind with
          | block label => exact flow_catch (ih _ _ _)
          | exit target => exact flow_bind (ih _ _ _) (fun value => flow_throw _)
      | literal value => exact flow_pure _
      | var name =>
          simp only [evalWithTrace, evalOutcomeWith]
          cases locals.find? (·.1 == name) with
          | none => exact flow_error _
          | some pair => exact flow_pure _
      | global name annotation =>
          simp only [evalWithTrace, evalOutcomeWith]
          cases annotation with
          | none => exact flow_error _
          | some type =>
              apply flow_bind (flow_lift _)
              intro pattern
              exact flow_bind (flow_lift _) (fun body => ih _ _ _)
      | tuple items | array items => exact flow_bind (args _ _ _) (fun values => flow_pure _)
      | «repeat» value n => exact flow_bind (ih _ _ _) (fun value => flow_pure _)
      | index value i | project value i | slice value start stop | member value field | neg value =>
          exact flow_bind (ih _ _ _) (fun value => flow_lift _)
      | builtin op items =>
          apply flow_bind (args _ _ _)
          intro values
          cases op with
          | assertEq message => simpa only [pure_bind] using (flow_lift (Builtin.apply (.assertEq message) values))
          | ascribe t => simpa only [pure_bind] using (flow_lift (Builtin.apply (.ascribe t) values))
          | debug message => exact emit_then _ (flow_lift _)
      | update paths items => exact flow_bind (args _ _ _) (fun values => flow_lift _)
      | record head items | construct name typeArgs ctor items | constructAs params t ctor items =>
          exact flow_bind (args _ _ _) (fun values => flow_pure _)
      | letValue pattern value body =>
          apply flow_bind (ih _ _ _)
          intro value
          apply flow_bind flow_get
          intro heap
          apply flow_bind (flow_lift _)
          intro matched
          cases matched with
          | none => exact flow_error _
          | some bindings => exact ih _ _ _
      | store value =>
          apply flow_bind (ih _ _ _)
          intro value
          apply flow_bind flow_get
          intro heap
          exact flow_bind (flow_set _) (fun _ => flow_pure _)
      | load value =>
          apply flow_bind (ih _ _ _)
          intro value
          exact flow_bind flow_get (fun heap => flow_lift _)
      | hint type key channel =>
          apply flow_bind (ih _ _ _)
          intro value
          exact flow_bind (flow_lift _) (fun value => flow_pure _)
      | binary op left right =>
          apply flow_bind (ih _ _ _)
          intro left
          exact flow_bind (ih _ _ _) (fun right => flow_lift _)
      | call name typeArgs inputs =>
          apply flow_bind (args _ _ _)
          intro values
          apply emit_then
          apply flow_bind (flow_lift _)
          intro (calleeTypes, bindings, body)
          have same := flow_lift_eval (agrees_finish (ih calleeTypes bindings body))
          have finished := flow_bind same (fun result => emit_then
            (.leave (instanceName types name typeArgs) result) (flow_pure result))
          simpa only [bind_pure] using finished
      | matchValue value arms =>
          apply flow_bind (ih _ _ _)
          intro value
          apply flow_bind flow_get
          intro heap
          apply flow_bind (flow_lift _)
          intro matched
          cases matched with
          | none => exact flow_error _
          | some pair => exact ih _ _ _

end Aiur.Generic.Traced
