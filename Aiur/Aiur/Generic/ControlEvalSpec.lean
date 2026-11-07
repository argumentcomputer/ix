import Aiur.Generic.ControlEvalFacts

namespace Aiur.Generic.SourceSemantics

variable {F : Type} [Field F] [DecidableEq F]
variable {world : World F} {types : Types} {hints : HintProvider world}

private theorem args_spec {locals : Environment F Nat} {fuel : Nat}
    (sound : ∀ expr before result after,
      (evalOutcomeWith world hints types locals fuel expr).run before = .ok (result, after) →
        Outcome.Evaluates world types locals expr before result after)
    {args : List (Expr F)} {before after : Heap F}
    (executed : (args.mapM (evalOutcomeWith world hints types locals fuel)).run before = .ok (outcome, after)) :
    ArgsOutcome world types locals args before outcome after := by
  induction args generalizing before outcome with
  | nil =>
      obtain ⟨rfl, rfl⟩ := FlowEvaluation.pure_ok.mp executed
      exact .nil
  | cons head tail ih =>
      rw [List.mapM_cons] at executed
      rcases FlowEvaluation.bind_ok.mp executed with ⟨value, middle, run, rest⟩ | ⟨⟨target, value⟩, run, rfl⟩
      · rcases FlowEvaluation.bind_ok.mp rest with ⟨values, last, tailRun, finished⟩ | ⟨⟨target, result⟩, tailRun, rfl⟩
        · obtain ⟨rfl, rfl⟩ := FlowEvaluation.pure_ok.mp finished
          exact .cons (sound _ _ _ _ run) (ih tailRun)
        · exact .tail (sound _ _ _ _ run) (ih tailRun)
      · exact .head (sound _ _ _ _ run)

/-- Successful execution gives either an ordinary evaluation or an explicit
exit derivation, including the exact heap retained at that point. -/
theorem evalOutcome_spec {locals : Environment F Nat} {fuel : Nat} {expr : Expr F}
    {before after : Heap F} {outcome : Outcome F}
    (executed : (evalOutcomeWith world hints types locals fuel expr).run before = .ok (outcome, after)) :
    Outcome.Evaluates world types locals expr before outcome after := by
  induction fuel generalizing types locals expr before outcome after with
  | zero => simp [evalOutcomeWith] at executed
  | succ fuel ih =>
      cases expr with
      | control kind body =>
          cases kind with
          | block label =>
              obtain ⟨inner, run, caught⟩ := catchExit_ok.mp executed
              cases inner with
              | ok value =>
                  simp only [Outcome.catch] at caught
                  subst outcome
                  exact .block (ih run)
              | error exit =>
                  rcases exit with ⟨target, value⟩
                  by_cases same : target = .block label
                  · subst target
                    simp only [Outcome.catch, if_pos rfl] at caught
                    subst outcome
                    exact .blockExit (ih run)
                  · simp only [Outcome.catch, if_neg same] at caught
                    subst outcome
                    exact .fromBlock same (ih run)
          | exit target =>
              rcases FlowEvaluation.bind_ok.mp executed with ⟨value, middle, run, rest⟩ | ⟨⟨other, value⟩, run, rfl⟩
              · obtain ⟨rfl, rfl⟩ := FlowEvaluation.throw_ok.mp rest
                exact .exit (ih run)
              · exact .exitPayload (ih run)
      | literal value =>
          obtain ⟨rfl, rfl⟩ := FlowEvaluation.pure_ok.mp executed
          exact .literal
      | var name =>
          cases found : locals.find? (·.1 == name) with
          | none => simp [evalOutcomeWith, found] at executed
          | some binding =>
              rcases binding with ⟨key, value⟩
              have same : key = name := by simpa using List.find?_some found
              subst key
              simp only [evalOutcomeWith, found] at executed
              obtain ⟨rfl, rfl⟩ := FlowEvaluation.pure_ok.mp executed
              exact .var found
      | builtin paths items =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨values, middle, run, operation⟩ | ⟨⟨target, value⟩, run, rfl⟩
          · obtain ⟨result, op, rfl, rfl⟩ := FlowEvaluation.lift_ok.mp operation
            exact .builtin (args_spec (fun _ _ _ _ h => ih h) run) op
          · exact .fromBuiltin (args_spec (fun _ _ _ _ h => ih h) run)
      | update paths items =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨values, middle, run, operation⟩ | ⟨⟨target, value⟩, run, rfl⟩
          · obtain ⟨result, op, rfl, rfl⟩ := FlowEvaluation.lift_ok.mp operation
            exact .update (args_spec (fun _ _ _ _ h => ih h) run) op
          · exact .fromUpdate (args_spec (fun _ _ _ _ h => ih h) run)
      | record head items | tuple items | array items | construct name args ctor items | constructAs params t ctor items =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨values, middle, run, finished⟩ | ⟨⟨target, value⟩, run, rfl⟩
          · obtain ⟨rfl, rfl⟩ := FlowEvaluation.pure_ok.mp finished
            have args := args_spec (fun _ _ _ _ h => ih h) run
            first | exact .record args | exact .tuple args | exact .array args | exact .construct args | exact .constructAs args
          · have args := args_spec (fun _ _ _ _ h => ih h) run
            first | exact .fromRecord args | exact .fromTuple args | exact .fromArray args | exact .fromConstruct args | exact .fromConstructAs args
      | member value field | project value index | index value index | slice value start stop | neg value =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨input, middle, run, operation⟩ | ⟨⟨target, value⟩, run, rfl⟩
          · obtain ⟨result, op, rfl, rfl⟩ := FlowEvaluation.lift_ok.mp operation
            first | exact .member (ih run) op | exact .project (ih run) op | exact .index (ih run) op
                  | exact .slice (ih run) op | exact .neg (ih run) op
          · first | exact .fromMember (ih run) | exact .fromProject (ih run) | exact .fromIndex (ih run)
                  | exact .fromSlice (ih run) | exact .fromNeg (ih run)
      | «repeat» value length =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨input, middle, run, finished⟩ | ⟨⟨target, result⟩, run, rfl⟩
          · obtain ⟨rfl, rfl⟩ := FlowEvaluation.pure_ok.mp finished
            exact .repeat (ih run)
          · exact .fromRepeat (ih run)
      | global name ann =>
          cases ann with
          | none => simp [evalOutcomeWith] at executed
          | some type =>
              simp only [evalOutcomeWith] at executed
              rcases FlowEvaluation.bind_ok.mp executed with ⟨pattern, middle, lookup, rest⟩ | ⟨exit, lookup, _⟩
              · obtain ⟨_, lookupOK, same, rfl⟩ := FlowEvaluation.lift_ok.mp lookup
                cases same
                rcases FlowEvaluation.bind_ok.mp rest with ⟨body, last, interpreted, run⟩ | ⟨exit, interpreted, _⟩
                · obtain ⟨_, interpretOK, same, rfl⟩ := FlowEvaluation.lift_ok.mp interpreted
                  cases same
                  have interpreted : Consts.toExpr pattern = .ok body := by
                    cases h : Consts.toExpr pattern <;> simp_all [Except.mapError]
                  cases outcome with
                  | ok => exact .global lookupOK interpreted (ih run)
                  | error exit => cases exit; exact .fromGlobal lookupOK interpreted (ih run)
                · obtain ⟨_, _, impossible, _⟩ := FlowEvaluation.lift_ok.mp interpreted
                  cases impossible
              · obtain ⟨_, _, impossible, _⟩ := FlowEvaluation.lift_ok.mp lookup
                cases impossible
      | hint type key channel =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨input, middle, run, rest⟩ | ⟨⟨target, value⟩, run, rfl⟩
          · rcases FlowEvaluation.bind_ok.mp rest with ⟨value, last, supplied, finished⟩ | ⟨exit, supplied, _⟩
            · obtain ⟨_, _, same, rfl⟩ := FlowEvaluation.lift_ok.mp supplied
              cases same
              obtain ⟨rfl, rfl⟩ := FlowEvaluation.pure_ok.mp finished
              exact .hint (ih run) value.property
            · obtain ⟨_, _, impossible, _⟩ := FlowEvaluation.lift_ok.mp supplied
              cases impossible
          · exact .fromHint (ih run)
      | store value =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨input, middle, run, stored⟩ | ⟨⟨target, result⟩, run, rfl⟩
          · change Except.ok (.ok (.ptr input.type middle.length), middle ++ [input]) = .ok (outcome, after) at stored
            cases Except.ok.inj stored
            exact .store (ih run)
          · exact .fromStore (ih run)
      | load value =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨input, middle, run, loaded⟩ | ⟨⟨target, result⟩, run, rfl⟩
          · change (liftM (loadValue middle input) : FlowEvaluation F _).run middle = .ok (outcome, after) at loaded
            obtain ⟨result, loadOK, rfl, rfl⟩ := FlowEvaluation.lift_ok.mp loaded
            exact .load (ih run) loadOK
          · exact .fromLoad (ih run)
      | binary op left right =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨leftValue, middle, leftRun, rest⟩ | ⟨⟨target, result⟩, run, rfl⟩
          · rcases FlowEvaluation.bind_ok.mp rest with ⟨rightValue, last, rightRun, operation⟩ | ⟨⟨target, result⟩, rightRun, rfl⟩
            · obtain ⟨result, operationOK, rfl, rfl⟩ := FlowEvaluation.lift_ok.mp operation
              exact .binary (ih leftRun) (ih rightRun) operationOK
            · exact .binaryRight (ih leftRun) (ih rightRun)
          · exact .binaryLeft (ih run)
      | letValue pattern value body =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨input, middle, run, rest⟩ | ⟨⟨target, result⟩, run, rfl⟩
          · have rest' : (do
                let some bindings ← liftM (world.matchPattern types middle pattern input) | flowError EvalError.patternMismatch
                evalOutcomeWith world hints types (bindings ++ locals) fuel body : FlowEvaluation F _).run middle = .ok (outcome, after) := rest
            rcases FlowEvaluation.bind_ok.mp rest' with ⟨bindings, last, matched, bodyRun⟩ | ⟨exit, matched, _⟩
            · obtain ⟨_, matchOK, same, rfl⟩ := FlowEvaluation.lift_ok.mp matched
              cases same
              cases bindings with
              | none => simp at bodyRun
              | some bindings =>
                  cases outcome with
                  | ok => exact .letValue (ih run) matchOK (ih bodyRun)
                  | error exit => cases exit; exact .letBody (ih run) matchOK (ih bodyRun)
            · obtain ⟨_, _, impossible, _⟩ := FlowEvaluation.lift_ok.mp matched
              cases impossible
          · exact .fromLetValue (ih run)
      | matchValue scrutinee arms =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨input, middle, run, rest⟩ | ⟨⟨target, result⟩, run, rfl⟩
          · have rest' : (do
                let some (bindings, body) ← liftM (selectArm world types middle input arms) | flowError EvalError.noMatchingArm
                evalOutcomeWith world hints types (bindings ++ locals) fuel body : FlowEvaluation F _).run middle = .ok (outcome, after) := rest
            rcases FlowEvaluation.bind_ok.mp rest' with ⟨selection, last, selected, bodyRun⟩ | ⟨exit, selected, _⟩
            · obtain ⟨_, selectionOK, same, rfl⟩ := FlowEvaluation.lift_ok.mp selected
              cases same
              cases selection with
              | none => simp at bodyRun
              | some pair =>
                  rcases pair with ⟨bindings, body⟩
                  cases outcome with
                  | ok => exact .matchValue (ih run) selectionOK (ih bodyRun)
                  | error exit => cases exit; exact .matchBody (ih run) selectionOK (ih bodyRun)
            · obtain ⟨_, _, impossible, _⟩ := FlowEvaluation.lift_ok.mp selected
              cases impossible
          · exact .fromMatchValue (ih run)
      | call name typeArgs args =>
          simp only [evalOutcomeWith] at executed
          rcases FlowEvaluation.bind_ok.mp executed with ⟨values, middle, arguments, rest⟩ | ⟨⟨target, result⟩, arguments, rfl⟩
          · rcases FlowEvaluation.bind_ok.mp rest with ⟨⟨calleeTypes, bindings, body⟩, last, prepared, called⟩ | ⟨exit, prepared, _⟩
            · obtain ⟨_, prepareOK, same, rfl⟩ := FlowEvaluation.lift_ok.mp prepared
              cases same
              obtain ⟨result, functionRun, rfl⟩ := FlowEvaluation.liftEvaluation_ok
                (action := finishFunction (evalOutcomeWith world hints calleeTypes bindings fuel body)) |>.mp called
              apply EvalExpr.call (args_spec (fun _ _ _ _ h => ih h) arguments)
              rcases finishFunction_ok.mp functionRun with normal | returned
              · exact .intro prepareOK (ih normal)
              · exact .returned prepareOK (ih returned)
            · obtain ⟨_, _, impossible, _⟩ := FlowEvaluation.lift_ok.mp prepared
              cases impossible
          · exact .fromCall (args_spec (fun _ _ _ _ h => ih h) arguments)

theorem evalFunction_spec {locals : Environment F Nat} {fuel : Nat} {expr : Expr F}
    {before after : Heap F}
    (prepared : world.prepare name args = .ok (types, locals, expr))
    (executed : evalFunctionWith world hints types locals fuel expr before = .ok (result, after)) :
    EvalFn world name args before result after := by
  rcases finishFunction_ok.mp executed with normal | returned
  · exact .intro prepared (evalOutcome_spec normal)
  · exact .returned prepared (evalOutcome_spec returned)

end Aiur.Generic.SourceSemantics
