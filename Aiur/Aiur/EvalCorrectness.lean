import Aiur.Semantics
import Aiur.Semantics.NoHints

namespace Aiur

variable {F : Type} {program : Program F} {hints : HintProvider F program.enums}

set_option linter.unusedSimpArgs false

namespace Evaluation

theorem bind_ok {first : Evaluation F α} {next : α → Evaluation F β}
    {before after : Heap F} {result : β} :
    (first >>= next) before = .ok (result, after) ↔
      ∃ value middle, first before = .ok (value, middle) ∧ next value middle = .ok (result, after) := by
  cases executed : first before with
  | error error => simp [StateT.bind, bind, Except.bind, executed]
  | ok output =>
      rcases output with ⟨value, middle⟩
      simp only [StateT.bind, bind, Except.bind, executed, Except.ok.injEq, Prod.mk.injEq]
      constructor
      · intro h; exact ⟨value, middle, ⟨rfl, rfl⟩, h⟩
      · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩; exact h

@[simp] theorem pure_ok {value result : α} {before after : Heap F} :
    (pure value : Evaluation F α) before = .ok (result, after) ↔ value = result ∧ before = after := by
  simp [pure, StateT.pure, Except.pure]

theorem lift_ok {computation : Except EvalError α} {value : α} {before after : Heap F} :
    (liftM computation : Evaluation F α) before = .ok (value, after) ↔
      computation = .ok value ∧ before = after := by
  cases computation with
  | error error =>
      change (Except.error error : Except EvalError _) = .ok (value, after) ↔ _
      simp
  | ok result =>
      change Except.ok (result, before) = (Except.ok (value, after) : Except EvalError _) ↔ _
      simp only [Except.ok.injEq, Prod.mk.injEq]

@[simp] theorem lift_apply (computation : Except EvalError α) (heap : Heap F) :
    (liftM computation : Evaluation F α) heap = computation.map (fun value => (value, heap)) := by
  cases computation <;> rfl

@[simp] theorem get_apply (heap : Heap F) :
    (get : Evaluation F (Heap F)) heap = .ok (heap, heap) := rfl

@[simp] theorem throw_apply (error : EvalError) (heap : Heap F) :
    (throw error : Evaluation F α) heap = .error error := rfl

end Evaluation

private theorem evalArgs_of_mapM [Field F] [DecidableEq F]
    {locals : Environment F Nat} {fuel : Nat}
    (sound : ∀ expr before result after,
      evalExprWith program hints locals fuel expr before = .ok (result, after) →
        EvalExpr program locals expr before result after)
    {args : List (Expr F)} {values : List (SourceValue F)} {before after : Heap F}
    (executed : args.mapM (evalExprWith program hints locals fuel) before = .ok (values, after)) :
    EvalArgs program locals args before values after := by
  induction args generalizing before values with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp executed
      exact .nil
  | cons head tail ih =>
      rw [List.mapM_cons] at executed
      obtain ⟨value, middle, headRun, rest⟩ := Evaluation.bind_ok.mp executed
      obtain ⟨results, last, tailRun, finished⟩ := Evaluation.bind_ok.mp rest
      obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
      exact .cons (sound head before value middle headRun) (ih tailRun)

/-- Every successful run, including its final heap, has a fuel-free evaluation proof. -/
theorem evalExpr_spec [Field F] [DecidableEq F]
    {locals : Environment F Nat} {fuel : Nat} {expr : Expr F}
    {before after : Heap F} {result : SourceValue F}
    (executed : evalExprWith program hints locals fuel expr before = .ok (result, after)) :
    EvalExpr program locals expr before result after := by
  induction fuel generalizing locals expr before result after with
  | zero => simp [evalExprWith] at executed
  | succ fuel ih =>
      cases expr with
      | literal value =>
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp executed
          exact .literal
      | var name =>
          cases found : locals.find? (·.1 == name) with
          | none => simp [evalExprWith, found, Evaluation.throw_apply] at executed
          | some binding =>
              rcases binding with ⟨key, value⟩
              have same : key = name := by simpa using List.find?_some found
              subst key
              simp only [evalExprWith, found] at executed
              obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp executed
              exact .var found
      | tuple items =>
          simp only [evalExprWith] at executed
          obtain ⟨values, middle, itemsRun, finished⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .tuple (evalArgs_of_mapM (fun _ _ _ _ h => ih h) itemsRun)
      | construct name ctor items =>
          simp only [evalExprWith] at executed
          obtain ⟨values, middle, itemsRun, finished⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .construct (evalArgs_of_mapM (fun _ _ _ _ h => ih h) itemsRun)
      | project value index =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, operation⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨projected, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .project (ih operand) projected
      | hint type key channel =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, keyRun, rest⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨value, last, supplied, finished⟩ := Evaluation.bind_ok.mp rest
          obtain ⟨_, rfl⟩ := Evaluation.lift_ok.mp supplied
          obtain ⟨rfl, rfl⟩ := Evaluation.pure_ok.mp finished
          exact .hint (ih keyRun) value.property
      | neg value =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, operation⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨negated, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .neg (ih operand) negated
      | store value =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, stored⟩ := Evaluation.bind_ok.mp executed
          have same : (.ptr input.type middle.length, middle ++ [input]) = (result, after) := by
            simpa [bind, StateT.bind, Evaluation.get_apply, set, StateT.set,
              pure, StateT.pure, Except.pure, Except.bind] using stored
          cases same
          exact .store (ih operand)
      | load value =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, loaded⟩ := Evaluation.bind_ok.mp executed
          have lifted : (liftM (loadValue middle input) : Evaluation F _) middle = .ok (result, after) := by
            simpa [bind, StateT.bind, Evaluation.get_apply, Except.bind] using loaded
          obtain ⟨loadOK, rfl⟩ := Evaluation.lift_ok.mp lifted
          exact .load (ih operand) loadOK
      | assertEq op left right =>
          simp only [evalExprWith] at executed
          obtain ⟨leftValue, middle, leftRun, rest⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rightValue, last, rightRun, operation⟩ := Evaluation.bind_ok.mp rest
          obtain ⟨operationOK, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .assertEq (ih leftRun) (ih rightRun) operationOK
      | binary op left right =>
          simp only [evalExprWith] at executed
          obtain ⟨leftValue, middle, leftRun, rest⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨rightValue, last, rightRun, operation⟩ := Evaluation.bind_ok.mp rest
          obtain ⟨operationOK, rfl⟩ := Evaluation.lift_ok.mp operation
          exact .binary (ih leftRun) (ih rightRun) operationOK
      | letValue pattern value body =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, rest⟩ := Evaluation.bind_ok.mp executed
          cases matched : pattern.bindings input with
          | none => simp [matched] at rest
          | some bindings =>
              exact .letValue (ih operand) matched (ih (by simpa only [matched] using rest))
      | matchValue scrutinee arms =>
          simp only [evalExprWith] at executed
          obtain ⟨input, middle, operand, rest⟩ := Evaluation.bind_ok.mp executed
          cases selected : selectArm input arms with
          | none => simp [selected] at rest
          | some binding =>
              rcases binding with ⟨bindings, body⟩
              exact .matchValue (ih operand) selected (ih (by simpa only [selected] using rest))
      | call name args =>
          simp only [evalExprWith] at executed
          obtain ⟨values, middle, arguments, rest⟩ := Evaluation.bind_ok.mp executed
          obtain ⟨⟨bindings, body⟩, last, prepared, called⟩ := Evaluation.bind_ok.mp rest
          obtain ⟨prepareOK, rfl⟩ := Evaluation.lift_ok.mp prepared
          exact .call (evalArgs_of_mapM (fun _ _ _ _ h => ih h) arguments) (.intro prepareOK (ih called))

/-- Evaluations in the hint-free fragment run with every provider and enough fuel. -/
theorem EvalExpr.eventually_runs [Field F] [DecidableEq F]
    {locals : Environment F Nat} {expr : Expr F} {result : SourceValue F} {before after : Heap F}
    (evaluates : EvalExpr program locals expr before result after) (safe : program.noHints = true) :
    expr.noHints = true →
    ∃ minimum, ∀ fuel, minimum ≤ fuel → evalExprWith program hints locals fuel expr before = .ok (result, after) := by
  induction evaluates using EvalExpr.rec
    (motive_2 := fun locals exprs before values after _ =>
      (∀ expr ∈ exprs, expr.noHints = true) → ∃ minimum, ∀ fuel, minimum ≤ fuel → exprs.mapM (evalExprWith program hints locals fuel) before = .ok (values, after))
    (motive_3 := fun name args before result after _ =>
      ∃ minimum, ∀ fuel, minimum ≤ fuel → ∃ locals expr,
        prepareCall program name args = .ok (locals, expr) ∧
          evalExprWith program hints locals fuel expr before = .ok (result, after)) with
  | literal =>
      intro _
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rfl
  | var lookup =>
      intro _
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [evalExprWith, lookup, pure, StateT.pure, Except.pure]
  | tuple _ ih | construct _ ih =>
      intro exprSafe
      obtain ⟨minimum, runs⟩ := ih (by simpa [Expr.noHints] using exprSafe)
      refine ⟨minimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [evalExprWith, runs fuel (by omega), bind, StateT.bind, Evaluation.lift_apply, Except.map, Evaluation.get_apply, pure, StateT.pure, Except.bind, Except.pure]
  | project _ projected ih | neg _ projected ih | load _ projected ih =>
      intro exprSafe
      obtain ⟨minimum, runs⟩ := ih (by simpa [Expr.noHints] using exprSafe)
      refine ⟨minimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [evalExprWith, runs fuel (by omega), projected, bind, StateT.bind, Except.bind, Evaluation.lift_apply, Except.map, Evaluation.get_apply]
  | store _ ih =>
      intro exprSafe
      obtain ⟨minimum, runs⟩ := ih (by simpa [Expr.noHints] using exprSafe)
      refine ⟨minimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [evalExprWith, runs fuel (by omega), bind, StateT.bind, Except.bind,
            Evaluation.get_apply, set, StateT.set, pure, StateT.pure, Except.pure]
  | hint => intro impossible; simp [Expr.noHints] at impossible
  | assertEq _ _ operation leftIH rightIH =>
      intro exprSafe
      simp only [Expr.noHints, Bool.and_eq_true] at exprSafe
      have safeParts := exprSafe
      obtain ⟨leftMinimum, leftRuns⟩ := leftIH safeParts.1
      obtain ⟨rightMinimum, rightRuns⟩ := rightIH safeParts.2
      refine ⟨max leftMinimum rightMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [evalExprWith, leftRuns fuel (by omega), rightRuns fuel (by omega),
            operation, bind, StateT.bind, Except.bind, Evaluation.lift_apply, Except.map, Evaluation.get_apply]
  | binary _ _ operation leftIH rightIH =>
      intro exprSafe
      simp only [Expr.noHints, Bool.and_eq_true] at exprSafe
      have safeParts := exprSafe
      obtain ⟨leftMinimum, leftRuns⟩ := leftIH safeParts.1
      obtain ⟨rightMinimum, rightRuns⟩ := rightIH safeParts.2
      refine ⟨max leftMinimum rightMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [evalExprWith, leftRuns fuel (by omega), rightRuns fuel (by omega),
            operation, bind, StateT.bind, Except.bind, Evaluation.lift_apply, Except.map, Evaluation.get_apply]
  | letValue _ matched _ valueIH bodyIH =>
      intro exprSafe
      simp only [Expr.noHints, Bool.and_eq_true] at exprSafe
      have safeParts := exprSafe
      obtain ⟨valueMinimum, valueRuns⟩ := valueIH safeParts.1
      obtain ⟨bodyMinimum, bodyRuns⟩ := bodyIH safeParts.2
      refine ⟨max valueMinimum bodyMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simpa [evalExprWith, valueRuns fuel (by omega), matched, bind, StateT.bind, Except.bind, Evaluation.lift_apply, Except.map, Evaluation.get_apply]
            using bodyRuns fuel (by omega)
  | matchValue _ matched _ valueIH bodyIH =>
      intro exprSafe
      simp only [Expr.noHints, Bool.and_eq_true] at exprSafe
      have safeParts := exprSafe
      obtain ⟨valueMinimum, valueRuns⟩ := valueIH safeParts.1
      obtain ⟨bodyMinimum, bodyRuns⟩ := bodyIH (selectArm_noHints (by simpa using safeParts.2) matched)
      refine ⟨max valueMinimum bodyMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simpa [evalExprWith, valueRuns fuel (by omega), matched, bind, StateT.bind, Except.bind, Evaluation.lift_apply, Except.map, Evaluation.get_apply]
            using bodyRuns fuel (by omega)
  | call _ _ argsIH callIH =>
      intro exprSafe
      obtain ⟨argsMinimum, argsRuns⟩ := argsIH (by simpa [Expr.noHints] using exprSafe)
      obtain ⟨callMinimum, callRuns⟩ := callIH
      refine ⟨max argsMinimum callMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          obtain ⟨locals, expr, prepared, bodyRun⟩ := callRuns fuel (by omega)
          simpa [evalExprWith, argsRuns fuel (by omega), prepared, bind, StateT.bind, Except.bind, Evaluation.lift_apply, Except.map, Evaluation.get_apply] using bodyRun
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | cons _ _ headIH tailIH =>
      rename_i exprSafe
      obtain ⟨headMinimum, headRuns⟩ := headIH (exprSafe _ (by simp))
      obtain ⟨tailMinimum, tailRuns⟩ := tailIH (fun e h => exprSafe e (by simp [h]))
      refine ⟨max headMinimum tailMinimum, ?_⟩
      intro fuel enough
      simp [List.mapM_cons, headRuns fuel (by omega), tailRuns fuel (by omega),
        bind, StateT.bind, Evaluation.lift_apply, Except.map, Evaluation.get_apply, pure, StateT.pure, Except.bind, Except.pure]
  | intro prepared _ bodyIH =>
      obtain ⟨minimum, runs⟩ := bodyIH (prepareCall_noHints safe prepared)
      exact ⟨minimum, fun fuel enough => ⟨_, _, prepared, runs fuel enough⟩⟩



theorem run_eq_ok_iff [Field F] [DecidableEq F]
    {name : String} {args : List (SourceValue F)} {fuel : Nat}
    {result : SourceValue F} {heap : Heap F} :
    run program name args fuel hints = .ok (result, heap) ↔
      typecheck program = .ok () ∧ checkEntry program name = .ok () ∧ ∃ locals expr,
        prepareCall program name args = .ok (locals, expr) ∧
        evalExprWith program hints locals fuel expr [] = .ok (result, heap) := by
  cases checked : typecheck program with
  | error error => simp [run, checked, bind, Except.bind]
  | ok finished =>
      cases finished
      cases entry : checkEntry program name with
      | error error => simp [run, checked, entry, bind, Except.bind, pure, Except.pure]
      | ok finished =>
          cases finished
          cases prepared : prepareCall program name args with
          | error error => simp [run, checked, entry, prepared, bind, Except.bind, pure, Except.pure]
          | ok binding =>
              rcases binding with ⟨locals, expr⟩
              simp only [run, checked, entry, prepared, bind, pure, Except.bind, Except.pure,
                Except.ok.injEq, Prod.mk.injEq, true_and]
              constructor
              · intro executed; exact ⟨locals, expr, ⟨rfl, rfl⟩, executed⟩
              · rintro ⟨_, _, ⟨rfl, rfl⟩, executed⟩; exact executed

theorem eval_eq_ok_iff [Field F] [DecidableEq F]
    {name : String} {args : List (SourceValue F)} {fuel : Nat} {result : SourceValue F} :
    eval program name args fuel hints = .ok result ↔ ∃ heap, run program name args fuel hints = .ok (result, heap) := by
  cases executed : run program name args fuel hints with
  | error error => simp [eval, executed, Except.map]
  | ok pair => cases pair; simp [eval, executed, Except.map]

/-- Successful execution agrees with the allocation-aware evaluation predicate. -/
theorem eval_spec [Field F] [DecidableEq F]
    {name : String} {args : List (SourceValue F)} {fuel : Nat} {result : SourceValue F}
    (executed : eval program name args fuel hints = .ok result) : EvalCall program name args result := by
  obtain ⟨heap, executed⟩ := eval_eq_ok_iff.mp executed
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  exact ⟨entry, heap, .intro prepared (evalExpr_spec body)⟩

theorem EvalCall.eventually_eval [Field F] [DecidableEq F]
    (checked : typecheck program = .ok ()) {name : String}
    {args : List (SourceValue F)} {result : SourceValue F} (evaluates : EvalCall program name args result)
    (safe : program.noHints = true) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel → eval program name args fuel hints = .ok result := by
  obtain ⟨entry, heap, evaluated⟩ := evaluates
  cases evaluated with
  | intro prepared body =>
      obtain ⟨minimum, runs⟩ := body.eventually_runs safe (prepareCall_noHints safe prepared)
      exact ⟨minimum, fun fuel enough => eval_eq_ok_iff.mpr
        ⟨heap, run_eq_ok_iff.mpr ⟨checked, entry, _, _, prepared, runs fuel enough⟩⟩⟩

theorem eval_complete [Field F] [DecidableEq F]
    (checked : typecheck program = .ok ()) {name : String}
    {args : List (SourceValue F)} {result : SourceValue F} (evaluates : EvalCall program name args result)
    (safe : program.noHints = true) :
    ∃ fuel, eval program name args fuel hints = .ok result := by
  obtain ⟨minimum, runs⟩ := evaluates.eventually_eval checked safe
  exact ⟨minimum, runs minimum (Nat.le_refl _)⟩

theorem exists_eval_iff [Field F] [DecidableEq F]
    {name : String} {args : List (SourceValue F)} {result : SourceValue F}
    (safe : program.noHints = true) :
    (∃ fuel, eval program name args fuel hints = .ok result) ↔
      typecheck program = .ok () ∧ EvalCall program name args result := by
  constructor
  · rintro ⟨fuel, executed⟩
    obtain ⟨heap, ran⟩ := eval_eq_ok_iff.mp executed
    exact ⟨(run_eq_ok_iff.mp ran).1, eval_spec executed⟩
  · rintro ⟨checked, evaluated⟩
    exact eval_complete checked evaluated safe

theorem EvalExpr.deterministic [Field F] [DecidableEq F]
    {locals : Environment F Nat} {expr : Expr F} {before leftHeap rightHeap : Heap F}
    {left right : SourceValue F}
    (first : EvalExpr program locals expr before left leftHeap)
    (second : EvalExpr program locals expr before right rightHeap)
    (safe : program.noHints = true) (exprSafe : expr.noHints = true) :
    left = right ∧ leftHeap = rightHeap := by
  obtain ⟨a, leftRuns⟩ := first.eventually_runs (hints := HintProvider.unavailable) safe exprSafe
  obtain ⟨b, rightRuns⟩ := second.eventually_runs (hints := HintProvider.unavailable) safe exprSafe
  exact Prod.mk.inj (Except.ok.inj ((leftRuns (max a b) (Nat.le_max_left _ _)).symm.trans
    (rightRuns (max a b) (Nat.le_max_right _ _))))

theorem EvalFn.deterministic [Field F] [DecidableEq F]
    {name : String} {args : List (SourceValue F)} {before leftHeap rightHeap : Heap F}
    {left right : SourceValue F}
    (first : EvalFn program name args before left leftHeap)
    (second : EvalFn program name args before right rightHeap)
    (safe : program.noHints = true) :
    left = right ∧ leftHeap = rightHeap := by
  cases first with
  | intro prepared body =>
      cases second with
      | intro otherPrepared otherBody =>
          cases Except.ok.inj (prepared.symm.trans otherPrepared)
          exact body.deterministic otherBody safe (prepareCall_noHints safe prepared)

theorem EvalCall.deterministic [Field F] [DecidableEq F]
    {name : String} {args : List (SourceValue F)} {left right : SourceValue F}
    (first : EvalCall program name args left) (second : EvalCall program name args right)
    (safe : program.noHints = true) :
    left = right := by
  obtain ⟨_, _, first⟩ := first
  obtain ⟨_, _, second⟩ := second
  exact (first.deterministic second safe).1

end Aiur
