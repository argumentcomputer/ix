import Aiur.Tuple.Semantics

namespace Aiur.Tuple

private theorem evalArgs_of_mapM [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F} {fuel : Nat}
    (sound : ∀ expr result, evalExpr program locals fuel expr = .ok result →
      EvalExpr program locals expr result)
    {args : List (Expr F)} {values : List (Value F)}
    (executed : args.mapM (evalExpr program locals fuel) = .ok values) :
    EvalArgs program locals args values := by
  induction args generalizing values with
  | nil =>
      simp [pure, Except.pure] at executed
      subst values
      exact .nil
  | cons head tail ih =>
      cases headRun : evalExpr program locals fuel head with
      | error error => simp [List.mapM_cons, headRun, bind, Except.bind] at executed
      | ok value =>
          cases tailRun : tail.mapM (evalExpr program locals fuel) with
          | error error => simp [List.mapM_cons, headRun, tailRun, bind, Except.bind] at executed
          | ok results =>
              simp [List.mapM_cons, headRun, tailRun, bind, pure, Except.bind, Except.pure] at executed
              subst values
              exact .cons (sound head value headRun) (ih tailRun)

/-- Every successful executable run has a finite fuel-free evaluation proof. -/
theorem evalExpr_spec [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F} {fuel : Nat} {expr : Expr F} {result : Value F}
    (executed : evalExpr program locals fuel expr = .ok result) :
    EvalExpr program locals expr result := by
  induction fuel generalizing locals expr result with
  | zero => simp [evalExpr] at executed
  | succ fuel ih =>
      cases expr with
      | literal value =>
          simp [evalExpr, pure, Except.pure] at executed
          subst result
          exact .literal
      | var name =>
          cases found : locals.find? (·.1 == name) with
          | none => simp [evalExpr, found, throw] at executed
          | some binding =>
              rcases binding with ⟨key, value⟩
              have same : key = name := by simpa using List.find?_some found
              subst key
              simp [evalExpr, found, pure, Except.pure] at executed
              subst result
              exact .var found
      | tuple items =>
          cases run : items.mapM (evalExpr program locals fuel) with
          | error error => simp [evalExpr, run, bind, Except.bind] at executed
          | ok values =>
              simp [evalExpr, run, bind, pure, Except.bind, Except.pure] at executed
              subst result
              exact .tuple (evalArgs_of_mapM (fun _ _ run => ih run) run)
      | project value index =>
          cases run : evalExpr program locals fuel value with
          | error error => simp [evalExpr, run, bind, Except.bind] at executed
          | ok input =>
              exact .project (ih run) (by simpa [evalExpr, run, bind, Except.bind] using executed)
      | neg value =>
          cases run : evalExpr program locals fuel value with
          | error error => simp [evalExpr, run, bind, Except.bind] at executed
          | ok input =>
              exact .neg (ih run) (by simpa [evalExpr, run, bind, Except.bind] using executed)
      | binary op left right =>
          cases leftRun : evalExpr program locals fuel left with
          | error error => simp [evalExpr, leftRun, bind, Except.bind] at executed
          | ok leftValue =>
              cases rightRun : evalExpr program locals fuel right with
              | error error => simp [evalExpr, leftRun, rightRun, bind, Except.bind] at executed
              | ok rightValue =>
                  exact .binary (ih leftRun) (ih rightRun)
                    (by simpa [evalExpr, leftRun, rightRun, bind, Except.bind] using executed)
      | letValue pattern value body =>
          cases run : evalExpr program locals fuel value with
          | error error => simp [evalExpr, run, bind, Except.bind] at executed
          | ok input =>
              cases matched : pattern.bindings input with
              | none => simp [evalExpr, run, matched, bind, Except.bind, throw] at executed
              | some bindings =>
                  exact .letValue (ih run) matched
                    (ih (by simpa [evalExpr, run, matched, bind, Except.bind] using executed))
      | call name args =>
          cases argsRun : args.mapM (evalExpr program locals fuel) with
          | error error => simp [evalExpr, argsRun, bind, Except.bind] at executed
          | ok values =>
              cases prepared : prepareCall program name values with
              | error error => simp [evalExpr, argsRun, prepared, bind, Except.bind] at executed
              | ok binding =>
                  rcases binding with ⟨calleeLocals, body⟩
                  exact .call (evalArgs_of_mapM (fun _ _ run => ih run) argsRun)
                    (.intro prepared
                      (ih (by simpa [evalExpr, argsRun, prepared, bind, Except.bind] using executed)))
      | matchValue scrutinee arms =>
          cases run : evalExpr program locals fuel scrutinee with
          | error error => simp [evalExpr, run, bind, Except.bind] at executed
          | ok input =>
              cases selected : selectArm input arms with
              | none => simp [evalExpr, run, selected, bind, Except.bind, throw] at executed
              | some binding =>
                  rcases binding with ⟨bindings, body⟩
                  exact .matchValue (ih run) selected
                    (ih (by simpa [evalExpr, run, selected, bind, Except.bind] using executed))

theorem eval_eq_ok_iff [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List (Value F)} {fuel : Nat} {result : Value F} :
    eval program name args fuel = .ok result ↔
      typecheck program = .ok () ∧ ∃ locals expr,
        prepareCall program name args = .ok (locals, expr) ∧
        evalExpr program locals fuel expr = .ok result := by
  cases checked : typecheck program with
  | error error => simp [eval, checked, bind, Except.bind]
  | ok checkedUnit =>
      cases checkedUnit
      cases prepared : prepareCall program name args with
      | error error => simp [eval, checked, prepared, bind, pure, Except.bind, Except.pure]
      | ok binding =>
          rcases binding with ⟨locals, expr⟩
          simp only [eval, checked, prepared, bind, pure, Except.bind, Except.pure,
            Except.ok.injEq, Prod.mk.injEq, true_and]
          constructor
          · intro run; exact ⟨locals, expr, ⟨rfl, rfl⟩, run⟩
          · rintro ⟨_, _, ⟨rfl, rfl⟩, run⟩; exact run

theorem eval_spec [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List (Value F)} {fuel : Nat} {result : Value F}
    (executed : eval program name args fuel = .ok result) : EvalCall program name args result := by
  obtain ⟨_, locals, expr, prepared, body⟩ := eval_eq_ok_iff.mp executed
  exact .intro prepared (evalExpr_spec body)

/-- Every finite evaluation runs with all sufficiently large fuel bounds. -/
theorem EvalExpr.eventually_runs [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F} {expr : Expr F} {result : Value F}
    (evaluates : EvalExpr program locals expr result) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel → evalExpr program locals fuel expr = .ok result := by
  induction evaluates using EvalExpr.rec
    (motive_2 := fun locals exprs values _ =>
      ∃ minimum, ∀ fuel, minimum ≤ fuel → exprs.mapM (evalExpr program locals fuel) = .ok values)
    (motive_3 := fun name args result _ =>
      ∃ minimum, ∀ fuel, minimum ≤ fuel → ∃ locals expr,
        prepareCall program name args = .ok (locals, expr) ∧
          evalExpr program locals fuel expr = .ok result) with
  | literal =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rfl
  | var lookup =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [evalExpr, lookup, pure, Except.pure]
  | tuple _ ih =>
      obtain ⟨minimum, runs⟩ := ih
      refine ⟨minimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [evalExpr, runs fuel (by omega), bind, pure, Except.bind, Except.pure]
  | project _ projected ih | neg _ projected ih =>
      obtain ⟨minimum, runs⟩ := ih
      refine ⟨minimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [evalExpr, runs fuel (by omega), projected, bind, Except.bind]
  | binary _ _ operation leftIH rightIH =>
      obtain ⟨leftMinimum, leftRuns⟩ := leftIH
      obtain ⟨rightMinimum, rightRuns⟩ := rightIH
      refine ⟨max leftMinimum rightMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [evalExpr, leftRuns fuel (by omega), rightRuns fuel (by omega),
            operation, bind, Except.bind]
  | letValue _ matched _ valueIH bodyIH | matchValue _ matched _ valueIH bodyIH =>
      obtain ⟨valueMinimum, valueRuns⟩ := valueIH
      obtain ⟨bodyMinimum, bodyRuns⟩ := bodyIH
      refine ⟨max valueMinimum bodyMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simpa [evalExpr, valueRuns fuel (by omega), matched, bind, Except.bind]
            using bodyRuns fuel (by omega)
  | call _ _ argsIH callIH =>
      obtain ⟨argsMinimum, argsRuns⟩ := argsIH
      obtain ⟨callMinimum, callRuns⟩ := callIH
      refine ⟨max argsMinimum callMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          obtain ⟨locals, expr, prepared, bodyRun⟩ := callRuns fuel (by omega)
          simpa [evalExpr, argsRuns fuel (by omega), prepared, bind, Except.bind] using bodyRun
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | cons _ _ headIH tailIH =>
      obtain ⟨headMinimum, headRuns⟩ := headIH
      obtain ⟨tailMinimum, tailRuns⟩ := tailIH
      refine ⟨max headMinimum tailMinimum, ?_⟩
      intro fuel enough
      simp [List.mapM_cons, headRuns fuel (by omega), tailRuns fuel (by omega),
        bind, pure, Except.bind, Except.pure]
  | intro prepared _ bodyIH =>
      obtain ⟨minimum, runs⟩ := bodyIH
      exact ⟨minimum, fun fuel enough => ⟨_, _, prepared, runs fuel enough⟩⟩

theorem EvalCall.eventually_eval [Field F] [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {name : String}
    {args : List (Value F)} {result : Value F} (evaluates : EvalCall program name args result) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel → eval program name args fuel = .ok result := by
  cases evaluates with
  | intro prepared body =>
      obtain ⟨minimum, runs⟩ := body.eventually_runs
      exact ⟨minimum, fun fuel enough => eval_eq_ok_iff.mpr ⟨checked, _, _, prepared, runs fuel enough⟩⟩

theorem eval_complete [Field F] [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {name : String}
    {args : List (Value F)} {result : Value F} (evaluates : EvalCall program name args result) :
    ∃ fuel, eval program name args fuel = .ok result := by
  obtain ⟨minimum, runs⟩ := evaluates.eventually_eval checked
  exact ⟨minimum, runs minimum (Nat.le_refl _)⟩

theorem exists_eval_iff [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List (Value F)} {result : Value F} :
    (∃ fuel, eval program name args fuel = .ok result) ↔
      typecheck program = .ok () ∧ EvalCall program name args result := by
  constructor
  · rintro ⟨fuel, executed⟩
    exact ⟨(eval_eq_ok_iff.mp executed).1, eval_spec executed⟩
  · rintro ⟨checked, evaluated⟩
    exact eval_complete checked evaluated

theorem EvalExpr.deterministic [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F} {expr : Expr F} {left right : Value F}
    (first : EvalExpr program locals expr left) (second : EvalExpr program locals expr right) :
    left = right := by
  obtain ⟨a, leftRuns⟩ := first.eventually_runs
  obtain ⟨b, rightRuns⟩ := second.eventually_runs
  exact Except.ok.inj ((leftRuns (max a b) (Nat.le_max_left _ _)).symm.trans
    (rightRuns (max a b) (Nat.le_max_right _ _)))

theorem EvalCall.deterministic [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List (Value F)} {left right : Value F}
    (first : EvalCall program name args left) (second : EvalCall program name args right) :
    left = right := by
  cases first with
  | intro prepared body =>
      cases second with
      | intro otherPrepared otherBody =>
          cases Except.ok.inj (prepared.symm.trans otherPrepared)
          exact body.deterministic otherBody

end Aiur.Tuple
