import Aiur.Scalar.Eval
import Aiur.Scalar.Semantics

namespace Aiur.Scalar

theorem SelectArm.find_eq [DecidableEq F] {value : F} {arms : List (Pattern F × Expr F)}
    {body : Expr F} (selected : SelectArm value arms body) :
    ∃ pattern, arms.find? (fun (pat, _) => pat.matches value) = some (pattern, body) := by
  induction selected with
  | literal => exact ⟨.literal value, by simp [List.find?, Pattern.matches]⟩
  | wildcard => exact ⟨.wildcard, by simp [List.find?, Pattern.matches]⟩
  | skip different _ ih =>
      obtain ⟨pattern, found⟩ := ih
      exact ⟨pattern, by simpa [List.find?, Pattern.matches, different] using found⟩

theorem SelectArm.of_find [DecidableEq F] {value : F} {arms : List (Pattern F × Expr F)}
    {pattern : Pattern F} {body : Expr F}
    (found : arms.find? (fun (pat, _) => pat.matches value) = some (pattern, body)) :
    SelectArm value arms body := by
  induction arms with
  | nil => simp at found
  | cons arm rest ih =>
      rcases arm with ⟨headPattern, headBody⟩
      cases headPattern with
      | wildcard =>
          simp [List.find?, Pattern.matches] at found
          rcases found with ⟨rfl, rfl⟩
          exact .wildcard
      | literal literal =>
          by_cases same : literal = value
          · subst literal
            simp [List.find?, Pattern.matches] at found
            rcases found with ⟨rfl, rfl⟩
            exact .literal
          · exact .skip same (ih (by simpa [List.find?, Pattern.matches, same] using found))

private theorem evalArgs_of_mapM [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F} {fuel : Nat}
    (sound : ∀ expr result, evalExpr program locals fuel expr = .ok result →
      EvalExpr program locals expr result)
    {args : List (Expr F)} {values : List F}
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

/-- Every successful executable expression evaluation has a fuel-free derivation. -/
theorem evalExpr_spec [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F} {fuel : Nat} {expr : Expr F} {result : F}
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
      | neg expr =>
          cases innerRun : evalExpr program locals fuel expr with
          | error error => simp [evalExpr, innerRun, bind, Except.bind] at executed
          | ok value =>
              simp [evalExpr, innerRun, bind, pure, Except.bind, Except.pure] at executed
              subst result
              exact .neg (ih innerRun)
      | binary op left right =>
          cases leftRun : evalExpr program locals fuel left with
          | error error => simp [evalExpr, leftRun, bind, Except.bind] at executed
          | ok leftValue =>
              cases rightRun : evalExpr program locals fuel right with
              | error error => simp [evalExpr, leftRun, rightRun, bind, Except.bind] at executed
              | ok rightValue =>
                  have operation : evalBinOp op leftValue rightValue = .ok result := by
                    simpa [evalExpr, leftRun, rightRun, bind, Except.bind] using executed
                  cases op with
                  | add =>
                      simp [evalBinOp] at operation
                      subst result
                      exact .add (ih leftRun) (ih rightRun)
                  | sub =>
                      simp [evalBinOp] at operation
                      subst result
                      exact .sub (ih leftRun) (ih rightRun)
                  | mul =>
                      simp [evalBinOp] at operation
                      subst result
                      exact .mul (ih leftRun) (ih rightRun)
                  | div =>
                      by_cases zero : rightValue = 0
                      · simp [evalBinOp, zero] at operation
                      · simp [evalBinOp, zero] at operation
                        subst result
                        exact .div (ih leftRun) (ih rightRun) zero
      | call name args =>
          cases found : program.findFunction? name with
          | none => simp [evalExpr, found, throw] at executed
          | some defn =>
              by_cases arity : defn.params.length = args.length
              · cases argsRun : args.mapM (evalExpr program locals fuel) with
                | error error =>
                    simp [evalExpr, found, arity, argsRun, bind, pure, Except.bind, Except.pure] at executed
                | ok values =>
                    have arguments := evalArgs_of_mapM (fun _ _ run => ih run) argsRun
                    have bodyRun : evalExpr program (defn.params.zip values) fuel defn.body = .ok result := by
                      simpa [evalExpr, found, arity, argsRun, bind, pure, Except.bind, Except.pure] using executed
                    exact .call arguments (.intro found (arity.trans arguments.length_eq) (ih bodyRun))
              · simp [evalExpr, found, arity, bind, Except.bind] at executed
      | matchValue scrutinee arms =>
          cases scrutineeRun : evalExpr program locals fuel scrutinee with
          | error error => simp [evalExpr, scrutineeRun, bind, Except.bind] at executed
          | ok value =>
              cases found : arms.find? (fun (pat, _) => pat.matches value) with
              | none => simp [evalExpr, scrutineeRun, found, bind, Except.bind, throw] at executed
              | some arm =>
                  rcases arm with ⟨pattern, body⟩
                  have bodyRun : evalExpr program locals fuel body = .ok result := by
                    simpa [evalExpr, scrutineeRun, found, bind, Except.bind] using executed
                  exact .matchValue (ih scrutineeRun) (.of_find found) (ih bodyRun)

/-- The public evaluator checks the program, resolves the entry, and executes its body. -/
theorem eval_eq_ok_iff [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List F} {fuel : Nat} {result : F} :
    eval program name args fuel = .ok result ↔
      typecheck program = .ok () ∧ ∃ defn, program.findFunction? name = some defn ∧
        defn.params.length = args.length ∧
        evalExpr program (defn.params.zip args) fuel defn.body = .ok result := by
  cases checked : typecheck program with
  | error error => simp [eval, checked, bind, Except.bind]
  | ok checkedUnit =>
      cases checkedUnit
      cases found : program.findFunction? name with
      | none => simp [eval, checked, found, bind, pure, Except.bind, Except.pure, throw]
      | some defn =>
          by_cases arity : defn.params.length = args.length <;>
            simp [eval, checked, found, arity, bind, pure, Except.bind, Except.pure]

/-- `eval = .ok result` implies the evaluation predicate, for every fuel bound. -/
theorem eval_spec [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List F} {fuel : Nat} {result : F}
    (executed : eval program name args fuel = .ok result) : EvalCall program name args result := by
  obtain ⟨_, defn, found, arity, body⟩ := eval_eq_ok_iff.mp executed
  exact .intro found arity (evalExpr_spec body)

/-- A finite expression derivation executes successfully at every sufficiently large fuel bound. -/
theorem EvalExpr.eventually_runs [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F} {expr : Expr F} {result : F}
    (evaluates : EvalExpr program locals expr result) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel → evalExpr program locals fuel expr = .ok result := by
  induction evaluates using EvalExpr.rec
    (motive_2 := fun locals exprs values _ =>
      ∃ minimum, ∀ fuel, minimum ≤ fuel → exprs.mapM (evalExpr program locals fuel) = .ok values)
    (motive_3 := fun name args result _ =>
      ∃ minimum, ∀ fuel, minimum ≤ fuel →
        ∃ defn, program.findFunction? name = some defn ∧ defn.params.length = args.length ∧
          evalExpr program (defn.params.zip args) fuel defn.body = .ok result) with
  | literal =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [evalExpr, pure, Except.pure]
  | var lookup =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => simp [evalExpr, lookup, pure, Except.pure]
  | neg _ ih =>
      obtain ⟨minimum, runs⟩ := ih
      refine ⟨minimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [evalExpr, runs fuel (by omega), bind, pure, Except.bind, Except.pure]
  | add _ _ leftIH rightIH | sub _ _ leftIH rightIH | mul _ _ leftIH rightIH =>
      obtain ⟨leftMinimum, leftRuns⟩ := leftIH
      obtain ⟨rightMinimum, rightRuns⟩ := rightIH
      refine ⟨max leftMinimum rightMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [evalExpr, leftRuns fuel (by omega), rightRuns fuel (by omega),
            evalBinOp, bind, Except.bind]
  | div _ _ nonzero leftIH rightIH =>
      obtain ⟨leftMinimum, leftRuns⟩ := leftIH
      obtain ⟨rightMinimum, rightRuns⟩ := rightIH
      refine ⟨max leftMinimum rightMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [evalExpr, leftRuns fuel (by omega), rightRuns fuel (by omega),
            evalBinOp, nonzero, bind, Except.bind]
  | call arguments _ argumentsIH calleeIH =>
      obtain ⟨argsMinimum, argsRuns⟩ := argumentsIH
      obtain ⟨callMinimum, callRuns⟩ := calleeIH
      refine ⟨max argsMinimum callMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          obtain ⟨defn, lookup, arity, bodyRun⟩ := callRuns fuel (by omega)
          have syntaxArity := arity.trans arguments.length_eq.symm
          simpa [evalExpr, lookup, syntaxArity, argsRuns fuel (by omega),
            bind, pure, Except.bind, Except.pure] using bodyRun
  | matchValue _ selected _ scrutineeIH branchIH =>
      obtain ⟨scrutineeMinimum, scrutineeRuns⟩ := scrutineeIH
      obtain ⟨branchMinimum, branchRuns⟩ := branchIH
      obtain ⟨pattern, found⟩ := selected.find_eq
      refine ⟨max scrutineeMinimum branchMinimum + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simpa [evalExpr, scrutineeRuns fuel (by omega), found, bind, Except.bind]
            using branchRuns fuel (by omega)
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | cons _ _ headIH tailIH =>
      obtain ⟨headMinimum, headRuns⟩ := headIH
      obtain ⟨tailMinimum, tailRuns⟩ := tailIH
      refine ⟨max headMinimum tailMinimum, ?_⟩
      intro fuel enough
      simp [List.mapM_cons, headRuns fuel (by omega), tailRuns fuel (by omega),
        bind, pure, Except.bind, Except.pure]
  | intro lookup arity _ bodyIH =>
      obtain ⟨minimum, bodyRuns⟩ := bodyIH
      exact ⟨minimum, fun fuel enough => ⟨_, lookup, arity, bodyRuns fuel enough⟩⟩

/-- The program check is the only extra condition imposed by the public evaluator. -/
theorem EvalCall.eventually_eval [Field F] [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {name : String} {args : List F} {result : F}
    (evaluates : EvalCall program name args result) :
    ∃ minimum, ∀ fuel, minimum ≤ fuel → eval program name args fuel = .ok result := by
  cases evaluates with
  | intro lookup arity body =>
      obtain ⟨minimum, runs⟩ := body.eventually_runs
      exact ⟨minimum, fun fuel enough => eval_eq_ok_iff.mpr ⟨checked, _, lookup, arity, runs fuel enough⟩⟩

/-- Every successful source call in a checked program can be run with enough fuel. -/
theorem eval_complete [Field F] [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {name : String} {args : List F} {result : F}
    (evaluates : EvalCall program name args result) :
    ∃ fuel, eval program name args fuel = .ok result := by
  obtain ⟨minimum, runs⟩ := evaluates.eventually_eval checked
  exact ⟨minimum, runs minimum (Nat.le_refl _)⟩

/-- Exact correspondence for the checked public evaluator, quantifying over sufficient fuel. -/
theorem exists_eval_iff [Field F] [DecidableEq F] {program : Program F}
    {name : String} {args : List F} {result : F} :
    (∃ fuel, eval program name args fuel = .ok result) ↔
      typecheck program = .ok () ∧ EvalCall program name args result := by
  constructor
  · rintro ⟨fuel, executed⟩
    exact ⟨(eval_eq_ok_iff.mp executed).1, eval_spec executed⟩
  · rintro ⟨checked, evaluated⟩
    exact eval_complete checked evaluated

end Aiur.Scalar
