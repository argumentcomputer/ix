import Aiur.Generic.PatternTypeFacts
import Aiur.Generic.PatternTranslation
import Aiur.Generic.OpenCore
import Aiur.Generic.Simulation

namespace Aiur.Generic

theorem except_toOption_some_iff {value : Except E A} : value.toOption = some x ↔ value = .ok x := by
  cases value <;> simp [Except.toOption]

theorem option_mapM_hasResult {f : A → Option B} {xs : List A} {ys : List B}
    (mapped : xs.mapM f = some ys) : ∀ x ∈ xs, ∃ y, f x = some y := by
  have related := option_mapM_relation mapped
  clear mapped
  induction related with
  | nil => simp
  | @cons x y xs ys head _ ih =>
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨y, head⟩
      · exact ih value member

theorem Expr.checkLowerTypes_infer {expr : Expr F} {program : Aiur.Program F}
    (checked : expr.checkLowerTypes program types locals = some result) :
    inferType program "$lower" locals (expr.lower types) = .ok result := by
  rw [Expr.checkLowerTypes.eq_def] at checked
  obtain ⟨type, inferred, checked⟩ := Option.bind_eq_some_iff.mp checked
  split at checked
  · cases checked
  · obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp checked
    cases same
    exact except_toOption_some_iff.mp inferred

theorem Expr.checkLowerTypes_scope {expr : Expr F} {program : Aiur.Program F}
    (checked : expr.checkLowerTypes program types locals = some result) :
    Engine.inScope (program.functions.map (·.name) ++ program.maps.map (·.name))
      (knownType program.enums) (expr.lower types) = true := by
  rw [Expr.checkLowerTypes.eq_def] at checked
  obtain ⟨_, _, checked⟩ := Option.bind_eq_some_iff.mp checked
  split at checked
  · cases checked
  · rename_i scope
    simpa using scope

theorem OpenCore.EvalExpr.toProgram [Field F] [DecidableEq F] {program : Aiur.Program F}
    (evaluated : OpenCore.EvalExpr (.ofProgram program) calls locals expr before result after)
    (closed : ∀ n args b v a, calls n args b v a → Aiur.EvalFn program n args b v a) :
    Aiur.EvalExpr program locals expr before result after :=
  (evaluated.mapCalls (fun _ _ _ _ _ h => Engine.core_iff.mpr (closed _ _ _ _ _ h))).close.toCore

theorem OpenCore.EvalExpr.lowerTyped [Field F] [DecidableEq F] {program : Aiur.Program F}
    {expr : Expr F}
    (checkedProgram : typecheck program = .ok ())
    (evaluated : OpenCore.EvalExpr (.ofProgram program) calls locals (expr.lower types) before result after)
    (closed : ∀ n args b v a, calls n args b v a → Aiur.EvalFn program n args b v a)
    (heapGood : before.Good program.enums) (localsGood : locals.Good program.enums)
    (checked : expr.checkLowerTypes program types (environmentTypes locals) = some type) :
    result.type = type ∧ result.Good program.enums ∧ after.Good program.enums :=
  (evaluated.toProgram closed).wellTyped checkedProgram heapGood localsGood "$lower" type
    (Expr.checkLowerTypes_infer checked)

end Aiur.Generic
