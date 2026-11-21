import Aiur.Semantics.CallTypes

namespace Aiur

@[simp] theorem Constant.toExpr_noHints (value : Constant F) : value.toExpr.noHints = true := by
  cases value with
  | field => simp [Constant.toExpr, Expr.noHints]
  | ptr _ address => exact Empty.elim address
  | tuple values | construct _ _ values =>
      simp only [Constant.toExpr, Expr.noHints, List.map_map, List.all_map, List.all_eq_true]
      exact fun value _ => Constant.toExpr_noHints value
termination_by sizeOf value

theorem prepareCall_noHints [DecidableEq F] {program : Program F}
    (safe : program.noHints = true) {name : String} {args : List (Value F A)}
    {locals : Environment F A} {body : Expr F}
    (prepared : prepareCall program name args = .ok (locals, body)) : body.noHints = true := by
  rcases prepareCall_spec prepared with function | table
  · obtain ⟨function, found, _, _, _, rfl⟩ := function
    exact (by simpa [Program.noHints] using safe : ∀ f ∈ program.functions, f.body.noHints = true)
      function (List.mem_of_find?_eq_some found)
  · obtain ⟨value, _, _, _, rfl⟩ := table
    exact value.toExpr_noHints

theorem selectArm_noHints [DecidableEq F] {value : Value F A}
    {arms : List (Pattern F × Expr F)} {bindings : Environment F A} {body : Expr F}
    (safe : ∀ arm ∈ arms, arm.2.noHints = true)
    (selected : selectArm value arms = some (bindings, body)) : body.noHints = true := by
  induction arms with
  | nil => cases selected
  | cons arm arms ih =>
      simp only [selectArm] at selected
      split at selected
      · cases selected; exact safe arm (by simp)
      · exact ih (fun a h => safe a (by simp [h])) selected

end Aiur
