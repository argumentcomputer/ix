import Aiur.Inlining.Tree
import Aiur.Generic.PatternBindingsFacts
import Aiur.Semantics.CallTypes

namespace Aiur.Inlining
open Generic

def choose [DecidableEq F] (value : SourceValue F) :
    List (Aiur.Pattern F × A) → Option (Environment F Nat × A)
  | [] => none
  | (pat,body) :: rest => match pat.bindings value with
    | none => choose value rest
    | some bs => some (bs,body)

theorem select_map [DecidableEq F] (value : SourceValue F) (arms : List (Aiur.Pattern F × A))
    (f : A → Aiur.Expr F) :
    selectArm value (arms.map fun a => (a.1,f a.2)) = (choose value arms).map (fun a => (a.1,f a.2)) := by
  induction arms with
  | nil => rfl
  | cons a rest ih =>
      rcases a with ⟨pat,body⟩
      cases h : pat.bindings value <;> simp [selectArm,choose,h,ih]

theorem choose_member [DecidableEq F] {arms : List (Aiur.Pattern F × A)}
    (selected : choose input arms = some (bs,body)) :
    ∃ pat, (pat,body) ∈ arms ∧ pat.bindings input = some bs := by
  induction arms with
  | nil => simp [choose] at selected
  | cons arm rest ih =>
      rcases arm with ⟨pat,expr⟩
      cases matched : pat.bindings input with
      | none =>
          obtain ⟨p,hp,hm⟩ := ih (by simpa [choose,matched] using selected)
          exact ⟨p,by simp [hp],hm⟩
      | some bindings =>
          obtain ⟨rfl,rfl⟩ := (by simpa [choose,matched] using selected : bindings = bs ∧ expr = body)
          exact ⟨pat,by simp,matched⟩

theorem Tree.checkTypes_infer {tree : Tree F} (checked : tree.checkTypes q locals = some type) :
    inferType q "$inline" locals tree.target = .ok type := by
  rw [Tree.checkTypes.eq_def] at checked
  obtain ⟨t,typed,rest⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨_,_,same⟩ := Option.map_eq_some_iff.mp rest
  cases same
  exact except_toOption_some_iff.mp typed

theorem Tree.typed [Field F] [DecidableEq F] {q : Aiur.Program F} {tree : Tree F}
    (programChecked : typecheck q = .ok ())
    (closed : ∀ n args b v a, calls n args b v a → Aiur.EvalFn q n args b v a)
    (ev : OpenCore.EvalExpr (.ofProgram q) calls locals tree.target before result after)
    (memory : before.Good q.enums) (values : locals.Good q.enums)
    (checked : tree.checkTypes q (environmentTypes locals) = some type) :
    result.type = type ∧ result.Good q.enums ∧ after.Good q.enums :=
  (ev.toProgram closed).wellTyped programChecked memory values "$inline" type
    (Tree.checkTypes_infer checked)

end Aiur.Inlining
