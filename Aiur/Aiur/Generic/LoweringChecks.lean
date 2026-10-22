import Aiur.Generic.Consts

/-! Finite hygiene checks for compiler-generated pattern names. These checks
refer only to syntax, not to evaluation, termination, or semantic equivalence. -/

namespace Aiur.Generic.PatternLowering

def LetSafe (types : List (String × Ty)) : Pattern F → Aiur.Expr F → Aiur.Expr F → Prop
  | .load pat, value, body => LetSafe types pat (.load value) body
  | pat, value, body =>
      match pat.toCore? types with
      | some _ => True
      | none =>
          let stem := freshPrefix (pat.bindingNames ++ exprNames value ++ exprNames body)
          let root := stem ++ "0"
          let tree := (planTree types stem pat 1).1
          Consts.dependencies pat = [] ∧ (root :: tree.temps).Nodup ∧
            ∀ n ∈ exprNames body, n ∉ root :: tree.temps
termination_by pat _ _ => sizeOf pat

instance decidableLetSafe (types : List (String × Ty)) (pat : Pattern F) (value body : Aiur.Expr F) :
    Decidable (LetSafe types pat value body) := by
  cases pat with
  | load pat => unfold LetSafe; exact decidableLetSafe types pat (.load value) body
  | _ => unfold LetSafe; split <;> infer_instance
termination_by sizeOf pat

def ArmsSafe (types : List (String × Ty)) (stem root : String) :
    List (Pattern F × Aiur.Expr F) → Nat → Prop
  | [], _ => True
  | (pat, body) :: arms, state =>
      let generated := planTree types stem pat state
      let tree := generated.1
      let failure := (matchArms types stem root arms generated.2).1
      Consts.dependencies pat = [] ∧ (root :: tree.temps).Nodup ∧
        (∀ n ∈ exprNames body, n ∉ root :: tree.temps) ∧
        (∀ fallback ∈ failure.toList, ∀ n ∈ exprNames fallback, n ∉ tree.temps) ∧
        ArmsSafe types stem root arms generated.2

instance (types : List (String × Ty)) (stem root : String)
    (arms : List (Pattern F × Aiur.Expr F)) (state : Nat) :
    Decidable (ArmsSafe types stem root arms state) := by
  cases arms with
  | nil => unfold ArmsSafe; infer_instance
  | cons arm arms =>
      rcases arm with ⟨pat, body⟩
      unfold ArmsSafe
      haveI := instDecidableArmsSafe types stem root arms (planTree types stem pat state).2
      infer_instance

def MatchSafe (types : List (String × Ty)) (value : Aiur.Expr F)
    (arms : List (Pattern F × Aiur.Expr F)) : Prop :=
  match arms.mapM (fun arm => return (← arm.1.toCore? types, arm.2)) with
  | some _ => True
  | none =>
      let names := exprNames value ++ arms.flatMap (fun arm => arm.1.bindingNames ++ exprNames arm.2)
      let stem := freshPrefix names
      ArmsSafe types stem (stem ++ "0") arms 1

instance (types : List (String × Ty)) (value : Aiur.Expr F) (arms : List (Pattern F × Aiur.Expr F)) :
    Decidable (MatchSafe types value arms) := by unfold MatchSafe; split <;> infer_instance

end Aiur.Generic.PatternLowering

namespace Aiur.Generic

private def decideAll (xs : List A) (p : A → Prop)
    (dec : ∀ x ∈ xs, Decidable (p x)) : Decidable (∀ x ∈ xs, p x) := by
  cases xs with
  | nil => exact isTrue (by simp)
  | cons x xs =>
      haveI := dec x (by simp)
      haveI := decideAll xs p (fun y hy => dec y (by simp [hy]))
      exact decidable_of_iff (p x ∧ ∀ y ∈ xs, p y) (by simp)

/-- Checked on the prepared expression, after const expansion and before
lowering. Rejection is a compiler error, not a new source-language behavior. -/
def Expr.lowerSafe (types : List (String × Ty)) : Expr F → Prop
  | .literal _ | .var _ => True
  | .global _ _ | .control _ _ => False
  | .builtin _ xs | .update _ xs | .record _ xs | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs | .call _ _ xs =>
      ∀ x ∈ xs, x.lowerSafe types
  | .repeat x _ | .index x _ | .project x _ | .store x | .load x | .hint _ x channel | .neg x => x.lowerSafe types
  | .member x field => x.lowerSafe types ∧ field.index < field.arity
  | .slice x start (some stop) => start ≤ stop ∧ x.lowerSafe types
  | .slice _ _ none => False
  | .binary _ left right => left.lowerSafe types ∧ right.lowerSafe types
  | .letValue pat value body =>
      value.lowerSafe types ∧ body.lowerSafe types ∧
        PatternLowering.LetSafe types pat (value.lower types) (body.lower types)
  | .matchValue value arms =>
      value.lowerSafe types ∧ (∀ arm ∈ arms, arm.2.lowerSafe types) ∧
        PatternLowering.MatchSafe types (value.lower types) (arms.map fun arm => (arm.1, arm.2.lower types))
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

instance decidableLowerSafe (types : List (String × Ty)) (expr : Expr F) : Decidable (expr.lowerSafe types) := by
  have sub (e : Expr F) (smaller : sizeOf e < sizeOf expr) : Decidable (e.lowerSafe types) :=
    decidableLowerSafe types e
  cases expr with
  | literal _ | var _ | global _ _ | control _ _ => unfold Expr.lowerSafe; infer_instance
  | builtin _ xs | update _ xs | record _ xs | tuple xs | array xs | construct _ _ _ xs | constructAs _ _ _ xs | call _ _ xs =>
      unfold Expr.lowerSafe
      apply decideAll
      intro e he
      exact sub e (by simp_wf; have := List.sizeOf_lt_of_mem he; omega)
  | «repeat» x _ | index x _ | project x _ | store x | load x | hint _ x channel | neg x =>
      unfold Expr.lowerSafe; exact sub x (by simp_wf <;> omega)
  | member x field =>
      haveI := sub x (by simp_wf; omega)
      unfold Expr.lowerSafe; infer_instance
  | slice x start stop =>
      haveI := sub x (by simp_wf; omega)
      cases stop <;> unfold Expr.lowerSafe <;> infer_instance
  | binary _ left right =>
      haveI := sub left (by simp_wf; omega)
      haveI := sub right (by simp_wf; omega)
      unfold Expr.lowerSafe; infer_instance
  | letValue pat value body =>
      haveI := sub value (by simp_wf; omega)
      haveI := sub body (by simp_wf; omega)
      unfold Expr.lowerSafe; infer_instance
  | matchValue value arms =>
      haveI := sub value (by simp_wf; omega)
      haveI : Decidable (∀ arm ∈ arms, arm.2.lowerSafe types) := by
        apply decideAll
        intro arm ha
        exact sub arm.2 (by have := List.sizeOf_lt_of_mem ha; cases arm; simp_all only [Expr.matchValue.sizeOf_spec, Prod.mk.sizeOf_spec]; omega)
      unfold Expr.lowerSafe; infer_instance
termination_by sizeOf expr
decreasing_by exact smaller

end Aiur.Generic
