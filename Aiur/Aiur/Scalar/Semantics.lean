import Aiur.Scalar.AST
import Mathlib.Algebra.Field.Defs

namespace Aiur.Scalar

abbrev Environment (F : Type) := List (String × F)

/-- Select the first matching arm. There is no rule for skipping a wildcard. -/
inductive SelectArm (value : F) : List (Pattern F × Expr F) → Expr F → Prop where
  | literal : SelectArm value ((.literal value, body) :: rest) body
  | wildcard : SelectArm value ((.wildcard, body) :: rest) body
  | skip (different : pattern ≠ value) (next : SelectArm value rest body) :
      SelectArm value ((.literal pattern, other) :: rest) body

theorem SelectArm.deterministic {value : F} {arms : List (Pattern F × Expr F)}
    {left right : Expr F} (first : SelectArm value arms left)
    (second : SelectArm value arms right) : left = right := by
  induction first with
  | literal => cases second <;> simp_all
  | wildcard => cases second <;> rfl
  | skip different _ ih =>
      cases second with
      | literal => exact (different rfl).elim
      | skip _ next => exact ih next

mutual
  /-- Successful expression evaluation, with finite derivations and no fuel. -/
  inductive EvalExpr [Field F] (program : Program F) : Environment F → Expr F → F → Prop where
    | literal : EvalExpr program locals (.literal value) value
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExpr program locals (.var name) value
    | neg (operand : EvalExpr program locals expr value) :
        EvalExpr program locals (.neg expr) (-value)
    | add (left : EvalExpr program locals lhs x) (right : EvalExpr program locals rhs y) :
        EvalExpr program locals (.binary .add lhs rhs) (x + y)
    | sub (left : EvalExpr program locals lhs x) (right : EvalExpr program locals rhs y) :
        EvalExpr program locals (.binary .sub lhs rhs) (x - y)
    | mul (left : EvalExpr program locals lhs x) (right : EvalExpr program locals rhs y) :
        EvalExpr program locals (.binary .mul lhs rhs) (x * y)
    | div (left : EvalExpr program locals lhs x) (right : EvalExpr program locals rhs y)
        (nonzero : y ≠ 0) :
        EvalExpr program locals (.binary .div lhs rhs) (x / y)
    | call (arguments : EvalArgs program locals args values)
        (callee : EvalCall program name values result) :
        EvalExpr program locals (.call name args) result
    | matchValue (scrutinee : EvalExpr program locals expr value)
        (selected : SelectArm value arms body) (branch : EvalExpr program locals body result) :
        EvalExpr program locals (.matchValue expr arms) result

  /-- Each argument is evaluated in the caller's environment, preserving its position. -/
  inductive EvalArgs [Field F] (program : Program F) :
      Environment F → List (Expr F) → List F → Prop where
    | nil : EvalArgs program locals [] []
    | cons (head : EvalExpr program locals expr value)
        (tail : EvalArgs program locals exprs values) :
        EvalArgs program locals (expr :: exprs) (value :: values)

  /-- A function call binds exactly its parameters and evaluates its body. -/
  inductive EvalCall [Field F] (program : Program F) : String → List F → F → Prop where
    | intro (lookup : program.findFunction? name = some defn)
        (arity : defn.params.length = args.length)
        (body : EvalExpr program (defn.params.zip args) defn.body result) :
        EvalCall program name args result
end

theorem EvalArgs.length_eq [Field F] {program : Program F}
    {locals : Environment F} {exprs : List (Expr F)} {values : List F}
    (evaluates : EvalArgs program locals exprs values) : exprs.length = values.length := by
  induction evaluates using EvalArgs.rec
    (motive_1 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True) <;> simp_all

/-- Unknown functions and calls with the wrong arity cannot have derivations. -/
theorem EvalCall.function_exists [Field F] {program : Program F} {name : String}
    {args : List F} {result : F} (evaluates : EvalCall program name args result) :
    ∃ defn, program.findFunction? name = some defn ∧ defn.params.length = args.length := by
  cases evaluates with
  | intro lookup arity _ => exact ⟨_, lookup, arity⟩

/-- A finite source evaluation determines its result uniquely. -/
theorem EvalExpr.deterministic [Field F] {program : Program F}
    {locals : Environment F} {expr : Expr F} {left right : F}
    (first : EvalExpr program locals expr left) (second : EvalExpr program locals expr right) :
    left = right := by
  induction first using EvalExpr.rec
    (motive_2 := fun locals exprs values _ =>
      ∀ other, EvalArgs program locals exprs other → values = other)
    (motive_3 := fun name args value _ =>
      ∀ other, EvalCall program name args other → value = other) generalizing right with
  | literal => cases second; rfl
  | var lookup => cases second; simp_all
  | neg _ ih =>
      cases second with
      | neg operand => rw [ih operand]
  | add _ _ leftIH rightIH =>
      cases second with
      | add left right => rw [leftIH left, rightIH right]
  | sub _ _ leftIH rightIH =>
      cases second with
      | sub left right => rw [leftIH left, rightIH right]
  | mul _ _ leftIH rightIH =>
      cases second with
      | mul left right => rw [leftIH left, rightIH right]
  | div _ _ _ leftIH rightIH =>
      cases second with
      | div left right _ => rw [leftIH left, rightIH right]
  | call _ _ argumentsIH calleeIH =>
      cases second with
      | call arguments callee =>
          cases argumentsIH _ arguments
          exact calleeIH _ callee
  | matchValue _ selected _ scrutineeIH branchIH =>
      cases second with
      | matchValue scrutinee otherSelected branch =>
          cases scrutineeIH scrutinee
          cases selected.deterministic otherSelected
          exact branchIH branch
  | nil => rename_i other evaluated; cases evaluated; rfl
  | cons _ _ headIH tailIH =>
      rename_i other evaluated
      cases evaluated with
      | cons head tail =>
          cases headIH head
          cases tailIH _ tail
          rfl
  | intro lookup _ _ bodyIH =>
      rename_i other evaluated
      cases evaluated with
      | intro otherLookup _ body =>
          have same := Option.some.inj (lookup.symm.trans otherLookup)
          cases same
          exact bodyIH body

theorem EvalCall.deterministic [Field F] {program : Program F} {name : String}
    {args : List F} {left right : F} (first : EvalCall program name args left)
    (second : EvalCall program name args right) : left = right := by
  cases first with
  | intro lookup _ body =>
      cases second with
      | intro otherLookup _ otherBody =>
          have same := Option.some.inj (lookup.symm.trans otherLookup)
          cases same
          exact body.deterministic otherBody

end Aiur.Scalar
