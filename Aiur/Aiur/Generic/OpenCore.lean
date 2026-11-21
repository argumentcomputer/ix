import Aiur.Generic.Engine

/-! A proof interface for expression evaluation with calls left as premises.
It adds no compiler or execution phase. Closing the premises with `EvalFn`
recovers the existing evaluator exactly. -/

namespace Aiur.Generic

abbrev CallRelation (F : Type) :=
  String → List (SourceValue F) → Heap F → SourceValue F → Heap F → Prop

namespace OpenCore

mutual
  /-- Finite source evaluation threads a fresh-allocation heap, with no fuel. -/
  inductive EvalExpr [Field F] [DecidableEq F] (world : Engine.World F) (calls : CallRelation F) :
      Environment F Nat → Aiur.Expr F → Heap F → SourceValue F → Heap F → Prop where
    | literal : EvalExpr world calls locals (.literal value) heap (.field value) heap
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExpr world calls locals (.var name) heap value heap
    | tuple (items : EvalArgs world calls locals exprs before values after) :
        EvalExpr world calls locals (.tuple exprs) before (.tuple values) after
    | construct (items : EvalArgs world calls locals exprs before values after) :
        EvalExpr world calls locals (.construct name ctor exprs) before (.construct name ctor values) after
    | project (value : EvalExpr world calls locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr world calls locals (.project expr index) before result after
    | letValue (value : EvalExpr world calls locals expr before input middle)
        (matched : pattern.bindings input = some bindings)
        (body : EvalExpr world calls (bindings ++ locals) rest middle result after) :
        EvalExpr world calls locals (.letValue pattern expr rest) before result after
    | store (value : EvalExpr world calls locals expr before input middle) :
        EvalExpr world calls locals (.store expr) before (.ptr input.type middle.length) (middle ++ [input])
    | load (pointer : EvalExpr world calls locals expr before input after)
        (loaded : loadValue after input = .ok result) :
        EvalExpr world calls locals (.load expr) before result after
    | hint (key : EvalExpr world calls locals expr before input after)
        {value : Constant F} (typed : world.typed type value = true) :
        EvalExpr world calls locals (.hint type expr channel) before value.toValue after
    | neg (value : EvalExpr world calls locals expr before input after)
        (operation : evalNeg input = .ok result) :
        EvalExpr world calls locals (.neg expr) before result after
    | assertEq (left : EvalExpr world calls locals lhs before x middle)
        (right : EvalExpr world calls locals rhs middle y after)
        (operation : evalAssertEq op x y = .ok result) :
        EvalExpr world calls locals (.assertEq op lhs rhs) before result after
    | binary (left : EvalExpr world calls locals lhs before x middle)
        (right : EvalExpr world calls locals rhs middle y after)
        (operation : evalBinOp op x y = .ok result) :
        EvalExpr world calls locals (.binary op lhs rhs) before result after
    | call (arguments : EvalArgs world calls locals args before values middle)
        (callee : calls name values middle result after) :
        EvalExpr world calls locals (.call name args) before result after
    | matchValue (value : EvalExpr world calls locals expr before input middle)
        (selected : selectArm input arms = some (bindings, body))
        (branch : EvalExpr world calls (bindings ++ locals) body middle result after) :
        EvalExpr world calls locals (.matchValue expr arms) before result after

  inductive EvalArgs [Field F] [DecidableEq F] (world : Engine.World F) (calls : CallRelation F) :
      Environment F Nat → List (Aiur.Expr F) → Heap F → List (SourceValue F) → Heap F → Prop where
    | nil : EvalArgs world calls locals [] heap [] heap
    | cons (head : EvalExpr world calls locals expr before value middle)
        (tail : EvalArgs world calls locals exprs middle values after) :
        EvalArgs world calls locals (expr :: exprs) before (value :: values) after

end

variable [Field F] [DecidableEq F] {world : Engine.World F} {calls other : CallRelation F}

theorem EvalExpr.mapCalls
    (h : EvalExpr world calls locals expr before result after)
    (transfer : ∀ n args b v a, calls n args b v a → other n args b v a) :
    EvalExpr world other locals expr before result after := by
  induction h using EvalExpr.rec
    (motive_2 := fun ls es b vs a _ => EvalArgs world other ls es b vs a) with
  | literal => exact .literal
  | var h => exact .var h
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | project _ h ih => exact .project ih h
  | letValue _ h _ ih1 ih2 => exact .letValue ih1 h ih2
  | store _ ih => exact .store ih
  | load _ h ih => exact .load ih h
  | hint _ h ih => exact .hint ih h
  | neg _ h ih => exact .neg ih h
  | assertEq _ _ h ih1 ih2 => exact .assertEq ih1 ih2 h
  | binary _ _ h ih1 ih2 => exact .binary ih1 ih2 h
  | matchValue _ h _ ih1 ih2 => exact .matchValue ih1 h ih2
  | nil => exact .nil
  | cons _ _ ih1 ih2 => exact .cons ih1 ih2
  | call _ callee ih => exact .call ih (transfer _ _ _ _ _ callee)

theorem EvalExpr.close
    (h : EvalExpr world (Engine.EvalFn world) locals expr before result after) :
    Engine.EvalExpr world locals expr before result after := by
  induction h using EvalExpr.rec
    (motive_2 := fun ls es b vs a _ => Engine.EvalArgs world ls es b vs a) with
  | literal => exact .literal
  | var h => exact .var h
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | project _ h ih => exact .project ih h
  | letValue _ h _ ih1 ih2 => exact .letValue ih1 h ih2
  | store _ ih => exact .store ih
  | load _ h ih => exact .load ih h
  | hint _ h ih => exact .hint ih h
  | neg _ h ih => exact .neg ih h
  | assertEq _ _ h ih1 ih2 => exact .assertEq ih1 ih2 h
  | binary _ _ h ih1 ih2 => exact .binary ih1 ih2 h
  | matchValue _ h _ ih1 ih2 => exact .matchValue ih1 h ih2
  | nil => exact .nil
  | cons _ _ ih1 ih2 => exact .cons ih1 ih2
  | call _ callee ih => exact .call ih callee

theorem of_closed
    (h : Engine.EvalExpr world locals expr before result after) :
    EvalExpr world (Engine.EvalFn world) locals expr before result after := by
  induction h using Engine.EvalExpr.rec
    (motive_2 := fun ls es b vs a _ => EvalArgs world (Engine.EvalFn world) ls es b vs a)
    (motive_3 := fun _ _ _ _ _ _ => True) with
  | literal => exact .literal
  | var h => exact .var h
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | project _ h ih => exact .project ih h
  | letValue _ h _ ih1 ih2 => exact .letValue ih1 h ih2
  | store _ ih => exact .store ih
  | load _ h ih => exact .load ih h
  | hint _ h ih => exact .hint ih h
  | neg _ h ih => exact .neg ih h
  | assertEq _ _ h ih1 ih2 => exact .assertEq ih1 ih2 h
  | binary _ _ h ih1 ih2 => exact .binary ih1 ih2 h
  | matchValue _ h _ ih1 ih2 => exact .matchValue ih1 h ih2
  | nil => exact .nil
  | cons _ _ ih1 ih2 => exact .cons ih1 ih2
  | call _ callee ih _ => exact .call ih callee
  | intro => trivial

theorem closed_iff :
    EvalExpr world (Engine.EvalFn world) locals expr before result after ↔
      Engine.EvalExpr world locals expr before result after :=
  ⟨EvalExpr.close, of_closed⟩

end OpenCore
end Aiur.Generic
