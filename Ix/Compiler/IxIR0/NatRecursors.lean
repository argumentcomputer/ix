import Ix.Compiler.IxIR0.NatArithmetic

namespace Ix.Compiler.IxIR0.NatArithmetic
open Ix.Compiler.Ixon (Address)
open Recursion

/-- The ordinary usage checker requires a shared literal producer at these
shared call sites. Erasure retains this constant closure application. -/
def sharedLiteral (number : Nat) : Expr := .app (.lam .many (.lit (.nat number))) .erased

theorem sharedLiteral_evaluates (ctx : Ctx) (environment : List Value) (number : Nat) :
    Evaluates ctx environment (sharedLiteral number) (.lit (.nat number)) :=
  evaluatesApp (evaluatesLam _ _ _ _) (evaluatesErased _ _) (appliesClosure (evaluatesLit _ _ _))

def fold (step : Nat → Nat → Nat) (initial : Nat) : Nat → Nat
  | 0 => initial
  | n + 1 => step n (fold step initial n)

/-- A reusable mathematical contract for the canonical recursor. Its step
is an ordinary source closure and may itself call other proved functions. -/
theorem recursor_fold {ctx : Ctx} {schema : Schema} (matched : Matches ctx schema)
    (step : Nat → Nat → Nat) (function : Value)
    (stepApplies : ∀ predecessor argument m n, Represents schema predecessor m → Represents schema argument n →
      ∃ closure result, Applies ctx function predecessor closure ∧ Applies ctx closure argument result ∧
        Represents schema result (step m n))
    {initial major : Value} {m n : Nat} (initialValue : Represents schema initial m) (majorValue : Represents schema major n) :
    ∃ result, Applies ctx (.pap (.rec_ schema.recursor 3) [initial, function]) major result ∧
      Represents schema result (fold step m n) := by
  have zero : Applies ctx (.pap (.rec_ schema.recursor 3) [initial, function]) (.lit (.nat 0)) initial := by
    apply appliesRecursorView matched.recursor rfl rfl rfl rfl
    exact evaluatesVar rfl
  have successor {major predecessor result : Value} {number : Nat}
      (view : majorCtor true major = .ok (1, [predecessor])) (predecessorValue : Represents schema predecessor number)
      (recursive : Applies ctx (.pap (.rec_ schema.recursor 3) [initial, function]) predecessor result)
      (represented : Represents schema result (fold step m number)) :
      ∃ result, Applies ctx (.pap (.rec_ schema.recursor 3) [initial, function]) major result ∧
        Represents schema result (fold step m (number + 1)) := by
    obtain ⟨closure, result, first, second, represented⟩ := stepApplies predecessor result number _ predecessorValue represented
    refine ⟨result, ?_, represented⟩
    apply appliesRecursorView matched.recursor rfl view rfl rfl
    refine evaluatesApp (evaluatesApp (evaluatesVar rfl) (evaluatesVar rfl) first) ?_ second
    exact evaluatesApp
      (evaluatesApp (evaluatesApp (evaluatesVar rfl) (evaluatesVar rfl) (appliesRecursorFirst _ _ _))
        (evaluatesVar rfl) (appliesRecursorSecond _ _ _ _))
      (evaluatesVar rfl) recursive
  induction majorValue with
  | literal n =>
      induction n with
      | zero => exact ⟨initial, zero, initialValue⟩
      | succ n ih =>
          obtain ⟨result, recursive, represented⟩ := ih
          exact successor rfl (.literal n) recursive represented
  | successor predecessor ih =>
      obtain ⟨result, recursive, represented⟩ := ih
      exact successor rfl predecessor recursive represented

def predStep : Expr := .lam .many (.lam .many (.var 1))
def predExpression (schema : Schema) : Expr :=
  .app (.app (.app (.ref schema.alias) (sharedLiteral 0)) predStep) (.var 0)
def predBody (schema : Schema) : Expr := .lam .many (predExpression schema)
def predValue (schema : Schema) : Value := .clos .many [] (predExpression schema)

theorem fold_predecessor (value : Nat) : fold (fun predecessor _ => predecessor) 0 value = value - 1 := by
  cases value <;> rfl

theorem pred_applies {ctx : Ctx} {schema : Schema} (matched : Matches ctx schema)
    {value : Value} {number : Nat} (represented : Represents schema value number) :
    ∃ result, Applies ctx (predValue schema) value result ∧ Represents schema result (number - 1) := by
  let stepFunction : Value := .clos .many [value] (.lam .many (.var 1))
  have stepApplies : ∀ predecessor argument m n, Represents schema predecessor m → Represents schema argument n →
      ∃ closure result, Applies ctx stepFunction predecessor closure ∧ Applies ctx closure argument result ∧ Represents schema result m := by
    intro predecessor argument m n predRep argRep
    exact ⟨_, predecessor, appliesClosure (evaluatesLam _ _ _ _), appliesClosure (evaluatesVar rfl), predRep⟩
  obtain ⟨result, recursive, resultRep⟩ := recursor_fold matched (fun predecessor _ => predecessor) stepFunction
    stepApplies (.literal 0) represented
  refine ⟨result, ?_, by simpa only [fold_predecessor] using resultRep⟩
  apply appliesClosure
  exact evaluatesApp
    (evaluatesApp (evaluatesApp (evaluatesDef matched.alias (evaluatesRecursor matched.recursor))
      (sharedLiteral_evaluates _ _ _) (appliesRecursorFirst _ _ _))
      (evaluatesLam _ _ _ _) (appliesRecursorSecond _ _ _ _))
    (evaluatesVar rfl) recursive

def subStep (predecessor : Address) : Expr := .lam .many (.lam .many (.app (.ref predecessor) (.var 0)))
def subExpression (schema : Schema) (predecessor : Address) : Expr :=
  .app (.app (.app (.ref schema.alias) (.var 1)) (subStep predecessor)) (.var 0)
def subBody (schema : Schema) (predecessor : Address) : Expr := .lam .many (.lam .many (subExpression schema predecessor))
def subValue (schema : Schema) (predecessor : Address) : Value := .clos .many [] (.lam .many (subExpression schema predecessor))

theorem fold_subtract (left right : Nat) : fold (fun _ result => result - 1) left right = left - right := by
  induction right with
  | zero => rfl
  | succ right ih => simp only [fold, ih, Nat.sub_sub]

theorem sub_applies {ctx : Ctx} {schema : Schema} (matched : Matches ctx schema) {predecessor : Address}
    (predDeclaration : ctx.env predecessor = some (.defn .shared (predBody schema)))
    {left right : Value} {m n : Nat} (leftValue : Represents schema left m) (rightValue : Represents schema right n) :
    ∃ closure result, Applies ctx (subValue schema predecessor) left closure ∧ Applies ctx closure right result ∧
      Represents schema result (m - n) := by
  let stepFunction : Value := .clos .many [right, left] (.lam .many (.app (.ref predecessor) (.var 0)))
  have stepApplies : ∀ pred argument a b, Represents schema pred a → Represents schema argument b →
      ∃ closure result, Applies ctx stepFunction pred closure ∧ Applies ctx closure argument result ∧
        Represents schema result (b - 1) := by
    intro pred argument a b predRep argRep
    obtain ⟨result, applied, resultRep⟩ := pred_applies matched argRep
    refine ⟨_, result, appliesClosure (evaluatesLam _ _ _ _), ?_, resultRep⟩
    exact appliesClosure (evaluatesApp (evaluatesDef predDeclaration (evaluatesLam _ _ _ _)) (evaluatesVar rfl) applied)
  obtain ⟨result, recursive, resultRep⟩ := recursor_fold matched (fun _ result => result - 1) stepFunction stepApplies leftValue rightValue
  refine ⟨_, result, appliesClosure (evaluatesLam _ _ _ _), ?_, by simpa only [fold_subtract] using resultRep⟩
  apply appliesClosure
  exact evaluatesApp
    (evaluatesApp (evaluatesApp (evaluatesDef matched.alias (evaluatesRecursor matched.recursor))
      (evaluatesVar rfl) (appliesRecursorFirst _ _ _))
      (evaluatesLam _ _ _ _) (appliesRecursorSecond _ _ _ _))
    (evaluatesVar rfl) recursive

theorem Represents.zero_view {schema : Schema} {value : Value} (represented : Represents schema value 0) :
    majorCtor true value = .ok (0, []) := by
  cases represented
  rfl

theorem Represents.successor_view {schema : Schema} {value : Value} {number : Nat}
    (represented : Represents schema value number) (positive : number ≠ 0) :
    ∃ predecessor, majorCtor true value = .ok (1, [predecessor]) ∧ Represents schema predecessor (number - 1) := by
  cases represented with
  | literal number =>
      cases number with
      | zero => contradiction
      | succ number => exact ⟨.lit (.nat number), rfl, .literal _⟩
  | successor tail => exact ⟨_, rfl, tail⟩

def caseRules : Array RecRule := #[
  { fields := 0, rhs := .app (.var 1) (sharedLiteral 0) },
  { fields := 1, rhs := .app (.var 1) (.var 0) }]

theorem case_zero {ctx : Ctx} {schema : Schema} {address : Address} {major zero successor result : Value}
    (declaration : ctx.env address = some (.recursor 2 true caseRules))
    (represented : Represents schema major 0) (selected : Applies ctx zero (.lit (.nat 0)) result) :
    Applies ctx (.pap (.rec_ address 3) [zero, successor]) major result := by
  apply appliesRecursorView declaration rfl represented.zero_view rfl rfl
  exact evaluatesApp (evaluatesVar rfl) (sharedLiteral_evaluates _ _ _) selected

theorem case_successor {ctx : Ctx} {address : Address} {major predecessor zero successor result : Value}
    (declaration : ctx.env address = some (.recursor 2 true caseRules))
    (view : majorCtor true major = .ok (1, [predecessor])) (selected : Applies ctx successor predecessor result) :
    Applies ctx (.pap (.rec_ address 3) [zero, successor]) major result := by
  apply appliesRecursorView declaration rfl view rfl rfl
  exact evaluatesApp (evaluatesVar rfl) (evaluatesVar rfl) selected

end Ix.Compiler.IxIR0.NatArithmetic
