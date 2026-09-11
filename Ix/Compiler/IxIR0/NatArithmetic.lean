import Ix.Compiler.IxIR0.RecursionSim

/-! A mathematical summary of the canonical Nat recursor used for addition.
The summary is proved in the ordinary evaluator, including literal peeling;
there is no arithmetic extern or replacement source oracle. -/

namespace Ix.Compiler.IxIR0.NatArithmetic

open Ix.Compiler.Ixon (Address)
open Recursion

structure Schema where
  successor : Address
  recursor : Address
  alias : Address
  deriving DecidableEq, Repr

def rules : Array RecRule := #[
  { fields := 0, rhs := .var 1 },
  { fields := 1, rhs := .app (.app (.var 1) (.var 0))
      (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)) }]

def stepBody (schema : Schema) : Expr :=
  .lam .many (.lam .many (.app (.ref schema.successor) (.var 0)))

def body (schema : Schema) : Expr :=
  .lam .many (.lam .many
    (.app (.app (.app (.ref schema.alias) (.var 1)) (stepBody schema)) (.var 0)))

structure Matches (ctx : Ctx) (schema : Schema) : Prop where
  successor : ctx.env schema.successor = some (.ctor 1 1)
  recursor : ctx.env schema.recursor = some (.recursor 2 true rules)
  alias : ctx.env schema.alias = some (.defn .shared (.ref schema.recursor))

instance (ctx : Ctx) (schema : Schema) : Decidable (Matches ctx schema) :=
  decidable_of_iff
    (ctx.env schema.successor = some (.ctor 1 1) ∧
      ctx.env schema.recursor = some (.recursor 2 true rules) ∧
      ctx.env schema.alias = some (.defn .shared (.ref schema.recursor)))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.successor, h.recursor, h.alias⟩⟩

/-- Runtime arguments can be literals; previous source additions can also
have constructed successor spines. Both denote the same unbounded Nat. -/
inductive Represents (schema : Schema) : Value → Nat → Prop where
  | literal (value : Nat) : Represents schema (.lit (.nat value)) value
  | successor {value : Value} {number : Nat} (tail : Represents schema value number) :
      Represents schema (.ctor schema.successor 1 [value]) (number + 1)

theorem appliesRecursorView {ctx : Ctx} {address : Address}
    {pre : List Value} {major : Value} {tag : Nat} {fields : List Value}
    {recRules : Array RecRule} {rule : RecRule} {result : Value}
    (declaration : ctx.env address = some (.recursor 2 true recRules))
    (arity : pre.length = 2)
    (view : majorCtor true major = .ok (tag, fields))
    (found : recRules[tag]? = some rule) (fieldCount : fields.length = rule.fields)
    (evaluated : Evaluates ctx
      (fields.reverse ++ pre.reverse ++ [.pap (.rec_ address 3) []]) rule.rhs result) :
    Applies ctx (.pap (.rec_ address 3) pre) major result := by
  obtain ⟨fuel, evaluated⟩ := evaluated
  refine ⟨fuel + 3, ?_⟩
  rw [apply.eq_def]
  dsimp only
  rw [saturate.eq_def]
  simp only [Head.arity, List.length_append, List.length_singleton, arity,
    beq_self_eq_true, ite_true]
  rw [fire.eq_def]
  simpa [declaration, view, found, fieldCount] using evaluated

theorem appliesRecursorFirst (ctx : Ctx) (address : Address) (value : Value) :
    Applies ctx (.pap (.rec_ address 3) []) value (.pap (.rec_ address 3) [value]) := by
  exact ⟨2, by simp [apply, saturate, Head.arity]⟩

theorem appliesRecursorSecond (ctx : Ctx) (address : Address) (left right : Value) :
    Applies ctx (.pap (.rec_ address 3) [left]) right (.pap (.rec_ address 3) [left, right]) := by
  exact ⟨2, by simp [apply, saturate, Head.arity]⟩

def stepValue (schema : Schema) (environment : List Value) : Value :=
  .clos .many environment (.lam .many (.app (.ref schema.successor) (.var 0)))

theorem step_applies {ctx : Ctx} {schema : Schema} (matched : Matches ctx schema)
    (environment : List Value) (predecessor argument : Value) :
    ∃ closure, Applies ctx (stepValue schema environment) predecessor closure ∧
      Applies ctx closure argument (.ctor schema.successor 1 [argument]) := by
  refine ⟨.clos .many (predecessor :: environment) (.app (.ref schema.successor) (.var 0)),
    appliesClosure (evaluatesLam _ _ _ _), ?_⟩
  apply appliesClosure
  refine evaluatesApp (f := .pap (.ctor schema.successor 1 1) []) ?_ (evaluatesVar rfl) ?_
  · exact ⟨2, by simp [eval, matched.successor, saturate, Head.arity]⟩
  · exact ⟨3, by simp [apply, saturate, fire, Head.arity]⟩

theorem recursor_add {ctx : Ctx} {schema : Schema} (matched : Matches ctx schema)
    (environment : List Value) {left right : Value} {m n : Nat}
    (leftValue : Represents schema left m) (rightValue : Represents schema right n) :
    ∃ result, Applies ctx (.pap (.rec_ schema.recursor 3) [left, stepValue schema environment]) right result ∧
      Represents schema result (m + n) := by
  have zero : Applies ctx (.pap (.rec_ schema.recursor 3) [left, stepValue schema environment])
      (.lit (.nat 0)) left := by
    apply appliesRecursorView matched.recursor rfl (by rfl) (by rfl) (by rfl)
    exact evaluatesVar rfl
  have successor {major predecessor result : Value} {number : Nat}
      (view : majorCtor true major = .ok (1, [predecessor]))
      (recursive : Applies ctx (.pap (.rec_ schema.recursor 3)
        [left, stepValue schema environment]) predecessor result)
      (represented : Represents schema result (m + number)) :
      ∃ result, Applies ctx (.pap (.rec_ schema.recursor 3) [left, stepValue schema environment])
        major result ∧ Represents schema result (m + (number + 1)) := by
    obtain ⟨closure, first, second⟩ := step_applies matched environment predecessor result
    refine ⟨.ctor schema.successor 1 [result], ?_, ?_⟩
    · apply appliesRecursorView matched.recursor rfl view (by rfl) (by rfl)
      refine evaluatesApp (evaluatesApp (evaluatesVar rfl) (evaluatesVar rfl) first) ?_ second
      exact evaluatesApp
        (evaluatesApp
          (evaluatesApp (evaluatesVar rfl) (evaluatesVar rfl) (appliesRecursorFirst _ _ _))
          (evaluatesVar rfl) (appliesRecursorSecond _ _ _ _))
        (evaluatesVar rfl) recursive
    · simpa only [Nat.add_assoc] using Represents.successor represented
  induction rightValue with
  | literal n =>
      induction n with
      | zero => exact ⟨left, zero, by simpa using leftValue⟩
      | succ n ih =>
          obtain ⟨result, recursive, represented⟩ := ih
          exact successor (by rfl) recursive represented
  | successor tail ih =>
      obtain ⟨result, recursive, represented⟩ := ih
      exact successor (by rfl) recursive represented

theorem body_applies {ctx : Ctx} {schema : Schema} (matched : Matches ctx schema)
    {left right : Value} {m n : Nat}
    (leftValue : Represents schema left m) (rightValue : Represents schema right n) :
    ∃ closure result,
      Applies ctx (.clos .many [] (match body schema with | .lam _ body => body | _ => .erased)) left closure ∧
      Applies ctx closure right result ∧ Represents schema result (m + n) := by
  obtain ⟨result, recursive, represented⟩ := recursor_add matched [right, left] leftValue rightValue
  refine ⟨_, result, appliesClosure (evaluatesLam _ _ _ _), ?_, represented⟩
  apply appliesClosure
  refine evaluatesApp
    (evaluatesApp
      (evaluatesApp ?_ (evaluatesVar rfl) (appliesRecursorFirst _ _ _))
      (evaluatesLam _ _ _ _) (appliesRecursorSecond _ _ _ _))
    (evaluatesVar rfl) recursive
  exact evaluatesDef matched.alias (evaluatesRecursor matched.recursor)

end Ix.Compiler.IxIR0.NatArithmetic
