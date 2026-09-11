import Ix.Compiler.IxIR0.UniqueReverse
import Ix.Compiler.IxIR0.RecursionSim

/-! Exact evaluator simulation for every checked finite unique-list source.
Both the literal builder-minor recursion and the direct instantiation evaluate
to the same accumulator reversal. No ownership or heap premise is assumed. -/

namespace Ix.Compiler.IxIR0.UniqueReverse

open Ix.Compiler.Ixon (Address)
open Recursion (Evaluates Applies evaluatesVar evaluatesLam evaluatesErased evaluatesLit
  evaluatesDef evaluatesRecursor evaluatesNullary appliesClosure evaluatesApp evaluatesCtor2
  appliesRecursor appliesTernaryFirst appliesTernaryNext appliesAccumulator)

def listValue (schema : Schema) : List Nat → Value
  | [] => .ctor schema.nil 0 []
  | n :: ns => .ctor schema.cons 1 [.lit (.nat n), listValue schema ns]

def reverseOnto (schema : Schema) : List Nat → Value → Value
  | [], accumulator => accumulator
  | n :: ns, accumulator => reverseOnto schema ns (.ctor schema.cons 1 [.lit (.nat n), accumulator])

theorem reverseOnto_listValue (schema : Schema) (values accumulator : List Nat) :
    reverseOnto schema values (listValue schema accumulator) =
      listValue schema (values.reverse ++ accumulator) := by
  induction values generalizing accumulator with
  | nil => rfl
  | cons n ns ih =>
      change reverseOnto schema ns (listValue schema (n :: accumulator)) = _
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem reverseOnto_nil (schema : Schema) (values : List Nat) :
    reverseOnto schema values (.ctor schema.nil 0 []) = listValue schema values.reverse := by
  simpa only [listValue, List.append_nil] using reverseOnto_listValue schema values []

def builderValue (schema : Schema) : Value :=
  .clos .linear [] (.lam .linear (Recursion.app2 (.ref schema.cons) (.var 1) (.var 0)))

theorem evaluatesBuilder {ctx : Ctx} {schema : Schema}
    (hs : SourceMatches ctx.env schema) (env : List Value) :
    Evaluates ctx env (.ref schema.builder) (builderValue schema) :=
  evaluatesDef hs.builder (evaluatesLam ctx [] .linear _)

theorem appliesBuilderFirst (ctx : Ctx) (schema : Schema) (head : Value) :
    Applies ctx (builderValue schema) head
      (.clos .linear [head] (Recursion.app2 (.ref schema.cons) (.var 1) (.var 0))) :=
  appliesClosure (evaluatesLam ctx [head] .linear _)

theorem appliesBuilderLast {ctx : Ctx} {schema : Schema}
    (hcons : ctx.env schema.cons = some (.ctor 1 2)) (head tail : Value) :
    Applies ctx (.clos .linear [head] (Recursion.app2 (.ref schema.cons) (.var 1) (.var 0)))
      tail (.ctor schema.cons 1 [head, tail]) :=
  appliesClosure (evaluatesCtor2 hcons (evaluatesVar (by rfl)) (evaluatesVar (by rfl)))

theorem literalLoop {ctx : Ctx} {schema : Schema} (hs : SourceMatches ctx.env schema)
    (values : List Nat) (accumulator : Value) :
    Applies ctx (.pap (.rec_ schema.recursor 3) [builderValue schema, accumulator])
      (listValue schema values) (reverseOnto schema values accumulator) := by
  induction values generalizing accumulator with
  | nil =>
      apply appliesRecursor hs.recursor (pre := [builderValue schema, accumulator])
        (tag := 0) (by rfl) (by rfl) (by rfl)
      exact evaluatesVar (by rfl)
  | cons n ns ih =>
      apply appliesRecursor hs.recursor (pre := [builderValue schema, accumulator])
        (tag := 1) (by rfl) (by rfl) (by rfl)
      exact evaluatesApp
        (evaluatesApp
          (evaluatesApp (evaluatesVar (by rfl)) (evaluatesVar (by rfl))
            (appliesTernaryFirst ctx schema.recursor (builderValue schema)))
          (evaluatesApp
            (evaluatesApp (evaluatesVar (by rfl)) (evaluatesVar (by rfl))
              (appliesBuilderFirst ctx schema (.lit (.nat n))))
            (evaluatesVar (by rfl)) (appliesBuilderLast hs.cons (.lit (.nat n)) accumulator))
          (appliesTernaryNext ctx schema.recursor (builderValue schema)
            (.ctor schema.cons 1 [.lit (.nat n), accumulator])))
        (evaluatesVar (by rfl)) (ih (.ctor schema.cons 1 [.lit (.nat n), accumulator]))

theorem directLoop {ctx : Ctx} {schema : Schema} {address : Address}
    (hcons : ctx.env schema.cons = some (.ctor 1 2))
    (hrec : ctx.env address = some (directRecursor schema))
    (values : List Nat) (accumulator : Value) :
    Applies ctx (.pap (.rec_ address 2) [accumulator]) (listValue schema values)
      (reverseOnto schema values accumulator) := by
  induction values generalizing accumulator with
  | nil =>
      apply appliesRecursor hrec (pre := [accumulator]) (tag := 0) (by rfl) (by rfl) (by rfl)
      exact evaluatesVar (by rfl)
  | cons n ns ih =>
      apply appliesRecursor hrec (pre := [accumulator]) (tag := 1) (by rfl) (by rfl) (by rfl)
      exact evaluatesApp
        (evaluatesApp (evaluatesVar (by rfl))
          (evaluatesCtor2 hcons (evaluatesVar (by rfl)) (evaluatesVar (by rfl)))
          (appliesAccumulator ctx address (.ctor schema.cons 1 [.lit (.nat n), accumulator])))
        (evaluatesVar (by rfl)) (ih (.ctor schema.cons 1 [.lit (.nat n), accumulator]))

theorem evaluatesList {ctx : Ctx} {schema : Schema}
    (hnil : ctx.env schema.nil = some (.ctor 0 0))
    (hcons : ctx.env schema.cons = some (.ctor 1 2)) (env : List Value) (values : List Nat) :
    Evaluates ctx env (listExpr schema values) (listValue schema values) := by
  induction values with
  | nil => exact evaluatesNullary hnil
  | cons n ns ih => exact evaluatesCtor2 hcons (evaluatesLit ctx env _) ih

theorem literalRun {ctx : Ctx} {schema : Schema} {env : List Value}
    {major accumulator : Expr} {values : List Nat} {acc : Value}
    (hs : SourceMatches ctx.env schema)
    (hmajor : Evaluates ctx env major (listValue schema values))
    (hacc : Evaluates ctx env accumulator acc) :
    Evaluates ctx env (literalCall schema major accumulator) (reverseOnto schema values acc) :=
  evaluatesApp
    (evaluatesApp
      (evaluatesApp (evaluatesDef hs.alias (evaluatesRecursor hs.recursor))
        (evaluatesBuilder hs env) (appliesTernaryFirst ctx schema.recursor (builderValue schema)))
      hacc (appliesTernaryNext ctx schema.recursor (builderValue schema) acc))
    hmajor (literalLoop hs values acc)

def Plan.value (plan : Plan) : Value := listValue plan.schema plan.values.reverse

theorem literalBodyRun {ctx : Ctx} {plan : Plan}
    (hs : SourceMatches ctx.env plan.schema) (env : List Value) :
    Evaluates ctx env plan.literalBody plan.value := by
  have h := literalRun hs (evaluatesList hs.nil hs.cons env plan.values) (evaluatesNullary hs.nil)
  simpa only [Plan.literalBody, Plan.value, reverseOnto_nil] using h

theorem directMainRun {ctx : Ctx} {plan : Plan} {address : Address}
    (ht : TargetMatches ctx.env plan.schema address) :
    Evaluates ctx [] (plan.directMain address) plan.value := by
  have h := evaluatesApp
    (evaluatesApp (evaluatesRecursor (env := []) ht.recursor) (evaluatesNullary ht.nil)
      (appliesAccumulator ctx address (.ctor plan.schema.nil 0 [])))
    (evaluatesList ht.nil ht.cons [] plan.values)
    (directLoop ht.cons ht.recursor plan.values (.ctor plan.schema.nil 0 []))
  simpa only [Plan.directMain, Plan.value, reverseOnto_nil, Recursion.app2] using h

theorem Checked.sourceEvaluates {declarations : List (Address × Decl)} {main : Expr}
    (checked : Checked declarations main) :
    Evaluates { env := Env.ofList declarations } [] main checked.plan.value := by
  simpa only [checked.mainEq] using evaluatesApp
    (evaluatesDef checked.entry (evaluatesLam _ [] .many _)) (evaluatesErased _ [])
    (appliesClosure (literalBodyRun checked.source [.erased]))

theorem Recovered.forwardSimulation {declarations : List (Address × Decl)} {main : Expr}
    (recovery : Recovered declarations main) {sourceFuel : Nat} {value : Value}
    (hsource : eval { env := Env.ofList declarations } sourceFuel [] main = .ok value) :
    ∃ targetFuel,
      eval { env := Env.ofList (targetDeclarations recovery.checked.plan recovery.address) }
        targetFuel [] (recovery.checked.plan.directMain recovery.address) = .ok value := by
  have heq := Evaluates.unique ⟨sourceFuel, hsource⟩ recovery.checked.sourceEvaluates
  rw [heq]
  exact directMainRun recovery.target

end Ix.Compiler.IxIR0.UniqueReverse
