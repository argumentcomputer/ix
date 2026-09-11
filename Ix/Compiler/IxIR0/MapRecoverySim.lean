import Ix.Compiler.IxIR0.MapRecovery
import Ix.Compiler.IxIR0.RecursionSim
import Ix.Compiler.IxIR0.ProjectionFree

/-! The actual eager source fold and its direct map both evaluate to the same
list. Fuel witnesses termination; uniqueness transports any successful source
run. The checked target also supplies projection-safe trace completeness. -/

namespace Ix.Compiler.IxIR0.MapRecovery

open Ix.Compiler.Ixon (Address)
open Recursion

def listOntoValue (s : Schema) : List Nat → Value → Value
  | [], tail => tail
  | n :: ns, tail => .ctor s.cons 1 [.lit (.nat n), listOntoValue s ns tail]
def listValue (s : Schema) (ns : List Nat) : Value := listOntoValue s ns (.ctor s.nil 0 [])
def mappedValue (s : Schema) (ns : List Nat) : Value := listValue s (ns.map (fun _ => s.replacement))
def baseValue (s : Schema) : Value := .ctor s.nil 0 []
def stepBody (s : Schema) : Expr := app2 (.ref s.cons) (.app (.ref s.worker) (.var 2)) (.var 0)
def stepValue (s : Schema) : Value := .clos .many [] (.lam .many (.lam .many (stepBody s)))

theorem workerRun {ctx : Ctx} {s : Schema} {env : List Value} {argument : Expr} {value : Value}
    (worker : ctx.env s.worker = some (.defn .shared (workerExpr s)))
    (arg : Evaluates ctx env argument value) :
    Evaluates ctx env (.app (.ref s.worker) argument) (.lit (.nat s.replacement)) :=
  evaluatesApp (evaluatesDef worker (evaluatesLam ..)) arg
    (appliesClosure (evaluatesGhost (evaluatesLit ..)))

theorem stepRun {ctx : Ctx} {s : Schema} (hs : SourceMatches ctx.env s)
    (head tail mapped : Value) :
    Applies ctx (.clos .many [tail, head] (stepBody s)) mapped
      (.ctor s.cons 1 [.lit (.nat s.replacement), mapped]) := by
  apply appliesClosure
  exact evaluatesCtor2 hs.cons (workerRun hs.worker (evaluatesVar (by rfl)))
    (evaluatesVar (by rfl))

theorem sourceMap {ctx : Ctx} {s : Schema} (hs : SourceMatches ctx.env s) (ns : List Nat) :
    Applies ctx (.pap (.rec_ s.recursor 3) [baseValue s, stepValue s])
      (listValue s ns) (mappedValue s ns) := by
  induction ns with
  | nil =>
      apply appliesRecursor hs.recursor (by rfl) (by rfl) (by rfl)
      exact evaluatesVar (by rfl)
  | cons n ns ih =>
      apply appliesRecursor hs.recursor (by rfl) (by rfl) (by rfl)
      have recursive : Evaluates ctx
          [listValue s ns, .lit (.nat n), stepValue s, baseValue s, .pap (.rec_ s.recursor 3) []]
          (.app (app2 (.var 4) (.var 3) (.var 2)) (.var 0)) (mappedValue s ns) := evaluatesApp
        (evaluatesApp
          (evaluatesApp (evaluatesVar (by rfl)) (evaluatesVar (by rfl))
            (appliesTernaryFirst ctx s.recursor (baseValue s)))
          (evaluatesVar (by rfl)) (appliesTernaryNext ctx s.recursor (baseValue s) (stepValue s)))
        (evaluatesVar (by rfl)) ih
      have first : Applies ctx (stepValue s) (.lit (.nat n))
          (.clos .many [.lit (.nat n)] (.lam .many (stepBody s))) :=
        appliesClosure (evaluatesLam ..)
      have second : Applies ctx (.clos .many [.lit (.nat n)] (.lam .many (stepBody s)))
          (listValue s ns) (.clos .many [listValue s ns, .lit (.nat n)] (stepBody s)) :=
        appliesClosure (evaluatesLam ..)
      exact evaluatesApp
        (evaluatesApp (evaluatesApp (evaluatesVar (by rfl)) (evaluatesVar (by rfl)) first)
          (evaluatesVar (by rfl)) second)
        recursive (stepRun hs _ _ _)

theorem targetMap {ctx : Ctx} {p : Plan} {address : Address}
    (hs : TargetMatches ctx.env p address) (ns : List Nat) :
    Applies ctx (.pap (.rec_ address 1) []) (listValue p.schema ns) (mappedValue p.schema ns) := by
  induction ns with
  | nil =>
      apply appliesRecursor hs.recursor (by rfl) (by rfl) (by rfl)
      exact evaluatesNullary hs.nil
  | cons n ns ih =>
      apply appliesRecursor hs.recursor (by rfl) (by rfl) (by rfl)
      exact evaluatesCtor2 hs.cons (workerRun hs.worker (evaluatesVar (by rfl)))
        (evaluatesApp (evaluatesVar (by rfl)) (evaluatesVar (by rfl)) ih)

theorem literalCallRun {ctx : Ctx} {s : Schema} {env : List Value} {major : Expr} {ns : List Nat}
    (hs : SourceMatches ctx.env s) (majorRun : Evaluates ctx env major (listValue s ns)) :
    Evaluates ctx env (literalCall s major) (mappedValue s ns) :=
  evaluatesApp
    (evaluatesApp
      (evaluatesApp (evaluatesDef hs.alias (evaluatesRecursor hs.recursor))
        (evaluatesDef hs.base (evaluatesGhost (evaluatesNullary hs.nil)))
        (appliesTernaryFirst ctx s.recursor (baseValue s)))
      (evaluatesDef hs.step (evaluatesLam ..))
      (appliesTernaryNext ctx s.recursor (baseValue s) (stepValue s))) majorRun (sourceMap hs ns)

theorem directCallRun {ctx : Ctx} {p : Plan} {address : Address} {env : List Value}
    {major : Expr} {ns : List Nat} (hs : TargetMatches ctx.env p address)
    (majorRun : Evaluates ctx env major (listValue p.schema ns)) :
    Evaluates ctx env (.app (.ref address) major) (mappedValue p.schema ns) :=
  evaluatesApp (evaluatesRecursor hs.recursor) majorRun (targetMap hs ns)

theorem listOntoRun {ctx : Ctx} {s : Schema} {env : List Value} {tail : Expr} {value : Value}
    (cons : ctx.env s.cons = some (.ctor 1 2)) (literal : Bool) (ns : List Nat)
    (tailRun : Evaluates ctx env tail value) :
    Evaluates ctx env (listOnto s literal ns tail) (listOntoValue s ns value) := by
  induction ns with
  | nil => exact tailRun
  | cons n ns ih =>
      apply evaluatesCtor2 cons
      · cases literal with
        | false => exact evaluatesLit ..
        | true => exact evaluatesGhost (evaluatesLit ..)
      · exact ih

theorem listRun {ctx : Ctx} {s : Schema} (nil : ctx.env s.nil = some (.ctor 0 0))
    (cons : ctx.env s.cons = some (.ctor 1 2)) (literal : Bool) (ns : List Nat) (env : List Value) :
    Evaluates ctx env (listExpr s literal ns) (listValue s ns) := by
  apply listOntoRun cons literal ns
  cases literal with
  | false => exact evaluatesNullary nil
  | true => exact evaluatesGhost (evaluatesNullary nil)

theorem listOntoValue_append (s : Schema) (xs ys : List Nat) (tail : Value) :
    listOntoValue s xs (listOntoValue s ys tail) = listOntoValue s (xs ++ ys) tail := by
  induction xs with
  | nil => rfl
  | cons n ns ih => simp only [listOntoValue, List.cons_append, ih]

def Plan.value (p : Plan) : Value :=
  match p.retainedAlias with
  | none => mappedValue p.schema p.values
  | some pair => .ctor pair 0 [mappedValue p.schema p.values,
      listValue p.schema (p.values.drop p.uniquePrefix)]

theorem mainRun {ctx : Ctx} {p : Plan} (literal : Bool) (call : Expr → Expr)
    (nil : ctx.env p.schema.nil = some (.ctor 0 0)) (cons : ctx.env p.schema.cons = some (.ctor 1 2))
    (alias : p.aliasMatches ctx.env)
    (callRun : ∀ {env major ns}, Evaluates ctx env major (listValue p.schema ns) →
      Evaluates ctx env (call major) (mappedValue p.schema ns)) :
    Evaluates ctx [] (p.main literal call) p.value := by
  cases retained : p.retainedAlias with
  | none =>
      simp only [Plan.main, Plan.value, retained]
      exact callRun (listRun nil cons literal p.values [])
  | some pair =>
      simp only [Plan.main, Plan.value, retained]
      have pairAt : ctx.env pair = some (.ctor 0 2) := by
        simpa only [Plan.aliasMatches, retained] using alias
      apply evaluatesLet (listRun nil cons literal (p.values.drop p.uniquePrefix) [])
      apply evaluatesCtor2 pairAt
      · apply callRun
        have parts := listOntoRun cons literal (p.values.take p.uniquePrefix)
          (evaluatesVar (ctx := ctx)
            (env := [listValue p.schema (p.values.drop p.uniquePrefix)]) (i := 0) (by rfl))
        simpa only [listValue, listOntoValue_append, List.take_append_drop] using parts
      · exact evaluatesVar (by rfl)

theorem Checked.sourceEvaluates {declarations : List (Address × Decl)} {main : Expr}
    (checked : Checked declarations main) :
    Evaluates { env := Env.ofList declarations } [] main checked.plan.value := by
  have body := mainRun (ctx := { env := Env.ofList declarations })
    true (literalCall checked.plan.schema) checked.source.nil checked.source.cons checked.alias
    (literalCallRun checked.source)
  simpa only [checked.mainEq] using evaluatesDef (env := []) checked.entry body

theorem Recovered.forwardSimulation {declarations : List (Address × Decl)} {main : Expr}
    (recovered : Recovered declarations main) {fuel : Nat} {value : Value}
    (run : eval { env := Env.ofList declarations } fuel [] main = .ok value) :
    ∃ targetFuel, eval { env := Env.ofList (targetDeclarations recovered.checked.plan recovered.address) }
      targetFuel [] (recovered.checked.plan.directMain recovered.address) = .ok value := by
  have values := (recovered.checked.sourceEvaluates).unique ⟨fuel, run⟩
  rw [← values]
  exact mainRun false (.app (.ref recovered.address)) recovered.target.nil recovered.target.cons
    recovered.target.alias (directCallRun recovered.target)

theorem Selection.forwardSimulation {declarations : List (Address × Decl)} {main : Expr}
    (selection : Selection declarations main) {fuel : Nat} {value : Value}
    (run : eval { env := Env.ofList declarations } fuel [] main = .ok value) :
    ∃ targetFuel, eval { env := Env.ofList selection.declarations } targetFuel [] selection.main = .ok value := by
  cases selection with
  | literal reason => exact ⟨fuel, run⟩
  | recovered recovered => exact recovered.forwardSimulation run

open ProjectionFree

theorem listOntoSafe (s : Schema) (ns : List Nat) {tail : Expr} (safe : ExprSafe tail) :
    ExprSafe (listOnto s false ns tail) := by
  induction ns with
  | nil => exact safe
  | cons n ns ih => simpa only [ExprSafe, listOnto, Bool.false_eq_true, ite_false,
      app2, syntaxSafe, Bool.true_and] using ih

theorem Plan.directMainSafe (plan : Plan) (address : Address) : ExprSafe (plan.directMain address) := by
  have lists : ∀ ns, ExprSafe (listExpr plan.schema false ns) :=
    fun ns => listOntoSafe plan.schema ns (by rfl)
  have heads := listOntoSafe plan.schema (plan.values.take plan.uniquePrefix) (tail := .var 0) (by rfl)
  cases alias : plan.retainedAlias <;>
    simp [ExprSafe, Plan.directMain, Plan.main, alias, app2, syntaxSafe, lists, heads]

theorem Plan.targetContextSafe (plan : Plan) (address : Address) :
    CtxSafe { env := Env.ofList (targetDeclarations plan address) } := by
  constructor
  · intro key declaration lookup
    have rows : (targetDeclarations plan address).all (fun row => declSafe row.2) = true := by
      cases alias : plan.retainedAlias <;>
        simp [targetDeclarations, alias, directRecursor, workerExpr, ghost, app2, declSafe, syntaxSafe]
    unfold Env.ofList at lookup
    obtain ⟨row, found, value⟩ := Option.map_eq_some_iff.mp lookup
    have safe := List.all_eq_true.mp rows row (List.mem_of_find?_eq_some found)
    simpa only [value] using safe
  · intro key arguments result _ oracle
    cases oracle

theorem Recovered.projectionSafe {declarations : List (Address × Decl)} {main : Expr}
    (recovery : Recovered declarations main) {fuel : Nat} {value : Value}
    (run : eval { env := Env.ofList (targetDeclarations recovery.checked.plan recovery.address) }
      fuel [] (recovery.checked.plan.directMain recovery.address) = .ok value) :
    ProjectionSafe.Eval { env := Env.ofList (targetDeclarations recovery.checked.plan recovery.address) }
      fuel [] (recovery.checked.plan.directMain recovery.address) value :=
  ProjectionFree.Eval.of_run (recovery.checked.plan.targetContextSafe recovery.address)
    ValuesSafe.nil (recovery.checked.plan.directMainSafe recovery.address) run

end Ix.Compiler.IxIR0.MapRecovery
