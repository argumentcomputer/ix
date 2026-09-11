import Ix.Compiler.IxIR0.Recursion

/-!
# Checked specialization of a closed source map

The ordinary list recursor receives a nil minor and a step minor that calls a
constant-valued worker before constructing the result cons. Specialization
exposes that worker and the recursive call in one rule. Recognition checks
every declaration and the complete entry; no replacement body is supplied by
the caller. Constructor and worker identities remain those of the source.
-/

namespace Ix.Compiler.IxIR0.MapRecovery

open Ix.Compiler.Ixon (Address)
open Recursion (app2 ghost)

def policyTag : String := "closed-map-specialize/1"

structure Schema where
  nil : Address
  cons : Address
  recursor : Address
  alias : Address
  base : Address
  step : Address
  worker : Address
  replacement : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def workerExpr (s : Schema) : Expr := .lam .many (ghost (.lit (.nat s.replacement)))
def baseExpr (s : Schema) : Expr := ghost (.ref s.nil)
def stepExpr (s : Schema) : Expr :=
  .lam .many (.lam .many (.lam .many
    (app2 (.ref s.cons) (.app (.ref s.worker) (.var 2)) (.var 0))))

def literalRecursor : Decl :=
  .recursor 2 false #[
    { fields := 0, rhs := .var 1 },
    { fields := 2
      rhs := .app (app2 (.var 2) (.var 1) (.var 0))
        (.app (app2 (.var 4) (.var 3) (.var 2)) (.var 0)) }]

def directRecursor (s : Schema) : Decl :=
  .recursor 0 false #[
    { fields := 0, rhs := .ref s.nil },
    { fields := 2
      rhs := app2 (.ref s.cons) (.app (.ref s.worker) (.var 1)) (.app (.var 2) (.var 0)) }]

def listOnto (s : Schema) (literal : Bool) : List Nat → Expr → Expr
  | [], tail => tail
  | n :: ns, tail => app2 (.ref s.cons)
      (if literal then ghost (.lit (.nat n)) else .lit (.nat n)) (listOnto s literal ns tail)

def listExpr (s : Schema) (literal : Bool) (values : List Nat) : Expr :=
  listOnto s literal values (if literal then ghost (.ref s.nil) else .ref s.nil)

def literalCall (s : Schema) (major : Expr) : Expr :=
  .app (app2 (.ref s.alias) (.ref s.base) (.ref s.step)) major

structure Plan where
  schema : Schema
  values : List Nat
  retainedAlias : Option Address := none
  uniquePrefix : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def Plan.main (p : Plan) (literal : Bool) (call : Expr → Expr) : Expr :=
  match p.retainedAlias with
  | none => call (listExpr p.schema literal p.values)
  | some pair =>
      .letE .many (listExpr p.schema literal (p.values.drop p.uniquePrefix))
        (app2 (.ref pair)
          (call (listOnto p.schema literal (p.values.take p.uniquePrefix) (.var 0))) (.var 0))

def Plan.literalMain (p : Plan) : Expr := p.main true (literalCall p.schema)
def Plan.directMain (p : Plan) (address : Address) : Expr := p.main false (.app (.ref address))

structure SourceMatches (env : Env) (s : Schema) : Prop where
  nil : env s.nil = some (.ctor 0 0)
  cons : env s.cons = some (.ctor 1 2)
  recursor : env s.recursor = some literalRecursor
  alias : env s.alias = some (.defn .shared (.ref s.recursor))
  base : env s.base = some (.defn .shared (baseExpr s))
  step : env s.step = some (.defn .shared (stepExpr s))
  worker : env s.worker = some (.defn .shared (workerExpr s))

instance (env : Env) (s : Schema) : Decidable (SourceMatches env s) :=
  decidable_of_iff
    (env s.nil = some (.ctor 0 0) ∧ env s.cons = some (.ctor 1 2) ∧
      env s.recursor = some literalRecursor ∧
      env s.alias = some (.defn .shared (.ref s.recursor)) ∧
      env s.base = some (.defn .shared (baseExpr s)) ∧
      env s.step = some (.defn .shared (stepExpr s)) ∧
      env s.worker = some (.defn .shared (workerExpr s)))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩,
      fun h => ⟨h.nil, h.cons, h.recursor, h.alias, h.base, h.step, h.worker⟩⟩

def Plan.aliasMatches (p : Plan) (env : Env) : Prop :=
  match p.retainedAlias with | none => True | some pair => env pair = some (.ctor 0 2)
instance (p : Plan) (env : Env) : Decidable (p.aliasMatches env) := by
  unfold Plan.aliasMatches
  split <;> infer_instance

structure Checked (declarations : List (Address × Decl)) (main : Expr) where
  plan : Plan
  root : Address
  mainEq : main = .ref root
  source : SourceMatches (Env.ofList declarations) plan.schema
  entry : Env.ofList declarations root = some (.defn .shared plan.literalMain)
  alias : plan.aliasMatches (Env.ofList declarations)

def check (declarations : List (Address × Decl)) (main : Expr) (plan : Plan) :
    Option (Checked declarations main) :=
  match main with
  | .ref root =>
      if hs : SourceMatches (Env.ofList declarations) plan.schema then
        if he : Env.ofList declarations root = some (.defn .shared plan.literalMain) then
          if ha : plan.aliasMatches (Env.ofList declarations) then
            some { plan, root, mainEq := rfl, source := hs, entry := he, alias := ha }
          else none
        else none
      else none
  | _ => none

private def call? : Expr → Option (Address × Address × Address × Expr)
  | .app (.app (.app (.ref alias) (.ref base)) (.ref step)) major => some (alias, base, step, major)
  | _ => none

private def listParts? (s : Schema) : Expr → Option (List Nat × Expr)
  | .app (.app (.ref address) (.app (.lam .many (.lit (.nat n))) .erased)) tail => do
      if address != s.cons then none else
        let (ns, endExpr) ← listParts? s tail
        return (n :: ns, endExpr)
  | expr => some ([], expr)

def propose (declarations : List (Address × Decl)) (main : Expr) : Option Plan := do
  let .ref root := main | none
  let env := Env.ofList declarations
  let some (.defn .shared body) := env root | none
  let (call, retainedAlias, suffix) ← match body with
    | .letE .many suffix (.app (.app (.ref pair) call) (.var 0)) => pure (call, some pair, suffix)
    | body => pure (body, none, .erased)
  let (alias, base, step, major) ← call? call
  let some (.defn .shared (.ref recursor)) := env alias | none
  let some (.defn .shared (.app (.lam .many (.ref nil)) .erased)) := env base | none
  let some (.defn .shared (.lam .many (.lam .many (.lam .many
      (.app (.app (.ref cons) (.app (.ref worker) (.var 2))) (.var 0)))))) := env step | none
  let some (.defn .shared (.lam .many (.app (.lam .many (.lit (.nat replacement))) .erased))) := env worker | none
  let schema : Schema := { nil, cons, recursor, alias, base, step, worker, replacement }
  match retainedAlias with
  | none =>
      let (values, endExpr) ← listParts? schema major
      if endExpr != ghost (.ref nil) then none else return { schema, values }
  | some pair =>
      let (heads, .var 0) ← listParts? schema major | none
      let (tail, endExpr) ← listParts? schema suffix
      if endExpr != ghost (.ref nil) then none else
        return { schema, values := heads ++ tail, retainedAlias := some pair, uniquePrefix := heads.length }

def targetDeclarations (p : Plan) (address : Address) : List (Address × Decl) :=
  [(p.schema.nil, .ctor 0 0), (p.schema.cons, .ctor 1 2),
    (p.schema.worker, .defn .shared (workerExpr p.schema)), (address, directRecursor p.schema)] ++
    p.retainedAlias.toList.map (fun pair => (pair, .ctor 0 2))

structure TargetMatches (env : Env) (p : Plan) (address : Address) : Prop where
  nil : env p.schema.nil = some (.ctor 0 0)
  cons : env p.schema.cons = some (.ctor 1 2)
  worker : env p.schema.worker = some (.defn .shared (workerExpr p.schema))
  recursor : env address = some (directRecursor p.schema)
  alias : p.aliasMatches env
instance (env : Env) (p : Plan) (address : Address) : Decidable (TargetMatches env p address) :=
  decidable_of_iff
    (env p.schema.nil = some (.ctor 0 0) ∧ env p.schema.cons = some (.ctor 1 2) ∧
      env p.schema.worker = some (.defn .shared (workerExpr p.schema)) ∧
      env address = some (directRecursor p.schema) ∧ p.aliasMatches env)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
      fun h => ⟨h.nil, h.cons, h.worker, h.recursor, h.alias⟩⟩

structure Recovered (declarations : List (Address × Decl)) (main : Expr) where
  checked : Checked declarations main
  address : Address
  addressed : address = (directRecursor checked.plan.schema).address
  fresh : address ∉ declarations.map (·.1)
  target : TargetMatches (Env.ofList (targetDeclarations checked.plan address)) checked.plan address

inductive Selection (declarations : List (Address × Decl)) (main : Expr) where
  | literal (reason : Recursion.Skip)
  | recovered (result : Recovered declarations main)

def Selection.declarations {declarations : List (Address × Decl)} {main : Expr} :
    Selection declarations main → List (Address × Decl)
  | .literal _ => declarations
  | .recovered result => targetDeclarations result.checked.plan result.address
def Selection.main {declarations : List (Address × Decl)} {main : Expr} : Selection declarations main → Expr
  | .literal _ => main
  | .recovered result => result.checked.plan.directMain result.address

def selectWith (declarations : List (Address × Decl)) (main : Expr) (proposal : Option Plan) :
    Selection declarations main :=
  match proposal with
  | none => .literal .unrecognized
  | some plan =>
      match check declarations main plan with
      | none => .literal .rejectedProposal
      | some checked =>
          let address := (directRecursor checked.plan.schema).address
          if hfresh : address ∉ declarations.map (·.1) then
            if ht : TargetMatches (Env.ofList (targetDeclarations checked.plan address)) checked.plan address then
              .recovered { checked, address, addressed := rfl, fresh := hfresh, target := ht }
            else .literal .rejectedTarget
          else .literal .addressConflict

def select (declarations : List (Address × Decl)) (main : Expr) : Selection declarations main :=
  selectWith declarations main (propose declarations main)

end Ix.Compiler.IxIR0.MapRecovery
