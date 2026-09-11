import Ix.Compiler.IxIR0.Serialize
import Ix.Compiler.IxIR0.Eval

/-!
# Checked recovery of a list accumulator recursor

The first recovery schema recognizes an eager, immediate-tail `below` fold.
Each source step constructs a tuple containing a function and the recursively
computed tuple. Only its function projection is used by the selected entry.
The replacement absorbs the accumulator before the major premise and invokes
the recursor value directly in the cons rule.

Recognition is deliberately bounded to closed Nat-list entries, optionally
retaining the input in a returned pair. The recursor simulation itself covers
arbitrary list elements and accumulators. This is a first schema, not a generic
`brecOn` specializer. Every declaration, binder, projection, and entry use is
checked against the exact erased input; an unrecognized input is unchanged.
-/

namespace Ix.Compiler.IxIR0.Recursion

open Ix.Compiler.Ixon (Address)

structure Schema where
  nil : Address
  cons : Address
  pack : Address
  unit : Address
  recursor : Address
  alias : Address
  base : Address
  step : Address
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def app2 (f x y : Expr) : Expr := .app (.app f x) y

/-- The source gate's erased-argument application. For an open `e`, indices
must already include this binder. The templates below spell those indices out.
-/
def ghost (e : Expr) : Expr := .app (.lam .many e) .erased

def consExpr (s : Schema) (head tail : Expr) : Expr :=
  app2 (.ref s.cons) head tail

def packExpr (s : Schema) (fn below : Expr) : Expr :=
  app2 (.ref s.pack) fn below

/-- Environment after applying the captured function:
`accumulator, erased argument, below, tail, head`. -/
def stepBody (s : Schema) : Expr :=
  .app (.proj 0 (.var 2)) (consExpr s (.var 4) (.var 0))

def baseExpr (s : Schema) : Expr :=
  packExpr s (ghost (.lam .many (.var 0))) (ghost (.ref s.unit))

def stepExpr (s : Schema) : Expr :=
  .lam .many (.lam .many (.lam .many
    (packExpr s (ghost (.lam .many (stepBody s))) (.var 0))))

/-- Ordinary immediate-tail structural recursion, with base and step minors.
The cons rule evaluates its recursive argument eagerly before the step.
Its environment is `tail, head, step, base, recursive self`. -/
def literalRecursor (_s : Schema) : Decl :=
  .recursor 2 false #[
    { fields := 0, rhs := .var 1 },
    { fields := 2
      rhs := .app (app2 (.var 2) (.var 1) (.var 0))
        (.app (app2 (.var 4) (.var 3) (.var 2)) (.var 0)) }]

/-- The accumulator precedes the major. The recursive call is saturated and
in tail position, which the existing ownership and CFG lowerers preserve. -/
def directRecursor (s : Schema) : Decl :=
  .recursor 1 false #[
    { fields := 0, rhs := .var 0 },
    { fields := 2
      rhs := app2 (.var 3) (consExpr s (.var 1) (.var 2)) (.var 0) }]

def literalList (s : Schema) : List Nat → Expr
  | [] => ghost (.ref s.nil)
  | n :: ns => consExpr s (ghost (.lit (.nat n))) (literalList s ns)

def directList (s : Schema) : List Nat → Expr
  | [] => .ref s.nil
  | n :: ns => consExpr s (.lit (.nat n)) (directList s ns)

def literalCall (s : Schema) (major accumulator : Expr) : Expr :=
  .app (.proj 0 (.app (app2 (.ref s.alias) (.ref s.base) (.ref s.step)) major)) accumulator

def directCall (address : Address) (major accumulator : Expr) : Expr :=
  app2 (.ref address) accumulator major

structure Plan where
  schema : Schema
  values : List Nat
  /-- A returned pair retains an alias to the input and makes every reset
  cold. `none` returns just the reversed list. -/
  retainedAlias : Option Address := none
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def Plan.literalMain (p : Plan) : Expr :=
  let s := p.schema
  match p.retainedAlias with
  | none => literalCall s (literalList s p.values) (ghost (.ref s.nil))
  | some pair =>
      .letE .many (literalList s p.values)
        (app2 (.ref pair) (literalCall s (.var 0) (ghost (.ref s.nil))) (.var 0))

def Plan.directMain (p : Plan) (address : Address) : Expr :=
  let s := p.schema
  match p.retainedAlias with
  | none => directCall address (directList s p.values) (.ref s.nil)
  | some pair =>
      .letE .many (directList s p.values)
        (app2 (.ref pair) (directCall address (.var 0) (.ref s.nil)) (.var 0))

/-- All facts read by the recursor simulation, checked against first-binding
wins lookup in the actual source environment. -/
structure SourceMatches (env : Env) (s : Schema) : Prop where
  nil : env s.nil = some (.ctor 0 0)
  cons : env s.cons = some (.ctor 1 2)
  pack : env s.pack = some (.ctor 0 2)
  unit : env s.unit = some (.ctor 1 0)
  recursor : env s.recursor = some (literalRecursor s)
  alias : env s.alias = some (.defn .shared (.ref s.recursor))
  base : env s.base = some (.defn .shared (baseExpr s))
  step : env s.step = some (.defn .shared (stepExpr s))

instance (env : Env) (s : Schema) : Decidable (SourceMatches env s) :=
  decidable_of_iff
    (env s.nil = some (.ctor 0 0) ∧ env s.cons = some (.ctor 1 2) ∧
      env s.pack = some (.ctor 0 2) ∧ env s.unit = some (.ctor 1 0) ∧
      env s.recursor = some (literalRecursor s) ∧
      env s.alias = some (.defn .shared (.ref s.recursor)) ∧
      env s.base = some (.defn .shared (baseExpr s)) ∧
      env s.step = some (.defn .shared (stepExpr s)))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩,
      fun h => ⟨h.nil, h.cons, h.pack, h.unit, h.recursor, h.alias, h.base, h.step⟩⟩

def Plan.aliasMatches (p : Plan) (env : Env) : Prop :=
  match p.retainedAlias with
  | none => True
  | some pair => env pair = some (.ctor 0 2)

instance (p : Plan) (env : Env) : Decidable (p.aliasMatches env) := by
  unfold Plan.aliasMatches
  split <;> infer_instance

/-- A proposal cannot supply a replacement body. Checking fixes both source
and target to the proved schema. Proof fields erase from generated code. -/
structure Checked (declarations : List (Address × Decl)) (main : Expr) where
  plan : Plan
  root : Address
  mainEq : main = .ref root
  source : SourceMatches (Env.ofList declarations) plan.schema
  entry : Env.ofList declarations root = some (.defn .shared plan.literalMain)
  alias : plan.aliasMatches (Env.ofList declarations)

def check (declarations : List (Address × Decl)) (main : Expr)
    (plan : Plan) : Option (Checked declarations main) :=
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

private def ghostRef? : Expr → Option Address
  | .app (.lam .many (.ref a)) .erased => some a
  | _ => none

private def literalList? (s : Schema) : Expr → Option (List Nat)
  | .app (.lam .many (.ref a)) .erased =>
      if a == s.nil then some [] else none
  | .app (.app (.ref a) (.app (.lam .many (.lit (.nat n))) .erased)) tail =>
      if a == s.cons then (n :: ·) <$> literalList? s tail else none
  | _ => none

private def call? : Expr → Option (Address × Address × Address × Expr × Address)
  | .app (.proj 0 (.app (.app (.app (.ref alias) (.ref base)) (.ref step)) major)) acc => do
      return (alias, base, step, major, ← ghostRef? acc)
  | _ => none

/-- The recognizer only proposes addresses and a parsed input. `check` then
compares the complete rules and entry, including every use of `below`. -/
def propose (declarations : List (Address × Decl)) (main : Expr) : Option Plan := do
  let .ref root := main | none
  let env := Env.ofList declarations
  let some (.defn .shared body) := env root | none
  let (alias, base, step, major, nil, retainedAlias) ← match body with
    | .letE .many major (.app (.app (.ref pair) call) (.var 0)) => do
        let (alias, base, step, .var 0, nil) ← call? call | none
        pure (alias, base, step, major, nil, some pair)
    | body => do
        let (alias, base, step, major, nil) ← call? body
        pure (alias, base, step, major, nil, none)
  let some (.defn .shared (.ref recursor)) := env alias | none
  let some (.recursor 2 false _) := env recursor | none
  let some (.defn .shared (.app (.app (.ref pack) _) unitExpr)) := env base | none
  let unit ← ghostRef? unitExpr
  let some (.defn .shared (.lam .many (.lam .many (.lam .many
    (.app (.app _ fn) _))))) := env step | none
  let .app (.lam .many (.lam .many body)) .erased := fn | none
  let .app _ (.app (.app (.ref cons) _) _) := body | none
  let schema : Schema := { nil, cons, pack, unit, recursor, alias, base, step }
  let values ← literalList? schema major
  return { schema, values, retainedAlias }

inductive Skip where
  | unrecognized
  | rejectedProposal
  | addressConflict
  | rejectedTarget
  deriving BEq, Repr

/-- The generated declaration has its own canonical IxIR₀ identity. Source
constructor identities are stable; source recursor and entry keys are never
reused for changed bodies. -/
def targetDeclarations (p : Plan) (address : Address) : List (Address × Decl) :=
  [(p.schema.nil, .ctor 0 0), (p.schema.cons, .ctor 1 2),
    (address, directRecursor p.schema)] ++
    p.retainedAlias.toList.map (fun pair => (pair, .ctor 0 2))

structure TargetMatches (env : Env) (p : Plan) (address : Address) : Prop where
  nil : env p.schema.nil = some (.ctor 0 0)
  cons : env p.schema.cons = some (.ctor 1 2)
  recursor : env address = some (directRecursor p.schema)
  alias : p.aliasMatches env

instance (env : Env) (p : Plan) (address : Address) :
    Decidable (TargetMatches env p address) :=
  decidable_of_iff
    (env p.schema.nil = some (.ctor 0 0) ∧ env p.schema.cons = some (.ctor 1 2) ∧
      env address = some (directRecursor p.schema) ∧ p.aliasMatches env)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
      fun h => ⟨h.nil, h.cons, h.recursor, h.alias⟩⟩

structure Recovered (declarations : List (Address × Decl)) (main : Expr) where
  checked : Checked declarations main
  address : Address
  addressed : address = (directRecursor checked.plan.schema).address
  fresh : address ∉ declarations.map (·.1)
  target : TargetMatches (Env.ofList (targetDeclarations checked.plan address))
    checked.plan address

inductive Selection (declarations : List (Address × Decl)) (main : Expr) where
  | literal (reason : Skip)
  | recovered (result : Recovered declarations main)

def Selection.declarations {declarations : List (Address × Decl)} {main : Expr} :
    Selection declarations main → List (Address × Decl)
  | .literal _ => declarations
  | .recovered result => targetDeclarations result.checked.plan result.address

def Selection.main {declarations : List (Address × Decl)} {main : Expr} :
    Selection declarations main → Expr
  | .literal _ => main
  | .recovered result => result.checked.plan.directMain result.address

/-- Untrusted proposals cross the exact checker; failures preserve the input
literally. Canonical naming and target lookup are checked independently. -/
def selectWith (declarations : List (Address × Decl)) (main : Expr)
    (proposal : Option Plan) : Selection declarations main :=
  match proposal with
  | none => .literal .unrecognized
  | some plan =>
      match check declarations main plan with
      | none => .literal .rejectedProposal
      | some checked =>
          let address := (directRecursor checked.plan.schema).address
          if hfresh : address ∉ declarations.map (·.1) then
            if ht : TargetMatches
                (Env.ofList (targetDeclarations checked.plan address)) checked.plan address then
              .recovered { checked, address, addressed := rfl, fresh := hfresh, target := ht }
            else .literal .rejectedTarget
          else .literal .addressConflict

def select (declarations : List (Address × Decl)) (main : Expr) :
    Selection declarations main :=
  selectWith declarations main (propose declarations main)

end Ix.Compiler.IxIR0.Recursion
