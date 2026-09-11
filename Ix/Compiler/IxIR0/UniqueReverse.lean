import Ix.Compiler.IxIR0.RecursorModes
import Ix.Compiler.IxIR0.Recursion

/-! Exact recognition of a closed unique-list accumulator recursor. The known
constructor-building minor is specialized away only after its entire body and
every recursor rule match. Ownership metadata is checked separately against
the original Ixon declarations; erasure alone does not supply the worlds. -/

namespace Ix.Compiler.IxIR0.UniqueReverse

open Ix.Compiler.Ixon (Address)
open Recursion (app2)

def policyTag : String := "unique-reverse-specialize/1"

structure Schema where
  nil : Address
  cons : Address
  recursor : Address
  alias : Address
  builder : Address
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def builderExpr (s : Schema) : Expr :=
  .lam .linear (.lam .linear (app2 (.ref s.cons) (.var 1) (.var 0)))

def literalRecursor : Decl :=
  .recursor 2 false #[
    { fields := 0, rhs := .var 0 },
    { fields := 2, rhs := .app (app2 (.var 4) (.var 3)
        (app2 (.var 3) (.var 1) (.var 2))) (.var 0) }]

def directRecursor (s : Schema) : Decl :=
  .recursor 1 false #[
    { fields := 0, rhs := .var 0 },
    { fields := 2, rhs := app2 (.var 3)
        (app2 (.ref s.cons) (.var 1) (.var 2)) (.var 0) }]

def sourceInstance : RecursorInstance :=
  { declaration := literalRecursor, arguments := [.shared, .unique, .unique]
    fields := [[], [.unique, .unique]], result := .unique }

def directInstance (s : Schema) : RecursorInstance :=
  { declaration := directRecursor s, arguments := [.unique, .unique]
    fields := [[], [.unique, .unique]], result := .unique }

@[simp] theorem sourceInstance_wellShaped : sourceInstance.wellShaped = true := rfl
@[simp] theorem directInstance_wellShaped (s : Schema) : (directInstance s).wellShaped = true := rfl

def listExpr (s : Schema) : List Nat → Expr
  | [] => .ref s.nil
  | n :: ns => app2 (.ref s.cons) (.lit (.nat n)) (listExpr s ns)

def literalCall (s : Schema) (major accumulator : Expr) : Expr :=
  .app (app2 (.ref s.alias) (.ref s.builder) accumulator) major

structure Plan where
  schema : Schema
  values : List Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def Plan.literalBody (plan : Plan) : Expr :=
  literalCall plan.schema (listExpr plan.schema plan.values) (.ref plan.schema.nil)

def Plan.directMain (plan : Plan) (address : Address) : Expr :=
  app2 (.ref address) (.ref plan.schema.nil) (listExpr plan.schema plan.values)

structure SourceMatches (env : Env) (s : Schema) : Prop where
  nil : env s.nil = some (.ctor 0 0)
  cons : env s.cons = some (.ctor 1 2)
  recursor : env s.recursor = some literalRecursor
  alias : env s.alias = some (.defn .shared (.ref s.recursor))
  builder : env s.builder = some (.defn .unique (builderExpr s))

instance (env : Env) (s : Schema) : Decidable (SourceMatches env s) :=
  decidable_of_iff
    (env s.nil = some (.ctor 0 0) ∧ env s.cons = some (.ctor 1 2) ∧
      env s.recursor = some literalRecursor ∧
      env s.alias = some (.defn .shared (.ref s.recursor)) ∧
      env s.builder = some (.defn .unique (builderExpr s)))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
      fun h => ⟨h.nil, h.cons, h.recursor, h.alias, h.builder⟩⟩

structure Checked (declarations : List (Address × Decl)) (main : Expr) where
  plan : Plan
  root : Address
  mainEq : main = .app (.ref root) .erased
  source : SourceMatches (Env.ofList declarations) plan.schema
  entry : Env.ofList declarations root = some (.defn .unique (.lam .many plan.literalBody))

def check (declarations : List (Address × Decl)) (main : Expr) (plan : Plan) :
    Option (Checked declarations main) :=
  match main with
  | .app (.ref root) .erased =>
      if hs : SourceMatches (Env.ofList declarations) plan.schema then
        if he : Env.ofList declarations root = some (.defn .unique (.lam .many plan.literalBody)) then
          some { plan, root, mainEq := rfl, source := hs, entry := he }
        else none
      else none
  | _ => none

private def list? (s : Schema) : Expr → Option (List Nat)
  | .ref address => if address == s.nil then some [] else none
  | .app (.app (.ref address) (.lit (.nat n))) tail =>
      if address == s.cons then (list? s tail).map (n :: ·) else none
  | _ => none

def propose (declarations : List (Address × Decl)) (main : Expr) : Option Plan := do
  let .app (.ref root) .erased := main | none
  let env := Env.ofList declarations
  let some (.defn .unique (.lam .many
      (.app (.app (.app (.ref alias) (.ref builder)) (.ref nil)) major))) := env root | none
  let some (.defn .shared (.ref recursor)) := env alias | none
  let some (.defn .unique (.lam .linear (.lam .linear
      (.app (.app (.ref cons) (.var 1)) (.var 0))))) := env builder | none
  let schema : Schema := { nil, cons, recursor, alias, builder }
  let values ← list? schema major
  return { schema, values }

def recognize (declarations : List (Address × Decl)) (main : Expr) :
    Option (Checked declarations main) := do
  let plan ← propose declarations main
  check declarations main plan

def targetDeclarations (plan : Plan) (address : Address) : List (Address × Decl) :=
  [(plan.schema.nil, .ctor 0 0), (plan.schema.cons, .ctor 1 2),
    (address, directRecursor plan.schema)]

structure TargetMatches (env : Env) (s : Schema) (address : Address) : Prop where
  nil : env s.nil = some (.ctor 0 0)
  cons : env s.cons = some (.ctor 1 2)
  recursor : env address = some (directRecursor s)

instance (env : Env) (s : Schema) (address : Address) : Decidable (TargetMatches env s address) :=
  decidable_of_iff
    (env s.nil = some (.ctor 0 0) ∧ env s.cons = some (.ctor 1 2) ∧
      env address = some (directRecursor s))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.nil, h.cons, h.recursor⟩⟩

structure Recovered (declarations : List (Address × Decl)) (main : Expr) where
  checked : Checked declarations main
  address : Address
  addressed : address = (directInstance checked.plan.schema).address
  fresh : address ∉ declarations.map (·.1)
  target : TargetMatches (Env.ofList (targetDeclarations checked.plan address))
    checked.plan.schema address

def recover (declarations : List (Address × Decl)) (main : Expr) :
    Option (Recovered declarations main) := do
  let checked ← recognize declarations main
  let address := (directInstance checked.plan.schema).address
  if hf : address ∉ declarations.map (·.1) then
    if ht : TargetMatches (Env.ofList (targetDeclarations checked.plan address)) checked.plan.schema address then
      some { checked, address, addressed := rfl, fresh := hf, target := ht }
    else none
  else none

end Ix.Compiler.IxIR0.UniqueReverse
