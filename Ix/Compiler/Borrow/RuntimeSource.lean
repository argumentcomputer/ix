import Ix.Compiler.Borrow.Sources
import Ix.Compiler.IxIR0.RecursionSim
import Ix.Compiler.IxIR2.Borrow.OpenResources

namespace Ix.Compiler.Borrow.Runtime

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR0
open Ix.Compiler.IxIR0.Recursion (Evaluates Applies evaluatesDef evaluatesLam evaluatesVar
  evaluatesApp evaluatesLet evaluatesLit evaluatesRecursor appliesClosure appliesRecursor)

/-- The canonical function and constructor declarations contain no runtime
input. Removing B1's closed application also removes its literal payload. -/
def source (depth : Nat) : Except String Coverage.Source := do
  let closed ← Examples.source depth true
  let some worker := closed.constants[2]? | throw "borrow source worker is missing"
  return { closed with
    name := s!"read-tag-runtime-{depth}"
    constants := closed.constants.take 5
    root := worker.1
    literals := [11, 22] }

namespace Source

def reader (zeroResult succResult : Nat) : Decl :=
  .recursor 0 false #[{ fields := 0, rhs := .lit (.nat zeroResult) },
    { fields := 1, rhs := .lit (.nat succResult) }]

def forwardBody (callee : Address) : Expr := .app (.ref callee) (.var 0)

def twiceBody (callee : Address) : Expr :=
  .letE .many (.app (.ref callee) (.var 0)) (.app (.ref callee) (.var 1))

inductive Chain (env : Env) (zeroResult succResult : Nat) : Address → Type where
  | reader (address : Address) (found : env address = some (reader zeroResult succResult)) :
      Chain env zeroResult succResult address
  | forward (address callee : Address)
      (found : env address = some (.defn .shared (.lam .many (forwardBody callee))))
      (tail : Chain env zeroResult succResult callee) : Chain env zeroResult succResult address

def Chain.depth {env zeroResult succResult address} : Chain env zeroResult succResult address → Nat
  | .reader .. => 0
  | .forward _ _ _ tail => tail.depth + 1

def Chain.value {env zeroResult succResult address} : Chain env zeroResult succResult address → Value
  | .reader address _ => .pap (.rec_ address 1) []
  | .forward _ callee .. => .clos .many [] (forwardBody callee)

def recognizeChain (env : Env) (zeroResult succResult : Nat) :
    Nat → (address : Address) → Option (Chain env zeroResult succResult address)
  | 0, _ => none
  | fuel + 1, address =>
      if found : env address = some (reader zeroResult succResult) then
        some (.reader address found)
      else do
        let some (.defn .shared (.lam .many (.app (.ref callee) (.var 0)))) := env address | none
        let tail ← recognizeChain env zeroResult succResult fuel callee
        if found : env address = some (.defn .shared (.lam .many (forwardBody callee))) then
          some (.forward address callee found tail)
        else none

structure Shape (declarations : List (Address × Decl)) (main : Expr) (zeroResult succResult : Nat) where
  root : Address
  worker : Address
  callee : Address
  mainEq : main = .ref root
  rootAt : Env.ofList declarations root = some (.defn .shared (.ref worker))
  workerAt : Env.ofList declarations worker = some (.defn .shared (.lam .many (twiceBody callee)))
  chain : Chain (Env.ofList declarations) zeroResult succResult callee

def recognize (declarations : List (Address × Decl)) (main : Expr)
    (zeroResult succResult fuel : Nat) : Option (Shape declarations main zeroResult succResult) := do
  let .ref root := main | none
  let env := Env.ofList declarations
  let some (.defn .shared (.ref worker)) := env root | none
  let some (.defn .shared (.lam .many (.letE .many
      (.app (.ref callee) (.var 0)) (.app (.ref _) (.var 1))))) := env worker | none
  let chain ← recognizeChain env zeroResult succResult fuel callee
  if mainEq : main = .ref root then
    if rootAt : env root = some (.defn .shared (.ref worker)) then
      if workerAt : env worker = some (.defn .shared (.lam .many (twiceBody callee))) then
        some ⟨root, worker, callee, mainEq, rootAt, workerAt, chain⟩
      else none
    else none
  else none

/-- Constructor payloads are unrestricted. The reader observes only the
outer tag and arity; the successor field may itself represent a large heap. -/
inductive Argument where
  | zero (constructor : Address)
  | succ (constructor : Address) (field : Value)

def Argument.value : Argument → Value
  | .zero constructor => .ctor constructor 0 []
  | .succ constructor field => .ctor constructor 1 [field]

def Argument.target (field : IxIR2.Eval.RVal) : Argument → IxIR2.Borrow.Open.Major
  | .zero _ => .zero
  | .succ .. => .succ field

def Argument.result (zeroResult succResult : Nat) : Argument → Nat
  | .zero _ => zeroResult
  | .succ .. => succResult

theorem Chain.evaluates {ctx : Ctx} {zeroResult succResult address}
    (chain : Chain ctx.env zeroResult succResult address) (env : List Value) :
    Evaluates ctx env (.ref address) chain.value := by
  cases chain with
  | reader _ found => exact evaluatesRecursor found
  | forward _ _ found _ => exact evaluatesDef found (evaluatesLam ctx [] .many _)

theorem Chain.applies {ctx : Ctx} {zeroResult succResult address}
    (chain : Chain ctx.env zeroResult succResult address) (argument : Argument) :
    Applies ctx chain.value argument.value (.lit (.nat (argument.result zeroResult succResult))) := by
  induction chain with
  | reader address found =>
      cases argument with
      | zero constructor =>
          exact appliesRecursor found rfl rfl rfl (evaluatesLit ctx _ _)
      | succ constructor field =>
          exact appliesRecursor found rfl rfl rfl (evaluatesLit ctx _ _)
  | forward address callee found tail ih =>
      exact appliesClosure (evaluatesApp (tail.evaluates _) (evaluatesVar rfl) ih)

def Shape.value {declarations main zeroResult succResult}
    (shape : Shape declarations main zeroResult succResult) : Value :=
  .clos .many [] (twiceBody shape.callee)

theorem Shape.evaluates {declarations main zeroResult succResult}
    (shape : Shape declarations main zeroResult succResult) :
    Evaluates { env := Env.ofList declarations } [] main shape.value := by
  simpa only [shape.mainEq, Shape.value] using
    (evaluatesDef shape.rootAt (evaluatesDef shape.workerAt
      (evaluatesLam { env := Env.ofList declarations } [] .many _)))

theorem Shape.applies {declarations main zeroResult succResult}
    (shape : Shape declarations main zeroResult succResult) (argument : Argument) :
    Applies { env := Env.ofList declarations } shape.value argument.value
      (.lit (.nat (argument.result zeroResult succResult))) := by
  have applied := Chain.applies (ctx := { env := Env.ofList declarations }) shape.chain argument
  apply appliesClosure
  apply evaluatesLet
  · exact evaluatesApp (shape.chain.evaluates _) (evaluatesVar rfl) applied
  · exact evaluatesApp (shape.chain.evaluates _) (evaluatesVar rfl) applied

theorem Argument.target_result (schema : IxIR2.Borrow.Open.Schema) (argument : Argument) (field : IxIR2.Eval.RVal) :
    (argument.target field).result schema = argument.result schema.zeroResult schema.succResult := by
  cases argument <;> rfl

end Source
end Ix.Compiler.Borrow.Runtime
