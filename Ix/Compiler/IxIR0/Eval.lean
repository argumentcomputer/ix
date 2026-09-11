import Ix.Compiler.IxIR0.Basic

/-!
# IxIR₀ functional big-step interpreter

`eval` is the definitional semantics of IxIR₀ — the anchor every
backend pass is proved against. Fuel is a pure totality device,
uniformly decremented at the entry of each of the four mutual
functions (`eval`/`apply`/`saturate`/`fire`), which makes termination
trivial and keeps the induction uniform. It is NOT a cost model —
cost lands at IxIR₁. "`e` terminates with `v`" is
`∃ fuel, eval ctx fuel ρ e = .ok v`; fuel-monotonicity is the first
lemma of the erasure-simulation work.

Error taxonomy: `Err.fuel` is the only non-answer (more fuel may
succeed). `Err.stuck` is unreachable on well-typed, well-usaged
inputs — a future theorem. `Err.oracleMissing` marks the
trusted-extern boundary (the `docs/compiler/trusted-extern-ledger.md` ledger).
`Err.unknownRef` is a hole in the closed world; the Merkle-DAG env of
a real program is total over its reachable addresses by construction.
-/

namespace Ix.Compiler.IxIR0

open Ix.Compiler.Ixon (Uses Address)

/-- A global awaiting saturation: values of the form
`pap head [a₁, …, aₖ]` with `k < head.arity`. Carries the arity so
application never re-consults the environment; recursor rules are
looked up only at ι-time. -/
inductive Head where
  | ctor (adr : Address) (tag arity : Nat)
  | rec_ (adr : Address) (arity : Nat)
  | ext (adr : Address) (arity : Nat)
  deriving BEq, Repr

def Head.arity : Head → Nat
  | .ctor _ _ a | .rec_ _ a | .ext _ a => a

/-- Values. Constructor values hold **kept fields only** (never
params); `args` lists are in application order. The `adr` on `ctor`
distinguishes same-tag constructors of different inductives in output
and in the future differential harness — ι matches on `tag` alone. -/
inductive Value where
  | clos (uses : Uses) (env : List Value) (body : Expr)
  | pap (head : Head) (args : List Value)
  | ctor (adr : Address) (tag : Nat) (args : List Value)
  | lit (l : Literal)
  | erased

inductive Err where
  | fuel
  | stuck (msg : String)
  | oracleMissing (adr : Address)
  | unknownRef (adr : Address)
  deriving BEq, Repr

/-- The extern semantics: pure, partial, keyed by address. Each ledger
entry axiomatizes one address's behavior. IO arrives later as
state-token threading through this same interface. -/
abbrev Oracle := Address → List Value → Option Value

structure Ctx where
  env : Env
  oracle : Oracle := fun _ _ => none

/-- View the major premise as a constructor application, peeling Nat
literals when the recursor allows it. -/
def majorCtor (natLit : Bool) : Value → Except Err (Nat × List Value)
  | .ctor _ tag args => .ok (tag, args)
  | .lit (.nat n) =>
    if natLit then
      match n with
      | 0 => .ok (0, [])
      | n + 1 => .ok (1, [.lit (.nat n)])
    else .error (.stuck "literal major premise (natLit disabled)")
  | _ => .error (.stuck "recursor major premise is not a constructor")

mutual

/-- Evaluate `e` under environment `ρ` (de Bruijn: `var i = ρ[i]`,
binding conses). -/
def eval (ctx : Ctx) (fuel : Nat) (ρ : List Value) (e : Expr) :
    Except Err Value :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match e with
    | .var i =>
      match ρ[i]? with
      | some v => .ok v
      | none => .error (.stuck s!"unbound de Bruijn index {i}")
    | .lit l => .ok (.lit l)
    | .erased => .ok .erased
    | .lam u body => .ok (.clos u ρ body)
    | .letE _ val body => do
      let v ← eval ctx fuel ρ val
      eval ctx fuel (v :: ρ) body
    | .app fn arg => do
      let f ← eval ctx fuel ρ fn
      let a ← eval ctx fuel ρ arg
      apply ctx fuel f a
    | .proj i s => do
      match ← eval ctx fuel ρ s with
      | .ctor _ _ args =>
        match args[i]? with
        | some v => .ok v
        | none => .error (.stuck s!"projection {i} out of bounds")
      | .erased => .ok .erased
      | _ => .error (.stuck "projection from a non-constructor value")
    | .ref a =>
      match ctx.env a with
      | none => .error (.unknownRef a)
      | some (.defn _ body) => eval ctx fuel [] body
      | some (.ctor tag arity) => saturate ctx fuel (.ctor a tag arity) []
      | some (.recursor numArgs _ _) => .ok (.pap (.rec_ a (numArgs + 1)) [])
      | some (.extern arity) => saturate ctx fuel (.ext a arity) []
  termination_by fuel

def apply (ctx : Ctx) (fuel : Nat) (f a : Value) : Except Err Value :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match f with
    | .clos _ ρ body => eval ctx fuel (a :: ρ) body
    | .pap h args => saturate ctx fuel h (args ++ [a])
    | .erased => .ok .erased
    | _ => .error (.stuck "application of a non-function value")
  termination_by fuel

/-- Fire a head at arity, else fold into a partial application.
Called with fresh heads (arity-0 ctors/externs fire at `ref`-time)
and after every argument. -/
def saturate (ctx : Ctx) (fuel : Nat) (h : Head) (args : List Value) :
    Except Err Value :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    if args.length == h.arity then fire ctx fuel h args
    else .ok (.pap h args)
  termination_by fuel

def fire (ctx : Ctx) (fuel : Nat) (h : Head) (args : List Value) :
    Except Err Value :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match h with
    | .ctor a tag _ => .ok (.ctor a tag args)
    | .ext a _ =>
      match ctx.oracle a args with
      | some v => .ok v
      | none => .error (.oracleMissing a)
    | .rec_ a arity =>
      match ctx.env a with
      | some (.recursor _ natLit rules) =>
        match args.getLast? with
        | none => .error (.stuck "recursor fired with no arguments")
        | some major => do
          let (tag, fields) ← majorCtor natLit major
          match rules[tag]? with
          | none => .error (.stuck s!"no recursor rule for constructor tag {tag}")
          | some rule =>
            if fields.length != rule.fields then
              .error (.stuck "constructor field count does not match recursor rule")
            else
              eval ctx fuel
                (fields.reverse ++ args.dropLast.reverse
                  ++ [.pap (.rec_ a arity) []])
                rule.rhs
      | _ => .error (.stuck "recursor head does not resolve to a recursor declaration")
  termination_by fuel

end

/-- Evaluate a closed expression. -/
def Ctx.run (ctx : Ctx) (e : Expr) (fuel : Nat := 100000) :
    Except Err Value :=
  eval ctx fuel [] e

/-! Elaboration-time smoke tests (pure — no FFI, so `#guard` is fine
here; contrast `Tests.lean`). The full example suite lives in
`Examples.lean`. -/

private def emptyCtx : Ctx := { env := Env.empty }

#guard
  match emptyCtx.run (.app (.lam .many (.var 0)) (.lit (.nat 7))) with
  | .ok (.lit (.nat 7)) => true
  | _ => false

#guard
  match emptyCtx.run (.app .erased (.lit (.nat 1))) with
  | .ok .erased => true
  | _ => false

end Ix.Compiler.IxIR0
