import CompilatrixTests.Support.Rng
import Compilatrix.Lam.Syntax

/-!
# Generated Lam programs

Well-formed, `ModesOk` Lam programs for the middle-end tests (design note 02
§13 item 5): closures and partial application, by-name arguments (a by-name
global's thunks), constructors (`Nat` peeling, `Bool`, a pair, an option),
`case` with and without defaults, projections, primitives, `tick`, `trap`,
recursion through globals (bounded by a decreasing `Nat` in the loop
template, unbounded elsewhere, so some runs time out) and □ in head,
projection, scrutinee and primitive positions, which must be stuck at every
level (06 S38). Each program also has three templates the passes should
transform: a loop with a fixed higher-order parameter (P4), a dictionary
CAF (P3, P2) and a by-name conditional (P1's thunks, P2's β). Programs are
determined by their seed.
-/

namespace CompilatrixTests.Support.LamGen

open Compilatrix Compilatrix.Lam
open CompilatrixTests.Support.RngM

def natZ : Key.CtorKey := .src 1
def natS : Key.CtorKey := .src 2
def bF : Key.CtorKey := .src 3
def bT : Key.CtorKey := .src 4
def pairK : Key.CtorKey := .src 5
def noneK : Key.CtorKey := .src 6
def someK : Key.CtorKey := .src 7

def ctors : List CtorInfo :=
  [{ key := natZ, tag := 0, arity := 0 }, { key := natS, tag := 1, arity := 1 },
   { key := bF, tag := 0, arity := 0 }, { key := bT, tag := 1, arity := 0 },
   { key := pairK, tag := 0, arity := 2 }, { key := noneK, tag := 0, arity := 0 },
   { key := someK, tag := 1, arity := 1 }]

def known : Known := { natZero := natZ, natSucc := natS, boolFalse := bF, boolTrue := bT }

def lit (n : Nat) : Term := .lit (.nat n)
def v (i : Nat) : Term := .var i

/-- The binder modes of each global (its arity is their number). -/
abbrev Sigs := Array (List Mode)

/-- Global ids of the templates. -/
def gRoot : Nat := 0
def gLoop : Nat := 1
def gDict : Nat := 2
def gIte : Nat := 3

/-- `loop f n acc = case n | 0 ⇒ acc | m+1 ⇒ loop f m (f acc)`. -/
def loopBody : Term :=
  .lam .strict {} (.lam .strict {} (.lam .strict {} (.case (v 1)
    [.mk natZ 0 (v 0),
     .mk natS 1 (.tick (.app (.app (.app (.glob gLoop) (v 3) .strict) (v 0) .strict)
       (.app (v 3) (v 1) .strict) .strict))] none)))

/-- A dictionary: `pair (λ a b. a + b) k`. -/
def dictBody (k : Nat) : Term :=
  .con pairK [.lam .strict {} (.lam .strict {} (.prim .natAdd [v 1, v 0])), lit k]

/-- `ite c ~t ~e` (a by-name variant): thunks read in the taken branch. -/
def iteBody : Term :=
  .lam .strict {} (.lam .name {} (.lam .name {} (.case (v 2)
    [.mk bF 0 (v 0), .mk bT 0 (v 1)] none)))

/-- A random term under `env` (the modes of the variables in scope,
innermost first). -/
partial def term (sigs : Sigs) (env : List Mode) (depth : Nat) : RngM Term := do
  let leaf : RngM Term := do
    match ← weighted [6, 3, 1] with
    | 0 => if env.isEmpty then return lit (← below 4) else return .var (← below env.length)
    | 1 => return lit (← below 5)
    | _ => return .box
  if depth == 0 then return ← leaf
  let sub := fun (env : List Mode) => term sigs env (depth - 1)
  match ← weighted [4, 2, 5, 2, 2, 3, 1, 3, 1, 1, 2] with
  | 0 => leaf
  | 1 => return .lam .strict {} (← sub (.strict :: env))
  | 2 => -- a spine headed by a global
    let g ← below sigs.size
    let modes := sigs[g]!
    let lastName := (modes.zipIdx.filter (·.1 == .name)).map (·.2) |>.getLast? |>.map (· + 1)
    let lo := max 1 (lastName.getD 0)
    let n ← range lo (modes.length + 1)
    let mut t : Term := .glob g
    for i in [0:n] do
      let m := modes.getD i .strict
      t := .app t (← sub env) m
    return t
  | 3 => -- a spine headed by a strict variable or a λ
    let strict := env.zipIdx.filter (·.1 == .strict)
    if strict.isEmpty || (← chance 30) then
      return .app (.lam .strict {} (← sub (.strict :: env))) (← sub env) .strict
    else
      let (_, i) ← pick strict.toArray
      return .app (.var i) (← sub env) .strict
  | 4 => return .letE { nonDep := true } (← sub env) (← sub (.strict :: env))
  | 5 => -- a constructor
    match ← below 5 with
    | 0 => return .con bT []
    | 1 => return .con bF []
    | 2 => return .con pairK [← sub env, ← sub env]
    | 3 => return .con someK [← sub env]
    | _ => return .con noneK []
  | 6 => return .proj pairK (← below 2) (← sub env)
  | 7 => -- a case
    let s ← sub env
    let dflt ← if ← chance 25 then some <$> sub env else pure none
    match ← below 4 with
    | 0 =>
      let alts := [Alt.mk natZ 0 (← sub env), .mk natS 1 (← sub (.strict :: env))]
      return .case s (if dflt.isSome && (← chance 50) then alts.take 1 else alts) dflt
    | 1 => return .case s [.mk bF 0 (← sub env), .mk bT 0 (← sub env)] dflt
    | 2 => return .case s [.mk pairK 2 (← sub (.strict :: .strict :: env))] dflt
    | _ => return .case s [.mk noneK 0 (← sub env), .mk someK 1 (← sub (.strict :: env))] dflt
  | 8 =>
    let p ← pick #[Prim.natAdd, .natSub, .natMul, .natBeq, .natBle, .natMod]
    return .prim p [← sub env, ← sub env]
  | 9 => return .tick (← sub env)
  | _ => -- a global's value (not a by-name variant), or a trap
    if ← chance 10 then return .trap
    let plain := (List.range sigs.size).filter fun g => sigs[g]!.all (· == .strict)
    return .glob (← pick plain.toArray)

/-- The root: uses of the templates and a random body over `x`. -/
def rootBody (sigs : Sigs) : RngM Term := do
  let step := Term.lam .strict {} (.prim .natAdd [v 0, lit (← range 1 3)])
  let uses : List Term :=
    [ -- the loop with a fixed step function
      .app (.app (.app (.glob gLoop) step .strict) (v 0) .strict) (lit (← below 3)) .strict,
      -- the dictionary's method, applied
      .app (.app (.proj pairK 0 (.glob gDict)) (v 0) .strict) (.proj pairK 1 (.glob gDict)) .strict,
      -- the by-name conditional
      .app (.app (.app (.glob gIte) (.prim .natBle [v 0, lit 1]) .strict) (lit 7) .name)
        (.prim .natAdd [v 0, lit 1]) .name ]
  let pick1 ← pick uses.toArray
  let rnd ← term sigs [.strict] 4
  match ← below 3 with
  | 0 => return .lam .strict {} pick1
  | 1 => return .lam .strict {} (.letE { nonDep := true } pick1 (.prim .natAdd [v 0, lit 1]))
  | _ => return .lam .strict {} (.letE { nonDep := true } pick1 rnd)

/-- A program of the templates and `extra` random globals. -/
def program (extra : Nat) : RngM Lam.Program := do
  let mut sigs : Sigs := #[[.strict], [.strict, .strict, .strict], [], [.strict, .name, .name]]
  for _ in [0:extra] do
    let arity ← below 3
    sigs := sigs.push (List.replicate arity .strict)
  let mut bodies : Array Term := #[← rootBody sigs, loopBody, dictBody (← below 5), iteBody]
  for g in [4:sigs.size] do
    let arity := sigs[g]!.length
    bodies := bodies.push (Term.lams (List.replicate arity .strict)
      (← term sigs (List.replicate arity .strict) 4))
  let gs : List Global := bodies.toList.zipIdx.map fun (b, g) =>
    { key := if g == gIte then .byName g [] else .const g [], body := b }
  return { globals := Src.NatMap.ofList (gs.zipIdx.map fun (gl, i) => (i, gl)), size := gs.length
           roots := [gRoot], ctors, known }

/-- The program of a seed. -/
def ofSeed (seed : Nat) : Lam.Program :=
  (do program (← below 3)).run' (Rng.ofSeed (UInt64.ofNat seed)) |>.run

end CompilatrixTests.Support.LamGen
