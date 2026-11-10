/-!
# Higher-order programs for P8 (closed-world defunctionalisation)

The workloads of the closures design (`docs/closures-design.md`, "Exit
criteria"), written for IxCC (Apache-2.0 OR MIT): real Lean programs whose
closures the Phase 1 middle end does not always remove. Every `Closures.*`
definition named in `corpus.json` is a closure root (at most five `Nat`
parameters, a `Nat` result). `main` is the oracle driver for `lean --run`:
each stdin line `ROOT ARG…` prints that root's value on those arguments.

`composeClosure` repeats `Decline.composeClosure`
(`fixtures/corpus/phase1-decline/src/Decline.lean`) word for word.
-/

namespace Closures

/-! ## A closure that grows on every iteration -/

def iterCompose : Nat → (Nat → Nat) → Nat → Nat
  | 0, f, x => f x
  | k + 1, f, x => iterCompose k (fun y => f (f y)) x

def composeClosure (k n : Nat) : Nat := iterCompose k (· + 1) n

/-! ## Dictionary-passing polymorphic recursion

The recursive call of `sizeAt` is at `α × α`: its dictionary is built from
the caller's, a new one at every level, so no specialisation on a finite set
of dictionaries removes it. The class has two methods, so a dictionary is a
constructor whose first field is a closure. -/

class Measure (α : Type) where
  size : α → Nat
  weight : Nat

instance : Measure Nat := ⟨fun n => n, 1⟩

instance {α : Type} [Measure α] : Measure (α × α) :=
  ⟨fun p => Measure.size p.1 + Measure.size p.2, 2 * Measure.weight α⟩

def sizeAt {α : Type} [Measure α] : Nat → α → Nat
  | 0, x => Measure.size x + Measure.weight α
  | n + 1, x => sizeAt n (x, x)

def polyRec (k n : Nat) : Nat := sizeAt k n

/-! ## A `StateT`-over-`Except` loop -/

def step (limit : Nat) : StateT Nat (Except Nat) Unit := do
  let s ← get
  if s ≥ limit then throw s
  set (s + 2)

def steps (limit : Nat) : Nat → StateT Nat (Except Nat) Unit
  | 0 => pure ()
  | n + 1 => do
    step limit
    steps limit n

def stateLoop (n limit : Nat) : Nat :=
  match (steps limit n).run 1 with
  | .ok ((), s) => s
  | .error e => 1000 + e

/-! ## Partial and over-application through a stored closure

`scale` takes one argument and returns a closure, so applying the stored
`scale` to two arguments over-applies it; `add2` is applied to one argument,
then to the next. The record is rebuilt with a new captured value at every
iteration. -/

structure Ops where
  add2 : Nat → Nat → Nat
  scale : Nat → Nat → Nat

def mkOps (k : Nat) : Ops :=
  { add2 := fun a b => a + b + k
    scale := fun a => let c := a * k + 1; fun b => c * b }

def useOps : Nat → Ops → Nat → Nat
  | 0, _, acc => acc
  | n + 1, ops, acc =>
    let inc := ops.add2 n
    let acc := inc acc
    let acc := ops.scale n acc % 1000
    useOps n (mkOps (acc % 7)) acc

def storedApply (n k : Nat) : Nat := useOps n (mkOps k) 1

/-! ## A fuel-indexed record of closures (the shape of IxCK's `coreKnot`)

Each level's closures capture the record one fuel level down. -/

structure Core where
  even : Nat → Bool
  odd : Nat → Bool
  depth : Nat → Nat

def coreKnot : Nat → Core
  | 0 => { even := fun _ => false, odd := fun _ => false, depth := fun _ => 0 }
  | fuel + 1 =>
    let r := coreKnot fuel
    { even := fun n => match n with
        | 0 => true
        | m + 1 => r.odd m
      odd := fun n => match n with
        | 0 => false
        | m + 1 => r.even m
      depth := fun n => r.depth n + 1 }

def knot (fuel n : Nat) : Nat :=
  let c := coreKnot fuel
  (if c.even n then 100 else 0) + c.depth n

end Closures

/-- The oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "Closures.composeClosure", [k, n] => toString (Closures.composeClosure k n)
        | "Closures.polyRec", [k, n] => toString (Closures.polyRec k n)
        | "Closures.stateLoop", [n, limit] => toString (Closures.stateLoop n limit)
        | "Closures.storedApply", [n, k] => toString (Closures.storedApply n k)
        | "Closures.knot", [fuel, n] => toString (Closures.knot fuel n)
        | _, _ => s!"unknown root {root} {args}"
