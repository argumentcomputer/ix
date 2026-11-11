/-!
# Roots whose compiled arity is not their declared parameter count

Regression roots for the root-arity check (`docs/closures-design.md`, "Proof
obligation"), written for IxCC (Apache-2.0 OR MIT). Lean does not η-expand a
definition's value to its type, so a root's compiled arity (the leading λs of
the body the table gives it: the kernel value, an equation's body, or a
`csimp` target) can differ from the number of parameters its declared type
shows. Every `Arity.*` root has a type `Nat → … → R` (after its erased
parameters, for the `main8` shapes); the table entries at the end are not
roots. `main` is the oracle driver for `lean --run`: each stdin line
`ROOT ARG…` prints that root's value on the type's number of arguments.
-/

namespace Arity

/-- The function every shape calls; order-sensitive, so a swapped or dropped
argument shows. -/
def g (a b : Nat) : Nat := a * 10 + b

def gb (a b : Nat) : Bool := decide (a < b)

/-! ## Two leading λs, one, none -/

def main1 (a b : Nat) : Nat := g a b
def main2 (a : Nat) : Nat → Nat := fun b => g a b
def main3 (a : Nat) : Nat → Nat := g a
def main4 : Nat → Nat → Nat := g

/-! ## Recursion: point-free in the last argument, and matching on both -/

/-- Structural, point-free in its last argument. -/
def addTo : Nat → Nat → Nat
  | 0 => id
  | n + 1 => fun b => addTo n (b + 2)

/-- Well-founded, point-free in its last argument: the kernel value has no λ
at all, its equation one. -/
def halve (n : Nat) : Nat → Nat :=
  if h : n < 2 then fun b => b else fun b => halve (n / 2) (b + 1)
termination_by n
decreasing_by omega

/-- Pattern matching on both arguments. -/
def pm : Nat → Nat → Nat
  | 0, b => b
  | a + 1, 0 => pm a 1
  | a + 1, b + 1 => pm a b + 2

/-! ## A result type that is a definition of a function type

The declared type shows one parameter; `main7`'s value has two λs. -/

def NatFn : Type := Nat → Nat
def main7 (a : Nat) : NatFn := fun b => g a b
def main7b (a : Nat) : NatFn := g a

/-! ## Erased leading parameters -/

def main8 (_h : 0 < 1) (a b : Nat) : Nat := g a b
def main8t (_α : Type) (a b : Nat) : Nat := g a b
def main8p (_h : 0 < 1) : Nat → Nat → Nat := g

/-! ## Aliases, a partial application, work before the λ, a match -/

def main9 := main1
def main9r := pm
def main10 : Nat → Nat := g 3
def main10c : Nat → Nat := fun b => b + 1
def main11 (a : Nat) : Nat → Nat := let k := a * a; fun b => k + b
def main12 (a : Nat) : Nat → Nat :=
  match a with
  | 0 => id
  | _ => fun b => g a b

/-! ## `Bool` results -/

def mainB3 (a : Nat) : Nat → Bool := gb a
def mainB4 : Nat → Nat → Bool := gb

/-! ## A definition that diverges after one argument (`partial_fixpoint`) -/

def spin (n : Nat) : Nat → Nat := spin (n + 1)
partial_fixpoint

/-! ## Table entries a certificate may choose (not roots) -/

/-- An η-long equation: with it in the table `main4` has two parameters. -/
theorem main4_eta (a b : Nat) : main4 a b = g a b := rfl

def slowDouble (n : Nat) : Nat := n + n
def fastDouble (n : Nat) : Nat := 2 * n
/-- With this entry in the table `slowDouble`'s body is `fastDouble`, a
constant: arity 0. -/
@[csimp] theorem slowDouble_eq : @slowDouble = @fastDouble := by
  funext n
  simp only [slowDouble, fastDouble]
  omega

end Arity

/-- The oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "Arity.main1", [x, y] => toString (Arity.main1 x y)
        | "Arity.main2", [x, y] => toString (Arity.main2 x y)
        | "Arity.main3", [x, y] => toString (Arity.main3 x y)
        | "Arity.main4", [x, y] => toString (Arity.main4 x y)
        | "Arity.addTo", [x, y] => toString (Arity.addTo x y)
        | "Arity.halve", [x, y] => toString (Arity.halve x y)
        | "Arity.pm", [x, y] => toString (Arity.pm x y)
        | "Arity.main7", [x, y] => toString (Arity.main7 x y)
        | "Arity.main7b", [x, y] => toString (Arity.main7b x y)
        | "Arity.main8", [_, x, y] => toString (Arity.main8 (by decide) x y)
        | "Arity.main8t", [_, x, y] => toString (Arity.main8t Nat x y)
        | "Arity.main8p", [_, x, y] => toString (Arity.main8p (by decide) x y)
        | "Arity.main9", [x, y] => toString (Arity.main9 x y)
        | "Arity.main9r", [x, y] => toString (Arity.main9r x y)
        | "Arity.main10", [y] => toString (Arity.main10 y)
        | "Arity.main10c", [y] => toString (Arity.main10c y)
        | "Arity.main11", [x, y] => toString (Arity.main11 x y)
        | "Arity.main12", [x, y] => toString (Arity.main12 x y)
        | "Arity.mainB3", [x, y] => toString (Arity.mainB3 x y)
        | "Arity.mainB4", [x, y] => toString (Arity.mainB4 x y)
        | "Arity.slowDouble", [x] => toString (Arity.slowDouble x)
        | _, _ => s!"unknown root {root} {args}"
