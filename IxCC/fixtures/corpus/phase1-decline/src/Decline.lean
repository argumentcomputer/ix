/-!
The Phase 1 decline corpus (phase 1 plan, MT.4; research §9.4.3): real Lean
programs outside the Phase 1 fragment, each declined with an exact
`stage: code` that the manifest records. A decline is data: a change in what
the compiler accepts shows up as a test failure. The roots that the compiler
has since learnt to compile (`nestedFor`, `mulN`, `unboxMatch`,
`subtypeMatch`) keep their fixtures, with cases (the roots of `Symbols.lean`
compile alone and are declined only together).

Uses `partial` and `unsafe` on purpose (the manifest's `allow_constructs`).
The oracle driver at the end prints the values of the roots with cases.
-/

namespace Decline

/-! ## Closures (`fir: fir.closures`) -/

/-- A function argument applied: an unknown call survives the middle end. -/
def applyArg (f : Nat → Nat) (n : Nat) : Nat := f n

/-- A function argument that grows each iteration: no specialisation removes
it. -/
def iterCompose : Nat → (Nat → Nat) → Nat → Nat
  | 0, f, x => f x
  | k + 1, f, x => iterCompose k (fun y => f (f y)) x

def composeClosure (k n : Nat) : Nat := iterCompose k (· + 1) n

/-- Nested `for` loops (MT.2: `Scalar.impFor`, `Scalar.pyth`). -/
def nestedFor (k : Nat) : Nat := Id.run do
  let mut c := 0
  for _ in [0:k] do
    for _ in [0:k] do
      c := c + 1
  return c

/-! ## Strings

`String.length` reaches the `String` library and a `panic!` message is a string
literal, both string literals in a relevant position (`admit: unsupported`;
under the Ixon v3 decoder `stringLength` was declined at `ingress: decode`). -/

/-- A string literal's length. -/
def stringLength (n : Nat) : Nat := "abc".length + n

/-- `panic!` carries its message as a string. -/
def withPanic (n : Nat) : Nat := if n == 7 then panic! "seven" else n

/-! ## Six parameters (`rt: rt.params`; the entry wrapper passes five) -/

def six (a b c d e f : Nat) : Nat := a + b + c + d + e + f

/-- Five `Nat` parameters and an erased type parameter: still six. -/
def fiveAndType (α : Type) (a b c d e : Nat) : Nat := a + b + c + d + e

/-- Five `Nat` parameters and a proof: still six. -/
def fiveAndProof (a b c d e : Nat) (_h : a ≤ b) : Nat := a + b + c + d + e

/-! ## A recursor with a variable minor (`erase: erase-minor`) -/

noncomputable def recMinor (g : Nat → Nat → Nat) (n : Nat) : Nat := Nat.rec 0 g n

/-! ## Single-field structures matched (`erase: erase-unbox-elim`) -/

structure Wrap where
  n : Nat

def unwrap : Wrap → Nat
  | ⟨n⟩ => n

def unboxMatch (k : Nat) : Nat := unwrap ⟨k⟩

/-- A `Subtype` matched. -/
def subtypeMatch (k : Nat) : Nat :=
  match (⟨k, Nat.le_refl k⟩ : { m : Nat // k ≤ m }) with
  | ⟨m, _⟩ => m

/-! ## Admission (`admit: …`) -/

opaque secret : Nat → Nat

def useOpaque (n : Nat) : Nat := secret n + 1

partial def spin (n : Nat) : Nat := if n == 0 then 0 else spin (n - 1)

def usePartial (n : Nat) : Nat := spin n

unsafe def unsafeId (n : Nat) : Nat := n

unsafe def useUnsafe (n : Nat) : Nat := unsafeId n + 1

noncomputable def useChoice (n : Nat) : Nat := Classical.choice ⟨n⟩

/-! ## Allocation (`alloc: alloc.fallback`, MT.2 finding 1)

A wrong decline: a `for` loop that reads a parameter besides its counter
specialises into a loop function of eight arguments, beyond the internal
convention's seven argument registers, and nothing before allocation
declines it (`plans/x86-phase1/mt/repro/`). -/

def mulN (n k : Nat) : Nat := Id.run do
  let mut c := 1
  for _ in [0:k] do
    c := c * n
  return c

end Decline

/-- The oracle driver: each stdin line `ROOT ARG…` prints one value (only the
roots that compile have cases). -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "Decline.nestedFor", [k] => toString (Decline.nestedFor k)
        | "Decline.mulN", [n, k] => toString (Decline.mulN n k)
        | "Decline.unboxMatch", [k] => toString (Decline.unboxMatch k)
        | "Decline.subtypeMatch", [k] => toString (Decline.subtypeMatch k)
        | _, _ => s!"unknown root {root} {args}"
