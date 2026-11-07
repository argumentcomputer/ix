/-! Lean 4 `tests/compile/typeFormerPolymorphism.lean` (v4.34.0,
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`; Apache-2.0, see
`../../LICENSES/lean4-LICENSE`), modified for IxCC: the text up to
`def main` is upstream's, verbatim; `entry` and the corpus oracle driver
replace upstream's `main` (which prints `(foo Nat (Type 0) alwaysNat 42).1`,
kept in `upstream/`). -/
@[noinline]
def foo (α : Type 0) (β : Type 1) (f : α → β) (a : α) : α × β × (α → β) × (α → β) :=
  ⟨a, f a, f, f⟩

def alwaysNat (_ : Nat) : Type 0 := Nat

def entry (n : Nat) : Nat := (foo Nat (Type 0) alwaysNat n).1

/-- The corpus oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "entry", [x] => toString (entry x)
        | _, _ => s!"unknown root {root} {args}"
