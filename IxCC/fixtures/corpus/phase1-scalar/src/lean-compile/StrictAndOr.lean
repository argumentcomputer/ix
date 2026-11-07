/-! Lean 4 `tests/compile/strictAndOr.lean` (v4.34.0,
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`; Apache-2.0, see
`../../LICENSES/lean4-LICENSE`), modified for IxCC: the upstream file
is only a `main` printing core's `strictOr` and `strictAnd` on the four
Boolean pairs (kept in `upstream/`). Here each is a closure root over
`Nat`-encoded Booleans (`0` is `false`), and `main` is the corpus oracle
driver. -/

def entryStrictOr (a b : Nat) : Bool := strictOr (a != 0) (b != 0)

def entryStrictAnd (a b : Nat) : Bool := strictAnd (a != 0) (b != 0)

/-- The corpus oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "entryStrictOr", [x, y] => toString (entryStrictOr x y)
        | "entryStrictAnd", [x, y] => toString (entryStrictAnd x y)
        | _, _ => s!"unknown root {root} {args}"
