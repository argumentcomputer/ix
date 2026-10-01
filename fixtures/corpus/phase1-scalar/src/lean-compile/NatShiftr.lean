/-! Lean 4 `tests/compile/nat_shiftr.lean` (v4.34.0,
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`; Apache-2.0, see
`../../LICENSES/lean4-LICENSE`), modified for Compilatr.ix: the text up to
`def main` is upstream's, verbatim (`test` prints `a >>> b` for twelve shift
counts); `entry` is that shift as a closure root, and the corpus oracle driver
replaces upstream's `main` (fourteen values of `a`, kept in `upstream/`; the
cases of `corpus.json` are its 168 lines). -/
def test (a : Nat) : IO Unit :=
  for b in #[0, 1, 14, 15, 16, 17, 31, 32, 33, 63, 64, 65] do
    IO.println f!"{a >>> b}"

def entry (a b : Nat) : Nat := a >>> b

/-- The corpus oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "entry", [x, y] => toString (entry x y)
        | _, _ => s!"unknown root {root} {args}"
