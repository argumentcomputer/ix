/-! Lean 4 `tests/compile/tuple.lean` (v4.34.0,
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`; Apache-2.0, see
`../../LICENSES/lean4-LICENSE`), modified for Compilatr.ix: the text up to
`def main` is upstream's, verbatim; `entry` and the corpus oracle driver
replace upstream's `main` (`IO.println (f (1, 2, 3,))`, kept in `upstream/`). -/

@[noinline] def f (a : Nat × Nat × Nat) : Nat:=
  a.fst + a.snd.fst + a.snd.snd

def entry (a b c : Nat) : Nat := f (a, b, c)

/-- The corpus oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "entry", [x, y, z] => toString (entry x y z)
        | _, _ => s!"unknown root {root} {args}"
