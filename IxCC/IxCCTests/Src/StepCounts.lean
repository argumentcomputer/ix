import IxCCTests.Src.Steps

/-! Pinned SrcEval step counts (`docs/source-steps.md`) on small bench-k1 rows,
and on rows of the sparse casesOn fixture whose arm is not taken (its cost does
not grow with the input), through `ixcc`'s front end. A change to SrcEval's rules or to the front end that
alters the unit changes these numbers; the counting form's agreement with
`Src.run` is checked on each row (`Steps.measure`). -/

namespace IxCCTests.Src.StepCounts

open IxCC IxCC.Src IxCCTests.Src

/-- `(fixture, arguments, result, charged steps, least clock)`. -/
def rows : List (String × List Nat × Nat × Nat × Nat) := [
  ("fib", [10], 55, 6081, 72),
  ("ackermann", [2, 3], 9, 1495, 71),
  ("prime-count", [10], 4, 3620, 117)]

/-- `(root, arguments, result, charged steps, least clock)` on the committed
fixture `phase2-closures/sparse`. Each root's match names one constructor and
ends in a catch-all, so Lean elaborates it through a sparse casesOn, whose
`lazy` row passes the arm by name: at `b = 1` the arm (`n` steps of work) is not
chosen and costs nothing, the same at `n = 1000` and `n = 100000`; at `b = 0`
it is chosen and costs its work. -/
def sparseRows : List (String × List Nat × Nat × Nat × Nat) := [
  ("Sparse.minS", [1, 1000], 1, 50, 7), ("Sparse.minS", [1, 100000], 1, 50, 7),
  ("Sparse.minO", [1, 1000], 1, 48, 7), ("Sparse.minO", [1, 100000], 1, 48, 7),
  ("Sparse.minE", [1, 1000], 1, 120, 13), ("Sparse.minE", [1, 100000], 1, 120, 13),
  ("Sparse.minN", [1, 1000], 1, 51, 9), ("Sparse.minN", [1, 100000], 1, 51, 9),
  ("Sparse.minS", [0, 1000], 1000, 34052, 5011)]

def run (a : Assert) : IO (List String) := do
  let mut out := []
  let dir : System.FilePath := "fixtures/corpus/phase2-closures"
  let bytes ← IO.FS.readBinFile (dir / "sparse.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "sparse.equations.json")))
  for (name, args, value, charged, least) in sparseRows do
    let (inp, ps) ← IO.ofExcept ((Steps.front bytes json [name]).mapError (·.render))
    let root ← IO.ofExcept (Steps.rootOf inp ps.src name)
    let m ← IO.ofExcept (Steps.measure ps.src root args 1000000000)
    expect a (natOf m.result == some value) s!"{name} {args}: {outcome m.result}, expected {value}"
    expect a (m.tally.charged == charged) s!"{name} {args}: {m.tally.charged} charged steps, pinned {charged}"
    expect a (m.leastClock == some least) s!"{name} {args}: least clock {m.leastClock}, pinned {least}"
    out := out ++ [s!"{name} {args} = {value}: {m.tally.charged} charged steps, least clock {m.leastClock.getD 0}"]
  for (name, args, value, charged, least) in rows do
    let dir := fixtures / "bench-k1"
    let bytes ← IO.FS.readBinFile (dir / s!"{name}.ixe")
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / s!"{name}.equations.json")))
    let (inp, ps) ← IO.ofExcept ((Steps.front bytes json ["entry"]).mapError (·.render))
    let root ← IO.ofExcept (Steps.rootOf inp ps.src "entry")
    let m ← IO.ofExcept (Steps.measure ps.src root args 1000000000)
    expect a (natOf m.result == some value) s!"{name} {args}: {outcome m.result}, expected {value}"
    expect a (m.tally.charged == charged) s!"{name} {args}: {m.tally.charged} charged steps, pinned {charged}"
    expect a (m.leastClock == some least) s!"{name} {args}: least clock {m.leastClock}, pinned {least}"
    out := out ++ [s!"{name} {args} = {value}: {m.tally.charged} charged steps, least clock {m.leastClock.getD 0}"]
  return out

end IxCCTests.Src.StepCounts
