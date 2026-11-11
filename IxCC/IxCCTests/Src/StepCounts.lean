import IxCCTests.Src.Steps

/-! Pinned SrcEval step counts (`docs/source-steps.md`) on small bench-k1 rows,
through `ixcc`'s front end. A change to SrcEval's rules or to the front end that
alters the unit changes these numbers; the counting form's agreement with
`Src.run` is checked on each row (`Steps.measure`). -/

namespace IxCCTests.Src.StepCounts

open IxCC IxCC.Src IxCCTests.Src

/-- `(fixture, arguments, result, charged steps, least clock)`. -/
def rows : List (String × List Nat × Nat × Nat × Nat) := [
  ("fib", [10], 55, 6081, 72),
  ("ackermann", [2, 3], 9, 1495, 71),
  ("prime-count", [10], 4, 3620, 117)]

def run (a : Assert) : IO (List String) := do
  let mut out := []
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
