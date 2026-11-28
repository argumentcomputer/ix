import IxCCTests.Src.Support

/-! K1 on the eqn route. Each run's clock budget
is `16 ×` Lean's call count (counted by instrumented native twins); the
suite also reports the least clock that succeeds on small inputs, and a
fallback row with no `eqn` entries (brecOn and `WellFounded.fix`). -/

namespace IxCCTests.Src.Runs

open IxCC IxCC.Src IxCCTests.Src
open IxCC.Sem (Result)

/-! ## Call counts of the Lean definitions -/

def fibCalls : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => 1 + fibCalls n + fibCalls (n + 1)

/-- `(result, calls)` of `ack m n`, with an explicit stack (no deep recursion). -/
def ackCalls (m n : Nat) : Nat × Nat := Id.run do
  let mut stack : List Nat := [m]
  let mut n := n
  let mut calls := 0
  for _ in [0:1 <<< 40] do
    match stack with
    | [] => break
    | m :: rest =>
      calls := calls + 1
      match m, n with
      | 0, n' => stack := rest; n := n' + 1
      | m' + 1, 0 => stack := m' :: rest; n := 1
      | m' + 1, n' + 1 => stack := (m' + 1) :: m' :: rest; n := n'
  return (n, calls)

def takCalls : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, _, z => (z, 1)
  | f + 1, x, y, z =>
    if y < x then
      let (a, ca) := takCalls f (x - 1) y z
      let (b, cb) := takCalls f (y - 1) z x
      let (c, cc) := takCalls f (z - 1) x y
      let (r, cr) := takCalls f a b c
      (r, 1 + ca + cb + cc + cr)
    else (z, 1)

def gcdSteps : Nat → Nat → Nat × Nat
  | a, 0 => (a, 1)
  | a, b + 1 =>
    let (r, s) := gcdSteps (b + 1) (a % (b + 1))
    (r, s + 1)
termination_by _ b => b
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

/-- The least clock at which `run` succeeds, by bisection below `hi`. -/
def leastClock (p : Program) (root : CId) (args : List Nat) (hi : Nat) : IO (Option Nat) := do
  let ok := fun k => do return (← runRoot p k root args) matches .ok _
  unless ← ok hi do return none
  let mut lo := 0
  let mut hi := hi
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if ← ok mid then hi := mid else lo := mid
  return some hi

structure Row where
  label : String
  expected : Nat
  calls : Nat
  ms : Nat

def runRow (a : Assert) (l : Loaded) (root : String) (args : List Nat) (expected calls : Nat)
    (budget : Nat := 16 * calls) : IO Row := do
  let r ← rootNamed l root
  let (res, ms) ← timed (runRoot l.program budget r args)
  expect a (natOf res == some expected)
    s!"{root} {args}: {outcome res} at clock {budget}, expected {expected}"
  return { label := s!"{root} {args}", expected, calls, ms }

/-- The required rows: `fib 30`, `ack 3 6`, `tak 20 18 12 6`, `sumLoop 10⁵`
and gcd pairs, on `k1.ixe`, under 60 s. -/
def eqnRoute (a : Assert) : IO (Array Row) := do
  let l ← loadK1
  let mut rows := #[]
  rows := rows.push (← runRow a l "K1.fib" [30] 832040 (fibCalls 30))
  let (ack36, ackC) := ackCalls 3 6
  rows := rows.push (← runRow a l "K1.ack" [3, 6] ack36 ackC)
  let (tak, takC) := takCalls 20 18 12 6
  rows := rows.push (← runRow a l "K1.tak" [20, 18, 12, 6] tak takC)
  rows := rows.push (← runRow a l "K1.sumLoop" [100000] 4999950000 100000 (budget := 64 * 100000))
  for (x, y) in [(832040, 514229), (1071, 462), (2 ^ 40 + 15, 2 ^ 33 + 7), (0, 5), (5, 0)] do
    let (g, steps) := gcdSteps x y
    rows := rows.push (← runRow a l "K1.gcd" [x, y] g steps (budget := 64 * steps + 64))
  let total := rows.foldl (· + ·.ms) 0
  expect a (total < 60000) s!"K1 eqn-route runs took {total} ms (budget 60 s)"
  return rows

/-- Least successful clocks on small inputs, against Lean's call counts. -/
def clockRatios : IO (Array String) := do
  let l ← loadK1
  let mut out := #[]
  for (root, args, calls) in [("K1.fib", [15], fibCalls 15), ("K1.ack", [2, 3], (ackCalls 2 3).2),
      ("K1.tak", [8, 6, 4, 2], (takCalls 8 6 4 2).2), ("K1.sumLoop", [100], 100),
      ("K1.gcd", [832040, 514229], (gcdSteps 832040 514229).2)] do
    let r ← rootNamed l root
    match ← leastClock l.program r args 10000000 with
    | some k => out := out.push s!"{root} {args}: least clock {k}, Lean calls {calls}"
    | none => out := out.push s!"{root} {args}: no success below 10^7"
  return out

/-- The fallback row: no `eqn` entries, so `fib` runs through `brecOn` and
`ack` through `WellFounded.fix` and `Acc.rec` (F3). -/
def fallback (a : Assert) : IO (Array String) := do
  let bytes ← IO.FS.readBinFile (fixtures / "k1/k1.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (fixtures / "k1/equations.json")))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (IxCC.Ixon.V3.decodeAnonymousEnv bytes)
  let l ← match loadEnv {} env { hints with proposals := #[] } with
    | .ok l => pure l
    | .error d => throw (IO.userError s!"fallback load: {d}")
  let mut out := #[]
  for (root, args, expected, calls) in [("K1.fib", [15], 610, fibCalls 15),
      ("K1.ack", [2, 3], 9, (ackCalls 2 3).2)] do
    let r ← rootNamed l root
    let (res, ms) ← timed (runRoot l.program 100000000 r args)
    expect a (natOf res == some expected) s!"fallback {root} {args}: {outcome res}"
    let least ← leastClock l.program r args 100000000
    out := out.push s!"fallback {root} {args} = {expected} in {ms} ms; least clock {least}, Lean calls {calls}"
  return out

end IxCCTests.Src.Runs
