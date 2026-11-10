import IxCCTests.Xv.Alloc.Support
import IxCCTests.Xv.Diff
import IxCCTests.Lir.Kernels
import IxCCTests.Xv.Alloc.Probe

/-!
# The Lir kernels through allocation (the early backend probe's inputs)

Each hand-written kernel of `IxCCTests.Lir.Kernels` is selected,
allocated by linear scan (which must validate, with no fallback) and by all
slots, and run at Xl on the kernel's cases: the expected result at the
exact clock and a timeout one below, as `check-xv-select` runs them at Xv.
The report gives each allocation's static spills, reloads, moves and slots
(at Xl).
-/

namespace IxCCTests.Xv.Alloc.Kernels

open IxCC IxCC.Lir IxCC.Xv IxCCTests.Lir IxCCTests.Xv

structure Row where
  kernel : String
  scan : IxCC.Xv.Alloc.EditCounts
  scanSlots : Nat
  allSlots : IxCC.Xv.Alloc.EditCounts
  allSlotsSlots : Nat
  insts : Nat
  xl : String

def kernels : List Lir.Func :=
  [Lir.Kernels.fib, Lir.Kernels.sumLoop, Lir.Kernels.sumFrom, Lir.Kernels.gcd, Lir.Kernels.natAdd,
    Lir.Kernels.natSub, Lir.Kernels.natDiv, Lir.Kernels.natMod]

/-- Allocate kernel `f` both ways; each must be accepted. -/
def allocate (f : Lir.Func) : Except String (VProgram × LProgram × LProgram × Row) := do
  let q ← match Select.run (Lir.Kernels.program f) with
    | .ok (q, _) => pure q
    | .error e => throw s!"{f.name}: selection: {e.text}"
  let scan ← match IxCC.Xv.Alloc.LinearScan.run {} q.funcs[0]! with
    | .ok o => pure o
    | .error e => throw s!"{f.name}: linear scan: {e}"
  if let .error e := IxCC.Xv.Validate.func {} 0 q.funcs[0]! scan then
    throw s!"{f.name}: linear scan rejected: {e.text}"
  let g ← IxCC.Xv.Validate.run {} q [scan]
  let all ← match IxCC.Xv.Alloc.runAllSlots {} q with
    | .ok r => pure r
    | .error e => throw s!"{f.name}: all slots: {e}"
  let row : Row := { kernel := f.name, scan := scan.counts, scanSlots := scan.numSlots
                     allSlots := countsOf all.outs, allSlotsSlots := all.outs.foldl (· + ·.numSlots) 0
                     insts := IxCCTests.Xv.Diff.xvSize q, xl := g.text }
  return (q, g, all.program, row)

/-- The kernel-evaluation probe's certificates are what linear scan emits
today (their generator is not kept in the repository; regenerate them by
hand from the allocator's output when the allocator changes). -/
def probeCertificates : Except String Unit := do
  for (f, o) in Probe.certificates do
    let q ← match Select.run (Lir.Kernels.program f) with
      | .ok (q, _) => pure q
      | .error e => throw s!"{f.name}: selection: {e.text}"
    match IxCC.Xv.Alloc.LinearScan.run {} q.funcs[0]! with
    | .ok o' => unless o' == o do throw s!"{f.name}: the probe's certificate is not linear scan's output"
    | .error e => throw s!"{f.name}: linear scan: {e}"

/-- Run every case of every kernel at Xl; returns the rows and the number of
outcome checks. -/
def check : Except String (List Row × Nat) := do
  probeCertificates
  let mut rows := #[]
  let mut checks := 0
  for f in kernels do
    let (_, g, a, row) ← allocate f
    rows := rows.push row
    for c in Lir.Kernels.cases.filter (·.kernel == f.name) do
      let args := c.args.map Lir.Kernels.tag
      let mem := Region.initial 0
      let want := IxCCTests.Xv.Diff.expected c.expect
      for (label, prog) in [("linear scan", g), ("all slots", a)] do
        let run (k : Nat) := light (Xl.eval prog {} k args mem Region.ctx)
        match c.charges with
        | some k =>
            unless run k == want do
              throw s!"{f.name} {c.args} ({label}): expected {want.text} at clock {k}, got {(run k).text}"
            checks := checks + 1
            if k > 0 then
              unless run (k - 1) == .timeout do throw s!"{f.name} {c.args} ({label}): clock {k - 1} should time out"
              checks := checks + 1
        | none =>
            unless run 1000000 == want do
              throw s!"{f.name} {c.args} ({label}): expected {want.text}, got {(run 1000000).text}"
            checks := checks + 1
  return (rows.toList, checks)

end IxCCTests.Xv.Alloc.Kernels
