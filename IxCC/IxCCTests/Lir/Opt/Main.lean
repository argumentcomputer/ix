import IxCCTests.Lir.Opt.Tests

/-! Standalone test & benchmark runner for `Lir.Opt`. -/

open IxCCTests.Lir.Opt

def main (args : List String) : IO UInt32 := do
  IO.println "=== Lir.Opt Unit Tests ==="
  unitAlgGvn
  IO.println "  [ok] algebraic simplification, GVN/CSE, copy prop, DCE, narrow-width, branch/interval/brOvf fold"
  unitLicm
  IO.println "  [ok] natural-loop LICM (inv param sub, preheader insert, pure hoist, fail-guard hoist)"
  unitDivMagic
  IO.println "  [ok] constant unsigned div/mod strength reduction (pow2 + w64/w32 Granlund-Montgomery)"
  unitMemory
  IO.println "  [ok] store-to-load forwarding, load CSE across disjoint stores, intra-block DSE"
  unitRotateLeaParity
  IO.println "  [ok] ror32/ror64 peephole, 3-address lea .addr folding, parity & even-addC tag cancellation"
  unitStructural
  IO.println "  [ok] helper/self inlining (with .tail in callee), odd-loop versioning, 4x unrolling, diamond if-conversion"

  IO.println "=== Lir.Opt Negative-Control Mutant Suite ==="
  let nMut ← negativeControls
  IO.println s!"  [ok] {nMut}/{nMut} unsound mutants rejected by Lir.Opt.check"

  IO.println "=== Lir.Opt Lir.Gen Fuzz Suite ==="
  let (nFuzz, nChanged) ← fuzzSuite 100
  IO.println s!"  [ok] {nFuzz} generated programs validated (check + wellFormed + eval parity; {nChanged} transformed)"

  unless args.contains "--no-bench" do
    IO.println "=== K1 Before vs After (Backend.compile vs Backend.compileOpt) ==="
    for line in (← benchK1) do
      IO.println line
    IO.println "=== K2/K3 Before vs After (Heap alloc & Nat div/mod 10) ==="
    for line in (← benchK2K3) do
      IO.println line

  IO.println "ALL Lir.Opt TESTS PASSED."
  return 0
