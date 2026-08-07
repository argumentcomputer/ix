module
public import Ix.Aiur.Compiler
public import Ix.Aiur.Semantics.BytecodeFfi
public import Ix.Aiur.Protocol

/-!
Circuit statistics for Aiur executions.

Given a `CompiledToplevel`, the per-circuit `QueryCount`s returned by
`execute`, and the per-circuit `CircuitShape`s read off the compiled Rust
`System`, computes per-circuit committed width, height (the unique-row
count), cache hits (sum of multiplicities), and the FFT cost for every
system circuit — constrained functions, memories, and the fixed-height
`Bytes1`/`Bytes2` byte gadgets.

The FFT cost counts the transforms the pinned prover actually runs, per
committed column, using the raw (unpadded) height `h` so the statistic
stays sensitive to one-row changes (the real prover pads `h` to a power of
two; structural powers of two like the blowup `B` and the quotient degree
`q` stay exact):

- each PCS trace commit (stage 1 width `m`, stage 2 width `s2`) is one
  size-`h` inverse DFT plus `B` size-`h` coset DFTs per column
  (`Radix2DitParallel::coset_lde_batch`), i.e. `(B+1)·F(h)`;
- the quotient runs one forward DFT of the `(q·h) × D` flattened quotient
  (`D·F(q·h)`) and one zero-padded size-`B·h` DFT per chunk column
  (`q·D·F(B·h)`, `lde_from_shifted_coefficients`); committing the
  prebuilt chunk LDE (`Pcs::commit_ldes`) runs no transform,

where `F(0) = 0` and `F(x) = x·log2(max(x, 2))`. Costs are `Float`s to
capture small changes continuously. Results are sorted by FFT cost in
decreasing order and printed with cumulative FFT cost percentages.
-/

public section

namespace Aiur

structure CircuitStats where
  name : String
  width : Nat
  height : Nat
  cacheHits : Nat
  fftCost : Float
  /-- FFT cost at the uncached height `height + cacheHits` (fixed-height
  gadget circuits keep their normal cost). Feeds `totalUncachedFftCost`. -/
  uncachedFftCost : Float

structure ExecutionStats where
  circuits : Array CircuitStats
  totalFftCost : Float
  totalUncachedFftCost : Float
  totalCacheHits : Nat
  deriving Inhabited

/-- Continuous transform-size surrogate: `0` at `0` (an empty circuit is
deactivated by the prover), else `x·log2(max(x, 2))` — the clamp keeps a
height-1 transform nonzero. -/
def transformCost (x : Nat) : Float :=
  if x == 0 then 0.0
  else
    let xf := x.toFloat
    xf * (max xf 2.0).log2

/-- FFT work of one circuit at height `h`: `(B+1)` size-`h` transforms per
trace column (stage 1 and 2 commits), plus the quotient's forward DFT and
its per-chunk-column size-`B·h` LDE transforms. See the module docstring. -/
def fftCost (shape : CircuitShape) (h : Nat) (logBlowup : Nat) : Float :=
  let qD := shape.quotientDegree * G.extensionDegree
  let traceWidth := shape.mainWidth + shape.stage2Width
  ((2 ^ logBlowup) + 1).toFloat * traceWidth.toFloat * transformCost h
    + G.extensionDegree.toFloat * transformCost (shape.quotientDegree * h)
    + qD.toFloat * transformCost ((2 ^ logBlowup) * h)

/-- Committed width of a circuit: stage 1 + stage 2 + quotient chunks. -/
def CircuitShape.committedWidth (shape : CircuitShape) : Nat :=
  shape.mainWidth + shape.stage2Width + shape.quotientDegree * G.extensionDegree

def computeStats (compiled : CompiledToplevel) (queryCounts : Array QueryCount)
    (shapes : Array CircuitShape)
    (logBlowup : Nat := defaultCommitmentParameters.logBlowup) :
    ExecutionStats :=
  let t := compiled.bytecode
  -- Invert nameMap to get FunIdx → String
  let reverseMap := compiled.nameMap.fold (init := (∅ : Std.HashMap Bytecode.FunIdx String))
    fun acc global idx => if !acc.contains idx then acc.insert idx (toString global) else acc
  let nAllFuns := t.functions.size
  let nConstrained := t.functions.foldl (fun n f => if f.constrained then n + 1 else n) 0
  -- Shapes arrive in canonical system order: constrained functions
  -- (ascending index), memories, `Bytes1`, `Bytes2`. A mismatch means the
  -- shapes were built from a different toplevel; misindexing would silently
  -- attribute costs to the wrong circuits.
  if shapes.size != nConstrained + t.memorySizes.size + 2 then
    panic! s!"computeStats: {shapes.size} circuit shapes for \
      {nConstrained} constrained functions + {t.memorySizes.size} memories + 2 gadgets"
  else
  let mkStats (name : String) (shape : CircuitShape) (h hits : Nat) : CircuitStats :=
    { name, width := shape.committedWidth, height := h, cacheHits := hits,
      fftCost := fftCost shape h logBlowup,
      uncachedFftCost := fftCost shape (h + hits) logBlowup }
  let functionCircuits := Id.run do
    let mut acc := #[]
    let mut shapeIdx := 0
    for i in [:nAllFuns] do
      if t.functions[i]!.constrained then
        let shape := shapes[shapeIdx]!
        shapeIdx := shapeIdx + 1
        let qc := queryCounts[i]!
        let name := reverseMap[i]?.getD s!"<fn {i}>"
        acc := acc.push
          (mkStats name shape qc.uniqueRows (qc.totalHits - qc.uniqueRows))
    acc
  let memoryCircuits := t.memorySizes.mapIdx fun i size =>
    let shape := shapes[nConstrained + i]!
    let qc := queryCounts[nAllFuns + i]!
    mkStats s!"memory[{size}]" shape qc.uniqueRows (qc.totalHits - qc.uniqueRows)
  -- The byte gadgets commit full-table traces in every proof: their height
  -- is the (fixed) preprocessed height, independent of the query set, so
  -- they carry no cache-hit counterfactual.
  let gadgetCircuits := #["Bytes1", "Bytes2"].mapIdx fun i name =>
    let shape := shapes[nConstrained + t.memorySizes.size + i]!
    mkStats name shape shape.preprocessedHeight 0
  let circuits := (functionCircuits ++ memoryCircuits ++ gadgetCircuits).qsort
    (·.fftCost > ·.fftCost)
  let totalFftCost := circuits.foldl (· + ·.fftCost) 0.0
  let totalUncachedFftCost := circuits.foldl (· + ·.uncachedFftCost) 0.0
  let totalCacheHits := circuits.foldl (· + ·.cacheHits) 0
  { circuits, totalFftCost, totalUncachedFftCost, totalCacheHits }

private def padLeft (s : String) (n : Nat) : String :=
  let pad := n - s.length
  String.ofList (List.replicate pad ' ') ++ s

private def padRight (s : String) (n : Nat) : String :=
  let pad := n - s.length
  s ++ String.ofList (List.replicate pad ' ')

private def formatPercent (fftCost totalFftCost : Float) : String :=
  if totalFftCost == 0.0 then "0.00%"
  else
    let pct := fftCost * 100.0 / totalFftCost
    let bps := (pct * 100.0).round.toUInt32.toNat
    let whole := bps / 100
    let frac := bps % 100
    let fracStr := if frac < 10 then s!"0{frac}" else toString frac
    s!"{whole}.{fracStr}%"

/-- Scientific notation with a two-decimal mantissa (`1.74e8`). Only used
for nonnegative costs; any nonzero circuit cost is ≥ 1, so the exponent
is never negative. -/
def formatSci (f : Float) : String :=
  if f == 0.0 then "0"
  else
    let e := f.log10.floor
    let cents := (f / (10.0 ^ e) * 100.0).round
    -- Rounding can push the mantissa to 10.00; carry into the exponent.
    let (cents, e) := if cents >= 1000.0 then (100.0, e + 1.0) else (cents, e)
    let cents := cents.toUInt64.toNat
    let frac := cents % 100
    let fracStr := if frac < 10 then s!"0{frac}" else toString frac
    s!"{cents / 100}.{fracStr}e{e.toUInt64.toNat}"

def printStats (stats : ExecutionStats) : IO Unit := do
  let wName := stats.circuits.foldl (fun m cs => Nat.max m cs.name.length) 4
  let wWidth := stats.circuits.foldl (fun m cs => Nat.max m (toString cs.width).length) 5
  let wHeight := stats.circuits.foldl (fun m cs => Nat.max m (toString cs.height).length) 6
  let wHits := stats.circuits.foldl (fun m cs => Nat.max m (toString cs.cacheHits).length) 5
  let formatCost (f : Float) : String :=
    let n := f.round.toUInt64.toNat
    toString n
  let wFftCost := stats.circuits.foldl (fun m cs => Nat.max m (formatSci cs.fftCost).length) 8
  let wPct := 7
  let wCum := 7
  let totalW := wName + 1 + wWidth + 1 + wHeight + 1 + wHits + 1 + wFftCost + 1 + wPct + 1 + wCum
  let totalWidth := stats.circuits.foldl (· + ·.width) 0
  let savedPct :=
    if stats.totalUncachedFftCost == 0.0 then "0.00%"
    else formatPercent (stats.totalUncachedFftCost - stats.totalFftCost) stats.totalUncachedFftCost
  let sep := String.ofList (List.replicate totalW '-')
  IO.println "=== Circuit Statistics ==="
  IO.println s!"Circuits: {stats.circuits.size}"
  IO.println s!"Total width: {totalWidth}"
  IO.println s!"Total FFT cost: {formatCost stats.totalFftCost} ({formatSci stats.totalFftCost})"
  IO.println s!"Total cache hits: {stats.totalCacheHits}"
  IO.println s!"Total saved cost: {savedPct}"
  IO.println sep
  IO.println s!"{padRight "Name" wName} {padLeft "Width" wWidth} {padLeft "Height" wHeight} {padLeft "Hits" wHits} {padLeft "FFT cost" wFftCost} {padLeft "%" wPct} {padLeft "%++" wCum}"
  IO.println sep
  let mut cumFftCost : Float := 0.0
  for cs in stats.circuits do
    cumFftCost := cumFftCost + cs.fftCost
    let pct := formatPercent cs.fftCost stats.totalFftCost
    let cum := formatPercent cumFftCost stats.totalFftCost
    IO.println s!"{padRight cs.name wName} {padLeft (toString cs.width) wWidth} {padLeft (toString cs.height) wHeight} {padLeft (toString cs.cacheHits) wHits} {padLeft (formatSci cs.fftCost) wFftCost} {padLeft pct wPct} {padLeft cum wCum}"

end Aiur

end
