module
public import Ix.Aiur.Compiler

/-!
Circuit statistics for Aiur executions.

Given a `CompiledToplevel` and the query counts returned by `execute`, computes
per-circuit width, height (the query count), and the FFT cost
(width × height × log2(height)) for every constrained function and memory
circuit. The FFT cost is a Float to capture small changes continuously.
Results are sorted by FFT cost in decreasing order and printed with cumulative
FFT cost percentages.
-/

public section

namespace Aiur

structure CircuitStats where
  name : String
  width : Nat
  height : Nat
  fftCost : Float

structure ExecutionStats where
  circuits : Array CircuitStats
  totalFftCost : Float

-- Clamp to at least 2 so that log2 is at least 1, avoiding zero cost for h = 1
def fftCost (w h : Nat) : Float :=
  if h == 0 then 0.0
  else
    let wf := w.toFloat
    let hf := h.toFloat
    wf * hf * (max hf 2.0).log2

def computeStats (compiled : CompiledToplevel) (queryCounts : Array Nat) :
    ExecutionStats :=
  let t := compiled.bytecode
  -- Invert nameMap to get FunIdx → String
  let reverseMap := compiled.nameMap.fold (init := (∅ : Std.HashMap Bytecode.FunIdx String))
    fun acc global idx => if !acc.contains idx then acc.insert idx (toString global) else acc
  let nAllFuns := t.functions.size
  -- One CircuitStats per constrained function
  let functionCircuits := Id.run do
    let mut acc := #[]
    for i in [:nAllFuns] do
      if t.functions[i]!.constrained then
        let w := t.functions[i]!.layout.totalWidth
        let h := queryCounts[i]!
        let name := reverseMap[i]?.getD s!"<fn {i}>"
        acc := acc.push { name, width := w, height := h, fftCost := fftCost w h : CircuitStats }
    acc
  -- One CircuitStats per memory size
  let memoryCircuits := t.memorySizes.mapIdx fun i size =>
    -- Apart from the values, accounted by `size`, there are also the multiplicity, selector and pointer
    -- in the first stage, and in the second stage there is the running accumulator and the inverse of the message,
    -- which are 4 Goldilock elements each
    let w := size + 11
    let h := queryCounts[nAllFuns + i]!
    { name := s!"memory[{size}]",
      width := w, height := h, fftCost := fftCost w h : CircuitStats }
  let circuits := (functionCircuits ++ memoryCircuits).qsort (·.fftCost > ·.fftCost)
  let totalFftCost := circuits.foldl (· + ·.fftCost) 0.0
  { circuits, totalFftCost }

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

def printStats (stats : ExecutionStats) : IO Unit := do
  let wName := stats.circuits.foldl (fun m cs => Nat.max m cs.name.length) 4
  let wWidth := stats.circuits.foldl (fun m cs => Nat.max m (toString cs.width).length) 5
  let wHeight := stats.circuits.foldl (fun m cs => Nat.max m (toString cs.height).length) 6
  let formatCost (f : Float) : String :=
    let n := f.round.toUInt64.toNat
    toString n
  let wFftCost := stats.circuits.foldl (fun m cs => Nat.max m (formatCost cs.fftCost).length) 7
  let wPct := 7
  let wCum := 7
  let totalW := wName + 1 + wWidth + 1 + wHeight + 1 + wFftCost + 1 + wPct + 1 + wCum
  let totalWidth := stats.circuits.foldl (· + ·.width) 0
  let sep := String.ofList (List.replicate totalW '-')
  IO.println "=== Circuit Statistics ==="
  IO.println s!"Circuits: {stats.circuits.size}"
  IO.println s!"Total width: {totalWidth}"
  IO.println s!"Total FFT cost: {formatCost stats.totalFftCost}"
  IO.println sep
  IO.println s!"{padRight "Name" wName} {padLeft "Width" wWidth} {padLeft "Height" wHeight} {padLeft "FFT cost" wFftCost} {padLeft "%" wPct} {padLeft "%++" wCum}"
  IO.println sep
  let mut cumFftCost : Float := 0.0
  for cs in stats.circuits do
    cumFftCost := cumFftCost + cs.fftCost
    let pct := formatPercent cs.fftCost stats.totalFftCost
    let cum := formatPercent cumFftCost stats.totalFftCost
    IO.println s!"{padRight cs.name wName} {padLeft (toString cs.width) wWidth} {padLeft (toString cs.height) wHeight} {padLeft (formatCost cs.fftCost) wFftCost} {padLeft pct wPct} {padLeft cum wCum}"

end Aiur

end
