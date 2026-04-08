module
public import Ix.Aiur.Compiler

/-!
Circuit statistics for Aiur executions.

Given a `CompiledToplevel` and the query counts returned by `execute`, computes
per-circuit width, height (next power of two of the query count), and the FFT
cost (width × height × log2(height)) for every constrained function and memory
circuit. Results are sorted by FFT cost in decreasing order and printed with
cumulative FFT cost percentages.
-/

public section

namespace Aiur

structure CircuitStats where
  name : String
  width : Nat
  height : Nat
  fftCost : Nat

structure ExecutionStats where
  circuits : Array CircuitStats
  totalFftCost : Nat

def fftCost (w h : Nat) : Nat := w * h * (max h.log2 1)

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
        let h := queryCounts[i]!.nextPowerOfTwo
        let name := reverseMap[i]?.getD s!"<fn {i}>"
        acc := acc.push { name, width := w, height := h, fftCost := fftCost w h : CircuitStats }
    acc
  -- One CircuitStats per memory size
  let memoryCircuits := t.memorySizes.mapIdx fun i size =>
    let w := size + 3
    let h := queryCounts[nAllFuns + i]!.nextPowerOfTwo
    { name := s!"memory[{size}]",
      width := w, height := h, fftCost := fftCost w h : CircuitStats }
  let circuits := (functionCircuits ++ memoryCircuits).qsort (·.fftCost > ·.fftCost)
  let totalFftCost := circuits.foldl (· + ·.fftCost) 0
  { circuits, totalFftCost }

private def padLeft (s : String) (n : Nat) : String :=
  let pad := n - s.length
  String.ofList (List.replicate pad ' ') ++ s

private def padRight (s : String) (n : Nat) : String :=
  let pad := n - s.length
  s ++ String.ofList (List.replicate pad ' ')

private def formatPercent (fftCost totalFftCost : Nat) : String :=
  if totalFftCost == 0 then "0.00%"
  else
    let bps := fftCost * 10000 / totalFftCost  -- basis points
    let whole := bps / 100
    let frac := bps % 100
    let fracStr := if frac < 10 then s!"0{frac}" else toString frac
    s!"{whole}.{fracStr}%"

def printStats (stats : ExecutionStats) : IO Unit := do
  let wName := stats.circuits.foldl (fun m cs => Nat.max m cs.name.length) 4
  let wWidth := stats.circuits.foldl (fun m cs => Nat.max m (toString cs.width).length) 5
  let wHeight := stats.circuits.foldl (fun m cs => Nat.max m (toString cs.height).length) 6
  let wFftCost := stats.circuits.foldl (fun m cs => Nat.max m (toString cs.fftCost).length) 7
  let wPct := 7
  let wCum := 7
  let totalW := wName + 1 + wWidth + 1 + wHeight + 1 + wFftCost + 1 + wPct + 1 + wCum
  let totalWidth := stats.circuits.foldl (· + ·.width) 0
  let sep := String.ofList (List.replicate totalW '-')
  IO.println "=== Circuit Statistics ==="
  IO.println s!"Circuits: {stats.circuits.size}"
  IO.println s!"Total width: {totalWidth}"
  IO.println s!"Total FFT cost: {stats.totalFftCost}"
  IO.println sep
  IO.println s!"{padRight "Name" wName} {padLeft "Width" wWidth} {padLeft "Height" wHeight} {padLeft "FFT cost" wFftCost} {padLeft "%" wPct} {padLeft "%++" wCum}"
  IO.println sep
  let mut cumFftCost := 0
  for cs in stats.circuits do
    cumFftCost := cumFftCost + cs.fftCost
    let pct := formatPercent cs.fftCost stats.totalFftCost
    let cum := formatPercent cumFftCost stats.totalFftCost
    IO.println s!"{padRight cs.name wName} {padLeft (toString cs.width) wWidth} {padLeft (toString cs.height) wHeight} {padLeft (toString cs.fftCost) wFftCost} {padLeft pct wPct} {padLeft cum wCum}"

end Aiur

end
