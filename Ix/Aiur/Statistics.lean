module
public import Ix.Aiur.Compiler

/-!
Circuit statistics for Aiur executions.

Given a `CompiledToplevel` and the query counts returned by `execute`, computes
per-circuit width, height (next power of two of the query count), and area
(width × height) for every constrained function and memory circuit. Results are
sorted by area in decreasing order and printed with cumulative area percentages.
-/

public section

namespace Aiur

structure CircuitStats where
  name : String
  width : Nat
  height : Nat
  area : Nat

structure ExecutionStats where
  circuits : Array CircuitStats
  totalArea : Nat

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
        let w := t.functions[i]!.layout.width
        let h := queryCounts[i]!.nextPowerOfTwo
        let name := reverseMap[i]?.getD s!"<fn {i}>"
        acc := acc.push { name, width := w, height := h, area := w * h : CircuitStats }
    acc
  -- One CircuitStats per memory size
  let memoryCircuits := t.memorySizes.mapIdx fun i size =>
    let w := size + 3
    let h := queryCounts[nAllFuns + i]!.nextPowerOfTwo
    { name := s!"memory[{size}]",
      width := w, height := h, area := w * h : CircuitStats }
  let circuits := (functionCircuits ++ memoryCircuits).qsort (·.area > ·.area)
  let totalArea := circuits.foldl (· + ·.area) 0
  { circuits, totalArea }

private def padLeft (s : String) (n : Nat) : String :=
  let pad := n - s.length
  String.ofList (List.replicate pad ' ') ++ s

private def padRight (s : String) (n : Nat) : String :=
  let pad := n - s.length
  s ++ String.ofList (List.replicate pad ' ')

private def formatPercent (area totalArea : Nat) : String :=
  if totalArea == 0 then "0.00%"
  else
    let bps := area * 10000 / totalArea  -- basis points
    let whole := bps / 100
    let frac := bps % 100
    let fracStr := if frac < 10 then s!"0{frac}" else toString frac
    s!"{whole}.{fracStr}%"

def printStats (stats : ExecutionStats) : IO Unit := do
  let wName := stats.circuits.foldl (fun m cs => Nat.max m cs.name.length) 4
  let wWidth := stats.circuits.foldl (fun m cs => Nat.max m (toString cs.width).length) 5
  let wHeight := stats.circuits.foldl (fun m cs => Nat.max m (toString cs.height).length) 6
  let wArea := stats.circuits.foldl (fun m cs => Nat.max m (toString cs.area).length) 4
  let wPct := 7
  let wCum := 7
  let totalW := wName + 1 + wWidth + 1 + wHeight + 1 + wArea + 1 + wPct + 1 + wCum
  let totalWidth := stats.circuits.foldl (· + ·.width) 0
  let sep := String.ofList (List.replicate totalW '-')
  IO.println "=== Circuit Statistics ==="
  IO.println s!"Circuits: {stats.circuits.size}"
  IO.println s!"Total width: {totalWidth}"
  IO.println s!"Total area: {stats.totalArea}"
  IO.println sep
  IO.println s!"{padRight "Name" wName} {padLeft "Width" wWidth} {padLeft "Height" wHeight} {padLeft "Area" wArea} {padLeft "%" wPct} {padLeft "%++" wCum}"
  IO.println sep
  let mut cumArea := 0
  for cs in stats.circuits do
    cumArea := cumArea + cs.area
    let pct := formatPercent cs.area stats.totalArea
    let cum := formatPercent cumArea stats.totalArea
    IO.println s!"{padRight cs.name wName} {padLeft (toString cs.width) wWidth} {padLeft (toString cs.height) wHeight} {padLeft (toString cs.area) wArea} {padLeft pct wPct} {padLeft cum wCum}"

end Aiur

end
