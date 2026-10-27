import Aiur.Optimized.Propagation
import Aiur.Optimized.Grouping.Snapshot
import Lean

/-! Isolated physical-chip snapshots for profiling value propagation. -/
namespace IxVM.PropagationBench
open Aiur
open Lean Optimized

def write [ToJson F] (path : String) (chip : Circuit.Chip F) : IO Unit :=
  IO.FS.writeFile path (toJson chip).compress

def run [Field F] [DecidableEq F] [FromJson F] (path : String)
    (trace : Bool := false) : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let source : Circuit.Chip F ← IO.ofExcept (fromJson? json)
  IO.eprintln s!"Loaded {source.name}: {source.numVars} columns, {source.constraints.length} equations"
  let start ← IO.monoMsNow
  if !trace then
    let result ← IO.ofExcept (Propagation.run source)
    unless result.chip.wellFormed do throw (IO.userError "propagation produced an invalid chip")
    IO.eprintln s!"Propagation: {(← IO.monoMsNow) - start}ms, {result.chip.numVars} columns"
    return
  let mut chip := source
  for iteration in [:source.numVars] do
    let start ← IO.monoMsNow
    let proposal := Propagation.proposal? chip
    IO.eprintln s!"{iteration}: candidate id {proposal.map (·.candidate.id)}"
    IO.eprintln s!"{iteration}: candidate {(← IO.monoMsNow) - start}ms"
    let some proposal := proposal | break
    let start ← IO.monoMsNow
    let some checked := proposal.check chip | throw (IO.userError "candidate certificate rejected")
    IO.eprintln s!"{iteration}: certificate {(← IO.monoMsNow) - start}ms"
    let start ← IO.monoMsNow
    chip := Propagation.rewrite chip id checked.val.replace
    IO.eprintln s!"{iteration}: rewritten equations {chip.constraints.length}"
    IO.eprintln s!"{iteration}: rewrite {(← IO.monoMsNow) - start}ms"
  IO.eprintln s!"Propagation steps: {(← IO.monoMsNow) - start}ms"

end IxVM.PropagationBench
