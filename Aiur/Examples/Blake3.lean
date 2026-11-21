import AiurTests.Blake3
import AiurTests.U8
import Mathlib.Algebra.Field.Rat

/-! Circuit statistics for the same Blake3, word, and byte modules used by IxVM. -/
namespace Blake3Example
open Aiur

set_option maxRecDepth 100000
set_option maxHeartbeats 80000000

def source : Modules.Program Nat := Library.Blake3.source.append AiurBlake3Tests.benchmark

private def get {α : Type} : Except String α → IO α := IO.ofExcept
private def ensure (message : String) (condition : Bool) : Except String Unit :=
  if condition then .ok () else .error message

structure Totals where
  chips : Nat
  columns : Nat
  degree : Nat
  calls : Nat
  rom : Nat
  lookupDegree : Nat
  deriving Repr, BEq

def totals (system : Circuit.System F) : Totals :=
  system.stats.foldl (fun acc s => {
    chips := acc.chips + 1
    columns := acc.columns + s.columns
    degree := max acc.degree s.maxConstraintDegree
    calls := acc.calls + s.callLookups
    rom := acc.rom + s.romLookups
    lookupDegree := max acc.lookupDegree s.maxLookupDegree
  }) ⟨0, 0, 0, 0, 0, 0⟩

def report : IO Unit := do
  AiurU8Tests.run
  IO.println "Preparing the Blake3 example and generated U8 tables..."
  let prepared ← get <| Modules.prepare (source.toField Rat) ["Benchmark::main"]
  -- Both compilers use this exact same specialization and inline configuration.
  let specialized ← get <| Generic.specialize prepared.environment.source prepared.entries
  IO.println "Compiling the reference circuit..."
  let reference ← get specialized.compile
  IO.println "Compiling the optimized circuit (degree cap 3)..."
  let optimized ← get specialized.compileOptimized
  get <| ensure "compilers received different programs" (reference.program == optimized.inlined.program)
  get <| ensure "precommitted data changed" (reference.system.tables == optimized.system.tables &&
    reference.system.maps == optimized.system.maps)
  -- Every original chip remains explainable, including under deduplication.
  for chip in reference.system.chips do
    let representative := ((optimized.artifact.representatives.find? (·.1 == chip.name)).map Prod.snd).getD chip.name
    let some other := optimized.system.findChip? representative |
      throw (IO.userError s!"missing optimized chip for {chip.name}")
    get <| ensure s!"lookup merging added slots in {chip.name}"
      (other.sends.length ≤ chip.sends.length && other.memory.length ≤ chip.memory.length)
  IO.println "\nReference chips:"
  reference.system.printStats
  IO.println "\nOptimized chips:"
  optimized.system.printStats
  IO.println "\nTotals (sum of static chip widths and lookup slots, not execution cost):"
  let before := totals reference.system
  let after := totals optimized.system
  IO.println "| Metric | Reference | Optimized |"
  IO.println "| --- | ---: | ---: |"
  for (label, a, b) in [
      ("Chips", before.chips, after.chips),
      ("Sum of chip columns", before.columns, after.columns),
      ("Maximum constraint degree", before.degree, after.degree),
      ("Call/map lookup slots", before.calls, after.calls),
      ("ROM lookup slots", before.rom, after.rom),
      ("Maximum lookup expression degree", before.lookupDegree, after.lookupDegree)] do
    IO.println s!"| {label} | {a} | {b} |"
  IO.println "\nShared precommitted tables (separate from chip columns):"
  let mut tableRows := 0
  let mut tableCells := 0
  for table in optimized.system.tables do
    let layout ← get <| (optimized.system.enums.layout table.rowType).mapError reprStr
    IO.println s!"{table.name}: rows={table.rows.length}, width={layout.width}"
    tableRows := tableRows + table.rows.length
    tableCells := tableCells + table.rows.length * layout.width
  IO.println s!"Shared table totals: {tableRows} rows, {tableCells} field cells"
  IO.println s!"Static maps: {optimized.system.maps.length}"
  let merged := optimized.artifact.representatives.filter (fun (name, representative) => name != representative)
  IO.println s!"Merged internal chips: {repr merged}"
  IO.println "\nEntrypoint: Benchmark::main generates 1,025 bytes, then hashes them."
  IO.println "This report compiles the program; it does not execute Blake3 or construct witnesses."
  IO.println "Entrypoint soundness/completeness, degree bounds, and deduplication are proved; memoized soundness assumes acyclicity."

end Blake3Example

def main : IO Unit := Blake3Example.report
