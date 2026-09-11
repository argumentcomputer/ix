import Benchmarks.Compiler.Data

/-! The benchmark oracle imports diagnostic IO and hashing, not the source
compiler, target selector, emitter, or any comparison implementation. -/
namespace Benchmarks.Compiler
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def implementations : Array String := #["compilatrix", "lean", "cakeml", "compcert", "gcc", "clang"]
def isArena (implementation : String) : Bool := !["lean", "cakeml"].contains implementation

def readLines (path : FilePath) : IO (Array Json) := do
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (!·.isEmpty)
  lines.toArray.mapM fun line => checked (Json.parse line)

def kind (row : Json) : IO String := strField row "kind"

def inspectHeap (heap : Json) (input : Input) (capacity : Nat) (released : Bool) : IO Unit := do
  let n := input.length
  let header ← (← arrField heap "header").mapM nat
  need (header == #[32 * (n + 2), 32 * capacity, n + 2, if released then n + 2 else 1,
      n, if released then 0 else n + 1, n + 2, 0, 2 * n, 0]) "benchmark heap counters disagree"
  let cells ← arrField heap "cells"
  need (cells.size == n + 2) "benchmark allocated cell inventory disagrees"
  for index in [:cells.size] do
    let actual ← array cells[index]!
    let expected := if released || index == 0 then
        #[toJson (3 : Nat), toJson (0 : Nat), Json.null, toJson (0 : Nat)]
      else if index == n + 1 then
        #[toJson (0 : Nat), toJson (0 : Nat), Json.null, toJson (0 : Nat)]
      else #[toJson (1 : Nat), toJson input.values[n - index]!.toNat, toJson (index + 1), toJson (0 : Nat)]
    need (actual == expected) "benchmark cell value, ownership, or reclamation disagrees"

def inspectCase (implementation : String) (input : Input) (capacity : Nat) (row : Json) : IO Unit := do
  need ((← kind row) == "case" && (← number row "id") == input.id) "benchmark case identity disagrees"
  need ((← field row "values") == toJson (input.values.reverse.map UInt64.toNat)) "benchmark reversed values disagree"
  need ((← number row "digest") == input.expectedDigest.toNat) "benchmark case digest disagrees"
  if isArena implementation then
    need ((← number row "capacity") == capacity) "benchmark capacity disagrees"
    inspectHeap (← field row "returned") input capacity false
    inspectHeap (← field row "reclaimed") input capacity true
    for flag in ["abi_preserved", "canaries_preserved", "unused_capacity_preserved"] do
      need ((← field row flag) == toJson true) s!"benchmark {flag} failed"
  else
    need ((← field row "capacity") == Json.null) "language runtime declared an arena capacity"
    if implementation == "lean" then
      for key in ["exclusive_input_cons", "exclusive_output_cons", "reused_cons"] do
        need ((← number row key) == input.length) s!"Lean {key} disagrees"
      need ((← field row "released") == toJson true) "Lean result was not released"
    else need ((← field row "roots_dropped") == toJson true) "CakeML result root retained"

def inspectMetadata (implementation : String) (row : Json) : IO Unit := do
  need ((← kind row) == "metadata" && (← strField row "format") == "compilatrix/benchmark-native/1" &&
    (← strField row "implementation") == implementation && (← strField row "timer") == "CLOCK_MONOTONIC_RAW")
    "benchmark metadata disagrees"
  for key in ["resolution_ns", "timer_pair_min_ns", "initial_rss_kb"] do
    need ((← number row key) > 0) s!"benchmark invalid metadata: {key}"
  let mean ← checked (fromJson? (← field row "timer_pair_mean_ns") : Except String Float)
  need (mean > 0 && mean < 1000000) "benchmark timer overhead invalid"

def inspectControl (row : Json) : IO Unit := do
  need ((← kind row) == "control" && (← number row "operations") == 4194304 &&
    (← number row "elapsed_ns") > 0 && (← number row "sink") == 0) "benchmark driver control invalid"
  need (["opaque-empty-handoff", "empty-reverse-handoff"].contains (← strField row "name")) "unknown driver control"

def inspectMatrix (implementation : String) (rows : Array Json) : IO Json := do
  need (implementations.contains implementation && rows.size >= 3) "benchmark implementation or matrix missing"
  inspectMetadata implementation rows[0]!
  inspectControl rows[1]!
  let mut index := 2
  for input in inputs do
    let capacities := if isArena implementation then 65 - input.length else 1
    for extra in [:capacities] do
      need (index < rows.size) "benchmark missing correctness row"
      inspectCase implementation input (input.length + 2 + extra) rows[index]!
      index := index + 1
  need (index + 1 == rows.size && (← kind rows[index]!) == "verified" &&
    (← number rows[index]! "cases") == index - 2) "benchmark correctness inventory disagrees"
  return Json.mkObj [("implementation", toJson implementation), ("cases", toJson (index - 2)),
    ("full_values", toJson true), ("matrix_blake3", toJson (digest (Json.arr (rows.extract 2 index)).compress.toUTF8))]

def sampleSink (row : TimingCase) (operations : Nat) : UInt64 := Id.run do
  let ids := row.inputIds
  let cycle := ids.foldl (fun total id => total + inputs[id]!.expectedDigest) 0
  let rest := (ids.extract 0 (operations % ids.size)).foldl (fun total id => total + inputs[id]!.expectedDigest) 0
  return cycle * (operations / ids.size).toUInt64 + rest

def inspectSample (implementation : String) (mode rowId sample operations : Nat) (row : Json) : IO Unit := do
  need (rowId < timingCases.size) "benchmark row outside inventory"
  need ((← kind row) == "sample" && (← strField row "implementation") == implementation &&
    (← number row "mode") == mode && (← number row "row") == rowId &&
    (← number row "sample") == sample && (← number row "operations") == operations &&
    operations > 0 && operations % (chunkSize * 6) == 0) "benchmark sample identity disagrees"
  need ((← number row "sink") == (sampleSink timingCases[rowId]! operations).toNat) "benchmark timed sink disagrees"
  let elapsed ← number row "elapsed_ns"
  let minimum ← number row "minimum_chunk_ns"
  let chunks := operations / chunkSize
  need ((← number row "chunks") == chunks && (← number row "timer_calls") == 2 * chunks &&
    minimum > 0 && elapsed >= minimum * chunks) "benchmark timer/chunk counts disagree"
  for key in ["envelope_cpu_ns", "minor_faults", "major_faults", "voluntary_switches", "involuntary_switches"] do
    let _ ← number row key
  need ((← number row "envelope_ns") >= elapsed && (← number row "rss_kb") > 0 &&
    (← number row "peak_rss_kb") > 0) "benchmark envelope or process memory invalid"

def checkerRegressions (implementation : String) (rows : Array Json) : IO Unit := do
  let row := rows[11]!
  let id ← number row "id"
  let input := inputs[id]!
  let capacity ← if isArena implementation then number row "capacity" else pure (input.length + 2)
  for (name, path, replacement, fragment) in [
      ("case id", ["id"], toJson (585 : Nat), "case identity"),
      ("case values", ["values"], toJson [123456789], "reversed values"),
      ("case digest", ["digest"], toJson (0 : Nat), "case digest")] do
    rejects name fragment (inspectCase implementation input capacity (← replaceAt row path replacement))
  if isArena implementation then
    for key in ["abi_preserved", "canaries_preserved", "unused_capacity_preserved"] do
      rejects key key (inspectCase implementation input capacity (← replaceAt row [key] (toJson false)))
    rejects "heap counters" "heap counters" (inspectCase implementation input capacity
      (← replaceAt row ["reclaimed", "header"] (toJson ([] : List Nat))))
  rejects "missing correctness row" "missing correctness row" (inspectMatrix implementation (rows.extract 0 8) *> pure ())

end Benchmarks.Compiler
