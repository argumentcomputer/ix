import Comparisons.Environment
import Compilatrix.Tools.IxIR2Check

/-! Compiler-scaling orchestration has no compiler/selector/evaluator imports.
It checks process records, canonical snapshot bytes, cache reuse inventories,
and an independently linked C oracle. -/
namespace Benchmark.CompilerScaling
open Lean System Compilatrix.Tools.Check Compilatrix.Tools.UniqueCheck

structure Case where
  family : String
  size : Nat
  edited : Bool := false
  deriving BEq, Inhabited, ToJson, FromJson

def Case.id (case : Case) : String :=
  s!"{case.family}-{case.size}{if case.edited then "-edited" else ""}"

def cases (profile : String) : Array Case :=
  let groups : List (String × List Nat) := if profile == "smoke" then [
    ("declarations", [1, 4, 352, 353]), ("call-depth", [1, 4, 32, 33, 318, 319]),
    ("branches", [1, 4, 31, 32, 453, 454]), ("allocations", [1, 4, 8, 9]),
    ("candidates", [511, 512, 513]), ("joins", [1, 4, 9, 10])]
  else [
    ("declarations", [1, 2, 4, 8, 16, 32, 64, 128, 256, 352, 353, 512]),
    ("call-depth", [1, 2, 4, 8, 16, 32, 33, 64, 128, 256, 318, 319, 512]),
    ("branches", [1, 2, 4, 8, 16, 31, 32, 64, 128, 256, 453, 454, 512]),
    ("allocations", [1, 2, 4, 8, 9, 16, 32, 64, 128]),
    ("candidates", [511, 512, 513]), ("joins", [1, 2, 4, 6, 8, 9, 10, 11, 12, 32, 43])]
  let base := groups.flatMap fun (family, sizes) => sizes.map fun size => ({ family, size } : Case)
  let edits := (if profile == "smoke" then [4] else [1, 4, 16, 32, 128, 318]).map fun size =>
    ({ family := "call-depth", size, edited := true } : Case)
  (base ++ edits).toArray

def workerEnv : Array (String × Option String) :=
  #[("LEAN_NUM_THREADS", some "1"), ("MALLOC_ARENA_MAX", some "1"), ("LC_ALL", some "C")]

def environment (core : Nat) : IO Json := do
  replaceAt (← Benchmark.environment core) ["runtime_overrides"] (toJson workerEnv)

def artifactInventory (directory : FilePath) : IO Json := do
  let entries ← array (← recordFiles directory)
  return Json.arr (← entries.filterM fun entry => do
    let name ← strField entry "path"
    return name != "measurements.json" && name != "stages.jsonl" && name != "current-stage.json")

def stageIdentities (metrics : Json) : IO Json := do
  let rows ← arrField metrics "stages"
  need (!rows.isEmpty) "missing compiler stage measurements"
  let names ← rows.mapM (fun row => strField row "stage")
  need names.toList.Nodup "duplicate compiler stage measurement"
  return Json.arr (← rows.mapM fun row => do
    let elapsed ← number row "elapsed_ns"
    need (elapsed > 0) "zero compiler stage duration"
    let before ← field row "memory_before"
    let after ← field row "memory_after"
    for memory in [before, after] do
      let rss ← number memory "rss_kib"
      let peak ← number memory "process_peak_rss_kib"
      need (rss > 0 && rss ≤ peak && peak ≤ 2 * 1024 * 1024) "invalid compiler process memory observation"
    -- Preserve raw /proc observations. The measurement host can report a
    -- slightly lower VmHWM later; GNU time records the final process peak.
    return Json.mkObj [("stage", ← field row "stage"), ("status", ← field row "status"), ("reason", ← field row "reason")])

def artifactCheck (directory : FilePath) (reference : Json) : IO Unit := do
  need ((← artifactInventory directory) == (← field reference "artifacts")) "compiler artifact inventory or bytes changed"
  let outcome ← readJson (directory / "outcome.json")
  need (outcome == (← field reference "outcome")) "compiler outcome changed"
  let metrics ← readJson (directory / "measurements.json")
  need ((← strField metrics "format") == "compilatrix/compiler-scaling-measurements/1" &&
    (← stageIdentities metrics) == (← field reference "stages")) "compiler stage inventory or rejection changed"
  need ((← readLines (directory / "stages.jsonl")) == (← arrField metrics "stages")) "compiler stage journal disagrees"
  if ← (directory / "ixir2.bin").pathExists then
    let bytes ← IO.FS.readBinFile (directory / "ixir2.bin")
    let decoded ← checked (Compilatrix.Tools.IxIR2Check.decode bytes)
    need (decoded == (← readJson (directory / "ixir2.json")) &&
      Compilatrix.Tools.IxIR2Check.root bytes == (← strField outcome "snapshot_root")) "independent snapshot decode disagrees"

def reference (directory : FilePath) : IO Json := do
  let result := Json.mkObj [
    ("outcome", ← readJson (directory / "outcome.json")), ("artifacts", ← artifactInventory directory),
    ("stages", ← stageIdentities (← readJson (directory / "measurements.json")))]
  artifactCheck directory result
  return result

def semanticOutcome (outcome : Json) : IO Json := do
  return Json.mkObj ((← pairs outcome).filter fun (key, _) => key != "hpt_cache" && key != "input_cache_bytes")

def cachePair (cold warm : Json) (old : Option Json := none) : IO Json := do
  let payload := fun reference => do
    let files ← arrField reference "artifacts"
    files.filterM fun file => return (← strField file "path") != "outcome.json"
  need ((← payload cold) == (← payload warm)) "cache state changed serialized artifact bytes"
  let cold ← field cold "outcome"
  let warm ← field warm "outcome"
  need ((← semanticOutcome cold) == (← semanticOutcome warm)) "cache state changed compiler artifacts or rejection"
  let keys ← arrField cold "hpt_cache_keys"
  let prior ← arrField (old.getD cold) "hpt_cache_keys"
  let hits := (keys.filter prior.contains).size
  let stats ← field warm "hpt_cache"
  let coldStats ← field cold "hpt_cache"
  need ((← number coldStats "hits") == 0 && (← number coldStats "misses") == keys.size &&
    (← number cold "input_cache_bytes") == 0) "cold compilation started with cached evidence"
  need ((← number stats "hits") == hits && (← number stats "misses") == keys.size - hits &&
    (← number stats "writes") == keys.size - hits && (← number stats "rejected") == 0 &&
    (← number stats "ingressEntries") == prior.size) "cache hits/writes do not match the exact reused key set"
  if old.isNone then
    need ((← number stats "rounds") == 0 && (← number stats "writeBytes") == 0) "unchanged warm cache rebuilt evidence"
  else
    need (hits > 0 && hits < keys.size && (← field cold "source_root") != (← field old.get! "source_root"))
      "dependency edit failed to preserve and invalidate distinct evidence"
  return Json.mkObj [("hits", toJson hits), ("misses", toJson (keys.size - hits)),
    ("unchanged_keys", toJson (keys.filter prior.contains)), ("new_keys", toJson (keys.filter (!prior.contains ·))),
    ("removed_keys", toJson (prior.filter (!keys.contains ·)))]

def launchArgs (worker : FilePath) (args : Array String) (core : Nat) : Array String :=
  #["--cpu-list", toString core, "prlimit", "--as=4294967296", "--cpu=120:125", "--core=0",
    "--", "timeout", "--signal=TERM", "--kill-after=5s", "180s", worker.toString] ++ args

def runWorker (worker : FilePath) (logs : FilePath) (name : String) (args : Array String)
    (core : Nat) (timer : String) : IO Unit := do
  let _ ← logged logs name "taskset" (launchArgs worker args core) workerEnv none timer
  pure ()

def inspectBuild (build : FilePath) : IO Json := do
  let metadata ← readJson (build / "build.json")
  need ((← strField metadata "format") == "compilatrix/compiler-scaling-build/1") "wrong compiler scaling build format"
  let profile ← strField metadata "profile"
  need (["smoke", "full"].contains profile && (← field metadata "cases") == toJson (cases profile)) "compiler workload matrix changed"
  for (directory, key) in [("inputs", "inputs"), ("tools", "tools"), ("harness", "harness")] do
    inspectFiles (build / directory) (← field metadata key)
  need (digest (← IO.FS.readBinFile (build / "protocol.md")) == (← strField metadata "protocol_blake3") &&
    digest (← IO.FS.readBinFile (build / "tool-identities.json")) == (← strField metadata "tool_identities_blake3")) "compiler protocol or tools changed"
  let rows ← arrField metadata "rows"
  let ids ← rows.mapM (fun row => strField row "id")
  need ids.toList.Nodup "duplicate compiler workload row"
  for row in rows do
    artifactCheck (build / "artifacts" / (← strField row "id")) (← field row "reference")
  let mut expectedIds := #[]
  let mut expectedPairs := #[]
  for case in cases profile do
    let coldMode := if case.edited then "edit-cold" else "cold"
    let coldId := s!"{case.id}-{coldMode}"
    let cold ← present (← rows.findM? fun row => return (← strField row "id") == coldId) "missing compiler cold row"
    let input := s!"inputs/{case.id}.json"
    need ((← field cold "case") == toJson case && (← strField cold "mode") == coldMode &&
      (← strField cold "input") == input && (← field cold "cache") == Json.null &&
      (← IO.FS.readBinFile (build / input)) == (← IO.FS.readBinFile (build / "artifacts" / coldId / "input.json")))
      "compiler cold row identity changed"
    expectedIds := expectedIds.push coldId
    if ← (build / "artifacts" / coldId / "hpt.store").pathExists then
      let baseId := s!"{case.family}-{case.size}-cold"
      let cacheId := if case.edited then baseId else coldId
      let warmMode := if case.edited then "edit-warm" else "warm"
      let warmId := s!"{case.id}-{warmMode}"
      let warm ← present (← rows.findM? fun row => return (← strField row "id") == warmId) "missing compiler warm row"
      need ((← field warm "case") == toJson case && (← strField warm "mode") == warmMode &&
        (← strField warm "input") == input && (← field warm "cache") == toJson s!"artifacts/{cacheId}/hpt.store")
        "compiler warm row identity changed"
      let prior ← if case.edited then do
          let base ← present (← rows.findM? fun row => return (← strField row "id") == baseId) "missing dependency edit baseline"
          pure (some (← field (← field base "reference") "outcome"))
        else pure none
      let reuse ← cachePair (← field cold "reference") (← field warm "reference") prior
      expectedPairs := expectedPairs.push (Json.mkObj [("cold", toJson coldId), ("warm", toJson warmId), ("reuse", reuse)])
      expectedIds := expectedIds.push warmId
  need (ids == expectedIds && (← field metadata "cache_pairs") == Json.arr expectedPairs)
    "compiler workload/cache matrix is incomplete or changed"
  return metadata

end Benchmark.CompilerScaling
