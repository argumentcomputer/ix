import Tests.FormalChecks.Common

/-!
# `formal-checks controller`

Exercise resident proving and cross-record IxVM proofs on production artifacts.

Uses fixtures from `check-formal.sh`. CPU is the default; `--devices 0,1` runs
the same resident jobs on real CUDA lanes and independently verifies on the
CPU. `--pipeline` additionally runs the expensive complete recursive
aggregation. All logs and reports are preserved in the fixture directory.
-/

namespace Tests.FormalChecks.Controller

open Lean System Tests.FormalChecks

def usage : String :=
  "usage: formal-checks controller [--devices DEVICES] [--pipeline] [--pipeline-ram-gib N] \
    --ixvm-artifact A --recursion-artifact A --aggregate-artifact A fixtures"

/-- The run's fixed context. -/
structure Context where
  out : FilePath
  report : Report
  env : Array (String × Option String)

/-- Run `command`, logged to `NN-name.log`, and record it. Its exit status must
be success unless `succeeds` is false. Returns the log. -/
def run (c : Context) (name : String) (command : Array String)
    (extra : Array (String × Option String) := #[]) (succeeds := true) : IO String := do
  let log := c.out / s!"{pad2 (← c.report.count "commands")}-{name}.log"
  let start ← seconds
  let child ← spawnLogged command (c.env ++ extra) log
  let code ← waitFor child (some 1800) name
  c.report.push "commands" (Json.mkObj [("name", toJson name), ("command", toJson command),
    ("log", toJson (log.fileName.getD "")), ("exit_code", toJson code.toNat),
    ("seconds", floatJson ((← seconds) - start))])
  c.report.save
  if (code == 0) != succeeds then
    fail s!"{name}: unexpected status {code}; see {log}"
  IO.FS.readFile log

/-- Wait for `path` to appear and parse it, failing if the resident host
exits first or after 600 seconds. -/
partial def waitFile (path : FilePath) (child : IO.Process.Child {}) : IO Json := do
  let deadline := (← seconds) + 600
  let rec loop : IO Json := do
    if ← path.pathExists then return ← readJson path
    if let some code ← child.tryWait then
      fail s!"resident exited {code} waiting for {path}"
    if (← seconds) > deadline then fail s!"timed out waiting for {path}"
    IO.sleep 20
    loop
  loop

/-- Run a resident host on `config`, submit `jobs`, and require each to end
with its status in `statuses`; the host must stop cleanly with no reserved
record bytes. -/
def resident (c : Context) (binary : FilePath) (name : String) (config : Json)
    (jobs : Array Json) (statuses : Array Nat) : IO FilePath := do
  let directory := c.out / name
  IO.FS.createDir directory
  let configPath := directory / "config.json"
  IO.FS.writeFile configPath config.compress
  let child ← spawnLogged #[binary.toString, "serve", configPath.toString, directory.toString]
    c.env (directory / "host.log")
  let code ← try
      let _ ← waitFile (directory / "ready.json") child
      for job in jobs do
        let id ← IO.ofExcept (job.getObjValAs? String "id")
        let path := directory / "pending" / (id ++ ".tmp")
        IO.FS.writeFile path job.compress
        IO.FS.rename path (directory / "pending" / (id ++ ".json"))
      for (job, expected) in jobs.zip statuses do
        let id ← IO.ofExcept (job.getObjValAs? String "id")
        let result ← waitFile (directory / "done" / (id ++ ".json")) child
        unless (result.getObjValAs? Nat "status").toOption == some expected do
          fail s!"resident job {id}: {result.compress}, expected status {expected}"
        c.report.push "resident_jobs" ((Json.mkObj [("id", toJson id)]).mergeObj result)
      IO.FS.writeFile (directory / "stop") ""
      waitFor child (some 120) s!"stopping {name}"
    catch e =>
      IO.FS.writeFile (directory / "stop") ""
      let _ ← waitFor child (some 120) s!"stopping {name}"
      throw e
  unless code == 0 do fail s!"{directory}: resident host exited {code}"
  let summary ← readJson (directory / "summary.json")
  unless (← natField summary ["record_reserved_bytes"]) == 0 do
    fail s!"{name}: record bytes still reserved: {summary.compress}"
  c.report.set name summary
  c.report.save
  return directory

def productFiles (path : FilePath) (ixvm : Bool) : FilePath × FilePath :=
  if ixvm then (path, path.toString ++ ".vk") else (path / "proof.bin", path / "key.bin")

def lastLine (text : String) : String :=
  (text.trimAscii.toString.splitOn "\n").getLast?.getD ""

def main (argv : List String) : IO UInt32 := do
  let args ← match Args.parse ["pipeline"] argv with
    | .ok a => pure a
    | .error e => return ← usageError usage e
  let some fixtures := args.positional[0]? | return ← usageError usage "missing fixtures"
  let required := ["ixvm-artifact", "recursion-artifact", "aggregate-artifact"].map args.flag?
  let [some ixvmArtifact, some recursionArtifact, some aggregateArtifact] := required
    | return ← usageError usage "the three artifacts are required"
  let devices : Option (List (Option Nat)) := match args.flag? "devices" with
    | none => some [none, none]
    | some s => (s.splitOn ",").mapM fun d => (d.trimAscii.toString.toNat?).map some
  let some devices := devices | return ← usageError usage "invalid CUDA device indices"
  if devices.isEmpty || devices.any (fun d => d.any (· ≥ 2 ^ 31)) then
    return ← usageError usage "invalid CUDA device indices"
  let pipelineRam := ((args.flag? "pipeline-ram-gib").bind String.toNat?).getD 192
  let fixtures ← IO.FS.realPath (System.FilePath.mk fixtures)
  let out ← freshDir fixtures "controller-check-"
  let cpu ← absolute "target/release"
  let gpu := args.has "devices"
  let binary ← if gpu then absolute "target/formal-cuda/release/ix-prover"
    else pure (cpu / "ix-prover")
  let artifacts ← [ixvmArtifact, recursionArtifact, aggregateArtifact].toArray.mapM
    fun p => IO.FS.realPath (System.FilePath.mk p)
  let mut env : Array (String × Option String) := #[("IX_CUDA", some "0"),
    ("AIUR_TRACE_ONLY_LOOKUPS", some "0"), ("RAYON_NUM_THREADS", some "8"),
    ("IX_AIUR_ARTIFACT", some artifacts[0]!.toString),
    ("IX_AGGR_ARTIFACT", some artifacts[2]!.toString)]
  if devices.eraseDups.length < devices.length && !devices.contains none then
    env := env.push ("IX_PROVER_SHARED_DEVICES", some "1")
  let report ← Report.new out [("success", false), ("devices", toJson devices),
    ("commands", Json.arr #[]), ("resident_jobs", Json.arr #[]),
    ("revision", toJson (← revision)), ("binary_sha256", toJson (← sha256 binary)),
    ("artifact_sha256", toJson (← artifacts.mapM sha256))]
  IO.println s!"Controller validation logs: {out}"
  (← IO.getStdout).flush
  let c : Context := { out, report, env }
  try
    let cases ← IO.ofExcept ((← readJson (fixtures / "claims.json")).getArr?)
    let some claim := cases.findSome? fun entry =>
        if (entry.getObjValAs? Bool "accept").toOption == some true &&
            (entry.getObjValAs? String "label").toOption == some "CheckEnv frontier-asm (Nat.add_comm)"
        then (entry.getObjVal? "invocation").toOption else none
      | fail "claims.json has no accepted CheckEnv frontier-asm (Nat.add_comm) case"
    let invocation := out / "claim.json"
    IO.FS.writeFile invocation claim.compress
    let inputs := #[invocation, fixtures / "inner/input.json", fixtures / "aggregation.json.wrap.json"]
    let mut jobs : Array Json := #[]
    let mut references : Array (ByteArray × ByteArray) := #[]
    for i in [0:3] do
      let artifact := artifacts[i]!
      let source := inputs[i]!
      let ixvm := i == 0
      let host := cpu / (if ixvm then "ixvm-proof" else "stark-verifier")
      let plan := out / s!"plan-{i}"
      let _ ← run c s!"plan-{i}" #[host.toString, "plan", artifact.toString, source.toString,
        plan.toString, "0", "regenerate"]
      let planPath : FilePath := if ixvm then plan.toString ++ ".report.json" else plan / "report.json"
      let rows := (← natField (← readJson planPath) ["plan", "max_rows"]) / 2
      unless rows > 0 do fail s!"plan-{i}: no rows"
      let reference := out / s!"reference-{i}"
      let _ ← run c s!"reference-{i}" #[host.toString, "prove", artifact.toString,
        source.toString, reference.toString, toString rows, "regenerate"]
      let (proof, key) := productFiles reference ixvm
      let proofBytes ← IO.FS.readBinFile proof
      let keyBytes ← IO.FS.readBinFile key
      references := references.push (proofBytes, keyBytes)
      for copy in [0:2] do
        jobs := jobs.push (Json.mkObj [("id", toJson s!"case-{i}-{copy}"),
          ("artifact", toJson artifact.toString), ("input", toJson source.toString),
          ("output", toJson (out / s!"proof-{i}-{copy}").toString), ("priority", toJson (i != 0)),
          ("options", Json.mkObj [("max_rows", toJson rows), ("retention", "regenerate")])])
    let config := Json.mkObj [
      ("artifacts", toJson (artifacts.zipIdx.map fun (p, i) => Json.mkObj [
        ("path", toJson p.toString), ("kind", toJson (if i == 0 then "ixvm" else "recursion"))])),
      ("devices", toJson devices), ("exec_jobs", toJson 2), ("threads_per_prover", toJson 4),
      ("max_ram_bytes", toJson (8 * 2 ^ 30)), ("texray", toJson true)]
    let directory ← resident c binary "resident" config jobs (jobs.map fun _ => 0)
    unless ((← IO.FS.readFile (directory / "host.log")).splitOn "[texray]").length > 1 do
      fail "texray emitted no phases"
    for job in jobs do
      let id ← IO.ofExcept (job.getObjValAs? String "id")
      let i := ((id.splitOn "-")[1]!).toNat!
      let output ← IO.ofExcept (job.getObjValAs? String "output")
      let (proof, key) := productFiles output (i == 0)
      unless (← IO.FS.readBinFile proof) == references[i]!.1 do fail s!"{id}: proof differs"
      unless (← IO.FS.readBinFile key) == references[i]!.2 do fail s!"{id}: key differs"
      let host := cpu / (if i == 0 then "ixvm-proof" else "stark-verifier")
      let _ ← run c (id ++ "-verify") #[host.toString, "verify", artifacts[i]!.toString,
        inputs[i]!.toString, proof.toString] #[("AIUR_TRACE_ONLY_LOOKUPS", some "1")]
    let limitedOutput := out / "limited-proof"
    let limited := (jobs[0]!.setObjVal! "id" "limited").setObjVal! "output" (toJson limitedOutput.toString)
    let _ ← resident c binary "record-limit" (config.setObjVal! "record_limit_bytes" (toJson 1024))
      #[limited] #[75]
    if ← limitedOutput.pathExists then fail "the record-limited job wrote a proof"

    -- A real dependency-bearing IxVM environment, with all worker records
    -- contributing to one public claim rather than independent leaf claims.
    let tiny := fixtures / "claims.json.controller.ixe"
    unless ← tiny.pathExists do
      fail "regenerate formal-aiur-tests fixtures: missing controller environment"
    let ix := (← absolute ".lake/build/bin/ix").toString
    let manifest := out / "two.ixes"
    let _ ← run c "partition" #[ix, "shard", tiny.toString, "--shards", "2", "--out", manifest.toString]
    let mut proofAddresses : Array String := #[]
    for retention in ["retain", "regenerate"] do
      let resultPath := out / s!"distributed-{retention}.json"
      let mut command := #[ix, "prove", "--distributed", "--ixe", tiny.toString, "--ixes",
        manifest.toString, "--exec-jobs", "2", "--max-ram", "8", "--retention", retention,
        "--no-index", "--report", resultPath.toString]
      if gpu then command := command ++ #["--gpu-device", toString (devices[0]!.getD 0)]
      let text ← run c ("distributed-" ++ retention) command
      let address := lastLine text
      proofAddresses := proofAddresses.push address
      let result ← readJson resultPath
      unless (← boolField result ["verified"]) && (← natField result ["cross_record_calls"]) > 0 do
        fail s!"distributed-{retention}: not verified across records"
      unless (((← field result ["workers"]).getArr?).toOption.map (·.size)) == some 2 &&
          (← natField result ["shards"]) ≥ 2 do
        fail s!"distributed-{retention}: expected two workers and at least two shards"
      let _ ← run c ("distributed-verify-" ++ retention) #[ix, "verify", "--distributed", "--ixe",
        tiny.toString, "--ixes", manifest.toString, address] #[("AIUR_TRACE_ONLY_LOOKUPS", some "1")]
    unless proofAddresses[0]! == proofAddresses[1]! do fail "retention changed distributed proof"
    report.set "distributed_proof" (toJson proofAddresses[0]!)
    let _ ← run c "reject-leaf-binding" #[ix, "verify", "--ixe", tiny.toString, "--ixes",
      manifest.toString, proofAddresses[0]!] (succeeds := false)
    let failedManifest := out / "failed.ixes"
    let failedReport := out / "failed-pipeline.json"
    let text ← run c "pipeline-budget-failure" #[ix, "prove", "--aggregate", "--direct-joins",
        "--no-cache", "--no-index", "--ixe", tiny.toString, "--ixes", manifest.toString,
        "--trace-shards", "--jobs", "2", "--exec-jobs", "2", "--max-ram", "8", "--report",
        failedReport.toString, "--out-ixes", failedManifest.toString]
      #[("AIUR_RECORD_MAX_BYTES", some "1024"),
        ("AIUR_LANES_CACHE_DIR", some (out / "failed-checkpoints").toString)] (succeeds := false)
    if (text.splitOn "no such process").length > 1 || (text.splitOn "prover stopped").length > 1 then
      fail "the failed pipeline lost a prover"
    if ← failedManifest.pathExists then fail "failed run published a completed manifest"
    let failedSummary ← readJson (failedReport.toString ++ ".summary.json")
    unless (← natField failedSummary ["record_reserved_bytes"]) == 0 do
      fail "the failed pipeline left record bytes reserved"
    if args.has "pipeline" then
      let mut command := #[ix, "prove", "--aggregate", "--direct-joins", "--ixe", tiny.toString,
        "--ixes", manifest.toString, "--trace-shards", "--shard-rows", "4194304",
        "--max-ram", toString pipelineRam, "--exec-jobs", "2",
        "--report", (out / "pipeline.json").toString, "--out-ixes", (out / "final.ixes").toString]
      if gpu then
        -- CLI --lanes chooses consecutive devices, so reject a hole.
        let first := devices[0]!.getD 0
        unless devices == (List.range devices.length).map (some <| first + ·) do
          fail "--pipeline needs consecutive devices"
        command := command ++ #["--lanes", toString devices.length, "--gpu-device", toString first]
      else
        command := command ++ #["--jobs", "2"]
      let checkpoints := #[("AIUR_LANES_CACHE_DIR", some (out / "checkpoints").toString)]
      let address := lastLine (← run c "pipeline" command checkpoints)
      let _ ← run c "pipeline-verify" #[ix, "verify", "--aggregate", "--ixe", tiny.toString,
        "--ixes", (out / "final.ixes").toString, address]
      unless lastLine (← run c "pipeline-resume" command checkpoints) == address do
        fail "the resumed pipeline proved another root"
      let events ← IO.FS.readFile (out / "pipeline.json.events.jsonl")
      unless events.trimAscii.isEmpty do fail "cached root triggered execution"
      report.set "pipeline_proof" (toJson address)
    report.set "success" true
    IO.println s!"Controller validation passed: {out / "report.json"}"
    report.save
    return 0
  catch e =>
    report.save
    throw e

end Tests.FormalChecks.Controller
