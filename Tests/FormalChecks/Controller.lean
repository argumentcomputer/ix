import Tests.FormalChecks.Common

/-!
# `formal-checks controller`

Exercise the in-process aggregate controller (`ix prove --aggregate`,
`--lanes`) on production artifacts.

Uses the two-claim environment `claims.ixt.controller.ixe` that
`formal-aiur-tests` writes for `check-formal.sh`, partitioned into two leaves:

- a claim whose record exceeds the per-record ceiling and cannot be split
  stops the run, and no manifest is published;
- the structural fold (`--structural-above 0`) proves on CPU lanes, reaches
  the composed verdict, verifies independently with `ix verify --aggregate`,
  is refused as a claim proof, and a rerun resumes from the cache without
  executing a claim;
- the claims alone (`ix prove --ixe --ixes`) print one `shard address` line
  per claim, and `ix verify` accepts them against the partition proven.

`--pipeline` additionally runs the complete recursive aggregation, on CUDA
lanes with `--devices` (which needs a CUDA build of `ix`); `--devices` affects
nothing else. All logs and the report are preserved in the fixture directory.
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

def mentions (text needle : String) : Bool :=
  (text.splitOn needle).length > 1

def logLines (text : String) : List String :=
  (text.splitOn "\n").map (·.trimAscii.toString)

/-- A store address as the CLI prints it: 64 lowercase hex digits. -/
def isAddress (s : String) : Bool :=
  s.length == 64 && s.all fun ch => ch.isDigit || ('a' ≤ ch && ch ≤ 'f')

/-- The root address an aggregating `ix prove` prints last on stdout. -/
def rootOf (name text : String) : IO String := do
  let some root := (logLines text).reverse.find? isAddress
    | fail s!"{name}: printed no root address"
  return root

/-- The `shard address` lines a claims-only `ix prove` prints. -/
def claimLines (text : String) : Array (Nat × String) :=
  (logLines text).toArray.filterMap fun line =>
    match line.splitOn " " with
    | [id, address] => (id.toNat?).bind fun id => if isAddress address then some (id, address) else none
    | _ => none

/-- Whether the controller's `[lanes]` log shows a claim being executed. -/
def executedClaim (text : String) : Bool :=
  (logLines text).any fun line => mentions line "claim" && mentions line "execution started"

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
  let gpu := args.has "devices"
  let pipeline := args.has "pipeline"
  -- `ix prove --lanes N --gpu-device D` proves on devices D … D+N-1, or with
  -- IX_PROVER_SHARED_DEVICES=1 runs every lane on D.
  let first := (devices.head?.bind id).getD 0
  let shared := gpu && devices.length > 1 && devices.all (· == some first)
  if pipeline && gpu && !shared &&
      devices != (List.range devices.length).map (some <| first + ·) then
    return ← usageError usage "--pipeline needs consecutive or repeated CUDA devices"
  let pipelineRam := ((args.flag? "pipeline-ram-gib").bind String.toNat?).getD 192
  let fixtures ← IO.FS.realPath (System.FilePath.mk fixtures)
  let out ← freshDir fixtures "controller-check-"
  let ixBinary ← absolute ".lake/build/bin/ix"
  let artifacts ← [ixvmArtifact, recursionArtifact, aggregateArtifact].toArray.mapM
    fun p => IO.FS.realPath (System.FilePath.mk p)
  let mut env : Array (String × Option String) := #[("IX_CUDA", some "0"),
    ("AIUR_TRACE_ONLY_LOOKUPS", some "0"),
    ("IX_AIUR_ARTIFACT", some artifacts[0]!.toString),
    ("IX_AGGR_ARTIFACT", some artifacts[2]!.toString)]
  if shared then env := env.push ("IX_PROVER_SHARED_DEVICES", some "1")
  let report ← Report.new out [("success", false), ("devices", toJson devices),
    ("commands", Json.arr #[]), ("revision", toJson (← revision)),
    ("binary_sha256", toJson (← sha256 ixBinary)),
    ("artifact_sha256", toJson (← artifacts.mapM sha256))]
  IO.println s!"Controller validation logs: {out}"
  (← IO.getStdout).flush
  let c : Context := { out, report, env }
  try
    -- A real dependency-bearing IxVM environment, split into two leaves.
    let tinyPath := fixtures / "claims.ixt.controller.ixe"
    unless ← tinyPath.pathExists do
      fail "regenerate formal-aiur-tests fixtures: missing controller environment"
    let tiny := tinyPath.toString
    let ix := ixBinary.toString
    let manifest := (out / "two.ixes").toString
    let _ ← run c "partition" #[ix, "shard", tiny, "--shards", "2", "--out", manifest]

    -- Under a 1 KiB record ceiling every claim is bisected down to one
    -- atomic block that still does not fit, which must stop the run.
    let failedManifest := out / "failed.ixes"
    let text ← run c "ceiling-failure" #[ix, "prove", "--aggregate", "--no-cache", "--no-index",
        "--ixe", tiny, "--ixes", manifest, "--trace-shards", "--jobs", "2", "--exec-jobs", "2",
        "--max-ram", "16", "--out-ixes", failedManifest.toString]
      #[("AIUR_RECORD_MAX_BYTES", some "1024"),
        ("AIUR_HOST_WORKSPACE_BYTES", some (toString (4 * 2 ^ 30))),
        ("AIUR_LANES_CACHE_DIR", some (out / "failed-cache").toString)] (succeeds := false)
    unless mentions text "cannot be split further" do
      fail "an unsplittable claim over the record ceiling did not stop the run"
    if ← failedManifest.pathExists then fail "the failed run published a completed manifest"

    -- Every join structural: proves, passes the composed verdict, verifies
    -- independently, and resumes from the aggregate cache.
    let structuralManifest := (out / "structural.ixes").toString
    let structural := #[ix, "prove", "--aggregate", "--structural-above", "0", "--ixe", tiny,
      "--ixes", manifest, "--trace-shards", "--jobs", "2", "--exec-jobs", "2", "--max-ram", "64",
      "--out-ixes", structuralManifest]
    let cpuEnv := #[("AIUR_HOST_WORKSPACE_BYTES", some (toString (16 * 2 ^ 30))),
      ("AIUR_LANES_CACHE_DIR", some (out / "cache").toString)]
    let text ← run c "structural" structural cpuEnv
    let root ← rootOf "structural" text
    unless mentions text "composed verdict OK" do fail "the controller skipped the composed verdict"
    let _ ← run c "structural-verify" #[ix, "verify", "--aggregate", "--structural-above", "0",
      "--ixe", tiny, "--ixes", structuralManifest, root]
    let _ ← run c "reject-root-as-claim" #[ix, "verify", "--ixe", tiny, "--ixes",
      structuralManifest, root] (succeeds := false)
    let text ← run c "structural-resume" structural cpuEnv
    unless (← rootOf "structural-resume" text) == root do
      fail "the resumed run proved another root"
    if executedClaim text then fail "the resumed run executed a claim again"
    unless mentions text "cache hit" do fail "the resumed run ignored the aggregate cache"
    report.set "structural_root" (toJson root)

    -- The claims alone: one line per claim, each a verified proof.
    let claimsManifest := (out / "claims.ixes").toString
    let text ← run c "claims-only" #[ix, "prove", "--ixe", tiny, "--ixes", manifest, "--jobs", "2",
      "--exec-jobs", "2", "--max-ram", "64", "--no-index", "--out-ixes", claimsManifest] cpuEnv
    let claims := claimLines text
    unless claims.size == 2 do
      fail s!"claims-only: expected two `shard address` lines, found {claims.size}"
    let _ ← run c "claims-verify" (#[ix, "verify", "--ixe", tiny, "--ixes", claimsManifest]
      ++ claims.map (·.2))
    report.set "claim_proofs" (toJson (claims.map (·.2)))

    if pipeline then
      let finalManifest := (out / "final.ixes").toString
      let mut command := #[ix, "prove", "--aggregate", "--ixe", tiny, "--ixes", manifest,
        "--trace-shards", "--shard-rows", "4194304", "--max-ram", toString pipelineRam,
        "--exec-jobs", "2", "--out-ixes", finalManifest]
      if gpu then
        command := command ++ #["--lanes", toString devices.length, "--gpu-device", toString first]
      else
        command := command ++ #["--jobs", "2"]
      let cache := #[("AIUR_LANES_CACHE_DIR", some (out / "pipeline-cache").toString)]
      let address ← rootOf "pipeline" (← run c "pipeline" command cache)
      let _ ← run c "pipeline-verify" #[ix, "verify", "--aggregate", "--ixe", tiny,
        "--ixes", finalManifest, address]
      let text ← run c "pipeline-resume" command cache
      unless (← rootOf "pipeline-resume" text) == address do
        fail "the resumed pipeline proved another root"
      if executedClaim text then fail "the resumed pipeline executed a claim"
      report.set "pipeline_proof" (toJson address)
    report.set "success" true
    IO.println s!"Controller validation passed: {out / "report.json"}"
    report.save
    return 0
  catch e =>
    report.save
    throw e

end Tests.FormalChecks.Controller
