import Tests.FormalChecks.Controller

/-! Resident manifest checking: concurrency must preserve verdicts, circuit
statistics and the destination budget. Exercise resource failures and split
accounting through the real CLI, as well as the host's no-proof modes. -/

namespace Tests.FormalChecks.Checking
open Lean System Tests.FormalChecks Tests.FormalChecks.Controller

def main (args : List String) : IO UInt32 := do
  let args ← IO.ofExcept (Args.parse [] args)
  let some artifact := args.flag? "ixvm-artifact"
    | return ← usageError "formal-checks checking --ixvm-artifact A fixtures" "missing artifact"
  let some fixtures := args.positional[0]?
    | return ← usageError "formal-checks checking --ixvm-artifact A fixtures" "missing fixtures"
  let artifact ← IO.FS.realPath artifact
  let fixtures ← IO.FS.realPath (FilePath.mk fixtures)
  let out ← freshDir fixtures "checking-"
  let binary ← absolute "target/release/ix-prover"
  let ix ← absolute ".lake/build/bin/ix"
  let report ← Report.new out [("success", false), ("commands", Json.arr #[]),
    ("resident_jobs", Json.arr #[])]
  let c : Context := { out, report, env := #[
    ("IX_AIUR_ARTIFACT", some artifact.toString), ("IX_PROVER_HOST", some binary.toString),
    ("IX_CUDA", some "0"), ("IX_AIUR_CIRCUIT_VERDICT", some "1")] }
  IO.println s!"Checking validation logs: {out}"
  try
    let env := fixtures / "claims.ixt.controller.ixe"
    let manifest := out / "two.ixes"
    let _ ← run c "partition" #[ix.toString, "shard", env.toString, "--shards", "2", "--out", manifest.toString]
    let resources ← IO.Process.output {
      cmd := (← absolute "target/release/ixvm-proof").toString, args := #["resources"] }
    unless resources.exitCode == 0 do fail resources.stderr
    let cores ← natField (← IO.ofExcept (Json.parse resources.stdout)) ["cores"]
    let mut reference : Option (Array Json) := none
    for jobs in [1, 2, 0] do
      let path := out / s!"jobs-{jobs}.json"
      let row := out / s!"jobs-{jobs}.bench.json"
      let args := #[ix.toString, "check", "--ixe", env.toString,
        "--ixes", manifest.toString, "--ram-budget", "8", "--exec-ram", "2",
        "--report", path.toString, "--json", row.toString, "--keep-going"]
      let _ ← run c s!"jobs-{jobs}" (args ++ if jobs == 0 then #[] else #["--jobs", toString jobs])
      let result ← readJson path
      let expectedJobs := if jobs == 0 then max 1 (min cores 2) else jobs
      unless (← natField result ["failures"]) == 0 && (← natField result ["jobs"]) == expectedJobs do
        fail s!"jobs-{jobs}: failed or ignored concurrency"
      let leaves ← IO.ofExcept ((← field result ["leaves"]).getArr?)
      let measurements ← leaves.flatMapM fun leaf => do
        let parts ← IO.ofExcept ((← field leaf ["parts"]).getArr?)
        parts.mapM fun part => do
          unless (← natField part ["report", "plan", "budget_bytes"]) == 8 * 2^30 do
            fail "concurrency divided the per-leaf budget"
          field part ["report", "execution_statistics"]
      if let some previous := reference then
        unless measurements == previous do fail "concurrency changed circuit statistics"
      reference := some measurements
      let summary ← readJson (path.toString ++ ".summary.json")
      unless (← natField summary ["record_reserved_bytes"]) == 0 do fail "leaked record reservation"
      let ready ← readJson (path.toString ++ ".ready.json")
      unless (← natField ready ["record_budget_bytes"]) < 2 * 2^30 do
        fail "execution ignored its separate memory budget"
      unless (← natField ready ["workspace_bytes"]) == 0 do
        fail "checking reserved a proving workspace"
      let row ← field (← readJson row) ["env"]
      let initial ← IO.ofExcept (row.getObjValAs? Float "check-time")
      let total ← IO.ofExcept (row.getObjValAs? Float "check-total-time")
      unless total ≥ initial do fail "total time excludes initial batch"

    -- Exhaust a record reservation, split to atomic blocks, and preserve a
    -- rejected benchmark row instead of reporting partial success.
    let failed := out / "limited.json"
    let refined := out / "limited.ixes"
    let _ ← run c "record-limited" #[ix.toString, "check", "--ixe", env.toString,
      "--ixes", manifest.toString, "--jobs", "2", "--ram-budget", "8", "--exec-ram", "2", "--keep-going",
      "--report", failed.toString, "--out-ixes", refined.toString,
      "--json", (out / "limited.bench.json").toString]
      #[("AIUR_RECORD_MAX_BYTES", some "1024")] false
    if ← refined.pathExists then fail "failed check wrote a refined manifest"
    let result ← readJson failed
    unless (← natField result ["failures"]) > 0 do fail "record failure was hidden"
    unless (← natField result ["split_waves"]) > 0 do fail "record failure did not exercise splitting"
    let initial ← IO.ofExcept (result.getObjValAs? Float "check_seconds")
    let total ← IO.ofExcept (result.getObjValAs? Float "total_seconds")
    unless total > initial do fail "split work was not included in total time"
    let status ← field (← readJson (out / "limited.bench.json")) ["env", "status"]
    unless status == toJson "rejected" do fail "record failure did not reject benchmark row"

    let input := out / "claim.ixi"
    IO.FS.writeBinFile input (← caseInvocation (fixtures / "claims.ixt") "CheckEnv frontier-asm (Nat.add_comm)")
    let entry := Json.mkObj [("path", toJson artifact.toString), ("kind", "ixvm"),
      ("digest", toJson (← artifactDigest artifact))]
    let config := Json.mkObj [("artifacts", toJson #[entry]), ("devices", toJson #[Json.null]),
      ("exec_jobs", toJson 2), ("threads_per_prover", toJson 1), ("max_ram_bytes", toJson (8 * 2^30))]
    let cases ← IO.ofExcept (Ix.AiurInvocation.decodeCases (← IO.FS.readBinFile (fixtures / "claims.ixt")))
    let some rejected := cases.find? fun c => !c.accept
      | fail "missing negative claim fixture"
    let invalid := out / "invalid.ixi"
    IO.FS.writeBinFile invalid rejected.bytes
    let rejectedJob := Json.mkObj [("id", "invalid"), ("artifact", toJson artifact.toString),
      ("input", toJson invalid.toString), ("output", toJson (out / "invalid-proof").toString)]
    let dir ← resident c binary "rejected" (config.setObjVal! "mode" "execute") #[rejectedJob] #[1]
    let error ← IO.ofExcept ((← field (← readJson (dir / "done/invalid.json")) ["report", "error"]).getStr?)
    if let some expected := rejected.rejectsWith then
      unless (error.splitOn expected).length > 1 do fail s!"wrong negative verdict: {error}"
    unless !error.isEmpty && (error.splitOn "missing hint").length == 1 do
      fail s!"negative fixture failed before reaching a verdict: {error}"
    for mode in ["execute", "plan"] do
      let output := out / s!"{mode}-proof"
      let job := Json.mkObj [("id", "claim"), ("artifact", toJson artifact.toString),
        ("input", toJson input.toString), ("output", toJson output.toString),
        ("options", Json.mkObj [("max_ram_bytes", toJson 1)])]
      let dir ← resident c binary mode (config.setObjVal! "mode" (toJson mode))
        #[job] #[if mode == "plan" then 75 else 0]
      if ← output.pathExists then fail s!"{mode} wrote a proof"
      let result ← readJson (dir / "done/claim.json")
      let _ ← field result ["report", "execution_statistics"]
      if mode == "plan" then
        unless (← field result ["report", "can_split"]) == toJson false do
          fail "fixed-floor refusal claimed splitting could help"
    -- Omitted mode keeps the existing proving protocol. Independently verify
    -- both jobs after the resident execution/prover queues have drained.
    let jobs := (Array.range 2).map fun i => Json.mkObj [
      ("id", toJson s!"prove-{i}"), ("artifact", toJson artifact.toString),
      ("input", toJson input.toString), ("output", toJson (out / s!"prove-{i}").toString)]
    let _ ← resident c binary "prove-default" config jobs #[0, 0]
    let host ← absolute "target/release/ixvm-proof"
    for i in [0:2] do
      let _ ← run c s!"verify-{i}" #[host.toString, "verify", artifact.toString,
        input.toString, (out / s!"prove-{i}").toString]
    report.set "success" (toJson true)
    report.save
    return 0
  catch e =>
    report.set "error" (toJson e.toString)
    report.save
    IO.eprintln s!"Checking validation failed: {e}; see {out}"
    return 1

end Tests.FormalChecks.Checking
