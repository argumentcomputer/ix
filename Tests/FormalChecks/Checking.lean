import Tests.FormalChecks.Controller

/-! Manifest checking and standalone IxVM host verification: concurrency must
preserve verdicts and circuit statistics; budget refusals must not publish a
refined manifest and must mark benchmark rows rejected; negative fixtures,
execute/plan fixed-floor refusal, and prove/verify are checked through the
production `ixvm-proof` host. -/

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
  let host ← absolute "target/release/ixvm-proof"
  let ix ← absolute ".lake/build/bin/ix"
  let report ← Report.new out [("success", false), ("commands", Json.arr #[])]
  let c : Context := { out, report, env := #[
    ("IX_AIUR_ARTIFACT", some artifact.toString),
    ("IX_CUDA", some "0"),
    ("IX_AIUR_CIRCUIT_VERDICT", some "1")] }
  IO.println s!"Checking validation logs: {out}"
  try
    let env := fixtures / "claims.ixt.controller.ixe"
    let manifest := out / "two.ixes"
    let _ ← run c "partition" #[ix.toString, "shard", env.toString, "--shards", "2", "--out", manifest.toString]
    let resources ← IO.Process.output { cmd := host.toString, args := #["resources"] }
    unless resources.exitCode == 0 do fail resources.stderr
    let cores ← natField (← IO.ofExcept (Json.parse resources.stdout)) ["cores"]
    let mut reference : Option (Array Json) := none
    for jobs in [1, 2, 0] do
      let path := out / s!"jobs-{jobs}.json"
      let row := out / s!"jobs-{jobs}.bench.json"
      let args := #[ix.toString, "check", "--ixe", env.toString,
        "--ixes", manifest.toString, "--ram-budget", "16",
        "--jobs", toString jobs,
        "--report", path.toString, "--json", row.toString, "--keep-going"]
      let _ ← run c s!"jobs-{jobs}" args
      let result ← readJson path
      let expectedJobs := if jobs == 0 then max 1 (min cores 2) else jobs
      unless (← natField result ["failures"]) == 0 && (← natField result ["jobs"]) == expectedJobs do
        fail s!"jobs-{jobs}: failed or ignored concurrency"
      let leaves ← IO.ofExcept ((← field result ["leaves"]).getArr?)
      let measurements ← leaves.flatMapM fun leaf => do
        let parts ← IO.ofExcept ((← field leaf ["parts"]).getArr?)
        parts.mapM fun part => do
          unless (← boolField part ["report", "plan", "fits"]) do
            fail s!"jobs-{jobs}: leaf plan unexpectedly did not fit"
          field part ["report", "execution_statistics"]
      if let some previous := reference then
        unless measurements == previous do fail "concurrency changed circuit statistics"
      reference := some measurements
      let rowObj ← field (← readJson row) ["env"]
      unless (← field rowObj ["status"]) == toJson "ok" do
        fail s!"jobs-{jobs}: benchmark row did not report ok"
      unless (← natField rowObj ["shards"]) == 2 do
        fail s!"jobs-{jobs}: unexpected shard count in benchmark row"
      let _ ← IO.ofExcept (rowObj.getObjValAs? Float "check-time")

    -- Budget refusal: `--ram-budget 1` must refuse, skip publishing `--out-ixes`,
    -- and mark the benchmark row `rejected` (exit 3).
    let refusedOut := out / "refused.ixes"
    let refusedRow := out / "refused.bench.json"
    let _ ← run c "budget-refuse"
      #[ix.toString, "check", "--ixe", env.toString, "--ixes", manifest.toString,
        "--ram-budget", "1", "--jobs", "1",
        "--out-ixes", refusedOut.toString, "--json", refusedRow.toString, "--keep-going"]
      #[] false
    if ← refusedOut.pathExists then fail "budget refusal published a refined manifest"
    let refusedRowObj ← field (← readJson refusedRow) ["env"]
    unless (← field refusedRowObj ["status"]) == toJson "rejected" do
      fail "budget refusal did not mark benchmark row rejected"

    -- Reject a negative claim fixture through `ixvm-proof execute`, verifying
    -- it reaches the expected rejection reason instead of failing on advice.
    let cases ← IO.ofExcept (Ix.AiurInvocation.decodeCases (← IO.FS.readBinFile (fixtures / "claims.ixt")))
    let some rejected := cases.find? fun c => !c.accept
      | fail "missing negative claim fixture"
    let invalid := out / "invalid.ixi"
    IO.FS.writeBinFile invalid rejected.bytes
    let rejectedLog ← run c "rejected"
      #[host.toString, "execute", artifact.toString, invalid.toString] #[] false
    if let some expected := rejected.rejectsWith then
      unless mentions rejectedLog expected do
        fail s!"wrong negative verdict: {rejectedLog}"
    unless !rejectedLog.isEmpty && !mentions rejectedLog "missing hint" do
      fail s!"negative fixture failed before reaching a verdict: {rejectedLog}"

    -- Exercise `execute` and fixed-floor `plan` refusal (`max_ram_bytes = 1`)
    -- without writing proof outputs, then prove & independently verify.
    let input := out / "claim.ixi"
    IO.FS.writeBinFile input (← caseInvocation (fixtures / "claims.ixt") "CheckEnv frontier-asm (Nat.add_comm)")
    let execOut := out / "execute-proof"
    let _ ← run c "execute" #[host.toString, "execute", artifact.toString, input.toString, execOut.toString]
    if ← execOut.pathExists then fail "execute wrote a proof"
    let execReport ← readJson (execOut.toString ++ ".report.json")
    let _ ← field execReport ["execution_statistics"]

    let tinyOpts := out / "tiny-ram.json"
    IO.FS.writeFile tinyOpts (Json.mkObj [("max_ram_bytes", toJson (1 : Nat))]).compress
    let planOut := out / "plan-proof"
    let _ ← run c "plan-refuse"
      #[host.toString, "plan", artifact.toString, input.toString, planOut.toString,
        "0", "auto", tinyOpts.toString]
    if ← planOut.pathExists then fail "plan wrote a proof"
    let planReport ← readJson (planOut.toString ++ ".report.json")
    unless (← field planReport ["can_split"]) == toJson false do
      fail "fixed-floor refusal claimed splitting could help"
    unless (← boolField planReport ["plan", "fits"]) == false do
      fail "fixed-floor refusal reported fits = true"

    let proofPath := out / "prove-0"
    let _ ← run c "prove-0" #[host.toString, "prove", artifact.toString, input.toString, proofPath.toString]
    let _ ← run c "verify-0" #[host.toString, "verify", artifact.toString, input.toString, proofPath.toString]
    report.set "success" (toJson true)
    report.save
    return 0
  catch e =>
    report.set "error" (toJson e.toString)
    report.save
    IO.eprintln s!"Checking validation failed: {e}; see {out}"
    return 1

end Tests.FormalChecks.Checking
