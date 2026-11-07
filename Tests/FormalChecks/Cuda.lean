import Tests.FormalChecks.Common

/-!
# `formal-checks cuda`

Check grouped, sharded CPU/CUDA proofs using `check-formal.sh` fixtures.

The default requires a real CUDA device. `--cpu-only` exercises the CPU
controls without claiming hardware validation. Every run preserves its logs and
report.
-/

namespace Tests.FormalChecks.Cuda

open Lean System Tests.FormalChecks

def usage : String :=
  "usage: formal-checks cuda [--cpu-dir DIR] [--cuda-dir DIR] [--device N] [--cpu-only] \
    --ixvm-artifact A --recursion-artifact A --aggregate-artifact A fixtures"

/-- A proof product's proof, key and report. -/
def files (product : FilePath) (ixvm : Bool) : FilePath × FilePath × FilePath :=
  if ixvm then (product, product.toString ++ ".vk", product.toString ++ ".report.json")
  else (product / "proof.bin", product / "key.bin", product / "report.json")

structure Context where
  out : FilePath
  report : Report

/-- Run `command`, logged to `NN-name.log`, and record it. Its exit status must
be success unless `succeeds` is false. -/
def run (c : Context) (name : String) (command : Array String)
    (env : Array (String × Option String)) (succeeds := true) : IO Unit := do
  let log := c.out / s!"{pad2 (← c.report.count "commands")}-{name}.log"
  IO.println name
  (← IO.getStdout).flush
  let start ← seconds
  let code ← waitFor (← spawnLogged command env log) none name
  let traceOnly := (env.findSome? fun (k, v) => if k == "AIUR_TRACE_ONLY_LOOKUPS" then v else none)
  c.report.push "commands" (Json.mkObj [("name", toJson name), ("command", toJson command),
    ("log", toJson (log.fileName.getD "")), ("seconds", floatJson ((← seconds) - start)),
    ("exit_code", toJson code.toNat), ("expected_success", toJson succeeds),
    ("trace_only_lookups", toJson traceOnly)])
  c.report.save
  if (code == 0) != succeeds then
    fail s!"{name}: unexpected exit {code}; see {log}"

/-- One proof variant: its name, host, environment, retention and device. -/
structure Variant where
  name : String
  binary : FilePath
  env : Array (String × Option String)
  retention : String
  device : Option Nat

/-- Prove `invocation` under `variant` with `rows`-row shards, check the proof
verifies (and has `shards` shards when given, more than one otherwise), verify
it independently on the CPU, and return its proof and key bytes and report. -/
def prove (c : Context) (cpu : FilePath) (name : String) (artifact invocation : FilePath)
    (ixvm : Bool) (directory : FilePath) (v : Variant) (rows : Nat)
    (verifyEnv : Array (String × Option String)) (single : Bool) :
    IO (ByteArray × ByteArray × Json × FilePath) := do
  let target := directory / v.name
  IO.FS.createDir target
  let product := target / "proof"
  let options := target / "options.json"
  IO.FS.writeFile options (Json.mkObj [("max_rows", toJson rows), ("retention", toJson v.retention),
    ("device", toJson v.device)]).compress
  run c s!"{name}-{v.name}" #[v.binary.toString, "prove", artifact.toString, invocation.toString,
    product.toString, toString rows, v.retention, options.toString] v.env
  let (proof, key, proofReport) := files product ixvm
  let result ← readJson proofReport
  let shards ← natField result ["shards"]
  if single then
    unless (← boolField result ["verified"]) && shards == 1 &&
        (← field result ["plan", "retention"]) == toJson v.retention do
      fail s!"{name}-{v.name}: single-shard retention was not honored"
  else
    unless (← boolField result ["verified"]) && shards ≥ 2 do
      fail s!"{name}-{v.name}: proof did not verify across multiple shards"
  -- Deliberately inherit the GPU lookup flag in the CPU verifier.
  run c s!"{name}-{v.name}-verify" #[cpu.toString, "verify", artifact.toString,
    invocation.toString, proof.toString] verifyEnv
  let proofBytes ← IO.FS.readBinFile proof
  let keyBytes ← IO.FS.readBinFile key
  return (proofBytes, keyBytes, result, proof)

def main (argv : List String) : IO UInt32 := do
  let args ← match Args.parse ["cpu-only"] argv with
    | .ok a => pure a
    | .error e => return ← usageError usage e
  let some fixtures := args.positional[0]? | return ← usageError usage "missing fixtures"
  let (some ixvmArtifact, some recursionArtifact, some aggregateArtifact) :=
      (args.flag? "ixvm-artifact", args.flag? "recursion-artifact", args.flag? "aggregate-artifact")
    | return ← usageError usage "the three artifacts are required"
  let cpuDir := System.FilePath.mk ((args.flag? "cpu-dir").getD "target/release")
  let cudaDir := System.FilePath.mk ((args.flag? "cuda-dir").getD "target/formal-cuda/release")
  let deviceText := (args.flag? "device").getD
    ((← IO.getEnv "MULTI_STARK_CUDA_DEVICE").getD "0")
  let some device := deviceText.toNat? | return ← usageError usage "argument --device: invalid int value"
  unless device < 2 ^ 31 do
    return ← usageError usage "device must be a nonnegative CUDA device index fitting i32"
  let cpuOnly := args.has "cpu-only"
  let fixtures ← IO.FS.realPath (System.FilePath.mk fixtures)
  let out ← freshDir fixtures "cuda-check-"
  let report ← Report.new out [("success", false), ("hardware_validated", false),
    ("cpu_only", toJson cpuOnly), ("device", toJson device),
    ("cuda_visible_devices", toJson (← IO.getEnv "CUDA_VISIBLE_DEVICES")),
    ("revision", toJson (← revision)), ("binary_sha256", Json.mkObj []),
    ("artifact_sha256", Json.mkObj []), ("input_sha256", Json.mkObj []),
    ("commands", Json.arr #[]), ("cases", Json.arr #[])]
  IO.println s!"CUDA validation logs and report: {out}"
  (← IO.getStdout).flush
  let c : Context := { out, report }
  let digests (key : String) (path : FilePath) : IO Unit := do
    report.set key (((← report.get key).setObjVal! path.toString (toJson (← sha256 path))))
  try
    let cpuEnv : Array (String × Option String) :=
      #[("IX_CUDA", some "0"), ("AIUR_TRACE_ONLY_LOOKUPS", some "0")]
    let verifyEnv := cpuEnv.push ("AIUR_TRACE_ONLY_LOOKUPS", some "1")
    let gpuEnv := cpuEnv ++ #[("IX_CUDA", some "1"), ("MULTI_STARK_CUDA_DEVICE", some (toString device))]
    for directory in #[cpuDir] ++ (if cpuOnly then #[] else #[cudaDir]) do
      for name in ["ixvm-proof", "stark-verifier"] do
        digests "binary_sha256" (directory / name)
    if !cpuOnly then
      let which ← IO.Process.output { cmd := "sh", args := #["-c", "command -v nvidia-smi"] }
      if which.exitCode == 0 then run c "nvidia-smi" #["nvidia-smi"] gpuEnv

    let claims ← IO.ofExcept ((← readJson (fixtures / "claims.json")).getArr?)
    let some claim := claims.findSome? fun entry =>
        if (entry.getObjValAs? Bool "accept").toOption == some true &&
            (entry.getObjValAs? String "label").toOption == some "CheckEnv frontier-asm (Nat.add_comm)"
        then (entry.getObjVal? "invocation").toOption else none
      | fail "claims.json has no accepted CheckEnv frontier-asm (Nat.add_comm) case"
    let claimPath := out / "claim.json"
    IO.FS.writeFile claimPath (claim.compress ++ "\n")
    let cases : Array (String × FilePath × FilePath × Bool) := #[
      ("ixvm", System.FilePath.mk ixvmArtifact, claimPath, true),
      ("recursion", System.FilePath.mk recursionArtifact, fixtures / "inner/input.json", false),
      ("aggregate", System.FilePath.mk aggregateArtifact, fixtures / "aggregation.json.wrap.json",
        false)]
    for (name, artifact, invocation, ixvm) in cases do
      digests "artifact_sha256" artifact
      digests "input_sha256" invocation
      let binaryName := if ixvm then "ixvm-proof" else "stark-verifier"
      let cpu := cpuDir / binaryName
      let cuda := cudaDir / binaryName
      let directory := out / name
      IO.FS.createDir directory
      -- Derive a two-shard fixture from the actual record, instead of
      -- picking a row cap that might silently leave a one-shard test.
      let plan := directory / "plan"
      run c s!"{name}-plan" #[cpu.toString, "plan", artifact.toString, invocation.toString,
        plan.toString, "0", "regenerate"] cpuEnv
      let planning ← field (← readJson (files plan ixvm).2.2) ["plan"]
      let maxRows ← natField planning ["max_rows"]
      unless (← boolField planning ["fits"]) && maxRows ≥ 2 do
        fail s!"{name}: fixture cannot exercise trace sharding"
      let rows := maxRows / 2
      let mut proofs : Array Json := #[]
      let mut singles : Array Json := #[]
      let caseIndex ← report.count "cases"
      let saveCase (proofs singles : Array Json) : IO Unit := do
        let all := ((← report.get "cases").getArr?).toOption.getD #[]
        report.set "cases" (.arr (all.set! caseIndex (Json.mkObj [("name", toJson name),
          ("max_rows", toJson rows), ("proofs", .arr proofs), ("single_shard_proofs", .arr singles)])))
        report.save
      report.push "cases" Json.null
      saveCase proofs singles
      let mut variants : Array Variant := #[
        ⟨"cpu-retain", cpu, cpuEnv, "retain", none⟩,
        ⟨"cpu-regenerate", cpu, cpuEnv, "regenerate", none⟩]
      if !cpuOnly then
        let graph := gpuEnv.push ("AIUR_TRACE_ONLY_LOOKUPS", some "1")
        variants := variants ++ #[
          ⟨"cuda-host-retain", cuda, gpuEnv, "retain", some device⟩,
          ⟨"cuda-host-regenerate", cuda, gpuEnv, "regenerate", some device⟩,
          ⟨"cuda-graph-regenerate", cuda, graph, "regenerate", some device⟩,
          -- Rows the GPU can populate are generated on the device.
          ⟨"cuda-gputrace-regenerate", cuda, graph.push ("AIUR_GPU_TRACE", some "generated"),
            "regenerate", some device⟩]
      let mut reference : Option (ByteArray × ByteArray) := none
      for v in variants do
        let (proofBytes, keyBytes, result, proof) ←
          prove c cpu name artifact invocation ixvm directory v rows verifyEnv false
        match reference with
        | none =>
          reference := some (proofBytes, keyBytes)
          let exported := directory / "cpu-key"
          run c s!"{name}-cpu-key" #[cpu.toString, "key", artifact.toString, exported.toString]
            verifyEnv
          unless (← IO.FS.readBinFile (exported / "key.bin")) == keyBytes do
            fail s!"{name}: exported key differs from proving key"
          let wrong ← readJson invocation
          let first ← IO.ofExcept ((← field wrong ["args"]).getArrVal? 0 >>= (·.getNat?))
          let args ← IO.ofExcept ((← field wrong ["args"]).getArr?)
          let wrong := wrong.setObjVal! "args" (.arr (args.set! 0 (toJson (if first == 0 then 1 else 0))))
          let wrongPath := directory / "wrong-public.json"
          IO.FS.writeFile wrongPath wrong.compress
          run c s!"{name}-reject-wrong-public" #[cpu.toString, "verify", artifact.toString,
            wrongPath.toString, proof.toString] verifyEnv (succeeds := false)
          -- A CPU host must not silently honor an explicit GPU request.
          let invalid := directory / "cpu-device.json"
          IO.FS.writeFile invalid (Json.mkObj [("device", toJson device)]).compress
          run c s!"{name}-reject-cpu-device" #[cpu.toString, "plan", artifact.toString,
            invocation.toString, (directory / "invalid").toString, toString rows, "auto",
            invalid.toString] cpuEnv (succeeds := false)
        | some r =>
          unless r == (proofBytes, keyBytes) do
            fail s!"{name}-{v.name}: CPU/CUDA or retention proof/key bytes differ"
        let key : FilePath := if ixvm then proof.toString ++ ".vk" else proof.parent.get! / "key.bin"
        proofs := proofs.push (Json.mkObj [("variant", toJson v.name),
          ("proof_sha256", toJson (← sha256 proof)), ("key_sha256", toJson (← sha256 key)),
          ("shards", (← field result ["shards"])), ("proof_bytes", (← field result ["proof_bytes"]))])
        saveCase proofs singles
      -- Graph-derived lookups must also work when the only stage-one
      -- commitment is retained. This avoids an entire extra upload/LDE/
      -- Merkle pass without increasing peak device residency.
      let mut singleVariants : Array Variant := #[⟨"cpu-single-retain", cpu, cpuEnv, "retain", none⟩]
      if !cpuOnly then
        let graph := gpuEnv.push ("AIUR_TRACE_ONLY_LOOKUPS", some "1")
        singleVariants := singleVariants ++ #[
          ⟨"cuda-graph-single-retain", cuda, graph, "retain", some device⟩,
          ⟨"cuda-graph-single-regenerate", cuda, graph, "regenerate", some device⟩,
          ⟨"cuda-gputrace-single-retain", cuda, graph.push ("AIUR_GPU_TRACE", some "generated"),
            "retain", some device⟩]
      let mut singleReference : Option (ByteArray × ByteArray) := none
      for v in singleVariants do
        let (proofBytes, keyBytes, result, proof) ←
          prove c cpu name artifact invocation ixvm directory v maxRows verifyEnv true
        unless some keyBytes == reference.map (·.2) do
          fail s!"{name}-{v.name}: sharding changed the key"
        match singleReference with
        | none => singleReference := some (proofBytes, keyBytes)
        | some r =>
          unless r == (proofBytes, keyBytes) do
            fail s!"{name}-{v.name}: single-shard CPU/CUDA proof bytes differ"
        let key : FilePath := if ixvm then proof.toString ++ ".vk" else proof.parent.get! / "key.bin"
        singles := singles.push (Json.mkObj [("variant", toJson v.name),
          ("proof_sha256", toJson (← sha256 proof)), ("key_sha256", toJson (← sha256 key)),
          ("shards", (← field result ["shards"])), ("retention", (← field result ["plan", "retention"])),
          ("proof_bytes", (← field result ["proof_bytes"]))])
        saveCase proofs singles
    report.set "success" true
    report.set "hardware_validated" (toJson (!cpuOnly))
    IO.println (if cpuOnly then "CPU controls passed." else "CPU/CUDA proof and key parity passed.")
    report.save
    return 0
  catch e =>
    report.set "error" (toJson (toString e))
    report.save
    throw e

end Tests.FormalChecks.Cuda
