module

public import Ix.Cli.CheckCmd

namespace Tests.Cli.NativePartition

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| IO.userError message

private def manifestBytes (shards : Array (Array Address)) : ByteArray := Id.run do
  let mut out : ByteArray := ⟨#[0x49, 0x58, 0x45, 0x53, 0, 0, 0, 0] ++ Array.replicate 16 0⟩
  out := out ++ shards.size.toUInt32.toLEBytes
  for (blocks, id) in shards.mapIdx (fun id blocks => (blocks, id)) do
    out := out ++ id.toUInt32.toLEBytes ++ ⟨Array.replicate 25 0⟩
    out := out ++ blocks.size.toUInt32.toLEBytes
    for block in blocks do out := out ++ block.hash
    out := out ++ (0 : UInt32).toLEBytes
  -- Explicit absent aggregation tree and measured peaks (legacy-compatible).
  return out ++ ⟨#[0, 0]⟩

public def run : IO Unit := do
  let dependency : Ixon.Constant :=
    ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ .zero]⟩
  let dependencyAddr := Address.blake3 (Ixon.serConstant dependency)
  let consumer : Ixon.Constant :=
    ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[dependencyAddr], #[]⟩
  let consumerAddr := Address.blake3 (Ixon.serConstant consumer)
  let env := (({} : Ixon.Env).storeConst dependencyAddr dependency)
    |>.storeConst consumerAddr consumer
  let shards := #[#[consumerAddr], #[dependencyAddr]]
  let bytes ← IO.ofExcept (Ixon.serEnv env)
  let dir ← IO.FS.createTempDir
  try
    let ixe := dir / "fixture.ixe"
    let ixes := dir / "fixture.ixes"
    let report := dir / "report.json"
    IO.FS.writeBinFile ixe bytes
    IO.FS.writeBinFile ixes (manifestBytes shards)
    let toplevel ← IO.ofExcept IxVM.ixVM
    let compiled ← IO.ofExcept toplevel.compile
    let funIdx := compiled.getFuncIdx `verify_claim |>.get!
    let check := fun bytecode jobs => compiled.bytecode.checkPartition funIdx
      ixe.toString ixes.toString jobs bytecode Aiur.defaultCommitmentParameters
      Aiur.defaultFriParameters report.toString "test" "ix check" "none"
    let legacyHandle ← IO.ofExcept (Aiur.EnvHandle.fromBytes bytes)
    let owned := Ix.Cli.CheckCmd.ownedConstsPer env shards
    expect (← Ix.Cli.CheckCmd.shardsCover env shards) "reference coverage failed"
    for bytecode in [false, true] do
      let native ← IO.ofExcept (← check bytecode 2)
      expect (native.constants == 2 && native.shards == 2 && native.failures == 0)
        "native full-partition execution/counts failed"
      let legacy ← IO.ofExcept (compiled.bytecode.shardCheckBatchWithEnv funIdx
        legacyHandle (Ix.Cli.CheckCmd.addrListsBlob owned) bytecode 2)
      expect (legacy.size == 2 && legacy.all (·.error.isEmpty))
        "legacy shard execution disagrees with native setup"
      let audit ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile report))
      let leaves ← IO.ofExcept (audit.getObjValAs? (Array Lean.Json) "leaves")
      expect (leaves.size == 2) "native audit omitted leaves"
      for (addresses, id) in owned.mapIdx (fun id addresses => (addresses, id)) do
        let (claim, _) ← IO.ofExcept (IxVM.ClaimHarness.shardCheckEnvClaimTrees env addresses)
        let expected := toString (Address.blake3 (Ix.Claim.ser claim))
        let actual ← IO.ofExcept (leaves[id]!.getObjValAs? String "claim")
        expect (actual == expected) "native audit changed a shard claim digest"
        let peak ← IO.ofExcept (leaves[id]!.getObjValAs? Nat "predicted_peak_bytes")
        expect (peak == legacy[id]!.peakBytes) "native execution record/peak disagrees with legacy"
    -- Exercise actual CLI dispatch and ensure options that still need the
    -- legacy wave driver are never silently ignored by the native fast path.
    let ix ← IO.FS.realPath ".lake/build/bin/ix"
    for (extra, nativePath, selected, budget) in
        [(#[], true, 2, 0), (#["--shards", "0"], false, 1, 0),
         (#["--ram-budget", "1"], false, 2, 1024 * 1024 * 1024)] do
      let out ← IO.Process.output { cmd := ix.toString, args :=
        #["check", "--ixe", ixe.toString, "--ixes", ixes.toString,
          "--jobs", "2", "--report", report.toString,
          "--json", (dir / "results.json").toString] ++ extra }
      expect (out.exitCode == 0) s!"partition CLI failed: {out.stdout}\n{out.stderr}"
      expect (out.stderr.contains "[ixvm_setup]" == nativePath)
        "partition CLI routed to the wrong setup path"
      let audit ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile report))
      expect ((← IO.ofExcept (audit.getObjValAs? Nat "selected")) == selected)
        "partition CLI ignored a shard selection"
      expect ((← IO.ofExcept (audit.getObjValAs? Nat "budget_bytes")) == budget)
        "partition CLI ignored a refinement budget"
    -- Invalid coverage must fail setup, never return successful partial work.
    -- Reuse the path strings after file writes: the IO FFI must read new bytes.
    for invalid in [#[#[consumerAddr]], #[#[consumerAddr, dependencyAddr], #[dependencyAddr]]] do
      IO.FS.writeBinFile ixes (manifestBytes invalid)
      expect (!(← check false 2).isOk) "native setup accepted incomplete/duplicate ownership"
    -- Both readers must reject malformed trailing manifest data.
    let trailing := (manifestBytes shards).push 0
    IO.FS.writeBinFile ixes trailing
    expect (!(Ix.Cli.CheckCmd.parseIxesManifest trailing).isOk) "reference parser accepted trailing bytes"
    expect (!(← check false 2).isOk) "native parser accepted trailing bytes"
    IO.FS.writeBinFile ixes (manifestBytes shards)
    let restored ← IO.ofExcept (← check false 2)
    expect (restored.failures == 0) "native setup reused a stale path-based result"
    -- A well-framed but ill-typed constant reaches execution and is rejected,
    -- rather than being mistaken for a successful setup/coverage result.
    let bad : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 99 #[]⟩, #[], #[], #[]⟩
    let badAddr := Address.blake3 (Ixon.serConstant bad)
    IO.FS.writeBinFile ixe (← IO.ofExcept (Ixon.serEnv (({} : Ixon.Env).storeConst badAddr bad)))
    IO.FS.writeBinFile ixes (manifestBytes #[#[badAddr]])
    let rejected ← IO.ofExcept (← check false 1)
    expect (rejected.constants == 1 && rejected.shards == 1 && rejected.failures == 1)
      "native full-partition execution accepted an invalid constant"
    IO.println "native partition: executor/claim/peak parity and fail-closed setup passed"
  finally
    IO.FS.removeDirAll dir

end Tests.Cli.NativePartition
