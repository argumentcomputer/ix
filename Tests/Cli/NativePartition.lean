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
    let checkSelected := fun (selection : Option (Array Nat)) bytecode jobs =>
      compiled.bytecode.checkPartition funIdx
      ixe.toString ixes.toString jobs bytecode Aiur.defaultCommitmentParameters
      Aiur.defaultFriParameters report.toString "test" "ix check" "none" selection
    let check := checkSelected none
    let legacyHandle ← IO.ofExcept (Aiur.EnvHandle.fromBytes bytes)
    let owned := Ix.Cli.CheckCmd.ownedConstsPer env shards
    expect (← Ix.Cli.CheckCmd.shardsCover env shards) "reference coverage failed"
    for bytecode in [false, true] do
      let native ← IO.ofExcept (← check bytecode 2)
      expect (native.constants == 2 && native.shards == 2 && native.failures == 0)
        "native full-partition execution/counts failed"
      let legacy ← IO.ofExcept (← compiled.bytecode.shardCheckBatchWithEnv funIdx
        legacyHandle (Ix.Cli.CheckCmd.addrListsBlob owned) bytecode 2)
      expect (legacy.size == 2 && legacy.all (·.error.isEmpty))
        "legacy shard execution disagrees with native setup"
      let audit ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile report))
      expect ((← IO.ofExcept (audit.getObjValAs? String "scheduler")) == "completion-driven" &&
          (← IO.ofExcept (audit.getObjVal? "waves")) == .null &&
          (← IO.ofExcept (audit.getObjValAs? Nat "executed")) == 2)
        "native scheduler audit still reports batch-wave semantics"
      let leaves ← IO.ofExcept (audit.getObjValAs? (Array Lean.Json) "leaves")
      expect (leaves.size == 2) "native audit omitted leaves"
      for (addresses, id) in owned.mapIdx (fun id addresses => (addresses, id)) do
        let (claim, _) ← IO.ofExcept (IxVM.ClaimHarness.shardCheckEnvClaimTrees env addresses)
        let expected := toString (Address.blake3 (Ix.Claim.ser claim))
        let actual ← IO.ofExcept (leaves[id]!.getObjValAs? String "claim")
        expect (actual == expected) "native audit changed a shard claim digest"
        let peak ← IO.ofExcept (leaves[id]!.getObjValAs? Nat "predicted_peak_bytes")
        expect (peak == legacy[id]!.peakBytes) "native execution record/peak disagrees with legacy"
      -- The dependent consumer needs the skipped shard's declaration as
      -- frontier input, but must not claim that shard was checked. Selecting
      -- only shard 1 also detects accidental compact-id remapping to shard 0.
      for selection in [#[0], #[1], #[1, 0, 1]] do
        let selected := selection.toList.eraseDups.toArray
        let subset ← IO.ofExcept (← checkSelected (some selection) bytecode 2)
        expect (subset.constants == selected.size && subset.shards == selected.size &&
            subset.failures == 0) "selected counts include skipped or duplicated shards"
        let audit ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile report))
        let leaves ← IO.ofExcept (audit.getObjValAs? (Array Lean.Json) "leaves")
        expect (leaves.size == shards.size) "selected audit dropped original manifest leaves"
        for id in [:shards.size] do
          expect ((← IO.ofExcept (leaves[id]!.getObjValAs? Nat "id")) == id)
            "selected audit renumbered a manifest leaf"
          let status ← IO.ofExcept (leaves[id]!.getObjValAs? String "status")
          if selected.contains id then
            expect (status == "measured") "selected shard was not executed"
            let (claim, _) ← IO.ofExcept
              (IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned[id]!)
            expect ((← IO.ofExcept (leaves[id]!.getObjValAs? String "claim")) ==
                toString (Address.blake3 (Ix.Claim.ser claim)))
              "selected claim differs from the legacy claim"
            expect ((← IO.ofExcept (leaves[id]!.getObjValAs? Nat "predicted_peak_bytes")) ==
                legacy[id]!.peakBytes) "selected execution record differs from legacy"
          else
            expect (status == "unchanged") "skipped shard was reported checked"
            expect ((← IO.ofExcept (leaves[id]!.getObjVal? "claim")) == .null &&
                (← IO.ofExcept (leaves[id]!.getObjVal? "predicted_peak_bytes")) == .null)
              "skipped shard acquired a claim or measured peak"
    for selection in [#[], #[2], #[2^128]] do
      expect (!(← checkSelected (some selection) false 2).isOk)
        "invalid/empty/oversized selection was accepted by the FFI"
    -- Exercise actual CLI dispatch and ensure options that still need the
    -- legacy wave driver are never silently ignored by the native fast path.
    let ix ← IO.FS.realPath ".lake/build/bin/ix"
    for (extra, nativePath, selected, budget, jobs) in
        [(#[], true, 2, 0, 1), (#[], true, 2, 0, 2), (#[], true, 2, 0, 64),
         (#["--shards", "0"], true, 1, 0, 2),
         (#["--shards", "1"], true, 1, 0, 2),
         (#["--shards", "1,0-1,1"], true, 2, 0, 2),
         (#["--shards", "1", "--interp", "bytecode"], true, 1, 0, 2),
         (#["--shards", "1", "--ram-budget", "1"], false, 1, 1024 * 1024 * 1024, 2),
         (#["--ram-budget", "1"], false, 2, 1024 * 1024 * 1024, 2)] do
      -- Opt-in final scans must work for native/bytecode and legacy setup,
      -- and remain silent when explicitly disabled, irrespective of the
      -- environment of the surrounding test runner.
      let profile := selected == 1
      let out ← IO.Process.output {
        cmd := ix.toString
        args := #["check", "--ixe", ixe.toString, "--ixes", ixes.toString,
          "--jobs", toString jobs, "--report", report.toString,
          "--json", (dir / "results.json").toString] ++ extra
        env := #[("IX_AIUR_SETUP_THREADS", some "2"), ("RAYON_NUM_THREADS", some "1"),
          ("IX_AIUR_COMPACT_MULTIPLICITIES", some (if profile then "1" else "0")),
          ("IX_AIUR_MULTIPLICITY_STATS", some (if profile then "1" else "0"))]
      }
      expect (out.exitCode == 0) s!"partition CLI failed: {out.stdout}\n{out.stderr}"
      expect (out.stderr.contains "[ixvm_setup]" == nativePath)
        "partition CLI routed to the wrong setup path"
      expect (out.stderr.contains "[ixvm_memory]")
        "partition CLI omitted memory-admission diagnostics"
      expect (out.stderr.contains "reason=" && out.stderr.contains "psi_avg10=")
        "partition CLI omitted the admission backoff reason/pressure trend"
      expect (out.stderr.contains "[aiur-multiplicity]" == profile)
        "multiplicity diagnostics ignored the opt-in setting"
      if profile then
        expect (out.stderr.contains "status=returned" &&
            out.stderr.contains "map=functions" && out.stderr.contains "map=memory" &&
            out.stderr.contains "snapshot_only=true" &&
            out.stderr.contains "stored_payload_bytes=" &&
            out.stderr.contains "stored_segments_u32_field=" &&
            out.stderr.contains "reservation_peak_bytes=")
          "successful execution omitted its bounded multiplicity snapshot"
      if nativePath then
        expect (out.stderr.contains "completion-driven queue" &&
            out.stderr.contains "attempt=" && out.stderr.contains "generation=")
          "native partition CLI omitted completion-driven attempt reporting"
        expect (out.stderr.contains s!"{selected}/{selected} shards")
          "native partition CLI omitted shard completions"
        expect (out.stderr.contains "(2 setup threads)")
          "native setup ignored its independent thread count"
        if jobs == 1 then
          expect (out.stderr.contains "limit=1/1" && out.stderr.contains "1 thread(s)")
            "parallel setup widened single-worker execution"
      let audit ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile report))
      expect ((← IO.ofExcept (audit.getObjValAs? Nat "selected")) == selected)
        "partition CLI ignored a shard selection"
      expect ((← IO.ofExcept (audit.getObjValAs? Nat "budget_bytes")) == budget)
        "partition CLI ignored a refinement budget"
      -- Compact counters must preserve the same claims as the full-width
      -- reference setup, also on the bytecode and legacy CLI paths.
      let leaves ← IO.ofExcept (audit.getObjValAs? (Array Lean.Json) "leaves")
      for (leaf, id) in leaves.mapIdx (fun id leaf => (leaf, id)) do
        if (← IO.ofExcept (leaf.getObjValAs? String "status")) == "measured" then
          let (claim, _) ← IO.ofExcept
            (IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned[id]!)
          expect ((← IO.ofExcept (leaf.getObjValAs? String "claim")) ==
              toString (Address.blake3 (Ix.Claim.ser claim)))
            "compact-counter CLI changed a selected claim digest"
      let rows ← Ix.Benchmark.Results.readRows (dir / "results.json").toString
      let row ← IO.ofExcept (rows.getObjVal? "env")
      expect ((← IO.ofExcept (row.getObjValAs? Nat "constants")) == selected)
        "benchmark row counted unselected constants"
      expect ((← IO.ofExcept (row.getObjValAs? Nat "shards")) == selected)
        "benchmark row counted unselected shards"
    for setting in ["0", "invalid", "184467440737095516160"] do
      let out ← IO.Process.output {
        cmd := ix.toString
        args := #["check", "--ixe", ixe.toString, "--ixes", ixes.toString, "--jobs", "1"]
        env := #[("IX_AIUR_SETUP_THREADS", some setting)]
      }
      expect (out.exitCode != 0 && out.stderr.contains "IX_AIUR_SETUP_THREADS" &&
          !out.stderr.contains "[ixvm_check]") "bad setup thread count reached execution"
    for selection in ["", "2", "340282366920938463463374607431768211456"] do
      let out ← IO.Process.output { cmd := ix.toString, args :=
        #["check", "--ixe", ixe.toString, "--ixes", ixes.toString,
          "--shards", selection, "--jobs", "2"] }
      expect (out.exitCode != 0 && !out.stderr.contains "[ixvm_check]")
        "invalid CLI selection reached execution"
    -- Force mid-execution record limits in both executors. A limited parent
    -- must split; a still-limited singleton must fail, not report success or
    -- loop forever. The legacy wave driver must consume the same typed result.
    IO.FS.writeBinFile ixes (manifestBytes #[#[consumerAddr, dependencyAddr]])
    for extra in [#[], #["--interp", "bytecode"], #["--ram-budget", "1"]] do
      let out ← IO.Process.output {
        cmd := ix.toString
        args := #["check", "--ixe", ixe.toString, "--ixes", ixes.toString,
          "--jobs", "2", "--report", report.toString] ++ extra
        env := #[("IX_AIUR_EXEC_MAX_BYTES", some "67108864"),
          ("IX_AIUR_COMPACT_MULTIPLICITIES", some "1"),
          ("IX_AIUR_MULTIPLICITY_STATS", some "1")] }
      expect (out.exitCode != 0) "resource-limited execution reported success"
      expect (out.stderr.contains "[ixvm_record]") "missing execution-limit diagnostics"
      expect (out.stderr.contains "status=resource-limit" &&
          out.stderr.contains "[aiur-multiplicity]")
        "partial execution omitted its resource-limit multiplicity snapshot"
      expect (out.stderr.contains "split" || out.stderr.contains "cut into 2")
        s!"oversized parent was not refined: {out.stdout}\n{out.stderr}"
      let audit ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile report))
      let failures ← IO.ofExcept (audit.getObjValAs? (Array Lean.Json) "failures")
      expect (!failures.isEmpty) "resource-limited leaves disappeared from the report"
    IO.FS.writeBinFile ixes (manifestBytes shards)
    -- Select a nonzero original id and force its split. The unselected leaf
    -- must remain untouched even when every selected child is resource-limited.
    IO.FS.writeBinFile ixes (manifestBytes #[#[], #[consumerAddr, dependencyAddr]])
    for extra in [#[], #["--interp", "bytecode"]] do
      let out ← IO.Process.output {
        cmd := ix.toString
        args := #["check", "--ixe", ixe.toString, "--ixes", ixes.toString,
          "--shards", "1", "--jobs", "2", "--report", report.toString] ++ extra
        env := #[("IX_AIUR_EXEC_MAX_BYTES", some "67108864")] }
      expect (out.exitCode != 0 && out.stderr.contains "shard 1: execution memory limit")
        s!"selected oversized parent was not refined natively: {out.stderr}"
      let audit ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile report))
      let leaves ← IO.ofExcept (audit.getObjValAs? (Array Lean.Json) "leaves")
      expect ((← IO.ofExcept (leaves[0]!.getObjValAs? String "status")) == "unchanged")
        "resource refinement executed an unselected leaf"
      let parts ← IO.ofExcept (leaves[1]!.getObjValAs? (Array Lean.Json) "parts")
      expect (parts.size == 2) "selected resource refinement lost a child"
      for part in parts do
        expect ((← IO.ofExcept (part.getObjValAs? String "label")).startsWith "1.")
          "selected refinement renumbered the original shard"
    IO.FS.writeBinFile ixes (manifestBytes shards)
    -- Invalid coverage must fail setup, never return successful partial work.
    -- Reuse the path strings after file writes: the IO FFI must read new bytes.
    for invalid in [#[#[consumerAddr]], #[#[consumerAddr, dependencyAddr], #[dependencyAddr]],
        #[#[consumerAddr], #[dependencyAddr, dependencyAddr]]] do
      IO.FS.writeBinFile ixes (manifestBytes invalid)
      expect (!(← check false 2).isOk) "native setup accepted incomplete/duplicate ownership"
      expect (!(← checkSelected (some #[0]) false 2).isOk)
        "selection bypassed full-partition coverage or uniqueness checks"
    -- Both readers must reject malformed trailing manifest data.
    let trailing := (manifestBytes shards).push 0
    IO.FS.writeBinFile ixes trailing
    expect (!(Ix.Cli.CheckCmd.parseIxesManifest trailing).isOk) "reference parser accepted trailing bytes"
    expect (!(← check false 2).isOk) "native parser accepted trailing bytes"
    expect (!(← checkSelected (some #[0]) false 2).isOk)
      "selection bypassed complete manifest parsing"
    -- An aggregation tree mentioning only the selected leaf is still invalid:
    -- it must cover the ORIGINAL manifest, including all skipped leaves.
    let framed := manifestBytes shards
    let partialTree := framed.extract 0 (framed.size - 2) ++
      ⟨#[1, 0]⟩ ++ (0 : UInt32).toLEBytes ++ ⟨#[0]⟩
    IO.FS.writeBinFile ixes partialTree
    expect (!(Ix.Cli.CheckCmd.parseIxesManifest partialTree).isOk)
      "reference parser accepted incomplete aggregation tree"
    expect (!(← checkSelected (some #[0]) false 2).isOk)
      "selection bypassed whole-manifest aggregation tree validation"
    IO.FS.writeBinFile ixes (manifestBytes shards)
    let restored ← IO.ofExcept (← check false 2)
    expect (restored.failures == 0) "native setup reused a stale path-based result"
    -- A well-framed but ill-typed constant reaches execution and is rejected,
    -- rather than being mistaken for a successful setup/coverage result.
    let bad : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 99 #[]⟩, #[], #[], #[]⟩
    let badAddr := Address.blake3 (Ixon.serConstant bad)
    let withBad := env.storeConst badAddr bad
    IO.FS.writeBinFile ixe (← IO.ofExcept (Ixon.serEnv withBad))
    IO.FS.writeBinFile ixes (manifestBytes (shards.push #[badAddr]))
    let skippedBad ← IO.ofExcept (← checkSelected (some #[0]) false 2)
    expect (skippedBad.constants == 1 && skippedBad.shards == 1 && skippedBad.failures == 0)
      "native selection executed an unrelated, ill-typed constant"
    let selectedBad ← IO.ofExcept (← checkSelected (some #[2]) false 2)
    expect (selectedBad.constants == 1 && selectedBad.shards == 1 && selectedBad.failures == 1)
      "native selection skipped its selected, ill-typed constant"
    -- Unlike an ill-typed declaration, a malformed body invalidates coverage,
    -- even when unrelated to the selected shard and correctly content-addressed.
    let malformed : ByteArray := ⟨#[0xff]⟩
    let malformedAddr := Address.blake3 malformed
    let malformedBody := Ixon.LazyConstant.ofSlice malformed 0 malformed.size
    let malformedEnv := { env with consts := env.consts.insert malformedAddr malformedBody }
    IO.FS.writeBinFile ixe (← IO.ofExcept (Ixon.serEnv malformedEnv))
    IO.FS.writeBinFile ixes (manifestBytes (shards.push #[malformedAddr]))
    expect (!(← checkSelected (some #[0]) false 2).isOk)
      "selection bypassed parsing an unreferenced malformed body"
    let wrongHashEnv := env.storeConst malformedAddr dependency
    IO.FS.writeBinFile ixe (← IO.ofExcept (Ixon.serEnv wrongHashEnv))
    expect (!(← checkSelected (some #[0]) false 2).isOk)
      "selection bypassed content-address verification of an unselected constant"
    IO.FS.writeBinFile ixe (← IO.ofExcept (Ixon.serEnv (({} : Ixon.Env).storeConst badAddr bad)))
    IO.FS.writeBinFile ixes (manifestBytes #[#[badAddr]])
    let rejected ← IO.ofExcept (← check false 1)
    expect (rejected.constants == 1 && rejected.shards == 1 && rejected.failures == 1)
      "native full-partition execution accepted an invalid constant"
    IO.println "native partition: full/selected executor/claim/peak parity and fail-closed setup passed"
  finally
    IO.FS.removeDirAll dir

end Tests.Cli.NativePartition
