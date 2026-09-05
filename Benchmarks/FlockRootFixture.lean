import Ix.Cli.FlockRootCmd
import Ix.Aiur.Statistics
import Ix.Benchmark.Bench
import Ix.TracingTexray

/-!
A small, genuine production-protocol `ix_aggr` root for Stage 3 measurements.
The environment has one well-formed axiom declaration, not a toy verifier
circuit. Both systems use the CLI's canonical parameters. No store or cache
is accessed. Outputs go into a newly created directory, never an existing one.

The default run proves the tiny IxVM child and only EXECUTES its aggregate
wrap. `--prove` also proves, verifies, and persists the aggregate. Require a
finite Linux address-space limit of at most 64 GiB in either mode: recursive
prover RAM estimates were calibrated on an older protocol, so they are not a
safe absolute budget for this measurement. Allocation failure can terminate
the subprocess; an incomplete directory is not a completed fixture.
`--verify DIRECTORY` checks a completed fixture in a fresh process without
proving, modifying files, or requiring the generation-only memory cap.
`--min-opening-width` explicitly selects the experimental aggregate lookup
packing profile in any mode. The default profile/keys remain unchanged.
`--count DIRECTORY` verifies the fixture, then counts Stage 3 with a one-byte
witness admission limit, so it cannot compile wiring or invoke a prover.
-/

open Lean (Json toJson)

namespace Benchmarks.FlockRootFixture

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| IO.userError message

private def timed (label : String) (action : Unit → Except String α) : IO (α × Nat) := do
  IO.eprintln s!"[flock-root-fixture] {label}"
  let start ← IO.monoNanosNow
  let result ← IO.ofExcept (← blackBoxIO action ())
  return (result, ((← IO.monoNanosNow) - start) / 1000)

private def memoryCap : IO Nat := do
  let limits ← IO.FS.readFile "/proc/self/limits"
  let some line := (limits.splitOn "\n").find? (·.startsWith "Max address space")
    | throw <| IO.userError "could not read the process address-space limit"
  let fields := line.splitOn " " |>.filter (!·.isEmpty)
  let cap := (fields[3]?).bind String.toNat?
  let some cap := cap
    | throw <| IO.userError "set a finite process memory cap: ulimit -v 67108864 (64 GiB)"
  require (cap > 0 && cap ≤ 64 * 1024 ^ 3)
    "the process address-space limit must be positive and at most 64 GiB"
  return cap

private def singletonEnv : Ixon.Env × Address :=
  let constant : Ixon.Constant :=
    ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ .zero]⟩
  let address := Address.blake3 (Ixon.serConstant constant)
  (({} : Ixon.Env).storeConst address constant, address)

private def compile (source : Except Aiur.Global Aiur.Source.Toplevel) :
    Except String Aiur.CompiledToplevel := do
  let top ← source.mapError toString
  top.compile.mapError toString

private def writeBytes (directory : System.FilePath) (name : String)
    (bytes : ByteArray) : IO Json := do
  IO.FS.writeBinFile (directory / name) bytes
  return Json.mkObj [("file", toJson name), ("bytes", toJson bytes.size),
    ("blake3", toJson (toString (Address.blake3 bytes)))]

private def circuitRow (stats : Aiur.CircuitStats) : Json :=
  Json.mkObj [("name", toJson stats.name), ("height", toJson stats.height),
    ("committed_width", toJson stats.width), ("cache_hits", toJson stats.cacheHits)]

private def lookupPolicy (minOpeningWidth : Bool) : String :=
  if minOpeningWidth then "min-opening-width-v1" else "legacy"

private def aggregateSystem (compiled : Aiur.CompiledToplevel)
    (minOpeningWidth : Bool) : Aiur.AiurSystem :=
  let recursion := MultiStark.defaultRecursionParameters
  if minOpeningWidth then
    Aiur.AiurSystem.buildMinOpeningWidth compiled.bytecode recursion.commitment recursion.fri
  else MultiStark.buildRecursionSystem compiled.bytecode recursion

/-- Fresh-process verification is deliberately cheap enough for CI. Validate
the persisted transport and the exact singleton subject, not just a proof of
an arbitrary self-reported bundled claim. -/
private def verify (directory : System.FilePath) (minOpeningWidth count : Bool) : IO Unit := do
  if count then discard memoryCap
  let manifestBytes ← Ix.Cli.FlockRootCmd.readBounded (directory / "fixture.json") (1024 ^ 2)
  let some manifestText := String.fromUTF8? manifestBytes
    | throw <| IO.userError "fixture manifest is not UTF-8"
  let manifest ← IO.ofExcept (Json.parse manifestText)
  require ((← IO.ofExcept (manifest.getObjValAs? String "schema")) == "ix.flock-stage3.root-fixture")
    "unexpected fixture schema"
  require ((← IO.ofExcept (manifest.getObjValAs? Nat "version")) == 1) "unexpected fixture version"
  require (← IO.ofExcept (manifest.getObjValAs? Bool "aggregate_proven")) "fixture is execution-only"
  let policy ← match manifest.getObjVal? "aggregate_lookup_policy" with
    | .ok json => IO.ofExcept (Lean.fromJson? json : Except String String)
    | .error _ => pure "legacy"
  require (policy == lookupPolicy minOpeningWidth)
    "fixture lookup policy differs from the explicitly requested profile"
  let inputs ← IO.ofExcept (manifest.getObjValAs? (Array Json) "inputs")
  let records := inputs.push (← IO.ofExcept (manifest.getObjVal? "child"))
    |>.push (← IO.ofExcept (manifest.getObjVal? "root"))
  let names := #["environment.ixe", "check-env.claim", "subjects.tree", "ixvm.vk",
    "aggr.vk", "outer-claim.bin", "ixvm.ixon-proof", "root.ixon-proof"]
  require (records.size == names.size) "unexpected fixture file count"
  let mut files : Std.HashMap String ByteArray := {}
  for (record, name) in records.zip names do
    -- Only literal filenames may select a read; never follow a manifest path.
    require ((← IO.ofExcept (record.getObjValAs? String "file")) == name) "unexpected fixture filename"
    let bytes ← Ix.Cli.FlockRootCmd.readBounded (directory / name) (64 * 1024 ^ 2)
    require ((← IO.ofExcept (record.getObjValAs? Nat "bytes")) == bytes.size) s!"{name}: size changed"
    require ((← IO.ofExcept (record.getObjValAs? String "blake3")) == toString (Address.blake3 bytes))
      s!"{name}: digest changed"
    files := files.insert name bytes
  -- Verify the same bounded, digest-checked bytes; do not re-open mutable
  -- paths between transport validation and native proof verification.
  let read := fun name => files[name]!
  let (env, owned) := singletonEnv
  require (read "environment.ixe" == (← IO.ofExcept (Ixon.serEnv env)))
    "fixture environment is not the expected singleton"
  let (claim, trees) ← IO.ofExcept (IxVM.ClaimHarness.shardCheckEnvClaimTrees env #[owned])
  let statement ← IO.ofExcept (MultiStark.CheckEnvTrees.ofClaim claim trees)
  require (read "subjects.tree" == statement.subjects.ser)
    "fixture subject tree changed"
  let claimBytes := Ix.Claim.ser claim
  require (read "check-env.claim" == claimBytes) "fixture claim changed"
  let (ixvmSystem, compiled) ← IO.ofExcept (← Ix.Cli.VerifyCmd.buildBackend)
  let some verifyIdx := compiled.getFuncIdx `verify_claim
    | throw <| IO.userError "missing verify_claim entrypoint"
  require (read "ixvm.vk" == ixvmSystem.vkBytes) "IxVM key changed"
  let aggrCompiled ← IO.ofExcept (compile Aggr.ixAggr)
  let some aggrIdx := aggrCompiled.getFuncIdx `ix_aggr
    | throw <| IO.userError "missing ix_aggr entrypoint"
  let aggrSystem := aggregateSystem aggrCompiled minOpeningWidth
  require (read "aggr.vk" == aggrSystem.vkBytes) "aggregate key changed"
  let allowed := Aggr.allowedBlob ixvmSystem.vkBytes verifyIdx aggrSystem.vkBytes aggrIdx
  let outerClaim := Ix.Cli.AggregateCmd.aggregateOuterClaim allowed aggrIdx claim
  require (read "outer-claim.bin" ==
    Ix.Cli.FlockRootCmd.outerClaimBytes outerClaim) "aggregate outer claim changed"
  let innerClaim := Aiur.buildClaim verifyIdx
    (IxVM.ClaimHarness.packedDigestKey (Address.blake3 claimBytes)) #[]
  for (name, system, expected) in
      [("ixvm.ixon-proof", ixvmSystem, innerClaim), ("root.ixon-proof", aggrSystem, outerClaim)] do
    let wrapper ← IO.ofExcept (Ixon.Proof.de (read name))
    require (wrapper.claim == claim) s!"{name}: bundled claim changed"
    let proof ← IO.ofExcept (Aiur.Proof.ofBytesChecked wrapper.proof)
    IO.ofExcept (system.verify expected proof)
  let verified := "Flock root fixture digests, subjects, keys, and native proofs verified"
  if count then IO.eprintln verified else IO.println verified
  if count then
    let wrapper ← IO.ofExcept (Ixon.Proof.de (read "root.ixon-proof"))
    let outcome : Except String String ← try
      pure (.ok (← Aiur.flockStage3AggregateRoot
        aggrSystem.vkBytes (Ix.Cli.FlockRootCmd.outerClaimBytes outerClaim)
        wrapper.proof MultiStark.defaultRecursionParameters.fri "preflight" "" ""
        "{\"max_table_capacity\":4294967296,\"max_union_witness_bytes\":1}"))
    catch error => pure (.error error.toString)
    match outcome with
    | .ok _ => throw <| IO.userError "count-only mode unexpectedly passed one-byte witness admission"
    | .error message =>
      require (message.startsWith "Stage 3 padded union witness requires ") message
      IO.println <| (Json.mkObj [("schema", toJson "ix.flock-stage3.fixture-count"),
        ("version", toJson (1 : Nat)), ("aggregate_lookup_policy", toJson policy),
        ("compiled", toJson false), ("admission_error", toJson message)]).compress

private def generate (directory : System.FilePath) (prove minOpeningWidth : Bool) : IO Unit := do
  let cap ← memoryCap
  -- createDir is exclusive: an existing directory, including a symlink,
  -- fails before any output is written. Never create the user's store.
  IO.FS.createDir directory
  TracingTexray.startSampler 10
  let (env, owned) := singletonEnv
  let envBytes ← IO.ofExcept (Ixon.serEnv env)
  let handle ← IO.ofExcept (Aiur.EnvHandle.fromBytes envBytes)
  let (claim, trees) ← IO.ofExcept (IxVM.ClaimHarness.shardCheckEnvClaimTrees env #[owned])
  IO.ofExcept (Ix.Cli.FlockRootCmd.validateBundledClaim claim)
  let statement ← IO.ofExcept (MultiStark.CheckEnvTrees.ofClaim claim trees)
  let audited ← IO.ofExcept <| Ix.Cli.VerifyCmd.auditAggregateConstants env
    (Ix.Cli.AggregateCmd.toAggrCheckEnvTrees statement)
  require (audited == 1) "fixture must certify exactly one environment constant"
  let claimBytes := Ix.Claim.ser claim
  let environmentFile ← writeBytes directory "environment.ixe" envBytes
  let claimFile ← writeBytes directory "check-env.claim" claimBytes
  let subjectsFile ← writeBytes directory "subjects.tree" statement.subjects.ser
  let (ixvmCompiled, ixvmCompileUs) ← timed "compile IxVM" fun _ => compile IxVM.ixVM
  let (aggrCompiled, aggrCompileUs) ← timed "compile ix_aggr" fun _ => compile Aggr.ixAggr
  let some verifyIdx := ixvmCompiled.getFuncIdx `verify_claim
    | throw <| IO.userError "missing verify_claim entrypoint"
  let some aggrIdx := aggrCompiled.getFuncIdx `ix_aggr
    | throw <| IO.userError "missing ix_aggr entrypoint"
  let recursion := MultiStark.defaultRecursionParameters
  let ixvmSystem := Aiur.AiurSystem.build ixvmCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let aggrSystem := aggregateSystem aggrCompiled minOpeningWidth
  let ixvmVk := ixvmSystem.vkBytes
  let aggrVk := aggrSystem.vkBytes
  let allowed := Aggr.allowedBlob ixvmVk verifyIdx aggrVk aggrIdx
  let ixvmVkFile ← writeBytes directory "ixvm.vk" ixvmVk
  let aggrVkFile ← writeBytes directory "aggr.vk" aggrVk
  let innerClaim := Aiur.buildClaim verifyIdx
    (IxVM.ClaimHarness.packedDigestKey (Address.blake3 claimBytes)) #[]
  TracingTexray.resetPeakTreeRss
  let (inner, ixvmProveUs) ← timed "prove IxVM child (2 GiB model budget)" fun _ =>
    ixvmSystem.shardProveWithEnv verifyIdx handle owned.hash (2 * 1024 ^ 3)
  require (inner.claimBytes == claimBytes) "native shard claim differs from host reconstruction"
  let some innerProof := inner.proof
    | throw <| IO.userError s!"IxVM child exceeds budget: predicted {inner.peakBytes} bytes"
  let ixvmPeak ← TracingTexray.peakTreeRssBytes
  let (_, ixvmVerifyUs) ← timed "verify IxVM child" fun _ =>
    ixvmSystem.verify innerClaim innerProof
  let childFile ← writeBytes directory "ixvm.ixon-proof"
    (Ixon.Proof.ser { claim, proof := innerProof.toBytes })
  let advice ← IO.ofExcept (ixvmSystem.proofToAdviceBytes innerClaim innerProof)
  let childClaims := MultiStark.serializeClaims #[innerClaim]
  let pubInput := Aggr.pubInput allowed claimBytes
  let outerClaim := Ix.Cli.AggregateCmd.aggregateOuterClaim allowed aggrIdx claim
  let outerFile ← writeBytes directory "outer-claim.bin"
    (Ix.Cli.FlockRootCmd.outerClaimBytes outerClaim)
  TracingTexray.resetPeakTreeRss
  let ((output, queries), aggrExecuteUs) ← timed "execute ix_aggr wrap (no aggregate proof yet)" fun _ =>
    aggrCompiled.bytecode.executeIxAggr aggrIdx pubInput 0
      advice ByteArray.empty ixvmVk aggrVk childClaims ByteArray.empty
      claimBytes allowed (Aggr.preimagesBlob #[]) (Aggr.treesBlob #[]) (Aggr.pathsBlob #[])
  require (Aiur.buildClaim aggrIdx pubInput output == outerClaim)
    "aggregate execution produced an unexpected outer claim"
  let aggrExecutePeak ← TracingTexray.peakTreeRssBytes
  let stats := Aiur.computeStats aggrCompiled queries aggrSystem.circuitShapes
    recursion.commitment.logBlowup
  let base := [("schema", toJson "ix.flock-stage3.root-fixture"), ("version", toJson (1 : Nat)),
    ("lean_toolchain", toJson Lean.versionString),
    ("description", toJson "single well-formed axiom declaration; production ix_aggr shape-0 wrap"),
    ("aggregate_lookup_policy", toJson (lookupPolicy minOpeningWidth)),
    ("active_committed_width", toJson <| stats.circuits.foldl
      (fun total circuit => total + if circuit.height == 0 then 0 else circuit.width) 0),
    ("subject", toJson (toString owned)), ("bundled_claim", toJson (toString claim)),
    ("address_space_limit_bytes", toJson cap),
    ("fri", Json.mkObj [("num_queries", toJson recursion.fri.numQueries),
      ("query_pow_bits", toJson recursion.fri.queryProofOfWorkBits),
      ("commit_pow_bits", toJson recursion.fri.commitProofOfWorkBits),
      ("max_log_arity", toJson recursion.fri.maxLogArity),
      ("log_final_poly_len", toJson recursion.fri.logFinalPolyLen),
      ("log_blowup", toJson recursion.commitment.logBlowup)]),
    ("inputs", Json.arr #[environmentFile, claimFile, subjectsFile, ixvmVkFile, aggrVkFile, outerFile]),
    ("child", childFile), ("ixvm_compile_us", toJson ixvmCompileUs),
    ("aggr_compile_us", toJson aggrCompileUs), ("ixvm_prove_us", toJson ixvmProveUs),
    ("ixvm_verify_us", toJson ixvmVerifyUs), ("ixvm_predicted_peak_bytes", toJson inner.peakBytes),
    ("ixvm_sampled_peak_rss_bytes", toJson ixvmPeak),
    ("aggr_execute_us", toJson aggrExecuteUs),
    ("aggr_execute_sampled_peak_rss_bytes", toJson aggrExecutePeak),
    ("aggregate_circuits", Json.arr (stats.circuits.map circuitRow))]
  IO.FS.writeFile (directory / "execution.json")
    ((Json.mkObj (base ++ [("aggregate_proven", toJson false)])).pretty ++ "\n")
  unless prove do
    IO.println s!"Aggregate execution passed; measurements: {directory / "execution.json"}"
    return
  TracingTexray.resetPeakTreeRss
  let ((provedClaim, proof), aggrProveUs) ← timed "prove ix_aggr wrap (process memory cap enforced)" fun _ =>
    aggrSystem.proveIxAggr aggrIdx pubInput 0
      advice ByteArray.empty ixvmVk aggrVk childClaims ByteArray.empty
      claimBytes allowed (Aggr.preimagesBlob #[]) (Aggr.treesBlob #[]) (Aggr.pathsBlob #[])
  let aggrProvePeak ← TracingTexray.peakTreeRssBytes
  require (provedClaim == outerClaim) "aggregate proof produced an unexpected outer claim"
  let (_, aggrVerifyUs) ← timed "verify ix_aggr wrap" fun _ => aggrSystem.verify outerClaim proof
  let rootFile ← writeBytes directory "root.ixon-proof"
    (Ixon.Proof.ser { claim, proof := proof.toBytes })
  -- Re-read the persisted transport, not just the in-memory proof handle.
  let wrapper ← IO.ofExcept (Ixon.Proof.de (← IO.FS.readBinFile (directory / "root.ixon-proof")))
  require (wrapper.claim == claim) "persisted aggregate claim changed"
  let rereadProof ← IO.ofExcept (Aiur.Proof.ofBytesChecked wrapper.proof)
  IO.ofExcept (aggrSystem.verify outerClaim rereadProof)
  IO.FS.writeFile (directory / "fixture.json")
    ((Json.mkObj (base ++ [("aggregate_proven", toJson true), ("root", rootFile),
      ("aggr_prove_us", toJson aggrProveUs), ("aggr_verify_us", toJson aggrVerifyUs),
      ("aggr_prove_sampled_peak_rss_bytes", toJson aggrProvePeak)])).pretty ++ "\n")
  IO.println s!"Verified current-protocol aggregate: {directory / "root.ixon-proof"}"

end Benchmarks.FlockRootFixture

def main (args : List String) : IO UInt32 := do
  try
    let minOpeningWidth := args.contains "--min-opening-width"
    let args := args.erase "--min-opening-width"
    if let ["--verify", directory] := args then
      Benchmarks.FlockRootFixture.verify directory minOpeningWidth false
      return 0
    if let ["--count", directory] := args then
      Benchmarks.FlockRootFixture.verify directory minOpeningWidth true
      return 0
    let (directory, prove) ← match args with
      | ["--output", directory] => pure (directory, false)
      | ["--output", directory, "--prove"] => pure (directory, true)
      | _ => throw (IO.userError "usage: bench-flock-root-fixture [--min-opening-width] (--output NEW_DIRECTORY [--prove] | --verify DIRECTORY | --count DIRECTORY)")
    Benchmarks.FlockRootFixture.generate directory prove minOpeningWidth
    return 0
  catch error =>
    IO.eprintln s!"flock-root-fixture: {error}"
    return 1
