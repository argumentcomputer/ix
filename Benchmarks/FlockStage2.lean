import Ix.Benchmark.Bench
import Ix.Cli.AggregateCmd
import Ix.Cli.FlockLeafCmd
import Ix.TracingTexray

/-!
# Paired Flock Stage 2 leaf benchmark

One fresh process measures either the production P3 shape-0 lift or the
current Flock verifier-core lower bound over the same persisted shard proof.
The Flock arm is intentionally not called a semantic leaf: it does not yet
constrain the `CheckEnv` preimage or publish the uniform aggregate claim.
-/

open Lean (Json)

namespace Benchmarks.FlockStage2

open Ix
open Ix.Cli.AggregateCmd

inductive Backend where
  | p3Lift
  | flockVerifierCore
  deriving BEq, Repr

def Backend.parse : String → Except String Backend
  | "p3-lift" => .ok .p3Lift
  | "flock-verifier-core" => .ok .flockVerifierCore
  | value => .error s!"invalid --backend {value}; expected p3-lift or flock-verifier-core"

def Backend.label : Backend → String
  | .p3Lift => "p3-lift"
  | .flockVerifierCore => "flock-verifier-core"

def argStr (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· != flag) with
  | _ :: value :: _ => some value
  | _ => none

def argNat? (args : List String) (flag : String) : Option Nat :=
  (argStr args flag).bind (·.toNat?)

def hasFlag (args : List String) (flag : String) : Bool :=
  args.contains flag

def commandOutput (cmd : String) (args : Array String := #[]) : IO String := do
  try
    let output ← IO.Process.output { cmd, args }
    if output.exitCode == 0 then pure output.stdout.trimAscii.toString
    else pure "unknown"
  catch _ => pure "unknown"

def cpuLabel : IO String := do
  let output ← commandOutput "lscpu"
  let model? := output.splitOn "\n" |>.find? (·.startsWith "Model name:")
  pure <| model?.map (·.drop 11 |>.trimAscii.toString) |>.getD "unknown"

def claimBytes (claim : Array Aiur.G) : ByteArray :=
  claim.foldl (init := .empty) fun bytes value =>
    bytes ++ value.val.toLEBytes

def writeReport (path : String) (status : String) (metadata : Json)
    (result? : Option Json := none) (error? : Option String := none) : IO Unit := do
  let fields : List (String × Json) :=
    [("schema_version", Lean.toJson (1 : Nat)),
     ("status", Json.str status),
     ("metadata", metadata),
     ("result", result?.getD Json.null)] ++
    match error? with
    | none => []
    | some error => [("error", Json.str error)]
  IO.FS.writeFile path ((Json.mkObj fields).pretty ++ "\n")

structure Fixture where
  ixePath : String
  ixesPath : String
  ixeDigest : Address
  ixesDigest : Address
  shardId : Nat
  subjectCount : Nat
  proofAddress : Address
  proofSource : String
  wrapper : Ixon.Proof
  ownedBlocks : Array Address
  statement : MultiStark.CheckEnvTrees

inductive ProofInput where
  | store (address : Address)
  | file (path : String)

def loadProofInput : ProofInput → IO (Except String (Address × ByteArray × String))
  | .store address => do
      let bytes ← StoreIO.toIO (Store.read address)
      let actual := Address.blake3 bytes
      if actual != address then
        return .error s!"store object {address} hashes to {actual}"
      return .ok (address, bytes, s!"store:{address}")
  | .file path => do
      let bytes ← IO.FS.readBinFile path
      let address := Address.blake3 bytes
      return .ok (address, bytes, s!"file:{path}")

def prepareFixture (ixePath ixesPath : String) (proofInput : ProofInput)
    (shardId : Nat) :
    IO (Except String Fixture) := do
  try
    let ixeBytes ← IO.FS.readBinFile ixePath
    let ixesBytes ← IO.FS.readBinFile ixesPath
    let env ← match Ixon.deEnvAnon ixeBytes with
      | .error error => return .error s!"deserialize {ixePath}: {error}"
      | .ok env => pure env
    let rawView ← match Ix.Cli.CheckCmd.parseIxesManifest ixesBytes with
      | .error error => return .error s!"parse {ixesPath}: {error}"
      | .ok view => pure view
    if !(← Ix.Cli.CheckCmd.shardsCover env rawView.shards) then
      return .error "manifest shards do not cover the environment"
    let (view, counts) ← match rawView.pruneEmpty env with
      | .error error => return .error error
      | .ok result => pure result
    let some denseIdx := view.shardIds.findIdx? (· == shardId)
      | return .error s!"manifest has no retained shard {shardId}"
    let some blocks := view.shards[denseIdx]?
      | return .error s!"manifest has no block list for shard {shardId}"
    let some subjectCount := counts[denseIdx]?
      | return .error s!"manifest has no subject count for shard {shardId}"
    let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks env blocks
    let (expectedClaim, trees) ←
      match IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned with
      | .error error => return .error s!"prepare shard {shardId}: {error}"
      | .ok result => pure result
    let statement ← match MultiStark.CheckEnvTrees.ofClaim expectedClaim trees with
      | .error error => return .error s!"decode shard CheckEnv: {error}"
      | .ok statement => pure statement
    let (proofAddress, wrapperBytes, proofSource) ← match ← loadProofInput proofInput with
      | .error error => return .error error
      | .ok loaded => pure loaded
    let wrapper ← match Ixon.Proof.de wrapperBytes with
      | .error error => return .error s!"proof wrapper {proofAddress}: {error}"
      | .ok wrapper => pure wrapper
    if wrapper.claim != expectedClaim then
      return .error s!"proof wrapper claim does not match manifest shard {shardId}: \
        proof has {wrapper.claim}; manifest reconstructs {expectedClaim}"
    return .ok {
      ixePath
      ixesPath
      ixeDigest := Address.blake3 ixeBytes
      ixesDigest := Address.blake3 ixesBytes
      shardId
      subjectCount
      proofAddress
      proofSource
      wrapper
      ownedBlocks := blocks
      statement
    }
  catch error =>
    return .error s!"prepare fixture: {error}"

/-- Produce a small, parameter-matched raw IxVM proof for the local paired
benchmark gate. This is a fixture-preparation mode, never part of a measured
backend run. The wrapper is written to an explicit file rather than the
content-addressed store because its FRI parameters are benchmark metadata and
are not encoded in the historical `Ixon.Proof` wrapper. -/
def generateProofFile (ixePath ixesPath outputPath : String) (shardId : Nat)
    (fri : Aiur.FriParameters) : IO (Except String Unit) := do
  try
    let ixeBytes ← IO.FS.readBinFile ixePath
    let ixesBytes ← IO.FS.readBinFile ixesPath
    let env ← match Ixon.deEnvAnon ixeBytes with
      | .error error => return .error s!"deserialize {ixePath}: {error}"
      | .ok env => pure env
    let rawView ← match Ix.Cli.CheckCmd.parseIxesManifest ixesBytes with
      | .error error => return .error s!"parse {ixesPath}: {error}"
      | .ok view => pure view
    if !(← Ix.Cli.CheckCmd.shardsCover env rawView.shards) then
      return .error "manifest shards do not cover the environment"
    let (view, _) ← match rawView.pruneEmpty env with
      | .error error => return .error error
      | .ok result => pure result
    let some denseIdx := view.shardIds.findIdx? (· == shardId)
      | return .error s!"manifest has no retained shard {shardId}"
    let some blocks := view.shards[denseIdx]?
      | return .error s!"manifest has no block list for shard {shardId}"
    let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks env blocks
    let (expectedClaim, _) ←
      match IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned with
      | .error error => return .error s!"prepare shard {shardId}: {error}"
      | .ok result => pure result

    let compiled ← match IxVM.ixVM with
      | .error error => return .error s!"IxVM toplevel merge: {error}"
      | .ok top => match top.compile with
        | .error error => return .error s!"IxVM compilation: {error}"
        | .ok compiled => pure compiled
    let some verifyClaimIndex := compiled.getFuncIdx `verify_claim
      | return .error "`verify_claim` is missing from the IxVM system"
    let system := Aiur.AiurSystem.build compiled.bytecode
      Aiur.defaultCommitmentParameters fri
    let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
      | .error error => return .error s!"EnvHandle.fromIxe {ixePath}: {error}"
      | .ok handle => pure handle
    let mut ownedBlob := ByteArray.empty
    for address in owned do
      ownedBlob := ownedBlob ++ address.hash
    let (claimWireBytes, proof) ←
      match system.shardProveWithEnv verifyClaimIndex envHandle ownedBlob with
      | .error error => return .error s!"q={fri.numQueries} shard prove: {error}"
      | .ok (claimBytes, proof, _) => pure (claimBytes, proof)
    let claim ← match Ixon.runGet Ix.Claim.get claimWireBytes with
      | .error error => return .error s!"decode generated claim: {error}"
      | .ok claim => pure claim
    if claim != expectedClaim then
      return .error "generated proof claim differs from the manifest shard"
    let serializedClaim := Ix.Claim.ser claim
    let innerClaim := Aiur.buildClaim verifyClaimIndex
      (IxVM.ClaimHarness.packedDigestKey (Address.blake3 serializedClaim)) #[]
    match system.verify innerClaim proof with
    | .error error => return .error s!"verify generated input proof: {error}"
    | .ok () => pure ()
    let wrapperBytes := Ixon.Proof.ser { claim, proof := proof.toBytes }
    IO.FS.writeBinFile outputPath wrapperBytes
    IO.println s!"generated q={fri.numQueries} shard {shardId} proof: {outputPath}"
    IO.println s!"  wrapper: {wrapperBytes.size} B, {Address.blake3 wrapperBytes}"
    IO.println s!"  compact: {proof.toBytes.size} B, {Address.blake3 proof.toBytes}"
    return .ok ()
  catch error =>
    return .error s!"generate input proof: {error}"

structure IxvmSetup where
  system : Aiur.AiurSystem
  verifyClaimIndex : Nat
  verifyingKey : ByteArray
  innerClaim : Array Aiur.G
  innerClaimBytes : ByteArray

def buildIxvmSetup (fixture : Fixture) (fri : Aiur.FriParameters) :
    IO (Except String IxvmSetup) := do
  let compiled ← match IxVM.ixVM with
    | .error error => return .error s!"IxVM toplevel merge: {error}"
    | .ok top => match top.compile with
      | .error error => return .error s!"IxVM compilation: {error}"
      | .ok compiled => pure compiled
  let system := Aiur.AiurSystem.build compiled.bytecode
    Aiur.defaultCommitmentParameters fri
  let some verifyClaimIndex := compiled.getFuncIdx `verify_claim
    | return .error "`verify_claim` is missing from the IxVM system"
  let claimDigest := Address.blake3 (Ix.Claim.ser fixture.wrapper.claim)
  let innerClaim := Aiur.buildClaim verifyClaimIndex
    (IxVM.ClaimHarness.packedDigestKey claimDigest) #[]
  if innerClaim.size != 10 then
    return .error s!"IxVM claim width is {innerClaim.size}, expected 10"
  pure <| .ok {
    system
    verifyClaimIndex
    verifyingKey := system.vkBytes
    innerClaim
    innerClaimBytes := claimBytes innerClaim
  }

def baseMetadata (fixture : Fixture) (backend : Backend)
    (fri : Aiur.FriParameters) : IO Json := do
  let commit ← commandOutput "git" #["rev-parse", "HEAD"]
  let dirty ← commandOutput "git" #["status", "--short"]
  let timestamp ← commandOutput "date" #["-Is"]
  let host ← commandOutput "hostname"
  let cpu ← cpuLabel
  let memInfo ← try IO.FS.readFile "/proc/meminfo" catch _ => pure ""
  let physicalRam := aggregateMemTotalBytes memInfo |>.getD 0
  pure <| Json.mkObj
    [("commit", Json.str commit),
     ("dirty", Lean.toJson (dirty != "")),
     ("timestamp", Json.str timestamp),
     ("host", Json.str host),
     ("cpu", Json.str cpu),
     ("physical_ram_bytes", Lean.toJson physicalRam),
     ("backend", Json.str backend.label),
     ("ixe", Json.str fixture.ixePath),
     ("ixe_digest", Json.str (toString fixture.ixeDigest)),
     ("ixes", Json.str fixture.ixesPath),
     ("ixes_digest", Json.str (toString fixture.ixesDigest)),
     ("shard_id", Lean.toJson fixture.shardId),
     ("subject_count", Lean.toJson fixture.subjectCount),
     ("proof_address", Json.str (toString fixture.proofAddress)),
     ("proof_source", Json.str fixture.proofSource),
     ("compact_proof_bytes", Lean.toJson fixture.wrapper.proof.size),
     ("compact_proof_digest", Json.str (toString (Address.blake3 fixture.wrapper.proof))),
     ("check_env_digest", Json.str (toString (Address.blake3
       (Ix.Claim.ser fixture.wrapper.claim)))),
     ("fri", Json.mkObj
       [("log_blowup", Lean.toJson Aiur.defaultCommitmentParameters.logBlowup),
        ("cap_height", Lean.toJson Aiur.defaultCommitmentParameters.capHeight),
        ("log_final_poly_len", Lean.toJson fri.logFinalPolyLen),
        ("max_log_arity", Lean.toJson fri.maxLogArity),
        ("num_queries", Lean.toJson fri.numQueries),
        ("commit_pow_bits", Lean.toJson fri.commitProofOfWorkBits),
        ("query_pow_bits", Lean.toJson fri.queryProofOfWorkBits)])]

def exportFixture (dir : String) (fixture : Fixture)
    (fri : Aiur.FriParameters) : IO (Except String Unit) := do
  try
    let ixeBytes ← IO.FS.readBinFile fixture.ixePath
    let ixesBytes ← IO.FS.readBinFile fixture.ixesPath
    let wrapperBytes := Ixon.Proof.ser fixture.wrapper
    if Address.blake3 ixeBytes != fixture.ixeDigest then
      return .error "environment changed after fixture validation"
    if Address.blake3 ixesBytes != fixture.ixesDigest then
      return .error "manifest changed after fixture validation"
    if Address.blake3 wrapperBytes != fixture.proofAddress then
      return .error "canonical proof wrapper differs from its input address"
    let claimBytes := Ix.Claim.ser fixture.wrapper.claim
    let subjectTreeBytes := Ix.AssumptionTree.ser fixture.statement.subjects
    IO.FS.createDirAll dir
    IO.FS.writeBinFile s!"{dir}/environment.ixe" ixeBytes
    IO.FS.writeBinFile s!"{dir}/manifest.ixes" ixesBytes
    IO.FS.writeBinFile s!"{dir}/proof.ixp" wrapperBytes
    IO.FS.writeBinFile s!"{dir}/check-env.claim" claimBytes
    IO.FS.writeBinFile s!"{dir}/subjects.tree" subjectTreeBytes
    let assumptionsJson ← match fixture.statement.assumptions with
      | none => pure Json.null
      | some tree =>
        let bytes := Ix.AssumptionTree.ser tree
        IO.FS.writeBinFile s!"{dir}/assumptions.tree" bytes
        pure <| Json.mkObj
          [("file", Json.str "assumptions.tree"),
           ("bytes", Lean.toJson bytes.size),
           ("root", Json.str (toString tree.root)),
           ("leaves", Lean.toJson tree.leaves.size)]
    let manifest := Json.mkObj
      [("schema_version", Lean.toJson (1 : Nat)),
       ("ixe", Json.mkObj
         [("file", Json.str "environment.ixe"),
          ("bytes", Lean.toJson ixeBytes.size),
          ("digest", Json.str (toString fixture.ixeDigest))]),
       ("ixes", Json.mkObj
         [("file", Json.str "manifest.ixes"),
          ("bytes", Lean.toJson ixesBytes.size),
          ("digest", Json.str (toString fixture.ixesDigest))]),
       ("shard_id", Lean.toJson fixture.shardId),
       ("subject_count", Lean.toJson fixture.subjectCount),
       ("owned_blocks", Json.arr <| fixture.ownedBlocks.map fun address =>
          Json.str (toString address)),
       ("proof", Json.mkObj
         [("file", Json.str "proof.ixp"),
          ("address", Json.str (toString fixture.proofAddress)),
          ("wrapper_bytes", Lean.toJson wrapperBytes.size),
          ("compact_proof_bytes", Lean.toJson fixture.wrapper.proof.size),
          ("compact_proof_digest", Json.str (toString
            (Address.blake3 fixture.wrapper.proof)))]),
       ("check_env", Json.mkObj
         [("claim_file", Json.str "check-env.claim"),
          ("claim_bytes", Lean.toJson claimBytes.size),
          ("claim_digest", Json.str (toString (Address.blake3 claimBytes))),
          ("claim", Json.str (toString fixture.wrapper.claim)),
          ("subjects", Json.mkObj
            [("file", Json.str "subjects.tree"),
             ("bytes", Lean.toJson subjectTreeBytes.size),
             ("root", Json.str (toString fixture.statement.subjects.root)),
             ("leaves", Lean.toJson fixture.statement.subjects.leaves.size)]),
          ("assumptions", assumptionsJson)]),
       ("fri", Json.mkObj
         [("log_blowup", Lean.toJson Aiur.defaultCommitmentParameters.logBlowup),
          ("cap_height", Lean.toJson Aiur.defaultCommitmentParameters.capHeight),
          ("log_final_poly_len", Lean.toJson fri.logFinalPolyLen),
          ("max_log_arity", Lean.toJson fri.maxLogArity),
          ("num_queries", Lean.toJson fri.numQueries),
          ("commit_pow_bits", Lean.toJson fri.commitProofOfWorkBits),
          ("query_pow_bits", Lean.toJson fri.queryProofOfWorkBits)])]
    IO.FS.writeFile s!"{dir}/fixture.json" (manifest.pretty ++ "\n")
    return .ok ()
  catch error =>
    return .error s!"export fixture: {error}"

def addSetupMetadata (metadata : Json) (setup : IxvmSetup) : Json :=
  match metadata with
  | .obj fields => .obj <| fields
      |>.insert "ixvm_vk_digest" (Json.str (toString (Address.blake3 setup.verifyingKey)))
      |>.insert "verify_claim_index" (Lean.toJson setup.verifyClaimIndex)
      |>.insert "p3_claim_digest" (Json.str (toString
        (Address.blake3 setup.innerClaimBytes)))
  | other => other

def corruptLast (bytes : ByteArray) : Option ByteArray := do
  if bytes.size = 0 then
    none
  let last := bytes.size - 1
  let byte ← bytes[last]?
  pure <| bytes.extract 0 last |>.push (byte ^^^ 1)

def runP3Lift (fixture : Fixture) (setup : IxvmSetup)
    (fri : Aiur.FriParameters)
    (programSetupNs : Nat) : IO (Except String Json) := do
  let p3SetupStarted ← IO.monoNanosNow
  let aggrCompiled ← match Aggr.ixAggr with
    | .error error => return .error s!"ix_aggr toplevel merge: {error}"
    | .ok top => match top.compile with
      | .error error => return .error s!"ix_aggr compilation: {error}"
      | .ok compiled => pure compiled
  let some aggrIdx := aggrCompiled.getFuncIdx `ix_aggr
    | return .error "`ix_aggr` is missing from the recursion system"
  let recursionParameters : MultiStark.RecursionParameters := {
    commitment := Aiur.defaultCommitmentParameters
    fri
  }
  let aggrSystem := MultiStark.buildRecursionSystem aggrCompiled.bytecode
    recursionParameters
  let aggrVk := aggrSystem.vkBytes
  let allowed := Aggr.allowedBlob setup.verifyingKey setup.verifyClaimIndex
    aggrVk aggrIdx
  let claimBytes := Ix.Claim.ser fixture.wrapper.claim
  let expectedOuterClaim := aggregateOuterClaim allowed aggrIdx fixture.wrapper.claim
  let totalProgramSetupNs := programSetupNs +
    ((← IO.monoNanosNow) - p3SetupStarted)

  TracingTexray.resetPeakTreeRss
  let totalStarted ← IO.monoNanosNow

  let phaseStarted ← IO.monoNanosNow
  let innerProof ← match Aiur.Proof.ofBytesChecked fixture.wrapper.proof with
    | .error error => return .error s!"decode input proof: {error}"
    | .ok proof => pure proof
  let decodeNs := (← IO.monoNanosNow) - phaseStarted

  let phaseStarted ← IO.monoNanosNow
  match setup.system.verify setup.innerClaim innerProof with
  | .error error => return .error s!"verify input proof: {error}"
  | .ok () => pure ()
  let inputVerifyNs := (← IO.monoNanosNow) - phaseStarted

  let phaseStarted ← IO.monoNanosNow
  let innerProofAdvice ← match setup.system.proofToAdviceBytes
      setup.innerClaim innerProof with
    | .error error => return .error s!"expand input proof advice: {error}"
    | .ok bytes => pure bytes
  let adviceNs := (← IO.monoNanosNow) - phaseStarted

  let pubInput := Aggr.pubInput allowed claimBytes
  let innerClaimsBytes := MultiStark.serializeClaims #[setup.innerClaim]
  let phaseStarted ← IO.monoNanosNow
  let (outerClaim, proof) ← match aggrSystem.proveIxAggr aggrIdx pubInput 0
      innerProofAdvice ByteArray.empty setup.verifyingKey aggrVk
      innerClaimsBytes ByteArray.empty claimBytes allowed
      (Aggr.preimagesBlob #[]) (Aggr.treesBlob #[]) (Aggr.pathsBlob #[]) with
    | .error error => return .error s!"P3 shape-0 proving: {error}"
    | .ok result => pure result
  let proveNs := (← IO.monoNanosNow) - phaseStarted
  if outerClaim != expectedOuterClaim then
    return .error "P3 shape-0 lift produced an unexpected outer claim"

  let phaseStarted ← IO.monoNanosNow
  match aggrSystem.verify outerClaim proof with
  | .error error => return .error s!"verify P3 lift: {error}"
  | .ok () => pure ()
  let validVerifyNs := (← IO.monoNanosNow) - phaseStarted

  let phaseStarted ← IO.monoNanosNow
  let proofBytes := proof.toBytes
  let serializeNs := (← IO.monoNanosNow) - phaseStarted
  let inputToVerifiedOutputNs := (← IO.monoNanosNow) - totalStarted
  let peakRss ← TracingTexray.peakTreeRssBytes

  let some corruptedBytes := corruptLast proofBytes
    | return .error "P3 shape-0 proof is empty"
  let phaseStarted ← IO.monoNanosNow
  let corruptedRejected ← match Aiur.Proof.ofBytesChecked corruptedBytes with
    | .error _ => pure true
    | .ok corrupted => pure <| match aggrSystem.verify outerClaim corrupted with
      | .error _ => true
      | .ok () => false
  let corruptRejectNs := (← IO.monoNanosNow) - phaseStarted
  if !corruptedRejected then
    return .error "corrupted P3 shape-0 proof was accepted"

  let result := Json.mkObj
    [("backend", Json.str "p3-lift"),
     ("semantic_scope", Json.str "uniform-check-env-shape-0"),
     ("cache_scope", Json.str "static-recursion-system"),
     ("identity", Json.mkObj
       [("ixvm_vk_digest", Json.str (toString (Address.blake3 setup.verifyingKey))),
        ("recursion_vk_digest", Json.str (toString (Address.blake3 aggrVk))),
        ("allowed_digest", Json.str (toString (Address.blake3 allowed))),
        ("output_claim_digest", Json.str (toString (Address.blake3 claimBytes)))]),
     ("transport", Json.mkObj
       [("compact_proof_bytes", Lean.toJson fixture.wrapper.proof.size),
        ("advice_bytes", Lean.toJson innerProofAdvice.size)]),
     ("timings_ns", Json.mkObj
       [("program_setup", Lean.toJson totalProgramSetupNs),
        ("input_decode", Lean.toJson decodeNs),
        ("input_verify", Lean.toJson inputVerifyNs),
        ("advice_expand", Lean.toJson adviceNs),
        ("prove", Lean.toJson proveNs),
        ("valid_verify", Lean.toJson validVerifyNs),
        ("serialize", Lean.toJson serializeNs),
        ("corrupt_reject", Lean.toJson corruptRejectNs),
        ("input_to_verified_output", Lean.toJson inputToVerifiedOutputNs)]),
     ("resources", Json.mkObj
       [("peak_tree_rss_bytes", Lean.toJson peakRss)]),
     ("proof", Json.mkObj
       [("bytes", Lean.toJson proofBytes.size),
        ("digest", Json.str (toString (Address.blake3 proofBytes))),
        ("valid_verification", Lean.toJson true),
        ("corrupted_rejected", Lean.toJson true)])]
  pure (.ok result)

def runFlockVerifierCore (fixture : Fixture) (setup : IxvmSetup)
    (fri : Aiur.FriParameters)
    (programSetupNs : Nat) : IO (Except String Json) := do
  TracingTexray.resetPeakTreeRss
  let started ← IO.monoNanosNow
  let reportBytes ← match Aiur.flockStage2IxvmLeafBenchmark
      setup.verifyingKey setup.innerClaimBytes fixture.wrapper.proof
      fri setup.verifyClaimIndex with
    | .error error => return .error error
    | .ok bytes => pure bytes
  let harnessWallNs := (← IO.monoNanosNow) - started
  let peakRss ← TracingTexray.peakTreeRssBytes
  let reportString ← match String.fromUTF8? reportBytes with
    | none => return .error "Flock benchmark returned non-UTF-8 JSON"
    | some string => pure string
  let backendReport ← match Json.parse reportString with
    | .error error => return .error s!"parse Flock benchmark JSON: {error}"
    | .ok json => pure json
  pure <| .ok <| Json.mkObj
    [("backend", Json.str "flock-verifier-core"),
     ("semantic_scope", Json.str "p3-verifier-only"),
     ("cache_scope", Json.str "same-witness-lower-bound"),
     ("program_setup_ns", Lean.toJson programSetupNs),
     ("harness_wall_ns", Lean.toJson harnessWallNs),
     ("peak_tree_rss_bytes", Lean.toJson peakRss),
     ("backend_report", backendReport)]

def usage : String :=
  "usage: bench-flock-stage2 --ixe ENV.ixe --ixes MANIFEST.ixes --shard N " ++
  "(--proof ADDRESS | --proof-file WRAPPER.ixp) " ++
  "--backend p3-lift|flock-verifier-core --json RESULT.json " ++
  "[--queries N] [--export-fixture DIR] [--metadata-only|--export-only]\n" ++
  "       bench-flock-stage2 --ixe ENV.ixe --ixes MANIFEST.ixes --shard N " ++
  "--queries N --generate-proof WRAPPER.ixp"

def main (args : List String) : IO UInt32 := do
  if hasFlag args "--help" then
    IO.println usage
    return 0
  let some ixePath := argStr args "--ixe" | do
    IO.eprintln "error: --ixe is required"; IO.eprintln usage; return 2
  let some ixesPath := argStr args "--ixes" | do
    IO.eprintln "error: --ixes is required"; IO.eprintln usage; return 2
  let some shardId := argNat? args "--shard" | do
    IO.eprintln "error: --shard is required"; IO.eprintln usage; return 2
  let queries := (argNat? args "--queries").getD
    Aiur.defaultFriParameters.numQueries
  if queries == 0 then
    IO.eprintln "error: --queries must be at least one"
    return 2
  let fri : Aiur.FriParameters := {
    Aiur.defaultFriParameters with numQueries := queries
  }
  if let some outputPath := argStr args "--generate-proof" then
    match ← generateProofFile ixePath ixesPath outputPath shardId fri with
    | .error error => IO.eprintln s!"error: {error}"; return 1
    | .ok () => return 0
  let proofInput ← match argStr args "--proof", argStr args "--proof-file" with
    | some proofHex, none => match Address.fromString proofHex with
      | some address => pure (.store address)
      | none =>
        IO.eprintln "error: --proof must be a 64-character store address"
        return 2
    | none, some path => pure (.file path)
    | none, none =>
      IO.eprintln "error: exactly one of --proof or --proof-file is required"
      IO.eprintln usage
      return 2
    | some _, some _ =>
      IO.eprintln "error: --proof and --proof-file are mutually exclusive"
      return 2
  let some backendValue := argStr args "--backend" | do
    IO.eprintln "error: --backend is required"; IO.eprintln usage; return 2
  let backend ← match Backend.parse backendValue with
    | .error error => IO.eprintln s!"error: {error}"; return 2
    | .ok backend => pure backend
  let some jsonPath := argStr args "--json" | do
    IO.eprintln "error: --json is required"; IO.eprintln usage; return 2
  let fixture ← match ← prepareFixture ixePath ixesPath proofInput shardId with
    | .error error =>
      IO.eprintln s!"error: {error}"
      return 1
    | .ok fixture => pure fixture
  let metadata0 ← baseMetadata fixture backend fri
  writeReport jsonPath "preparing" metadata0
  if let some exportDir := argStr args "--export-fixture" then
    match ← exportFixture exportDir fixture fri with
    | .error error =>
      writeReport jsonPath "error" metadata0 (error? := some error)
      IO.eprintln s!"error: {error}"
      return 1
    | .ok () => IO.println s!"fixture exported to {exportDir}"
  if hasFlag args "--export-only" then
    writeReport jsonPath "export-only" metadata0
    return 0
  if hasFlag args "--metadata-only" then
    writeReport jsonPath "metadata-only" metadata0
    IO.println s!"fixture metadata written to {jsonPath}"
    return 0

  TracingTexray.startSampler 25
  TracingTexray.resetPeakTreeRss
  let setupStarted ← IO.monoNanosNow
  let setup ← match ← buildIxvmSetup fixture fri with
    | .error error =>
      writeReport jsonPath "error" metadata0 (error? := some error)
      IO.eprintln s!"error: {error}"
      return 1
    | .ok setup => pure setup
  let programSetupNs := (← IO.monoNanosNow) - setupStarted
  let metadata := addSetupMetadata metadata0 setup
  writeReport jsonPath "running" metadata
  let result ← match backend with
    | .p3Lift => runP3Lift fixture setup fri programSetupNs
    | .flockVerifierCore => runFlockVerifierCore fixture setup fri programSetupNs
  match result with
  | .error error =>
    writeReport jsonPath "error" metadata (error? := some error)
    IO.eprintln s!"error: {error}"
    return 1
  | .ok result =>
    writeReport jsonPath "ok" metadata (some result)
    IO.println s!"ok: {backend.label} benchmark written to {jsonPath}"
    return 0

end Benchmarks.FlockStage2

def main (args : List String) : IO UInt32 :=
  Benchmarks.FlockStage2.main args
