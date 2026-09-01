import Ix.Cli.AggregateCmd
import Ix.Benchmark.Bench
import Ix.TracingTexray

/-!
# Four-shard converged aggregation policy benchmark

This executable is the M1-f handoff harness. It consumes four persisted IxVM
shard proofs from a validated manifest, derives the selected subtree from the
manifest aggregation tree, and measures either production wrap-first or
non-default direct joins through the single `ix_aggr` entrypoint.

Base shard proving is deliberately out of scope. Every input and recursive
output is natively verified, every recursive output is persisted as an ordinary
`Ixon.Proof` wrapper, aggregate cache access is disabled, and a structured JSON
report is rewritten after every completed slot.
-/

open Lean (Json)

namespace Benchmarks.AggregatePolicy

open Ix
open Ix.Cli.AggregateCmd

abbrev AggregationTree := Ix.Cli.CheckCmd.AggregationTree
abbrev FoldOp := Ix.Cli.CheckCmd.AggregationTree.FoldOp

inductive Policy where
  | wrapFirst
  | direct
  deriving BEq, Repr

def Policy.parse : String → Except String Policy
  | "wrap-first" => .ok .wrapFirst
  | "direct" => .ok .direct
  | value => .error s!"invalid --policy {value}; expected wrap-first or direct"

def Policy.label : Policy → String
  | .wrapFirst => "wrap-first"
  | .direct => "direct"

def Policy.directJoins : Policy → Bool
  | .wrapFirst => false
  | .direct => true

def argStr (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· != flag) with
  | _ :: value :: _ => some value
  | _ => none

def argNat? (args : List String) (flag : String) : Option Nat :=
  (argStr args flag).bind (·.toNat?)

def hasFlag (args : List String) (flag : String) : Bool :=
  args.contains flag

def jsonRound (digits : Nat) (value : Float) : Json :=
  let scale := (10.0 : Float) ^ digits.toFloat
  let scaled := value * scale
  let mantissa : _root_.Int :=
    if scaled < 0 then -_root_.Int.ofNat (-scaled).round.toUInt64.toNat
    else _root_.Int.ofNat scaled.round.toUInt64.toNat
  Json.num ⟨mantissa, digits⟩

def timed (action : Unit → α) : IO (α × Float) := do
  let started ← IO.monoNanosNow
  let result ← blackBoxIO action ()
  let elapsed ← IO.monoNanosNow
  pure (result, (elapsed - started).toFloat / 1e9)

def parseShardIds (value : String) : Except String (Array Nat) := do
  let parts := value.splitOn ","
  if parts.length != 4 then
    throw s!"--shards must contain exactly four comma-separated ids; got {parts.length}"
  let mut ids : Array Nat := #[]
  for part in parts do
    let some shard := part.toNat?
      | throw s!"invalid shard id in --shards: {part}"
    if ids.contains shard then
      throw s!"--shards repeats shard {shard}"
    ids := ids.push shard
  pure ids

def compileToplevel (label : String)
    (source : Except Aiur.Global Aiur.Source.Toplevel) :
    IO (Except String Aiur.CompiledToplevel) := do
  match source with
  | .error error => pure (.error s!"{label} toplevel merge failed: {error}")
  | .ok top => match top.compile with
    | .error error => pure (.error s!"{label} compilation failed: {error}")
    | .ok compiled => pure (.ok compiled)

def prepareShard (env : Ixon.Env) (blocks : Array Address) :
    Except String PreparedShard := do
  let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks env blocks
  let (claim, trees) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned
  let statement ← MultiStark.CheckEnvTrees.ofClaim claim trees
  pure { claim, statement }

structure Fixture where
  shardIds : Array Nat
  blocks : Array (Array Address)
  subjectCounts : Array Nat
  tree : AggregationTree
  prepared : Array PreparedShard

/-- Select four retained manifest shards and contract every other tree leaf.
The requested-id order determines dense indices; tree topology and left/right
orientation remain those of the manifest. -/
def selectFixture (env : Ixon.Env) (view : Ix.Cli.CheckCmd.IxesManifestView)
    (counts requestedIds : Array Nat) : Except String Fixture := do
  if requestedIds.size != 4 then
    throw "internal: policy benchmark requires exactly four shards"
  if view.shards.size != counts.size || view.shards.size != view.shardIds.size then
    throw "manifest view/count cardinality mismatch"
  let mut remap : Array (Option Nat) := Array.replicate view.shards.size none
  let mut blocks : Array (Array Address) := #[]
  let mut selectedCounts : Array Nat := #[]
  let mut prepared : Array PreparedShard := #[]
  for (originalId, selectedIdx) in
      requestedIds.mapIdx fun selectedIdx originalId => (originalId, selectedIdx) do
    let some denseIdx := view.shardIds.findIdx? (· == originalId)
      | throw s!"manifest has no retained shard {originalId}"
    let some shardBlocks := view.shards[denseIdx]?
      | throw s!"manifest is missing blocks for retained shard {originalId}"
    let some subjectCount := counts[denseIdx]?
      | throw s!"manifest is missing the subject count for retained shard {originalId}"
    remap := remap.set! denseIdx (some selectedIdx)
    blocks := blocks.push shardBlocks
    selectedCounts := selectedCounts.push subjectCount
    prepared := prepared.push (← prepareShard env shardBlocks)
  let some tree := view.aggregationTree.pruneAndRemap remap
    | throw "selected shards produced an empty aggregation tree"
  if tree.leaves.size != 4 then
    throw s!"selected aggregation tree has {tree.leaves.size} leaves, expected 4"
  let fixture : Fixture := {
    shardIds := requestedIds
    blocks := blocks
    subjectCounts := selectedCounts
    tree := tree
    prepared := prepared
  }
  pure fixture

/-- Recompute the host fold without claims, verifying that the benchmark root
is exactly the selected manifest subtree rather than a full-environment root. -/
def expectedStatements (plan : Array ScheduledFold)
    (prepared : Array PreparedShard) :
    Except String (Array MultiStark.CheckEnvTrees) := do
  let mut statements : Array MultiStark.CheckEnvTrees := #[]
  for item in plan do
    match item.op with
    | .leaf shard =>
      let some source := prepared[shard]?
        | throw s!"expected fold references missing shard {shard}"
      statements := statements.push source.statement
    | .join leftIdx rightIdx =>
      let some left := statements[leftIdx]?
        | throw s!"expected fold references missing left slot {leftIdx}"
      let some right := statements[rightIdx]?
        | throw s!"expected fold references missing right slot {rightIdx}"
      let left := toAggrCheckEnvTrees left
      let right := toAggrCheckEnvTrees right
      let output := if item.structural then left.joinStructural right
        else left.join right
      statements := statements.push (fromAggrCheckEnvTrees output)
  pure statements

def childKindLabel : Aggr.ChildKind → String
  | .ixvm => "ixvm"
  | .aggr => "ix_aggr"

def optionNatJson : Option Nat → Json
  | none => Json.null
  | some value => Lean.toJson value

def planOperation (item : ScheduledFold) : String :=
  match item.op with
  | .leaf _ => if item.kind == .ixvm then "raw" else "wrap"
  | .join _ _ => if item.structural then "structural-join" else "flat-join"

def planRows (plan : Array ScheduledFold) (shardIds : Array Nat) : Array Json :=
  plan.mapIdx fun slotIdx item =>
    let base : List (String × Json) :=
      [("slot", Lean.toJson slotIdx),
       ("operation", Json.str (planOperation item)),
       ("shape", optionNatJson item.shape?),
       ("subject_count", Lean.toJson item.subjectCount),
       ("ram_weight_bytes", Lean.toJson (aggregateSlotRamBytes item))]
    match item.op with
    | .leaf shard =>
      Json.mkObj (base ++
        [("shard", Lean.toJson ((shardIds[shard]?).getD shard)),
         ("left_kind", Json.str (childKindLabel item.kind)),
         ("right_kind", Json.null)])
    | .join leftIdx rightIdx =>
      let leftKind := (plan[leftIdx]?).map (childKindLabel ·.kind)
        |>.getD "missing"
      let rightKind := (plan[rightIdx]?).map (childKindLabel ·.kind)
        |>.getD "missing"
      Json.mkObj (base ++
        [("left_slot", Lean.toJson leftIdx),
         ("right_slot", Lean.toJson rightIdx),
         ("left_kind", Json.str leftKind),
         ("right_kind", Json.str rightKind)])

def printPlan (policy : Policy) (plan : Array ScheduledFold)
    (shardIds : Array Nat) (structuralAbove : Nat) : IO Unit := do
  IO.println s!"[aggregate-policy] {policy.label}; structural threshold > {structuralAbove}"
  for (item, slotIdx) in plan.mapIdx fun slotIdx item => (item, slotIdx) do
    match item.op with
    | .leaf shard =>
      let originalShard := (shardIds[shard]?).getD shard
      IO.println s!"  slot {slotIdx}: {planOperation item} shard {originalShard}; \
        shape {item.shape?.map toString |>.getD "raw"}; {item.subjectCount} subjects"
    | .join left right =>
      IO.println s!"  slot {slotIdx}: {planOperation item} slots {left},{right}; \
        shape {item.shape?.map toString |>.getD "missing"}; {item.subjectCount} subjects"

structure InputProof where
  address : Address
  wrapper : Ixon.Proof
  proof : Aiur.Proof
  innerClaim : Array Aiur.G
  claimsBytes : ByteArray

def loadInputProof (shardId : Nat) (proofAddress : String)
    (prepared : PreparedShard) (verifyIdx : Aiur.Bytecode.FunIdx) :
    IO (Except String InputProof) := do
  let some address := Address.fromString proofAddress
    | return .error s!"--proof-{shardId}: expected a 64-character store address"
  try
    let wrapper ← match Ixon.Proof.de (← StoreIO.toIO (Store.read address)) with
      | .error error =>
        return .error s!"shard {shardId}: wrapper decode failed: {error}"
      | .ok wrapper => pure wrapper
    if wrapper.claim != prepared.claim then
      return .error s!"shard {shardId}: persisted wrapper claim does not match the selected shard"
    let proof ← match Aiur.Proof.ofBytesChecked wrapper.proof with
      | .error error =>
        return .error s!"shard {shardId}: proof decode failed: {error}"
      | .ok proof => pure proof
    let claimBytes := Ix.Claim.ser prepared.claim
    let innerClaim := Aiur.buildClaim verifyIdx
      (IxVM.ClaimHarness.packedDigestKey (Address.blake3 claimBytes)) #[]
    let input : InputProof := {
      address := address
      wrapper := wrapper
      proof := proof
      innerClaim := innerClaim
      claimsBytes := MultiStark.serializeClaims #[innerClaim]
    }
    pure (.ok input)
  catch error =>
    pure (.error s!"shard {shardId}: store read failed: {error}")

def persistAggregateProof (statement : MultiStark.CheckEnvTrees)
    (proof : Aiur.Proof) : IO Address := do
  let claim := statement.claim
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
  let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
  StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))

structure MeasuredSlot where
  slot : AggregateSlot
  row : Json
  proveSeconds : Float
  peakTreeRssBytes : Nat

def stageRow (slotIdx : Nat) (item : ScheduledFold)
    (leftKind rightKind : Option Aggr.ChildKind) (proveSeconds verifySeconds : Float)
    (inputVerifySeconds : Option Float) (peakTreeRssBytes proofBytes : Nat)
    (claimDigest proofAddress : Address) : Json :=
  Json.mkObj <|
    [("slot", Lean.toJson slotIdx),
     ("operation", Json.str (planOperation item)),
     ("shape", optionNatJson item.shape?),
     ("left_kind", leftKind.map (Json.str ∘ childKindLabel) |>.getD Json.null),
     ("right_kind", rightKind.map (Json.str ∘ childKindLabel) |>.getD Json.null),
     ("subject_count", Lean.toJson item.subjectCount),
     ("prove_seconds", jsonRound 6 proveSeconds),
     ("verify_seconds", jsonRound 6 verifySeconds),
     ("peak_tree_rss_bytes", Lean.toJson peakTreeRssBytes),
     ("proof_bytes", Lean.toJson proofBytes),
     ("claim_digest", Json.str (toString claimDigest)),
     ("proof_address", Json.str (toString proofAddress))] ++
    match inputVerifySeconds with
    | none => []
    | some seconds => [("input_verify_seconds", jsonRound 6 seconds)]

def runLeaf (slotIdx shardId : Nat) (item : ScheduledFold)
    (prepared : PreparedShard) (input : InputProof) (spec : AggregateSlotSpec)
    (ixvmSystem aggrSystem : Aiur.AiurSystem) (ixvmVk aggrVk allowed : ByteArray)
    (aggrIdx : Aiur.Bytecode.FunIdx) : IO (Except String MeasuredSlot) := do
  TracingTexray.resetPeakTreeRss
  let (innerVerified, innerVerifySeconds) ← timed fun _ =>
    ixvmSystem.verify input.innerClaim input.proof
  let innerVerifyPeak ← TracingTexray.peakTreeRssBytes
  match innerVerified with
  | .error error =>
    return .error s!"shard {shardId}: native input verification failed: {error}"
  | .ok () => pure ()
  if spec.outerClaim != (if item.kind == .ixvm then input.innerClaim
      else aggregateOuterClaim allowed aggrIdx prepared.claim) then
    return .error s!"shard {shardId}: prepared leaf outer claim is inconsistent"
  match item.kind with
  | .ixvm =>
    if item.shape?.isSome then
      return .error s!"shard {shardId}: raw leaf unexpectedly has an ix_aggr shape"
    let slot : AggregateSlot := {
      kind := .ixvm, statement := spec.statement,
      subjectCount := spec.subjectCount, outerClaim := input.innerClaim,
      proof := input.proof, proofAddress? := some input.address,
      claimsBytes := input.claimsBytes
    }
    pure (.ok {
      slot
      row := stageRow slotIdx item (some .ixvm) none 0 innerVerifySeconds none
        innerVerifyPeak input.wrapper.proof.size
        (Address.blake3 (Ix.Claim.ser spec.statement.claim)) input.address
      proveSeconds := 0
      peakTreeRssBytes := innerVerifyPeak
    })
  | .aggr =>
    if item.shape? != some 0 then
      return .error s!"shard {shardId}: wrap leaf requires shape 0"
    let innerProofAdvice ← match ixvmSystem.proofToAdviceBytes
        input.innerClaim input.proof with
      | .error error =>
        return .error s!"shard {shardId}: proof advice encoding failed: {error}"
      | .ok bytes => pure bytes
    let claimBytes := Ix.Claim.ser prepared.claim
    let pubInput := Aggr.pubInput allowed claimBytes
    IO.println s!"[aggregate-policy] proving slot {slotIdx}: wrap shard {shardId}"
    (← IO.getStdout).flush
    TracingTexray.resetPeakTreeRss
    let (proved, proveSeconds) ← timed fun _ =>
      aggrSystem.proveIxAggr aggrIdx pubInput 0
        innerProofAdvice ByteArray.empty ixvmVk aggrVk
        input.claimsBytes ByteArray.empty claimBytes allowed
        (Aggr.preimagesBlob #[]) (Aggr.treesBlob #[]) (Aggr.pathsBlob #[])
    let provePeak ← TracingTexray.peakTreeRssBytes
    let (outerClaim, proof) ← match proved with
      | .error error => return .error s!"shard {shardId}: wrap proving failed: {error}"
      | .ok result => pure result
    if outerClaim != spec.outerClaim then
      return .error s!"shard {shardId}: wrap produced an unexpected outer claim"
    TracingTexray.resetPeakTreeRss
    let (verified, verifySeconds) ← timed fun _ => aggrSystem.verify outerClaim proof
    let verifyPeak ← TracingTexray.peakTreeRssBytes
    match verified with
    | .error error =>
      return .error s!"shard {shardId}: wrap output verification failed: {error}"
    | .ok () => pure ()
    let address ← persistAggregateProof spec.statement proof
    let proofBytes := proof.toBytes
    let peak := max innerVerifyPeak (max provePeak verifyPeak)
    let slot : AggregateSlot := {
      kind := .aggr, statement := spec.statement,
      subjectCount := spec.subjectCount, outerClaim,
      proof, proofAddress? := some address,
      claimsBytes := MultiStark.serializeClaims #[outerClaim]
    }
    pure (.ok {
      slot
      row := stageRow slotIdx item (some .ixvm) none proveSeconds verifySeconds
        (some innerVerifySeconds) peak proofBytes.size
        (Address.blake3 claimBytes) address
      proveSeconds
      peakTreeRssBytes := peak
    })

def runJoin (slotIdx : Nat) (item : ScheduledFold) (left right : AggregateSlot)
    (spec : AggregateSlotSpec) (ixvmSystem aggrSystem : Aiur.AiurSystem)
    (ixvmVk aggrVk allowed : ByteArray) (aggrIdx : Aiur.Bytecode.FunIdx) :
    IO (Except String MeasuredSlot) := do
  let output := spec.statement
  let outputClaimBytes := Ix.Claim.ser output.claim
  let pubInput := Aggr.pubInput allowed outputClaimBytes
  let leftStatement := toAggrCheckEnvTrees left.statement
  let rightStatement := toAggrCheckEnvTrees right.statement
  let outputStatement := toAggrCheckEnvTrees output
  let preimagesBlob := Aggr.preimagesBlob
    #[Ix.Claim.ser left.statement.claim, Ix.Claim.ser right.statement.claim]
  let trees := if item.structural then
      Aggr.CheckEnvTrees.structuralAdviceTrees leftStatement rightStatement outputStatement
    else Aggr.CheckEnvTrees.adviceTrees leftStatement rightStatement outputStatement
  let treesBlob := Aggr.treesBlob trees
  let pathsBlob := if item.structural then
      Aggr.pathsBlob
        (Aggr.CheckEnvTrees.structuralPathAdvice leftStatement rightStatement outputStatement)
    else Aggr.pathsBlob #[]
  let leftSystem := if left.kind == .ixvm then ixvmSystem else aggrSystem
  let rightSystem := if right.kind == .ixvm then ixvmSystem else aggrSystem
  let leftProofAdvice ← match leftSystem.proofToAdviceBytes left.outerClaim left.proof with
    | .error error => return .error s!"slot {slotIdx}: left proof advice failed: {error}"
    | .ok bytes => pure bytes
  let rightProofAdvice ← match rightSystem.proofToAdviceBytes right.outerClaim right.proof with
    | .error error => return .error s!"slot {slotIdx}: right proof advice failed: {error}"
    | .ok bytes => pure bytes
  let some shape := item.shape?
    | return .error s!"slot {slotIdx}: join has no ix_aggr shape"
  let mode := if item.structural then "structural" else "flat"
  IO.println s!"[aggregate-policy] proving slot {slotIdx}: {mode} shape {shape}"
  (← IO.getStdout).flush
  TracingTexray.resetPeakTreeRss
  let (proved, proveSeconds) ← timed fun _ =>
    aggrSystem.proveIxAggr aggrIdx pubInput shape
      leftProofAdvice rightProofAdvice ixvmVk aggrVk
      left.claimsBytes right.claimsBytes outputClaimBytes allowed
      preimagesBlob treesBlob pathsBlob
  let provePeak ← TracingTexray.peakTreeRssBytes
  let (outerClaim, proof) ← match proved with
    | .error error => return .error s!"slot {slotIdx}: join proving failed: {error}"
    | .ok result => pure result
  if outerClaim != spec.outerClaim then
    return .error s!"slot {slotIdx}: join produced an unexpected outer claim"
  TracingTexray.resetPeakTreeRss
  let (verified, verifySeconds) ← timed fun _ => aggrSystem.verify outerClaim proof
  let verifyPeak ← TracingTexray.peakTreeRssBytes
  match verified with
  | .error error => return .error s!"slot {slotIdx}: output verification failed: {error}"
  | .ok () => pure ()
  let address ← persistAggregateProof output proof
  let proofBytes := proof.toBytes
  let peak := max provePeak verifyPeak
  let slot : AggregateSlot := {
    kind := .aggr, statement := output,
    subjectCount := spec.subjectCount, outerClaim,
    proof, proofAddress? := some address,
    claimsBytes := MultiStark.serializeClaims #[outerClaim]
  }
  pure (.ok {
    slot
    row := stageRow slotIdx item (some left.kind) (some right.kind)
      proveSeconds verifySeconds none peak proofBytes.size
      (Address.blake3 outputClaimBytes) address
    proveSeconds
    peakTreeRssBytes := peak
  })

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

def writeReport (path? : Option String) (metadata : Json) (plan stages : Array Json)
    (status : String) (totals? : Option Json := none)
    (error? : Option String := none) : IO Unit := do
  if let some path := path? then
    let fields : List (String × Json) :=
      [("schema_version", Lean.toJson (1 : Nat)),
       ("status", Json.str status),
       ("metadata", metadata),
       ("plan", Json.arr plan),
       ("stages", Json.arr stages),
       ("totals", totals?.getD Json.null)] ++
      match error? with
      | none => []
      | some error => [("error", Json.str error)]
    IO.FS.writeFile path ((Json.mkObj fields).pretty ++ "\n")

def metadata (ixePath ixesPath : String) (ixeBytes ixesBytes : ByteArray)
    (fixture : Fixture) (proofAddresses : Array String) (policy : Policy)
    (queries structuralAbove jobs maxRamGiB : Nat)
    (ixvmVk? aggrVk? : Option ByteArray := none) : IO Json := do
  let commit ← commandOutput "git" #["rev-parse", "HEAD"]
  let timestamp ← commandOutput "date" #["-Is"]
  let host ← commandOutput "hostname"
  let cpu ← cpuLabel
  let memInfo ← try IO.FS.readFile "/proc/meminfo" catch _ => pure ""
  let physicalRam := aggregateMemTotalBytes memInfo |>.getD 0
  let fri := { Aiur.defaultFriParameters with numQueries := queries }
  pure <| Json.mkObj
    [("commit", Json.str commit),
     ("timestamp", Json.str timestamp),
     ("host", Json.str host),
     ("cpu", Json.str cpu),
     ("physical_ram_bytes", Lean.toJson physicalRam),
     ("ixe", Json.str ixePath),
     ("ixe_digest", Json.str (toString (Address.blake3 ixeBytes))),
     ("ixe_bytes", Lean.toJson ixeBytes.size),
     ("ixes", Json.str ixesPath),
     ("ixes_digest", Json.str (toString (Address.blake3 ixesBytes))),
     ("ixes_bytes", Lean.toJson ixesBytes.size),
     ("shard_ids", Lean.toJson fixture.shardIds),
     ("input_proof_addresses", Lean.toJson proofAddresses),
     ("policy", Json.str policy.label),
     ("recursion_parameters", Json.mkObj
       [("log_blowup", Lean.toJson Aiur.defaultCommitmentParameters.logBlowup),
        ("cap_height", Lean.toJson Aiur.defaultCommitmentParameters.capHeight),
        ("log_final_poly_len", Lean.toJson fri.logFinalPolyLen),
        ("max_log_arity", Lean.toJson fri.maxLogArity),
        ("num_queries", Lean.toJson fri.numQueries),
        ("commit_pow_bits", Lean.toJson fri.commitProofOfWorkBits),
        ("query_pow_bits", Lean.toJson fri.queryProofOfWorkBits)]),
     ("structural_above", Lean.toJson structuralAbove),
     ("jobs", Lean.toJson jobs),
     ("max_ram_gib", Lean.toJson maxRamGiB),
     ("cache", Json.str "disabled"),
     ("wall_scope", Json.str "input verification plus recursive slots"),
     ("ixvm_vk_digest", ixvmVk?.map (Json.str ∘ toString ∘ Address.blake3)
       |>.getD Json.null),
     ("ix_aggr_vk_digest", aggrVk?.map (Json.str ∘ toString ∘ Address.blake3)
       |>.getD Json.null)]

def usage : String :=
  "usage: bench-aggregate-policy --ixe ENV.ixe --ixes MANIFEST.ixes " ++
  "--shards A,B,C,D --proof-A ADDR --proof-B ADDR --proof-C ADDR " ++
  "--proof-D ADDR --policy wrap-first|direct [--structural-above N] " ++
  "[--queries N] [--jobs 1] [--max-ram GIB] --no-cache --json RESULT.json " ++
  "[--plan-only]"

def main (args : List String) : IO UInt32 := do
  if hasFlag args "--help" then
    IO.println usage
    return 0
  let some ixePath := argStr args "--ixe" | do
    IO.eprintln "error: --ixe is required"; IO.eprintln usage; return 2
  let some ixesPath := argStr args "--ixes" | do
    IO.eprintln "error: --ixes is required"; IO.eprintln usage; return 2
  let some shardsValue := argStr args "--shards" | do
    IO.eprintln "error: --shards is required"; IO.eprintln usage; return 2
  let shardIds ← match parseShardIds shardsValue with
    | .error error => IO.eprintln s!"error: {error}"; return 2
    | .ok ids => pure ids
  let some policyValue := argStr args "--policy" | do
    IO.eprintln "error: --policy is required"; IO.eprintln usage; return 2
  let policy ← match Policy.parse policyValue with
    | .error error => IO.eprintln s!"error: {error}"; return 2
    | .ok policy => pure policy
  let queries := (argNat? args "--queries").getD 100
  if queries != 100 then
    IO.eprintln "error: M1-f requires --queries 100 so roots use the production verifier parameters"
    return 2
  let structuralAbove := (argNat? args "--structural-above").getD defaultStructuralAbove
  let jobs := (argNat? args "--jobs").getD 1
  if jobs != 1 then
    IO.eprintln "error: the M1-f policy comparison requires --jobs 1"; return 2
  let maxRamGiB := (argNat? args "--max-ram").getD 450
  if maxRamGiB == 0 then
    IO.eprintln "error: --max-ram must be positive"; return 2
  let planOnly := hasFlag args "--plan-only"
  let jsonPath? := argStr args "--json"
  if !planOnly && jsonPath?.isNone then
    IO.eprintln "error: measured runs require --json"; return 2
  if !planOnly && !hasFlag args "--no-cache" then
    IO.eprintln "error: measured runs require --no-cache"; return 2

  let ixeBytes ← IO.FS.readBinFile ixePath
  let ixesBytes ← IO.FS.readBinFile ixesPath
  let env ← match Ixon.deEnvAnon ixeBytes with
    | .error error => IO.eprintln s!"deserialize {ixePath} failed: {error}"; return 1
    | .ok env => pure env
  let rawView ← match Ix.Cli.CheckCmd.parseIxesManifest ixesBytes with
    | .error error => IO.eprintln s!"manifest parse failed: {error}"; return 1
    | .ok view => pure view
  if !(← Ix.Cli.CheckCmd.shardsCover env rawView.shards) then return 1
  let (view, counts) ← match rawView.pruneEmpty env with
    | .error error => IO.eprintln error; return 1
    | .ok result => pure result
  let fixture ← match selectFixture env view counts shardIds with
    | .error error => IO.eprintln s!"select fixture: {error}"; return 1
    | .ok fixture => pure fixture
  let plan ← match schedulePlan fixture.tree.foldPlan fixture.subjectCounts
      structuralAbove policy.directJoins with
    | .error error => IO.eprintln s!"schedule selected fixture: {error}"; return 1
    | .ok plan => pure plan
  let expected ← match expectedStatements plan fixture.prepared with
    | .error error => IO.eprintln s!"reconstruct selected root: {error}"; return 1
    | .ok statements => pure statements
  let some expectedRoot := expected.back? | do
    IO.eprintln "selected fixture produced no host root"; return 1
  let rows := planRows plan fixture.shardIds
  printPlan policy plan fixture.shardIds structuralAbove
  let weights := aggregateSlotRamWeights plan
  let requiredRam := weights.foldl max 0
  if maxRamGiB * aggregateGiB < requiredRam then
    IO.eprintln s!"error: --max-ram {maxRamGiB} GiB is below the plan's largest \
      slot reserve of {requiredRam / aggregateGiB} GiB"
    return 2

  let mut proofHexes : Array String := #[]
  if !planOnly then
    for shardId in fixture.shardIds do
      let flag := s!"--proof-{shardId}"
      let some proofHex := argStr args flag | do
        IO.eprintln s!"error: {flag} is required"; return 2
      proofHexes := proofHexes.push proofHex
  let metadata0 ← metadata ixePath ixesPath ixeBytes ixesBytes fixture proofHexes
    policy queries structuralAbove jobs maxRamGiB
  if planOnly then
    writeReport jsonPath? metadata0 rows #[] "plan-only"
    return 0

  writeReport jsonPath? metadata0 rows #[] "preparing"
  TracingTexray.startSampler 25
  IO.println "[aggregate-policy] compiling IxVM and ixAggr systems"
  let ixvmCompiled ← match ← compileToplevel "IxVM" IxVM.ixVM with
    | .error error =>
      writeReport jsonPath? metadata0 rows #[] "error" (error? := some error)
      IO.eprintln error
      return 1
    | .ok compiled => pure compiled
  let aggrCompiled ← match ← compileToplevel "ixAggr recursion" Aggr.ixAggr with
    | .error error =>
      writeReport jsonPath? metadata0 rows #[] "error" (error? := some error)
      IO.eprintln error
      return 1
    | .ok compiled => pure compiled
  let verifyIdx := ixvmCompiled.getFuncIdx `verify_claim |>.get!
  let aggrIdx := aggrCompiled.getFuncIdx `ix_aggr |>.get!
  let friParameters := { Aiur.defaultFriParameters with numQueries := queries }
  let recursionParameters : MultiStark.RecursionParameters := {
    commitment := Aiur.defaultCommitmentParameters
    fri := friParameters
  }
  let ixvmSystem := Aiur.AiurSystem.build ixvmCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let aggrSystem := MultiStark.buildRecursionSystem aggrCompiled.bytecode
    recursionParameters
  let ixvmVk := ixvmSystem.vkBytes
  let aggrVk := aggrSystem.vkBytes
  let allowed := Aggr.allowedBlob ixvmVk verifyIdx aggrVk aggrIdx
  let specs ← match buildAggrSlotSpecs plan fixture.prepared aggrVk allowed
      verifyIdx aggrIdx recursionParameters with
    | .error error =>
      let error := s!"prepare policy slots: {error}"
      writeReport jsonPath? metadata0 rows #[] "error" (error? := some error)
      IO.eprintln error
      return 1
    | .ok specs => pure specs
  let some rootSpec := specs.back? | do
    let error := "prepared policy has no root slot"
    writeReport jsonPath? metadata0 rows #[] "error" (error? := some error)
    IO.eprintln error
    return 1
  if rootSpec.statement.claim != expectedRoot.claim then
    let error := "prepared root differs from independent selected-subtree fold"
    writeReport jsonPath? metadata0 rows #[] "error" (error? := some error)
    IO.eprintln error
    return 1

  let mut inputs : Array InputProof := #[]
  for shard in [:fixture.shardIds.size] do
    let shardId := fixture.shardIds[shard]!
    let some preparedShard := fixture.prepared[shard]? | do
      let error := s!"internal: missing prepared shard {shardId}"
      writeReport jsonPath? metadata0 rows #[] "error" (error? := some error)
      IO.eprintln error
      return 1
    let input ← match ← loadInputProof shardId proofHexes[shard]!
        preparedShard verifyIdx with
      | .error error =>
        writeReport jsonPath? metadata0 rows #[] "error" (error? := some error)
        IO.eprintln error
        return 1
      | .ok input => pure input
    inputs := inputs.push input
  let metadata ← metadata ixePath ixesPath ixeBytes ixesBytes fixture proofHexes
    policy queries structuralAbove jobs maxRamGiB (some ixvmVk) (some aggrVk)
  let mut stages : Array Json := #[]
  writeReport jsonPath? metadata rows stages "running"
  let wallStarted ← IO.monoNanosNow
  let mut slots : Array AggregateSlot := #[]
  let mut proveSeconds : Float := 0
  let mut maxPeak : Nat := 0
  for (item, slotIdx) in plan.mapIdx fun slotIdx item => (item, slotIdx) do
    let some spec := specs[slotIdx]? | do
      let error := s!"missing prepared slot {slotIdx}"
      writeReport jsonPath? metadata rows stages "error" (error? := some error)
      IO.eprintln error
      return 1
    let measured ← match item.op with
      | .leaf shard =>
        let shardId := fixture.shardIds[shard]!
        let some preparedShard := fixture.prepared[shard]? | do
          let error := s!"slot {slotIdx}: missing prepared shard {shardId}"
          writeReport jsonPath? metadata rows stages "error" (error? := some error)
          IO.eprintln error
          return 1
        let some input := inputs[shard]? | do
          let error := s!"slot {slotIdx}: missing input proof for shard {shardId}"
          writeReport jsonPath? metadata rows stages "error" (error? := some error)
          IO.eprintln error
          return 1
        match ← runLeaf slotIdx shardId item preparedShard
            input spec ixvmSystem aggrSystem ixvmVk aggrVk allowed aggrIdx with
        | .error error =>
          writeReport jsonPath? metadata rows stages "error" (error? := some error)
          IO.eprintln error
          return 1
        | .ok measured => pure measured
      | .join leftIdx rightIdx =>
        let some left := slots[leftIdx]? | do
          let error := s!"slot {slotIdx}: missing left slot {leftIdx}"
          writeReport jsonPath? metadata rows stages "error" (error? := some error)
          IO.eprintln error
          return 1
        let some right := slots[rightIdx]? | do
          let error := s!"slot {slotIdx}: missing right slot {rightIdx}"
          writeReport jsonPath? metadata rows stages "error" (error? := some error)
          IO.eprintln error
          return 1
        match ← runJoin slotIdx item left right spec ixvmSystem aggrSystem
            ixvmVk aggrVk allowed aggrIdx with
        | .error error =>
          writeReport jsonPath? metadata rows stages "error" (error? := some error)
          IO.eprintln error
          return 1
        | .ok measured => pure measured
    slots := slots.push measured.slot
    stages := stages.push measured.row
    proveSeconds := proveSeconds + measured.proveSeconds
    maxPeak := max maxPeak measured.peakTreeRssBytes
    writeReport jsonPath? metadata rows stages "running"

  let wallEnded ← IO.monoNanosNow
  let wallSeconds := (wallEnded - wallStarted).toFloat / 1e9
  let some root := slots.back? | do
    let error := "policy plan produced no root slot"
    writeReport jsonPath? metadata rows stages "error" (error? := some error)
    IO.eprintln error
    return 1
  if root.kind != .aggr || root.statement.claim != expectedRoot.claim then
    let error := "proved root differs from the independently reconstructed ix_aggr root"
    writeReport jsonPath? metadata rows stages "error" (error? := some error)
    IO.eprintln error
    return 1
  let some rootAddress := root.proofAddress? | do
    let error := "root aggregate proof was not persisted"
    writeReport jsonPath? metadata rows stages "error" (error? := some error)
    IO.eprintln error
    return 1
  let rootProofBytes := root.proof.toBytes
  let rootClaimDigest := Address.blake3 (Ix.Claim.ser root.statement.claim)
  let outerClaimDigest := Address.blake3 (MultiStark.serializeClaims #[root.outerClaim])
  let totals := Json.mkObj
    [("wall_seconds", jsonRound 6 wallSeconds),
     ("serialized_prove_seconds", jsonRound 6 proveSeconds),
     ("peak_tree_rss_bytes", Lean.toJson maxPeak),
     ("root_claim_digest", Json.str (toString rootClaimDigest)),
     ("root_outer_claim_digest", Json.str (toString outerClaimDigest)),
     ("root_proof_bytes", Lean.toJson rootProofBytes.size),
     ("root_proof_address", Json.str (toString rootAddress)),
     ("retains_assumptions", Lean.toJson root.statement.assumptions.isSome)]
  writeReport jsonPath? metadata rows stages "ok" (some totals)
  IO.println s!"[aggregate-policy] OK: {policy.label}; {proveSeconds}s proving; \
    {wallSeconds}s measured wall; peak {maxPeak} bytes; root {rootAddress} \
    ({rootProofBytes.size} bytes, claim {rootClaimDigest})"
  pure 0

end Benchmarks.AggregatePolicy

def main (args : List String) : IO UInt32 :=
  Benchmarks.AggregatePolicy.main args
