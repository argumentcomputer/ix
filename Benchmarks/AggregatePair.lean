import Ix.Cli.AggregateCmd
import Ix.Cli.NameResolve
import Ix.TracingTexray
import Ix.Benchmark.Bench

/-!
# Two-shard end-to-end production aggregation benchmark

This is deliberately a benchmark executable rather than a production CLI
mode. It can select two shards from a validated `.ixes` manifest and benchmark
the complete proof path:

```
shard A -> IxVM proof A -> recursive lift A ---+
                                             +-> structural/flat join -> verify
shard B -> IxVM proof B -> recursive lift B ---+
```

Unlike `ix aggregate`, the result is allowed to retain assumptions and need
not cover the whole environment. It therefore cannot be mistaken for a closed
full-environment aggregate.

With no arguments it reads `init.ixe` and treats the `False` and `True` block
groups as two conditional micro-shards. They exercise the real Init environment
and production proof stack without inheriting the memory footprint of a full
RAM-planned shard. `--ixes` switches to a complete manifest and automatically
chooses its smallest direct sibling pair. Supplying `--shard-a` and `--shard-b`
instead selects any two nonempty shards from that manifest; they need not be
siblings:

```
lake exe bench-aggregate-pair -- \
  --ixe /path/init.ixe --name-a False --name-b True \
  --json /tmp/init-pair.json --texray

lake exe bench-aggregate-pair -- \
  --ixe /path/init.ixe --ixes /path/init.ixes \
  --shard-a 3 --shard-b 17 --json /tmp/init-real-pair.json
```

`--proof-a` and `--proof-b` may be supplied together to reuse persisted base
proofs. They are an explicit warm-start mode; the default always measures base
proving as well as recursive aggregation.

Every stage is the real production proof call, with no execution-only preflight
or memory gate. Like `bench-typecheck --recursive`, the default benchmark
profile uses 50 FRI queries and zero query PoW for both base and recursive
proofs; `--queries` can override the count. Timings and measured peak RSS are
recorded after the fact.
-/

open Lean (Json)

namespace Benchmarks.AggregatePair

open Ix
open Ix.Cli.AggregateCmd

abbrev AggregationTree := Ix.Cli.CheckCmd.AggregationTree
abbrev FoldOp := Ix.Cli.CheckCmd.AggregationTree.FoldOp

/-- Keep this in lockstep with `Benchmarks.Typecheck.recursiveFriParameters`.
The benchmark measures the full recursive architecture under the repository's
established tractable recursion profile, not the 100-query production policy. -/
def benchmarkFriParameters (queries : Nat) : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := queries
  commitProofOfWorkBits := 0
  queryProofOfWorkBits := 0
}

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

def stageJson (fields : List (String × Json)) : Json :=
  Json.mkObj (("status", Json.str "ok") :: fields)

def errorJson (message : String) : Json :=
  Json.mkObj [("status", Json.str "error"), ("message", Json.str message)]

def writeReport (path? : Option String) (metadata : List (String × Json))
    (status : String) (stages : Array (String × Json)) : IO Unit := do
  if let some path := path? then
    let report := Json.mkObj (metadata ++
      [("status", Json.str status), ("stages", Json.mkObj stages.toList)])
    IO.FS.writeFile path (report.pretty ++ "\n")

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

def blockOfAddress (env : Ixon.Env) (address : Address) : Except String Address := do
  let some constant := env.getConst? address
    | throw s!"constant {address} is absent or malformed"
  pure <| match constant.info with
    | .iPrj projection => projection.block
    | .cPrj projection => projection.block
    | .rPrj projection => projection.block
    | .dPrj projection => projection.block
    | _ => address

def namedMicroShard (env : Ixon.Env) (name : String) :
    Except String (Array Address) := do
  let some address := Ix.Cli.NameResolve.resolveIxeAddr env name
    | throw s!"Init micro-shard name not found: {name}"
  pure #[← blockOfAddress env address]

partial def siblingLeafPairs (tree : AggregationTree) : Array (Nat × Nat) :=
  match tree with
  | .leaf _ => #[]
  | .node left right =>
    let here := match left, right with
      | .leaf l, .leaf r => #[(l, r)]
      | _, _ => #[]
    here ++ siblingLeafPairs left ++ siblingLeafPairs right

/-- The smallest direct sibling pair by combined subject count. The manifest
tree and count array have already passed coverage/pruning validation. -/
def smallestSiblingPair? (tree : AggregationTree) (counts : Array Nat) :
    Option (Nat × Nat) :=
  (siblingLeafPairs tree).foldl (init := none) fun best pair =>
    match best with
    | none => some pair
    | some current =>
      let pairCount := counts[pair.1]! + counts[pair.2]!
      let currentCount := counts[current.1]! + counts[current.2]!
      if pairCount < currentCount then some pair else some current

def loadProofWrapper (label proofAddress : String) : IO (Except String Ixon.Proof) := do
  let some address := Address.fromString proofAddress
    | return .error s!"{label}: expected a 64-character store address"
  try
    match Ixon.Proof.de (← StoreIO.toIO (Store.read address)) with
    | .error error => pure (.error s!"{label}: wrapper decode failed: {error}")
    | .ok wrapper => pure (.ok wrapper)
  catch error =>
    pure (.error s!"{label}: store read failed: {error}")

structure BenchSlot where
  slot : AggregateSlot
  proveSeconds : Float

structure BaseProofBench where
  wrapper : Ixon.Proof
  proveSeconds : Float

/-- Generate one ordinary shard proof through the same native EnvHandle path as
`ix prove --ixe E --ixes M --shard K`, but retain it in memory for the lift. -/
def runBaseProof (label : String) (envHandle : Aiur.EnvHandle)
    (owned : Array Address) (expectedClaim : Ix.Claim)
    (ixvmSystem : Aiur.AiurSystem) (verifyIdx : Aiur.Bytecode.FunIdx)
    (record : String → Json → IO Unit) : IO (Except String BaseProofBench) := do
  let ownedBlob := owned.foldl (fun bytes address => bytes ++ address.hash)
    ByteArray.empty
  IO.println s!"[pair-bench] proving {label}"
  (← IO.getStdout).flush
  TracingTexray.resetPeakTreeRss
  let (proved, proveSeconds) ← timed fun _ =>
    ixvmSystem.shardProveWithEnv verifyIdx envHandle ownedBlob
  let provePeak ← TracingTexray.peakTreeRssBytes
  let (claimBytes, proof) ← match proved with
    | .error error =>
      record s!"{label}-prove" (errorJson error)
      return .error s!"{label}: shardProveWithEnv failed: {error}"
    | .ok (claimBytes, proof, _) => pure (claimBytes, proof)
  let claim ← match Ixon.runGet Ix.Claim.get claimBytes with
    | .error error =>
      record s!"{label}-prove" (errorJson s!"claim decode failed: {error}")
      return .error s!"{label}: claim decode failed: {error}"
    | .ok claim => pure claim
  if claim != expectedClaim then
    let error := "native shard prover returned a different CheckEnv claim"
    record s!"{label}-prove" (errorJson error)
    return .error s!"{label}: {error}"
  let proofBytes := proof.toBytes
  record s!"{label}-prove" (stageJson
    [("seconds", jsonRound 6 proveSeconds),
     ("peak-rss-bytes", Lean.toJson provePeak),
     ("proof-bytes", Lean.toJson proofBytes.size),
     ("source", Json.str "generated")])
  pure (.ok {
    wrapper := { claim, proof := proofBytes }
    proveSeconds
  })

def reuseBaseProof (label address : String) (expectedClaim : Ix.Claim)
    (record : String → Json → IO Unit) : IO (Except String BaseProofBench) := do
  let wrapper ← match ← loadProofWrapper label address with
    | .error error => return .error error
    | .ok wrapper => pure wrapper
  if wrapper.claim != expectedClaim then
    return .error s!"{label}: persisted wrapper claim does not match the selected shard"
  record s!"{label}-prove" (stageJson
    [("seconds", jsonRound 6 0),
     ("peak-rss-bytes", Lean.toJson (0 : Nat)),
     ("proof-bytes", Lean.toJson wrapper.proof.size),
     ("source", Json.str "reused")])
  pure (.ok { wrapper, proveSeconds := 0 })

def runLift (label : String) (prepared : PreparedShard) (wrapper : Ixon.Proof)
    (spec : AggregateSlotSpec) (ixvmSystem recursionSystem : Aiur.AiurSystem)
    (verifyIdx liftIdx : Aiur.Bytecode.FunIdx) (ixvmVk : ByteArray)
    (record : String → Json → IO Unit) :
    IO (Except String BenchSlot) := do
  if wrapper.claim != prepared.claim then
    return .error s!"{label}: bundled CheckEnv claim does not match the selected shard"
  let innerProof ← match Aiur.Proof.ofBytesChecked wrapper.proof with
    | .error error => return .error s!"{label}: inner proof decode failed: {error}"
    | .ok proof => pure proof
  let claimBytes := Ix.Claim.ser prepared.claim
  let verifyInput := IxVM.ClaimHarness.packedDigestKey (Address.blake3 claimBytes)
  let innerClaim := Aiur.buildClaim verifyIdx verifyInput #[]

  TracingTexray.resetPeakTreeRss
  let (innerVerified, innerVerifySeconds) ← timed fun _ =>
    ixvmSystem.verify innerClaim innerProof
  let innerVerifyPeak ← TracingTexray.peakTreeRssBytes
  match innerVerified with
  | .error error =>
    record s!"{label}-inner-verify" (errorJson error)
    return .error s!"{label}: inner proof verification failed: {error}"
  | .ok () =>
    record s!"{label}-inner-verify" (stageJson
      [("seconds", jsonRound 6 innerVerifySeconds),
       ("peak-rss-bytes", Lean.toJson innerVerifyPeak),
       ("proof-bytes", Lean.toJson wrapper.proof.size)])

  let innerProofAdvice ← match ixvmSystem.proofToAdviceBytes innerClaim innerProof with
    | .error error =>
      return .error s!"{label}: inner proof advice encoding failed: {error}"
    | .ok bytes => pure bytes

  let innerClaimsBytes := MultiStark.serializeClaims #[innerClaim]
  let pubInput := MultiStark.verifierPubInput ixvmVk innerClaimsBytes
  IO.println s!"[pair-bench] proving {label}"
  (← IO.getStdout).flush
  TracingTexray.resetPeakTreeRss
  let ((outerClaim, proof), proveSeconds) ← timed fun _ =>
    recursionSystem.proveMultiStark liftIdx pubInput innerProofAdvice ixvmVk innerClaimsBytes
  let provePeak ← TracingTexray.peakTreeRssBytes
  if outerClaim != spec.outerClaim then
    let error := "produced an unexpected outer claim"
    record s!"{label}-prove" (errorJson error)
    return .error s!"{label}: {error}"
  let proofBytes := proof.toBytes
  record s!"{label}-prove" (stageJson
    [("seconds", jsonRound 6 proveSeconds),
     ("peak-rss-bytes", Lean.toJson provePeak),
     ("proof-bytes", Lean.toJson proofBytes.size)])

  TracingTexray.resetPeakTreeRss
  let (verified, verifySeconds) ← timed fun _ =>
    recursionSystem.verify outerClaim proof
  let verifyPeak ← TracingTexray.peakTreeRssBytes
  match verified with
  | .error error =>
    record s!"{label}-outer-verify" (errorJson error)
    return .error s!"{label}: lift proof verification failed: {error}"
  | .ok () =>
    record s!"{label}-outer-verify" (stageJson
      [("seconds", jsonRound 6 verifySeconds),
       ("peak-rss-bytes", Lean.toJson verifyPeak)])

  pure (.ok {
    slot := {
      statement := spec.statement
      subjectCount := spec.subjectCount
      outerClaim
      proof
      proofAddress? := none
      openPreimages := #[innerClaimsBytes, claimBytes]
    }
    proveSeconds
  })

def runJoin (item : ScheduledFold) (left right : AggregateSlot)
    (spec : AggregateSlotSpec) (recursionSystem : Aiur.AiurSystem)
    (joinIdx structuralJoinIdx : Aiur.Bytecode.FunIdx)
    (recursionVk allowed : ByteArray)
    (record : String → Json → IO Unit) : IO (Except String BenchSlot) := do
  let output := spec.statement
  let outputClaimBytes := Ix.Claim.ser output.claim
  let pubInput := MultiStark.joinPubInput allowed outputClaimBytes
  let leftClaimsBytes := MultiStark.serializeClaims #[left.outerClaim]
  let rightClaimsBytes := MultiStark.serializeClaims #[right.outerClaim]
  let preimagesBlob := MultiStark.joinPreimagesBlob
    (left.openPreimages ++ right.openPreimages)
  let trees := if item.structural then
      MultiStark.CheckEnvTrees.structuralAdviceTrees left.statement right.statement output
    else
      MultiStark.CheckEnvTrees.adviceTrees left.statement right.statement output
  let treesBlob := MultiStark.joinTreesBlob trees
  let pathsBlob := if item.structural then
      MultiStark.joinPathsBlob
        (MultiStark.CheckEnvTrees.structuralPathAdvice left.statement right.statement output)
    else MultiStark.joinPathsBlob #[]
  let joinFunIdx := if item.structural then structuralJoinIdx else joinIdx
  let label := if item.structural then "structural-join" else "flat-join"
  let leftProofAdvice ← match recursionSystem.proofToAdviceBytes
      left.outerClaim left.proof with
    | .error error =>
      return .error s!"{label}: left child proof advice encoding failed: {error}"
    | .ok bytes => pure bytes
  let rightProofAdvice ← match recursionSystem.proofToAdviceBytes
      right.outerClaim right.proof with
    | .error error =>
      return .error s!"{label}: right child proof advice encoding failed: {error}"
    | .ok bytes => pure bytes

  IO.println s!"[pair-bench] proving {label}"
  (← IO.getStdout).flush
  TracingTexray.resetPeakTreeRss
  let (proved, proveSeconds) ← timed fun _ =>
    recursionSystem.proveMultiStarkJoin joinFunIdx pubInput
      leftProofAdvice rightProofAdvice recursionVk
      leftClaimsBytes rightClaimsBytes outputClaimBytes allowed
      preimagesBlob treesBlob pathsBlob
  let provePeak ← TracingTexray.peakTreeRssBytes
  let (outerClaim, proof) ← match proved with
    | .error error =>
      record s!"{label}-prove" (errorJson error)
      return .error s!"{label}: prove failed: {error}"
    | .ok result => pure result
  if outerClaim != spec.outerClaim then
    let error := "produced an unexpected outer claim"
    record s!"{label}-prove" (errorJson error)
    return .error s!"{label}: {error}"
  let proofBytes := proof.toBytes
  record s!"{label}-prove" (stageJson
    [("seconds", jsonRound 6 proveSeconds),
     ("peak-rss-bytes", Lean.toJson provePeak),
     ("proof-bytes", Lean.toJson proofBytes.size)])

  TracingTexray.resetPeakTreeRss
  let (verified, verifySeconds) ← timed fun _ =>
    recursionSystem.verify outerClaim proof
  let verifyPeak ← TracingTexray.peakTreeRssBytes
  match verified with
  | .error error =>
    record s!"{label}-verify" (errorJson error)
    return .error s!"{label}: proof verification failed: {error}"
  | .ok () =>
    record s!"{label}-verify" (stageJson
      [("seconds", jsonRound 6 verifySeconds),
       ("peak-rss-bytes", Lean.toJson verifyPeak)])

  pure (.ok {
    slot := {
      statement := output
      subjectCount := spec.subjectCount
      outerClaim
      proof
      proofAddress? := none
      openPreimages := #[outputClaimBytes]
    }
    proveSeconds
  })

structure PairSelection where
  leftBlocks : Array Address
  rightBlocks : Array Address
  leftId : Nat
  rightId : Nat
  leftLabel : String
  rightLabel : String
  expectedLeftSubjects? : Option Nat := none
  expectedRightSubjects? : Option Nat := none
  source : String
  manifestPath? : Option String := none

def usage : String :=
  "usage: bench-aggregate-pair [--ixe E] [--name-a A --name-b B] " ++
  "[--ixes M --shard-a A --shard-b B] " ++
  "[--proof-a ADDR --proof-b ADDR] " ++
  "[--queries N] [--structural-above N] [--json PATH] " ++
  "[--plan-only] [--texray]"

def main (args : List String) : IO UInt32 := do
  let ixePath := (argStr args "--ixe").getD "init.ixe"
  let manifestPath? := argStr args "--ixes"
  let requestedA? := argNat? args "--shard-a"
  let requestedB? := argNat? args "--shard-b"
  if requestedA?.isSome != requestedB?.isSome then
    IO.eprintln "error: --shard-a and --shard-b must be supplied together"
    IO.eprintln usage
    return 2
  if let some requestedA := requestedA? then
    if requestedB? == some requestedA then
      IO.eprintln "error: --shard-a and --shard-b must differ"
      return 2
  if manifestPath?.isNone && requestedA?.isSome then
    IO.eprintln "error: --shard-a/--shard-b require --ixes"
    return 2
  if manifestPath?.isSome &&
      ((argStr args "--name-a").isSome || (argStr args "--name-b").isSome) then
    IO.eprintln "error: --name-a/--name-b select micro-shards and cannot accompany --ixes"
    return 2
  let proofAHex? := argStr args "--proof-a"
  let proofBHex? := argStr args "--proof-b"
  if proofAHex?.isSome != proofBHex?.isSome then
    IO.eprintln "error: --proof-a and --proof-b must be supplied together"
    IO.eprintln usage
    return 2
  let structuralAbove := (argNat? args "--structural-above").getD defaultStructuralAbove
  let queries := (argNat? args "--queries").getD 50
  if queries == 0 then
    IO.eprintln "error: --queries must be positive"
    return 2
  let jsonPath? := argStr args "--json"

  TracingTexray.startSampler 25
  if hasFlag args "--texray" then TracingTexray.init {}

  let env ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error error => IO.eprintln s!"deserialize {ixePath} failed: {error}"; return 1
    | .ok env => pure env
  let selection : PairSelection ← match manifestPath? with
    | none =>
      let nameA := (argStr args "--name-a").getD "False"
      let nameB := (argStr args "--name-b").getD "True"
      let leftBlocks ← match namedMicroShard env nameA with
        | .error error => IO.eprintln error; return 1
        | .ok blocks => pure blocks
      let rightBlocks ← match namedMicroShard env nameB with
        | .error error => IO.eprintln error; return 1
        | .ok blocks => pure blocks
      if leftBlocks == rightBlocks then
        IO.eprintln s!"micro-shard names {nameA} and {nameB} resolve to the same block"
        return 1
      pure {
        leftBlocks, rightBlocks, leftId := 0, rightId := 1
        leftLabel := nameA, rightLabel := nameB
        source := "init-named-microshards"
      }
    | some manifestPath =>
      let rawView ← match Ix.Cli.CheckCmd.parseIxesManifest
          (← IO.FS.readBinFile manifestPath) with
        | .error error => IO.eprintln s!"manifest parse failed: {error}"; return 1
        | .ok view => pure view
      if !(← Ix.Cli.CheckCmd.shardsCover env rawView.shards) then return 1
      let (view, shardCounts) ← match rawView.pruneEmpty env with
        | .error error => IO.eprintln error; return 1
        | .ok result => pure result
      let (leftDense, rightDense) ← match requestedA?, requestedB? with
        | none, none => match smallestSiblingPair? view.aggregationTree shardCounts with
          | some pair => pure pair
          | none =>
            IO.eprintln "manifest has no direct sibling leaf pair"
            return 1
        | some requestedA, some requestedB =>
          let some denseA := view.shardIds.findIdx? (· == requestedA)
            | IO.eprintln s!"manifest has no retained shard {requestedA}"; return 1
          let some denseB := view.shardIds.findIdx? (· == requestedB)
            | IO.eprintln s!"manifest has no retained shard {requestedB}"; return 1
          pure (denseA, denseB)
        | _, _ =>
          IO.eprintln "internal: partial shard override passed validation"
          return 1
      let leftOriginal := view.shardIds[leftDense]!
      let rightOriginal := view.shardIds[rightDense]!
      pure {
        leftBlocks := view.shards[leftDense]!
        rightBlocks := view.shards[rightDense]!
        leftId := leftOriginal
        rightId := rightOriginal
        leftLabel := s!"shard {leftOriginal}"
        rightLabel := s!"shard {rightOriginal}"
        expectedLeftSubjects? := some shardCounts[leftDense]!
        expectedRightSubjects? := some shardCounts[rightDense]!
        source := if requestedA?.isSome then "explicit-manifest-pair"
          else "smallest-manifest-siblings"
        manifestPath? := some manifestPath
      }
  let leftProofHex? := proofAHex?
  let rightProofHex? := proofBHex?
  let leftBlocks := selection.leftBlocks
  let rightBlocks := selection.rightBlocks
  let leftPrepared ← match prepareShard env leftBlocks with
    | .error error => IO.eprintln s!"prepare {selection.leftLabel}: {error}"; return 1
    | .ok prepared => pure prepared
  let rightPrepared ← match prepareShard env rightBlocks with
    | .error error => IO.eprintln s!"prepare {selection.rightLabel}: {error}"; return 1
    | .ok prepared => pure prepared
  if selection.expectedLeftSubjects?.any
      (· != leftPrepared.statement.subjectCount) ||
      selection.expectedRightSubjects?.any
        (· != rightPrepared.statement.subjectCount) then
      IO.eprintln "internal: reconstructed subject counts differ from the manifest view"
      return 1

  let compactOps : Array FoldOp := #[.leaf 0, .leaf 1, .join 0 1]
  let plan ← match schedulePlan compactOps
      #[leftPrepared.statement.subjectCount, rightPrepared.statement.subjectCount]
      structuralAbove with
    | .error error => IO.eprintln error; return 1
    | .ok plan => pure plan
  let some joinItem := plan[2]?
    | IO.eprintln "internal: compact pair plan has no join slot"; return 1
  let mode := if joinItem.structural then "structural" else "flat"
  let baseProofSource := if proofAHex?.isSome then "reused" else "generated"
  IO.println (s!"[pair-bench] {selection.leftLabel}, {selection.rightLabel}: " ++
    s!"{leftPrepared.statement.subjectCount} + {rightPrepared.statement.subjectCount} " ++
    s!"subjects; {mode} join (threshold > {structuralAbove}); " ++
    s!"{baseProofSource} base proofs")
  if hasFlag args "--plan-only" then return 0

  let metadata : List (String × Json) :=
    [("schema-version", Lean.toJson (2 : Nat)),
     ("ixe", Json.str ixePath),
     ("ixes", selection.manifestPath?.map Json.str |>.getD Json.null),
     ("left-shard", Lean.toJson selection.leftId),
     ("right-shard", Lean.toJson selection.rightId),
     ("left-label", Json.str selection.leftLabel),
     ("right-label", Json.str selection.rightLabel),
     ("left-subjects", Lean.toJson leftPrepared.statement.subjectCount),
     ("right-subjects", Lean.toJson rightPrepared.statement.subjectCount),
     ("pair-source", Json.str selection.source),
     ("base-proof-source", Json.str baseProofSource),
     ("queries", Lean.toJson queries),
     ("join-mode", Json.str mode),
     ("structural-above", Lean.toJson structuralAbove)]
  let stagesRef ← IO.mkRef (#[] : Array (String × Json))
  let record (name : String) (row : Json) : IO Unit := do
    let stages := (← stagesRef.get).push (name, row)
    stagesRef.set stages
    writeReport jsonPath? metadata "running" stages
    IO.println s!"[pair-bench] recorded {name}"
  writeReport jsonPath? metadata "running" #[]

  IO.println "[pair-bench] compiling IxVM and MultiStark systems"
  let ixvmCompiled ← match ← compileToplevel "IxVM" IxVM.ixVM with
    | .error error => IO.eprintln error; return 1
    | .ok compiled => pure compiled
  let recursionCompiled ← match ← compileToplevel "MultiStark recursion"
      MultiStark.multiStark with
    | .error error => IO.eprintln error; return 1
    | .ok compiled => pure compiled
  let verifyIdx := ixvmCompiled.getFuncIdx `verify_claim |>.get!
  let liftIdx := recursionCompiled.getFuncIdx `verify_multi_stark_proof |>.get!
  let joinIdx := recursionCompiled.getFuncIdx `join_two |>.get!
  let structuralJoinIdx := recursionCompiled.getFuncIdx `join_two_structural |>.get!
  let friParameters := benchmarkFriParameters queries
  let recursionParameters : MultiStark.RecursionParameters := {
    commitment := Aiur.defaultCommitmentParameters
    fri := friParameters
  }
  let ixvmSystem := Aiur.AiurSystem.build ixvmCompiled.bytecode
    Aiur.defaultCommitmentParameters friParameters
  let recursionSystem := MultiStark.buildRecursionSystem recursionCompiled.bytecode
    recursionParameters
  let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
    | .error error => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {error}"; return 1
    | .ok handle => pure handle
  let ixvmVk := ixvmSystem.vkBytes
  let recursionVk := recursionSystem.vkBytes
  let allowed := MultiStark.allowedBlob ixvmVk verifyIdx recursionVk liftIdx
    joinIdx structuralJoinIdx
  let specs ← match buildAggregateSlotSpecs plan #[leftPrepared, rightPrepared]
      ixvmVk recursionVk allowed verifyIdx liftIdx joinIdx structuralJoinIdx
      recursionParameters with
    | .error error => IO.eprintln s!"prepare pair slots: {error}"; return 1
    | .ok specs => pure specs
  let some leftSpec := specs[0]?
    | IO.eprintln "internal: pair specs have no left lift"; return 1
  let some rightSpec := specs[1]?
    | IO.eprintln "internal: pair specs have no right lift"; return 1
  let some rootSpec := specs[2]?
    | IO.eprintln "internal: pair specs have no join"; return 1

  let leftBase ← match leftProofHex? with
    | some proofHex =>
      match ← reuseBaseProof "base-left" proofHex leftPrepared.claim record with
      | .error error =>
        IO.eprintln error
        writeReport jsonPath? metadata "error" (← stagesRef.get)
        return 1
      | .ok result => pure result
    | none =>
      let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks env leftBlocks
      match ← runBaseProof "base-left" envHandle owned leftPrepared.claim
          ixvmSystem verifyIdx record with
      | .error error =>
        IO.eprintln error
        writeReport jsonPath? metadata "error" (← stagesRef.get)
        return 1
      | .ok result => pure result
  let rightBase ← match rightProofHex? with
    | some proofHex =>
      match ← reuseBaseProof "base-right" proofHex rightPrepared.claim record with
      | .error error =>
        IO.eprintln error
        writeReport jsonPath? metadata "error" (← stagesRef.get)
        return 1
      | .ok result => pure result
    | none =>
      let owned := Ix.Cli.CheckCmd.ownedConstsForBlocks env rightBlocks
      match ← runBaseProof "base-right" envHandle owned rightPrepared.claim
          ixvmSystem verifyIdx record with
      | .error error =>
        IO.eprintln error
        writeReport jsonPath? metadata "error" (← stagesRef.get)
        return 1
      | .ok result => pure result

  let left ← match ← runLift "lift-left" leftPrepared leftBase.wrapper leftSpec
      ixvmSystem recursionSystem verifyIdx liftIdx ixvmVk record with
    | .error error =>
      IO.eprintln error
      writeReport jsonPath? metadata "error" (← stagesRef.get)
      return 1
    | .ok slot => pure slot
  let right ← match ← runLift "lift-right" rightPrepared rightBase.wrapper rightSpec
      ixvmSystem recursionSystem verifyIdx liftIdx ixvmVk record with
    | .error error =>
      IO.eprintln error
      writeReport jsonPath? metadata "error" (← stagesRef.get)
      return 1
    | .ok slot => pure slot
  let root ← match ← runJoin joinItem left.slot right.slot rootSpec
      recursionSystem joinIdx structuralJoinIdx recursionVk allowed record with
    | .error error =>
      IO.eprintln error
      writeReport jsonPath? metadata "error" (← stagesRef.get)
      return 1
    | .ok slot => pure slot

  let expectedStatement := if joinItem.structural then
      leftPrepared.statement.joinStructural rightPrepared.statement
    else leftPrepared.statement.join rightPrepared.statement
  if root.slot.statement.claim != expectedStatement.claim then
    IO.eprintln "pair root statement differs from independent host reconstruction"
    writeReport jsonPath? metadata "error" (← stagesRef.get)
    return 1

  -- Cheap negative control: the valid proof must reject under a one-word
  -- mutation of its exact outer claim.
  let some outerWord := root.slot.outerClaim[2]?
    | IO.eprintln "internal: aggregate outer claim is shorter than three words"; return 1
  let wrongOuter := root.slot.outerClaim.set! 2 (outerWord + 1)
  let (wrongResult, negativeSeconds) ← timed fun _ =>
    recursionSystem.verify wrongOuter root.slot.proof
  match wrongResult with
  | .ok () =>
    record "negative-control" (errorJson "proof accepted a mutated outer claim")
    writeReport jsonPath? metadata "error" (← stagesRef.get)
    return 1
  | .error _ =>
    record "negative-control" (stageJson [("seconds", jsonRound 6 negativeSeconds)])

  let baseProveSeconds := leftBase.proveSeconds + rightBase.proveSeconds
  let recursiveProveSeconds := left.proveSeconds + right.proveSeconds + root.proveSeconds
  let serialProveSeconds := baseProveSeconds + recursiveProveSeconds
  let parallelLowerBound :=
    max (leftBase.proveSeconds + left.proveSeconds)
      (rightBase.proveSeconds + right.proveSeconds) + root.proveSeconds
  let rootBytes := root.slot.proof.toBytes
  let summary := stageJson
    [("base-prove-seconds", jsonRound 6 baseProveSeconds),
     ("recursive-prove-seconds", jsonRound 6 recursiveProveSeconds),
     ("serial-total-prove-seconds", jsonRound 6 serialProveSeconds),
     ("parallel-branch-lower-bound-seconds", jsonRound 6 parallelLowerBound),
     ("root-proof-bytes", Lean.toJson rootBytes.size),
     ("root-proof-digest", Json.str (toString (Address.blake3 rootBytes))),
     ("subjects", Lean.toJson root.slot.subjectCount),
     ("retains-assumptions", Lean.toJson root.slot.statement.assumptions.isSome)]
  record "summary" summary
  writeReport jsonPath? metadata "ok" (← stagesRef.get)
  IO.println (s!"[pair-bench] OK: serial base proving {baseProveSeconds}s; " ++
    s!"recursive proving {recursiveProveSeconds}s; total {serialProveSeconds}s; " ++
    s!"parallel branch lower bound {parallelLowerBound}s; root {rootBytes.size} bytes")
  pure 0

end Benchmarks.AggregatePair

def main (args : List String) : IO UInt32 :=
  Benchmarks.AggregatePair.main args
