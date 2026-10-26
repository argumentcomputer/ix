module
public import Ix.Cli.FormalAiur
public import Ix.Aggr.Verification

/-! Application scheduling for the separate formal recursive verifier. The
host constructs advice; every fold relation and child proof is checked again
by ordinary Aiur code. No legacy execution or compiler is used on this path. -/
public section
namespace Ix.Cli.FormalAggregate
open Lean Aggr FormalAiur

def artifact (p : Cli.Parsed) : IO String :=
  compiledArtifact p "aggr-artifact" "IX_AGGR_ARTIFACT"
    "MultiStark/.lake/build/bin/stark-export" "stark-export"
    "MultiStark/MultiStark/Aggregate.aiur" "export-trace" #["--aggregate"]

def host : IO String := rustHost "stark-verifier" "stark-verifier" "IX_STARK_HOST"

def invoke (artifactPath mode : String) (input : Json) (output : String)
    (rows : Nat := 65536) (retention : String := "regenerate") : IO Unit :=
  IO.FS.withTempFile fun h path => do
    h.putStr input.compress
    h.flush
    command (← host) #[mode, artifactPath, path.toString, output, toString rows, retention]

structure Identity where
  key : ByteArray
  index : Nat

def identity (host artifact : String) : IO Identity :=
  IO.FS.withTempDir fun dir => do
    command host #["key", artifact, dir.toString]
    let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / "identity.json")))
    let channel : Nat ← IO.ofExcept (json.getObjValAs? Nat "call_channel")
    unless channel == 1 do throw (IO.userError "unexpected formal call namespace")
    let key ← IO.FS.readBinFile (dir / "key.bin")
    let index ← IO.ofExcept (json.getObjValAs? Nat "function_index")
    return { key, index }

structure Context where
  ixvmArtifact : String
  aggrArtifact : String
  ixvm : Identity
  aggr : Identity
  allowed : ByteArray

def context (p : Cli.Parsed) : IO Context := do
  let ixvmArtifact ← FormalAiur.artifact p
  let aggrArtifact ← artifact p
  let ixvm ← identity (← FormalAiur.host) ixvmArtifact
  let aggr ← identity (← host) aggrArtifact
  let allowed := Aggr.allowedBlob ixvm.key ixvm.index aggr.key aggr.index
  return { ixvmArtifact, aggrArtifact, ixvm, aggr, allowed }

def outerClaim (ctx : Context) (kind : ChildKind) (claim : Ix.Claim) : Array LegacyAiur.G :=
  let bytes := Ix.Claim.ser claim
  match kind with
  | .ixvm => #[1, .ofNat ctx.ixvm.index] ++ LegacyMultiStark.digestGs bytes
  | .aggr => #[1, .ofNat ctx.aggr.index] ++ Aggr.pubInput ctx.allowed bytes

def rawProof (kind : ChildKind) (proof : ByteArray) : IO ByteArray := do
  let magic := (if kind == .ixvm then "IXAIUR2\x00" else "IXAGGR2\x00").toUTF8
  unless proof.extract 0 magic.size == magic do
    throw (IO.userError "proof belongs to a different backend or recursion kind")
  return proof.extract magic.size proof.size

def verifyWrapper (ctx : Context) (kind : ChildKind) (wrapper : Ixon.Proof) : IO Unit := do
  if kind == .ixvm then return ← FormalAiur.verifyWrapper ctx.ixvmArtifact wrapper
  let .checkEnv _ _ := wrapper.claim | throw (IO.userError "aggregate must carry CheckEnv")
  let raw ← rawProof .aggr wrapper.proof
  IO.FS.withTempFile fun _ path => do
    IO.FS.writeBinFile path raw
    invoke ctx.aggrArtifact "verify"
      (invocation (Aggr.pubInput ctx.allowed (Ix.Claim.ser wrapper.claim)) default "MultiStark::ix_aggr")
      path.toString

structure Node where
  statement : CheckEnvTrees
  kind : ChildKind
  wrapper : Ixon.Proof

def childAdvice (ctx : Context) (io : LegacyAiur.IOBuffer) (slot : Nat) (node : Node) : IO LegacyAiur.IOBuffer := do
  let io := extendVk io node.kind (if node.kind == .ixvm then ctx.ixvm.key else ctx.aggr.key)
  return extendChild io slot (← rawProof node.kind node.wrapper.proof)
    (LegacyMultiStark.serializeClaims #[outerClaim ctx node.kind node.wrapper.claim])

/-- Build a wrap/pair witness with the same manifest fold semantics used by
the independent verifier. Host tree operations never bypass circuit checks. -/
def advice (ctx : Context) (left : Node) (right : Option Node)
    (output : CheckEnvTrees) (structural : Bool) : IO LegacyAiur.IOBuffer := do
  let shape := match right with
    | none => shapeCode (left.kind, none)
    | some r => if structural then structuralShapeCode left.kind r.kind
        else shapeCode (left.kind, some r.kind)
  let mut io ← childAdvice ctx (extendIdentity default ctx.allowed shape) 0 left
  if let some right := right then
    io ← childAdvice ctx io 1 right
    let outputBytes := Ix.Claim.ser output.claim
    io := extendOutputClaim io outputBytes
    for c in #[left.wrapper.claim, right.wrapper.claim] do
      io := extendPreimage io (Ix.Claim.ser c)
    let trees := if structural then left.statement.structuralAdviceTrees right.statement output
      else left.statement.adviceTrees right.statement output
    for tree in trees do io := extendTree io tree
    if structural then
      for (addr, path) in left.statement.structuralPathAdvice right.statement output do
        io := extendPath io addr path
  return io

private def persist (wrapper : Ixon.Proof) : IO Address := do
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser wrapper.claim))
  StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))

def cachedNode (ctx : Context) (output : CheckEnvTrees) : IO (Option Node) := do
  let cache ← StoreIO.toIO (Store.cacheDir "formal-aggregates")
  let key := Address.blake3 (ctx.aggr.key ++ LegacyMultiStark.serializeClaims #[outerClaim ctx .aggr output.claim])
  if let some addr ← ShardProofIndex.readAddress cache key then
    try
      let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
      unless wrapper.claim == output.claim do throw (IO.userError "cached aggregate claim mismatch")
      verifyWrapper ctx .aggr wrapper
      IO.println s!"[aiur aggregate] reused {addr}"
      return some { statement := output, kind := .aggr, wrapper }
    catch e => IO.eprintln s!"[aiur aggregate] ignored cache entry: {e}"
  return none

def proveAdvice (ctx : Context) (bytes : ByteArray) (io : LegacyAiur.IOBuffer)
    (options : HostOptions) : IO ByteArray := do
  let input := invocation (Aggr.pubInput ctx.allowed bytes) io "MultiStark::ix_aggr"
  IO.FS.withTempDir fun dir => do
    let binary ← rustHost "stark-verifier" "stark-verifier" "IX_STARK_HOST" options.device
    let code ← runHost binary ctx.aggrArtifact "prove" input dir.toString options
    unless code == 0 do
      let report := dir / "report.json"
      if ← report.pathExists then IO.eprintln (← IO.FS.readFile report)
      throw (IO.userError s!"recursive prover exited {code}; reduce --range or increase --max-ram")
    IO.FS.readBinFile (dir / "proof.bin")

def proveNode (p : Cli.Parsed) (ctx : Context) (output : CheckEnvTrees)
    (left : Node) (right : Option Node := none) (structural : Bool := false)
    (options : HostOptions := {}) (force : Bool := false) : IO Node := do
  let cache ← StoreIO.toIO (Store.cacheDir "formal-aggregates")
  let key := Address.blake3 (ctx.aggr.key ++ LegacyMultiStark.serializeClaims #[outerClaim ctx .aggr output.claim])
  unless force || p.hasFlag "no-cache" do
    if let some node ← cachedNode ctx output then return node
  let io ← advice ctx left right output structural
  let proof ← proveAdvice ctx (Ix.Claim.ser output.claim) io options
  let wrapper : Ixon.Proof := { claim := output.claim, proof := "IXAGGR2\x00".toUTF8 ++ proof }
  unless p.hasFlag "no-write" do
    let addr ← persist wrapper
    unless p.hasFlag "no-cache" do ShardProofIndex.writeAddress cache key addr
    IO.println s!"[formal aggregate] persisted {addr}"
  return { statement := output, kind := .aggr, wrapper }

structure RangeNode where
  statement : ByteArray
  proof : ByteArray

def rangeClaims (ctx : Context) (statement : ByteArray) : ByteArray :=
  LegacyMultiStark.serializeClaims #[#[1, .ofNat ctx.aggr.index] ++ Aggr.pubInput ctx.allowed statement]

def verifyRange (ctx : Context) (node : RangeNode) : IO Unit :=
  IO.FS.withTempFile fun _ path => do
    IO.FS.writeBinFile path node.proof
    invoke ctx.aggrArtifact "verify"
      (invocation (pubInput ctx.allowed node.statement) default "MultiStark::ix_aggr") path.toString

def proveRange (p : Cli.Parsed) (ctx : Context) (statement : ByteArray)
    (io : LegacyAiur.IOBuffer) (options : HostOptions) : IO RangeNode := do
  let cache ← StoreIO.toIO (Store.cacheDir "formal-ranges")
  let key := Address.blake3 (ctx.aggr.key ++ rangeClaims ctx statement)
  unless p.hasFlag "no-cache" do
    if let some addr ← ShardProofIndex.readAddress cache key then
      try
        let node : RangeNode := { statement, proof := ← StoreIO.toIO (Store.read addr) }
        verifyRange ctx node
        return node
      catch e => IO.eprintln s!"[aiur range] ignored cache: {e}"
  let proof ← proveAdvice ctx statement io options
  unless p.hasFlag "no-write" || p.hasFlag "no-cache" do
    let addr ← StoreIO.toIO (Store.write proof)
    ShardProofIndex.writeAddress cache key addr
  return { statement, proof }

def rangeChild (ctx : Context) (io : LegacyAiur.IOBuffer) (slot : Nat) (node : RangeNode) : LegacyAiur.IOBuffer :=
  extendPreimage (extendChild (extendVk io .aggr ctx.aggr.key) slot node.proof (rangeClaims ctx node.statement)) node.statement

/-- The native host only slices serialized advice. Shapes 10, 11 and 12 in
ordinary Aiur verify every range, sum, boundary, and final public claim. -/
def wrapRanges (p : Cli.Parsed) (ctx : Context) (source : Node)
    (options : HostOptions) (size : Nat) (force : Bool := false) : IO Node := do
  unless force || p.hasFlag "no-cache" do
    if let some node ← cachedNode ctx source.statement then return node
  unless source.kind == .ixvm && size > 0 do throw (IO.userError "range wrapping requires an IxVM proof and positive range size")
  IO.FS.withTempDir fun dir => do
    let raw := dir / "source.bin"
    IO.FS.writeBinFile raw (← rawProof .ixvm source.wrapper.proof)
    command (← host) #["ranges", raw.toString, dir.toString, toString size]
    let specs ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / "ranges.json")) >>= Json.getArr?)
    let preamble ← IO.FS.readBinFile (dir / "preamble.bin")
    let mut nodes : Array RangeNode := #[]
    for i in [:specs.size] do
      let children ← IO.ofExcept (specs[i]!.getObjValAs? (Array Nat) "children")
      let statement ← IO.FS.readBinFile (dir / s!"{i}.statement")
      let io ← if children.isEmpty then do
          let io := extendVk (extendIdentity default ctx.allowed 10) .ixvm ctx.ixvm.key
          let io := extendChild io 0 preamble ByteArray.empty
          pure (extendChild io 1 (← IO.FS.readBinFile (dir / s!"{i}.proofs")) ByteArray.empty)
        else do
          unless children.size == 2 do throw (IO.userError "invalid range plan")
          let some l := nodes[children[0]!]? | throw (IO.userError "missing range child")
          let some r := nodes[children[1]!]? | throw (IO.userError "missing range child")
          pure (rangeChild ctx (rangeChild ctx (extendIdentity default ctx.allowed 11) 0 l) 1 r)
      let node ← proveRange p ctx statement (extendOutputClaim io statement) options
      nodes := nodes.push node
    let some rangeRoot := nodes.back? | throw (IO.userError "empty range plan")
    let io := rangeChild ctx (extendIdentity default ctx.allowed 12) 0 rangeRoot
    let io := extendVk (extendChild io 1 preamble ByteArray.empty) .ixvm ctx.ixvm.key
    let proof ← proveAdvice ctx (Ix.Claim.ser source.statement.claim) io options
    let wrapper : Ixon.Proof := { claim := source.statement.claim, proof := "IXAGGR2\x00".toUTF8 ++ proof }
    unless p.hasFlag "no-write" do
      let addr ← persist wrapper
      unless p.hasFlag "no-cache" do
        let key := Address.blake3 (ctx.aggr.key ++ rangeClaims ctx (Ix.Claim.ser source.statement.claim))
        ShardProofIndex.writeAddress (← StoreIO.toIO (Store.cacheDir "formal-aggregates")) key addr
    return { statement := source.statement, kind := .aggr, wrapper }

def traceShards (node : Node) : IO Nat :=
  IO.FS.withTempFile fun _ path => do
    IO.FS.writeBinFile path (← rawProof node.kind node.wrapper.proof)
    let result ← IO.Process.output { cmd := ← host, args := #["inspect", path.toString] }
    unless result.exitCode == 0 do throw (IO.userError result.stderr)
    IO.ofExcept (Json.parse result.stdout >>= fun j => j.getObjValAs? Nat "shards")

/-- Dependency closure in a topologically ordered fold plan. -/
def neededSlots (plan : Array Reference.ScheduledFold) (root : Nat) : Except String (Array Bool) := do
  unless root < plan.size do throw "slot out of range"
  let mut needed := (Array.replicate plan.size false).set! root true
  for i in (List.range (root + 1)).reverse do
    if needed[i]! then
      let some item := plan[i]? | throw "missing plan slot"
      if let .join l r := item.op then
        unless l < i && r < i do throw "aggregation plan is not topologically ordered"
        needed := needed.set! l true |>.set! r true
  return needed

def manifest (p : Cli.Parsed) : IO (Ixon.Env × Ix.Shard.IxesManifestView × Array Nat) := do
  let some envPath := (p.flag? "ixe").map (·.as! String) | throw (IO.userError "aggregate requires --ixe")
  let some path := (p.flag? "ixes").map (·.as! String) | throw (IO.userError "aggregate requires --ixes")
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile envPath))
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile path))
  unless ← Ix.Shard.shardsCover env view.shards do throw (IO.userError "invalid manifest coverage")
  let (view, counts) ← IO.ofExcept (view.pruneEmpty env)
  return (env, view, counts)

def run (p : Cli.Parsed) : IO UInt32 := do
  rejectFlags p #["exec-ahead", "texray"]
  let (env, view, counts) ← manifest p
  let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
  let plan ← IO.ofExcept (Reference.schedulePlan view.aggregationTree.foldPlan counts above (p.hasFlag "direct-joins"))
  let subtree := (p.flag? "subtree").map (·.as! Nat)
  let reprove := (p.flag? "reprove-slot").map (·.as! Nat)
  if subtree.isSome && (reprove.isSome || p.hasFlag "wrap-root") then
    throw (IO.userError "--subtree cannot be combined with --reprove-slot or --wrap-root")
  if reprove.isSome && (p.hasFlag "no-cache" || p.hasFlag "plan-only") then
    throw (IO.userError "--reprove-slot requires caches and cannot be combined with --plan-only")
  let rootSlot := (subtree.orElse fun _ => reprove).getD (plan.size - 1)
  let needed ← IO.ofExcept (neededSlots plan rootSlot)
  if p.hasFlag "plan-only" then
    let mut shards : Array String := #[]
    for i in [:plan.size] do
      if needed[i]! then
        let some item := plan[i]? | throw (IO.userError "missing plan slot")
        IO.println s!"slot {i}: {repr item}"
        if let .leaf k := item.op then shards := shards.push (toString view.shardIds[k]!)
    if let some n := subtree then IO.println s!"subtree {n} shards: {String.intercalate "," shards.toList}"
    return 0
  let jobs := min plan.size (← jobCount p)
  let options ← hostOptions p jobs
  let _ ← rustHost "stark-verifier" "stark-verifier" "IX_STARK_HOST" options.device
  let ctx ← context p
  let prepared ← IO.ofExcept (Reference.prepareShards env view.shards view.shardIds)
  let mut statements : Array CheckEnvTrees := #[]
  for item in plan do
    let statement ← match item.op with
      | .leaf shard => do
        let some source := prepared[shard]? | throw (IO.userError "missing shard")
        pure source.statement
      | .join l r => do
        let some left := statements[l]? | throw (IO.userError "missing left statement")
        let some right := statements[r]? | throw (IO.userError "missing right statement")
        pure (if item.structural then left.joinStructural right else left.join right)
    statements := statements.push statement
  let mut byClaim : Std.HashMap Address Ixon.Proof := {}
  let mut supplied : Std.HashMap Address Ixon.Proof := {}
  for hex in p.variableArgsAs! String do
    let some addr := Address.fromString hex | throw (IO.userError "invalid shard proof address")
    let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
    let kind := if wrapper.proof.extract 0 8 == "IXAIUR2\x00".toUTF8 then ChildKind.ixvm else .aggr
    let matchesPlan := if kind == .ixvm then prepared.any (·.claim == wrapper.claim)
      else statements.any (·.claim == wrapper.claim)
    unless matchesPlan do throw (IO.userError s!"{addr}: not a statement in this manifest plan")
    let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
    if byClaim.contains digest || supplied.contains digest then throw (IO.userError "duplicate statement proof")
    verifyWrapper ctx kind wrapper
    if kind == .ixvm then byClaim := byClaim.insert digest wrapper
    else supplied := supplied.insert digest wrapper
  let rangeSize := ((p.flag? "range").map (·.as! Nat)).getD 0
  let mut nodes : Array (Option Node) := Array.replicate plan.size none
  let mut pending := Array.replicate plan.size false |>.set! rootSlot true
  -- Verified caches are dependency boundaries. Reproving a slot requires its
  -- immediate aggregate children to be present; it never quietly reproves them.
  for i in (List.range (rootSlot + 1)).reverse do
    let some item := plan[i]? | throw (IO.userError "missing plan slot")
    let some statement := statements[i]? | throw (IO.userError "missing statement")
    if pending[i]! && reprove != some i then
      if let some wrapper := supplied.get? (Address.blake3 (Ix.Claim.ser statement.claim)) then
        nodes := nodes.set! i (some { statement, kind := .aggr, wrapper })
      else if item.kind == .aggr && !p.hasFlag "no-cache" then
        if let some cached ← cachedNode ctx statement then nodes := nodes.set! i (some cached)
    if pending[i]! && nodes[i]!.isNone then
      if let .join l r := item.op then pending := pending.set! l true |>.set! r true
  if let some slot := reprove then
    let some item := plan[slot]? | throw (IO.userError "missing slot")
    if let .join l r := item.op then
      for child in #[l, r] do
        let some item := plan[child]? | throw (IO.userError "missing child")
        if item.kind == .aggr && nodes[child]!.isNone then
          throw (IO.userError s!"--reprove-slot requires verified cached child {child}")
  while nodes[rootSlot]!.isNone do
    let ready := (Array.range plan.size).filter fun i => pending[i]! && nodes[i]!.isNone &&
      (plan[i]?.any fun item => match item.op with
      | .leaf _ => true
      | .join l r => nodes[l]!.isSome && nodes[r]!.isSome)
    if ready.isEmpty then throw (IO.userError "aggregate plan has no ready slot")
    let wave := ready.extract 0 (max jobs 1)
    let results ← boundedMap jobs wave fun members slot => do
      let options := options.forWave jobs members
      let some item := plan[slot]? | throw (IO.userError "missing slot")
      IO.println s!"[aiur aggregate] slot {slot}/{plan.size}: shape {item.shape?}"
      let some output := statements[slot]? | throw (IO.userError "missing statement")
      let node ← match item.op with
      | .leaf shard => do
        let some source := prepared[shard]? | throw (IO.userError "missing shard")
        let some wrapper := byClaim.get? (Address.blake3 (Ix.Claim.ser source.claim))
          | throw (IO.userError s!"missing proof of shard {view.shardIds[shard]!}")
        let raw : Node := { statement := source.statement, kind := .ixvm, wrapper }
        if item.kind == .ixvm then pure raw
        else if rangeSize > 0 && (← traceShards raw) > rangeSize then wrapRanges p ctx raw options rangeSize (reprove == some slot)
        else proveNode p ctx output raw none false options (reprove == some slot)
      | .join l r => do
        let some left := nodes[l]! | throw (IO.userError "missing left child")
        let some right := nodes[r]! | throw (IO.userError "missing right child")
        proveNode p ctx output left (some right) item.structural options (reprove == some slot)
      return (slot, node)
    for (slot, node) in results do nodes := nodes.set! slot (some node)
  let some completed := nodes[rootSlot]! | throw (IO.userError "missing aggregate root")
  let mut root := completed
  if subtree.isNone && reprove.isNone then
    let count ← IO.ofExcept (auditAggregateConstants env root.statement)
    IO.println s!"[aiur aggregate] verified coverage of {count} constants, no undischarged assumptions"
    if p.hasFlag "wrap-root" then
      let mut count ← traceShards root
      while count > 1 do
        root ← proveNode p ctx root.statement root none false options true
        let next ← traceShards root
        unless next < count do
          throw (IO.userError s!"root wrapping stopped at {next} shards without shrinking; increase --shard-rows")
        count := next
  verifyWrapper ctx root.kind root.wrapper
  unless p.hasFlag "no-write" do IO.println (toString (← persist root.wrapper))
  return 0

def verify (p : Cli.Parsed) : IO UInt32 := do
  rejectFlags p #["shard", "record"]
  let ctx ← context p
  let expected ← match (p.flag? "ixe").map (·.as! String), (p.flag? "ixes").map (·.as! String) with
  | none, none => pure none
  | none, some _ => throw (IO.userError "--ixes requires --ixe")
  | some path, none => do
    let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
    let some subjects := LegacyIxVM.ClaimHarness.envCanonicalTree env | throw (IO.userError "empty environment")
    let statement : CheckEnvTrees := { subjects, assumptions := none }
    let _ ← IO.ofExcept (auditAggregateConstants env statement)
    pure (some statement.claim)
  | some _, some _ => do
    let (env, view, _) ← manifest p
    let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
    let root ← IO.ofExcept (Reference.expectedFromManifest env view above)
    let _ ← IO.ofExcept (auditAggregateConstants env root)
    pure (some root.claim)
  let proofs := p.variableArgsAs! String
  if proofs.isEmpty then throw (IO.userError "expected an aggregate proof address")
  for hex in proofs do
    let some addr := Address.fromString hex | throw (IO.userError "invalid aggregate address")
    let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
    unless expected.all (· == wrapper.claim) do throw (IO.userError "aggregate does not match the requested environment/manifest")
    verifyWrapper ctx .aggr wrapper
    IO.println s!"ok: aggregate {addr} verifies {wrapper.claim}"
  return 0

end Ix.Cli.FormalAggregate
end
