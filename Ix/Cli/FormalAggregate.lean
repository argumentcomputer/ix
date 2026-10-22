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

def host : IO String := do
  if let some path ← IO.getEnv "IX_STARK_HOST" then return path
  let path := System.FilePath.mk "target/release/stark-verifier"
  unless ← path.pathExists do
    command "cargo" #["build", "--release", "--locked", "-p", "stark-verifier", "--features", "parallel"]
  return path.toString

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

def proveNode (p : Cli.Parsed) (ctx : Context) (output : CheckEnvTrees)
    (left : Node) (right : Option Node := none) (structural : Bool := false) : IO Node := do
  let cache ← StoreIO.toIO (Store.cacheDir "formal-aggregates")
  let key := Address.blake3 (ctx.aggr.key ++ LegacyMultiStark.serializeClaims #[outerClaim ctx .aggr output.claim])
  unless p.hasFlag "no-cache" do
    if let some addr ← ShardProofIndex.readAddress cache key then
      try
        let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
        unless wrapper.claim == output.claim do throw (IO.userError "cached aggregate claim mismatch")
        verifyWrapper ctx .aggr wrapper
        IO.println s!"[formal aggregate] reused {addr}"
        return { statement := output, kind := .aggr, wrapper }
      catch e => IO.eprintln s!"[formal aggregate] ignored cache entry: {e}"
  let io ← advice ctx left right output structural
  let input := invocation (Aggr.pubInput ctx.allowed (Ix.Claim.ser output.claim)) io "MultiStark::ix_aggr"
  let wrapper ← IO.FS.withTempDir fun dir => do
    invoke ctx.aggrArtifact "prove" input dir.toString (← rows p) (← retention p)
    let proof ← IO.FS.readBinFile (dir / "proof.bin")
    return { claim := output.claim, proof := "IXAGGR2\x00".toUTF8 ++ proof : Ixon.Proof }
  unless p.hasFlag "no-write" do
    let addr ← persist wrapper
    unless p.hasFlag "no-cache" do ShardProofIndex.writeAddress cache key addr
    IO.println s!"[formal aggregate] persisted {addr}"
  return { statement := output, kind := .aggr, wrapper }

def manifest (p : Cli.Parsed) : IO (Ixon.Env × Ix.Shard.IxesManifestView × Array Nat) := do
  let some envPath := (p.flag? "ixe").map (·.as! String) | throw (IO.userError "aggregate requires --ixe")
  let some path := (p.flag? "ixes").map (·.as! String) | throw (IO.userError "aggregate requires --ixes")
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile envPath))
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile path))
  unless ← Ix.Shard.shardsCover env view.shards do throw (IO.userError "invalid manifest coverage")
  let (view, counts) ← IO.ofExcept (view.pruneEmpty env)
  return (env, view, counts)

def run (p : Cli.Parsed) : IO UInt32 := do
  rejectFlags p #["jobs", "max-ram", "exec-ahead", "range", "wrap-root", "subtree", "reprove-slot", "texray"]
  let (env, view, counts) ← manifest p
  let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
  let plan ← IO.ofExcept (Reference.schedulePlan view.aggregationTree.foldPlan counts above (p.hasFlag "direct-joins"))
  if p.hasFlag "plan-only" then
    for (item, i) in plan.mapIdx fun i item => (item, i) do
      IO.println s!"slot {i}: {repr item}"
    return 0
  let ctx ← context p
  let prepared ← IO.ofExcept (Reference.prepareShards env view.shards view.shardIds)
  let mut byClaim : Std.HashMap Address Ixon.Proof := {}
  for hex in p.variableArgsAs! String do
    let some addr := Address.fromString hex | throw (IO.userError "invalid shard proof address")
    let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
    unless prepared.any (·.claim == wrapper.claim) do throw (IO.userError s!"{addr}: not a manifest shard")
    let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
    if byClaim.contains digest then throw (IO.userError "duplicate shard proof")
    verifyWrapper ctx .ixvm wrapper
    byClaim := byClaim.insert digest wrapper
  unless byClaim.size == prepared.size do throw (IO.userError "expected exactly one proof per nonempty shard")
  let mut nodes : Array Node := #[]
  for (item, slot) in plan.mapIdx fun i item => (item, i) do
    IO.println s!"[formal aggregate] slot {slot}/{plan.size}: shape {item.shape?}"
    let node ← match item.op with
    | .leaf shard => do
      let some source := prepared[shard]? | throw (IO.userError "invalid plan leaf")
      let some wrapper := byClaim.get? (Address.blake3 (Ix.Claim.ser source.claim))
        | throw (IO.userError "missing shard proof")
      let raw : Node := { statement := source.statement, kind := .ixvm, wrapper }
      if item.kind == .ixvm then pure raw else proveNode p ctx raw.statement raw
    | .join l r => do
      let some left := nodes[l]? | throw (IO.userError "invalid left child")
      let some right := nodes[r]? | throw (IO.userError "invalid right child")
      let output := if item.structural then left.statement.joinStructural right.statement
        else left.statement.join right.statement
      proveNode p ctx output left (some right) item.structural
    nodes := nodes.push node
  let some root := nodes.back? | throw (IO.userError "empty aggregation plan")
  let count ← IO.ofExcept (auditAggregateConstants env root.statement)
  verifyWrapper ctx .aggr root.wrapper
  IO.println s!"[formal aggregate] verified {count} constants, no undischarged assumptions"
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
