module
public import Ix.Cli.FormalAiur
public import Ix.Cli.Compression
public import Ix.Cli.ClaimPolicy
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
    "export-trace" #["--aggregate"]

def host : IO String := rustHost "stark-verifier" "stark-verifier" "IX_STARK_HOST"

def invoke (artifactPath mode : String) (input : ByteArray) (output : String)
    (rows : Nat := 65536) (retention : String := "regenerate") : IO Unit :=
  IO.FS.withTempFile fun h path => do
    h.write input
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
    unless channel == Aiur.functionChannel.n do throw (IO.userError "unexpected formal call namespace")
    let key ← IO.FS.readBinFile (dir / "key.bin")
    let index ← IO.ofExcept (json.getObjValAs? Nat "function_index")
    return { key, index }

structure Context where
  ixvmArtifact : String
  aggrArtifact : String
  ixvm : Identity
  aggr : Identity
  allowed : ByteArray

def aggrIdentity (p : Cli.Parsed) : IO (String × Identity) := do
  let aggrArtifact ← artifact p
  let aggr ← identity (← host) aggrArtifact
  return (aggrArtifact, aggr)

def context (p : Cli.Parsed) : IO Context := do
  let ixvmArtifact ← FormalAiur.artifact p
  let (aggrArtifact, aggr) ← aggrIdentity p
  let ixvm ← identity (← FormalAiur.host) ixvmArtifact
  let allowed := Aggr.allowedBlob ixvm.key ixvm.index aggr.key aggr.index
  return { ixvmArtifact, aggrArtifact, ixvm, aggr, allowed }

def outerClaim (ctx : Context) (kind : ChildKind) (claim : Ix.Claim) : Array Aiur.G :=
  match kind with
  | .ixvm => Aiur.buildClaim ctx.ixvm.index (MultiStark.digestGs (Ix.Claim.ser claim)) #[]
  | .aggr => Aggr.aggregateOuterClaim ctx.allowed ctx.aggr.index claim

def rawProof (kind : ChildKind) (proof : ByteArray) : IO ByteArray := do
  let magic := (if kind == .ixvm then "IXAIUR2\x00" else "IXAGGR2\x00").toUTF8
  unless proof.extract 0 magic.size == magic do
    throw (IO.userError "proof belongs to a different backend or recursion kind")
  return proof.extract magic.size proof.size

/-- Build the shape-1 (`(.aggr, none)`) recursive wrap invocation for an
aggregate root `wrapper`. Returns `(rawProofBytes, invocation)`, the invocation
in Ixon (`Ix.AiurInvocation`). -/
def wrapInvocation (ctx : Context) (wrapper : Ixon.Proof) : IO (ByteArray × ByteArray) := do
  let raw ← rawProof .aggr wrapper.proof
  let shape := Aggr.shapeCode (.aggr, none)
  let io := Aggr.extendChild (Aggr.extendVk (Aggr.extendIdentity default ctx.allowed shape) .aggr ctx.aggr.key) 0 raw
    (MultiStark.serializeClaims #[outerClaim ctx .aggr wrapper.claim])
  let claimBytes := Ix.Claim.ser wrapper.claim
  let inv := FormalAiur.invocation (Aggr.pubInput ctx.allowed claimBytes) io "MultiStark::ix_aggr"
  return (raw, inv)

/-- Normalize `wrapper`'s aggregate root to `layout` (`.ixl` bytes) under `ctx`. -/
def normalize (ctx : Context) (wrapper : Ixon.Proof) (layout : ByteArray) : IO ByteArray := do
  let (raw, inv) ← wrapInvocation ctx wrapper
  Compression.normalizeRoot ctx.aggrArtifact inv raw layout

/-- The root statement a compressed proof of `claim` must expose: the public
claim of the backend's `MultiStark::ix_aggr` entrypoint, serialized as one
batch claim. -/
def statementBytes (ctx : Context) (claim : Ix.Claim) : ByteArray :=
  MultiStark.serializeClaims #[outerClaim ctx .aggr claim]

def verifyWrapper (ctx : Context) (kind : ChildKind) (wrapper : Ixon.Proof) : IO Unit := do
  if kind == .ixvm then return ← FormalAiur.verifyWrapper ctx.ixvmArtifact wrapper
  match wrapper.claim with
  | .checkEnv .. | .catalog _ => pure ()
  | _ => throw (IO.userError "aggregate must carry CheckEnv or Catalog")
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

def childAdvice (ctx : Context) (io : Aiur.IOBuffer) (slot : Nat) (node : Node) : IO Aiur.IOBuffer := do
  let io := extendVk io node.kind (if node.kind == .ixvm then ctx.ixvm.key else ctx.aggr.key)
  return extendChild io slot (← rawProof node.kind node.wrapper.proof)
    (MultiStark.serializeClaims #[outerClaim ctx node.kind node.wrapper.claim])

/-- Build a wrap/pair witness with the same manifest fold semantics used by
the independent verifier. Host tree operations never bypass circuit checks. -/
def advice (ctx : Context) (left : Node) (right : Option Node)
    (output : CheckEnvTrees) (structural : Bool) : IO Aiur.IOBuffer := do
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

def persist (wrapper : Ixon.Proof) : IO Address := do
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser wrapper.claim))
  StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))

/-- Whether earlier aggregate and range proofs must not be reused: `--no-cache`
neither reads nor writes the caches, and `ix prove --fresh` replaces their
entries with new proofs. -/
def noCacheReads (p : Cli.Parsed) : Bool :=
  p.hasFlag "no-cache" || p.hasFlag "fresh"

def cachedNode (ctx : Context) (output : CheckEnvTrees) : IO (Option Node) := do
  let cache ← StoreIO.toIO (Store.cacheDir "formal-aggregates")
  let key := Address.blake3 (ctx.aggr.key ++ MultiStark.serializeClaims #[outerClaim ctx .aggr output.claim])
  if let some addr ← ShardProofIndex.readAddress cache key then
    try
      let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
      unless wrapper.claim == output.claim do throw (IO.userError "cached aggregate claim mismatch")
      verifyWrapper ctx .aggr wrapper
      IO.println s!"[aiur aggregate] reused {addr}"
      return some { statement := output, kind := .aggr, wrapper }
    catch e => IO.eprintln s!"[aiur aggregate] ignored cache entry: {e}"
  return none

def proveAdvice (ctx : Context) (bytes : ByteArray) (io : Aiur.IOBuffer)
    (options : HostOptions) : IO ByteArray := do
  let input := invocation (Aggr.pubInput ctx.allowed bytes) io "MultiStark::ix_aggr"
  IO.FS.withTempDir fun dir => do
    let binary ← if options.resident.isSome then pure ""
      else rustHost "stark-verifier" "stark-verifier" "IX_STARK_HOST" options.device
    let code ← runHost binary ctx.aggrArtifact "prove" input dir.toString { options with priority := true }
    unless code == 0 do
      let report := dir / "report.json"
      if ← report.pathExists then IO.eprintln (← IO.FS.readFile report)
      throw (IO.userError s!"recursive prover exited {code}; reduce --range or give each prover lane more workspace (a larger --max-ram, or fewer --jobs on CPU)")
    IO.FS.readBinFile (dir / "proof.bin")

def proveNode (p : Cli.Parsed) (ctx : Context) (output : CheckEnvTrees)
    (left : Node) (right : Option Node := none) (structural : Bool := false)
    (options : HostOptions := {}) (force : Bool := false) : IO Node := do
  let cache ← StoreIO.toIO (Store.cacheDir "formal-aggregates")
  let key := Address.blake3 (ctx.aggr.key ++ MultiStark.serializeClaims #[outerClaim ctx .aggr output.claim])
  unless force || noCacheReads p do
    if let some node ← cachedNode ctx output then return node
  let io ← advice ctx left right output structural
  let proof ← proveAdvice ctx (Ix.Claim.ser output.claim) io options
  let wrapper : Ixon.Proof := { claim := output.claim, proof := "IXAGGR2\x00".toUTF8 ++ proof }
  unless p.hasFlag "no-write" do
    let addr ← persist wrapper
    unless p.hasFlag "no-cache" do ShardProofIndex.writeAddress cache key addr
    IO.println s!"[formal aggregate] persisted {addr}"
  return { statement := output, kind := .aggr, wrapper }

def dischargeAdvice (ctx : Context) (child : Node) (bindingWrapper : Ixon.Proof)
    (output : CheckEnvTrees) : IO Aiur.IOBuffer := do
  let shape := dischargeShapeCode child.kind
  let mut io ← childAdvice ctx (extendIdentity default ctx.allowed shape) 0 child
  io := extendVk io .ixvm ctx.ixvm.key
  io := extendChild io 1 (← rawProof .ixvm bindingWrapper.proof)
    (MultiStark.serializeClaims #[outerClaim ctx .ixvm bindingWrapper.claim])
  io := extendOutputClaim io (Ix.Claim.ser output.claim)
  for c in #[child.wrapper.claim, bindingWrapper.claim] do
    io := extendPreimage io (Ix.Claim.ser c)
  return io

def dischargeBindingNode (p : Cli.Parsed) (ctx : Context) (child : Node)
    (bindingWrapper : Ixon.Proof) (options : HostOptions := {})
    (force : Bool := false) : IO Node := do
  let output : CheckEnvTrees := { child.statement with ctx := { child.statement.ctx with bindingAssumed := false } }
  let cache ← StoreIO.toIO (Store.cacheDir "formal-aggregates")
  let key := Address.blake3 (ctx.aggr.key ++ MultiStark.serializeClaims #[outerClaim ctx .aggr output.claim])
  unless force || noCacheReads p do
    if let some node ← cachedNode ctx output then return node
  let io ← dischargeAdvice ctx child bindingWrapper output
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
  MultiStark.serializeClaims #[Aiur.buildClaim ctx.aggr.index (Aggr.pubInput ctx.allowed statement) #[]]

def verifyRange (ctx : Context) (node : RangeNode) : IO Unit :=
  IO.FS.withTempFile fun _ path => do
    IO.FS.writeBinFile path node.proof
    invoke ctx.aggrArtifact "verify"
      (invocation (pubInput ctx.allowed node.statement) default "MultiStark::ix_aggr") path.toString

def proveRange (p : Cli.Parsed) (ctx : Context) (statement : ByteArray)
    (io : Aiur.IOBuffer) (options : HostOptions) : IO RangeNode := do
  let cache ← StoreIO.toIO (Store.cacheDir "formal-ranges")
  let key := Address.blake3 (ctx.aggr.key ++ rangeClaims ctx statement)
  unless noCacheReads p do
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

def rangeChild (ctx : Context) (io : Aiur.IOBuffer) (slot : Nat) (node : RangeNode) : Aiur.IOBuffer :=
  extendPreimage (extendChild (extendVk io .aggr ctx.aggr.key) slot node.proof (rangeClaims ctx node.statement)) node.statement

/-- The native host only slices serialized advice. Shapes 10, 11 and 12 in
ordinary Aiur verify every range, sum, boundary, and final public claim.
Independent range proofs run concurrently up to `jobs`, evicting child range
proof buffers as soon as their consuming parent extracts them. -/
def wrapRanges (p : Cli.Parsed) (ctx : Context) (source : Node)
    (options : HostOptions) (size : Nat) (force : Bool := false)
    (jobs : Nat := 1) : IO Node := do
  unless force || noCacheReads p do
    if let some node ← cachedNode ctx source.statement then return node
  unless source.kind == .ixvm && size > 0 do throw (IO.userError "range wrapping requires an IxVM proof and positive range size")
  IO.FS.withTempDir fun dir => do
    let raw := dir / "source.bin"
    IO.FS.writeBinFile raw (← rawProof .ixvm source.wrapper.proof)
    command (← host) #["ranges", raw.toString, dir.toString, toString size]
    let specs ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / "ranges.json")) >>= Json.getArr?)
    if specs.isEmpty then throw (IO.userError "empty range plan")
    let preamble ← IO.FS.readBinFile (dir / "preamble.bin")
    let mut planChildren : Array (Array Nat) := #[]
    let mut users : Array Nat := Array.replicate specs.size 0
    for i in [:specs.size] do
      let children ← IO.ofExcept (specs[i]!.getObjValAs? (Array Nat) "children")
      unless children.isEmpty || children.size == 2 do
        throw (IO.userError "invalid range plan")
      for c in children do
        unless c < i do throw (IO.userError "missing range child")
        users := users.modify c (· + 1)
      planChildren := planChildren.push children
    let rootIdx := specs.size - 1
    let mut nodes : Array (Option RangeNode) := Array.replicate specs.size none
    let mut completed : Array Bool := Array.replicate specs.size false
    let mut inFlight : Array Bool := Array.replicate specs.size false
    let mut running : Array (Nat × Task (Except IO.Error RangeNode)) := #[]
    let admitted ← IO.mkRef running
    let limit := max 1 (min jobs specs.size)
    let childOptions := if limit <= 1 || options.resident.isSome then options
      else options.forWave 1 limit
    try
      while !completed[rootIdx]! do
        let mut waiting := #[]
        for (idx, task) in running do
          if ← IO.hasFinished task then
            inFlight := inFlight.set! idx false
            let node ← IO.ofExcept task.get
            nodes := nodes.set! idx (some node)
            completed := completed.set! idx true
          else waiting := waiting.push (idx, task)
        running := waiting
        admitted.set running
        if !completed[rootIdx]! && running.size < limit then
          let mut ready : Array Nat := #[]
          for i in [:specs.size] do
            if !completed[i]! && !inFlight[i]! then
              let cs := planChildren[i]!
              if cs.isEmpty || (completed[cs[0]!]! && completed[cs[1]!]!) then
                ready := ready.push i
          -- Prefer internal joins over leaves so finished child range proofs
          -- can be evicted sooner.
          let readyJoins := ready.filter fun i => !planChildren[i]!.isEmpty
          let readyLeaves := ready.filter fun i => planChildren[i]!.isEmpty
          for i in (readyJoins ++ readyLeaves).extract 0 (limit - running.size) do
            let cs := planChildren[i]!
            let task ← if cs.isEmpty then do
                IO.asTask (prio := .dedicated) do
                  let statement ← IO.FS.readBinFile (dir / s!"{i}.statement")
                  let io := extendVk (extendIdentity default ctx.allowed 10) .ixvm ctx.ixvm.key
                  let io := extendChild io 0 preamble ByteArray.empty
                  let io := extendChild io 1 (← IO.FS.readBinFile (dir / s!"{i}.proofs")) ByteArray.empty
                  proveRange p ctx statement (extendOutputClaim io statement) childOptions
              else do
                let lIdx := cs[0]!
                let rIdx := cs[1]!
                let some l := nodes[lIdx]! | throw (IO.userError "missing range child")
                let some r := nodes[rIdx]! | throw (IO.userError "missing range child")
                for c in #[lIdx, rIdx] do
                  users := users.modify c (· - 1)
                  if c != rootIdx && users[c]! == 0 then
                    nodes := nodes.set! c none
                IO.asTask (prio := .dedicated) do
                  let statement ← IO.FS.readBinFile (dir / s!"{i}.statement")
                  let io := rangeChild ctx (rangeChild ctx (extendIdentity default ctx.allowed 11) 0 l) 1 r
                  proveRange p ctx statement (extendOutputClaim io statement) childOptions
            inFlight := inFlight.set! i true
            running := running.push (i, task)
            admitted.set running
        if !completed[rootIdx]! && running.isEmpty then
          throw (IO.userError "range plan has no ready slot")
        unless completed[rootIdx]! do IO.sleep 1
    finally
      for (_, task) in (← admitted.get) do let _ ← IO.wait task; pure ()
    let some rangeRoot := nodes[rootIdx]! | throw (IO.userError "empty range plan")
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

/-- The immutable result of simulating aggregate-slot admission. Runtime and
unit tests share the same admission function; the simulator completes the
lowest-numbered in-flight slot after every admission pass solely to make its
trace deterministic. -/
structure AggregateScheduleTrace where
  admissionOrder : Array Nat
  admissionBatches : Array (Array Nat)
  maxReservedBytes : Nat
  deriving BEq, Repr

private def aggregateScheduleInputsValid (plan : Array Reference.ScheduledFold)
    (weights : Array Nat) : Except String Unit := do
  if weights.size != plan.size then
    throw s!"aggregate scheduler received {weights.size} weights for {plan.size} slots"
  for (item, slotIdx) in plan.mapIdx fun slotIdx item => (item, slotIdx) do
    if weights[slotIdx]! == 0 then
      throw s!"aggregate scheduler slot {slotIdx} has zero RAM weight"
    match item.op with
    | .leaf _ => pure ()
    | .join left right =>
      if left >= slotIdx || right >= slotIdx then
        throw s!"aggregate scheduler slot {slotIdx} has non-prior child {left}, {right}"

private def aggregateDependenciesComplete (item : Reference.ScheduledFold)
    (completed : Array Bool) : Bool :=
  match item.op with
  | .leaf _ => true
  | .join left right =>
    (completed[left]?).getD false && (completed[right]?).getD false

/-- Select one deterministic admission batch from the currently ready slots.
Candidates are ordered by descending RAM weight, then joins before leaves
(freeing child proof buffers sooner at equal weight), then ascending slot
number. Slots that do not fit are skipped so lighter work can use the
remaining budget. An individually oversized slot may run only when nothing
else is reserved, following the Rust `RamGate` admit-when-alone rule.
`jobs = 0` means no concurrency cap beyond the number of plan slots. When
`pending?` is provided, only slots marked `true` in `pending` are admitted. -/
def admitAggregateReady (plan : Array Reference.ScheduledFold) (weights : Array Nat)
    (completed inFlight : Array Bool) (reservedBytes budgetBytes jobs : Nat)
    (pending? : Option (Array Bool) := none) :
    Array Nat := Id.run do
  let active := inFlight.count true
  let maxJobs := if jobs == 0 then max 1 plan.size else max 1 jobs
  if active >= maxJobs then return #[]
  let openJobs := maxJobs - active
  let mut ready : Array Nat := #[]
  for slotIdx in [:plan.size] do
    let isPending := match pending? with
      | some pending => (pending[slotIdx]?).getD false
      | none => true
    if isPending && !(completed[slotIdx]?).getD false &&
        !(inFlight[slotIdx]?).getD false then
      if let some item := plan[slotIdx]? then
        if aggregateDependenciesComplete item completed then
          ready := ready.push slotIdx
  let isJoin (slot : Nat) : Bool :=
    match plan[slot]? with
    | some item => match item.op with | .join _ _ => true | .leaf _ => false
    | none => false
  ready := ready.qsort fun left right =>
    let leftWeight := (weights[left]?).getD 0
    let rightWeight := (weights[right]?).getD 0
    if leftWeight != rightWeight then leftWeight > rightWeight
    else if isJoin left != isJoin right then isJoin left
    else left < right
  let mut admitted : Array Nat := #[]
  let mut admittedBytes := 0
  for slotIdx in ready do
    if admitted.size >= openJobs then break
    let weight := (weights[slotIdx]?).getD 0
    let nextReserved := reservedBytes + admittedBytes + weight
    if nextReserved <= budgetBytes ||
        (reservedBytes == 0 && admitted.isEmpty) then
      admitted := admitted.push slotIdx
      admittedBytes := admittedBytes + weight
  return admitted

/-- Pure deterministic exercise of the runtime admission algorithm. This is
used to gate heaviest-first ordering, dependency release, job caps, and peak
reservation without starting proof tasks. -/
def simulateAggregateSchedule (plan : Array Reference.ScheduledFold)
    (weights : Array Nat) (jobs budgetBytes : Nat) :
    Except String AggregateScheduleTrace := do
  aggregateScheduleInputsValid plan weights
  if budgetBytes == 0 then throw "aggregate scheduler RAM budget must be positive"
  let mut completed := Array.replicate plan.size false
  let mut inFlight := Array.replicate plan.size false
  let mut completedCount := 0
  let mut reservedBytes := 0
  let mut maxReservedBytes := 0
  let mut admissionOrder : Array Nat := #[]
  let mut admissionBatches : Array (Array Nat) := #[]
  while completedCount < plan.size do
    let admitted := admitAggregateReady plan weights completed inFlight
      reservedBytes budgetBytes jobs
    if !admitted.isEmpty then
      admissionBatches := admissionBatches.push admitted
      for slotIdx in admitted do
        inFlight := inFlight.set! slotIdx true
        reservedBytes := reservedBytes + weights[slotIdx]!
        admissionOrder := admissionOrder.push slotIdx
      maxReservedBytes := max maxReservedBytes reservedBytes
    let mut finish? : Option Nat := none
    for slotIdx in [:plan.size] do
      if finish?.isNone && inFlight[slotIdx]! then finish? := some slotIdx
    let some finished := finish?
      | throw "aggregate scheduler deadlocked with unfinished slots"
    inFlight := inFlight.set! finished false
    completed := completed.set! finished true
    reservedBytes := reservedBytes - weights[finished]!
    completedCount := completedCount + 1
  pure { admissionOrder, admissionBatches, maxReservedBytes }

private def blockAddrOf (addr : Address) (c : Ixon.Constant) : Address :=
  match c.info with
  | .iPrj prj => prj.block
  | .cPrj prj => prj.block
  | .rPrj prj => prj.block
  | .dPrj prj => prj.block
  | _ => addr

/-- Validate disjoint shard coverage, prune zero-constant manifest leaves, and
partition claimable owned constants per retained shard in ONE `inertUsers`
graph walk and ONE pass over `ixonEnv.consts`. Produces identical coverage
diagnostics and errors to `Ix.Shard.shardsCover` followed by `pruneEmpty`. -/
private def coverAndPrune (ixonEnv : Ixon.Env) (view : Ix.Shard.IxesManifestView) :
    IO (Ix.Shard.IxesManifestView × Array Nat × Array (Array Address)) := do
  let mut blockToShard : Std.HashMap Address Nat := {}
  let mut dup : Nat := 0
  for (blocks, k) in view.shards.mapIdx (fun k b => (b, k)) do
    for blk in blocks do
      match blockToShard.get? blk with
      | some _ => dup := dup + 1
      | none => blockToShard := blockToShard.insert blk k
  let inert := IxVM.ClaimHarness.inertUsers ixonEnv
  let mut blockOf : Array (Address × Address) := #[]
  let mut aside : Std.HashSet Address := {}
  let mut unparsed : Nat := 0
  for (addr, lc) in ixonEnv.consts do
    let some c := lc.get? | unparsed := unparsed + 1; continue
    if c.outsideLogic then aside := aside.insert addr
    blockOf := blockOf.push (addr, blockAddrOf addr c)
  let mut ownedRaw : Array (Array Address) := Array.replicate view.shards.size #[]
  let mut unowned : Nat := 0
  let mut setAside : Nat := 0
  let mut inertAside : Nat := 0
  for (addr, blk) in blockOf do
    if aside.contains addr || aside.contains blk then
      setAside := setAside + 1
      continue
    if inert.contains addr then
      inertAside := inertAside + 1
      continue
    match blockToShard.get? blk with
    | some k => ownedRaw := ownedRaw.modify k (·.push addr)
    | none => unowned := unowned + 1
  IO.println s!"[shards] {view.shards.size} shards, {ixonEnv.consts.size} consts"
  for (blocks, k) in view.shards.mapIdx (fun k b => (b, k)) do
    IO.println s!"  shard {k}: {blocks.size} blocks, {(ownedRaw[k]?).map (·.size) |>.getD 0} consts"
  if setAside != 0 then
    IO.println s!"[shards] {setAside} const(s) outside Lean's logic (unsafe or partial) \
      set aside: owned by no shard, claimed by none"
  if inertAside != 0 then
    IO.println s!"[shards] {inertAside} const(s) using an inert axiom (sorryAx or a \
      compiler-trust axiom) set aside: owned by no shard, claimed by none"
  if dup != 0 then
    IO.eprintln s!"[shards] FAIL: {dup} block(s) owned by >1 shard (not disjoint)"
  if unowned != 0 then
    IO.eprintln s!"[shards] FAIL: {unowned} const(s) with no owning shard (coverage gap)"
  if unparsed != 0 then
    IO.eprintln s!"[shards] FAIL: {unparsed} const(s) whose bytes do not parse \
      (cannot be assigned to a shard)"
  let ok := dup == 0 && unowned == 0 && unparsed == 0
  if ok then
    IO.println s!"[shards] OK: partition covers all \
      {ixonEnv.consts.size - setAside - inertAside} claimable consts, disjoint"
  unless ok do throw (IO.userError "invalid manifest coverage")
  if view.shards.size != view.shardIds.size then
    throw (IO.userError "ixes: internal shard/id cardinality mismatch")
  let mut remap : Array (Option Nat) := Array.replicate view.shards.size none
  let mut shards : Array (Array Address) := #[]
  let mut shardIds : Array Nat := #[]
  let mut measuredPeakBytes : Array Nat := #[]
  let mut keptCounts : Array Nat := #[]
  let mut keptOwned : Array (Array Address) := #[]
  for (owned, oldIdx) in ownedRaw.mapIdx fun oldIdx owned => (owned, oldIdx) do
    if !owned.isEmpty then
      let some blocks := view.shards[oldIdx]?
        | throw (IO.userError s!"ixes: internal missing shard {oldIdx}")
      let some originalId := view.shardIds[oldIdx]?
        | throw (IO.userError s!"ixes: internal missing shard id {oldIdx}")
      remap := remap.set! oldIdx (some shards.size)
      shards := shards.push blocks
      shardIds := shardIds.push originalId
      measuredPeakBytes := measuredPeakBytes.push ((view.measuredPeakBytes[oldIdx]?).getD 0)
      keptCounts := keptCounts.push owned.size
      keptOwned := keptOwned.push owned
  let some aggregationTree := view.aggregationTree.pruneAndRemap remap
    | throw (IO.userError "aggregate: manifest has no shard owning an environment constant")
  return ({ shards, shardIds, aggregationTree, measuredPeakBytes }, keptCounts, keptOwned)

private def manifestWithOwned (p : Cli.Parsed) (override : Option String := none) :
    IO (Ixon.Env × Ix.Shard.IxesManifestView × Array Nat × Array (Array Address)) := do
  let some envPath := (p.flag? "ixe").map (·.as! String) | throw (IO.userError "aggregate requires --ixe")
  let some path := override.orElse (fun _ => (p.flag? "ixes").map (·.as! String)) | throw (IO.userError "aggregate requires --ixes")
  let env ← IO.ofExcept (IxVM.ClaimHarness.withDefaultRoleBinding (← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile envPath))))
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile path))
  let (view, counts, ownedPerShard) ← coverAndPrune env view
  return (env, view, counts, ownedPerShard)

def manifest (p : Cli.Parsed) (override : Option String := none) : IO (Ixon.Env × Ix.Shard.IxesManifestView × Array Nat) := do
  let (env, view, counts, _) ← manifestWithOwned p override
  return (env, view, counts)

private def prepareOwnedShard (env : Ixon.Env) (owned : Array Address)
    (assumeBinding : Bool := false) : Except String Reference.PreparedShard := do
  let (claim, trees) ← IxVM.ClaimHarness.shardCheckEnvClaimTreesOf env owned assumeBinding
  let statement ← Aggr.CheckEnvTrees.ofClaim claim trees
  pure { claim, statement }

private def prepareOwnedShards (env : Ixon.Env) (ownedPerShard : Array (Array Address))
    (shardIds : Array Nat := #[]) (assumeBinding : Bool := false) :
    Except String (Array Reference.PreparedShard) := do
  let mut prepared : Array Reference.PreparedShard := #[]
  for (owned, shard) in ownedPerShard.mapIdx fun shard owned => (owned, shard) do
    let originalShard := (shardIds[shard]?).getD shard
    let item ← match prepareOwnedShard env owned assumeBinding with
      | .error e => throw s!"prepare shard {originalShard}: {e}"
      | .ok item => pure item
    prepared := prepared.push item
  pure prepared

private partial def proveBlocks (p : Cli.Parsed) (ctx : Context) (env : Ixon.Env)
    (blocks owned : Array Address) (source? : Option Reference.PreparedShard)
    (options : HostOptions)
    (progress : Array (Array Address × Nat) → IO Unit) (preferRaw : Bool := false)
    (assumeBinding : Bool := false) (jobs : Nat := 1) : IO (Node × Array (Array Address × Nat)) := do
  let source ← match source? with
    | some s => pure s
    | none => IO.ofExcept (prepareOwnedShard env owned assumeBinding)
  unless preferRaw || noCacheReads p do
    if let some cached ← cachedNode ctx source.statement then
      progress #[(blocks, 0)]
      return (cached, #[(blocks, 0)])
  let (claim, witness) ← IO.ofExcept (IxVM.ClaimHarness.buildShardCheckEnvWitnessOf env owned assumeBinding)
  let result ← FormalAiur.one p ctx.ixvmArtifact "" options "prove" claim (.leanW witness)
    s!"leaf ({blocks.size} blocks)" true
  if result.code == 0 then
    let some address := result.address | throw (IO.userError "leaf produced no proof")
    let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read address)))
    progress #[(blocks, result.peak)]
    return ({ statement := source.statement, kind := .ixvm, wrapper }, #[(blocks, result.peak)])
  unless result.code == 75 && blocks.size > 1 &&
      (result.report.getObjValAs? Bool "can_split").toOption.getD true do
    throw (IO.userError s!"leaf failed: {result.report.compress}")
  let parts := Ix.Shard.Check.cutBlocks blocks 2
  unless parts.size == 2 && parts.all (fun b => !b.isEmpty && b.size < blocks.size) do
    throw (IO.userError "cannot refine oversized leaf")
  let ownedParts := Ix.Shard.partitionOwned env owned parts
  IO.println s!"[aiur lanes] refining {blocks.size} blocks into {parts[0]!.size} + {parts[1]!.size}"
  progress #[(parts[0]!, 0), (parts[1]!, 0)]
  let ((left, lp), (right, rp)) ← if jobs <= 1 then do
      let (left, lp) ← proveBlocks p ctx env parts[0]! ownedParts[0]! none options
        (fun lp => progress (lp ++ #[(parts[1]!, 0)])) true assumeBinding 1
      let (right, rp) ← proveBlocks p ctx env parts[1]! ownedParts[1]! none options
        (fun rp => progress (lp ++ rp)) true assumeBinding 1
      pure ((left, lp), (right, rp))
    else do
      let leftJobs := max 1 (jobs / 2)
      let rightJobs := max 1 (jobs - leftJobs)
      let childOpts := if options.resident.isSome then options else options.forWave 1 2
      let splitState ← Std.Mutex.new (#[(parts[0]!, 0)], #[(parts[1]!, 0)])
      let rightTask ← IO.asTask (prio := .dedicated) (proveBlocks p ctx env parts[1]! ownedParts[1]! none childOpts
        (fun rp => splitState.atomically fun ref => do
          let (l, _) ← ref.get
          ref.set (l, rp)
          progress (l ++ rp)) true assumeBinding rightJobs)
      let leftRes ← try
          proveBlocks p ctx env parts[0]! ownedParts[0]! none childOpts
            (fun lp => splitState.atomically fun ref => do
              let (_, r) ← ref.get
              ref.set (lp, r)
              progress (lp ++ r)) true assumeBinding leftJobs
        catch e => do
          let _ ← IO.wait rightTask
          throw e
      let rightRes ← IO.ofExcept rightTask.get
      pure (leftRes, rightRes)
  let joined := left.statement.join right.statement
  unless joined.claim == source.claim do throw (IO.userError "refinement changed the original leaf statement")
  let node ← proveNode p ctx joined left (some right) false options
  return (node, lp ++ rp)

private def runCore (p : Cli.Parsed) (proveLeaves : Bool)
    (onRoot : Address → IO Unit := fun _ => pure ()) : IO UInt32 := do
  let original : Option String := (p.flag? "ixes").map (·.as! String)
  let checkpoint ← if proveLeaves && !p.hasFlag "plan-only" then do
      let some original := original | throw (IO.userError "--lanes requires --ixes")
      let some ixe := (p.flag? "ixe").map (·.as! String) | throw (IO.userError "--lanes requires --ixe")
      let key := Address.blake3 ((Address.blake3 (← IO.FS.readBinFile ixe)).hash ++ (← IO.FS.readBinFile original))
      let cache ← match ← IO.getEnv "AIUR_LANES_CACHE_DIR" with
        | some dir => pure (System.FilePath.mk dir / "formal")
        | none => StoreIO.toIO (Store.cacheDir "formal-lanes")
      IO.FS.createDirAll cache
      pure (some (cache / s!"{key}.ixes"))
    else pure none
  let sourcePath ← match checkpoint with
    | some path => if ← path.pathExists then pure (some path.toString) else pure original
    | none => pure original
  let (env, view, counts, ownedPerShard) ← manifestWithOwned p sourcePath
  let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
  let plan ← IO.ofExcept (Reference.schedulePlan view.aggregationTree.foldPlan counts above (p.hasFlag "direct-joins"))
  let subtree := (p.flag? "subtree").map (·.as! Nat)
  let reproveSlot := (p.flag? "reprove-slot").map (·.as! Nat)
  if subtree.isSome && (reproveSlot.isSome || p.hasFlag "wrap-root") then
    throw (IO.userError "--subtree cannot be combined with --reprove-slot or --wrap-root")
  if reproveSlot.isSome && (p.hasFlag "no-cache" || p.hasFlag "plan-only") then
    throw (IO.userError "--reprove-slot requires caches and cannot be combined with --plan-only")
  let rootSlot := (subtree.orElse fun _ => reproveSlot).getD (plan.size - 1)
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
  let jobs := min plan.size (((p.flag? "lanes").map (·.as! Nat)).getD (← jobCount p))
  let options ← hostOptions p
  let ctx ← context p
  let bindingProof? := (p.flag? "binding-proof").map (·.as! String)
  let assumeBinding := bindingProof?.isSome
  let bindingWrapper? ← match bindingProof? with
    | none => pure none
    | some bPath => do
      let bWrapper ← FormalAiur.readProofFileOrStore bPath
      let expectedCtx ← IO.ofExcept (Ix.ClaimContext.ofEnv env false)
      let expectedClaim := Ix.Claim.binding expectedCtx.spec expectedCtx.binding
      unless bWrapper.claim == expectedClaim do
        throw (IO.userError s!"binding proof {bPath} states {bWrapper.claim}, expected {expectedClaim}")
      FormalAiur.verifyWrapper ctx.ixvmArtifact bWrapper
      pure (some bWrapper)
  withController p #[(ctx.ixvmArtifact, "ixvm"), (ctx.aggrArtifact, "recursion")] options jobs fun options => do
    let refinements : Std.Mutex (Array (Nat × Array (Array Address × Nat))) ← Std.Mutex.new #[]
    let saveLeaf : Nat → Array (Array Address × Nat) → IO Unit ← if proveLeaves then do
        let some sourcePath := sourcePath | throw (IO.userError "missing source manifest")
        let some resident := options.resident | throw (IO.userError "missing resident controller")
        let bytes ← IO.FS.readBinFile sourcePath
        let sourceView ← IO.ofExcept (Ix.Shard.parseIxesManifest bytes)
        let snapshot := resident.directory / "base.ixes"
        IO.FS.writeBinFile snapshot bytes
        let some ixe := (p.flag? "ixe").map (·.as! String) | throw (IO.userError "missing environment")
        let handle ← IO.ofExcept (Aiur.EnvHandle.fromIxe ixe)
        pure (fun shard parts => refinements.atomically fun ref => do
          let id := view.shardIds[shard]!
          let index := sourceView.shardIds.toList.idxOf id
          let previous ← ref.get
          let runs := if let some pos := previous.findIdx? (fun (i, _) => i == index) then
              previous.set! pos (index, parts)
            else previous.push (index, parts)
          ref.set runs
          let (splits, measured) := Ix.Shard.Check.refinementsOfRuns sourceView.shards.size runs
          if let some path := checkpoint then
            let temp := System.FilePath.mk s!"{path}.tmp.{← IO.Process.getPID}.{← IO.monoNanosNow}"
            try
              let _ ← Ix.Shard.Check.emitRefinedManifest "aiur lanes checkpoint" handle snapshot.toString temp.toString splits measured 0
              IO.FS.rename temp path
            finally
              if ← temp.pathExists then IO.FS.removeFile temp
          pure ())
      else pure (fun (_ : Nat) (_ : Array (Array Address × Nat)) => pure ())
    let prepared ← IO.ofExcept (prepareOwnedShards env ownedPerShard view.shardIds assumeBinding)
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
    for i in (List.range (rootSlot + 1)).reverse do
      let some item := plan[i]? | throw (IO.userError "missing plan slot")
      let some statement := statements[i]? | throw (IO.userError "missing statement")
      if pending[i]! && reproveSlot != some i then
        if let some wrapper := supplied.get? (Address.blake3 (Ix.Claim.ser statement.claim)) then
          nodes := nodes.set! i (some { statement, kind := .aggr, wrapper })
        else if item.kind == .aggr && !noCacheReads p then
          if let some cached ← cachedNode ctx statement then nodes := nodes.set! i (some cached)
      if pending[i]! && nodes[i]!.isNone then
        if let .join l r := item.op then pending := pending.set! l true |>.set! r true
    if let some slot := reproveSlot then
      let some item := plan[slot]? | throw (IO.userError "missing slot")
      if let .join l r := item.op then
        for child in #[l, r] do
          let some item := plan[child]? | throw (IO.userError "missing child")
          if item.kind == .aggr && nodes[child]!.isNone then
            throw (IO.userError s!"--reprove-slot requires verified cached child {child}")
    let slotWeights := Reference.aggregateSlotRamWeights plan
    let lanes := ((p.flag? "lanes").map (·.as! Nat)).getD (if options.device.isSome then 1 else jobs)
    let ramBudgetBytes ←
      if (p.flag? "max-ram").isSome || (p.flag? "ram-budget").isSome then
        pure (max 1 (if p.hasFlag "lanes" && p.hasFlag "max-ram" then options.ram * max 1 lanes else options.ram))
      else
        Aggr.defaultAggregateRamBudgetBytes
    let ahead ← executionJobs p jobs
    let capacity := if (p.flag? "exec-ahead").map (·.as! Nat) == some 0 then max jobs 1 else max 1 (jobs + ahead)
    let mut completed := nodes.map Option.isSome
    let mut inFlight := Array.replicate plan.size false
    let mut reservedBytes := 0
    let mut running : Array (Nat × Task (Except IO.Error Node)) := #[]
    let admitted ← IO.mkRef running
    let mut users := Array.replicate plan.size 0
    for i in [:plan.size] do
      if pending[i]! && !completed[i]! then
        if let some item := plan[i]? then
          if let .join l r := item.op then
            users := users.modify l (· + 1) |>.modify r (· + 1)
    try
      while !completed[rootSlot]! do
        let mut waiting := #[]
        for (slot, task) in running do
          if ← IO.hasFinished task then
            inFlight := inFlight.set! slot false
            reservedBytes := reservedBytes - (slotWeights[slot]?).getD 0
            let node ← IO.ofExcept task.get
            nodes := nodes.set! slot (some node)
            completed := completed.set! slot true
          else waiting := waiting.push (slot, task)
        running := waiting
        admitted.set running
        if !completed[rootSlot]! then
          let batch := admitAggregateReady plan slotWeights completed inFlight
            reservedBytes ramBudgetBytes capacity (some pending)
          for slot in batch do
            let some item := plan[slot]? | throw (IO.userError "missing slot")
            let some output := statements[slot]? | throw (IO.userError "missing statement")
            let forceSlot := reproveSlot == some slot
            let totalSlots := plan.size
            -- Extract ONLY the child proof buffers / leaf inputs needed by this
            -- slot before spawning `IO.asTask` so no task closure retains `nodes`.
            let task ← match item.op with
              | .leaf shard => do
                let some source := prepared[shard]? | throw (IO.userError "missing shard")
                let rawByClaim? := byClaim.get? (Address.blake3 (Ix.Claim.ser source.claim))
                let blocks := view.shards[shard]!
                let shardOwned := ownedPerShard[shard]!
                let shardId := view.shardIds[shard]!
                let onLeafProgress := saveLeaf shard
                IO.asTask (prio := .dedicated) do
                  IO.println s!"[aiur aggregate] slot {slot}/{totalSlots}: shape {item.shape?}"
                  let raw ← if let some wrapper := rawByClaim? then
                      pure ({ statement := source.statement, kind := .ixvm, wrapper } : Node)
                    else if proveLeaves then do
                      let (node, _) ← proveBlocks p ctx env blocks shardOwned (some source) options onLeafProgress
                        (item.kind == .ixvm) assumeBinding jobs
                      pure node
                    else throw (IO.userError s!"missing proof of shard {shardId}")
                  if item.kind == .ixvm || raw.kind == .aggr then pure raw
                  else if rangeSize > 0 && (← traceShards raw) > rangeSize then
                    wrapRanges p ctx raw options rangeSize forceSlot jobs
                  else proveNode p ctx output raw none false options forceSlot
              | .join l r => do
                let some left := nodes[l]! | throw (IO.userError "missing left child")
                let some right := nodes[r]! | throw (IO.userError "missing right child")
                for child in #[l, r] do
                  users := users.modify child (· - 1)
                  if child != rootSlot && users[child]! == 0 then
                    nodes := nodes.set! child none
                IO.asTask (prio := .dedicated) do
                  IO.println s!"[aiur aggregate] slot {slot}/{totalSlots}: shape {item.shape?}"
                  proveNode p ctx output left (some right) item.structural options forceSlot
            inFlight := inFlight.set! slot true
            reservedBytes := reservedBytes + (slotWeights[slot]?).getD 0
            running := running.push (slot, task)
            admitted.set running
        if !completed[rootSlot]! && running.isEmpty then
          throw (IO.userError "aggregate plan has no ready slot")
        unless completed[rootSlot]! do IO.sleep 1
    finally
      for (_, task) in (← admitted.get) do let _ ← IO.wait task; pure ()
    let some completedRoot := nodes[rootSlot]! | throw (IO.userError "missing aggregate root")
    let mut root := completedRoot
    if subtree.isNone && reproveSlot.isNone then
      let count ← IO.ofExcept (auditAggregateConstants env root.statement)
      IO.println s!"[aiur aggregate] verified coverage of {count} constants, no undischarged assumptions"
      if let some bWrapper := bindingWrapper? then
        root ← dischargeBindingNode p ctx root bWrapper options
      if p.hasFlag "wrap-root" || proveLeaves then
        if root.kind == .ixvm then
          root ← proveNode p ctx root.statement root none false options
        let mut count ← traceShards root
        while count > 1 do
          root ← proveNode p ctx root.statement root none false options true
          let next ← traceShards root
          unless next < count do
            throw (IO.userError s!"root wrapping stopped at {next} shards without shrinking; raise or omit --shard-rows, or give each prover lane more workspace (--max-ram)")
          count := next
    verifyWrapper ctx root.kind root.wrapper
    if proveLeaves then
      if let some flag := p.flag? "out-ixes" then
        let saved ← match checkpoint with
          | some path => if ← path.pathExists then pure (some path.toString) else pure sourcePath
          | none => pure sourcePath
        let some saved := saved | throw (IO.userError "missing completed partition")
        IO.FS.writeBinFile (flag.as! String) (← IO.FS.readBinFile saved)
    unless p.hasFlag "no-write" do
      let address ← persist root.wrapper
      if let some flag := p.flag? "report" then
        IO.FS.writeFile (flag.as! String) (Json.mkObj [("schema", toJson "ix-formal-pipeline/1"),
          ("root", toJson (toString address)), ("slots", toJson plan.size), ("jobs", toJson jobs),
          ("proved_leaves", toJson proveLeaves), ("verified", toJson true)]).pretty
      IO.println (toString address)
      onRoot address
    return 0

def run (p : Cli.Parsed) : IO UInt32 := runCore p false

def runPipeline (p : Cli.Parsed) (onRoot : Address → IO Unit := fun _ => pure ()) : IO UInt32 := do
  unless p.hasFlag "ixe" && p.hasFlag "ixes" do
    throw (IO.userError "--lanes/--aggregate/--compress requires --ixe and --ixes")
  for flag in #["shard", "shards", "distributed", "exec-only"] do
    if p.hasFlag flag then throw (IO.userError s!"--lanes/--aggregate cannot be combined with --{flag}")
  if p.hasFlag "lanes" && p.hasFlag "jobs" then
    throw (IO.userError "choose --lanes for GPU provers or --jobs for CPU provers")
  runCore p true onRoot

def verify (p : Cli.Parsed) : IO UInt32 := do
  rejectFlags p #["shard", "record", "distributed"]
  -- the expected claim, and the environment whose records the kernel's admission of
  -- the claim's table reads
  let (expected, tableEnvs) ← match (p.flag? "ixe").map (·.as! String),
      (p.flag? "ixes").map (·.as! String) with
  | none, none => pure ((none : Option Ix.Claim), ([] : List Ixon.Env))
  | none, some _ => throw (IO.userError "--ixes requires --ixe")
  | some path, none => do
    let env ← IO.ofExcept (IxVM.ClaimHarness.withDefaultRoleBinding (← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))))
    let some subjects := IxVM.ClaimHarness.envCanonicalTree env | throw (IO.userError "empty environment")
    let envCtx ← IO.ofExcept (Ix.ClaimContext.ofEnv env false)
    let statement : CheckEnvTrees := { ctx := envCtx, subjects, assumptions := none }
    let _ ← IO.ofExcept (auditAggregateConstants env statement)
    pure (some statement.claim, [env])
  | some _, some _ => do
    let (env, view, counts, ownedPerShard) ← manifestWithOwned p
    let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
    let plan ← IO.ofExcept (Reference.schedulePlan view.aggregationTree.foldPlan counts above)
    let prepared ← IO.ofExcept (prepareOwnedShards env ownedPerShard view.shardIds)
    let mut slots : Array CheckEnvTrees := #[]
    for item in plan do
      match item.op with
      | .leaf shard =>
        let some source := prepared[shard]? | throw (IO.userError s!"aggregate plan references missing shard {shard}")
        slots := slots.push source.statement
      | .join left right =>
        let some leftStatement := slots[left]? | throw (IO.userError s!"aggregate plan references missing left slot {left}")
        let some rightStatement := slots[right]? | throw (IO.userError s!"aggregate plan references missing right slot {right}")
        slots := slots.push <| if item.structural then leftStatement.joinStructural rightStatement else leftStatement.join rightStatement
    let some root := slots.back? | throw (IO.userError "aggregate manifest produced no root")
    let _ ← IO.ofExcept (auditAggregateConstants env root)
    pure (some root.claim, [env])
  let proofs := p.variableArgsAs! String
  if proofs.isEmpty then throw (IO.userError "expected an aggregate proof address")
  let mut ctx? : Option Context := none
  for hex in proofs do
    let some addr := Address.fromString hex | throw (IO.userError "invalid aggregate address")
    let wrapper ← Compression.readProof addr
    unless expected.all (· == wrapper.claim) do throw (IO.userError "aggregate does not match the requested environment/manifest")
    let statement ← ClaimPolicy.admit p wrapper.claim (envs := pure tableEnvs)
    if Compression.isCompressed wrapper.proof then
      let .checkEnv .. := wrapper.claim
        | throw (IO.userError s!"aggregate proof {addr} does not bundle a CheckEnv claim")
      let rc ← Compression.verifyProof addr wrapper (p.hasFlag "dev-srs") statement
      if rc != 0 then return rc
    else
      let ctx ← match ctx? with
        | some c => pure c
        | none =>
          let c ← context p
          ctx? := some c
          pure c
      verifyWrapper ctx .aggr wrapper
      IO.println s!"ok: aggregate {addr} verifies claim {Address.blake3 (Ix.Claim.ser wrapper.claim)}"
      IO.println statement
  return 0

end Ix.Cli.FormalAggregate
end
