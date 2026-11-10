module
public import Ix.Cli.FormalAiur
public import Ix.Cli.Compression
public import Ix.Aggr.Verification

/-! The formal recursive verifier's identity, its trusted acceptance check
(`verify`, `accept`), and the commands that prove on the aggregate
controller. The controller builds every witness, binding discharge
included; the circuits check each fold relation and child proof again, and
`accept` recomputes the expected root statement from the environment before
a root is printed. `Tests/FormalAdvice.lean` keeps a Lean advice builder as
the reference the controller's encoder is checked against. -/
public section
namespace Ix.Cli.FormalAggregate
open Lean Aggr FormalAiur

def artifact (p : Cli.Parsed) (registry : FormalProver.Registry) : IO Selected :=
  aggregationArtifact p registry

structure Identity where
  key : ByteArray
  index : Nat

def identity (system : FormalProver.System) (recursive : Bool) : IO Identity := do
  let (key, index, channel) ← system.identity recursive
  unless channel == Aiur.functionChannel.n do throw (IO.userError "unexpected formal call namespace")
  return { key, index }

/-- How the two certified systems' claims are addressed: their verifying
keys, entry indices and the identity blob aggregates commit to. -/
structure Keys where
  ixvm : Identity
  aggr : Identity
  allowed : ByteArray

/-- The certified IxVM and aggregation programs a command selected: their
package files, their systems and their keys. -/
structure Context extends Keys where
  ixvmArtifact : String
  aggrArtifact : String
  ixvmSystem : FormalProver.System
  aggrSystem : FormalProver.System

def aggrIdentity (p : Cli.Parsed) (registry : FormalProver.Registry) :
    IO (Selected × FormalProver.System × Identity) := do
  let selected ← artifact p registry
  let aggrSystem ← selected.system
  let aggr ← identity aggrSystem true
  return (selected, aggrSystem, aggr)

def context (p : Cli.Parsed) : IO Context := do
  let registry ← FormalProver.Registry.new
  let ixvmSelected ← FormalAiur.artifact p registry
  let ixvmSystem ← ixvmSelected.system
  let (aggrSelected, aggrSystem, aggr) ← aggrIdentity p registry
  let ixvm ← identity ixvmSystem false
  let allowed := Aggr.allowedBlob ixvm.key ixvm.index aggr.key aggr.index
  return { ixvmArtifact := ixvmSelected.path, aggrArtifact := aggrSelected.path, ixvmSystem,
           aggrSystem, ixvm, aggr, allowed }

def outerClaim (ctx : Keys) (kind : ChildKind) (claim : Ix.Claim) : Array Aiur.G :=
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
def wrapInvocation (ctx : Keys) (wrapper : Ixon.Proof) : IO (ByteArray × ByteArray) := do
  let raw ← rawProof .aggr wrapper.proof
  let shape := Aggr.shapeCode (.aggr, none)
  let io := Aggr.extendChild (Aggr.extendVk (Aggr.extendIdentity default ctx.allowed shape) .aggr ctx.aggr.key) 0 raw
    (MultiStark.serializeClaims #[outerClaim ctx .aggr wrapper.claim])
  let claimBytes := Ix.Claim.ser wrapper.claim
  let inv := FormalAiur.invocation (Aggr.pubInput ctx.allowed claimBytes) io "MultiStark::ix_aggr"
  return (raw, inv)

/-- The root statement a compressed proof of `claim` must expose: the public
claim of the backend's `MultiStark::ix_aggr` entrypoint, serialized as one
batch claim. -/
def statementBytes (ctx : Keys) (claim : Ix.Claim) : ByteArray :=
  MultiStark.serializeClaims #[outerClaim ctx .aggr claim]

def verifyWrapper (ctx : Context) (kind : ChildKind) (wrapper : Ixon.Proof) : IO Unit := do
  if kind == .ixvm then return ← FormalAiur.verifyWrapper ctx.ixvmSystem wrapper
  match wrapper.claim with
  | .checkEnv .. | .catalog _ => pure ()
  | _ => throw (IO.userError "aggregate must carry CheckEnv or Catalog")
  let raw ← rawProof .aggr wrapper.proof
  let _ ← ctx.aggrSystem.verify "MultiStark::ix_aggr"
    ((Aggr.pubInput ctx.allowed (Ix.Claim.ser wrapper.claim)).map (·.val)) raw

def manifest (p : Cli.Parsed) (override : Option String := none) : IO (Ixon.Env × Ix.Shard.IxesManifestView × Array Nat) := do
  let some envPath := (p.flag? "ixe").map (·.as! String) | throw (IO.userError "aggregate requires --ixe")
  let some path := override.orElse (fun _ => (p.flag? "ixes").map (·.as! String)) | throw (IO.userError "aggregate requires --ixes")
  let env ← IO.ofExcept (IxVM.ClaimHarness.withDefaultRoleBinding (← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile envPath))))
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile path))
  unless ← Ix.Shard.shardsCover env view.shards do throw (IO.userError "invalid manifest coverage")
  let (view, counts) ← IO.ofExcept (view.pruneEmpty env)
  return (env, view, counts)

/-- The wrapper of a proof the controller returned: decoded from `bytes`
when the controller did not write it to the store (`--no-write`), read from
the store otherwise. Either copy is untrusted until `accept` or `acceptSlot`
checks it; the digest check only ties the bytes to the printed address. -/
def resultWrapper (address : Address) (bytes : ByteArray := .empty) : IO Ixon.Proof := do
  let bytes ← if bytes.size == 0 then StoreIO.toIO (Store.read address) else do
    unless Address.blake3 bytes == address do
      throw (IO.userError s!"the controller's proof bytes do not hash to {address}")
    pure bytes
  IO.ofExcept (Ixon.Proof.de bytes)

/-- The acceptance check of `ix verify --aggregate`, applied to a root that
the untrusted controller produced: the root statement `manifestPath` folds to
is recomputed from the environment, every constant is audited, and the
proof must verify against exactly that claim under the certified artifacts. -/
def accept (p : Cli.Parsed) (ctx : Context) (manifestPath : String) (wrapper : Ixon.Proof) :
    IO Nat := do
  let (env, view, _) ← manifest p manifestPath
  let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
  let root ← IO.ofExcept (Reference.expectedFromManifest env view above)
  let count ← IO.ofExcept (auditAggregateConstants env root)
  unless wrapper.claim == root.claim do
    throw (IO.userError "the controller's root does not prove the manifest's statement")
  verifyWrapper ctx .aggr wrapper
  return count

/-- The acceptance check of `ix aggregate --subtree`/`--reprove-slot`, applied
to the proof the untrusted controller produced for plan slot `slot`: the
slot's statement is recomputed from the environment, and the proof must
verify against exactly that claim under the certified artifacts. A slot below
the root may keep assumptions, so its coverage is not audited. With
`assumeBinding` the slot's claims assume their role binding, as the
controller proves them under `--binding-proof`; only a full root discharges
that assumption, so the accepted claim then still carries it. -/
def acceptSlot (p : Cli.Parsed) (ctx : Context) (manifestPath : String) (slot : Nat)
    (assumeBinding : Bool) (wrapper : Ixon.Proof) : IO Unit := do
  let (env, view, _) ← manifest p manifestPath
  let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
  let slots ← IO.ofExcept (Reference.expectedSlotsFromManifest env view above assumeBinding)
  let some statement := slots[slot]? | throw (IO.userError s!"the plan has no slot {slot}")
  unless wrapper.claim == statement.claim do
    throw (IO.userError s!"the controller's proof of slot {slot} does not prove its statement")
  verifyWrapper ctx .aggr wrapper

/-- `--binding-proof`: a proof of the `binding` claim of `env`'s role binding
(`ix prove-binding`), from a file or the store. It must state exactly that
claim and verify. With `persist` it is then written to the store, and its
address is what the controller takes; without (`--no-write`, `--plan-only`)
nothing is written, and the controller takes the serialized wrapper instead.
Returns the wrapper's address and bytes. With it the claims assume their
binding and the controller's root discharges that assumption once, before
any wrap, so the root states the claim `accept` expects. `--assume-binding`
alone would leave the root conditional, so it requires `--binding-proof`. -/
private def bindingProof (p : Cli.Parsed) (ctx : Context) (env : Ixon.Env) (persist : Bool) :
    IO (Option (Address × ByteArray)) := do
  let path? := (p.flag? "binding-proof").map (·.as! String)
  if path?.isNone && p.hasFlag "assume-binding" then
    throw (IO.userError "--assume-binding: the aggregate root discharges the binding, so pass the proof of its binding claim with --binding-proof (`ix prove-binding`)")
  let some path := path? | return none
  let wrapper ← FormalAiur.readProofFileOrStore path
  let envCtx ← IO.ofExcept (Ix.ClaimContext.ofEnv env false)
  let expected := Ix.Claim.binding envCtx.spec envCtx.binding
  unless wrapper.claim == expected do
    throw (IO.userError s!"binding proof {path} states {wrapper.claim}, expected {expected}")
  FormalAiur.verifyWrapper ctx.ixvmSystem wrapper
  let bytes := Ixon.Proof.ser wrapper
  unless persist do return some (Address.admissionHash bytes, bytes)
  let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser wrapper.claim))
  let address ← StoreIO.toIO (Store.write bytes)
  return some (address, bytes)

/-- `--lanes`/`--aggregate`: the aggregate controller legacy proves with,
and its fold: claims join directly and only the root is wrapped. The root it
returns is accepted only after `accept`, then printed and passed to
`onRoot`. -/
def runController (p : Cli.Parsed) (onRoot : Address → IO Unit := fun _ => pure ()) :
    IO UInt32 := do
  for flag in #["subtree", "reprove-slot", "plan-only", "wrap-root", "range"] do
    if p.hasFlag flag then throw (IO.userError s!"--{flag} applies to `ix aggregate`, not to proving")
  let some ixe := (p.flag? "ixe").map (·.as! String) | throw (IO.userError "missing --ixe")
  let some ixes := (p.flag? "ixes").map (·.as! String) | throw (IO.userError "missing --ixes")
  let (env, handle) ← Ix.Check.loadBoundIxe ixe
  let ctx ← context p
  let binding ← bindingProof p ctx env true
  let options ← hostOptions p
  let gpu := p.hasFlag "lanes"
  let lanes ← if gpu then pure (((p.flag? "lanes").map (·.as! Nat)).getD 1) else jobCount p
  if lanes == 0 then throw (IO.userError "--lanes must be positive")
  -- Legacy's units: --max-ram is per GPU with --lanes and the total with
  -- --jobs; omitted, the controller detects the host's allowance.
  let maxRam := match (p.flag? "max-ram").map (·.as! Nat) with
    | some gib => if gpu then gib * 1024^3 else gib * 1024^3 / lanes
    | none => 0
  let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
  IO.FS.withTempDir fun scratch => do
    let out := ((p.flag? "out-ixes").map (·.as! String)).getD (scratch / "proven.ixes").toString
    let config : FormalProver.LaneConfig := {
      manifest := ixes, lanes, device := options.device, maxRamBytes := maxRam
      execJobs := ((p.flag? "exec-jobs").map (·.as! Nat)).getD 0
      structuralAbove := above, outManifest := some out, select := none
      bindingProof := binding.map (·.1.hash), options := options.job
      useCache := !(p.hasFlag "no-cache"), useIndex := !(p.hasFlag "no-index")
      claimsOnly := false, assumeBinding := false }
    let .root bytes ← FormalProver.proveLanes ctx.ixvmSystem ctx.aggrSystem handle config
      | throw (IO.userError "the controller returned claims instead of a root")
    let address : Address := ⟨bytes⟩
    let root := toString address
    let count ← accept p ctx out (← resultWrapper address)
    IO.println s!"[aiur aggregate] verified coverage of {count} constants, no undischarged assumptions"
    if let some flag := p.flag? "report" then
      IO.FS.writeFile (flag.as! String) (Json.mkObj [("schema", toJson "ix-formal-pipeline/1"),
        ("root", toJson root), ("jobs", toJson lanes), ("proved_leaves", toJson true),
        ("verified", toJson true)]).pretty
    IO.println root
    onRoot address
    return 0

/-- `ix aggregate`: fold the supplied claim proofs into the root, or with
`--subtree` into one subtree, on the aggregate controller, with the fold
`ix prove` uses (claims join directly, the root wrapped on request). A full
root is printed only after `accept`, a subtree or replayed slot only after
`acceptSlot`. Under `--no-write` the controller persists nothing and hands
back the proof's wrapper bytes, which are accepted in the same way. With
`--binding-proof` every claim assumes its binding; a full root discharges it,
while a subtree or replayed slot is accepted, and printed, still assuming
it. -/
def run (p : Cli.Parsed) : IO UInt32 := do
  if p.hasFlag "range" then
    throw (IO.userError "--range wraps single claims, which the controller's fold never does: claims join directly")
  let some ixe := (p.flag? "ixe").map (·.as! String) | throw (IO.userError "aggregate requires --ixe")
  let some ixes := (p.flag? "ixes").map (·.as! String) | throw (IO.userError "aggregate requires --ixes")
  let (env, handle) ← Ix.Check.loadBoundIxe ixe
  let ctx ← context p
  let readOnly := p.hasFlag "no-write" || p.hasFlag "plan-only"
  let binding ← bindingProof p ctx env !readOnly
  let options ← hostOptions p
  let lanes := max 1 (← jobCount p)
  let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
  let subtree := (p.flag? "subtree").map (·.as! Nat)
  let reproveSlot := (p.flag? "reprove-slot").map (·.as! Nat)
  let proofs ← (p.variableArgsAs! String).mapM fun hex => do
    let some address := Address.fromString hex
      | throw (IO.userError s!"expected a 64-character hex address, got {hex}")
    pure address.hash
  let config : FormalProver.AggregateConfig := {
    manifest := ixes, proofs, lanes, device := options.device
    execAhead := ((p.flag? "exec-ahead").map (·.as! Nat)).getD 1
    structuralAbove := above, reproveSlot, subtree
    bindingProof := if readOnly then none else binding.map (·.1.hash)
    options := options.job, planOnly := p.hasFlag "plan-only"
    useCache := !(p.hasFlag "no-cache"), writeOutputs := !(p.hasFlag "no-write")
    wrapRoot := p.hasFlag "wrap-root", assumeBinding := false }
  let bindingBytes := if readOnly then binding.map (·.2) else none
  let some (addressBytes, bytes) ← FormalProver.aggregate ctx.ixvmSystem ctx.aggrSystem handle
      config bindingBytes
    | return 0
  let result : Address := ⟨addressBytes⟩
  let address := toString result
  let wrapper ← resultWrapper result bytes
  match subtree.orElse (fun _ => reproveSlot) with
  | some slot =>
    acceptSlot p ctx ixes slot binding.isSome wrapper
    if binding.isSome then
      IO.eprintln s!"[aiur aggregate] slot {slot} still assumes its role binding: only a full \
        root discharges it, so {address} is not a discharged root"
  | none =>
    let count ← accept p ctx ixes wrapper
    IO.println s!"[aiur aggregate] verified coverage of {count} constants, no undischarged assumptions"
  IO.println address
  return 0

def runPipeline (p : Cli.Parsed) (onRoot : Address → IO Unit := fun _ => pure ()) : IO UInt32 := do
  unless p.hasFlag "ixe" && p.hasFlag "ixes" do
    throw (IO.userError "--lanes/--aggregate/--compress requires --ixe and --ixes")
  for flag in #["shard", "shards", "exec-only"] do
    if p.hasFlag flag then throw (IO.userError s!"--lanes/--aggregate cannot be combined with --{flag}")
  if p.hasFlag "lanes" && p.hasFlag "jobs" then
    throw (IO.userError "choose --lanes for GPU provers or --jobs for CPU provers")
  runController p onRoot

def verify (p : Cli.Parsed) : IO UInt32 := do
  rejectFlags p #["shard", "record"]
  let expected ← match (p.flag? "ixe").map (·.as! String), (p.flag? "ixes").map (·.as! String) with
  | none, none => pure none
  | none, some _ => throw (IO.userError "--ixes requires --ixe")
  | some path, none => do
    let env ← IO.ofExcept (IxVM.ClaimHarness.withDefaultRoleBinding (← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))))
    let some subjects := IxVM.ClaimHarness.envCanonicalTree env | throw (IO.userError "empty environment")
    let envCtx ← IO.ofExcept (Ix.ClaimContext.ofEnv env false)
    let statement : CheckEnvTrees := { ctx := envCtx, subjects, assumptions := none }
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
  let mut ctx? : Option Context := none
  for hex in proofs do
    let some addr := Address.fromString hex | throw (IO.userError "invalid aggregate address")
    let wrapper ← Compression.readProof addr
    unless expected.all (· == wrapper.claim) do throw (IO.userError "aggregate does not match the requested environment/manifest")
    if Compression.isCompressed wrapper.proof then
      let .checkEnv .. := wrapper.claim
        | throw (IO.userError s!"aggregate proof {addr} does not bundle a CheckEnv claim")
      let rc ← Compression.verifyProof addr wrapper (p.hasFlag "dev-srs")
      if rc != 0 then return rc
    else
      let ctx ← match ctx? with
        | some c => pure c
        | none =>
          let c ← context p
          ctx? := some c
          pure c
      verifyWrapper ctx .aggr wrapper
      IO.println s!"ok: aggregate {addr} verifies {wrapper.claim}"
  return 0

end Ix.Cli.FormalAggregate
end
