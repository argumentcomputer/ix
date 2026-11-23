module
public import Ix.Cli.FormalAiur
public import Ix.Cli.Compression
public import Ix.Cli.StarkShrinker
public import Ix.Cli.AiurCompression
public import Ix.Cli.ClaimPolicy
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

/-- The certified IxVM and aggregation systems of the command, whose keys
must be the pinned ones (`FormalKeys.pinnedAllowed`); the identity blob is
built from the pins. -/
def context (p : Cli.Parsed) : IO Context := do
  let registry ← FormalProver.Registry.new
  let selected ← selectAll p registry #[.ixvm, .aggregation]
  let (some ixvmSelected, some aggrSelected) := (selected[0]?, selected[1]?)
    | throw (IO.userError "missing selected programs")
  let ixvmSystem ← ixvmSelected.system
  let aggrSystem ← aggrSelected.system
  let aggr ← identity aggrSystem true
  let ixvm ← identity ixvmSystem false
  let allowed ← FormalKeys.pinnedAllowed ixvm.key ixvm.index aggr.key aggr.index
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

/-- The coverage-checked manifest at `path` over `env`, pruned of empty
shards, with each remaining shard's constant count. -/
def manifestOf (env : Ixon.Env) (path : String) :
    IO (Ix.Shard.IxesManifestView × Array Nat) := do
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile path))
  unless ← Ix.Shard.shardsCover env view.shards do throw (IO.userError "invalid manifest coverage")
  IO.ofExcept (view.pruneEmpty env)

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
  let (view, counts) ← manifestOf env path
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

/-- The part of `accept` that depends only on the environment and a
manifest: the manifest as parsed, the root statement it folds to and the
audited count of constants it covers. -/
structure Expected where
  source : Ix.Shard.IxesManifestView
  root : Aggr.CheckEnvTrees
  count : Nat

def expected (p : Cli.Parsed) (env : Ixon.Env) (manifestPath : String) : IO Expected := do
  let (view, _) ← manifestOf env manifestPath
  let source ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifestPath))
  let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
  let root ← IO.ofExcept (Reference.expectedFromManifest env view above)
  let count ← IO.ofExcept (auditAggregateConstants env root)
  return { source, root, count }

/-- The acceptance check of `ix verify --aggregate`, applied to a root that
the untrusted controller produced: the root statement `manifestPath` folds to
is recomputed from the environment, every constant is audited, and the
proof must verify against exactly that claim under the certified artifacts.
`env`, when given, is `--ixe` as `manifest` decodes it. `early` is
`expected` of that environment computed from another manifest, typically
while the controller ran; it stands in for the recomputation only when that
manifest has the same shards and aggregation tree as `manifestPath`, which are
all the statement depends on. -/
def accept (p : Cli.Parsed) (ctx : Context) (manifestPath : String) (wrapper : Ixon.Proof)
    (env : Option Ixon.Env := none) (early : Option (Except IO.Error Expected) := none) :
    IO Nat := do
  let start ← IO.monoMsNow
  let reusable ← match early with
    | some (.ok e) => do
      let parsed ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifestPath))
      pure <| if parsed.shards == e.source.shards
          && parsed.aggregationTree == e.source.aggregationTree
        then some e else none
    | _ => pure none
  let e ← match reusable, env with
    | some e, _ => pure e
    | none, some env => expected p env manifestPath
    | none, none => do expected p (← manifest p manifestPath).1 manifestPath
  unless wrapper.claim == e.root.claim do
    throw (IO.userError "the controller's root does not prove the manifest's statement")
  verifyWrapper ctx .aggr wrapper
  let ms := (← IO.monoMsNow) - start
  IO.eprintln s!"[aiur aggregate] acceptance {ms / 1000}.{ms % 1000 / 100}s, statement \
    {if reusable.isSome then "computed while proving" else "recomputed"}"
  return e.count

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
  -- One lane per GPU unless --lanes or --jobs says otherwise; on a host
  -- without GPUs, --jobs CPU lanes.
  let first := ((← IO.getEnv "MULTI_STARK_CUDA_DEVICE").bind String.toNat?).getD 0
  let gpus := (← resources).gpus - first
  let gpu := p.hasFlag "lanes" || (gpus > 0 && !p.hasFlag "jobs")
  let lanes ← match (p.flag? "lanes").map (·.as! Nat) with
    | some n => pure n
    | none => if gpu then pure gpus else jobCount p
  if lanes == 0 then throw (IO.userError "--lanes must be positive")
  let options := if gpu && options.device.isNone then { options with device := some first }
    else options
  -- --max-ram is the process-wide budget across all lanes; omitted, the
  -- controller uses MemTotal less the 20% host reservation.
  let maxRam := ((p.flag? "max-ram").map (·.as! Nat)).map (· * 1024^3) |>.getD 0
  let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
  let early ← IO.asTask (prio := .dedicated) (expected p env ixes)
  -- The runtime finalizes its task manager before reporting `main`'s error,
  -- and `early` may then wait on tasks that never start, so every failure
  -- below waits for `early` before raising its error.
  try
    IO.FS.withTempDir fun scratch => do
      let out := ((p.flag? "out-ixes").map (·.as! String)).getD (scratch / "proven.ixes").toString
      let config : FormalProver.LaneConfig := {
        manifest := ixes, lanes, device := options.device, maxRamBytes := maxRam
        execJobs := ((p.flag? "exec-jobs").map (·.as! Nat)).getD 0
        structuralAbove := above, outManifest := some out, select := none
        bindingProof := binding.map (·.1.hash), options := options.job
        useCache := !(p.hasFlag "no-cache"), useIndex := !(p.hasFlag "no-index")
        fresh := p.hasFlag "fresh"
        claimsOnly := false, assumeBinding := false }
      let result ← FormalProver.proveLanes ctx.ixvmSystem ctx.aggrSystem handle config
      let .root bytes _ := result
        | throw (IO.userError "the controller returned claims instead of a root")
      let address : Address := ⟨bytes⟩
      let root := toString address
      let count ← accept p ctx out (← resultWrapper address) env (some (← IO.wait early))
      IO.println s!"[aiur aggregate] verified coverage of {count} constants, no undischarged assumptions"
      if let some flag := p.flag? "report" then
        IO.FS.writeFile (flag.as! String) (Json.mkObj [("schema", toJson "ix-formal-pipeline/1"),
          ("root", toJson root), ("jobs", toJson lanes), ("proved_leaves", toJson true),
          ("constants", toJson count),
          ("verified", toJson true)]).pretty
      IO.println root
      onRoot address
      return 0
  catch e => do
    let _ ← IO.wait early
    throw e

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
    let count ← accept p ctx ixes wrapper env
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

/-- Independently verify an Endpoint 1 `IXSTARK6\0` shrunk `Fp^3` STARK proof
(`--stark-128` transparent `v6` or `--stark-128-zk` hiding `v6-zk`) against the
pinned aggregate key and statement (v2 compact 1-circuit Plonkish `FixedRoot`
envelope with zero `.ixa` artifact required, or v1 Aiur `.ixa` envelope for
backwards compatibility and `Catalog` claims), then print the honest trust/ZK
metadata banner and claim statement. -/
def verifyShrunkProof (p : Cli.Parsed) (addr : Address) (wrapper : Ixon.Proof)
    (statement : String) (ctx? : Option Context := none) : IO UInt32 := do
  match wrapper.claim with
  | .checkEnv .. | .catalog _ => pure ()
  | _ => throw (IO.userError s!"shrunk STARK proof {addr} must bundle a CheckEnv or Catalog claim")
  let ver ← match StarkShrinker.envelopeVersion wrapper.proof with
    | some 2 =>
      let .checkEnv .. := wrapper.claim
        | throw (IO.userError s!"Plonkish v2 shrunk STARK proof {addr} requires a CheckEnv claim")
      pure (2 : UInt16)
    | some 1 => pure (1 : UInt16)
    | some v =>
      throw (IO.userError s!"unsupported IXSTARK6 envelope version {v} in shrunk STARK proof {addr} (expected 1 or 2)")
    | none =>
      throw (IO.userError s!"truncated or malformed IXSTARK6 envelope header in shrunk STARK proof {addr}")
  let ctx ← match ctx? with
    | some c => pure c
    | none => context p
  let stmtBytes := statementBytes ctx.toKeys wrapper.claim
  let banner ← if ver == 2 then
      let layout ← Compression.releaseRootLayout ctx.aggr.key
      StarkShrinker.verifyFixedRootRaw ctx.aggr.key layout wrapper.proof stmtBytes
    else
      let verifierPath ← verifierArtifactPath p
      let pinnedDigest ← StarkShrinker.pinnedVerifierDigest
      let expectedInnerVk := (Address.blake3 ctx.aggr.key).hash
      let expectedClaim := (Address.blake3 stmtBytes).hash
      StarkShrinker.verifyRaw verifierPath pinnedDigest wrapper.proof
        expectedInnerVk expectedClaim
  IO.println s!"ok: shrunk Fp^3 STARK proof {addr} verifies claim {Address.blake3 (Ix.Claim.ser wrapper.claim)}"
  IO.println banner
  IO.println statement
  return 0

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
    let (env, view, _) ← manifest p
    let above := ((p.flag? "structural-above").map (·.as! Nat)).getD defaultStructuralAbove
    let root ← IO.ofExcept (Reference.expectedFromManifest env view above)
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
    if AiurCompression.selected p && !AiurCompression.isCompressed wrapper.proof then
      throw (IO.userError "expected an Aiur compression envelope for the supplied verifier")
    if StarkShrinker.isShrunk wrapper.proof then
      let ctx ← match ctx? with
        | some c => pure c
        | none =>
          let c ← context p
          ctx? := some c
          pure c
      let rc ← verifyShrunkProof p addr wrapper statement (some ctx)
      if rc != 0 then return rc
    else if Compression.isCompressed wrapper.proof then
      let .checkEnv .. := wrapper.claim
        | throw (IO.userError s!"aggregate proof {addr} does not bundle a CheckEnv claim")
      if AiurCompression.isCompressed wrapper.proof then
        let opts ← AiurCompression.options p
        let ctx ← match ctx? with
          | some c => pure c
          | none =>
            let c ← context p
            ctx? := some c
            pure c
        AiurCompression.verifyProof opts addr wrapper ctx.aggr.key (statementBytes ctx.toKeys wrapper.claim) (p.hasFlag "dev-srs")
      else
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
