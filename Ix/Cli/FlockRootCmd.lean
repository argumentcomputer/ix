/-
Preflight closed aggregate roots, prove one root, or verify its Stage 3
artifact. JSONL stdout contains one versioned result per requested root;
progress and pre-prove reports go to stderr. A batch reuses only the Aiur
backend, never a root-specific Flock relation.
-/
module
public import Cli
public import Ix.Address
public import Ix.Aiur.Protocol
public import Ix.Aggr
public import Ix.Cli.AggregateCmd
public import Ix.Cli.VerifyCmd
public import Ix.Common
public import Ix.Ixon
public import Ix.MultiStark
public import Ix.Store
public import Ix.Unsigned

public section

namespace Ix.Cli.FlockRootCmd

def outerClaimBytes (claim : Array Aiur.G) : ByteArray :=
  claim.foldl (init := .empty) fun bytes value => bytes ++ value.val.toLEBytes

/-- Flock Stage 3 accepts only closed aggregate roots. -/
def validateBundledClaim (claim : Ix.Claim) : Except String Unit := do
  let .checkEnv _ assumptions := claim
    | throw "aggregate root wrapper does not contain a CheckEnv claim"
  if assumptions.isSome then
    throw "aggregate root retains assumptions; Flock Stage 3 requires a closed root"

/-- Bound reads even if a file grows after opening; do not allocate from an
untrusted file length. The extra byte detects oversized wrappers. -/
def readBounded (path : System.FilePath) (maximum : Nat) : IO ByteArray := do
  let handle ← IO.FS.Handle.mk path .read
  let mut bytes := ByteArray.empty
  repeat
    let chunk ← handle.read (min (1024 * 1024) (maximum + 1 - bytes.size)).toUSize
    if chunk.isEmpty then return bytes
    bytes := bytes ++ chunk
    if bytes.size > maximum then
      throw <| IO.userError s!"{path} exceeds the {maximum}-byte input limit"

/-- Read the canonical wrapper without changing the store. File mode derives
its address from the bytes; address mode also checks the requested identity. -/
def loadAggregateWrapper (rootHex rootFile : String) : IO (Address × Ixon.Proof) := do
  let maximum := 64 * 1024 * 1024 + 4096
  let (address, bytes) ← if rootFile.isEmpty then do
    let some address := Address.fromString rootHex
      | throw <| IO.userError s!"aggregate root: expected a 64-char hex address, got {rootHex}"
    let path ← StoreIO.toIO (Store.existingPath address)
    pure (address, ← readBounded path maximum)
  else do
    let bytes ← readBounded rootFile maximum
    pure (Address.blake3 bytes, bytes)
  let wrapper ← IO.ofExcept <| VerifyCmd.decodeAggregateWrapperAt address bytes
  IO.ofExcept <| validateBundledClaim wrapper.claim
  return (address, wrapper)

abbrev CachedBackend := Option (Except String VerifyCmd.AggregateBackend)

def runRoot (rootHex rootFile mode artifact output limits : String)
    (backendRef : IO.Ref CachedBackend) : IO Lean.Json := do
  let started ← IO.monoNanosNow
  let (address, wrapper) ← loadAggregateWrapper rootHex rootFile
  let recursionParameters := MultiStark.defaultRecursionParameters
  let backendStarted ← IO.monoNanosNow
  let cached ← backendRef.get
  let backend ← match cached with
    | some result => IO.ofExcept result
    | none => do
      let result ← VerifyCmd.buildAggregateBackend recursionParameters
      backendRef.set (some result)
      IO.ofExcept result
  let backendUs := ((← IO.monoNanosNow) - backendStarted) / 1000
  let outerClaim := AggregateCmd.aggregateOuterClaim
    backend.allowed backend.aggrIdx wrapper.claim
  if outerClaim.size != 18 then
    throw <| IO.userError s!"internal ix_aggr claim width is {outerClaim.size}, expected 18"
  IO.eprintln s!"Flock Stage 3 {mode}: aggregate root {address}"
  let report ← Aiur.flockStage3AggregateRoot
    backend.system.vkBytes (outerClaimBytes outerClaim) wrapper.proof
    recursionParameters.fri mode artifact output limits
  let details ← IO.ofExcept (Lean.Json.parse report)
  return Lean.Json.mkObj
    [ ("root_address", Lean.toJson (toString address))
    , ("bundled_claim", Lean.toJson (toString wrapper.claim))
    , ("backend_prepare_us", Lean.toJson backendUs)
    , ("backend_cache", Lean.toJson (if cached.isSome then "hit" else "miss"))
    , ("root_total_us", Lean.toJson (((← IO.monoNanosNow) - started) / 1000))
    , ("details", details) ]

def resourceLimitsJson (p : Cli.Parsed) : Except String String := do
  let mut fields := []
  for (flag, field, scale) in
      [("max-advice-mib", "max_advice_bytes", 1024 * 1024),
       ("max-witness-mib", "max_union_witness_bytes", 1024 * 1024),
       ("max-table-capacity", "max_table_capacity", 1)] do
    if let some value := p.flag? flag then
      let text := value.as! String
      let some n := text.toNat?
        | throw s!"--{flag} requires a positive integer"
      if n == 0 || n * scale > 18446744073709551615 then
        throw s!"--{flag} is outside the positive u64 range after scaling"
      fields := fields ++ [(field, Lean.toJson (n * scale))]
  return (Lean.Json.mkObj fields).compress

def runFlockRootCmd (p : Cli.Parsed) : IO UInt32 := do
  let flag (name : String) := (p.flag? name).map (·.as! String) |>.getD ""
  let mode := if (flag "mode").isEmpty then "preflight" else flag "mode"
  let artifact := flag "artifact"
  let output := flag "output"
  let rootFile := flag "root-file"
  let rootsFile := flag "roots-file"
  let jsonl := p.hasFlag "jsonl"
  try
    if mode != "preflight" && mode != "prove" && mode != "verify" then
      throw <| IO.userError s!"unknown Flock mode {mode} (expected preflight|prove|verify)"
    if mode == "preflight" && (!artifact.isEmpty || !output.isEmpty) then
      throw <| IO.userError "--artifact and --output are not valid with --mode preflight"
    if mode == "prove" && (!artifact.isEmpty || output.isEmpty) then
      throw <| IO.userError "Flock proving requires --output and forbids --artifact"
    if mode == "verify" && (artifact.isEmpty || !output.isEmpty) then
      throw <| IO.userError "Flock verification requires --artifact and forbids --output"
    let limits ← IO.ofExcept (resourceLimitsJson p)
    let mut roots := p.variableArgsAs! String
    if !rootsFile.isEmpty then
      let bytes ← readBounded rootsFile (1024 * 1024)
      let some contents := String.fromUTF8? bytes
        | throw <| IO.userError "--roots-file must be UTF-8"
      roots := roots ++ (contents.splitOn "\n" |>.filterMap fun line =>
        let line := line.trimAscii.toString
        if line.isEmpty || line.startsWith "#" then none else some line).toArray
    if !rootFile.isEmpty then
      if !roots.isEmpty || !rootsFile.isEmpty then
        throw <| IO.userError "--root-file cannot be combined with addresses or --roots-file"
      roots := #[rootFile]
    if roots.isEmpty then
      throw <| IO.userError "expected an aggregate root address, --roots-file, or --root-file"
    if mode != "preflight" && roots.size != 1 then
      throw <| IO.userError "prove and verify require exactly one root; batches use preflight"
    let backendRef ← IO.mkRef (none : CachedBackend)
    let mut failed := false
    for source in roots do
      let common :=
        [("schema", Lean.toJson "ix.flock-stage3.root"), ("version", Lean.toJson (1 : Nat)),
         ("ix_version", Lean.toJson Ix.versionString), ("lean_toolchain", Lean.toJson Lean.versionString),
         ("mode", Lean.toJson mode), ("source", Lean.toJson source)]
      try
        let result ← runRoot source rootFile mode artifact output limits backendRef
        if jsonl then
          IO.println (Lean.Json.mkObj (common ++
            [("status", Lean.toJson "ok"), ("result", result)])).compress
        else
          IO.println s!"ok: Flock Stage 3 {mode} accepted {source}"
          if !output.isEmpty then IO.println s!"  artifact saved to {output}"
      catch error =>
        failed := true
        if jsonl then
          IO.println (Lean.Json.mkObj (common ++
            [("status", Lean.toJson "error"), ("error", Lean.toJson error.toString)])).compress
        else
          IO.eprintln s!"error: Flock Stage 3 {mode} failed for {source}: {error}"
      (← IO.getStdout).flush
    return if failed then 1 else 0
  catch error =>
    IO.eprintln s!"error: {error}"
    return 1

end Ix.Cli.FlockRootCmd

open Ix.Cli.FlockRootCmd in
def flockRootCmd : Cli.Cmd := `[Cli|
  "flock-root" VIA runFlockRootCmd;
  "Preflight closed ix_aggr roots, or prove/verify one root with Flock Stage 3 (IX_FLOCK=1)"

  FLAGS:
    "mode" : String; "preflight | prove | verify (default: preflight)."
    "artifact" : String; "Read a Stage3ArtifactV1 (required for verify)."
    "output" : String; "Atomically save the verified artifact (required for prove; no overwrite)."
    "jsonl"; "Emit one versioned JSON result per root on stdout; progress stays on stderr."
    "roots-file" : String; "Append addresses from a UTF-8 file, one per line (# comments allowed)."
    "root-file" : String; "Read one offline Ixon proof wrapper instead of a store address."
    "max-advice-mib" : String; "Host expanded-advice bound in MiB (default: 256)."
    "max-witness-mib" : String; "Padded z/a/b union bound in MiB, excluding scratch (default: 32768)."
    "max-table-capacity" : String; "Maximum rows/table before wiring compilation (default: 4194304)."

  ARGS:
    ...root : String; "32-byte store addresses; multiple roots are supported in preflight mode."
]

end
