/-
  The shard-proof index: `~/.ix/cache/shard-proofs/<claim-digest-hex>` holds
  the store address of an `Ixon.Proof` wrapper whose bundled `CheckEnv` claim
  has that digest. It is what lets a partially proved partition resume after
  a refinement: a leaf's identity is its claim digest, never its manifest
  index. An index entry is an untrusted hint — readers decode the wrapper,
  compare the bundled claim with the one they expect and verify the proof
  natively before reusing it, the aggregate cache's discipline.
-/
module
public import Ix.Address
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.Claim
public import Ix.Ixon
public import Ix.Store
public import Ix.IxVM.ClaimHarness

public section

namespace Ix.Cli.ShardProofIndex

/-- The index directory: the global `~/.ix/cache/shard-proofs`, or a hermetic
    root for tests. -/
def indexDir (cacheRoot? : Option System.FilePath := none) : IO System.FilePath := do
  match cacheRoot? with
  | some root =>
    let dir := root / "shard-proofs"
    IO.FS.createDirAll dir
    pure dir
  | none => StoreIO.toIO (Store.cacheDir "shard-proofs")

/-- Read an index entry. A missing or malformed entry is a miss, never an
    error: store loading and verification happen separately. -/
def readAddress (dir : System.FilePath) (digest : Address) : IO (Option Address) := do
  let path := dir / toString digest
  if !(← path.pathExists) then return none
  try
    let raw ← IO.FS.readFile path
    pure (Address.fromString raw.trimAscii.toString)
  catch _ => pure none

/-- Atomically replace one index entry. -/
def writeAddress (dir : System.FilePath) (digest addr : Address) : IO Unit := do
  let tmp := dir / s!"{digest}.tmp"
  IO.FS.writeFile tmp s!"{addr}\n"
  IO.FS.rename tmp (dir / toString digest)

/-- Native verification of a persisted shard-proof wrapper against the claim
    the caller expects: the wrapper must decode, bundle exactly `expected`,
    and its proof must verify under `verify_claim`'s public input for that
    claim (the same check `ix verify --shard K` performs). -/
def verifyWrapper (aiurSystem : Aiur.AiurSystem) (compiled : Aiur.CompiledToplevel)
    (expected : Ix.Claim) (proofAddr : Address) : IO (Except String Unit) := do
  try
    let bytes ← StoreIO.toIO (Store.read proofAddr)
    match Ixon.Proof.de bytes with
    | .error e => pure (.error s!"wrapper {proofAddr} does not decode: {e}")
    | .ok wrapper =>
      if wrapper.claim != expected then
        return .error s!"wrapper {proofAddr} bundles a different claim"
      match Aiur.Proof.ofBytesChecked wrapper.proof with
      | .error e => pure (.error s!"proof {proofAddr} does not decode: {e}")
      | .ok proof =>
        let some funIdx := compiled.getFuncIdx `verify_claim
          | return .error "`verify_claim` entrypoint missing from compiled toplevel"
        let input := IxVM.ClaimHarness.packedDigestKey
          (Address.blake3 (Ix.Claim.ser wrapper.claim))
        match aiurSystem.verify (Aiur.buildClaim funIdx input #[]) proof with
        | .ok () => pure (.ok ())
        | .error e => pure (.error s!"proof {proofAddr} does not verify: {e}")
  catch e => pure (.error s!"{e}")

/-- The address of a verified proof of `expected`, if the index has one.
    An entry that fails any check is reported and treated as a miss. -/
def verifiedProof (aiurSystem : Aiur.AiurSystem) (compiled : Aiur.CompiledToplevel)
    (dir : System.FilePath) (expected : Ix.Claim) : IO (Option Address) := do
  let digest := Address.blake3 (Ix.Claim.ser expected)
  let some addr ← readAddress dir digest | return none
  match ← verifyWrapper aiurSystem compiled expected addr with
  | .ok () => pure (some addr)
  | .error e =>
    IO.eprintln s!"[shard-proofs] index entry for {digest} ignored: {e}"
    pure none

end Ix.Cli.ShardProofIndex
