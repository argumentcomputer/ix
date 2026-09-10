/-
  Compressing an aggregate root proof to a BN254 PLONK proof.

  An aggregate root (`ix aggregate`) is a multi-stark proof of the `ix_aggr`
  recursion toplevel over Goldilocks. Compression verifies that proof inside
  an Aiur execution of the KoalaBear byte verifier
  (`MultiStark.multiStarkKoalaBear`, entry `verify_multi_stark_proof`) proven
  by SP1 Hypercube, then folds the Hypercube proof through SP1's recursion
  tail — leaf, compose, shrink, BN254 wrap (`Aiur.HypercubeSystem.wrap`) —
  and finishes it with the gnark PLONK stage (`Aiur.HypercubeSystem.plonk`).

  The PLONK proof's public inputs bind the whole chain: the Poseidon2 digest
  of the byte verifier's Hypercube verifying key (which machine ran), the
  digest of its claim — the entry index, the Blake3 digests of the `ix_aggr`
  verifying key and of the claims (`verifierPubInput2`) — and the recursion
  vk allowlist root (which recursion programs folded it).

  Needs `ix-ffi` built with the SP1 recursion tail (`IX_SP1_RECURSION=1`).
-/
module
public import Cli
public import Ix.Address
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.Aiur.Hypercube
public import Ix.Aggr
public import Ix.Claim
public import Ix.Common
public import Ix.IxVM
public import Ix.IxVM.Toplevel
public import Ix.MultiStark
public import Ix.Store

public section

open System (FilePath)

namespace Ix.Cli.Compress

/-- The two deterministic systems whose identities an aggregate root commits
to: the IxVM vk (through the allowlist blob) and the single-entrypoint
recursion system, whose vk and proof the byte verifier receives. -/
structure AggregateBackend where
  system : Aiur.AiurSystem
  aggrIdx : Aiur.Bytecode.FunIdx
  allowed : ByteArray

/-- Every persisted aggregate proof has the same outer claim regardless of
whether its witness used a wrap, flat pair, or structural pair. -/
def aggregateOuterClaim (allowed : ByteArray) (aggrIdx : Aiur.Bytecode.FunIdx)
    (claim : Ix.Claim) : Array Aiur.G :=
  Aiur.buildClaim aggrIdx (Aggr.pubInput allowed (Ix.Claim.ser claim)) #[]

/-- Build the aggregate backend (the same construction `ix verify --aggregate`
uses). -/
def buildAggregateBackend
    (recursionParameters : MultiStark.RecursionParameters) :
    IO (Except String AggregateBackend) := do
  let ixvmCompiled ← match IxVM.ixVM with
    | .error e => return .error s!"IxVM toplevel merging failed: {e}"
    | .ok top => match top.compileWithGroups IxVM.functionGroups with
      | .error e => return .error s!"IxVM compilation failed: {e}"
      | .ok compiled => pure compiled
  let aggrCompiled ← match Aggr.ixAggr with
    | .error e => return .error s!"recursion toplevel merging failed: {e}"
    | .ok top => match top.compileWithGroups Aggr.functionGroups with
      | .error e => return .error s!"recursion compilation failed: {e}"
      | .ok compiled => pure compiled
  let verifyIdx := ixvmCompiled.getFuncIdx `verify_claim |>.get!
  let aggrIdx := aggrCompiled.getFuncIdx `ix_aggr |>.get!
  let ixvmSystem := Aiur.AiurSystem.build ixvmCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let aggrSystem := MultiStark.buildRecursionSystem aggrCompiled.bytecode
    recursionParameters
  let allowed := Aggr.allowedBlob ixvmSystem.vkBytes verifyIdx
    aggrSystem.vkBytes aggrIdx
  return .ok { system := aggrSystem, aggrIdx, allowed }

/-- Decode a proof wrapper only after checking that its bytes reproduce the
content address supplied by the caller. -/
def decodeWrapperAt (proofAddr : Address) (bytes : ByteArray) :
    Except String Ixon.Proof := do
  let actual := Address.blake3 bytes
  if actual != proofAddr then
    throw s!"aggregate proof store object {proofAddr} hashes to {actual}"
  Ixon.Proof.de bytes

/-- What to produce and where. -/
structure Options where
  /-- Stop after the BN254 wrap proof (no gnark stage). -/
  wrapOnly : Bool := false
  /-- Where to write the PLONK proof JSON (default: the `plonk` cache
  namespace of the store, `<proof address>.json`). -/
  out : Option FilePath := none
  /-- Where to write the wrap proof blob, if wanted. -/
  wrapOut : Option FilePath := none
  /-- A file caching the Hypercube proof blob: read instead of proving when
  it exists, written after proving otherwise. -/
  blob : Option FilePath := none

private def hwm : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  pure <| (((s.splitOn "\n").find? (·.startsWith "VmHWM")).getD "VmHWM: ?")
    |>.trimAscii.toString

private def ms (a b : Nat) : String := s!"{b - a} ms"

/-- The byte verifier's Hypercube system: the KoalaBear multi-stark verifier
toplevel, built for `verify_multi_stark_proof` (whose index is returned). -/
def buildVerifierSystem :
    IO (Except String (Aiur.HypercubeSystem × Aiur.Bytecode.FunIdx)) := do
  let vTop ← match MultiStark.multiStarkKoalaBear with
    | .error e => return .error s!"koalabear verifier merge failed: {e}"
    | .ok t => pure t
  let vCompiled ← match vTop.compile with
    | .error e => return .error s!"koalabear verifier compilation failed: {e}"
    | .ok c => pure c
  let some vIdx := vCompiled.getFuncIdx `verify_multi_stark_proof
    | return .error "verify_multi_stark_proof entrypoint not found"
  match Aiur.HypercubeSystem.build vCompiled.bytecode vIdx with
  | .error e => return .error e
  | .ok sys => return .ok (sys, vIdx)

/-- Compress the persisted aggregate root `proofAddr`: verify it natively,
prove its verification on Hypercube, wrap it to BN254 and (unless
`wrapOnly`) produce the PLONK proof. Prints timings; exits 1 on failure. -/
def compressAggregateRoot (recursionParameters : MultiStark.RecursionParameters)
    (opts : Options) (proofAddr : Address) : IO UInt32 := do
  -- ── The root proof and the recursion system it is a proof of.
  let t0 ← IO.monoMsNow
  let backend ← match ← buildAggregateBackend recursionParameters with
    | .error e => IO.eprintln s!"error: {e}"; return 1
    | .ok backend => pure backend
  let bytes ← StoreIO.toIO (Store.read proofAddr)
  let wrapper ← match decodeWrapperAt proofAddr bytes with
    | .ok wrapper => pure wrapper
    | .error e => IO.eprintln s!"error: {e}"; return 1
  let .checkEnv _ _ := wrapper.claim | do
    IO.eprintln s!"error: aggregate proof {proofAddr} does not bundle a CheckEnv claim"
    return 1
  let proof ← match Aiur.Proof.ofBytesChecked wrapper.proof with
    | .ok proof => pure proof
    | .error e =>
      IO.eprintln s!"error: aggregate proof {proofAddr} does not decode: {e}"
      return 1
  let outerClaim := aggregateOuterClaim backend.allowed backend.aggrIdx wrapper.claim
  match backend.system.verify outerClaim proof with
  | .ok () => pure ()
  | .error e => IO.eprintln s!"error: aggregate root failed native verification: {e}"; return 1
  let t1 ← IO.monoMsNow
  IO.println s!"[compress] root {proofAddr} verifies {wrapper.claim}"
  IO.println s!"[compress] backend + native verify {ms t0 t1}"

  -- ── The byte verifier's inputs: proof, vk and claims as advice, their
  -- digests as the public input.
  let proofBytes := proof.toBytes
  let vkBytes := backend.system.vkBytes
  let claimBytes := MultiStark.serializeClaims #[outerClaim]
  let pubInput := MultiStark.verifierPubInput2 vkBytes claimBytes
  let toGs (b : ByteArray) : Array Aiur.G := b.data.map .ofUInt8
  let io := (((default : Aiur.IOBuffer).extend 0 #[Aiur.G.ofNat 0]
    (toGs proofBytes)).extend 1 #[Aiur.G.ofNat 0] (toGs vkBytes)).extend 2
    #[Aiur.G.ofNat 0] (toGs claimBytes)
  IO.println s!"[compress] byte verifier input: proof {proofBytes.size} bytes, \
    vk {vkBytes.size} bytes, claims {claimBytes.size} bytes"

  -- ── Stage 2: the byte verifier proven by Hypercube.
  let (sys, vIdx) ← match ← buildVerifierSystem with
    | .error e => IO.eprintln s!"error: {e}"; return 1
    | .ok r => pure r
  let t2 ← IO.monoMsNow
  IO.println s!"[compress] hypercube machine {ms t1 t2}"
  -- The claim: `[function channel, entry index] ++ public input`.
  let claimS2 := #[Aiur.G.ofNat 0, Aiur.G.ofNat vIdx] ++ pubInput
  let cached? ← match opts.blob with
    | some p => do
      if ← p.pathExists then
        let blob ← IO.FS.readBinFile p
        IO.println s!"[compress] hypercube blob loaded from {p} (prove skipped)"
        pure (some blob)
      else pure none
    | none => pure none
  let blob ← match cached? with
    | some blob => pure blob
    | none =>
      let (claim, blob) ← match sys.prove pubInput io with
        | .ok r => pure r
        | .error e => IO.eprintln s!"error: hypercube prove failed: {e}"; return 1
      if claim != claimS2 then
        IO.eprintln "error: hypercube claim is not the verifier's claim"
        return 1
      if let some p := opts.blob then IO.FS.writeBinFile p blob
      pure blob
  let t3 ← IO.monoMsNow
  IO.println s!"[compress] hypercube prove {ms t2 t3}: blob {blob.size} bytes; {← hwm}"
  match Aiur.HypercubeSystem.verify sys claimS2 blob with
  | .ok () => pure ()
  | .error e => IO.eprintln s!"error: hypercube proof failed verification: {e}"; return 1
  let t4 ← IO.monoMsNow
  IO.println s!"[compress] hypercube verify {ms t3 t4}"

  -- ── The recursion tail: leaf, compose, shrink, wrap.
  let wrapBlob ← match Aiur.HypercubeSystem.wrap sys blob with
    | .ok b => pure b
    | .error e => IO.eprintln s!"error: recursion wrap failed: {e}"; return 1
  let t5 ← IO.monoMsNow
  IO.println s!"[compress] wrap {ms t4 t5}: {wrapBlob.size} bytes; {← hwm}"
  if let some p := opts.wrapOut then
    IO.FS.writeBinFile p wrapBlob
    IO.println s!"[compress] wrap proof written to {p}"
  if opts.wrapOnly then
    return 0

  -- ── PLONK.
  let (plonk, inputs) ← match Aiur.HypercubeSystem.plonk wrapBlob with
    | .ok r => pure r
    | .error e => IO.eprintln s!"error: plonk failed: {e}"; return 1
  let t6 ← IO.monoMsNow
  IO.println s!"[compress] plonk {ms t5 t6}: {plonk.size} bytes JSON"
  IO.println s!"[compress] public inputs: {inputs}"
  let out ← match opts.out with
    | some p => pure p
    | none =>
      let dir ← StoreIO.toIO (Store.cacheDir "plonk")
      pure (dir / s!"{proofAddr}.json")
  if let some dir := out.parent then IO.FS.createDirAll dir
  IO.FS.writeBinFile out plonk
  IO.FS.writeFile (out.withExtension "inputs.txt") s!"{inputs}\n"
  IO.println s!"[compress] plonk proof written to {out}"
  return 0

end Ix.Cli.Compress
