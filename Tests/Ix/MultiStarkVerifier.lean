import LSpec
import Blake3.Rust
import MultiStark.Package
import Ix.FormalProver
import Ix.Cert.MultiStark.LookupsPlain
import Ix.Cert.MultiStark.Wire
import Ix.Cert.MultiStark.Transcript
import Ix.Cert.MultiStark.Preamble
import Ix.Cert.MultiStark.Verifier

/-! # Protocol v6 ($\mathbb{F}_{p^3}$) Aiur Recursive Verifier Cross-Language Fixture Tests

Compiles the formal Aiur recursive verifier (`MultiStark.recursionProgram`, entry point
`MultiStark::verify_multi_stark_proof`) and executes it via `Ix.FormalProver` against
real Rust `multi-stark` Protocol `v6` ($\mathbb{F}_{p^3} = \mathbb{F}_p[X]/(X^3 - X - 1)$,
BLAKE3 `derive_key`, `FriBatching::Tensor`, `vk_digest`) binary fixtures covering:
1. Grouped preprocessed single-shard proof (`Tests/Fixtures/MultiStark/`)
2. Multi-shard proof with inactive fixed table (`Tests/Fixtures/MultiStark/two_shard/`)
3. Single-shard proof without preprocessed trace (`Tests/Fixtures/MultiStark/single_no_prep/`)
4. Two-shard proof with `MEMSEG = 16` cross-shard closure pairs (`Tests/Fixtures/MultiStark/memseg_two_shard/`)
5. Fixed-table circuit first (`Tests/Fixtures/MultiStark/prep_first/`), with mutants that put
   its fixed table at another height, each rejected

For every accepted fixture, verifies genuine proof acceptance AND rejection of tampered
proof tail, tampered proof header, tampered claims, truncated proof, and Protocol `v5` /
$\mathbb{F}_{p^2}$ / `FriBatching::Horner` header downgrade attacks.
-/

open LSpec
open Ix

namespace Tests.Ix.MultiStarkVerifier

private def flipByte (bs : ByteArray) (idx : Nat) : ByteArray :=
  if h : idx < bs.size then
    bs.set idx (bs[idx]'h ^^^ 0x01) h
  else
    bs

private def setU16LE (bs : ByteArray) (offset : Nat) (val : UInt16) : ByteArray :=
  if offset + 1 < bs.size then
    let b0 := (val &&& 0xff).toUInt8
    let b1 := ((val >>> 8) &&& 0xff).toUInt8
    (bs.set! offset b0).set! (offset + 1) b1
  else
    bs

private def pushUInt64LE (acc : ByteArray) (n : UInt64) : ByteArray := Id.run do
  let mut out := acc
  for i in [0:8] do
    out := out.push (n >>> (8 * i).toUInt64).toUInt8
  return out

private def packBlake3Digest (bs : ByteArray) : Array UInt64 := Id.run do
  let h := (Blake3.Rust.hash bs).val
  let mut words : Array UInt64 := Array.mkEmpty 8
  for i in [0:8] do
    let b0 := h.get! (4 * i) |>.toUInt64
    let b1 := h.get! (4 * i + 1) |>.toUInt64
    let b2 := h.get! (4 * i + 2) |>.toUInt64
    let b3 := h.get! (4 * i + 3) |>.toUInt64
    words := words.push (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))
  return words

private def buildVerifyRequest (sys clm prf : ByteArray) : IO FormalProver.Request := do
  let args := packBlake3Digest sys ++ packBlake3Digest clm
  let mut layout := ByteArray.empty
  let mut bytes := ByteArray.empty
  for (chan, payload) in (#[(0, prf), (1, sys), (2, clm)] : Array (UInt64 × ByteArray)) do
    layout := pushUInt64LE layout chan
    layout := pushUInt64LE layout 0 -- byte stream
    layout := pushUInt64LE layout 1 -- key length = 1
    layout := pushUInt64LE layout 0 -- key = [0]
    layout := pushUInt64LE layout payload.size.toUInt64
    bytes := bytes ++ payload
  FormalProver.Request.buffers MultiStark.recursionEntry args layout bytes ByteArray.empty

private def checkProof (system : FormalProver.System) (sys clm prf : ByteArray) : IO Bool := do
  try
    let req ← buildVerifyRequest sys clm prf
    let out ← system.check req 0 false
    return out.status == 0
  catch _ =>
    return false

private def loadRecursionSystem : IO FormalProver.System := do
  let cacheDir : System.FilePath :=
    System.FilePath.mk ".lake/build/multistark-verifier-cache" / MultiStark.recursionDigest
  IO.FS.createDirAll cacheDir
  let pkgPath := cacheDir / "recursion.ixa"
  if !(← pkgPath.pathExists) then
    let bytes ← MultiStark.compilePackage (aggregate := false) (trace := true)
    IO.FS.writeBinFile pkgPath bytes
  let reg ← FormalProver.Registry.new
  let prog ← reg.load pkgPath.toString
  reg.system prog {}

private def fixtures : List (String × System.FilePath × Bool) := [
  ("grouped_prep_1shard", "Tests/Fixtures/MultiStark", false),
  ("two_shard", "Tests/Fixtures/MultiStark/two_shard", true),
  ("single_no_prep", "Tests/Fixtures/MultiStark/single_no_prep", false),
  ("memseg_two_shard", "Tests/Fixtures/MultiStark/memseg_two_shard", false),
  ("prep_first", "Tests/Fixtures/MultiStark/prep_first", false)
]

/-- Every committed fixture key decodes under `StarkSystem.fromBytes` and satisfies the full
production static check (`Ix.Cert.MultiStark.checkSystem`), matching the security floor and
structural invariants enforced in-circuit by `MultiStark.recursionProgram`. -/
def admissibilitySuite : IO (List TestSeq) := do
  let mut tests : TestSeq := .done
  for (name, dir, _) in fixtures do
    let sys ← IO.FS.readBinFile (dir / "system.bin")
    match Ix.Cert.MultiStark.StarkSystem.fromBytes sys with
    | .ok s =>
      tests := tests ++ test s!"{name}: key decodes and satisfies checkSystem"
        (Ix.Cert.MultiStark.checkSystem s)
    | .error e =>
      tests := tests ++ test s!"{name}: Lean decoder accepts the fixture key ({e})" false
  return [tests]

section DecoderParity

open Ix.Cert.MultiStark
open CertiFri.P3

private def containsSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def pushU16LE (buf : ByteArray) (n : Nat) : ByteArray :=
  let buf := buf.push (n &&& 0xFF).toUInt8
  buf.push ((n >>> 8) &&& 0xFF).toUInt8

private def pushU32LE (buf : ByteArray) (n : Nat) : ByteArray :=
  let buf := buf.push (n &&& 0xFF).toUInt8
  let buf := buf.push ((n >>> 8) &&& 0xFF).toUInt8
  let buf := buf.push ((n >>> 16) &&& 0xFF).toUInt8
  buf.push ((n >>> 24) &&& 0xFF).toUInt8

private def pushU64LE (buf : ByteArray) (n : Nat) : ByteArray :=
  pushU32LE (pushU32LE buf n) (n >>> 32)

private def floorParams : StarkParams := {
  logBlowup := 2
  capHeight := 0
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 128
  commitPowBits := 0
  queryPowBits := 20
}

private def makeSelfConsistent (params : StarkParams) (circuits : Array SysCircuit)
    (prepCommit : Option (Array D) := none)
    (prepIndices : Array (Option Nat) := Array.replicate circuits.size none) : StarkSystem :=
  { vkDigest := computeVkDigest circuits
    params := params
    circuits := circuits
    preprocessedCommit := prepCommit
    preprocessedIndices := prepIndices }

/-- Build raw wire bytes for a minimal 1-circuit verifying key with a single tag-1 (`ConstBig`)
node, optionally populating the canonical `vk_digest` when `rawVal` is a canonical Goldilocks
element. -/
private def rawSingleNodeConstBigKey (rawVal : Nat) (canonicalVk : Bool) : ByteArray := Id.run do
  let digest : D :=
    if canonicalVk then
      match Goldilocks.ofCanonical? (UInt64.ofNat rawVal) with
      | some v =>
        let c : SysCircuit := {
          mainWidth := 1, preprocessedWidth := 0, preprocessedHeight := 0
          maxConstraintDegree := 1, lookupGroupSize := 1, lookupPrefixLen := 0
          nodes := #[.const v], zeros := #[], lookups := #[]
        }
        computeVkDigest #[c]
      | none => default
    else
      default
  let mut buf := ByteArray.empty
  buf := pushU16LE buf 6
  buf := pushU16LE buf 3
  buf := pushU16LE buf 1
  buf := buf ++ digest.toBytes
  buf := pushU16LE buf floorParams.logBlowup
  buf := pushU16LE buf floorParams.capHeight
  buf := pushU16LE buf floorParams.logFinalPolyLen
  buf := pushU16LE buf floorParams.maxLogArity
  buf := pushU16LE buf floorParams.numQueries
  buf := pushU16LE buf floorParams.commitPowBits
  buf := pushU16LE buf floorParams.queryPowBits
  buf := pushU16LE buf 1 -- circuit count
  buf := pushU16LE buf 1 -- mainWidth
  buf := pushU16LE buf 0 -- preprocessedWidth
  buf := pushU32LE buf 0 -- preprocessedHeight
  buf := pushU16LE buf 1 -- maxConstraintDegree
  buf := buf.push 1 -- lookupGroupSize
  buf := pushU16LE buf 1 -- nodeCount
  buf := pushU16LE buf 0 -- lookupPrefixLen
  buf := pushU64LE (buf.push 1) rawVal -- tag 1 (ConstBig) + u64 LE
  buf := pushU16LE buf 0 -- zeroCount
  buf := pushU16LE buf 0 -- lookupCount
  buf := buf.push 0 -- preprocessedCommit = none
  buf := pushU16LE buf 0xFFFF -- preprocessedIndices = #[none]
  return buf

private def expectErr {α : Type} (res : Except String α) (needle : String) : Bool :=
  match res with
  | .error e => containsSubstr e needle
  | .ok _ => false

private def expectOkCheck (bytes : ByteArray) (pred : StarkSystem → Bool) : Bool :=
  match StarkSystem.fromBytes bytes with
  | .ok s => pred s
  | .error _ => false

/-- Parity and negative-control suite for the Lean verifying-key decoder (`StarkSystem.fromBytes`),
static system validator (`checkSystem` / `checkSystemWithFloor`), transcript shape binding
(`observeShape`), and executable `LookupsPlain` checker (`checkLookupsPlain`). -/
def decoderParitySuite : IO (List TestSeq) := do
  let mut tests : TestSeq := .done

  -- 1. Positive checks on all 5 real Rust fixtures (including `prep_first`)
  for (name, dir, hasInactivePrep) in fixtures do
    let sysBytes ← IO.FS.readBinFile (dir / "system.bin")
    let clmBytes ← IO.FS.readBinFile (dir / "claims.bin")
    let prfBytes ← IO.FS.readBinFile (dir / "proof.bin")
    match StarkSystem.fromBytes sysBytes with
    | .error e =>
      tests := tests ++ test s!"{name}: StarkSystem.fromBytes accepts fixture ({e})" false
    | .ok s =>
      tests := tests ++ test s!"{name}: toBytes round-trips byte-identically"
        (s.toBytes == sysBytes)
      tests := tests ++ test s!"{name}: vkDigest matches recomputed computeVkDigest"
        (s.vkDigest == computeVkDigest s.circuits)
      tests := tests ++ test s!"{name}: passes checkSystemWithFloor(allowBelowFloor=true)"
        (checkSystemWithFloor s true)
      tests := tests ++ test s!"{name}: all circuits pass checkLookupsPlain"
        (s.circuits.all checkLookupsPlain)
      let sFloor := { s with params := floorParams }
      tests := tests ++ test s!"{name}: passes StarkSystem.fromBytes and checkSystem at production floor"
        (expectOkCheck sFloor.toBytes fun s2 => checkSystem s2 && s2 == sFloor)
      tests := tests ++ test s!"{name}: verifyBatchBytesWithFloor matches expected acceptance"
        (verifyBatchBytesWithFloor sysBytes clmBytes prfBytes none true hasInactivePrep)
      if hasInactivePrep then
        tests := tests ++ test s!"{name}: strict active-preprocessed rejects inactive fixed table"
          (!verifyBatchBytesWithFloor sysBytes clmBytes prfBytes none true false)

  -- Load grouped_prep_1shard as base production-floor key for single-invariant mutations
  let baseBytes ← IO.FS.readBinFile (System.FilePath.mk "Tests/Fixtures/MultiStark" / "system.bin")
  let .ok baseToy := StarkSystem.fromBytes baseBytes
    | return [tests ++ test "base fixture decode" false]
  let base := { baseToy with params := floorParams }
  let baseFloorBytes := base.toBytes
  tests := tests ++ test "base production-floor key decodes and passes checkSystem"
    (expectOkCheck baseFloorBytes checkSystem)

  -- 2. Header downgrades, vk_digest mismatch, and transcript binding
  tests := tests ++ test "negative: Protocol v5 header rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes (setU16LE baseFloorBytes 0 5)) "Protocol v6")
  tests := tests ++ test "negative: Fp^2 extension_degree rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes (setU16LE baseFloorBytes 2 2)) "cubic extension")
  tests := tests ++ test "negative: FriBatching::Horner tag rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes (setU16LE baseFloorBytes 4 0)) "Tensor")
  tests := tests ++ test "negative: tampered vk_digest rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes (flipByte baseFloorBytes 6)) "vk_digest")
  let badDigestSys := { base with vkDigest := default }
  tests := tests ++ test "negative: mismatched vkDigest rejected by checkSystem"
    (!checkSystem badDigestSys)
  tests := tests ++ test "transcript: observeShape absorbs recomputed vkDigest regardless of stale field"
    (observeShape (initialChallenger base.params) base ==
      observeShape (initialChallenger base.params) badDigestSys)
  let altCirc := { base.circuits[0]! with nodes := base.circuits[0]!.nodes.push (.const Goldilocks.one) }
  let altSys := { base with circuits := base.circuits.set! 0 altCirc }
  tests := tests ++ test "transcript: observeShape changes when circuit graph changes even with fixed vkDigest"
    (observeShape (initialChallenger base.params) base !=
      observeShape (initialChallenger base.params) altSys)

  -- 3. Lookup roots outside lookupPrefixLen
  let c0 := base.circuits[0]!
  let badPrefixC0 := { c0 with lookupPrefixLen := c0.lookupPrefixLen - 1 }
  let badPrefixSys := makeSelfConsistent floorParams (base.circuits.set! 0 badPrefixC0)
    base.preprocessedCommit base.preprocessedIndices
  tests := tests ++ test "negative: lookup root outside lookupPrefixLen rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes badPrefixSys.toBytes) "lookup")
  tests := tests ++ test "negative: lookup root outside lookupPrefixLen rejected by checkSystem"
    (!checkSystem badPrefixSys)
  tests := tests ++ test "negative: lookup root outside lookupPrefixLen rejected by checkLookupsPlain"
    (!checkLookupsPlain badPrefixC0)
  let oobPrefixC0 := { c0 with lookupPrefixLen := c0.nodes.size + 1 }
  let oobPrefixSys := makeSelfConsistent floorParams (base.circuits.set! 0 oobPrefixC0)
    base.preprocessedCommit base.preprocessedIndices
  tests := tests ++ test "negative: lookupPrefixLen > nodes.size rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes oobPrefixSys.toBytes) "lookup_prefix_len")
  tests := tests ++ test "negative: lookupPrefixLen > nodes.size rejected by checkSystem"
    (!checkSystem oobPrefixSys)
  -- Separate multiplicity vs argument root outside lookupPrefixLen
  let badMultCirc : SysCircuit := {
    mainWidth := 1, preprocessedWidth := 0, preprocessedHeight := 0
    maxConstraintDegree := 2, lookupGroupSize := 1, lookupPrefixLen := 1
    nodes := #[.var .main .current 0, .const Goldilocks.one]
    zeros := #[], lookups := #[{ multiplicity := 1, args := #[0] }]
  }
  let badMultSys := makeSelfConsistent floorParams #[badMultCirc]
  tests := tests ++ test "negative: lookup multiplicity outside lookupPrefixLen rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes badMultSys.toBytes) "multiplicity")
  tests := tests ++ test "negative: lookup multiplicity outside lookupPrefixLen rejected by checkLookupsPlain"
    (!checkLookupsPlain badMultCirc)

  -- 4. Derived maxConstraintDegree mismatch, blowup budget, and mul-DAG degree overflow
  let badDegHiC0 := { c0 with maxConstraintDegree := c0.maxConstraintDegree + 1 }
  let badDegHiSys := makeSelfConsistent floorParams (base.circuits.set! 0 badDegHiC0)
    base.preprocessedCommit base.preprocessedIndices
  tests := tests ++ test "negative: inflated maxConstraintDegree rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes badDegHiSys.toBytes) "max_constraint_degree")
  tests := tests ++ test "negative: inflated maxConstraintDegree rejected by checkSystem"
    (!checkSystem badDegHiSys)
  let badDegLoC0 := { c0 with maxConstraintDegree := c0.maxConstraintDegree - 1 }
  let badDegLoSys := makeSelfConsistent floorParams (base.circuits.set! 0 badDegLoC0)
    base.preprocessedCommit base.preprocessedIndices
  tests := tests ++ test "negative: deflated maxConstraintDegree rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes badDegLoSys.toBytes) "max_constraint_degree")
  tests := tests ++ test "negative: deflated maxConstraintDegree rejected by checkSystem"
    (!checkSystem badDegLoSys)
  let deg4Circ : SysCircuit := {
    mainWidth := 1, preprocessedWidth := 0, preprocessedHeight := 0
    maxConstraintDegree := 4, lookupGroupSize := 1, lookupPrefixLen := 0
    nodes := #[.var .main .current 0, .mul 0 0, .mul 1 1]
    zeros := #[2], lookups := #[]
  }
  let lowBlowupParams := { floorParams with logBlowup := 1, numQueries := 238 }
  let blowupExceedSys := makeSelfConsistent lowBlowupParams #[deg4Circ]
  let blowupOkSys := makeSelfConsistent floorParams #[deg4Circ]
  tests := tests ++ test "negative: degree exceeding blowup budget rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes blowupExceedSys.toBytes) "blowup")
  tests := tests ++ test "negative: degree exceeding blowup budget rejected by checkSystem"
    (!checkSystem blowupExceedSys)
  tests := tests ++ test "positive: degree within blowup budget accepted by fromBytes and checkSystem"
    (expectOkCheck blowupOkSys.toBytes checkSystem)
  let overflowNodes : Array GraphNode := Id.run do
    let mut ns : Array GraphNode := #[.var .main .current 0]
    for i in [0:32] do
      ns := ns.push (.mul i i)
    return ns
  let overflowCirc : SysCircuit := {
    mainWidth := 1, preprocessedWidth := 0, preprocessedHeight := 0
    maxConstraintDegree := 1, lookupGroupSize := 1, lookupPrefixLen := 0
    nodes := overflowNodes, zeros := #[32], lookups := #[]
  }
  let overflowSys := makeSelfConsistent floorParams #[overflowCirc]
  tests := tests ++ test "negative: mul-DAG degree overflow rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes overflowSys.toBytes) "overflow")
  tests := tests ++ test "negative: mul-DAG degree overflow rejected by checkSystem"
    (!checkSystem overflowSys)

  -- 5. lookupGroupSize bounds (0 and 9 > MAX_LOOKUP_GROUP = 8; 8 accepted)
  let trivialCirc : SysCircuit := {
    mainWidth := 1, preprocessedWidth := 0, preprocessedHeight := 0
    maxConstraintDegree := 1, lookupGroupSize := 1, lookupPrefixLen := 0
    nodes := #[.var .main .current 0], zeros := #[0], lookups := #[]
  }
  let grp0Sys := makeSelfConsistent floorParams #[{ trivialCirc with lookupGroupSize := 0 }]
  let grp9Sys := makeSelfConsistent floorParams #[{ trivialCirc with lookupGroupSize := 9 }]
  let grp8Sys := makeSelfConsistent floorParams #[{ trivialCirc with lookupGroupSize := 8 }]
  tests := tests ++ test "negative: lookupGroupSize = 0 rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes grp0Sys.toBytes) "lookup group size")
  tests := tests ++ test "negative: lookupGroupSize = 0 rejected by checkSystem"
    (!checkSystem grp0Sys)
  tests := tests ++ test "negative: lookupGroupSize = 9 (> MAX_LOOKUP_GROUP) rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes grp9Sys.toBytes) "lookup group size")
  tests := tests ++ test "negative: lookupGroupSize = 9 (> MAX_LOOKUP_GROUP) rejected by checkSystem"
    (!checkSystem grp9Sys)
  tests := tests ++ test "positive: lookupGroupSize = 8 (MAX_LOOKUP_GROUP) accepted"
    (expectOkCheck grp8Sys.toBytes checkSystem)

  -- 6. Compiler-context parity (lookup prefix forbidden nodes & stage-2 reachable from zeros)
  let forbiddenPrefixNodes : List (String × GraphNode) := [
    ("Public(0)", .publicInput 0),
    ("IsFirstRow", .isFirstRow),
    ("IsLastRow", .isLastRow),
    ("IsTransition", .isTransition),
    ("Var(Stage2)", .var .stage2 .current 0)
  ]
  for (label, badNode) in forbiddenPrefixNodes do
    let rawBadCirc : SysCircuit := {
      mainWidth := 1, preprocessedWidth := 0, preprocessedHeight := 0
      maxConstraintDegree := 2, lookupGroupSize := 1, lookupPrefixLen := 2
      nodes := #[.const Goldilocks.one, badNode]
      zeros := #[], lookups := #[{ multiplicity := 0, args := #[1] }]
    }
    let degs := sweepDegreesTotal rawBadCirc.nodes
    let expectedDeg := deriveLookupDegree degs rawBadCirc.lookups rawBadCirc.lookupGroupSize
    let badCirc := { rawBadCirc with maxConstraintDegree := expectedDeg }
    let badSys := makeSelfConsistent floorParams #[badCirc]
    tests := tests ++ test s!"negative: {label} in lookup prefix rejected by fromBytes"
      (expectErr (StarkSystem.fromBytes badSys.toBytes) "lookup prefix")
    tests := tests ++ test s!"negative: {label} in lookup prefix rejected by checkSystem"
      (!checkSystem badSys)
    tests := tests ++ test s!"negative: {label} in lookup prefix rejected by checkLookupsPlain"
      (!checkLookupsPlain badCirc)
  let s2ZeroDirect : SysCircuit := {
    mainWidth := 1, preprocessedWidth := 0, preprocessedHeight := 0
    maxConstraintDegree := 1, lookupGroupSize := 1, lookupPrefixLen := 0
    nodes := #[.var .stage2 .current 0], zeros := #[0], lookups := #[]
  }
  let s2DirectSys := makeSelfConsistent floorParams #[s2ZeroDirect]
  tests := tests ++ test "negative: stage-2 directly in zero constraint rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes s2DirectSys.toBytes) "stage-2")
  tests := tests ++ test "negative: stage-2 directly in zero constraint rejected by checkSystem"
    (!checkSystem s2DirectSys)
  let s2ZeroIndirect : SysCircuit := {
    mainWidth := 1, preprocessedWidth := 0, preprocessedHeight := 0
    maxConstraintDegree := 2, lookupGroupSize := 1, lookupPrefixLen := 0
    nodes := #[.var .stage2 .current 0, .mul 0 0, .neg 1], zeros := #[2], lookups := #[]
  }
  let s2IndirectSys := makeSelfConsistent floorParams #[s2ZeroIndirect]
  tests := tests ++ test "negative: stage-2 reachable from zero constraint rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes s2IndirectSys.toBytes) "stage-2")
  tests := tests ++ test "negative: stage-2 reachable from zero constraint rejected by checkSystem"
    (!checkSystem s2IndirectSys)
  let selPubZeroCirc : SysCircuit := {
    mainWidth := 1, preprocessedWidth := 0, preprocessedHeight := 0
    maxConstraintDegree := 2, lookupGroupSize := 1, lookupPrefixLen := 0
    nodes := #[.var .main .current 0, .isFirstRow, .mul 0 1, .publicInput 0, .add 2 3]
    zeros := #[4], lookups := #[]
  }
  let selPubSys := makeSelfConsistent floorParams #[selPubZeroCirc]
  tests := tests ++ test "positive: selectors and publics in zero constraints accepted"
    (expectOkCheck selPubSys.toBytes checkSystem)

  -- 7. Preprocessed width/height consistency & power-of-two height
  let badPrepW : SysCircuit := { trivialCirc with preprocessedWidth := 1, preprocessedHeight := 0 }
  let badPrepWSys := makeSelfConsistent floorParams #[badPrepW]
  tests := tests ++ test "negative: preprocessedWidth > 0 with preprocessedHeight == 0 rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes badPrepWSys.toBytes) "preprocessed_width")
  tests := tests ++ test "negative: preprocessedWidth > 0 with preprocessedHeight == 0 rejected by checkSystem"
    (!checkSystem badPrepWSys)
  let dummyRoot : D := base.vkDigest
  let badPrepH : SysCircuit := { trivialCirc with preprocessedWidth := 0, preprocessedHeight := 4 }
  let badPrepHSys := makeSelfConsistent floorParams #[badPrepH] (some #[dummyRoot]) #[some 0]
  tests := tests ++ test "negative: preprocessedWidth == 0 with preprocessedHeight > 0 rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes badPrepHSys.toBytes) "preprocessed_width")
  tests := tests ++ test "negative: preprocessedWidth == 0 with preprocessedHeight > 0 rejected by checkSystem"
    (!checkSystem badPrepHSys)
  let nonPotPrepH : SysCircuit := { trivialCirc with preprocessedWidth := 1, preprocessedHeight := 3 }
  let nonPotSys := makeSelfConsistent floorParams #[nonPotPrepH] (some #[dummyRoot]) #[some 0]
  tests := tests ++ test "negative: non-power-of-two preprocessedHeight rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes nonPotSys.toBytes) "power of two")
  tests := tests ++ test "negative: non-power-of-two preprocessedHeight rejected by checkSystem"
    (!checkSystem nonPotSys)

  -- 8. Canonical ConstBig encodings
  for badVal in ([0, 1, 0xFFFF, Goldilocks.order, Goldilocks.order + 1, 0xFFFFFFFFFFFFFFFF] : List Nat) do
    let badBytes := rawSingleNodeConstBigKey badVal false
    tests := tests ++ test s!"negative: non-canonical ConstBig {badVal} rejected by fromBytes"
      (expectErr (StarkSystem.fromBytes badBytes) "non-canonical")
  for goodVal in ([0x10000, Goldilocks.order - 1] : List Nat) do
    let goodBytes := rawSingleNodeConstBigKey goodVal true
    tests := tests ++ test s!"positive: canonical ConstBig {goodVal} accepted and round-trips"
      (expectOkCheck goodBytes fun s => checkSystem s && s.toBytes == goodBytes)

  -- 9. Node index bounds, topological order, trailer, nonzero capHeight LDE check, PoW cap, EOF
  let oobPubSys := makeSelfConsistent floorParams
    #[{ trivialCirc with nodes := #[.publicInput 12], zeros := #[] }]
  tests := tests ++ test "negative: OOB Public(12) rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes oobPubSys.toBytes) "out of bounds")
  tests := tests ++ test "negative: OOB Public(12) rejected by checkSystem"
    (!checkSystem oobPubSys)
  let oobMainSys := makeSelfConsistent floorParams
    #[{ trivialCirc with nodes := #[.var .main .current 1], zeros := #[] }]
  tests := tests ++ test "negative: OOB Main var rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes oobMainSys.toBytes) "out of bounds")
  tests := tests ++ test "negative: OOB Main var rejected by checkSystem"
    (!checkSystem oobMainSys)
  let oobPrepSys := makeSelfConsistent floorParams
    #[{ trivialCirc with nodes := #[.var .preprocessed .current 0], zeros := #[] }]
  tests := tests ++ test "negative: OOB Preprocessed var rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes oobPrepSys.toBytes) "out of bounds")
  tests := tests ++ test "negative: OOB Preprocessed var rejected by checkSystem"
    (!checkSystem oobPrepSys)
  let oobS2Sys := makeSelfConsistent floorParams
    #[{ trivialCirc with nodes := #[.var .stage2 .current 3], zeros := #[] }]
  tests := tests ++ test "negative: OOB Stage2 var rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes oobS2Sys.toBytes) "out of bounds")
  tests := tests ++ test "negative: OOB Stage2 var rejected by checkSystem"
    (!checkSystem oobS2Sys)
  let oobZeroSys := makeSelfConsistent floorParams
    #[{ trivialCirc with zeros := #[5] }]
  tests := tests ++ test "negative: OOB zero root rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes oobZeroSys.toBytes) "out of bounds")
  tests := tests ++ test "negative: OOB zero root rejected by checkSystem"
    (!checkSystem oobZeroSys)
  let nonTopoSys := makeSelfConsistent floorParams
    #[{ trivialCirc with nodes := #[.neg 0], zeros := #[] }]
  tests := tests ++ test "negative: non-topological node rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes nonTopoSys.toBytes) "topological")
  tests := tests ++ test "negative: non-topological node rejected by checkSystem"
    (!checkSystem nonTopoSys)

  let missingCommitSys := { base with preprocessedCommit := none }
  tests := tests ++ test "negative: missing preprocessed commitment rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes missingCommitSys.toBytes) "missing preprocessed commitment")
  tests := tests ++ test "negative: missing preprocessed commitment rejected by checkSystem"
    (!checkSystem missingCommitSys)
  let extraCommitSys := makeSelfConsistent floorParams #[trivialCirc] (some #[dummyRoot]) #[none]
  tests := tests ++ test "negative: extraneous preprocessed commitment rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes extraCommitSys.toBytes) "no preprocessed circuits")
  tests := tests ++ test "negative: extraneous preprocessed commitment rejected by checkSystem"
    (!checkSystem extraCommitSys)
  let badRankSys := { base with preprocessedIndices := #[none, some 1] }
  tests := tests ++ test "negative: non-canonical preprocessed rank rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes badRankSys.toBytes) "rank")
  tests := tests ++ test "negative: non-canonical preprocessed rank rejected by checkSystem"
    (!checkSystem badRankSys)
  let missingIdxSys := { base with preprocessedIndices := #[none, none] }
  tests := tests ++ test "negative: missing preprocessed index rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes missingIdxSys.toBytes) "preprocessed_height")
  tests := tests ++ test "negative: missing preprocessed index rejected by checkSystem"
    (!checkSystem missingIdxSys)
  for capN in ([0, 2, 3] : List Nat) do
    let badCapSys := { base with preprocessedCommit := some (Array.replicate capN dummyRoot) }
    tests := tests ++ test s!"negative: malformed preprocessed cap len {capN} rejected by fromBytes"
      (expectErr (StarkSystem.fromBytes badCapSys.toBytes) "roots")
    tests := tests ++ test s!"negative: malformed preprocessed cap len {capN} rejected by checkSystem"
      (!checkSystem badCapSys)

  -- Nonzero cap_height LDE root count check (height 2, logBlowup 2 => LDE log 3, capHeight 2 => 4 roots)
  let prep2Circ : SysCircuit := { trivialCirc with preprocessedWidth := 1, preprocessedHeight := 2 }
  let cap2Params := { floorParams with capHeight := 2 }
  let cap2GoodSys := makeSelfConsistent cap2Params #[prep2Circ] (some (Array.replicate 4 dummyRoot)) #[some 0]
  let cap2BadSys := makeSelfConsistent cap2Params #[prep2Circ] (some (Array.replicate 2 dummyRoot)) #[some 0]
  tests := tests ++ test "nonzero capHeight validates against preprocessed LDE height (4 roots ok, checkSystem rejects)"
    (expectOkCheck cap2GoodSys.toBytes fun s => !checkSystem s)
  tests := tests ++ test "negative: nonzero capHeight with unblown root count (2 roots) rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes cap2BadSys.toBytes) "roots")

  let badCommitPowSys := { base with params := { base.params with commitPowBits := 33 } }
  let badQueryPowSys := { base with params := { base.params with queryPowBits := 33 } }
  tests := tests ++ test "negative: commitPowBits > 32 rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes badCommitPowSys.toBytes) "exceeds")
  tests := tests ++ test "negative: commitPowBits > 32 rejected by checkSystemWithFloor(true)"
    (!checkSystemWithFloor badCommitPowSys true)
  tests := tests ++ test "negative: queryPowBits > 32 rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes badQueryPowSys.toBytes) "exceeds")
  tests := tests ++ test "negative: queryPowBits > 32 rejected by checkSystemWithFloor(true)"
    (!checkSystemWithFloor badQueryPowSys true)
  tests := tests ++ test "negative: trailing byte rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes (baseFloorBytes.push 0)) "trailing")
  tests := tests ++ test "negative: truncated key rejected by fromBytes"
    (expectErr (StarkSystem.fromBytes (baseFloorBytes.extract 0 (baseFloorBytes.size - 1))) "eof")

  return [tests]

end DecoderParity

/-- The fixed-table circuit first (`prep_first/`), its log degree changed from 2
(a table of 4 rows) to each of these in the preamble header and the shard proof
(`prep_first/logdeg_<k>/proof.bin`, written by `crates/stark-verifier`'s fixture
test). A fixed table must be bound to its height (a historical soundness bug of
this verifier): with the fixed-table circuit first, the verifier meets the
height assertion of `StarkVerifier::ood_loop` before any other circuit's
out-of-domain check. -/
private def prepFirstHeightMutants : List Nat := [0, 1, 3, 4]

def suite : IO (List TestSeq) := do
  let system ← loadRecursionSystem
  let mut tests : TestSeq := .done
  for (name, dir, hasInactivePrep) in fixtures do
    let sys ← IO.FS.readBinFile (dir / "system.bin")
    let prf ← IO.FS.readBinFile (dir / "proof.bin")
    let clm ← IO.FS.readBinFile (dir / "claims.bin")
    if hasInactivePrep then
      -- Strict active-preprocessed invariant: `select_active_prep` rejects shards that
      -- deactivate a circuit with a fixed preprocessed table.
      let ok ← checkProof system sys clm prf
      tests := tests ++ test s!"{name}: strict active-preprocessed check rejects inactive fixed table"
        (!ok)
    else
      let ok ← checkProof system sys clm prf
      tests := tests ++ test s!"{name}: valid Protocol v6 Fp^3 Rust proof accepted by Aiur verifier" ok
      -- Negative control 1: flip a byte near the end of the proof (FRI/MMCS payload)
      let badPrf1 := flipByte prf (prf.size - 17)
      tests := tests ++ test s!"{name}: tampered proof tail rejected"
        (!(← checkProof system sys clm badPrf1))
      -- Negative control 2: flip a byte in the proof header/length prefix
      let badPrf2 := flipByte prf (min 12 (prf.size - 1))
      tests := tests ++ test s!"{name}: tampered proof header rejected"
        (!(← checkProof system sys clm badPrf2))
      -- Negative control 3: flip a byte in claims.bin
      let badClm := flipByte clm (clm.size - 1)
      tests := tests ++ test s!"{name}: tampered claims rejected"
        (!(← checkProof system sys badClm prf))
      -- Negative control 4: truncated proof rejected without panicking
      let truncPrf := prf.extract 0 (prf.size / 2)
      tests := tests ++ test s!"{name}: truncated proof rejected"
        (!(← checkProof system sys clm truncPrf))
      -- Negative control 5: Protocol v5 header downgrade rejected fail-closed
      let v5Sys := setU16LE sys 0 5
      tests := tests ++ test s!"{name}: Protocol v5 downgrade rejected fail-closed"
        (!(← checkProof system v5Sys clm prf))
      -- Negative control 6: Fp^2 (extension_degree = 2) header downgrade rejected fail-closed
      let fp2Sys := setU16LE sys 2 2
      tests := tests ++ test s!"{name}: Fp^2 (ext_degree=2) downgrade rejected fail-closed"
        (!(← checkProof system fp2Sys clm prf))
      -- Negative control 7: FriBatching::Horner (tag 0) downgrade rejected fail-closed
      let hornerSys := setU16LE sys 4 0
      tests := tests ++ test s!"{name}: FriBatching::Horner downgrade rejected fail-closed"
        (!(← checkProof system hornerSys clm prf))
  -- Negative control 8: a fixed table at a height other than its own is rejected.
  let pfDir : System.FilePath := "Tests/Fixtures/MultiStark/prep_first"
  let pfSys ← IO.FS.readBinFile (pfDir / "system.bin")
  let pfClm ← IO.FS.readBinFile (pfDir / "claims.bin")
  for ld in prepFirstHeightMutants do
    let bad ← IO.FS.readBinFile (pfDir / s!"logdeg_{ld}" / "proof.bin")
    tests := tests ++ test
      s!"prep_first: fixed table of 4 rows at log degree {ld} rejected (height binding)"
      (!(← checkProof system pfSys pfClm bad))
  -- Negative control 9: non-zero commit PoW witness when commit_pow_bits == 0 is rejected.
  let npDir : System.FilePath := "Tests/Fixtures/MultiStark/single_no_prep"
  let npSys ← IO.FS.readBinFile (npDir / "system.bin")
  let npClm ← IO.FS.readBinFile (npDir / "claims.bin")
  let badCpowPrf ← IO.FS.readBinFile (npDir / "nonzero_cpow" / "proof.bin")
  tests := tests ++ test
    "single_no_prep: nonzero commit PoW witness when commit_pow_bits == 0 rejected"
    (!(← checkProof system npSys npClm badCpowPrf))
  -- Negative control 10: natively valid below-floor proof rejected in-circuit.
  let lowDir : System.FilePath := npDir / "below_floor"
  let lowSys ← IO.FS.readBinFile (lowDir / "system.bin")
  let lowClm ← IO.FS.readBinFile (lowDir / "claims.bin")
  let lowPrf ← IO.FS.readBinFile (lowDir / "proof.bin")
  tests := tests ++ test
    "single_no_prep/below_floor: natively valid below-floor proof rejected in-circuit"
    (!(← checkProof system lowSys lowClm lowPrf))
  return [tests] ++ (← admissibilitySuite) ++ (← decoderParitySuite)

end Tests.Ix.MultiStarkVerifier
