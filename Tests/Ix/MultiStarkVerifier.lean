import LSpec
import Blake3.Rust
import MultiStark.Package
import Ix.FormalProver

/-! # Protocol v6 ($\mathbb{F}_{p^3}$) Aiur Recursive Verifier Cross-Language Fixture Tests

Compiles the formal Aiur recursive verifier (`MultiStark.recursionProgram`, entry point
`MultiStark::verify_multi_stark_proof`) and executes it via `Ix.FormalProver` against
real Rust `multi-stark` Protocol `v6` ($\mathbb{F}_{p^3} = \mathbb{F}_p[X]/(X^3 - X - 1)$,
BLAKE3 `derive_key`, `FriBatching::Tensor`, `vk_digest`) binary fixtures covering:
1. Grouped preprocessed single-shard proof (`Tests/Fixtures/MultiStark/`)
2. Multi-shard proof with inactive fixed table (`Tests/Fixtures/MultiStark/two_shard/`)
3. Single-shard proof without preprocessed trace (`Tests/Fixtures/MultiStark/single_no_prep/`)
4. Two-shard proof with `MEMSEG = 16` cross-shard closure pairs (`Tests/Fixtures/MultiStark/memseg_two_shard/`)

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
  ("memseg_two_shard", "Tests/Fixtures/MultiStark/memseg_two_shard", false)
]

def suite : IO Spec := do
  let system ← loadRecursionSystem
  let loaded ← fixtures.mapM fun (name, dir, hasInactivePrep) => do
    let sys ← IO.FS.readBinFile (dir / "system.bin")
    let prf ← IO.FS.readBinFile (dir / "proof.bin")
    let clm ← IO.FS.readBinFile (dir / "claims.bin")
    return (name, hasInactivePrep, sys, prf, clm)
  return do
    for (name, hasInactivePrep, sys, prf, clm) in loaded do
      if hasInactivePrep then
        -- Strict active-preprocessed invariant: `select_active_prep` rejects shards that
        -- deactivate a circuit with a fixed preprocessed table.
        it s!"{name}: strict active-preprocessed check rejects inactive fixed table" do
          expectFalse (← checkProof system sys clm prf)
      else
        it s!"{name}: valid Protocol v6 Fp^3 Rust proof accepted by Aiur verifier" do
          expect (← checkProof system sys clm prf)
        -- Negative control 1: flip a byte near the end of the proof (FRI/MMCS payload)
        it s!"{name}: tampered proof tail rejected" do
          let badPrf1 := flipByte prf (prf.size - 17)
          expectFalse (← checkProof system sys clm badPrf1)
        -- Negative control 2: flip a byte in the proof header/length prefix
        it s!"{name}: tampered proof header rejected" do
          let badPrf2 := flipByte prf (min 12 (prf.size - 1))
          expectFalse (← checkProof system sys clm badPrf2)
        -- Negative control 3: flip a byte in claims.bin
        it s!"{name}: tampered claims rejected" do
          let badClm := flipByte clm (clm.size - 1)
          expectFalse (← checkProof system sys badClm prf)
        -- Negative control 4: truncated proof rejected without panicking
        it s!"{name}: truncated proof rejected" do
          let truncPrf := prf.extract 0 (prf.size / 2)
          expectFalse (← checkProof system sys clm truncPrf)
        -- Negative control 5: Protocol v5 header downgrade rejected fail-closed
        it s!"{name}: Protocol v5 downgrade rejected fail-closed" do
          let v5Sys := setU16LE sys 0 5
          expectFalse (← checkProof system v5Sys clm prf)
        -- Negative control 6: Fp^2 (extension_degree = 2) header downgrade rejected fail-closed
        it s!"{name}: Fp^2 (ext_degree=2) downgrade rejected fail-closed" do
          let fp2Sys := setU16LE sys 2 2
          expectFalse (← checkProof system fp2Sys clm prf)
        -- Negative control 7: FriBatching::Horner (tag 0) downgrade rejected fail-closed
        it s!"{name}: FriBatching::Horner downgrade rejected fail-closed" do
          let hornerSys := setU16LE sys 4 0
          expectFalse (← checkProof system hornerSys clm prf)

end Tests.Ix.MultiStarkVerifier
