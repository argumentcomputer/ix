import LSpec
import Ix.Cert.MultiStark.Verifier

/-! # Certified Multi-STARK Verifier Cross-Language Fixture Tests

Verifies the Mathlib-free executable verifier `Ix.Cert.MultiStark.verifyBatchBytes`
against real Rust `multi-stark` (`3515632f`) binary fixtures covering:
1. Grouped preprocessed single-shard proof (`Tests/Fixtures/MultiStark/`)
2. Multi-shard proof with shared batch challenger (`Tests/Fixtures/MultiStark/two_shard/`)
3. Single-shard proof without preprocessed trace (`Tests/Fixtures/MultiStark/single_no_prep/`)
4. Two-shard proof with `MEMSEG = 16` cross-shard closure pairs (`Tests/Fixtures/MultiStark/memseg_two_shard/`)

For every fixture, verifies both acceptance of the genuine proof and rejection of
4 distinct tampered variants (corrupted proof byte, corrupted claims byte,
corrupted system byte, and truncated/length-corrupted proof).
-/

open LSpec

namespace Tests.Ix.MultiStarkVerifier

private def flipByte (bs : ByteArray) (idx : Nat) : ByteArray :=
  if h : idx < bs.size then
    bs.set idx (bs[idx]'h ^^^ 0x01) h
  else
    bs

private def fixtures : List (String × System.FilePath) := [
  ("grouped_prep_1shard", "Tests/Fixtures/MultiStark"),
  ("two_shard", "Tests/Fixtures/MultiStark/two_shard"),
  ("single_no_prep", "Tests/Fixtures/MultiStark/single_no_prep"),
  ("memseg_two_shard", "Tests/Fixtures/MultiStark/memseg_two_shard")
]

def suite : IO (List TestSeq) := do
  let mut tests : TestSeq := .done
  for (name, dir) in fixtures do
    let sys ← IO.FS.readBinFile (dir / "system.bin")
    let prf ← IO.FS.readBinFile (dir / "proof.bin")
    let clm ← IO.FS.readBinFile (dir / "claims.bin")
    let ok := Ix.Cert.MultiStark.verifyBatchBytes sys clm prf
    tests := tests ++ test s!"{name}: valid Rust proof accepted" ok
    -- Negative control 1: flip a byte near the end of the proof (FRI/MMCS payload)
    let badPrf1 := flipByte prf (prf.size - 17)
    tests := tests ++ test s!"{name}: tampered proof tail rejected"
      (!Ix.Cert.MultiStark.verifyBatchBytes sys clm badPrf1)
    -- Negative control 2: flip a byte in the proof header/length prefix
    let badPrf2 := flipByte prf (min 12 (prf.size - 1))
    tests := tests ++ test s!"{name}: tampered proof header rejected"
      (!Ix.Cert.MultiStark.verifyBatchBytes sys clm badPrf2)
    -- Negative control 3: flip a byte in claims.bin
    let badClm := flipByte clm (clm.size - 1)
    tests := tests ++ test s!"{name}: tampered claims rejected"
      (!Ix.Cert.MultiStark.verifyBatchBytes sys badClm prf)
    -- Negative control 4: truncated proof rejected without panicking
    let truncPrf := prf.extract 0 (prf.size / 2)
    tests := tests ++ test s!"{name}: truncated proof rejected"
      (!Ix.Cert.MultiStark.verifyBatchBytes sys clm truncPrf)
  return [tests]

end Tests.Ix.MultiStarkVerifier
