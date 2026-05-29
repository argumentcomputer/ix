import Ix.Aiur.Meta
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Aiur.Statistics
import Ix.MultiStark
import Ix.Keccak
import Tests.Aiur.Common

/-!
# Recursive verifier end-to-end test

A standalone executable that exercises the Multi-STARK verifier scaffold
(`Ix/MultiStark.lean`) against a real proof:

1. Define a tiny Aiur toplevel with a `factorial` entrypoint.
2. Prove `factorial(5) = 120` with the Multi-STARK backend.
3. Serialize that proof (`Proof.toBytes`, bincode) and seed it on the IO
   channel under key `[0]` — the hint the recursive verifier reads
   non-deterministically via `#read_byte_stream`.
4. Run the `verify_multi_stark_proof` entrypoint over that IO buffer and
   prove *its* execution, producing a recursive proof.

Run with `lake exe recursive-verifier`.
-/

open Aiur

private def toHex (b : ByteArray) : String :=
  b.data.foldl (fun s x =>
    let h := String.ofList (Nat.toDigits 16 x.toNat)
    s ++ (if h.length == 1 then "0" ++ h else h)) ""

/-- 8 little-endian bytes of a `Nat` (taken mod 2^64). -/
private def u64le (n : Nat) : Array UInt8 :=
  (Array.range 8).map (fun i => UInt8.ofNat ((n >>> (8 * i)) % 256))

/-- Serialize the public claims for the verifier's IO channel, matching the
in-circuit `read_claims` wire format: u64 `num_claims`, then per claim a u64
`num_vals` followed by the `Val`s as canonical 8-byte little-endian `u64`s. -/
private def serializeClaims (claims : Array (Array Aiur.G)) : ByteArray := Id.run do
  let mut out : Array UInt8 := u64le claims.size
  for c in claims do
    out := out ++ u64le c.size
    for g in c do
      out := out ++ u64le g.val.toNat
  return ⟨out⟩

/-- A tiny Aiur program: `factorial` as the proving entrypoint. -/
def factorialProgram : Source.Toplevel := ⟦
  pub fn factorial(n: G) -> G {
    match n {
      0 => 1,
      _ => n * factorial(n - 1),
    }
  }
⟧

/-- Compile a toplevel and build its proving system, or fail with a message. -/
def buildSystem (label : String) (top : Source.Toplevel) :
    IO (CompiledToplevel × AiurSystem) := do
  let compiled ← match top.compile with
    | .error e => throw <| IO.userError s!"{label}: compilation failed: {e}"
    | .ok c => pure c
  pure (compiled, AiurSystem.build compiled.bytecode commitmentParameters)

/-- Minimal FRI parameters for the *inner* proof: keccak-256 over the serialized
proof runs one keccak-f per 136 bytes, so we keep the proof small (≈ a few KB)
to make the in-circuit hash tractable to execute. Security of the inner proof is
irrelevant for this end-to-end test. -/
def innerFri : FriParameters :=
  { logFinalPolyLen := 0, maxLogArity := 1, numQueries := 1,
    commitProofOfWorkBits := 0, queryProofOfWorkBits := 0 }

def main : IO UInt32 := do
  -- ── 1. factorial system ──────────────────────────────────────────────────
  let (facCompiled, facSystem) ← buildSystem "factorial" factorialProgram
  let facIdx ← match facCompiled.getFuncIdx `factorial with
    | some i => pure i
    | none => IO.eprintln "factorial entrypoint not found"; return 1

  -- ── 2. prove factorial(5) = 120 ──────────────────────────────────────────
  -- `G` is a reserved token (the Aiur DSL), so spell the field type qualified.
  let input := #[Aiur.G.ofNat 5]
  let (claim, proof, _) := facSystem.prove innerFri facIdx input default
  let expected := buildClaim facIdx input #[Aiur.G.ofNat 120]
  if claim != expected then
    IO.eprintln s!"unexpected factorial claim:\n  got {claim}\n  want {expected}"
    return 1
  IO.println s!"✓ proved factorial(5) = 120  (claim = {claim})"
  match facSystem.verify innerFri claim (.ofBytes proof.toBytes) with
  | .error e => IO.eprintln s!"inner proof failed to verify: {e}"; return 1
  | .ok _ => IO.println "✓ inner proof verifies"

  -- ── 3. serialize proof, compute its keccak-256 digest (the public input) ──
  let proofBytes := proof.toBytes
  let blocks := (proofBytes.size + 1) / 136 + 1
  IO.println s!"  serialized proof: {proofBytes.size} bytes  (~{blocks} keccak-f blocks)"
  let digest := Keccak.hash proofBytes
  IO.println s!"  keccak256(proof) = {toHex digest}"
  let digestInput : Array Aiur.G := digest.data.map .ofUInt8
  let proofGs : Array Aiur.G := proofBytes.data.map .ofUInt8

  -- Verifying key (`System<AiurCircuit>`) bytes + its keccak-256 digest.
  let vkBytes := facSystem.vkBytes
  IO.println s!"  verifying key: {vkBytes.size} bytes  (~{(vkBytes.size + 1) / 136 + 1} keccak-f blocks)"
  let sysDigest := Keccak.hash vkBytes
  IO.println s!"  keccak256(vk)    = {toHex sysDigest}"
  let sysDigestInput : Array Aiur.G := sysDigest.data.map .ofUInt8
  let vkGs : Array Aiur.G := vkBytes.data.map .ofUInt8

  -- Public claims (`&[&[Val]]` = the single factorial claim) + keccak digest.
  let claimBytes := serializeClaims #[claim]
  IO.println s!"  claims: {claimBytes.size} bytes"
  let claimsDigest := Keccak.hash claimBytes
  IO.println s!"  keccak256(claims)= {toHex claimsDigest}"
  let claimsDigestInput : Array Aiur.G := claimsDigest.data.map .ofUInt8
  let claimGs : Array Aiur.G := claimBytes.data.map .ofUInt8

  -- Public input = proof digest ++ vk digest ++ claims digest;
  -- IO hints: proof at [0], vk at [1], claims at [2].
  let input : Array Aiur.G := digestInput ++ sysDigestInput ++ claimsDigestInput
  let verifierIO : IOBuffer :=
    (((default : IOBuffer).extend #[Aiur.G.ofNat 0] proofGs).extend #[Aiur.G.ofNat 1] vkGs).extend #[Aiur.G.ofNat 2] claimGs

  -- ── 4. recursive verifier system ─────────────────────────────────────────
  let vTop ← match MultiStark.multiStark with
    | .error e => IO.eprintln s!"verifier toplevel merge failed: {e}"; return 1
    | .ok t => pure t
  let (vCompiled, _vSystem) ← buildSystem "verifier" vTop
  let vIdx ← match vCompiled.getFuncIdx `verify_multi_stark_proof with
    | some i => pure i
    | none => IO.eprintln "verify_multi_stark_proof entrypoint not found"; return 1

  -- ── 5. run the verifier: deserialize proof + vk, recompute keccak digests,
  --       reconstruct the System<AiurCircuit>, run structural checks ──────────
  IO.println "running verifier (proof + verifying-key deserialize + keccak binding)…"
  match vCompiled.bytecode.execute vIdx input verifierIO with
  | .error e => IO.eprintln s!"✗ verifier rejected: {e}"; return 1
  | .ok (_, _, queryCounts) =>
    IO.println "✓ verifier accepted: proof + vk deserialized, both keccak digests match"
    -- ── 6. negative test: a tampered proof digest must be rejected ──────────
    let badInput := input.set! 0 (Aiur.G.ofNat ((digest.data[0]!.toNat + 1) % 256))
    match vCompiled.bytecode.execute vIdx badInput verifierIO with
    | .error _ => IO.println "✓ tampered digest correctly rejected (assert_eq failed)"
    | .ok _ => IO.eprintln "✗ tampered digest was NOT rejected"; return 1
    -- ── 6b. negative test: a tampered CLAIM (with a matching keccak digest)
    --        must be rejected by the OOD / accumulator check. Changing the
    --        claim feeds a different value into Fiat-Shamir (→ different ζ) and
    --        into the lookup accumulator, so the composition/quotient identity
    --        no longer holds even though the keccak binding passes. ──────────
    let badClaim : Array Aiur.G := claim.set! (claim.size - 1) (Aiur.G.ofNat 121)
    let badClaimBytes := serializeClaims #[badClaim]
    let badClaimsDigest := Keccak.hash badClaimBytes
    let badClaimInput : Array Aiur.G :=
      digestInput ++ sysDigestInput ++ (badClaimsDigest.data.map .ofUInt8)
    let badClaimIO : IOBuffer :=
      (((default : IOBuffer).extend #[Aiur.G.ofNat 0] proofGs).extend #[Aiur.G.ofNat 1] vkGs).extend
        #[Aiur.G.ofNat 2] (badClaimBytes.data.map .ofUInt8)
    match vCompiled.bytecode.execute vIdx badClaimInput badClaimIO with
    | .error _ => IO.println "✓ tampered claim correctly rejected (OOD/accumulator mismatch)"
    | .ok _ => IO.eprintln "✗ tampered claim was NOT rejected"; return 1
    -- ── 7. circuit statistics ───────────────────────────────────────────────
    IO.println "\n── verifier circuit statistics ──"
    Aiur.printStats (Aiur.computeStats vCompiled queryCounts)
  pure 0
