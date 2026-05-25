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
  -- Public input: the 32 digest bytes (grouped by the entrypoint into [[U8;8];4]).
  let digestInput : Array Aiur.G := digest.data.map .ofUInt8
  -- IO hint under key [0]: the proof byte stream the verifier reads.
  let proofGs : Array Aiur.G := proofBytes.data.map .ofUInt8
  let verifierIO : IOBuffer := (default : IOBuffer).extend #[Aiur.G.ofNat 0] proofGs

  -- ── 4. recursive verifier system ─────────────────────────────────────────
  let vTop ← match MultiStark.multiStark with
    | .error e => IO.eprintln s!"verifier toplevel merge failed: {e}"; return 1
    | .ok t => pure t
  let (vCompiled, _vSystem) ← buildSystem "verifier" vTop
  let vIdx ← match vCompiled.getFuncIdx `verify_multi_stark_proof with
    | some i => pure i
    | none => IO.eprintln "verify_multi_stark_proof entrypoint not found"; return 1

  -- ── 5. run the verifier: deserialize + recompute keccak256, assert == digest
  IO.println "running verifier (deserialize + keccak256 over the proof bytes)…"
  match vCompiled.bytecode.execute vIdx digestInput verifierIO with
  | .error e => IO.eprintln s!"✗ verifier rejected the proof: {e}"; return 1
  | .ok (_, _, queryCounts) =>
    IO.println "✓ verifier accepted: deserialized OK and keccak256(bytes) == digest"
    -- ── 6. negative test: a tampered digest must be rejected ────────────────
    let badDigest := digestInput.set! 0 (Aiur.G.ofNat ((digest.data[0]!.toNat + 1) % 256))
    match vCompiled.bytecode.execute vIdx badDigest verifierIO with
    | .error _ => IO.println "✓ tampered digest correctly rejected (assert_eq failed)"
    | .ok _ => IO.eprintln "✗ tampered digest was NOT rejected"; return 1
    -- ── 7. circuit statistics ───────────────────────────────────────────────
    IO.println "\n── verifier circuit statistics ──"
    Aiur.printStats (Aiur.computeStats vCompiled queryCounts)
  pure 0
