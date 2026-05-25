import Ix.Aiur.Meta
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Aiur.Statistics
import Ix.MultiStark
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

def main : IO UInt32 := do
  -- ── 1. factorial system ──────────────────────────────────────────────────
  let (facCompiled, facSystem) ← buildSystem "factorial" factorialProgram
  let facIdx ← match facCompiled.getFuncIdx `factorial with
    | some i => pure i
    | none => IO.eprintln "factorial entrypoint not found"; return 1

  -- ── 2. prove factorial(5) = 120 ──────────────────────────────────────────
  -- `G` is a reserved token (the Aiur DSL), so spell the field type qualified.
  let input := #[Aiur.G.ofNat 5]
  let (claim, proof, _) := facSystem.prove friParameters facIdx input default
  let expected := buildClaim facIdx input #[Aiur.G.ofNat 120]
  if claim != expected then
    IO.eprintln s!"unexpected factorial claim:\n  got {claim}\n  want {expected}"
    return 1
  IO.println s!"✓ proved factorial(5) = 120  (claim = {claim})"
  match facSystem.verify friParameters claim (.ofBytes proof.toBytes) with
  | .error e => IO.eprintln s!"inner proof failed to verify: {e}"; return 1
  | .ok _ => IO.println "✓ inner proof verifies"

  -- ── 3. serialize proof, seed it as the IO hint under key [0] ─────────────
  let proofBytes := proof.toBytes
  IO.println s!"  serialized proof: {proofBytes.size} bytes"
  let proofGs : Array Aiur.G := proofBytes.data.map .ofUInt8
  let verifierIO : IOBuffer := (default : IOBuffer).extend #[Aiur.G.ofNat 0] proofGs

  -- ── 4. recursive verifier system ─────────────────────────────────────────
  let vTop ← match MultiStark.multiStark with
    | .error e => IO.eprintln s!"verifier toplevel merge failed: {e}"; return 1
    | .ok t => pure t
  let (vCompiled, vSystem) ← buildSystem "verifier" vTop
  let vIdx ← match vCompiled.getFuncIdx `verify_multi_stark_proof with
    | some i => pure i
    | none => IO.eprintln "verify_multi_stark_proof entrypoint not found"; return 1

  -- ── 5. run the verifier over the hint, producing a recursive proof ───────
  let (vClaim, vProof, _) := vSystem.prove friParameters vIdx #[] verifierIO
  IO.println s!"✓ recursive verifier executed  (claim = {vClaim})"
  match vSystem.verify friParameters vClaim (.ofBytes vProof.toBytes) with
  | .error e => IO.eprintln s!"recursive proof failed to verify: {e}"; return 1
  | .ok _ => IO.println "✓ recursive proof verifies"
  IO.println s!"  recursive proof: {vProof.toBytes.size} bytes"

  -- ── 6. circuit statistics for the recursive proof ────────────────────────
  IO.println "\n── recursive proof statistics ──"
  match vCompiled.bytecode.execute vIdx #[] verifierIO with
  | .error e => IO.eprintln s!"verifier execution failed: {e}"; return 1
  | .ok (_, _, queryCounts) =>
    Aiur.printStats (Aiur.computeStats vCompiled queryCounts)
  pure 0
