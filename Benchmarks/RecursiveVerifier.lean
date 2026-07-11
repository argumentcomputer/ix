import Ix.Aiur.Meta
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Aiur.Statistics
import Ix.MultiStark
import Ix.TracingTexray

open Aiur

/-!
# Recursive-verifier cost benchmark

Proves `factorial(5)` with the multi-stark backend, then runs the in-circuit
recursive verifier (`verify_multi_stark_proof`) over that proof and reports its
cost. Mirrors the setup of `Tests/MultiStark.lean::endToEndSuite`, but measures
cost instead of asserting accept/reject.

```
lake exe bench-recursive-verifier                 # execute + FFT + PROVE (texray) — ~5 s / ~7 GB
lake exe bench-recursive-verifier --execute-only  # skip the prove (FFT/exec only)
```

What it reports:
* **In-circuit FFT cost** (`Σ width·height·log₂(height)`) — the prover-work / RAM
  driver for proving the verifier. This is the headline recursion-cost metric.
* By default, the **end-to-end STARK prove** of the verifier, with `tracing-texray`
  emitting the per-stage timeline (`stage1_commit` / `quotient` / `fri_open`) and
  RAM Δ/peak (~5 s, ~7 GB peak). Pass `--execute-only` to skip the prove on a
  memory-constrained box.

Determinism note: the multi-stark prover is **non-deterministic under `parallel`**
(the same statement yields byte-different valid proofs run-to-run), so the
verifier authenticates slightly different Merkle paths and its FFT drifts ~±15%.
Aiur *execution* FFT is deterministic; pin the inner proof with
`RAYON_NUM_THREADS=1` for exactly reproducible numbers.
-/

def factorialProgram : Source.Toplevel := ⟦
  pub fn factorial(n: G) -> G {
    match n {
      0 => 1,
      _ => n * factorial(n - 1),
    }
  }
⟧

def recCommitParams : Aiur.CommitmentParameters := { logBlowup := 2, capHeight := 0 }
def innerFri : Aiur.FriParameters :=
  { logFinalPolyLen := 0, maxLogArity := 1, numQueries := 3,
    commitProofOfWorkBits := 20, queryProofOfWorkBits := 0 }

def main (args : List String) : IO Unit := do
  let doProve := !args.contains "--execute-only"
  -- Inner proof: factorial(5) under the multi-stark backend.
  let facCompiled ← match factorialProgram.compile with
    | .ok c => pure c | .error e => IO.eprintln s!"factorial compile failed: {e}"; return
  let facSystem := AiurSystem.build facCompiled.bytecode recCommitParams innerFri
  let facIdx := facCompiled.getFuncIdx `factorial |>.get!
  IO.println "proving inner factorial(5)…"
  let it0 ← IO.monoNanosNow
  let (claim, proof, _) := facSystem.prove facIdx #[Aiur.G.ofNat 5] default
  let proofBytes := proof.toBytes
  let it1 ← IO.monoNanosNow
  let innerOk := facSystem.verify claim proof matches .ok _
  let it2 ← IO.monoNanosNow
  IO.println s!"inner PROVE: {(Float.ofNat (it1 - it0)) / 1e9} s, \
    proof {proofBytes.size} bytes; inner VERIFY: \
    {(Float.ofNat (it2 - it1)) / 1e9} s ({if innerOk then "ok" else "FAILED"})"
  -- Proof (advice, channel 0), vk (channel 1), claims (channel 2), plus the
  -- Blake3-bound vk/claims digests and FRI params as public input.
  let claimBytes := MultiStark.serializeClaims #[claim]
  let (pubInput, io) := MultiStark.verifierInput proofBytes facSystem.vkBytes
    claimBytes recCommitParams innerFri
  -- Compile the verifier toplevel and run it over the proof.
  let vTop ← match MultiStark.multiStark with
    | .ok t => pure t | .error e => IO.eprintln s!"verifier merge failed: {e}"; return
  let vCompiled ← match vTop.compile with
    | .ok c => pure c | .error e => IO.eprintln s!"verifier compile failed: {e}"; return
  let vIdx := vCompiled.getFuncIdx `verify_multi_stark_proof |>.get!
  IO.println "executing verify_multi_stark_proof…"
  match vCompiled.bytecode.execute vIdx pubInput io with
  | .error e => IO.eprintln s!"verifier execution failed: {e}"
  | .ok (out, _, qc) =>
    let stats := Aiur.computeStats vCompiled qc
    IO.println s!"verifier output (1=accept): {out}"
    IO.println s!"\n=== recursive verifier in-circuit cost ==="
    IO.println s!"totalFftCost = {stats.totalFftCost}"
    IO.println "\n=== per-circuit breakdown (top FFT contributors) ==="
    Aiur.printStats stats
    if doProve then
      -- PROVE the verifier execution (multi-stark) with texray: per-stage timeline
      -- + RAM Δ/peak (~7 GB).
      IO.println "\n=== PROVING the verifier (multi-stark + texray) ==="
      TracingTexray.init {}
      let vSystem := AiurSystem.build vCompiled.bytecode recCommitParams innerFri
      let t0 ← IO.monoNanosNow
      let (vclaim, vproof, _) := vSystem.prove vIdx pubInput io
      let nbytes := vproof.toBytes.size  -- force the (lazy, pure) prove to run
      let t1 ← IO.monoNanosNow
      let outerOk := vSystem.verify vclaim vproof matches .ok _
      let t2 ← IO.monoNanosNow
      IO.println s!"verifier PROVE time: {(Float.ofNat (t1 - t0)) / 1e9} s, proof {nbytes} bytes"
      IO.println s!"verifier proof VERIFY time: \
        {(Float.ofNat (t2 - t1)) / 1e9} s ({if outerOk then "ok" else "FAILED"})"
