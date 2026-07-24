import Ix.Aiur.Meta
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Aiur.Statistics
import Ix.MultiStark
import Ix.TracingTexray
import Ix.Benchmark.Results

open Aiur

/-!
# Recursive-verifier cost benchmark

Proves a tiny fixed statement with the multi-stark backend, runs the in-circuit
recursive verifier (`verify_multi_stark_proof`) over that proof, then proves
and verifies THAT execution — the end-to-end recursion step. Mirrors the setup
of `Tests/MultiStark.lean::endToEndSuite`, but measures cost instead of
asserting accept/reject.

```
lake exe bench-recursive-verifier                 # factorial(5), q=100 (soundness level — heavy)
lake exe bench-recursive-verifier --queries 3     # cheap local run (toy soundness)
lake exe bench-recursive-verifier --execute-only  # skip the outer prove (FFT/exec only)

  --trivial        square(5) instead of factorial(5) — the per-statement floor
  --queries N      FRI query count (default 100 = soundness level; pass a
                   small value for a cheap local run)
  --log-blowup N   log2 blowup            (default 2)
  --pow N          query PoW bits         (default 20)
  --json <path>    write a benchmark results row (Ix.Benchmark.Results); the
                   row lands after the verifier execute and is refined after
                   the outer prove, so a kill mid-prove keeps the execute
                   metrics. `ix bench run --backend aiur-recursive`
                   drives this.
  --json-name <n>  row key (default: the inner entrypoint name)
  --texray         tracing-texray timeline + RAM; with --json, spans also land
                   at `<json>.spans` for the CI drill-down
```

Row metrics: `prove-time`/`proof-size`/`verify-time` (the INNER statement),
`peak-rss` (inner-prove window), `recursive-execute-time`/`recursive-fft-cost` (the
verifier's execution and its in-circuit cost — the recursion-cost proxy), and
`recursive-prove-time`/`recursive-peak-rss`/`recursive-proof-size`/
`recursive-verify-time` (the outer prove — the headline recursion metrics).

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

/-- The most trivial provable statement (`--trivial`): one non-recursive
function, no memory — the floor of the verifier's per-statement cost. -/
def squareProgram : Source.Toplevel := ⟦
  pub fn square(n: G) -> G {
    n * n
  }
⟧

/-- `--queries N`-style overrides for parameter sweeps (e.g. pairing a run
against a config another commit could complete); defaults are the standard
recursion-tuned set. -/
def argNat (args : List String) (flag : String) (dflt : Nat) : Nat :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => v.toNat?.getD dflt
  | _ => dflt

def argStr (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => some v
  | _ => none

def recCommitParams (args : List String) : Aiur.CommitmentParameters :=
  { logBlowup := argNat args "--log-blowup" 2, capHeight := 0 }
def innerFri (args : List String) : Aiur.FriParameters :=
  { logFinalPolyLen := argNat args "--final-poly" 0, maxLogArity := 1,
    numQueries := argNat args "--queries" 100,
    commitProofOfWorkBits := 0, queryProofOfWorkBits := argNat args "--pow" 20 }

def secs (t0 t1 : Nat) : Float := (Float.ofNat (t1 - t0)) / 1e9

open Ix.Benchmark.Results in
def main (args : List String) : IO UInt32 := do
  let doProve := !args.contains "--execute-only"
  let recCommitParams := recCommitParams args
  let innerFri := innerFri args
  let jsonOut := argStr args "--json"
  IO.println s!"params: logBlowup={recCommitParams.logBlowup} \
    numQueries={innerFri.numQueries} finalPoly={innerFri.logFinalPolyLen} \
    pow={innerFri.queryProofOfWorkBits}"
  -- Inner proof: factorial(5) (or `square(5)` under --trivial) under the
  -- multi-stark backend.
  let (program, entry) :=
    if args.contains "--trivial" then (squareProgram, `square)
    else (factorialProgram, `factorial)
  let rowName := (argStr args "--json-name").getD entry.toString
  -- Same texray/sampler arrangement as bench-typecheck: the RSS sampler
  -- always runs (peak-rss windows), the timeline only under --texray, and
  -- with --json too the spans stream to `<json>.spans`.
  TracingTexray.startSampler
  if args.contains "--texray" then
    TracingTexray.init {}
    if let some path := jsonOut then TracingTexray.jsonSink s!"{path}.spans"
  let writeRow' := fun (fields : List (String × Lean.Json)) =>
    match jsonOut with
    | some path => writeRow path rowName "ok" fields
    | none => pure ()
  let facCompiled ← match program.compile with
    | .ok c => pure c
    | .error e => IO.eprintln s!"inner compile failed: {e}"; return 1
  let facSystem := AiurSystem.build facCompiled.bytecode recCommitParams innerFri
  let facIdx := facCompiled.getFuncIdx entry |>.get!
  IO.println s!"proving inner {entry}(5)…"
  TracingTexray.resetPeakTreeRss
  let it0 ← IO.monoNanosNow
  let (claim, proof, _) := facSystem.prove facIdx #[Aiur.G.ofNat 5] default
  let proofBytes := proof.toBytes
  let it1 ← IO.monoNanosNow
  let innerOk := facSystem.verify claim proof matches .ok _
  let it2 ← IO.monoNanosNow
  let innerPeak ← TracingTexray.peakTreeRssBytes
  IO.println s!"inner PROVE: {secs it0 it1} s, \
    proof {proofBytes.size} bytes; inner VERIFY: \
    {secs it1 it2} s ({if innerOk then "ok" else "FAILED"})"
  if !innerOk then
    IO.eprintln "inner proof failed to verify"
    return 1
  -- Proof (advice, channel 0), vk (channel 1), claims (channel 2), plus the
  -- Blake3-bound vk/claims digests as public input (the FRI params ride in
  -- the digest-bound vk). The advice buffer is built natively in Rust from
  -- the raw byte blobs (`executeMultiStark` / `proveMultiStark`).
  let claimBytes := MultiStark.serializeClaims #[claim]
  let vkBytes := facSystem.vkBytes
  let pubInput := MultiStark.verifierPubInput vkBytes claimBytes
  -- Compile the verifier toplevel and run it over the proof.
  let vTop ← match MultiStark.multiStark with
    | .ok t => pure t
    | .error e => IO.eprintln s!"verifier merge failed: {e}"; return 1
  let vCompiled ← match vTop.compile with
    | .ok c => pure c
    | .error e => IO.eprintln s!"verifier compile failed: {e}"; return 1
  let vIdx := vCompiled.getFuncIdx `verify_multi_stark_proof |>.get!
  IO.println "executing verify_multi_stark_proof…"
  -- `--use-bytecode`: route through the generic Aiur interpreter instead of
  -- the codegen'd verifier (same escape hatch as `ix check --use-bytecode`;
  -- useful for iterating on `Ix/MultiStark/*.lean` without regenerating
  -- `crates/ixvm-codegen/src/aiur_multi_stark.rs`, and for measuring the
  -- interpreter ↔ codegen gap).
  let useBytecode := args.contains "--use-bytecode"
  let e0 ← IO.monoNanosNow
  match vCompiled.bytecode.executeMultiStark vIdx pubInput proofBytes vkBytes
    claimBytes useBytecode with
  | .error e => IO.eprintln s!"verifier execution REJECTED: {e}"; return 1
  | .ok (_, qc) =>
    let e1 ← IO.monoNanosNow
    let stats := Aiur.computeStats vCompiled qc
    IO.println s!"verifier accepted, execute {secs e0 e1} s"
    IO.println s!"\n=== recursive verifier in-circuit cost ==="
    IO.println s!"totalFftCost = {stats.totalFftCost}"
    IO.println "\n=== per-circuit breakdown (top FFT contributors) ==="
    Aiur.printStats stats
    -- The execute-side row lands before the outer prove, so an OOM kill
    -- there still leaves these metrics on disk (the orchestrator merges
    -- `status: oom` in over them).
    let baseFields : List (String × Lean.Json) :=
      [ ("prove-time", jsonRound 6 (secs it0 it1))
      , ("proof-size", Lean.toJson proofBytes.size)
      , ("verify-time", jsonRound 6 (secs it1 it2))
      , ("peak-rss", Lean.toJson innerPeak)
      , ("recursive-execute-time", jsonRound 6 (secs e0 e1))
      , ("recursive-fft-cost", jsonRound 0 stats.totalFftCost) ]
    writeRow' baseFields
    if !doProve then
      return 0
    -- PROVE the verifier execution (multi-stark): the recursion step itself.
    IO.println "\n=== PROVING the verifier (multi-stark) ==="
    let vSystem := AiurSystem.build vCompiled.bytecode recCommitParams innerFri
    TracingTexray.resetPeakTreeRss
    let t0 ← IO.monoNanosNow
    let (vclaim, vproof) := vSystem.proveMultiStark vIdx pubInput proofBytes
      vkBytes claimBytes
    let nbytes := vproof.toBytes.size  -- force the (lazy, pure) prove to run
    let t1 ← IO.monoNanosNow
    let outerPeak ← TracingTexray.peakTreeRssBytes
    let outerOk := vSystem.verify vclaim vproof matches .ok _
    let t2 ← IO.monoNanosNow
    IO.println s!"verifier PROVE time: {secs t0 t1} s, proof {nbytes} bytes"
    IO.println s!"verifier proof VERIFY time: \
      {secs t1 t2} s ({if outerOk then "ok" else "FAILED"})"
    if !outerOk then
      IO.eprintln "outer proof failed to verify"
      return 1
    writeRow' <| baseFields ++
      [ ("recursive-prove-time", jsonRound 6 (secs t0 t1))
      , ("recursive-peak-rss", Lean.toJson outerPeak)
      , ("recursive-proof-size", Lean.toJson nbytes)
      , ("recursive-verify-time", jsonRound 6 (secs t1 t2)) ]
    return 0
