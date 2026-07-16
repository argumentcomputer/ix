import Ix.Meta
import Ix.IxVM
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Aiur.Statistics
import Ix.MultiStark
import Ix.TracingTexray
import Ix.Benchmark.Bench
import Ix.Benchmark.Results

/-!
# Ix end-to-end recursion benchmark

Proves an Ix typecheck claim (`Ix.Claim.check` over a constant's transitive
closure, via the IxVM kernel), then runs the in-circuit multi-stark verifier
(`verify_multi_stark_proof`) over that fresh proof: execute it, then prove
THAT execution — the full Ix→recursion pipeline for a real constant, without
needing a `.ixe` (the Lean environment is embedded at compile time via
`get_env!`, and the constant's closure is compiled to Ixon at runtime).

```
lake exe bench-ix-recursion <const> [<const> …] [flags]

lake exe bench-ix-recursion Nat.add_comm --queries 3    # cheap local run (toy soundness)
lake exe bench-ix-recursion Nat.add_comm                # q=100 (soundness level — heavy)

  <const>          fully-qualified constant name(s), e.g. `Nat.add_comm`. Must
                   be importable from this module's import closure (Lean core +
                   Ix's deps); extend this file's imports to reach further.
  --queries N      FRI query count (default 100 = soundness level; the query
                   count IS the soundness level, and the verifier's in-circuit
                   cost scales with it — pass a small value for a cheap run)
  --blowup N       log2 blowup (default 2)
  --pow N          commit PoW bits (default 20)
  --final-poly N   log2 final poly length (default 0)
  --skip-deps      check only the target itself (verify_const, trusting its
                   deps) instead of its whole transitive closure (verify_claim,
                   the default) — a much smaller inner statement
  --execute-only   skip the outer prove: still proves the inner claim and
                   executes the verifier over it (recursive-execute-time /
                   recursive-fft-cost), but stops before the RAM-heavy
                   recursion prove
  --json <path>    write benchmark results rows (Ix.Benchmark.Results), one
                   per constant; rows flush incrementally (execute-side fields
                   land before the outer prove, so an OOM kill keeps them)
  --texray         tracing-texray timeline + RAM; with --json, spans also land
                   at `<json>.spans`
```

The WHOLE system — the inner IxVM prove included — runs under the flag-tuned
parameters, so the verifier's query loop stays proportional to `--queries`;
rows are therefore not comparable across different parameter sets (same
contract as `bench-typecheck --recursive`, which this tool mirrors minus the
`.ixe` plumbing — defaults match its recursion-tuned set). At the full
q=100 soundness level an IxVM-scale verifier execute alone needs >108 GB.

Row metrics mirror `bench-typecheck --recursive`: `constants`/`fft-cost`/
`execute-time` (the inner typecheck), `prove-time`/`throughput`/`peak-rss`/
`proof-size`/`verify-time` (the inner prove), `recursive-execute-time`/
`recursive-fft-cost` (the verifier's execution — the recursion-cost proxy),
and `recursive-prove-time`/`recursive-peak-rss`/`recursive-proof-size`/
`recursive-verify-time` (the outer prove — the headline recursion metrics).

Exit codes: 0 = every constant recursed ok; `exitUsage` = bad invocation;
`exitRejected` = the kernel rejected a constant; 1 = an infrastructure
failure (a verifier reject of a fresh proof, or a failed verification).
-/

open Lean (Json Name)

structure BenchArgs where
  names : Array String := #[]
  queries : Nat := 100
  blowup : Nat := 2
  pow : Nat := 20
  finalPoly : Nat := 0
  skipDeps : Bool := false
  executeOnly : Bool := false
  texray : Bool := false
  json : Option String := none

def parseNatArg (flag v : String) : Except String Nat :=
  match v.toNat? with
  | some n => .ok n
  | none => .error s!"{flag} expects a natural number, got `{v}`"

def parseArgs (cfg : BenchArgs) : List String → Except String BenchArgs
  | [] => .ok cfg
  | "--queries" :: v :: rest => do
    parseArgs { cfg with queries := ← parseNatArg "--queries" v } rest
  | "--blowup" :: v :: rest => do
    parseArgs { cfg with blowup := ← parseNatArg "--blowup" v } rest
  | "--pow" :: v :: rest => do
    parseArgs { cfg with pow := ← parseNatArg "--pow" v } rest
  | "--final-poly" :: v :: rest => do
    parseArgs { cfg with finalPoly := ← parseNatArg "--final-poly" v } rest
  | "--json" :: v :: rest => parseArgs { cfg with json := some v } rest
  | "--skip-deps" :: rest => parseArgs { cfg with skipDeps := true } rest
  | "--execute-only" :: rest => parseArgs { cfg with executeOnly := true } rest
  | "--texray" :: rest => parseArgs { cfg with texray := true } rest
  | arg :: rest =>
    if arg.startsWith "--" then
      .error s!"unknown flag (or flag missing its value): {arg}"
    else
      parseArgs { cfg with names := cfg.names.push arg } rest

def usage : String :=
  "usage: bench-ix-recursion <const> [<const> …] [--queries N] [--blowup N] \
   [--pow N] [--final-poly N] [--skip-deps] [--execute-only] [--json <path>] \
   [--texray]"

/-- Time a thunk, returning its value and the elapsed seconds (the result is
    forced by `blackBoxIO`, same as `bench-typecheck`). -/
def timed (f : Unit → α) : IO (α × Float) := do
  let t0 ← IO.monoNanosNow
  let a ← blackBoxIO f ()
  let t1 ← IO.monoNanosNow
  return (a, (t1 - t0).toFloat / 1e9)

open Ix.Benchmark.Results in
def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs {} args with
    | .ok c => pure c
    | .error e => IO.eprintln s!"error: {e}"; IO.eprintln usage; return exitUsage
  if cfg.names.isEmpty then
    IO.eprintln "error: provide at least one constant name (e.g. Nat.add_comm)"
    IO.eprintln usage
    return exitUsage
  let commitParams : Aiur.CommitmentParameters :=
    { logBlowup := cfg.blowup, capHeight := 0 }
  let friParams : Aiur.FriParameters :=
    { logFinalPolyLen := cfg.finalPoly, maxLogArity := 1,
      numQueries := cfg.queries, commitProofOfWorkBits := cfg.pow,
      queryProofOfWorkBits := 0 }
  IO.println s!"params: logBlowup={cfg.blowup} numQueries={cfg.queries} \
    finalPoly={cfg.finalPoly} pow={cfg.pow}"

  -- The RSS sampler always runs (peak-rss windows); the timeline only under
  -- --texray, and with --json too the spans stream to `<json>.spans`.
  TracingTexray.startSampler
  if cfg.texray then
    TracingTexray.init {}
    if let some path := cfg.json then TracingTexray.jsonSink s!"{path}.spans"

  -- The IxVM kernel (the Ix typechecker), compiled once. The prover system is
  -- built under the flag-tuned parameters: the verifier's query loop scales
  -- with numQueries, so the whole system — inner prove included — must share
  -- them (same contract as `bench-typecheck --recursive`).
  let .ok toplevel := IxVM.ixVM
    | IO.eprintln "Merging IxVM kernel failed"; return 1
  let .ok compiled := toplevel.compile
    | IO.eprintln "Compilation of IxVM kernel failed"; return 1
  let entrypoint := if cfg.skipDeps then `verify_const else `verify_claim
  let some funIdx := compiled.getFuncIdx entrypoint
    | IO.eprintln s!"{entrypoint} entrypoint missing"; return 1
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitParams friParams

  -- The multi-stark verifier toplevel, compiled once (constant-independent);
  -- its prover system only when the outer prove will run.
  let .ok vTop := MultiStark.multiStark
    | IO.eprintln "Merging multi-stark verifier failed"; return 1
  let .ok vCompiled := vTop.compile
    | IO.eprintln "Compilation of multi-stark verifier failed"; return 1
  let some vIdx := vCompiled.getFuncIdx `verify_multi_stark_proof
    | IO.eprintln "verify_multi_stark_proof entrypoint missing"; return 1
  let vSystem? := if cfg.executeOnly then none
    else some (Aiur.AiurSystem.build vCompiled.bytecode commitParams friParams)

  IO.println "loading the embedded Lean environment…"
  let leanEnv ← get_env!

  let writeRow' := fun (name status : String) (fields : List (String × Json)) =>
    match cfg.json with
    | some path => writeRow path name status fields
    | none => pure ()

  let mut anyRejected := false
  let mut anyFailed := false
  for nameStr in cfg.names do
    let name := nameStr.toName
    if !leanEnv.contains name then
      IO.eprintln s!"warning: {nameStr} not found in the embedded Lean \
        environment (extend Benchmarks/IxRecursion.lean's imports to reach \
        it); skipping"
      continue
    try
      -- Lean → Ixon compile of the constant's transitive closure, then the
      -- `verify_claim` witness (claim bytes + closure consts/blobs/hints on
      -- their blake3-keyed IO channels) — or the subject-only `verify_const`
      -- witness under --skip-deps.
      let ixonEnv ← IxVM.ClaimHarness.loadIxonEnv name leanEnv
      let addr ← IxVM.ClaimHarness.lookupAddr ixonEnv name
      let witness ←
        if cfg.skipDeps then
          pure (IxVM.ClaimHarness.buildVerifyConst ixonEnv addr)
        else match IxVM.ClaimHarness.buildClaimWitness ixonEnv (.check addr none) with
          | .ok w => pure w
          | .error e => throw (IO.userError s!"witness build failed: {e}")

      -- Inner execute: the out-of-circuit typecheck. Deterministic, so it
      -- yields the structural metrics (constants / fft-cost) and catches a
      -- kernel reject before any proving cost is paid.
      IO.println s!"executing {entrypoint} for {nameStr} …"
      (← IO.getStdout).flush
      let (execRes, execSec) ← timed fun _ =>
        compiled.bytecode.executeIxVM funIdx witness.input witness.inputIOBuffer
      match execRes with
      | .error e =>
        IO.eprintln s!"❌ {nameStr} FAILED TO TYPECHECK: {e}"
        writeRow' nameStr "rejected" []
        anyRejected := true
      | .ok (_, _, queryCounts) =>
        let stats := Aiur.computeStats compiled queryCounts
        let constants := (IxVM.ClaimHarness.closureFrom ixonEnv addr).size
        IO.println s!"  {nameStr}: constants={constants} \
          fft-cost={stats.totalFftCost} execute={execSec}s"
        let baseFields : List (String × Json) :=
          [ ("constants", Lean.toJson constants)
          , ("fft-cost", jsonRound 0 stats.totalFftCost)
          , ("execute-time", jsonRound 6 execSec) ]
        writeRow' nameStr "ok" baseFields

        -- Inner prove: the Ix proof the recursion step will consume.
        IO.println s!"proving {nameStr} (inner, IxVM) …"
        (← IO.getStdout).flush
        TracingTexray.resetPeakTreeRss
        let ((claim, proof, _), proveSec) ← timed fun _ =>
          aiurSystem.proveIxVM funIdx witness.input witness.inputIOBuffer
        let innerPeak ← TracingTexray.peakTreeRssBytes
        let proofBytes := Aiur.Proof.toBytes proof
        let (verifyRes, verifySec) ← timed fun _ =>
          aiurSystem.verify claim proof
        let verifyOk ← match verifyRes with
          | .ok () => pure true
          | .error e =>
            IO.eprintln s!"  inner verify {nameStr} FAILED: {e}"
            anyFailed := true
            pure false
        IO.println s!"  {nameStr}: prove={proveSec}s verify={verifySec}s \
          proof={proofBytes.size} bytes"
        let baseFields := baseFields ++
          [ ("prove-time", jsonRound 6 proveSec)
          , ("throughput", jsonRound 2 (constants.toFloat / proveSec))
          , ("peak-rss", Lean.toJson innerPeak)
          , ("proof-size", Lean.toJson proofBytes.size) ] ++
          (if verifyOk then [("verify-time", jsonRound 6 verifySec)] else [])
        writeRow' nameStr "ok" baseFields

        -- Recursion, step 1: execute the in-circuit verifier over the fresh
        -- proof (vk/claims wire recipe from Ix/MultiStark.lean).
        IO.println s!"executing verify_multi_stark_proof over {nameStr}'s proof …"
        (← IO.getStdout).flush
        let claimBytes := MultiStark.serializeClaims #[claim]
        let (pubInput, io) := MultiStark.verifierInput proofBytes
          aiurSystem.vkBytes claimBytes commitParams friParams
        let (rvRes, rvSec) ← timed fun _ =>
          vCompiled.bytecode.execute vIdx pubInput io
        match rvRes with
        | .error e =>
          IO.eprintln s!"❌ recursive verifier REJECTED {nameStr}'s proof: {e}"
          anyFailed := true
        | .ok (_, _, qc) =>
          let rvStats := Aiur.computeStats vCompiled qc
          IO.println s!"  {nameStr}: recursive-execute={rvSec}s \
            recursive-fft-cost={rvStats.totalFftCost}"
          IO.println "  === per-circuit breakdown (top FFT contributors) ==="
          Aiur.printStats rvStats
          -- Flush the execute-side pair before the outer prove: an OOM there
          -- keeps them on disk.
          let baseFields := baseFields ++
            [ ("recursive-execute-time", jsonRound 6 rvSec)
            , ("recursive-fft-cost", jsonRound 0 rvStats.totalFftCost) ]
          writeRow' nameStr "ok" baseFields
          -- Recursion, step 2: PROVE the verifier execution (skipped under
          -- --execute-only) — the end-to-end recursion step.
          if let some vSystem := vSystem? then
            IO.println s!"proving the verifier over {nameStr} (outer) …"
            (← IO.getStdout).flush
            TracingTexray.resetPeakTreeRss
            let ((rvClaim, rvProof, _), rvProveSec) ← timed fun _ =>
              vSystem.prove vIdx pubInput io
            let rvPeak ← TracingTexray.peakTreeRssBytes
            let rvProofBytes := Aiur.Proof.toBytes rvProof
            let (rvVerifyRes, rvVerifySec) ← timed fun _ =>
              vSystem.verify rvClaim rvProof
            let rvVerifyOk ← match rvVerifyRes with
              | .ok () => pure true
              | .error e =>
                IO.eprintln s!"  outer verify {nameStr} FAILED: {e}"
                anyFailed := true
                pure false
            IO.println s!"  {nameStr}: recursive-prove={rvProveSec}s \
              recursive-verify={rvVerifySec}s outer proof={rvProofBytes.size} bytes"
            writeRow' nameStr "ok" <| baseFields ++
              [ ("recursive-prove-time", jsonRound 6 rvProveSec)
              , ("recursive-peak-rss", Lean.toJson rvPeak)
              , ("recursive-proof-size", Lean.toJson rvProofBytes.size) ] ++
              (if rvVerifyOk then [("recursive-verify-time", jsonRound 6 rvVerifySec)]
               else [])
    catch e =>
      IO.eprintln s!"  {nameStr} threw: {e}"
      anyFailed := true

  if let some path := cfg.json then
    IO.println s!"results written to {path}"
  if anyRejected then return exitRejected
  return if anyFailed then 1 else 0
