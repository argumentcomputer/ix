import Cli
import Ix.IxVM
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Aiur.Statistics
import Ix.MultiStark
import Ix.TracingTexray
import Ix.Benchmark.Bench
import Ix.Benchmark.Results
import Ix.Cli.ConstsFile
import Ix.Cli.NameResolve

/-!
# Aiur typecheck benchmark

Out-of-circuit **execution** and in-circuit **proving** benchmark for the IxVM
kernel's `verify_claim` entrypoint, run over constants from a serialized
`Ixon.Env` (`.ixe`). Reading the env from a `.ixe` keeps this on Ix's critical
path (same load `ix check --ixe` uses) and avoids importing Lean modules at
runtime. Useful standalone (per-constant timeline + RAM breakdown via
tracing-texray) and as a machine source (benchmark results JSON).

```
lake exe bench-typecheck --ixe <path> --consts <n1,n2,…> [--consts-file <p>] [flags]

  --ixe <path>          serialized `Ixon.Env`, e.g. from `ix compile Foo.lean`
                        (writes `foo.ixe`). Required.
  --consts <n1,n2,…>    comma-separated fully-qualified constant names to
                        benchmark (e.g. `Nat.add_comm,String.append`). Same
                        flag/shape as `ix check --consts`, `zisk-host --consts`,
                        and `sp1-host --consts`.
  --consts-file <path>  additionally read names from a file: one per line, blank
                        lines and `#` comments ignored. Unions with --consts.

  Names (from any source) resolve against the env's named map via
  `String.toName` plus a `toString` fallback (mirrors `ix check --ixe`), so
  numeric / private components round-trip (`Foo.0.Bar`, `_private.M.0.foo`).
  Pass at least one name via --consts or --consts-file.

  --skip-deps    check only each target itself (verify_const, trusting its
                 deps) instead of its whole transitive closure (verify_claim,
                 the default). Same flag as `zisk-host --skip-deps`; reserved
                 for targets too expensive to full-closure-check.
  --json <path>  write per-constant results JSON to <path>. Off by default:
                 normal CLI usage prints only the human-readable summary.
  --texray       enable the tracing-texray timeline + RAM breakdown. With
                 --json <path>, per-phase span timings are also written to
                 <path>.spans (JSON Lines) for the CI drill-down. Off by default.
  --execute-only run only Phase 1 (constants / fft-cost / execute-time) and skip
                 proving — the fast `execute`-mode signal.
  --recursive    after each constant's prove, run the in-circuit multi-stark
                 verifier (`verify_multi_stark_proof`) over the fresh proof:
                 execute it (`recursive-execute-time`, `recursive-fft-cost` — the
                 recursion-cost proxy), then prove that execution end-to-end
                 (`recursive-prove-time`, `recursive-peak-rss`,
                 `recursive-proof-size`, `recursive-verify-time`). The whole
                 system, inner prove included, switches to the recursion-tuned
                 parameters (`recursiveFriParameters`), so recursive rows are
                 NOT comparable to the standard prove cell — they land on
                 their own testbed (`ix bench run --backend aiur --mode
                 recursive`), which stays empty while the IxVM-scale cell
                 OOMs (>108 GB in the verifier execute today; the kill lands
                 as a `status: oom` row that bmf drops). With --texray, both
                 proves stream the same `stark/...` span names, so the summed
                 `phase-stark-*` fields cover the pair. Conflicts with
                 --execute-only.
```

For each constant the harness STARK-checks `Ix.Claim.check addr none` (the full
transitive typecheck) in two phases:

1. **Execute** (every constant): run the bytecode out-of-circuit. Cheap and
   deterministic, so we always record `constants` (closure size), `fft-cost`
   (Σ width·height·log2(height) over circuits — the proving-cost proxy), and
   `execute-time`.
2. **Prove** (cheap→expensive by measured fft-cost): the end-to-end STARK prove,
   recording `prove-time`, the serialized `proof-size` (bytes), and
   `verify-time` (verifying the fresh proof) — prover changes can trade speed
   against proof size or verification cost, so all three are tracked. With
   texray on, each prove emits a per-span timeline (`aiur/execute`,
   `aiur/witness`, `stark/...`) with RAM Δ/peak to stderr.
3. **Recursive** (`--recursive` only, right after each constant's prove): feed
   the fresh proof + vk + claims to `verify_multi_stark_proof`, execute it,
   then prove the verifier execution — the end-to-end recursion cost.

When `--json` is set the file is rewritten after every prove, so an external
`timeout` still leaves a complete file of the results collected so far (cheapest
first). A name absent from the env or whose execution errors is skipped with a
warning, so a single bad name never fails the run. The harness imposes no time
limit; bound a run with an external `timeout` if needed.

The JSON is a flat shape (`{ "<name>": { "constants": …, "fft-cost": …,
"execute-time": …, "prove-time": …, "proof-size": …, "verify-time": …,
"throughput": …, "peak-rss": …, and with --recursive also "recursive-execute-time": …,
"recursive-fft-cost": …, "recursive-prove-time": …, "recursive-peak-rss": …,
"recursive-proof-size": …, "recursive-verify-time": … } }`). `peak-rss` and `throughput` are
phase-scoped by MODE: an `--execute-only` row carries the Phase-1 RSS
high-water and constants/sec over the execute; a prove row carries the
prover's high-water and constants/sec over the prove (with `prove-time`,
`proof-size`, `verify-time` present only once proven). The two modes are
stored on separate bencher testbeds, so the shared names never collide. Any
bencher-specific reshaping is the caller's job (see
`.github/workflows/bench-main.yml`).
-/

open Lean (Json Name)

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 1
  capHeight := 0
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

/-- Recursion-tuned commitment parameters for `--recursive`, matching
    `bench-recursive-verifier`'s defaults. -/
def recursiveCommitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 2
  capHeight := 0
}

/-- Recursion-tuned FRI parameters: the in-circuit verifier's cost scales with
    the inner proof's query count, so the recursion configuration trades
    queries (3, not 100) for blowup and commit proof-of-work. `--recursive`
    runs the WHOLE system — the inner prove included — under these, so its
    rows are not comparable to the standard `prove` cell's. -/
def recursiveFriParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 3
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}



/-- Per-constant measurements. `proveSec` is `none` when the constant was
    executed but not (yet) proven. -/
structure Result where
  name : String
  constants : Nat
  fftCost : Float
  executeSec : Float
  /-- The kernel REJECTED the constant (Phase-1 check error). The JSON entry
      is `{"status": "rejected"}` (see `Ix.Benchmark.Results`) — a rejected
      constant is a correctness signal, not a benchmark datum — Phase 2
      skips it, and the run exits with the reserved rejection code. -/
  failed : Bool := false
  proveSec : Option Float := none
  /-- Serialized proof size in bytes (`Aiur.Proof.toBytes`). Tracked because
      prover changes can trade speed against proof size. -/
  proofSize : Option Nat := none
  /-- Wall time of `AiurSystem.verify` over the fresh proof — the other side
      of the same trade-off. `none` if verification failed (reported loudly). -/
  verifySec : Option Float := none
  /-- The constant's prove-phase RSS high-water in bytes (tracing-texray
      tree sampler; the window resets per prove). -/
  peakRss : Option Nat := none
  /-- The constant's own Phase-1 (execute) RSS high-water mark — the sampler
      window resets per constant. Emitted as `peak-rss` in execute-only
      mode; a prove row's `peak-rss` is the prover's window instead (the
      prover would dwarf an execute peak, so the modes never share a row —
      or a testbed). -/
  executePeakRss : Option Nat := none
  /-- Wall time of executing the in-circuit multi-stark verifier over this
      constant's fresh proof (`--recursive` only). -/
  recursiveExecuteSec : Option Float := none
  /-- That execution's own in-circuit FFT cost — the deterministic proxy for
      what proving the verifier costs. Drifts ~±15% run-to-run: the parallel
      prover emits byte-different valid proofs, so the verifier authenticates
      different Merkle paths (pin with `RAYON_NUM_THREADS=1`). -/
  recursiveFftCost : Option Float := none
  /-- Wall time of PROVING the verifier execution — the end-to-end recursion
      cost. -/
  recursiveProveSec : Option Float := none
  /-- The outer (recursion) prove's RSS high-water (windowed like `peakRss`;
      the outer prove dwarfs the verifier execution, so one field serves). -/
  recursivePeakRss : Option Nat := none
  /-- Serialized outer proof size in bytes. -/
  recursiveProofSize : Option Nat := none
  /-- Wall time of `AiurSystem.verify` over the outer proof; `none` if that
      verification failed (reported loudly). -/
  recursiveVerifySec : Option Float := none
  deriving Inhabited

/-- A `Json` number with at most `d` decimal places, rendered decimally.
    `Float`'s own `ToJson` prints the full binary representation
    (`0.02602000000000000146…`), so build the `JsonNumber` (mantissa ·
    10⁻ᵈ) directly from the rounded value instead. -/
def jsonRound (d : Nat) (f : Float) : Json :=
  let scale := (10.0 : Float) ^ d.toFloat
  let scaled := f * scale
  let m : Int :=
    if scaled < 0 then -Int.ofNat (-scaled).round.toUInt64.toNat
    else Int.ofNat scaled.round.toUInt64.toNat
  Json.num ⟨m, d⟩

/-- Flat results object: `name → { constants, fft-cost, execute-time, … }`.
    No bencher-specific shaping.

    `peak-rss` and `throughput` are PHASE-SCOPED BY MODE, not by name: an
    execute-only run's row carries the Phase-1 peak and constants/sec over
    the execute; a prove run's row carries the prove-phase peak and
    constants/sec over the prove. The two modes upload to separate bencher
    testbeds (aiur-check-execute-* / aiur-check-prove-*), so the shared names never
    collide — run the execute cell when you want execute-side numbers. -/
def Result.toJsonEntry (executeOnly : Bool) (r : Result) : String × Json :=
  if r.failed then
    (r.name, Json.mkObj [("status", Json.str "rejected")]) else
  let base : List (String × Json) :=
    [ ("status", Json.str "ok")
    , ("constants", Lean.toJson r.constants)
    , ("fft-cost", jsonRound 0 r.fftCost)
    , ("execute-time", jsonRound 6 r.executeSec) ]
  if executeOnly then
    let fields := if r.executeSec > 0 then
      base ++ [ ("throughput", jsonRound 2 (r.constants.toFloat / r.executeSec)) ]
    else base
    let fields := match r.executePeakRss with
      | some n => fields ++ [ ("peak-rss", Lean.toJson n) ]
      | none => fields
    (r.name, Json.mkObj fields)
  else
    -- prove-time, the proving throughput, and the prove-phase peak are
    -- present only once proven.
    let fields := match r.proveSec with
      | some p => base ++ [ ("prove-time", jsonRound 6 p)
                          , ("throughput", jsonRound 2 (r.constants.toFloat / p)) ]
      | none => base
    let fields := match r.peakRss with
      | some n => fields ++ [ ("peak-rss", Lean.toJson n) ]
      | none => fields
    let fields := match r.proofSize with
      | some n => fields ++ [ ("proof-size", Lean.toJson n) ]
      | none => fields
    let fields := match r.verifySec with
      | some v => fields ++ [ ("verify-time", jsonRound 6 v) ]
      | none => fields
    -- The recursion metrics (--recursive), in measurement order; the
    -- execute-side pair lands before the outer prove runs, so an OOM'd
    -- outer prove still leaves them on disk.
    let fields := match r.recursiveExecuteSec, r.recursiveFftCost with
      | some s, some c => fields ++ [ ("recursive-execute-time", jsonRound 6 s)
                                    , ("recursive-fft-cost", jsonRound 0 c) ]
      | _, _ => fields
    let fields := match r.recursiveProveSec with
      | some s => fields ++ [ ("recursive-prove-time", jsonRound 6 s) ]
      | none => fields
    let fields := match r.recursivePeakRss with
      | some n => fields ++ [ ("recursive-peak-rss", Lean.toJson n) ]
      | none => fields
    let fields := match r.recursiveProofSize with
      | some n => fields ++ [ ("recursive-proof-size", Lean.toJson n) ]
      | none => fields
    let fields := match r.recursiveVerifySec with
      | some v => fields ++ [ ("recursive-verify-time", jsonRound 6 v) ]
      | none => fields
    (r.name, Json.mkObj fields)

/-- Time a thunk, returning its value and the elapsed seconds. The result is
    forced by `blackBoxIO` so a pure computation isn't optimized away. -/
def timed (f : Unit → α) : IO (α × Float) := do
  let t0 ← IO.monoNanosNow
  let a ← blackBoxIO f ()
  let t1 ← IO.monoNanosNow
  return (a, (t1 - t0).toFloat / 1e9)

def runTypecheckCmd (p : Cli.Parsed) : IO UInt32 := do
  let some ixeArg := p.flag? "ixe"
    | IO.eprintln "error: --ixe <path> is required"; return 1
  let ixePath := ixeArg.as! String
  -- `--consts` comma-list ∪ `--consts-file`, shared grammar + dedup
  -- (Ix.Cli.ConstsFile — same parser as `ix check-rs`). Raw strings:
  -- resolution against the env happens later (so the `toString` fallback can
  -- see the displayed form the user wrote).
  let nameArgs ← Ix.Cli.ConstsFile.gather p
  if nameArgs.isEmpty then
    IO.eprintln "error: provide at least one constant via --consts <n1,n2,…> and/or --consts-file <path>"
    return 1
  let jsonOut : Option String := (p.flag? "json").map (·.as! String)
  -- skip-deps: check just the target (`verify_const`, trusting its deps)
  -- instead of re-checking the whole transitive closure (`verify_claim`).
  let skipDeps := p.hasFlag "skip-deps"
  -- Execute-only: run just Phase 1 (constants / fft-cost / execute-time) and
  -- skip the Phase 2 prove loop.
  let executeOnly := p.hasFlag "execute-only"
  -- Recursive: after each constant's prove, execute AND prove the in-circuit
  -- multi-stark verifier over the fresh proof (Phase 3).
  let recursive := p.hasFlag "recursive"
  if recursive && executeOnly then
    IO.eprintln "error: --recursive measures the prove path; drop --execute-only"
    return Ix.Benchmark.Results.exitUsage
  -- Off by default; CI passes --texray explicitly.
  let useTexray := p.hasFlag "texray"
  -- Start the process-tree RSS sampler so each Result's peak-rss reflects the
  -- true high-water mark. With --texray, install the streaming subscriber up
  -- front: every phase span — aiur/execute_ixvm in Phase 1 included —
  -- renders its duration and RAM Δ/peak through the one shared channel
  -- instead of per-benchmark arithmetic. With --json too, the per-span sink
  -- also lands the timings at `<json>.spans` as JSON Lines for the CI
  -- comparison.
  TracingTexray.startSampler
  if useTexray then TracingTexray.init {}
  match useTexray, jsonOut with
  | true, some path => TracingTexray.jsonSink s!"{path}.spans"
  | _, _ => pure ()

  -- Compile the IxVM kernel once; build the prover system once.
  let .ok toplevel := IxVM.ixVM
    | throw (IO.userError "Merging IxVM kernel failed")
  let .ok compiled := toplevel.compile
    | throw (IO.userError "Compilation of IxVM kernel failed")
  let entrypoint := if skipDeps then `verify_const else `verify_claim
  let some funIdx := compiled.getFuncIdx entrypoint
    | throw (IO.userError s!"{entrypoint} entrypoint missing")
  -- Recursive mode runs the WHOLE system — the inner prove included — under
  -- the recursion-tuned parameters, so the verifier's query loop stays
  -- tractable (cost scales with numQueries).
  let (commitParams, friParams) :=
    if recursive then (recursiveCommitmentParameters, recursiveFriParameters)
    else (commitmentParameters, friParameters)
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitParams
  -- The recursive-verifier context, compiled and built ONCE: the verifier
  -- toplevel is constant-independent, and its prover system (same recursion
  -- parameters) is reused for every constant's outer prove.
  let vCtx : Option (Aiur.CompiledToplevel × Aiur.Bytecode.FunIdx × Aiur.AiurSystem) ←
    if !recursive then pure none else do
      let .ok vTop := MultiStark.multiStark
        | throw (IO.userError "Merging multi-stark verifier failed")
      let .ok vCompiled := vTop.compile
        | throw (IO.userError "Compilation of multi-stark verifier failed")
      let some vIdx := vCompiled.getFuncIdx `verify_multi_stark_proof
        | throw (IO.userError "verify_multi_stark_proof entrypoint missing")
      pure (some (vCompiled, vIdx,
        Aiur.AiurSystem.build vCompiled.bytecode commitParams))

  -- Load the serialized env lazily (the `ix check --ixe` path, #445): byte-window
  -- constants over the backing buffer, so only the checked closure is ever
  -- materialized — no whole-env (100+GB on mathlib) load just to check a few.
  let ixonEnv ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error e => IO.eprintln s!"deserialize {ixePath} failed: {e}"; return 1
    | .ok env => pure env
  IO.println s!"Loaded {ixePath}: {ixonEnv.namedCount} named, {ixonEnv.constCount} consts"
  let mut targets : Array (String × Address) := #[]
  for arg in nameArgs do
    match Ix.Cli.NameResolve.resolveIxeAddr ixonEnv arg with
    | some addr => targets := targets.push (arg, addr)
    | none => IO.eprintln s!"warning: {arg} not found in {ixePath}; skipping"
  if targets.isEmpty then
    IO.eprintln "no requested constants were found in the env"
    return 1

  -- Build the env once into a Rust-owned `EnvHandle` and share it
  -- across both Phase 1 and Phase 2 loops. Per-target FFI calls
  -- reuse the parsed env — no per-call mmap / lazy-index rebuild.
  let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
    | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
    | .ok h => pure h

  -- Phase 1: execute every constant (cheap, deterministic structural metrics).
  -- For full-closure check claims, use `checkAddrWithEnv` against the
  -- shared `envHandle`. For `--skip-deps` (`buildVerifyConst`), the
  -- witness is a small subject-only blob — keep Lean witness +
  -- `executeIxVM`.
  IO.println "── Phase 1: execute (witness generation) ──"
  let mut execed : Array (Result × Address) := #[]
  let mut execIdx := 0
  for (label, addr) in targets do
    execIdx := execIdx + 1
    try
      -- Announce BEFORE the execute (flushed): a kill mid-execute must
      -- leave the in-flight constant's name in the log.
      IO.println s!"  [{execIdx}/{targets.size}] executing {label} …"
      (← IO.getStdout).flush
      -- Windowed high-water: reset per constant so each row's
      -- execute peak is its own, not the loop's running maximum.
      TracingTexray.resetPeakTreeRss
      let (res, execSec) ← timed fun _ =>
        if skipDeps then
          let witness := IxVM.ClaimHarness.buildVerifyConst ixonEnv addr
          compiled.bytecode.executeIxVM funIdx witness.input witness.inputIOBuffer
        else
          compiled.bytecode.checkAddrWithEnv funIdx envHandle addr.hash
      let execPeak ← TracingTexray.peakTreeRssBytes
      match res with
      | .error e =>
        IO.eprintln s!"  ❌ {label} FAILED TO TYPECHECK: {e}"
        execed := execed.push
          ({ name := label, constants := 0, fftCost := 0, executeSec := 0,
             failed := true }, addr)
      | .ok (_, _, queryCounts) =>
        let stats := Aiur.computeStats compiled queryCounts
        let constants := (IxVM.ClaimHarness.closureFrom ixonEnv addr).size
        -- Throughput via the shared benchmark framework; duration/RAM per
        -- phase stream from texray's `aiur/execute_ixvm` span line.
        let thrpt := (Throughput.Elements constants.toUInt64 "consts").formatRate
          (execSec * 1e9)
        IO.println s!"  {label}: constants={constants} fft-cost={stats.totalFftCost} \
          execute={execSec}s thrpt={thrpt}"
        execed := execed.push
          ({ name := label, constants, fftCost := stats.totalFftCost,
             executeSec := execSec, executePeakRss := some execPeak }, addr)
    catch e =>
      IO.eprintln s!"  execute {label} threw: {e}"

  -- Persist rows when `--json` was given, MERGING into the file (the shared
  -- results-row contract): rows land after each result, so a kill leaves the
  -- completed ones, and per-constant processes can share one file with the
  -- orchestrator and each other.
  let writeJson (results : Array Result) : IO Unit :=
    match jsonOut with
    | some path =>
      results.forM fun r =>
        let (name, row) := Result.toJsonEntry executeOnly r
        Ix.Benchmark.Results.writeEntry path name row
    | none => pure ()

  -- `--execute-only`: stop after Phase 1; the results JSON (if requested) is
  -- already complete with the execute metrics.
  if executeOnly then
    writeJson (execed.map (·.1))
    match jsonOut with
    | some path => IO.println s!"wrote {execed.size} execute-only benchmarks to {path}"
    | none => IO.println s!"executed {execed.size} constants (--execute-only); pass --json <path> to emit results"
    return if execed.any (·.1.failed) then Ix.Benchmark.Results.exitRejected else 0

  -- Phase 2: prove cheap→expensive. Refine each entry with its prove-time as
  -- it lands (texray was installed before Phase 1, so the prove spans render
  -- the same way the execute ones did).
  IO.println "── Phase 2: prove ──"
  let mut ordered := execed.qsort (·.1.fftCost < ·.1.fftCost)
  writeJson (ordered.map (·.1))
  let mut spent : Float := 0.0
  for i in [:ordered.size] do
    let (r, addr) := ordered[i]!
    if r.failed then continue
    try
      -- Announce BEFORE the prove (flushed): when a watchdog kill or OOM
      -- lands mid-prove, the log must already say which constant died.
      IO.println s!"  [{i + 1}/{ordered.size}] proving {r.name} (fft-cost={r.fftCost}) …"
      (← IO.getStdout).flush
      -- Windowed high-water: each prove's peak is its own window, not
      -- the run's cumulative maximum (mirrors the Phase-1 resets).
      TracingTexray.resetPeakTreeRss
      let (proveRes, proveSec) ← timed fun _ =>
        if skipDeps then
          let witness := IxVM.ClaimHarness.buildVerifyConst ixonEnv addr
          let (claim, proof, ioBuf) :=
            aiurSystem.proveIxVM friParams funIdx witness.input witness.inputIOBuffer
          (.ok (claim, proof, ioBuf) :
            Except String (Array Aiur.G × Aiur.Proof × Aiur.IOBuffer))
        else
          match aiurSystem.proveAddrWithEnv friParams funIdx envHandle addr.hash with
          | .error e => .error e
          | .ok (claimBytes, proof, ioBuf) =>
            -- The envHandle path returns the SERIALIZED `Ix.Claim`; rebuild
            -- the Array-G claim `verify` takes — `verify_claim`'s input is
            -- the 32-G blake3 digest of those bytes (same recipe as
            -- `ix verify`).
            let digest := Address.blake3 claimBytes
            let claim :=
              Aiur.buildClaim funIdx (digest.hash.data.map .ofUInt8) #[]
            .ok (claim, proof, ioBuf)
      match (proveRes : Except String (Array Aiur.G × Aiur.Proof × Aiur.IOBuffer)) with
      | .error e => IO.eprintln s!"  prove {r.name} failed: {e}"; continue
      | .ok (claim, proof, _ioBuf) =>
        spent := spent + proveSec
        let peak ← TracingTexray.peakTreeRssBytes
        let proofBytes := Aiur.Proof.toBytes proof
        let (verifyRes, verifySec) ← timed fun _ =>
          aiurSystem.verify friParams claim proof
        let verifySec? ← match verifyRes with
          | .ok () => pure (some verifySec)
          | .error e =>
            IO.eprintln s!"  verify {r.name} FAILED: {e}"
            pure none
        IO.println s!"  {r.name}: prove={proveSec}s verify={verifySec}s \
          proof={proofBytes.size} bytes (cumulative {spent}s)"
        ordered := ordered.set! i
          ({ r with proveSec := some proveSec, peakRss := some peak
                  , proofSize := some proofBytes.size, verifySec := verifySec? }, addr)
        writeJson (ordered.map (·.1))
        -- Phase 3 (--recursive): the in-circuit verifier over the fresh
        -- proof — execute it (recursive-execute-time / recursive-fft-cost), then prove
        -- that execution (recursive-prove-time / recursive-peak-rss /
        -- recursive-proof-size / recursive-verify-time). A reject on the execute
        -- is a correctness alarm, reported loudly with the recursive fields
        -- left absent — never a benchmark datum.
        if let some (vCompiled, vIdx, vSystem) := vCtx then
          IO.println s!"  [{i + 1}/{ordered.size}] recursively verifying {r.name} …"
          (← IO.getStdout).flush
          let claimBytes := MultiStark.serializeClaims #[claim]
          let (pubInput, io) := MultiStark.verifierInput proofBytes
            aiurSystem.vkBytes claimBytes commitParams friParams
          let (rvRes, rvSec) ← timed fun _ =>
            vCompiled.bytecode.execute vIdx pubInput io
          match rvRes with
          | .error e =>
            IO.eprintln s!"  ❌ recursive verifier REJECTED {r.name}'s proof: {e}"
          | .ok (_, _, qc) =>
            let rvStats := Aiur.computeStats vCompiled qc
            IO.println s!"  {r.name}: recursive={rvSec}s \
              recursive-fft-cost={rvStats.totalFftCost}"
            let (row, _) := ordered[i]!
            ordered := ordered.set! i
              ({ row with recursiveExecuteSec := some rvSec
                        , recursiveFftCost := some rvStats.totalFftCost }, addr)
            -- Flush the execute-side pair before the outer prove: an OOM
            -- there keeps them, and the announce (flushed) names the
            -- constant that died.
            writeJson (ordered.map (·.1))
            IO.println s!"  [{i + 1}/{ordered.size}] proving the verifier over {r.name} …"
            (← IO.getStdout).flush
            TracingTexray.resetPeakTreeRss
            let ((rvClaim, rvProof, _), rvProveSec) ← timed fun _ =>
              vSystem.prove friParams vIdx pubInput io
            let rvPeak ← TracingTexray.peakTreeRssBytes
            let rvProofBytes := Aiur.Proof.toBytes rvProof
            let (rvVerifyRes, rvVerifySec) ← timed fun _ =>
              vSystem.verify friParams rvClaim rvProof
            let rvVerifySec? ← match rvVerifyRes with
              | .ok () => pure (some rvVerifySec)
              | .error e =>
                IO.eprintln s!"  outer verify {r.name} FAILED: {e}"
                pure none
            IO.println s!"  {r.name}: recursive-prove={rvProveSec}s \
              recursive-verify={rvVerifySec}s outer proof={rvProofBytes.size} bytes"
            let (row, _) := ordered[i]!
            ordered := ordered.set! i
              ({ row with recursiveProveSec := some rvProveSec
                        , recursivePeakRss := some rvPeak
                        , recursiveProofSize := some rvProofBytes.size
                        , recursiveVerifySec := rvVerifySec? }, addr)
            writeJson (ordered.map (·.1))
    catch e =>
      IO.eprintln s!"  prove {r.name} threw: {e}"

  match jsonOut with
  | some path => IO.println s!"wrote {ordered.size} benchmarks to {path} ({spent}s proving)"
  | none => IO.println s!"proved {ordered.size} constants ({spent}s); pass --json <path> to emit results"
  return if ordered.any (·.1.failed) then Ix.Benchmark.Results.exitRejected else 0

def typecheckCmd : Cli.Cmd := `[Cli|
  typecheck VIA runTypecheckCmd;
  "Benchmark IxVM-kernel execution + proving of `Ix.Claim.check` over `.ixe` constants"

  FLAGS:
    "ixe"          : String; "Path to a serialized `Ixon.Env` (e.g. produced by `ix compile`). Required."
    "consts"       : String; "Comma-separated fully-qualified constant names to benchmark (e.g. `Nat.add_comm,String.append`). Same flag/shape as `ix check --consts`, `zisk-host --consts`, and `sp1-host --consts`."
    "consts-file"  : String; "Additionally read constant names from a file (one per line; `#` comments and blank lines ignored). Unions with --consts."
    "json"      : String; "Write per-constant results JSON to this path. Off by default; normal CLI usage prints only the human-readable summary."
    "skip-deps";          "Check only each target itself (verify_const, trusting its deps) instead of re-checking its whole transitive closure (verify_claim). Same flag as `zisk-host --skip-deps`."
    "execute-only";       "Execute only (Phase 1: constants / fft-cost / execute-time) and skip proving. The fast per-PR `execute`-mode signal."
    "recursive";          "After each prove, execute and then prove the in-circuit multi-stark verifier over the fresh proof (the recursive-* metrics; see the module docstring). Uses recursion-tuned FRI parameters. Conflicts with --execute-only."
    texray;               "Enable the tracing-texray timeline + RAM breakdown (per-prove spans on stderr). Combined with --json, per-phase span timings are additionally written to `<json>.spans` as JSON Lines for the CI drill-down. Off by default."

]

def main (args : List String) : IO UInt32 :=
  typecheckCmd.validate args
