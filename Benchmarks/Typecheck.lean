import Cli
import Ix.IxVM
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Aiur.Statistics
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

When `--json` is set the file is rewritten after every prove, so an external
`timeout` still leaves a complete file of the results collected so far (cheapest
first). A name absent from the env or whose execution errors is skipped with a
warning, so a single bad name never fails the run. The harness imposes no time
limit; bound a run with an external `timeout` if needed.

The JSON is a flat shape (`{ "<name>": { "constants": …, "fft-cost": …,
"execute-time": …, "execute-peak-rss": …, "prove-time": …, "proof-size": …,
"verify-time": …, "peak-rss": …, "throughput": … } }`). `execute-peak-rss` is
the Phase-1 RSS high-water, sampled before proving starts, so it is comparable
across execute-only and prove runs; `prove-time`, `proof-size`, `verify-time`,
`peak-rss` (the prover's high-water), and `throughput` appear only for proven
constants. Any bencher-specific reshaping is the caller's job (see
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
  /-- Peak resident-set size in bytes (tracing-texray tree sampler), captured
      after the constant's heaviest phase. -/
  peakRss : Option Nat := none
  /-- The constant's own Phase-1 (execute) RSS high-water mark — the sampler
      window resets per constant. Present in BOTH modes so an execute-only
      run compares apples-to-apples against a prove run's baseline —
      `peak-rss` in a prove run is dominated by the prover and would dwarf
      an execute-only peak. -/
  executePeakRss : Option Nat := none
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

/-- Flat results object: `name → { constants, fft-cost, execute-time,
    prove-time?, throughput? }`. No bencher-specific shaping. -/
def Result.toJsonEntry (r : Result) : String × Json :=
  if r.failed then
    (r.name, Json.mkObj [("status", Json.str "rejected")]) else
  let base : List (String × Json) :=
    [ ("status", Json.str "ok")
    , ("constants", Lean.toJson r.constants)
    , ("fft-cost", jsonRound 0 r.fftCost)
    , ("execute-time", jsonRound 6 r.executeSec) ]
  let base := match r.peakRss with
    | some n => base ++ [ ("peak-rss", Lean.toJson n) ]
    | none => base
  let base := match r.executePeakRss with
    | some n => base ++ [ ("execute-peak-rss", Lean.toJson n) ]
    | none => base
  -- prove-time and the derived proving throughput (constants/prove-time, the
  -- proving analog of compile's constants/sec) are present only once proven.
  let fields := match r.proveSec with
    | some p => base ++ [ ("prove-time", jsonRound 6 p)
                        , ("throughput", jsonRound 2 (r.constants.toFloat / p)) ]
    | none => base
  let fields := match r.proofSize with
    | some n => fields ++ [ ("proof-size", Lean.toJson n) ]
    | none => fields
  let fields := match r.verifySec with
    | some v => fields ++ [ ("verify-time", jsonRound 6 v) ]
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
  -- Off by default; CI passes --texray explicitly.
  let useTexray := p.hasFlag "texray"
  -- Start the process-tree RSS sampler so each Result's peak-rss reflects the
  -- true high-water mark. When --texray + --json are both on, also install the
  -- streaming subscriber and point the per-span sink at `<json>.spans`, so the
  -- prover's aiur/* and stark/* phase timings land as JSON Lines for the CI
  -- comparison.
  TracingTexray.startSampler
  match useTexray, jsonOut with
  | true, some path => TracingTexray.init {}; TracingTexray.jsonSink s!"{path}.spans"
  | _, _ => pure ()

  -- Compile the IxVM kernel once; build the prover system once.
  let .ok toplevel := IxVM.ixVM
    | throw (IO.userError "Merging IxVM kernel failed")
  let .ok compiled := toplevel.compile
    | throw (IO.userError "Compilation of IxVM kernel failed")
  let entrypoint := if skipDeps then `verify_const else `verify_claim
  let some funIdx := compiled.getFuncIdx entrypoint
    | throw (IO.userError s!"{entrypoint} entrypoint missing")
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters

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
      -- execute-peak-rss is its own, not the loop's running maximum.
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
        IO.println s!"  {label}: constants={constants} fft-cost={stats.totalFftCost} \
          execute={execSec}s"
        execed := execed.push
          ({ name := label, constants, fftCost := stats.totalFftCost,
             executeSec := execSec, executePeakRss := some execPeak }, addr)
    catch e =>
      IO.eprintln s!"  execute {label} threw: {e}"

  -- Write the benchmark results JSON, but only when `--json` was given. Rewritten
  -- after each prove so a `timeout` kill still leaves a complete file.
  let writeJson (results : Array Result) : IO Unit :=
    match jsonOut with
    | some path =>
      IO.FS.writeFile path (Json.mkObj (results.map Result.toJsonEntry).toList).pretty
    | none => pure ()

  -- `--execute-only`: stop after Phase 1; the results JSON (if requested) is
  -- already complete with the execute metrics.
  if executeOnly then
    writeJson (execed.map (·.1))
    match jsonOut with
    | some path => IO.println s!"wrote {execed.size} execute-only benchmarks to {path}"
    | none => IO.println s!"executed {execed.size} constants (--execute-only); pass --json <path> to emit results"
    return if execed.any (·.1.failed) then Ix.Benchmark.Results.exitRejected else 0

  -- Phase 2: prove cheap→expensive. Refine each entry with its prove-time as it
  -- lands. Install texray first so the prove spans (timeline + RAM Δ/peak) render.
  if useTexray then TracingTexray.init {}
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
      -- Windowed high-water: each prove's peak-rss is its own window, not
      -- the run's cumulative maximum (mirrors the Phase-1 resets).
      TracingTexray.resetPeakTreeRss
      let (proveRes, proveSec) ← timed fun _ =>
        if skipDeps then
          let witness := IxVM.ClaimHarness.buildVerifyConst ixonEnv addr
          let (claim, proof, ioBuf) :=
            aiurSystem.proveIxVM friParameters funIdx witness.input witness.inputIOBuffer
          (.ok (claim, proof, ioBuf) :
            Except String (Array Aiur.G × Aiur.Proof × Aiur.IOBuffer))
        else
          match aiurSystem.proveAddrWithEnv friParameters funIdx envHandle addr.hash with
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
        let proofSize := (Aiur.Proof.toBytes proof).size
        let (verifyRes, verifySec) ← timed fun _ =>
          aiurSystem.verify friParameters claim proof
        let verifySec? ← match verifyRes with
          | .ok () => pure (some verifySec)
          | .error e =>
            IO.eprintln s!"  verify {r.name} FAILED: {e}"
            pure none
        IO.println s!"  {r.name}: prove={proveSec}s verify={verifySec}s \
          proof={proofSize} bytes (cumulative {spent}s)"
        ordered := ordered.set! i
          ({ r with proveSec := some proveSec, peakRss := some peak
                  , proofSize := some proofSize, verifySec := verifySec? }, addr)
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
    texray;               "Enable the tracing-texray timeline + RAM breakdown (per-prove spans on stderr). Combined with --json, per-phase span timings are additionally written to `<json>.spans` as JSON Lines for the CI drill-down. Off by default."

]

def main (args : List String) : IO UInt32 :=
  typecheckCmd.validate args
