import Cli
import Ix.IxVM
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Aiur.Statistics
import Ix.TracingTexray
import Ix.Benchmark.Bench
import Ix.Cli.NameResolve

/-!
# Aiur typecheck benchmark

Out-of-circuit **execution** and in-circuit **proving** benchmark for the IxVM
kernel's `verify_claim` entrypoint, run over constants from a serialized
`Ixon.Env` (`.ixe`). Reading the env from a `.ixe` keeps this on Ix's critical
path (same load `ix check --ixe` uses) and avoids importing Lean modules at
runtime. Useful standalone (per-constant timeline + RAM breakdown via
tracing-texray) and as a machine source (neutral results JSON).

```
lake exe bench-typecheck --ixe <path> [--constant <name>] [names…] [flags]

  --ixe <path>       serialized `Ixon.Env`, e.g. from `ix compile Foo.lean`
                     (writes `foo.ixe`). Required.
  --constant <name>  constant to benchmark, by fully-qualified Lean name. The
                     canonical single-target flag, shared with the Zisk
                     `zisk-host --constant`. Unions with names / manifest.
  [names…]           zero or more additional constant names to benchmark,
                     e.g. `Nat.add_comm String.append`.
  --manifest <path>  additionally read names from a file: one per line, blank
                     lines and `#` comments ignored. Unions with [names…].

  Names (from any source) resolve against the env's named map via
  `String.toName` plus a `toString` fallback (mirrors `ix check --ixe`), so
  numeric / private components round-trip (`Foo.0.Bar`, `_private.M.0.foo`).
  Pass at least one name via --constant, positional args, or --manifest.

  --skip-deps    check only each target itself (verify_const, trusting its
                 deps) instead of its whole transitive closure (verify_claim,
                 the default). Same flag as `zisk-host --skip-deps`; reserved
                 for targets too expensive to full-closure-check.
  --json <path>  write per-constant results JSON to <path>. Off by default:
                 normal CLI usage prints only the human-readable summary.
  --texray       force the tracing-texray timeline + RAM breakdown on.
  --no-texray    force it off. Default: on iff `--json` was NOT given, so a
                 plain local run gets the breakdown while a JSON run stays quiet.
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
   recording `prove-time`. With texray on, each prove emits a per-span timeline
   (`aiur/execute`, `aiur/witness`, `stark/...`) with RAM Δ/peak to stderr.

When `--json` is set the file is rewritten after every prove, so an external
`timeout` still leaves a complete file of the results collected so far (cheapest
first). A name absent from the env or whose execution errors is skipped with a
warning, so a single bad name never fails the run. The harness imposes no time
limit; bound a run with an external `timeout` if needed.

The JSON is a neutral, flat shape (`{ "<name>": { "constants": …, "fft-cost": …,
"execute-time": …, "prove-time": …, "throughput": … } }`, where `prove-time` and
`throughput` appear only for proven constants); any bencher-specific reshaping
is the caller's job (see `.github/workflows/bench-main.yml`).
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

/-- Manifest lines as raw strings: one name per line. Everything from a `#` to
    end of line is a comment (whole-line or inline); blank lines are dropped.
    `#` never appears in a Lean name, so splitting on it is safe. Resolution
    against the env happens later (so the `toString` fallback can see the
    displayed form the user wrote). -/
def parseManifest (contents : String) : Array String :=
  (contents.splitOn "\n").filterMap (fun line =>
    let s := ((line.splitOn "#").head?.getD "").trimAscii
    if s.isEmpty then none else some s.toString) |>.toArray


/-- Per-constant measurements. `proveSec` is `none` when the constant was
    executed but not (yet) proven. -/
structure Result where
  name : String
  constants : Nat
  fftCost : Float
  executeSec : Float
  proveSec : Option Float := none
  deriving Inhabited

/-- Round a Float to `d` decimal places, to keep the emitted JSON readable. -/
def roundTo (d : Nat) (f : Float) : Float :=
  let scale := (10.0 : Float) ^ d.toFloat
  (f * scale).round / scale

/-- Neutral, flat results object: `name → { constants, fft-cost, execute-time,
    prove-time?, throughput? }`. No bencher-specific shaping. -/
def Result.toJsonEntry (r : Result) : String × Json :=
  let base : List (String × Json) :=
    [ ("constants", Lean.toJson r.constants)
    , ("fft-cost", Lean.toJson (roundTo 0 r.fftCost))
    , ("execute-time", Lean.toJson (roundTo 6 r.executeSec)) ]
  -- prove-time and the derived proving throughput (constants/prove-time, the
  -- proving analog of compile's constants/sec) are present only once proven.
  let fields := match r.proveSec with
    | some p => base ++ [ ("prove-time", Lean.toJson (roundTo 6 p))
                        , ("throughput", Lean.toJson (roundTo 2 (r.constants.toFloat / p))) ]
    | none => base
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
  -- Names come from `--constant`, the variadic positional args, and/or a
  -- `--manifest` file. `--constant` is the canonical single-target flag shared
  -- with the Zisk `zisk-host --constant`; positional names and `--manifest`
  -- remain for benchmarking many constants at once.
  let constName : Array String := match p.flag? "constant" with
    | some f => #[f.as! String]
    | none => #[]
  let cliNames := p.variableArgsAs! String
  let fileNames ← match p.flag? "manifest" with
    | some f => pure (parseManifest (← IO.FS.readFile (f.as! String)))
    | none => pure #[]
  -- Union, preserving first-seen order, so the same const isn't proven twice.
  let nameArgs := Id.run do
    let mut seen : Std.HashSet String := {}
    let mut acc : Array String := #[]
    for n in constName ++ cliNames ++ fileNames do
      if !seen.contains n then seen := seen.insert n; acc := acc.push n
    return acc
  if nameArgs.isEmpty then
    IO.eprintln "error: provide a constant via --constant, positional name(s), and/or --manifest <path>"
    return 1
  let jsonOut : Option String := (p.flag? "json").map (·.as! String)
  -- skip-deps: check just the target (`verify_const`, trusting its deps)
  -- instead of re-checking the whole transitive closure (`verify_claim`).
  let skipDeps := p.hasFlag "skip-deps"
  -- Execute-only: run just Phase 1 (constants / fft-cost / execute-time) and
  -- skip the Phase 2 prove loop.
  let executeOnly := p.hasFlag "execute-only"
  -- Default: trace iff we're not in JSON/bencher mode.
  let useTexray :=
    if p.hasFlag "texray" then true
    else if p.hasFlag "no-texray" then false
    else jsonOut.isNone

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
  for (label, addr) in targets do
    try
      let (res, execSec) ← timed fun _ =>
        if skipDeps then
          let witness := IxVM.ClaimHarness.buildVerifyConst ixonEnv addr
          compiled.bytecode.executeIxVM funIdx witness.input witness.inputIOBuffer
        else
          compiled.bytecode.checkAddrWithEnv funIdx envHandle addr.hash
      match res with
      | .error e => IO.eprintln s!"  execute {label} failed: {e}"
      | .ok (_, _, queryCounts) =>
        let stats := Aiur.computeStats compiled queryCounts
        let constants := (IxVM.ClaimHarness.closureFrom ixonEnv addr).size
        IO.println s!"  {label}: constants={constants} fft-cost={stats.totalFftCost} \
          execute={execSec}s"
        execed := execed.push
          ({ name := label, constants, fftCost := stats.totalFftCost, executeSec := execSec }, addr)
    catch e =>
      IO.eprintln s!"  execute {label} threw: {e}"

  -- Write the neutral results JSON, but only when `--json` was given. Rewritten
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
    return 0

  -- Phase 2: prove cheap→expensive. Refine each entry with its prove-time as it
  -- lands. Install texray first so the prove spans (timeline + RAM Δ/peak) render.
  if useTexray then TracingTexray.init {}
  IO.println "── Phase 2: prove ──"
  let mut ordered := execed.qsort (·.1.fftCost < ·.1.fftCost)
  writeJson (ordered.map (·.1))
  let mut spent : Float := 0.0
  for i in [:ordered.size] do
    let (r, addr) := ordered[i]!
    try
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
          | .ok (_claimBytes, proof, ioBuf) =>
            -- The shared envHandle path doesn't return an `Array G`
            -- claim — adapt to the existing benchmark return shape
            -- by recomputing the claim digest from the witness's
            -- input (Phase 2 doesn't read it).
            .ok (#[], proof, ioBuf)
      match (proveRes : Except String (Array Aiur.G × Aiur.Proof × Aiur.IOBuffer)) with
      | .error e => IO.eprintln s!"  prove {r.name} failed: {e}"; continue
      | .ok _ => pure ()
      spent := spent + proveSec
      IO.println s!"  {r.name}: prove={proveSec}s (cumulative {spent}s)"
      ordered := ordered.set! i ({ r with proveSec := some proveSec }, addr)
      writeJson (ordered.map (·.1))
    catch e =>
      IO.eprintln s!"  prove {r.name} threw: {e}"

  match jsonOut with
  | some path => IO.println s!"wrote {ordered.size} benchmarks to {path} ({spent}s proving)"
  | none => IO.println s!"proved {ordered.size} constants ({spent}s); pass --json <path> to emit results"
  return 0

def typecheckCmd : Cli.Cmd := `[Cli|
  typecheck VIA runTypecheckCmd;
  "Benchmark IxVM-kernel execution + proving of `Ix.Claim.check` over `.ixe` constants"

  FLAGS:
    "ixe"       : String; "Path to a serialized `Ixon.Env` (e.g. produced by `ix compile`). Required."
    "constant"  : String; "Constant to benchmark, by fully-qualified Lean name. The canonical single-target flag (shared with `zisk-host --constant`). Unions with positional names / --manifest."
    "manifest"  : String; "Additionally read constant names from a file (one per line; `#` comments and blank lines ignored). Unions with the positional names."
    "json"      : String; "Write per-constant results JSON to this path. Off by default; normal CLI usage prints only the human-readable summary."
    "skip-deps";          "Check only each target itself (verify_const, trusting its deps) instead of re-checking its whole transitive closure (verify_claim). Same flag as `zisk-host --skip-deps`."
    "execute-only";       "Execute only (Phase 1: constants / fft-cost / execute-time) and skip proving. The fast per-PR `execute`-mode signal."
    texray;               "Force the tracing-texray timeline + RAM breakdown on (per-prove spans on stderr)."
    "no-texray";          "Force the breakdown off. Default: on iff --json was not given."

  ARGS:
    ...names : String;   "Fully-qualified constant name(s) to benchmark (e.g. `Nat.add_comm String.append`). Optional if `--manifest` is given."
]

def main (args : List String) : IO UInt32 :=
  typecheckCmd.validate args
