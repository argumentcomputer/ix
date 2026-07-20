module

public import Ix.Tc.Driver
public import Ix.Tc.IngressMeta
public import Std.Sync.Mutex

/-!
Parallel whole-env kernel check driver (`ix check-lean`'s engine) plus the
eager parallel meta-ingress driver it needs (shared with `Ix.Tc.Validate`).

Mirrors the Rust parallel checker's coordination design
(`crates/ffi/src/kernel.rs`: work-stealing over an atomic next-index,
per-worker in-flight slots, a reporter thread emitting a periodic
`done/total · rate · elapsed · eta · in-flight` line, persistent lines only
for "interesting" outcomes) with Lean-native primitives:

- workers are `.dedicated` `IO` tasks: each gets a FRESH runtime thread
  spawned at `ParCheckCfg.stackBytes` (Rust `KERNEL_CHECK_STACK_SIZE`
  parity — deep recursor expansions blow the default 8 MB `lthread`
  stack, and pool threads pre-spawned by ingress keep whatever size they
  were born with). Parallelism is bounded by the worker count itself;
  the shared next-index is an `IO.Ref Nat` popped with the atomic
  `modifyGet`;
- each worker owns its own `TcState` over the SHARED fully-ingressed
  `KEnv` (persistent maps: cheap to share by value; per-worker caches
  clone-and-extend privately). Checking is subject-only — a work item
  certifies its own block and trusts referenced constants' declared
  types — so items are independent and the fan-out is sound;
- the reporter is one `.dedicated` thread and the SOLE terminal writer
  while checking (Lake-monitor pattern): workers only mutate shared state
  (`Std.Mutex` over slots/events + `IO.Ref` counters), so progress lines
  never interleave.

Divergence-hunting workflow (found the 2026-07 kernel bugs): run the
suspect constant seeded and journaled through BOTH kernels —
`IX_TC_DEBUG_CONST=<label> IX_TC_STEP_TRACE=1 ix check-lean <env.ixe>
--consts <label> --workers 1 2>lean.log` and the Rust side with
`IX_STEP_TRACE=1 ix check-rs … --consts <label> 2>rs.log` — then
canonicalize and `diff` the `[deq]`/`[whnf+]` sequences: the first fork
names the diverging operation (`TcM.stepTrace` documents the line
shape). `IX_TC_STATS=1` appends `fuel=/deq=/whnf=` counters to
verbose/slow per-item lines for call-count comparisons against the Rust
counters (`IX_DEF_EQ_COUNT_LOG`); `IX_MAX_REC_FUEL` overrides the
per-constant fuel budget on both sides.
-/

public section
@[expose] section

namespace Ix.Tc

/-- Set the stack size, in bytes, for subsequently spawned Lean runtime
    threads (`.dedicated` task threads and not-yet-spawned pool workers) —
    the knob behind `lean --tstack`. Already-running threads keep their
    stacks. The Rust shim (`crates/ffi/src/kernel.rs`) adapts the bare
    `void(size_t)` runtime call to the IO ABI. -/
@[extern "rs_lean_set_thread_stack_size"]
opaque setLeanThreadStackSize : USize → BaseIO Unit

/-! ### Eager parallel meta ingress -/

/-- Eager parallel whole-env meta ingress: chunked local envs merged into
    one `MetaEnv` (see `ingressEnvParallelWith`). One work item per
    `env.named` entry — aliases land as separate `KId`s. -/
def ingressMetaEnvParallel (ixonEnv : Ixon.Env)
    (chunkSize : Nat := 512) (verify : Bool := true) :
    Except IngressErr MetaEnv :=
  ingressEnvParallelWith (buildMetaWork ixonEnv)
    (ingressMetaWorkItem ixonEnv · verify) chunkSize

/-! ### Check work enumeration from an ingressed env -/

/-- One parallel-check work item: `checkConst primary` certifies every id
    in `targets` (block coordination + `blockCheckResults` fan one block
    verdict to all members). -/
structure CheckWorkItem (m : Mode) where
  primary : KId m
  targets : Array (KId m)

/-- Enumerate check work from a fully-ingressed env: one item per
    registered block (standalones are 1-member blocks in both modes),
    sorted by block id for deterministic run order. The post-ingress
    analog of `buildAnonWork`; in meta mode aliases are separate blocks
    and check separately (Rust parity: one row per Named entry). -/
def buildCheckWork (kenv : KEnv m) : Array (CheckWorkItem m) := Id.run do
  let mut items : Array (KId m × CheckWorkItem m) := #[]
  for (bid, members) in kenv.blocks do
    if let some first := members[0]? then
      items := items.push (bid, ⟨first, members⟩)
  let sorted := items.qsort fun a b => (a.1.cmp b.1).isLT
  return sorted.map (·.2)

/-! ### Progress state -/

/-- What one worker is checking right now (reporter-visible). -/
structure InFlight where
  label : String
  startMs : Nat
  stuckNotified : Bool := false

/-- Shared reporter-visible state (one `Std.Mutex`): per-worker in-flight
    slots and pending "interesting" output lines. -/
structure ParProgress where
  slots : Array (Option InFlight)
  events : Array String

/-- Parallel check configuration. The env-var tunables mirroring the Rust
    checker (`IX_KERNEL_CHECK_PROGRESS_MS`/`IX_PROGRESS_MS`,
    `IX_KERNEL_CHECK_SLOW_MS`, `IX_KERNEL_CHECK_ACTIVE_SLOW_MS`) are
    resolved by the CLI; the library takes plain numbers. -/
structure ParCheckCfg where
  /-- Worker count (≥ 1; the CLI resolves a machine default). -/
  workers : Nat := 8
  /-- Clear each worker's reduction-memo caches every N items (0 off).
      Default 0: with the subst/univ memo fix the transient-garbage
      motivation is gone, and warm caches win ~20% whole-env wall
      (62.1s vs 77.3s at 32 workers) for ~3 GB extra peak RSS. -/
  clearEvery : Nat := 0
  /-- Serial mode with one line per constant (forces one worker). -/
  verbose : Bool := false
  /-- Periodic aggregate progress line cadence in ms; 0 disables. -/
  progressMs : Nat := 2000
  /-- Promote ok-outcomes at/over this many ms to persistent lines; 0 off. -/
  slowMs : Nat := 7000
  /-- One-shot "still checking" notice age in ms; 0 disables. -/
  stuckMs : Nat := 30000
  /-- Worker-thread stack size in bytes (0 keeps the runtime default).
      Default mirrors the Rust checker's `KERNEL_CHECK_STACK_SIZE`
      (256 MB): with `maxRecFuel` at 10M, fuel-legal recursor expansions
      recurse far past the default 8 MB native stack (observed: a ~30k-frame
      whnf/iota chain killing `Std.DTreeMap.Internal.Impl.
      minEntry!_eq_get!_minEntry?`). Reservation is virtual; pages commit
      only as touched. -/
  stackBytes : Nat := 256 * 1024 * 1024
  /-- Prefix for progress/notice lines. -/
  tag : String := "[check-lean]"
  /-- Suppress ALL live output (library/test callers); the report and any
      `failOut?` stream still carry everything. -/
  silent : Bool := false
  /-- Set `debugLabel` on the item whose label (or fail-label) equals
      this, scoping the step journal to one constant
      (CLI: `IX_TC_DEBUG_CONST`). -/
  debugConst? : Option String := none
  /-- Emit the `[deq]`/`[whnf+]` step journal for the debug-target
      constant (CLI: `IX_TC_STEP_TRACE=1`; see `TcM.stepTrace`). -/
  stepTrace : Bool := false
  /-- Count defeq/whnf calls+misses, appended to verbose/slow per-item
      lines as `fuel=N deq=calls/misses whnf=calls/misses`
      (CLI: `IX_TC_STATS=1`). -/
  stats : Bool := false
  /-- Override the per-constant fuel budget (CLI: `IX_MAX_REC_FUEL`). -/
  maxRecFuel? : Option UInt64 := none
  /-- Disable Ix-specific semantic shortcuts (differential testing; see
      `TcState.noAccel`; CLI: `IX_TC_NO_ACCEL=1`). -/
  noAccel : Bool := false

/-- Whole-run verdict summary. `failures` carries one `(label, message)`
    row per failed TARGET (a failing block fans to every member), sorted
    by label so parallel runs report deterministically. -/
structure ParCheckReport where
  targetsCovered : Nat := 0
  passed : Nat := 0
  failures : Array (String × String) := #[]
  elapsedMs : Nat := 0

/-- `12.3`-style one-decimal rendering (values are non-negative). -/
def fmt1 (x : Float) : String :=
  let n := (x * 10.0 + 0.5).toUInt64.toNat
  s!"{n / 10}.{n % 10}"

/-- Compact a label for in-flight display (check-rs caps at 120 chars). -/
def compactLabel (l : String) : String :=
  if l.length > 120 then (l.take 117).toString ++ "..." else l

/-- Render the periodic aggregate line (check-rs
    `ParallelProgress::report` shape). -/
def renderProgressLine (tag : String) (startMs now done total : Nat)
    (slots : Array (Option InFlight)) : String := Id.run do
  let elapsedMs := now - startMs
  let pct := if total == 0 then 100.0
    else Float.ofNat done * 100.0 / Float.ofNat total
  let rate := if elapsedMs == 0 then 0.0
    else Float.ofNat done * 1000.0 / Float.ofNat elapsedMs
  let mut line :=
    s!"{tag} {done}/{total} ({fmt1 pct}%) · {fmt1 rate}/s · \
       elapsed {elapsedMs / 1000}s"
  if rate > 0.0 && done < total then
    let etaS := (Float.ofNat (total - done) / rate).toUInt64.toNat
    line := line ++ s!" · eta {etaS}s"
  let inFlight := (slots.filterMap id).qsort (fun a b => a.startMs < b.startMs)
  if !inFlight.isEmpty then
    let shown := inFlight.extract 0 (min 3 inFlight.size)
    let parts := shown.map fun f =>
      s!"{compactLabel f.label} ({(now - f.startMs) / 1000}s)"
    line := line ++ " · in-flight: " ++ String.intercalate ", " parts.toList
  return line

/-- Check `work` in parallel over the shared env (see module doc for the
    coordination design). `labelOf` renders progress labels;
    `failLabelOf` renders failure rows and `failOut?` records — the CLI
    passes bare Lean names (meta) / `#hex` (anon) there so a fail-out file
    round-trips into `check-rs --consts-file`. Kernel rejections land in
    the report; worker `IO` errors rethrow. -/
def checkEnvParallel (kenv : KEnv m) (prims : Primitives m)
    (work : Array (CheckWorkItem m)) (labelOf failLabelOf : KId m → String)
    (cfg : ParCheckCfg) (failOut? : Option IO.FS.Handle := none) :
    IO ParCheckReport := do
  let total := work.size
  let totalTargets := work.foldl (fun n it => n + it.targets.size) 0
  let nWorkers :=
    if cfg.verbose then 1 else max 1 (min cfg.workers (max 1 total))
  let startMs ← IO.monoMsNow
  let nextIdx ← IO.mkRef 0
  let doneRef ← IO.mkRef 0
  let stopRef ← IO.mkRef false
  let progress : Std.Mutex ParProgress ← Std.Mutex.new
    { slots := .replicate nWorkers none, events := #[] }

  -- One worker: own TcState over the shared env; work-stealing loop.
  let worker (wi : Nat) : IO (Nat × Array (String × String)) := do
    let mut st := TcState.new kenv prims
    st := { st with
      stepTrace := cfg.stepTrace
      stats := cfg.stats
      noAccel := cfg.noAccel
      fuelBudget := cfg.maxRecFuel?.getD st.fuelBudget
      recFuel := cfg.maxRecFuel?.getD st.recFuel }
    let mut passed := 0
    let mut failures : Array (String × String) := #[]
    let mut sinceClear := 0
    let mut running := true
    while running do
      let idx ← nextIdx.modifyGet fun n => (n, n + 1)
      if h : idx < work.size then
        let item := work[idx]
        let lbl := labelOf item.primary
        if cfg.debugConst?.isSome then
          let isTarget := (cfg.debugConst? == some lbl
            || cfg.debugConst? == some (failLabelOf item.primary))
          st := { st with debugLabel := if isTarget then some lbl else none }
        let (dc0, dm0, wc0, wm0, ks0, kr0) :=
          (st.deqCalls, st.deqMisses, st.whnfCalls, st.whnfMisses,
           st.kSynthAttempts, st.kSynthRejects)
        let t0 ← IO.monoMsNow
        if cfg.verbose && !cfg.silent then
          IO.eprint s!"  [{idx + 1}/{total}] {lbl} ... "
        else
          progress.atomically fun ref => ref.modify fun s =>
            { s with slots := s.slots.set! wi (some ⟨lbl, t0, false⟩) }
        let (err?, st') := match (TcM.checkConst item.primary).run st with
          | .ok () s => (none, s)
          | .error e s => (some (toString e), s)
        st := st'
        let t1 ← IO.monoMsNow
        let ms := t1 - t0
        let depth := st.defEqPeak
        let stats := if !cfg.stats then "" else
          s!" fuel={st.fuelBudget - st.recFuel} \
             deq={st.deqCalls - dc0}/{st.deqMisses - dm0} \
             whnf={st.whnfCalls - wc0}/{st.whnfMisses - wm0} \
             ksynth={st.kSynthAttempts - ks0}/{st.kSynthRejects - kr0}"
        match err? with
        | none => passed := passed + item.targets.size
        | some msg =>
          for t in item.targets do
            failures := failures.push (failLabelOf t, msg)
        if cfg.verbose then
          if !cfg.silent then
            match err? with
            | none => IO.eprintln s!"ok ({ms}ms, depth={depth}{stats})"
            | some msg =>
              IO.eprintln s!"FAIL ({ms}ms, depth={depth}{stats}): {msg}"
        else
          let interesting? : Option String :=
            if cfg.silent then none else match err? with
            | some msg =>
              some s!"  ✗ {lbl}: FAIL ({ms}ms, depth={depth}{stats}): {msg}"
            | none =>
              if cfg.slowMs != 0 && ms ≥ cfg.slowMs then
                some s!"  {lbl} ok ({ms}ms, depth={depth}{stats}) [slow]"
              else none
          progress.atomically fun ref => ref.modify fun s =>
            let s := { s with slots := s.slots.set! wi none }
            match interesting? with
            | some line => { s with events := s.events.push line }
            | none => s
        -- Stream the failure record (check-rs FailureLog shape: `# msg`
        -- comment + one bare label line per covered target, flushed so
        -- `tail -f` sees it live). Serialized via the progress mutex.
        if let some h := failOut? then
          if let some msg := err? then
            let collapsed := (msg.replace "\n" " | ").replace "\r" ""
            progress.atomically fun _ => do
              h.putStrLn ""
              h.putStrLn s!"# {collapsed}"
              for t in item.targets do
                h.putStrLn (failLabelOf t)
              h.flush
        doneRef.modify (· + 1)
        sinceClear := sinceClear + 1
        if cfg.clearEvery != 0 && sinceClear ≥ cfg.clearEvery then
          st := { st with env := st.env.clearReductionCaches }
          sinceClear := 0
      else
        running := false
    -- Whole-run counter totals, one line per worker (grep-and-sum for
    -- cross-kernel count comparisons; ephemeral progress is separate).
    if cfg.stats then
      IO.eprintln s!"{cfg.tag} worker {wi} totals: \
                     deq={st.deqCalls}/{st.deqMisses} \
                     whnf={st.whnfCalls}/{st.whnfMisses} \
                     ksynth={st.kSynthAttempts}/{st.kSynthRejects}"
    return (passed, failures)

  -- Reporter: sole terminal writer while checking. Drains interesting
  -- lines every 250ms; aggregate line every `progressMs`; exits (after a
  -- final drain) once the stop flag is set.
  let reporter : IO Unit := do
    let mut lastLine := startMs
    let mut go := true
    while go do
      IO.sleep 250
      let stop ← stopRef.get
      let evs ← progress.atomically fun ref =>
        ref.modifyGet fun s => (s.events, { s with events := #[] })
      for e in evs do
        IO.eprintln e
      let now ← IO.monoMsNow
      if cfg.stuckMs != 0 then
        let notices ← progress.atomically fun ref =>
          ref.modifyGet fun s => Id.run do
            let mut ns : Array String := #[]
            let mut slots := s.slots
            for i in [0:slots.size] do
              if let some f := slots[i]! then
                if !f.stuckNotified && now - f.startMs ≥ cfg.stuckMs then
                  ns := ns.push
                    s!"{cfg.tag} still checking {compactLabel f.label} \
                       after {(now - f.startMs) / 1000}s"
                  slots := slots.set! i (some { f with stuckNotified := true })
            return (ns, { s with slots })
        for n in notices do
          IO.eprintln n
      if cfg.progressMs != 0 && !stop && now - lastLine ≥ cfg.progressMs then
        lastLine := now
        let done ← doneRef.get
        let slots ← progress.atomically fun ref => (·.slots) <$> ref.get
        IO.eprintln (renderProgressLine cfg.tag startMs now done total slots)
      if stop then
        go := false

  -- Big-stack workers: set the lthread size, then spawn each worker
  -- `.dedicated` so it gets a FRESH thread at that size (default-priority
  -- tasks would reuse pool threads born at 8 MB during ingress).
  if cfg.stackBytes != 0 then
    setLeanThreadStackSize (USize.ofNat cfg.stackBytes)
  let workerTasks ← (Array.range nWorkers).mapM fun wi =>
    IO.asTask (prio := .dedicated) (worker wi)
  let reporter? ←
    if cfg.verbose || cfg.silent then pure none
    else some <$> IO.asTask (prio := .dedicated) reporter
  let mut passed := 0
  let mut failures : Array (String × String) := #[]
  for t in workerTasks do
    let (p, fs) ← IO.ofExcept t.get
    passed := passed + p
    failures := failures ++ fs
  stopRef.set true
  if let some r := reporter? then
    let _ ← IO.ofExcept r.get
  let endMs ← IO.monoMsNow
  return { targetsCovered := totalTargets, passed
           failures := failures.qsort fun a b => a.1 < b.1
           elapsedMs := endMs - startMs }

end Ix.Tc

end
end
