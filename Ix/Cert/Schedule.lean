import Ix.Cert.Compile

/-! # The driver's schedule is a fold (CQP.4 a)

`Ix.CompileM.compileEnvFold` is the driver of both `Ix.Cert.compile` and the
IO pipeline (`Ix.CompileM.compileDecoratedConsts`). Each wave computes its
ready blocks' outcomes (`auxBlockOutcome`) against the wave's snapshot on
at most `width` tasks (`waveTasks`), and applies them in block-key order.
This file proves that the schedule is only a schedule:

* `applyTasks_eq`: the tasks' outcomes, applied chunk by chunk, are the
  ready blocks' outcomes applied one by one in key order, for every
  `width`. The chunks are contiguous slices of the ready blocks
  (`chunks_flatten`), and a spawned task's value is its function's
  (`(Task.spawn f).get = f ()` by definition);
* `foldWave_eq`, `foldWaves_eq`: a wave, and the waves, are their
  sequential forms (`foldWaveSeq`, `foldWavesSeq`), which take no `width`
  and no `dbg` (the per-wave trace is `dbgTrace`, whose value is its
  continuation's);
* `compileEnvFold_eq_seq`: **the driver is the sequential fold**
  (`compileEnvFoldSeq`); so `compileEnvFold_width` its value does not depend
  on `width` or `dbg`: `Ix.Cert.compile` (width `foldWaveTasks`, no trace)
  and the IO pipeline (width `4 * numWorkers`, its options' trace) run the
  same fold;
* `lazyPure_eq`: the IO pipeline's wrapper `IO.lazyPure` is `pure` of the
  value.

"Sequential" is the fold's own order: within a wave every outcome is
computed against the wave's snapshot (the state the previous wave left),
then the outcomes are applied in key order. That this equals compiling each
block against the live state in some dependency order (the reference
schedule `Tests.Ix.Compile.ScheduleReference`) is a
property of the blocks' independence within a wave, tested by
`compile-schedule-identity` and `cert-compile-parity-init`, not proved
here.

The driver is restated with its apply step as a parameter
(`foldWaveWith`), by `rfl` (`foldWave_eq_with`): an edit of `foldWave`
breaks the build here until the restatement follows. `compileEnvFoldSeq`
restates `compileEnvFold` verbatim, with `foldWavesSeq` for `foldWaves`. -/

namespace Ix.Cert.Schedule

open Ix.CompileM

/-! ## The chunks are the ready blocks -/

/-- Consecutive slices of `xs`, `k` of them of size `s`, are its prefix of
length `k * s`. -/
theorem slices_flatten {α : Type} (xs : Array α) (s : Nat) :
    ∀ k, ((Array.range k).map fun c => xs.extract (c * s) ((c + 1) * s)).flatten = xs.extract 0 (k * s) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Array.range_succ, Array.map_append, Array.flatten_append, ih]
    rw [show ((#[k] : Array Nat).map fun c => xs.extract (c * s) ((c + 1) * s)).flatten =
      xs.extract (k * s) ((k + 1) * s) by simp]
    rw [Array.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
      Nat.max_eq_right (Nat.mul_le_mul_right s (Nat.le_succ k))]

/-- `ceil (n / s) * s` covers `n`. -/
theorem ceil_mul_ge (n s : Nat) (pos : 0 < s) : n ≤ (n + s - 1) / s * s := by
  have split := Nat.div_add_mod (n + s - 1) s
  have small := Nat.mod_lt (n + s - 1) pos
  generalize (n + s - 1) / s = q at split ⊢
  generalize (n + s - 1) % s = r at split small
  rw [Nat.mul_comm] at split
  omega

/-- The chunk count `waveTasks` computes, times its chunk size, covers the
ready blocks. -/
theorem chunks_cover (n w : Nat) (wpos : 0 < w) :
    n ≤ (if ((n + w - 1) / w == 0) = true then 0 else (n + (n + w - 1) / w - 1) / ((n + w - 1) / w)) *
      ((n + w - 1) / w) := by
  by_cases zero : (n + w - 1) / w = 0
  · have := ceil_mul_ge n w wpos
    rw [zero, Nat.zero_mul] at this
    simp only [zero]
    omega
  · simp only [zero, beq_iff_eq, ite_false]
    exact ceil_mul_ge n _ (Nat.pos_of_ne_zero zero)

/-- Slices covering `xs`, mapped, are `xs` mapped. -/
theorem slices_map {α β : Type} (f : α → β) (xs : Array α) (s k : Nat) (cover : xs.size ≤ k * s) :
    ((Array.range k).map fun c => (xs.extract (c * s) ((c + 1) * s)).map f).flatten = xs.map f := by
  have slices := slices_flatten xs s k
  rw [Array.extract_eq_self_of_le cover] at slices
  have mapped := congrArg (Array.map f) slices
  rw [Array.map_flatten, Array.map_map] at mapped
  simpa [Function.comp_def] using mapped

/-- **The tasks' values, flattened, are the ready blocks' outcomes against
the snapshot, in order**, whatever `width`. -/
theorem waveTasks_flatten (width : Nat) (snapshot : CompileEnv) (ready : Array (Ix.Name × Ix.Name × Ix.Set Ix.Name)) :
    ((waveTasks width snapshot ready).map Task.get).flatten =
      ready.map fun (key, _, all) => (key, all, auxBlockOutcome snapshot key all) := by
  unfold waveTasks
  simp only [Array.map_map, Function.comp_def]
  exact slices_map _ ready _ _ (chunks_cover ready.size (max 1 width)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 width)))

/-! ## The apply step -/

/-- The fold's apply step as it runs: the tasks' outcomes applied in task
order, each task's in its order. -/
def applyTasks (width : Nat) (snapshot : CompileEnv) (ready : Array (Ix.Name × Ix.Name × Ix.Set Ix.Name))
    (acc : DriverAcc) : DriverAcc := Id.run do
  let tasks := waveTasks width snapshot ready
  let mut acc := acc
  for t in tasks do
    for (key, all, outcome) in t.get do
      acc := (applyAuxBlockOutcome acc key all outcome).1
  return acc

/-- **The sequential apply step**: each ready block's outcome against the
snapshot, applied one by one in the ready blocks' (key) order. -/
def applySeq (snapshot : CompileEnv) (ready : Array (Ix.Name × Ix.Name × Ix.Set Ix.Name))
    (acc : DriverAcc) : DriverAcc :=
  ready.foldl (fun acc (key, _, all) => (applyAuxBlockOutcome acc key all (auxBlockOutcome snapshot key all)).1) acc

/-- **Chunked = sequential**: the tasks apply exactly the sequential
outcomes, whatever `width`. -/
theorem applyTasks_eq (width : Nat) (snapshot : CompileEnv) (ready : Array (Ix.Name × Ix.Name × Ix.Set Ix.Name))
    (acc : DriverAcc) : applyTasks width snapshot ready acc = applySeq snapshot ready acc := by
  unfold applyTasks applySeq
  simp only [Id.run, bind_pure, pure_bind, Array.forIn_pure_yield_eq_foldl]
  have flat := congrArg
    (fun xs => Array.foldl (fun acc (x : Ix.Name × Ix.Set Ix.Name × AuxBlockOutcome) =>
      (applyAuxBlockOutcome acc x.1 x.2.1 x.2.2).1) acc xs)
    (waveTasks_flatten width snapshot ready)
  simp only [Array.foldl_flatten, Array.foldl_map] at flat
  exact flat

/-! ## The waves -/

open Ix (Name Set) in
/-- `foldWave` with its apply step as a parameter: the readiness rule, the
key order and the settling are `foldWave`'s, verbatim; the wave's outcomes
are applied by `apply snapshot ready`. -/
def foldWaveWith (apply : CompileEnv → Array (Name × Name × Set Name) → DriverAcc → DriverAcc)
    (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st : FoldState) : Except String FoldState := Id.run do
  let { acc, settled, unmet, candidates, remaining, waves } := st
  let sourceOwned := blocks.lowLinks.contains
  let mut ready : Array (Name × Name × Set Name) := #[]
  let mut parked : Array Name := #[]
  for rep in candidates do
    let some all := blocks.blocks.get? rep
      | return .error s!"wave driver: block {rep.pretty} is not in the condensation"
    let deps := (sched.deps.get? rep).getD {}
    let depsOk := Id.run do
      for d in deps do
        if !auxDependencyReady sourceOwned acc.cenv settled d then return false
      return true
    if depsOk then ready := ready.push (blockKey rep all, rep, all)
    else parked := parked.push rep
  if ready.isEmpty then
    return .error s!"Circular dependency detected: {remaining} blocks remaining but none ready"
  ready := ready.qsort fun a b => Ix.nameCompare a.1 b.1 == .lt
  let acc := apply acc.cenv ready acc
  let mut settled := settled
  let mut unmet := unmet
  let mut next := parked
  for (_, _, all) in ready do
    for m in all do
      settled := settled.insert m
  for (_, _, all) in ready do
    for m in all do
      for w in (sched.waiters.get? m).getD #[] do
        match unmet.get? w with
        | some 1 =>
          unmet := unmet.erase w
          next := next.push w
        | some k => unmet := unmet.insert w (k - 1)
        | none => pure ()
  return .ok { acc, settled, unmet, candidates := next,
               remaining := remaining - ready.size, waves := waves + 1 }

/-- `foldWave` is its restatement with the tasks' apply step, for either
`dbg` (the trace is `dbgTrace`, whose value is its continuation's). -/
theorem foldWave_eq_with (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (width : Nat) (dbg : Bool)
    (st : FoldState) : foldWave blocks sched width dbg st = foldWaveWith (applyTasks width) blocks sched st := by
  cases dbg <;> rfl

/-- **A wave, sequentially**: the ready blocks (the candidates the readiness
rule admits against the previous wave's state, in `blockKey` order), each
block's outcome computed against that state and applied one by one in
order (`applySeq`), then the wave's members settle. -/
def foldWaveSeq (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st : FoldState) :
    Except String FoldState :=
  foldWaveWith applySeq blocks sched st

/-- **A wave is its sequential form**, for every `width` and `dbg`. -/
theorem foldWave_eq (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (width : Nat) (dbg : Bool)
    (st : FoldState) : foldWave blocks sched width dbg st = foldWaveSeq blocks sched st := by
  rw [foldWave_eq_with]
  have same : applyTasks width = applySeq := by
    funext snapshot ready acc
    exact applyTasks_eq width snapshot ready acc
  rw [same]
  rfl

/-- **The waves, sequentially**: `foldWaves` with `foldWaveSeq`. -/
def foldWavesSeq (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) : Nat → FoldState → Except String FoldState
  | 0, st =>
    if st.remaining == 0 then .ok st
    else .error s!"Only compiled {blocks.blocks.size - st.remaining}/{blocks.blocks.size} \
blocks - circular dependency?"
  | fuel + 1, st =>
    if st.remaining == 0 then .ok st
    else match foldWaveSeq blocks sched st with
      | .error e => .error e
      | .ok st' => foldWavesSeq blocks sched fuel st'

/-- **The waves are their sequential form**, for every `width` and `dbg`. -/
theorem foldWaves_eq (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (width : Nat) (dbg : Bool) :
    ∀ fuel st, foldWaves blocks sched width dbg fuel st = foldWavesSeq blocks sched fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st; rfl
  | succ fuel ih =>
    intro st
    simp only [foldWaves, foldWavesSeq, foldWave_eq, ih]
    rfl

/-! ## The driver -/

/-- **The driver, sequentially**: `compileEnvFold` with its waves
sequential (`foldWavesSeq`). It has no `width` and no `dbg`. -/
def compileEnvFoldSeq (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    : Except String (Ixon.Env × Nat × CompileEnv) := do
  if let some msg := missingBlockRefs? blocks then throw msg
  validateInductiveFlags env
  validateMutualSafety env blocks
  let view : Ix.Environment := { consts := {}, fallback? := some env.get? }
  let sched := FoldSchedule.of blocks
  let cenv₀ := { CompileEnv.new view with sharingLimits }
  let st ← foldWavesSeq blocks sched (blocks.blocks.size + 1) (FoldState.init cenv₀ blocks sched)
  let (ixe, bytes, cenv) ← finalizeEnv st.acc
  return (ixe, bytes, { cenv with env })

/-- **Schedule = fold (CQP.4 a)**: the driver is its sequential form, for
every `width` and `dbg`: within each wave, every ready block's outcome is
computed against the wave's snapshot and the outcomes are applied one by
one in block-key order. -/
theorem compileEnvFold_eq_seq (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (dbg : Bool)
    (sharingLimits : Ix.Sharing.Exact.Limits) (width : Nat) :
    compileEnvFold env blocks dbg sharingLimits width =
      compileEnvFoldSeq env blocks sharingLimits := by
  unfold compileEnvFold compileEnvFoldSeq
  simp only [foldWaves_eq]
  rfl

/-- **The driver's value does not depend on its schedule**: `width` (the
tasks per wave) and `dbg` (the per-wave trace) change nothing. So
`Ix.Cert.compile`'s fold (width `foldWaveTasks`, no trace) and the IO
pipeline's (width `4 * numWorkers`, its options' trace) are one function of
the environment, the condensation and the sharing limits. -/
theorem compileEnvFold_width (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (dbg dbg' : Bool)
    (sharingLimits : Ix.Sharing.Exact.Limits) (width width' : Nat) :
    compileEnvFold env blocks dbg sharingLimits width =
      compileEnvFold env blocks dbg' sharingLimits width' := by
  rw [compileEnvFold_eq_seq, compileEnvFold_eq_seq]

/-- The IO pipeline's wrapper (`compileDecoratedConsts` runs the driver
under `IO.lazyPure`) is `pure` of the value. -/
theorem lazyPure_eq {α : Type} (f : Unit → α) : IO.lazyPure f = pure (f ()) := rfl

end Ix.Cert.Schedule
