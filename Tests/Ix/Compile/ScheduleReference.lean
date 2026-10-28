/-
  A second schedule of the Lean compiler, for the tests only: a sequential
  driver that compiles one block at a time against the live state, taking
  the ready block with the least canonical key first (or, with
  `least := false`, the greatest). It is the driver of no compile:
  `compile-schedule-identity`, `compile-claim-conflict` and
  `compile-driver-input` compare the fold (`compileEnvFold`, which computes a
  wave's blocks against the wave's snapshot) with it, so a schedule-dependent
  value shows as a byte difference.
-/
import Ix.CompileDriver

public section

namespace Tests.Ix.Compile.ScheduleReference

open _root_.Ix _root_.Ix.CompileM

/-- Compile an entire environment's condensation one block at a time, each
    against the live state, in least-key-first (or greatest-key-first)
    topological order of the block graph. An input inductive group with
    non-canonical flags, or a mutual block of mixed safety, fails the compile
    first, as in the fold.

    Per-block failures, and conflicting claims or payloads, are recorded in
    `ungrounded` per member and the scheduler continues (dependents cascade
    into `MissingConstant` failures recorded the same way), as Rust's
    scheduler does. -/
def sequential (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (dbg : Bool := false)
    (sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    (least : Bool := true)
    : Except String (Ixon.Env × Nat × CompileEnv) := Id.run do
  if let some msg := missingBlockRefs? blocks then return .error msg
  if let .error e := validateInductiveFlags env then return .error e
  if let .error e := validateMutualSafety env blocks then return .error e
  let mut acc : DriverAcc := { cenv := { CompileEnv.new env with sharingLimits } }

  let totalBlocks := blocks.blocks.size
  let mut blockInfo : Std.HashMap Name (Set Name × Nat) := {}
  let mut reverseDeps : Std.HashMap Name (Array Name) := {}
  for (lo, all) in blocks.blocks do
    let deps := match blocks.blockRefs.get? lo with
      | some d => d
      | none => {}
    blockInfo := blockInfo.insert lo (all, deps.size)
    for depName in deps do
      reverseDeps := reverseDeps.alter depName fun
        | some arr => some (arr.push lo)
        | none => some #[lo]
  -- The ready blocks keyed by their canonical key (`blockKey`), the least
  -- (or the greatest) taken first: a function of the graph and the keys
  -- alone.
  let mut readyQueue : Std.TreeMap Name (Set Name) Ix.nameCompare := {}
  for (lo, (all, depCount)) in blockInfo do
    if depCount == 0 then
      readyQueue := readyQueue.insert (blockKey lo all) all

  let mut blocksCompleted : Nat := 0
  let mut lastPct : Nat := 0
  -- Deps already satisfied (released): a name is released at most once per
  -- dependent, as Rust's `remaining.remove`.
  let mut released : Set Name := {}

  while !readyQueue.isEmpty do
    -- `lo` is the block's canonical key from here on.
    let some (lo, all) := (if least then readyQueue.minEntry? else readyQueue.maxEntry?) | break
    readyQueue := readyQueue.erase lo
    let fail (acc : DriverAcc) (e : CompileError) : DriverAcc := Id.run do
      -- Soft failure: record per member; the scheduler keeps running and
      -- dependents cascade.
      let msg := toString e
      let mut acc := acc
      for m in all do
        acc := { acc with cenv := { acc.cenv with
          ungrounded := acc.cenv.ungrounded.insert m msg } }
      return acc
    match runBlock acc.cenv all lo with
    | .error e => acc := fail acc e
    | .ok (result, cache) =>
      -- A conflicting claim is a failure of this block (Rust raises it
      -- inside `compile_const`): nothing of it is merged.
      match checkCompiledBlock acc.cenv lo result cache with
      | .error e => acc := fail acc e
      | .ok () => acc := mergeCompiledBlock acc lo result cache

    -- Release dependents: the block's members.
    for name in all do
      if released.contains name then
        continue
      released := released.insert name
      if let some dependents := reverseDeps.get? name then
        for dependentLo in dependents do
          if let some (depAll, depCount) := blockInfo.get? dependentLo then
            let newCount := depCount - 1
            blockInfo := blockInfo.insert dependentLo (depAll, newCount)
            if newCount == 0 then
              readyQueue := readyQueue.insert (blockKey dependentLo depAll) depAll

    blocksCompleted := blocksCompleted + 1
    if dbg then
      let pct := (blocksCompleted * 100) / totalBlocks
      if pct >= lastPct + 10 then
        dbg_trace s!"  [schedule-reference] {pct}% ({blocksCompleted}/{totalBlocks})"
        lastPct := pct

  if blocksCompleted != totalBlocks then
    return .error s!"Only compiled {blocksCompleted}/{totalBlocks} blocks \
- circular dependency?"

  return finalizeEnv acc

end Tests.Ix.Compile.ScheduleReference
