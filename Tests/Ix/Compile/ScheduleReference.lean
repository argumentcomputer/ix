/-
  A second schedule of the Lean compiler, for the tests only: the sequential
  driver that `compileEnvFold` (CQ2.14) replaced, kept as it was.

  It compiles one block at a time against the live state, takes the ready
  block with the least canonical key first (or, with `least := false`, the
  greatest), and pre-compiles the aux-gen seeds' closure in a pre-pass and
  re-promotes those names when their blocks come up, as the Rust compiler does
  (`precompile_aux_gen_prereqs`), where the fold makes the seeds scheduling
  dependencies. It is the driver of no compile: `compile-schedule-identity`,
  `aux-gen-diff`, `compile-claim-conflict` and `compile-driver-input` compare
  the fold with it, so a schedule-dependent value (or a difference between the
  seeds' two routes) shows as a byte difference.

  The two definitions are `Ix.CompileM.precompileAuxGenPrereqs` and
  `Ix.CompileM.compileEnvAux` as of CQ2.13/CQ2.24, renamed, with the
  `least` switch on the ready queue, and the clique rows emitted after the
  loop (`emitRows`, CQ5.2 (b)), as in both drivers of the fold.
-/
import Ix.CompileDriver

public section

namespace Tests.Ix.Compile.ScheduleReference

open _root_.Ix _root_.Ix.CompileM

/-- Pre-compile the transitive SCC closure of the aux_gen seed names in
    reverse-topological (dep-first) order, then move the compiled names
    from `nameToAddr` to `auxNameToAddr` so the scheduler's promotion
    pass recognizes and re-promotes them when their blocks come up.
    Mirrors `precompile_aux_gen_prereqs` (env.rs:1036-1140). -/
def precompileSeeds (blocks : Ix.CondensedBlocks) (acc₀ : DriverAcc)
    : Except String DriverAcc := Id.run do
  let seedReps := auxGenSeedNames.filterMap (blocks.lowLinks.get? ·)
  if seedReps.isEmpty then
    return .ok acc₀
  -- Iterative DFS post-order over the condensed graph (env.rs:1063-1097).
  let mut order : Array Name := #[]
  let mut visited : Set Name := {}
  -- Frame: (rep, isExit)
  let mut stack : Array (Name × Bool) := seedReps.map ((·, false))
  repeat
    match stack.back? with
    | none => break
    | some (rep, isExit) =>
      stack := stack.pop
      if isExit then
        order := order.push rep
      else
        if visited.contains rep then
          continue
        visited := visited.insert rep
        stack := stack.push (rep, true)
        if let some outRefs := blocks.blockRefs.get? rep then
          for referenced in outRefs do
            if let some depRep := blocks.lowLinks.get? referenced then
              if !visited.contains depRep then
                stack := stack.push (depRep, false)
  let mut acc := acc₀
  for rep₀ in order do
    let some all := blocks.blocks.get? rep₀ | continue
    -- The block is compiled under its canonical key.
    let rep := blockKey rep₀ all
    if acc.cenv.auxNameToAddr.contains rep then
      continue
    let failed (e : CompileError) : String := s!"aux_gen prereq pre-compile failed for SCC \
'{rep.pretty}' ({all.size} members): {e}. The SCC closure is traversed \
in reverse-topological order starting from the aux_gen seed names, so \
all transitive deps should be compiled before this — if you're hitting \
this, a dep relationship isn't captured in the ref graph, or the source \
env is inconsistent."
    match runBlock acc.cenv all rep with
    | .error e => return .error (failed e)
    | .ok (result, cache, _, published) =>
      -- A conflicting claim fails the pre-compile like a block error (Rust's
      -- claims raise inside `compile_const`).
      match checkCompiledBlock acc.cenv rep result cache published with
      | .error e => return .error (failed e)
      | .ok () => acc := mergeCompiledBlock acc rep result cache published
      -- Move compiled names → auxNameToAddr (env.rs:1119-1137). At this
      -- stage `nameToAddr` contains exactly the prereq registrations.
      let moved := acc.cenv.nameToAddr
      acc := { acc with cenv := { acc.cenv with
        nameToAddr := {}
        auxNameToAddr := moved.fold (fun m k v => m.insert k v)
          acc.cenv.auxNameToAddr } }
  return .ok acc

/-- Compile an entire environment with the FULL production pipeline
    semantics: aux-gen prereq pre-compilation, per-block aux tails
    (regeneration and Pass 3's hooks), the scheduler promotion pass with
    the no-aux original-form second compile (`Named.original`), and
    pending-aux dependency release. Sequential mirror of Rust
    `compile_env_with_options`' scheduler (env.rs:146-990; grounding and
    SCC condensation happen upstream of the `blocks` input, as in the
    Rust FFI phase split). An input inductive group with non-canonical
    flags fails the compile first (`validateInductiveFlags`).

    Per-block failures, and the names of a cross-SCC subset whose compile
    fails, are recorded in `ungrounded` per member and the scheduler
    continues (dependents cascade into `MissingConstant` failures recorded
    the same way) — mirroring env.rs:727-737. -/
def sequential (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (dbg : Bool := false)
    (unmaterialized : Nat := 0)
    (sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    (least : Bool := true)
    : Except String (Ixon.Env × Nat × CompileEnv) := Id.run do
  if let some msg := missingBlockRefs? blocks then return .error msg
  if let .error e := validateInductiveFlags env then return .error e
  if let .error e := validateMutualSafety env blocks then return .error e
  -- Pass 3's clique transport, set up as the fold sets it up
  -- (`compileEnvFoldWithSource`): the clique table and the encoding roots in
  -- the compile environment, the scheduling edges in the ready order below;
  -- each block's own references (`p3BlockRefs`, keyed as `FoldState.init`
  -- keys them) stay the condensation's
  let sc := Ix.Compile.Pass.Clique.scheduleCliques env blocks
  let sizePlan := prepareSizeOfPlan env sc.1
  let scheduled := sizePlan.1
  let ra := Ix.AuxGen.Source.RunAhead.start env.get? blocks
    (scheduleLevels blocks (FoldSchedule.of scheduled)) .recursors
  let blockRefs : Std.HashMap Name (Set Name) := blocks.blocks.fold (init := {}) fun m rep all =>
    match blocks.blockRefs.get? rep with
    | some refs => m.insert (blockKey rep all) refs
    | none => m
  let cenv₀ : CompileEnv := { CompileEnv.new env with
    sourceFamilyOracle := some (sourceFamilyProvider env.get? blocks ra)
    unmaterialized, sharingLimits, p3Cliques := sc.2.1, p3CliqueRoots := sc.2.2,
    p3BlockRefs := blockRefs, p3O11aPlans := sizePlan.2 }
  let mut acc : DriverAcc := { cenv := cenv₀ }
  match precompileSeeds blocks acc with
  | .error e => return .error e
  | .ok a => acc := a

  let totalBlocks := blocks.blocks.size
  let mut blockInfo : Std.HashMap Name (Set Name × Nat) := {}
  let mut reverseDeps : Std.HashMap Name (Array Name) := {}
  for (lo, all) in blocks.blocks do
    let deps := match scheduled.blockRefs.get? lo with
      | some d => d
      | none => {}
    blockInfo := blockInfo.insert lo (all, deps.size)
    for depName in deps do
      reverseDeps := reverseDeps.alter depName fun
        | some arr => some (arr.push lo)
        | none => some #[lo]
  -- The ready blocks keyed by their canonical key (`blockKey`), the least
  -- taken first: the fold's order is the least-key-first topological order
  -- of the block graph, a function of the graph and the keys alone. It was
  -- a stack filled in `HashMap` iteration order, so the order depended on
  -- the condensation's representatives and the maps' histories. The output
  -- does not depend on the order on valid input, so this changes no value.
  let mut readyQueue : Std.TreeMap Name (Set Name) Ix.nameCompare := {}
  for (lo, (all, depCount)) in blockInfo do
    if depCount == 0 then
      readyQueue := readyQueue.insert (blockKey lo all) all

  let mut blocksCompleted : Nat := 0
  let mut lastPct : Nat := 0
  -- Deps already satisfied (released) — HashSet-style idempotent release
  -- mirrors Rust's `remaining.remove` (env.rs:838-856): a name can be
  -- released at most once per dependent.
  let mut released : Set Name := {}

  while !readyQueue.isEmpty do
    -- `lo` is the block's canonical key from here on.
    let some (lo, all) := (if least then readyQueue.minEntry? else readyQueue.maxEntry?) | break
    readyQueue := readyQueue.erase lo

    if (resolveAddrPure acc.cenv lo).isSome then
      -- Promotion path (env.rs:566-708): the block was pre-compiled into
      -- `auxNameToAddr` (prereqs or a parent block's aux tail).
      let anyAuxGen := Id.run do
        for n in all do
          if acc.cenv.auxGenExtraNames.contains n then return true
        return false
      let mut unresolvedNames : Array Name := #[]
      for n in all do
        if acc.cenv.nameToAddr.contains n then
          continue
        if (resolveAddrPure acc.cenv n).isSome then
          continue
        unresolvedNames := unresolvedNames.push n
      let mut auxIncomplete := false
      if !unresolvedNames.isEmpty then
        if anyAuxGen then
          auxIncomplete := true
          let missing := ", ".intercalate
            (unresolvedNames.toList.map (·.pretty))
          let msg := s!"aux_gen precompile incomplete for {lo.pretty}; \
missing canonical aliases: {missing}"
          acc := failAuxPromotion acc all msg
        else
          -- Cross-SCC compile of the unresolved subset (env.rs:617-651).
          let crossAll : Set Name :=
            unresolvedNames.foldl (fun s n => s.insert n) {}
          -- The subset is named by its canonical key, not by its first name
          -- in `Set` order.
          let clo := canonicalKey lo unresolvedNames
          -- The subset's names are failures of the compile when it fails or
          -- claims a name another block owns (Rust claims inside
          -- `compile_const`), recorded per name as Rust records them, and not
          -- registered: dependents get `MissingConstant` rather than broken
          -- data.
          let crossFailed (acc : DriverAcc) (e : CompileError) : DriverAcc := Id.run do
            let msg := toString e
            let mut acc := acc
            for n in unresolvedNames do
              acc := { acc with cenv := { acc.cenv with
                ungrounded := acc.cenv.ungrounded.insert n msg } }
            return acc
          match runBlock acc.cenv crossAll clo with
          | .error e => acc := crossFailed acc e
          | .ok (result, cache, _, published) =>
            match checkCompiledBlock acc.cenv clo result cache published with
            | .error e => acc := crossFailed acc e
            | .ok () =>
              acc := mergeCompiledBlock acc clo result cache published
              for n in unresolvedNames do
                acc := { acc with
                  cenv := { acc.cenv with
                    auxGenExtraNames := acc.cenv.auxGenExtraNames.insert n }
                  pending := acc.pending.push n }
      if !auxIncomplete then
        -- Compile the original Lean form and promote, atomically
        -- (`finishAuxPromotion`): a failure of the original-form compile, of
        -- its promotion, of a remaining claim, or of the cross-SCC subset
        -- withdraws the whole block.
        let original := if anyAuxGen then
          (compileConstNoAuxPure acc.cenv lo all).map some
        else .ok none
        match original with
        | .error e => acc := failAuxPromotion acc all (toString e)
        | .ok result =>
          let (next, _, _) := finishAuxPromotion acc lo all result
          acc := next
    else
      -- Normal path: compile the block with the aux tail.
      let fail (acc : DriverAcc) (e : CompileError) : DriverAcc := Id.run do
        -- Soft failure (env.rs:727-737): record per member; the
        -- scheduler keeps running and dependents cascade.
        let msg := toString e
        let mut acc := acc
        for m in all do
          acc := { acc with cenv := { acc.cenv with
            ungrounded := acc.cenv.ungrounded.insert m msg } }
        return acc
      match runBlock acc.cenv all lo with
      | .error e => acc := fail acc e
      | .ok (result, cache, _, published) =>
        -- A conflicting claim is a failure of this block (Rust raises it
        -- inside `compile_const`): nothing of it is merged.
        match checkCompiledBlock acc.cenv lo result cache published with
        | .error e => acc := fail acc e
        | .ok () => acc := mergeCompiledBlock acc lo result cache published

    -- Release dependents: block members plus drained pending-aux names
    -- (env.rs:838-870).
    let pendingDrained := acc.pending
    acc := { acc with pending := #[] }
    let mut releaseNames : Array Name := #[]
    for n in all do
      releaseNames := releaseNames.push n
    -- Source-owned auxiliaries settle only when their own block finishes its
    -- original-form promotion (`auxDependencyReady`); generated names without
    -- a source block can release now.
    releaseNames := releaseNames ++ pendingDrained.filter (!blocks.lowLinks.contains ·)
    for name in releaseNames do
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
        dbg_trace s!"  [CompileAux] {pct}% ({blocksCompleted}/{totalBlocks})"
        lastPct := pct

  if blocksCompleted != totalBlocks then
    return .error s!"Only compiled {blocksCompleted}/{totalBlocks} blocks \
- circular dependency?"

  -- the clique rows after the loop, as the fold does (`emitRows`, CQ5.2 (b))
  return (emitRows acc).bind finalizeEnv


end Tests.Ix.Compile.ScheduleReference
