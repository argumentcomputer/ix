module
public import Ix.Check
public import Ix.Shard.Environment
public import Ix.Benchmark.Results
public import Ix.TracingTexray
public import Ix.Unsigned

/-! Manifest-driven IxVM execution, resource auditing, and shard refinement. -/

public section
namespace Ix.Shard.Check
open Ix.Check Ix.Shard IxVM.ClaimHarness

/-- Run the shard operation for one shard, given the already-loaded env and the
    shard's owned `blocks`: build the `CheckEnv` witness over the owned consts
    (ingress their closure, skip the frontier) and dispatch `runOne`. -/
def runShardOwned (ixonEnv : Ixon.Env) (blocks : Array Address) (shardK : Nat)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  let owned := ownedConstsForBlocks ixonEnv blocks
  IO.println s!"[shard] shard {shardK}: {blocks.size} owned blocks → \
    {owned.size}/{ixonEnv.consts.size} owned consts"
  match IxVM.ClaimHarness.buildShardCheckEnvWitness ixonEnv owned with
  | .error e => IO.eprintln s!"shard witness build failed: {e}"; return 1
  | .ok (claim, witness) => runOne claim witness s!"shard {shardK}"

/-- IxVM-native fast path: dispatch through `shardCheckWithEnv` (a
    Rust-owned `EnvHandle` reused across calls). Caller threads in
    the pre-built envHandle so all shards in an all-shards run share
    one env parse. -/
def runShardOwnedNative (envHandle : Aiur.EnvHandle) (compiled : Aiur.CompiledToplevel)
    (printStats : Bool) (statsOut : Option String)
    (useBytecode : Bool)
    (ixonEnv : Ixon.Env) (blocks : Array Address) (shardK : Nat) : IO UInt32 := do
  let owned := ownedConstsForBlocks ixonEnv blocks
  IO.println s!"[shard] shard {shardK}: {blocks.size} owned blocks → \
    {owned.size}/{ixonEnv.consts.size} owned consts"
  let label := s!"shard {shardK}"
  IO.println s!"Typechecking {label}"
  (← IO.getStdout).flush
  let funIdx := compiled.getFuncIdx `verify_claim |>.get!
  let mut blob := ByteArray.empty
  for a in owned do
    blob := blob ++ a.hash
  match compiled.bytecode.shardCheckWithEnv funIdx envHandle blob useBytecode with
  | .error e =>
    IO.eprintln s!"{label}: IxVM-native shard check error: {e}"
    return 1
  | .ok (_output, _ioBuffer, queryCounts) =>
    if printStats then emitStats compiled queryCounts statsOut
    pure 0

/-- Manifest-driven check/prove of one shard `shardK` of the partition. -/
def runShardCheckManifest (manifestPath ixePath : String) (shardK : Nat)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) => match shards[shardK]? with
    | none => IO.eprintln s!"shard {shardK} out of range ({shards.size} shards)"; return 1
    | some blocks => runShardOwned ixonEnv blocks shardK runOne

/-- IxVM-native shard check, single shard. Builds an `EnvHandle`
    once for this one call. -/
def runShardCheckManifestNative (manifestPath ixePath : String) (shardK : Nat)
    (compiled : Aiur.CompiledToplevel) (printStats : Bool)
    (statsOut : Option String)
    (useBytecode : Bool) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) => match shards[shardK]? with
    | none => IO.eprintln s!"shard {shardK} out of range ({shards.size} shards)"; return 1
    | some blocks =>
      let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
        | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
        | .ok h => pure h
      runShardOwnedNative envHandle compiled printStats statsOut
        useBytecode ixonEnv blocks shardK

/-- Cut `blocks` into contiguous, nonempty, roughly equal-count parts
    (`p` clamped to `[2, blocks.size]` — a rejection always needs at
    least two parts, and the block list caps how many a cut can
    produce). Equal block counts approximate the prover-row distribution.
    Shared by the prove split recursion and the check wave loop. -/
def cutBlocks (blocks : Array Address) (p : Nat) : Array (Array Address) :=
  let p := min (max p 2) blocks.size
  (Array.range p).map fun i =>
    blocks.extract (blocks.size * i / p) (blocks.size * (i + 1) / p)

/-- Measured-peaks blob for the manifest emit: one 8-byte LE value per
    shard, in shard order. -/
def peaksBlob (peaks : Array Nat) : ByteArray :=
  peaks.foldl (init := ByteArray.empty) fun blob pk =>
    blob ++ pk.toUInt64.toLEBytes

/-- Wire encoding shared by the shard batch FFI and the manifest emit:
    per entry, a 4-byte LE count followed by the 32-byte addresses. -/
def addrListsBlob (lists : Array (Array Address)) : ByteArray :=
  lists.foldl (init := ByteArray.empty) fun blob l =>
    l.foldl (fun b a => b ++ a.hash) (blob ++ l.size.toUInt32.toLEBytes)

/-- One leaf of a source manifest cut into parts, as the prove and check
    split loops produce it: the parts' block lists in block order, each
    with the analytic prover peak measured on its executed record
    (`0` = unmeasured). -/
structure LeafRefinement where
  shard : Nat
  parts : Array (Array Address × Nat)

/-- Wire encoding of `Aiur.shardManifestRefine`'s refinements argument:
    `count(u32)`, then per refined leaf `id(u32) ‖ nparts(u32)` and per
    part `nblocks(u32) ‖ 32·nblocks ‖ peak(u64)`. -/
def refinementsBlob (rs : Array LeafRefinement) : ByteArray :=
  rs.foldl (init := rs.size.toUInt32.toLEBytes) fun blob r =>
    r.parts.foldl
      (init := blob ++ r.shard.toUInt32.toLEBytes ++ r.parts.size.toUInt32.toLEBytes)
      fun blob (blocks, peak) =>
        (blocks.foldl (fun b a => b ++ a.hash) (blob ++ blocks.size.toUInt32.toLEBytes))
          ++ peak.toUInt64.toLEBytes

/-- Group per-leaf run results `(shard, parts)` over the `n` leaves of a
    source manifest into the leaves that split (≥ 2 parts) and the
    measured peaks of the leaves that did not (`0` where a leaf was not
    run). -/
def refinementsOfRuns (n : Nat)
    (runs : Array (Nat × Array (Array Address × Nat))) :
    Array LeafRefinement × Array Nat :=
  runs.foldl (init := (#[], Array.replicate n 0)) fun (rs, measured) (k, parts) =>
    if parts.size > 1 then (rs.push { shard := k, parts }, measured)
    else match parts[0]? with
      | some (_, peak) => (rs, if k < measured.size then measured.set! k peak else measured)
      | none => (rs, measured)

/-- Decode the new-id table `Aiur.shardManifestRefine` returns:
    `count(u32)`, then per refinement `n(u32) ‖ n × id(u32)`. Malformed
    input yields the ids decoded so far, never a panic. -/
def decodeIdTable (bytes : ByteArray) : Array (Array Nat) := Id.run do
  let u32At (i : Nat) : Option Nat :=
    if i + 4 ≤ bytes.size then
      some (bytes[i]!.toNat ||| (bytes[i+1]!.toNat <<< 8)
        ||| (bytes[i+2]!.toNat <<< 16) ||| (bytes[i+3]!.toNat <<< 24))
    else none
  let some count := u32At 0 | return #[]
  let mut pos := 4
  let mut table : Array (Array Nat) := #[]
  for _ in [0:count] do
    let some n := u32At pos | return table
    pos := pos + 4
    let mut ids : Array Nat := #[]
    for _ in [0:n] do
      let some id := u32At pos | return table
      ids := ids.push id
      pos := pos + 4
    table := table.push ids
  return table

/-- Emit the partition a run actually validated as a refinement of the
    manifest it started from — the shared tail of `ix prove --out-ixes`
    and `ix check --ram-budget --out-ixes`. Untouched leaves keep their
    records, ids and tree positions (`Aiur.shardManifestRefine`); a leaf
    that split becomes a subtree over its parts, part 0 keeping the leaf's
    id and later parts taking fresh ids after the last existing one.
    `measured` carries the peaks of the leaves that ran unsplit. Skipped
    with a note when any shard failed: a refined manifest describes a
    fully-validated partition. Returns the parts' new ids per refinement. -/
def emitRefinedManifest (tag : String) (envHandle : Aiur.EnvHandle)
    (sourcePath out : String) (refinements : Array LeafRefinement)
    (measured : Array Nat) (failures : Nat) : IO (Array (Array Nat)) := do
  if failures == 0 then
    let ids ← Aiur.shardManifestRefine envHandle sourcePath
      (refinementsBlob refinements) (peaksBlob measured) out
    IO.println s!"[{tag}] refined manifest → {out} \
      ({refinements.size} leaf/leaves split)"
    pure (decodeIdTable ids)
  else
    IO.eprintln s!"--out-ixes {out} skipped: {failures} failure(s)"
    pure #[]

/-- What a batch run is asked to do beyond the plain check. -/
structure AuditOptions where
  /-- Leaves to execute in wave 0; `none` = every leaf of the manifest. -/
  selection : Option (Array Nat) := none
  /-- Decide, once the env and every leaf's owned constants are loaded,
      which selected leaves a verified proof already covers: they are
      reported `proven-kept`, never executed and never split (the
      shard-proof index guard of `ix shard refine`). Receives the env, the
      leaves' block lists, their owned constants, and the selected ids. -/
  provenGuard : Option (Ixon.Env → Array (Array Address) → Array (Array Address)
    → Array Nat → IO (Std.HashMap Nat Address)) := none
  /-- Write the provisional JSON report (`ix-refine/0`) here. -/
  report : Option String := none
  /-- `true` (`ix shard refine`): write `--out-ixes` even when some leaves
      failed — they stay unchanged — and exit 2. `false` (`ix check`): skip
      the manifest on any failure. -/
  emitOnFailure : Bool := false
  /-- The invoking command line, recorded in the report. -/
  command : String := ""
  /-- How the budget was chosen (`flag` or `detected`), for the report. -/
  budgetSource : String := "flag"

/-- One settled part of a leaf's cascade, for the manifest and the report. -/
structure PartReport where
  label : String
  blocks : Array Address
  owned : Array Address
  peak : Nat
  error : String := ""

/-- Claim digest of a leaf from its already-known owned constants (no env
    rescan): the digest `ix prove` persists and `ix aggregate` matches on. -/
def claimDigestOfOwned (ixonEnv : Ixon.Env) (owned : Array Address) :
    Except String Address := do
  let (claim, _) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees ixonEnv owned
  pure (Address.blake3 (Ix.Claim.ser claim))

/-- `K`, `a-b`, or a comma list of those: the leaf ids a run is restricted
    to, sorted and deduplicated. -/
def parseShardSelection (s : String) : Except String (Array Nat) := do
  let mut ids : Array Nat := #[]
  for piece in s.splitOn "," do
    let piece := piece.trimAscii.toString
    if piece.isEmpty then continue
    match piece.splitOn "-" with
    | [one] =>
      let some k := one.trimAscii.toString.toNat?
        | throw s!"--shards: not a shard id: `{piece}`"
      ids := ids.push k
    | [lo, hi] =>
      let some a := lo.trimAscii.toString.toNat?
        | throw s!"--shards: not a range: `{piece}`"
      let some b := hi.trimAscii.toString.toNat?
        | throw s!"--shards: not a range: `{piece}`"
      if b < a then throw s!"--shards: empty range `{piece}`"
      for k in [a:b+1] do ids := ids.push k
    | _ => throw s!"--shards: malformed `{piece}` (use K, a-b, or a comma list)"
  if ids.isEmpty then throw "--shards: empty selection"
  let sorted := ids.qsort (· < ·)
  pure (sorted.foldl (fun acc k => if acc.back? == some k then acc else acc.push k) #[])

private def fileDigest (path : String) : IO (Option (String × Nat)) := do
  try
    let bytes ← IO.FS.readBinFile path
    pure (some (toString (Address.blake3 bytes), bytes.size))
  catch _ => pure none

private def gitRevision : IO String := do
  try
    let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
    pure (if out.exitCode == 0 then out.stdout.trimAscii.toString else "unknown")
  catch _ => pure "unknown"

private def fileJson (path : String) (digest : Option (String × Nat))
    (shards : Option Nat) : Lean.Json :=
  Lean.Json.mkObj ([("path", Lean.Json.str path)]
    ++ (match digest with
        | some (h, n) => [("blake3", Lean.Json.str h), ("bytes", Lean.toJson n)]
        | none => [])
    ++ (match shards with | some n => [("shards", Lean.toJson n)] | none => []))

/-- Whole-partition check as ONE Rust rayon batch: work-stealing across
    shards, no chunk barriers (measured 2.3–2.5x faster than the
    per-shard Lean-task scheduler it replaced, whose chunk-of-N full
    barrier idled workers on each wave's slowest shard). Each shard
    runs the identical single-shard machinery over its own record; per
    shard the analytic prover RAM peak of the executed record is
    reported — the input to split (over a prover budget) / merge (far
    under it) decisions. Builds the `EnvHandle` ONCE, shared by every
    shard. Coverage-gates the manifest before running any shard — exit
    0 has to mean "every env const was checked by some shard", same
    soundness contract as `runShardCheckAll`.

    `opts` turns the batch into an audit: a selection of leaves, the
    proven-leaf guard, a JSON report, and `ix shard refine`'s failure
    policy. -/
def runShardBatchNative (manifestPath ixePath : String) (jobs? : Option Nat)
    (compiled : Aiur.CompiledToplevel) (useBytecode : Bool)
    (json? : Option (String × String))
    (maxRamBytes : Nat) (outIxes : Option String)
    (opts : AuditOptions := {}) :
    IO UInt32 := do
  -- The row's peak-rss needs the process-tree RSS sampler running
  -- (`peakTreeRssBytes` reports 0 otherwise); started before the env
  -- load so the peak covers the whole run, like `check-rs`.
  if json?.isSome then TracingTexray.startSampler
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) =>
    if !(← shardsCover ixonEnv shards) then return 1
    let selected : Array Nat ← match opts.selection with
      | none => pure (Array.range shards.size)
      | some sel =>
        if let some k := sel.find? (· ≥ shards.size) then
          IO.eprintln s!"--shards: shard {k} out of range ({shards.size} shards)"
          return 1
        pure sel
    let selectedSet : Std.HashSet Nat := selected.foldl (·.insert ·) {}
    let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
      | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
      | .ok h => pure h
    let funIdx := compiled.getFuncIdx `verify_claim |>.get!
    let jobs := jobs?.getD 0
    -- The whole run's ownership assignment: one env pass here, and every
    -- later wave's parts inherit their parent's owned consts via
    -- `partitionOwned` — no wave ever rescans the env.
    let ownedAll := ownedConstsPer ixonEnv shards
    -- Leaves a verified proof already covers stay exactly as they are.
    let proven : Std.HashMap Nat Address ← match opts.provenGuard with
      | none => pure {}
      | some guard => guard ixonEnv shards ownedAll selected
    if !proven.isEmpty then
      IO.println s!"[audit] {proven.size} selected leaf/leaves already have a \
        verified proof — kept unsplit"
    let cutLabeled (origin : Nat) (label : String) (blocks owned : Array Address)
        (p : Nat) : Array (Nat × String × Array Address × Array Address) :=
      let parts := cutBlocks blocks p
      (parts.zip (partitionOwned ixonEnv owned parts)).mapIdx
        fun i (part, po) => (origin, s!"{label}.{i}", part, po)
    -- One loop over execution waves. Wave 0 is the selected part of the
    -- planned partition; with a budget every over-budget leaf is cut into
    -- the peak model's suggested part count and the parts re-batched as
    -- the next wave, until everything fits or is a single block. Without
    -- a budget the FFI answers 1 part everywhere and the loop is a single
    -- wave — the plain batch check.
    let mut wave : Array (Nat × String × Array Address × Array Address) :=
      selected.filterMap fun k =>
        if proven.contains k then none
        else (shards[k]?).bind fun b => (ownedAll[k]?).map fun o => (k, s!"{k}", b, o)
    let executed := wave.size
    let mut waveNum := 0
    let mut failed : Array String := #[]
    let mut final : Array (Array Address × Nat) := #[]
    -- Per source leaf: its wave-0 peak, and the parts that ended its
    -- cascade (fit, or failed) — what the manifest and the report describe.
    let mut leafPeak : Std.HashMap Nat Nat := {}
    let mut leafParts : Std.HashMap Nat (Array PartReport) := {}
    let mut totalConsts := 0
    let mut elapsedMs := 0
    while wave.size > 0 do
      if waveNum == 0 then
        IO.println s!"Typechecking {wave.size} shard(s) in one rayon \
          batch, {jobs} thread(s) (0 = all)"
      else
        IO.println s!"[wave {waveNum}] re-executing {wave.size} part(s)"
      (← IO.getStdout).flush
      let ownedPer := wave.map (·.2.2.2)
      let start ← IO.monoMsNow
      match compiled.bytecode.shardCheckBatchWithEnv funIdx envHandle
          (addrListsBlob ownedPer) useBytecode jobs
          Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
          maxRamBytes with
      | .error e => IO.eprintln s!"shard batch (wave {waveNum}): {e}"; return 1
      | .ok rs =>
        if waveNum == 0 then
          -- The bench row's measured window: the planned partition's
          -- batch call, matching `check-rs`. Split waves are audit
          -- extras outside the benchmarked engine window.
          elapsedMs := (← IO.monoMsNow) - start
          totalConsts := ownedPer.foldl (· + ·.size) 0
        let mut next : Array (Nat × String × Array Address × Array Address) := #[]
        for (r, origin, label, blocks, owned) in rs.zip wave do
          let gib := toGib r.peakBytes
          if waveNum == 0 then leafPeak := leafPeak.insert origin r.peakBytes
          let mut settled : Option String := none
          if !r.error.isEmpty then
            IO.eprintln s!"[shard {label}] FAILED: {r.error}"
            failed := failed.push s!"shard {label}: {r.error}"
            settled := some r.error
          else if r.suggestedParts <= 1 then
            IO.println s!"[shard {label}] ok, projected prover peak {gib} GiB"
            settled := some ""
          else if blocks.size <= 1 then
            IO.eprintln s!"[shard {label}] peak {gib} GiB over budget and a \
              single block — cannot split"
            failed := failed.push s!"shard {label}: single block over budget"
            settled := some "single block over budget"
          else
            IO.println s!"[shard {label}] peak {gib} GiB over budget — cut \
              into {r.suggestedParts}"
            next := next ++ cutLabeled origin label blocks owned r.suggestedParts
          if let some error := settled then
            final := final.push (blocks, r.peakBytes)
            leafParts := leafParts.insert origin ((leafParts.getD origin #[]).push
              { label, blocks, owned, peak := r.peakBytes, error })
        wave := next
        waveNum := waveNum + 1
    let tag := if opts.emitOnFailure then "refine" else "split-audit"
    let waves := if waveNum == 0 then 0 else waveNum - 1
    if maxRamBytes > 0 then
      IO.println s!"[{tag}] {final.size} part(s) from {executed} executed \
        leaf/leaves ({shards.size} in the manifest), {waves} split wave(s), \
        {failed.size} failure(s)"
    -- A split leaf's parts in block order, whatever wave settled them.
    let sortedParts (k : Nat) (parts : Array PartReport) : Array PartReport :=
      let pos : Std.HashMap Address Nat :=
        (((shards[k]?).getD #[]).mapIdx fun i a => (a, i)).foldl
          (fun m (a, i) => m.insert a i) {}
      let posOf (p : PartReport) : Nat := ((p.blocks[0]?).bind pos.get?).getD 0
      parts.qsort fun a b => posOf a < posOf b
    -- The refined partition — what this run actually validated — written
    -- as a refinement of the manifest it started from: untouched leaves
    -- keep their records, ids and tree positions; a failed leaf stays as
    -- in the source.
    let runs : Array (Nat × Array (Array Address × Nat)) :=
      (Array.range shards.size).filterMap fun k =>
        (leafParts.get? k).bind fun ps =>
          if ps.any (·.error != "") then none
          else some (k, (sortedParts k ps).map fun p => (p.blocks, p.peak))
    let mut idTable : Array (Array Nat) := #[]
    let mut wroteManifest := false
    if let some out := outIxes then
      if failed.isEmpty || opts.emitOnFailure then
        let (refinements, measured) := refinementsOfRuns shards.size runs
        idTable ← emitRefinedManifest tag envHandle manifestPath out
          refinements measured 0
        wroteManifest := true
      else
        IO.eprintln s!"--out-ixes {out} skipped: {failed.size} failure(s)"
    if let some reportPath := opts.report then
      -- New ids per split leaf, in refinement order (ascending leaf id).
      let mut newIds : Std.HashMap Nat (Array Nat) := {}
      for ((k, _), ids) in (runs.filter (·.2.size > 1)).zip idTable do
        newIds := newIds.insert k ids
      let digestJson (owned : Array Address) : Lean.Json :=
        match claimDigestOfOwned ixonEnv owned with
        | .ok d => Lean.Json.str (toString d)
        | .error _ => Lean.Json.null
      let mut leaves : Array Lean.Json := #[]
      let mut failures : Array Lean.Json := #[]
      for k in [0:shards.size] do
        let blocks := (shards[k]?).getD #[]
        let owned := (ownedAll[k]?).getD #[]
        let inRun := proven.contains k || selectedSet.contains k
        let base := [("id", Lean.toJson k), ("blocks", Lean.toJson blocks.size),
          ("consts", Lean.toJson owned.size),
          ("claim", if inRun then digestJson owned else Lean.Json.null),
          ("predicted_peak_bytes", match leafPeak.get? k with
            | some p => Lean.toJson p | none => Lean.Json.null)]
        let status (s : String) := Lean.Json.mkObj (base ++ [("status", Lean.Json.str s)])
        if let some addr := proven.get? k then
          leaves := leaves.push (Lean.Json.mkObj (base ++
            [("status", Lean.Json.str "proven-kept"), ("proof", Lean.Json.str (toString addr))]))
        else if !selectedSet.contains k then
          leaves := leaves.push (status "unchanged")
        else match leafParts.get? k with
          | none => leaves := leaves.push (status "unchanged")
          | some ps =>
            let ps := sortedParts k ps
            let anyFailed := ps.any (·.error != "")
            for p in ps do
              if p.error != "" then
                let names := (p.owned.filterMap fun a =>
                  (ixonEnv.addrToName.get? a).map toString).extract 0 8
                failures := failures.push (Lean.Json.mkObj ([("id", Lean.toJson k),
                  ("label", Lean.Json.str p.label), ("reason", Lean.Json.str p.error),
                  ("blocks", Lean.toJson p.blocks.size), ("consts", Lean.toJson p.owned.size),
                  ("predicted_peak_bytes", Lean.toJson p.peak),
                  ("names", Lean.toJson names)]
                  ++ (match p.blocks[0]? with
                      | some b => if p.blocks.size == 1 then [("block", Lean.Json.str (toString b))] else []
                      | none => [])))
            if anyFailed then
              leaves := leaves.push (status "failed")
            else if ps.size == 1 then
              leaves := leaves.push (status "measured")
            else
              let ids := (newIds.get? k).getD #[]
              let depth := ps.foldl (fun d p => max d ((p.label.splitOn ".").length - 1)) 0
              let parts := ps.mapIdx fun i p => Lean.Json.mkObj [
                ("id", match ids[i]? with | some id => Lean.toJson id | none => Lean.Json.null),
                ("label", Lean.Json.str p.label), ("blocks", Lean.toJson p.blocks.size),
                ("consts", Lean.toJson p.owned.size),
                ("predicted_peak_bytes", Lean.toJson p.peak),
                ("claim", digestJson p.owned)]
              leaves := leaves.push (Lean.Json.mkObj (base ++
                [("status", Lean.Json.str "split"), ("depth", Lean.toJson depth),
                 ("parts", Lean.Json.arr parts)]))
      -- Consolidation: the leaf count the measured total says would fit the
      -- budget — arithmetic from measured peaks, never an execution.
      let consolidation := if maxRamBytes > 0 then
          let sum := final.foldl (· + ·.2) 0
          let target := maxRamBytes * 95 / 100
          Lean.toJson (max 1 ((sum + target - 1) / target))
        else Lean.Json.null
      let sourceDigest ← fileDigest manifestPath
      let outJson ← match outIxes with
        | some out =>
          if wroteManifest then do
            let d ← fileDigest out
            let n := shards.size + idTable.foldl (fun acc ids => acc + ids.size - 1) 0
            pure (fileJson out d (some n))
          else pure Lean.Json.null
        | none => pure Lean.Json.null
      let envBytes ← (do
        try pure (Lean.toJson (← System.FilePath.metadata ixePath).byteSize.toNat)
        catch _ => pure Lean.Json.null)
      let report := Lean.Json.mkObj [
        ("schema", Lean.Json.str "ix-refine/0"),
        ("revision", Lean.Json.str (← gitRevision)),
        ("command", Lean.Json.str opts.command),
        ("env", Lean.Json.mkObj [("path", Lean.Json.str ixePath), ("bytes", envBytes)]),
        ("source", fileJson manifestPath sourceDigest (some shards.size)),
        ("out", outJson),
        ("budget_bytes", Lean.toJson maxRamBytes),
        ("budget_source", Lean.Json.str opts.budgetSource),
        ("jobs", Lean.toJson jobs),
        ("selected", Lean.toJson selected.size),
        ("executed", Lean.toJson executed),
        ("waves", Lean.toJson waves),
        ("consolidation_shards", consolidation),
        ("leaves", Lean.Json.arr leaves),
        ("failures", Lean.Json.arr failures)]
      IO.FS.writeFile reportPath (report.pretty ++ "\n")
      IO.println s!"[{tag}] report → {reportPath}"
    -- One env-keyed results row for `ix bench run --backend aiur-sharded-env`:
    -- the measured window is the wave-0 batch FFI call (env load and
    -- blob setup are excluded, matching what the benchmark tracks — the
    -- execution engine, not the loader).
    if let some (path, key) := json? then
      let secs := elapsedMs.toFloat / 1000.0
      let tput := if elapsedMs > 0
        then totalConsts.toFloat * 1000.0 / elapsedMs.toFloat else 0.0
      let peakRss ← TracingTexray.peakTreeRssBytes
      let status := if failed.isEmpty then "ok" else "rejected"
      Ix.Benchmark.Results.writeRow path key status
        [ ("constants", Lean.toJson totalConsts)
        , ("shards", Lean.toJson final.size)
        , ("check-time", Ix.Benchmark.Results.jsonRound 3 secs)
        , ("throughput", Ix.Benchmark.Results.jsonRound 2 tput)
        , ("peak-rss", Lean.toJson peakRss) ]
    if failed.isEmpty then
      IO.println s!"All {final.size} shard(s) passed"
      return 0
    IO.eprintln s!"{failed.size} of {final.size} shard(s) FAILED:"
    for f in failed do IO.eprintln s!"  {f}"
    -- `ix shard refine` still wrote its manifest (failed leaves unchanged):
    -- exit 2 tells the operator to read the report. Under `--json` a kernel
    -- rejection is the benchmark's `rejected` exit (the row is already
    -- written), same contract as `check-rs`.
    if opts.emitOnFailure then return 2
    return if json?.isSome then Ix.Benchmark.Results.exitRejected else 1


/-- Run the shard operation over EVERY shard — the whole-partition behavior of
    `--ixes` with no `--shard` (used by `prove`). Loads the env once. Returns 1
    if any shard fails, else 0. -/
def runShardManifestAll (manifestPath ixePath : String)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) =>
    let mut rc : UInt32 := 0
    for (blocks, k) in shards.mapIdx (fun k b => (b, k)) do
      if (← runShardOwned ixonEnv blocks k runOne) != 0 then rc := 1
    pure rc

/-- Check EVERY shard of the partition concurrently (shards are independent
    bytecode runs) after verifying coverage — the whole-partition behavior of
    `check --ixes` with no `--shard`. At most `jobs` shards run at once
    (`none` ⇒ all of them); cap it to bound peak RAM, since each in-flight
    shard's IO buffer re-ingests its whole closure. Returns 1 on a coverage gap
    or any shard failure. -/
def runShardCheckAll (manifestPath ixePath : String) (jobs? : Option Nat)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  let (ixonEnv, shards) ← match (← loadEnvAndShards manifestPath ixePath) with
    | .error e => IO.eprintln e; return 1
    | .ok r => pure r
  if !(← shardsCover ixonEnv shards) then return 1
  -- The env + compiled toplevel are read-only, so each shard runs on its own
  -- dedicated task; chunk by `jobs` to cap the number in flight at once.
  let maxJobs := max 1 (jobs?.getD shards.size)
  let mut rc : UInt32 := 0
  for chunk in (shards.mapIdx (fun k b => (b, k))).toList.toChunks maxJobs do
    let tasks ← chunk.mapM fun (blocks, k) =>
      IO.asTask (prio := .dedicated) (runShardOwned ixonEnv blocks k runOne)
    for t in tasks do
      match t.get with
      | .ok r => if r != 0 then rc := 1
      | .error e => IO.eprintln s!"shard check task failed: {e}"; rc := 1
  pure rc

end Ix.Shard.Check
end
