module

public import Ix.Tc.Driver
public import Ix.Tc.IngressMeta
public import Ix.Tc.ParCheck
public import Ix.Tc.EgressLean
public import Ix.CanonM
public import Ix.Compile.Pass.Names

/-!
Whole-env validation drivers for the pure-Lean `Ix.Tc` pipeline — the
shared core behind the `tc-roundtrip` test suite and `ix validate-lean`.

Three gates over a Rust-compiled `.ixe` byte image:

1. `serdeGate` — the pure parser/writer close the loop: `Ixon.deEnv`
   parses every section (call-site surgery, extension tables, aux
   layouts, originals included) and `Ixon.serEnv` reproduces the input
   bytes EXACTLY.
2. `anonRoundtripEnv` — structural kernel roundtrip: every constant
   anon-ingressed, egressed back to `Ixon.Constant`, canonically compared
   (see `Ix.Tc.Egress`); projections byte-exact. Parallel per work item.
3. `metaRoundtripEnv` — full-fidelity kernel roundtrip against the SOURCE
   Lean environment (the oracle): phase-parallel meta ingress of the
   whole env into one merged `KEnv .meta`, then per-named-entry egress to
   `Ix.ConstantInfo` compared against `CanonM.canonConst` of the original
   constant with Rust `compare_envs` semantics — type hash always, value
   hash for defn/thm/opaque, per-rule RHS for recursors. LEON hashes are
   name/info/mdata-sensitive, so this certifies metadata fidelity.
   Skipped with counts: aux-rewritten entries (`original.isSome` —
   decompile regenerates those) and altering-surgery entries
   (`metaHasAlteringSurgery` — only decompile's surgery replay can
   restore their source form); ixon names absent from the Lean env count
   as informational `notFound`, as in Rust, and reserved `_ix` display
   entries as `display`. The streaming driver (`metaRoundtripEnvStreaming`)
   routes the blocks the compiler collapsed (`collapsedBlocks`) out of the
   gated comparison (BB-F7: the meta ingress loses a collapsed member) for
   the caller's anonymous roundtrip, and charges an ingress failure to its
   block rather than to its chunk.

Plus `checkAnonAddrs`: anonymous `Ix.Tc` checks of chosen constants with
lazy ingress of their closure (`ix validate-lean` phase 7's rule
statements, in a test-only copy of the environment).
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashMap)

/-! ### Gate 1: pure serde -/

/-- Parse `bytes` with the pure reader and require the pure writer to
    reproduce them byte-exactly. Returns the parsed env. -/
def serdeGate (bytes : ByteArray) : Except String Ixon.Env := do
  let env ← match Ixon.deEnv bytes with
    | .ok env => pure env
    | .error e => throw s!"pure deEnv failed: {e}"
  match Ixon.serEnv env with
  | .error e => throw s!"pure serEnv failed: {e}"
  | .ok bytes' =>
    if bytes' != bytes then
      throw s!"serEnv bytes differ from input: {bytes'.size} vs {bytes.size}"
  return env

/-- Streaming `serdeGate`: identical verification strength — every unit
    parsed by the pure reader, re-serialized by the pure writer, and
    compared against its input span, spans covering the image gaplessly,
    plus the order/root/trailing contracts the whole-image compare used
    to pin — at O(largest unit) transient memory instead of two whole-env
    materializations (`Ixon.getEnvVerifiedLazy`). Constants stay
    zero-copy windows; §5 metadata stays a window per `NamedRow`,
    materialized per name by consumers. At whole-Mathlib scale this is
    the difference between ~6 GiB and a >100 GiB resident spike. -/
def serdeGateStreaming (bytes : ByteArray) : Except String Ixon.LazyEnvParts :=
  Ixon.deEnvVerifiedLazy bytes

/-! ### Gate 2: anon structural roundtrip -/

/-- Roundtrip every work item of an env (parallel over the task pool).
    Returns `(rows, firstFailure?)`; full coverage means
    `rows == env.consts.size`. -/
def anonRoundtripEnv (ixonEnv : Ixon.Env) (cap : Option Nat := none)
    (sequential : Bool := false) (stageCut : Nat := 0) :
    Nat × Option String := Id.run do
  match dbgTrace "[anonRoundtrip] building work" (fun _ => buildAnonWork ixonEnv) with
  | .error e => return (0, some s!"work discovery failed: {e}")
  | .ok workAll =>
    let work := match cap with
      | some n => workAll.extract 0 n
      | none => workAll
    if sequential then
      let mut rows := 0
      let mut firstErr : Option String := none
      for item in work do
        for r in roundtripWorkItem ixonEnv item true stageCut do
          rows := rows + 1
          if firstErr.isNone then
            if let some msg := r.err? then
              firstErr := some s!"{r.addr}: {msg}"
      if cap.isNone && firstErr.isNone && rows != ixonEnv.consts.size then
        firstErr := some
          s!"coverage gap: {rows} rows vs {ixonEnv.consts.size} env constants"
      return (rows, firstErr)
    let tasks := dbgTrace s!"[anonRoundtrip] {work.size} items (of {workAll.size}); spawning tasks"
      fun _ => roundtripTasks ixonEnv work
    let mut rows := 0
    let mut firstErr : Option String := none
    let mut ti := 0
    for t in tasks do
      if ti % 200 == 0 then
        dbgTrace s!"[anonRoundtrip] awaiting task {ti}/{tasks.size}" fun _ => ()
      ti := ti + 1
      for r in t.get do
        rows := rows + 1
        if firstErr.isNone then
          if let some msg := r.err? then
            firstErr := some s!"{r.addr}: {msg}"
    if cap.isNone && firstErr.isNone && rows != ixonEnv.consts.size then
      firstErr := some
        s!"coverage gap: {rows} roundtrip rows vs {ixonEnv.consts.size} env constants"
    return (rows, firstErr)

/-! ### Gate 3: meta roundtrip vs the source Lean env -/

/-- Per-entry meta roundtrip verdict. -/
inductive MetaVerdict where
  | checked
  | notFound
  | skippedAux
  | skippedSurgery
  /-- A reserved `_ix` display entry (D14): an alias of an Ix auxiliary, not a
      Lean constant, so the source environment has nothing to compare it
      with. -/
  | display
  | error (name : Ix.Name) (msg : String)

/-- Whether a metadata arena carries ALTERING call-site surgery: collapsed
    arguments, a rewritten head, or a non-identity kept permutation. Such
    constants' canonical expressions genuinely differ from the Lean source
    (compile rewrote them, recording how to restore the source in the
    surgery metadata) — only decompile's surgery REPLAY can undo that, so
    the kernel-direct comparison skips them with a count. Identity-kept
    call sites (every source arg kept in place, head unchanged) are NOT
    altering and stay in the comparison. Their anon-structural fidelity is
    covered by the anon roundtrip either way. -/
def metaHasAlteringSurgery (cm : Ixon.ConstantMeta) : Bool :=
  let arena := match cm.info with
    | .defn _ _ _ _ a _ _ => a
    | .axio _ _ a _ => a
    | .quot _ _ a _ => a
    | .indc _ _ _ _ _ a _ => a
    | .ctor _ _ _ a _ => a
    | .recr _ _ _ _ _ a _ _ => a
    | .empty | .muts _ _ => {}
  arena.nodes.any fun node => match node with
    | .callSite _ entries canonMeta origHead =>
      origHead.isSome || entries.size != canonMeta.size ||
      (entries.zipIdx.any fun (e, i) => match e with
        | .collapsed .. => true
        | .kept canonIdx _ => canonIdx.toNat != i)
    | .etaCallSite .. => true
    -- Pass 3's decompile record of a rewritten call site (`_ix.inline`):
    -- the term is the inline form, the source lives in `metaSharing`.
    | .mdata kvmaps _ => kvmaps.any fun kv => kv.any fun (k, _) =>
      k == Ix.Compile.Pass.inlineKey.getHash
    | _ => false

/-- Meta roundtrip summary counts. -/
structure MetaRoundtripReport where
  checked : Nat := 0
  notFound : Nat := 0
  skippedAux : Nat := 0
  skippedSurgery : Nat := 0
  /-- Total comparison errors (all of them, not just the stored ones). -/
  errorCount : Nat := 0
  /-- The first comparison errors: ≤ 50 in the eager driver, ≤ 1000 in the
      streaming one (which localises an ingress failure to its block, so
      this bounds blocks rather than chunks). -/
  errors : Array (Ix.Name × String) := #[]
  /-- Reserved `_ix` display entries (`MetaVerdict.display`). -/
  display : Nat := 0
  /-- Rows of collapsed blocks routed to the anonymous roundtrip (BB-F7: the
      meta-mode ingress loses a collapsed member). They are neither counted
      as checked nor as errors here; their meta-mode verdicts are reported in
      the `routed*` fields and the caller roundtrips `routedBlocks` in
      anonymous mode. -/
  routedRows : Nat := 0
  /-- Owning block addresses of the routed rows. -/
  routedBlocks : Array Address := #[]
  /-- Meta-mode verdicts on the routed rows (reported, not gated). -/
  routedChecked : Nat := 0
  routedErrorCount : Nat := 0
  routedErrors : Array (Ix.Name × String) := #[]

/-- Meta whole-env roundtrip: phase-parallel ingress (chunked local envs
    merged via `KEnv.union`), then parallel per-named-entry egress+compare
    against `leanEnv` (the oracle). -/
def metaRoundtripEnv (leanEnv : Lean.Environment) (ixonEnv : Ixon.Env)
    (chunkSize : Nat := 512) : Except String MetaRoundtripReport := do
  -- Phase 1: parallel chunked ingress into local kernel envs, merged
  -- (shared with `ix check-lean`'s meta path).
  let kenv : MetaEnv ← match ingressMetaEnvParallel ixonEnv chunkSize with
    | .ok env => pure env
    | .error e => throw s!"meta ingress failed: {e}"
  -- Source-side canonical map: Ix.Name → Lean.ConstantInfo.
  let canonMap : Std.HashMap Ix.Name Lean.ConstantInfo := Id.run do
    let (m, _) := (leanEnv.constants.toList.foldlM
      (fun (m : Std.HashMap Ix.Name Lean.ConstantInfo)
           (p : Lean.Name × Lean.ConstantInfo) => do
        let ixn ← Ix.CanonM.canonName p.1
        return m.insert ixn p.2) {} : Ix.CanonM.CanonM _).run {}
    return m
  -- Phase 2: parallel egress + compare per named entry.
  let entries := ixonEnv.named.toArray.qsort fun a b =>
    (a.1.getHash.cmpBytes b.1.getHash).isLT
  let kenvShared := kenv
  let compareTasks := Id.run do
    let mut out : Array (Task (Array MetaVerdict)) := #[]
    let mut i := 0
    while i < entries.size do
      let chunk := entries.extract i (min (i + chunkSize) entries.size)
      out := out.push <| Task.spawn fun () =>
        chunk.map fun (name, named) => Id.run do
          if named.original.isSome then
            return .skippedAux
          if metaHasAlteringSurgery named.constMeta then
            return .skippedSurgery
          match canonMap[name]? with
          | none => return .notFound
          | some leanCI =>
            match kenvShared.get? ⟨named.addr, name⟩ with
            | none =>
              return .error name "constant absent from kernel env after ingress"
            | some kc =>
              match egressConstant kc with
              | .error e => return .error name s!"egress failed: {e}"
              | .ok egressed =>
                let (orig, _) := (Ix.CanonM.canonConst leanCI).run {}
                match compareLeanCI orig egressed with
                | none => return .checked
                | some msg => return .error name msg
      i := i + chunkSize
    return out
  let mut report : MetaRoundtripReport := {}
  for t in compareTasks do
    for v in t.get do
      match v with
      | .checked => report := { report with checked := report.checked + 1 }
      | .notFound => report := { report with notFound := report.notFound + 1 }
      | .skippedAux =>
        report := { report with skippedAux := report.skippedAux + 1 }
      | .skippedSurgery =>
        report := { report with skippedSurgery := report.skippedSurgery + 1 }
      | .display => report := { report with display := report.display + 1 }
      | .error name msg =>
        report := { report with errorCount := report.errorCount + 1 }
        if report.errors.size < 50 then
          report := { report with errors := report.errors.push (name, msg) }
  return report

/-- The projection key of a named row's constant: `(block, member, ctor+1)`
    for a projection (`0` in the last slot for a non-constructor), `none`
    for a standalone constant. Two distinct Lean names with one key are
    members of a collapsed class (alpha-collapse in Pass 1). -/
def projKey? (env : Ixon.Env) (addr : Address) : Option (Address × UInt64 × UInt64) :=
  match (env.consts.get? addr).bind (·.get?) with
  | some c =>
    match c.info with
    | .iPrj p => some (p.block, p.idx, 0)
    | .cPrj p => some (p.block, p.idx, p.cidx + 1)
    | .rPrj p => some (p.block, p.idx, 0)
    | .dPrj p => some (p.block, p.idx, 0)
    | _ => none
  | none => none

/-- The blocks of `parts` the compiler collapsed: a `Muts` block in which
    two distinct named rows (synthetic `Muts` names excluded by the caller's
    `skip`) project to the same member. -/
def collapsedBlocks (parts : Ixon.LazyEnvParts) (skip : Ix.Name → Bool := fun _ => false) :
    Std.HashSet Address := Id.run do
  let mut seen : Std.HashMap (Address × UInt64 × UInt64) Ix.Name := {}
  let mut out : Std.HashSet Address := {}
  for row in parts.namedRows do
    if skip row.name then continue
    if let some k := projKey? parts.env row.addr then
      match seen.get? k with
      | some n => if n != row.name then out := out.insert k.1
      | none => seen := seen.insert k row.name
  return out

/-- Streaming `metaRoundtripEnv`: same per-name verdicts, but each chunk
    materializes its §5 rows, ingresses them into a chunk-local `MetaEnv`
    (a per-chunk env value sharing the lazy parts' consts/names/blobs
    maps with only the chunk's `named` entries filled — the ingress
    itself is already per-entry-independent, which is what let the eager
    driver merge chunk-local envs), egresses, compares, and DROPS
    everything. The whole-env merged `MetaEnv` — a third whole-env copy
    live alongside the Lean oracle env at whole-Mathlib scale — never
    exists. Rows arrive in §5 order (ascending name hash), matching the
    eager driver's sort.

    **Collapsed blocks (BB-F7).** The meta-mode ingress of a collapsed
    block loses a collapsed member (`Ix.Tc`'s ingress keys a member by its
    name, and a collapsed class has one member for several names). With
    `routed` (the caller passes `collapsedBlocks`), the rows of those blocks
    are taken out of the gated comparison: each such block is ingressed on
    its own, its meta verdicts land in `routedChecked`/`routedErrors`
    (reported, not gated), and its address in `routedBlocks`, which the
    caller roundtrips in anonymous mode.

    **Failure localisation.** When a chunk's ingress fails, each block of
    the chunk is ingressed on its own, so an ingress failure is charged to
    the rows of the block that caused it (e.g. BELOW-ORDER: the canonicity
    gate rejects one `IndPredBelow` block), not to the whole chunk. -/
def metaRoundtripEnvStreaming (leanEnv : Lean.Environment)
    (parts : Ixon.LazyEnvParts) (chunkSize : Nat := 512)
    (routed : Std.HashSet Address := {})
    : Except String MetaRoundtripReport := do
  -- Source-side canonical map: Ix.Name → Lean.ConstantInfo.
  let canonMap : Std.HashMap Ix.Name Lean.ConstantInfo := Id.run do
    let (m, _) := (leanEnv.constants.toList.foldlM
      (fun (m : Std.HashMap Ix.Name Lean.ConstantInfo)
           (p : Lean.Name × Lean.ConstantInfo) => do
        let ixn ← Ix.CanonM.canonName p.1
        return m.insert ixn p.2) {} : Ix.CanonM.CanonM _).run {}
    return m
  -- Meta ingress of a Muts member resolves its SIBLING members' names
  -- through `env.named`, so a chunk must contain whole blocks: group rows
  -- by owning block (projections parse their tiny constant to read the
  -- block address; everything else owns itself), then pack whole groups
  -- into chunks. Grouping keys keep §5 row order for determinism.
  let rows := parts.namedRows
  let blockKey : Ixon.NamedRow → Address := fun row =>
    match (parts.env.consts.get? row.addr).bind (·.get?) with
    | some c =>
      match c.info with
      | .iPrj p => p.block
      | .cPrj p => p.block
      | .rPrj p => p.block
      | .dPrj p => p.block
      | _ => row.addr
    | none => row.addr
  let (grouped, groupKeys) : Array (Array Ixon.NamedRow) × Array Address := Id.run do
    let mut byBlock : Std.HashMap Address (Array Ixon.NamedRow) := {}
    let mut order : Array Address := #[]
    for row in rows do
      let k := blockKey row
      match byBlock.get? k with
      | some arr => byBlock := byBlock.insert k (arr.push row)
      | none =>
        byBlock := byBlock.insert k #[row]
        order := order.push k
    return (order.map (byBlock.get? · |>.getD #[]), order)
  -- Ingress also resolves every name a metadata arena REFERENCES to its
  -- constant address (`resolve_all`), across the whole env — only the
  -- `.addr` is read for referenced entries. One shared address-only stub
  -- table (no metadata parse, ~O(rows) tiny) serves those lookups; each
  -- chunk overlays its own rows fully materialized.
  let stubNamed : Std.HashMap Ix.Name Ixon.Named := Id.run do
    let mut m : Std.HashMap Ix.Name Ixon.Named := {}
    for row in rows do
      m := m.insert row.name { addr := row.addr, hints := row.hints }
    return m
  -- Chunks of whole groups; a routed (collapsed) block is a chunk of its own.
  let (chunks, routedFlags) : Array (Array (Array Ixon.NamedRow)) × Array Bool := Id.run do
    let mut chunks : Array (Array (Array Ixon.NamedRow)) := #[]
    let mut flags : Array Bool := #[]
    let mut pending : Array (Array Ixon.NamedRow) := #[]
    let mut pendingRows := 0
    for (group, key) in grouped.zip groupKeys do
      if routed.contains key then
        chunks := chunks.push #[group]
        flags := flags.push true
        continue
      if !pending.isEmpty && pendingRows + group.size > chunkSize then
        chunks := chunks.push pending
        flags := flags.push false
        pending := #[]
        pendingRows := 0
      pending := pending.push group
      pendingRows := pendingRows + group.size
    if !pending.isEmpty then
      chunks := chunks.push pending
      flags := flags.push false
    return (chunks, flags)
  let compareTasks := Id.run do
    let mut out : Array (Task (Array (Bool × MetaVerdict))) := #[]
    let mut i := 0
    while i < chunks.size do
      let groups := chunks[i]!
      let isRouted := routedFlags[i]!
      out := out.push <| Task.spawn fun () => Id.run do
        -- Materialize this chunk's rows; failures become per-name errors.
        -- Work is enumerated from the CHUNK-ONLY env (so only this
        -- chunk's rows are ingressed), while ingress-time name→address
        -- resolution reads the chunk rows overlaid on the whole-env stub
        -- table (references reach across blocks; only `.addr` is read
        -- for non-chunk entries).
        let mut chunkOnly : Std.HashMap Ix.Name Ixon.Named := {}
        let mut resolveNamed : Std.HashMap Ix.Name Ixon.Named := stubNamed
        let mut materializeErrs : Std.HashMap Ix.Name String := {}
        for group in groups do
          for row in group do
            match row.materialize parts.backing parts.nameRev with
            | .ok named =>
              chunkOnly := chunkOnly.insert row.name named
              resolveNamed := resolveNamed.insert row.name named
            | .error e => materializeErrs := materializeErrs.insert row.name e
        let chunkNamed := chunkOnly
        let resolveEnv := { parts.env with named := resolveNamed }
        let ingressRows (rs : Array Ixon.NamedRow) : Except IngressErr MetaEnv :=
          let only : Std.HashMap Ix.Name Ixon.Named := rs.foldl (init := {}) fun m row =>
            match chunkNamed.get? row.name with
            | some nd => m.insert row.name nd
            | none => m
          let workEnv := { parts.env with named := only }
          ingressEnvParallelWith (buildMetaWork workEnv)
            (ingressMetaWorkItem resolveEnv · true) chunkSize
        let whole := ingressRows (groups.foldl (· ++ ·) #[])
        -- A failed chunk ingress is retried block by block, so the failure
        -- is charged to the block that caused it.
        let perGroup : Array (Except IngressErr MetaEnv) := match whole with
          | .ok k => groups.map fun _ => .ok k
          | .error e =>
            if groups.size ≤ 1 then groups.map fun _ => .error e
            else groups.map ingressRows
        let mut verdicts : Array (Bool × MetaVerdict) := #[]
        for (group, kenv?) in groups.zip perGroup do
          for row in group do
            let v : MetaVerdict := Id.run do
              if let some e := materializeErrs.get? row.name then
                return .error row.name s!"metadata materialize failed: {e}"
              let some named := chunkNamed.get? row.name
                | return .error row.name "row lost during materialization"
              if named.original.isSome then
                return .skippedAux
              if metaHasAlteringSurgery named.constMeta then
                return .skippedSurgery
              if Ix.Compile.Pass.hasReserved row.name then
                return .display
              match canonMap[row.name]? with
              | none => return .notFound
              | some leanCI =>
                match kenv? with
                | .error e => return .error row.name s!"meta ingress failed: {e}"
                | .ok kenv =>
                  match kenv.get? ⟨named.addr, row.name⟩ with
                  | none =>
                    return .error row.name "constant absent from kernel env after ingress"
                  | some kc =>
                    match egressConstant kc with
                    | .error e => return .error row.name s!"egress failed: {e}"
                    | .ok egressed =>
                      let (orig, _) := (Ix.CanonM.canonConst leanCI).run {}
                      match compareLeanCI orig egressed with
                      | none => return .checked
                      | some msg => return .error row.name msg
            verdicts := verdicts.push (isRouted, v)
        return verdicts
      i := i + 1
    return out
  let mut report : MetaRoundtripReport := {}
  let mut routedBlocks : Array Address := #[]
  for (flag, group) in routedFlags.zip chunks do
    if flag then
      if let some row := (group[0]?).bind (·[0]?) then
        routedBlocks := routedBlocks.push (blockKey row)
  report := { report with routedBlocks }
  for t in compareTasks do
    for (isRouted, v) in t.get do
      if isRouted then
        match v with
        | .checked =>
          report := { report with routedRows := report.routedRows + 1,
                                  routedChecked := report.routedChecked + 1 }
        | .error name msg =>
          report := { report with routedRows := report.routedRows + 1,
                                  routedErrorCount := report.routedErrorCount + 1 }
          if report.routedErrors.size < 1000 then
            report := { report with routedErrors := report.routedErrors.push (name, msg) }
        | .skippedAux =>
          report := { report with skippedAux := report.skippedAux + 1 }
        | .skippedSurgery =>
          report := { report with skippedSurgery := report.skippedSurgery + 1 }
        | .display => report := { report with display := report.display + 1 }
        | .notFound => report := { report with notFound := report.notFound + 1 }
        continue
      match v with
      | .checked => report := { report with checked := report.checked + 1 }
      | .notFound => report := { report with notFound := report.notFound + 1 }
      | .skippedAux =>
        report := { report with skippedAux := report.skippedAux + 1 }
      | .skippedSurgery =>
        report := { report with skippedSurgery := report.skippedSurgery + 1 }
      | .display => report := { report with display := report.display + 1 }
      | .error name msg =>
        report := { report with errorCount := report.errorCount + 1 }
        if report.errors.size < 1000 then
          report := { report with errors := report.errors.push (name, msg) }
  return report

/-! ### Anonymous kernel checks of chosen constants (lazy ingress) -/

/-- Type-check the constants at `addrs` in anonymous mode with `Ix.Tc`,
    ingressing their dependencies lazily (the `TcState.newLazyAnon` fault
    hook), so the cost is the closure of the targets, not the environment.
    A projection is checked through its block. Returns one verdict per
    requested address (`none` = accepted). -/
def checkAnonAddrs (env : Ixon.Env) (addrs : Array Address) (verify : Bool := true) :
    Array (Address × Option String) := Id.run do
  let cfg : CheckCfg := { verifyHashes := verify }
  let mut items : Array AnonWorkItem := #[]
  let mut itemOf : Std.HashMap Address Nat := {}
  let mut early : Std.HashMap Address String := {}
  for a in addrs do
    let b := blockOfAddr env a
    if itemOf.contains b then continue
    match buildAnonWorkItem env b with
    | .ok (some item) =>
      itemOf := itemOf.insert b items.size
      items := items.push item
    | .ok none => early := early.insert a s!"no work item for {b}"
    | .error e => early := early.insert a s!"work discovery failed: {e}"
  let st := runAnonCheckList cfg items.toList (initialAnonCheckLoopState env cfg)
  let verdict : Std.HashMap Address (Option String) :=
    st.results.foldl (init := {}) fun m r => m.insert r.addr r.err?
  return addrs.map fun a =>
    match early.get? a with
    | some e => (a, some e)
    | none =>
      match verdict.get? a with
      | some v => (a, v)
      | none =>
        -- a block's own address is not among its projection targets
        match itemOf.get? (blockOfAddr env a) with
        | some i => (a, (st.results.find? (·.addr == items[i]!.primary)).bind (·.err?))
        | none => (a, some "not checked")

end Ix.Tc

end
end
