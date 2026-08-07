module

public import Ix.Tc.Driver
public import Ix.Tc.IngressMeta
public import Ix.Tc.ParCheck
public import Ix.Tc.EgressLean
public import Ix.CanonM

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
   as informational `notFound`, as in Rust.
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
    | _ => false

/-- Meta roundtrip summary counts. -/
structure MetaRoundtripReport where
  checked : Nat := 0
  notFound : Nat := 0
  skippedAux : Nat := 0
  skippedSurgery : Nat := 0
  /-- Total comparison errors (all of them, not just the stored ones). -/
  errorCount : Nat := 0
  /-- First ≤ 50 comparison errors. -/
  errors : Array (Ix.Name × String) := #[]

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
      | .error name msg =>
        report := { report with errorCount := report.errorCount + 1 }
        if report.errors.size < 50 then
          report := { report with errors := report.errors.push (name, msg) }
  return report

/-- Streaming `metaRoundtripEnv`: same per-name verdicts, but each chunk
    materializes its §5 rows, ingresses them into a chunk-local `MetaEnv`
    (a per-chunk env value sharing the lazy parts' consts/names/blobs
    maps with only the chunk's `named` entries filled — the ingress
    itself is already per-entry-independent, which is what let the eager
    driver merge chunk-local envs), egresses, compares, and DROPS
    everything. The whole-env merged `MetaEnv` — a third whole-env copy
    live alongside the Lean oracle env at whole-Mathlib scale — never
    exists. Rows arrive in §5 order (ascending name hash), matching the
    eager driver's sort. -/
def metaRoundtripEnvStreaming (leanEnv : Lean.Environment)
    (parts : Ixon.LazyEnvParts) (chunkSize : Nat := 512)
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
  let grouped : Array (Array Ixon.NamedRow) := Id.run do
    let mut byBlock : Std.HashMap Address (Array Ixon.NamedRow) := {}
    let mut order : Array Address := #[]
    for row in rows do
      let k := blockKey row
      match byBlock.get? k with
      | some arr => byBlock := byBlock.insert k (arr.push row)
      | none =>
        byBlock := byBlock.insert k #[row]
        order := order.push k
    return order.map (byBlock.get? · |>.getD #[])
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
  let compareTasks := Id.run do
    let mut out : Array (Task (Array MetaVerdict)) := #[]
    let mut i := 0
    let mut pending : Array Ixon.NamedRow := #[]
    let mut chunks : Array (Array Ixon.NamedRow) := #[]
    for group in grouped do
      if !pending.isEmpty && pending.size + group.size > chunkSize then
        chunks := chunks.push pending
        pending := #[]
      pending := pending ++ group
    if !pending.isEmpty then
      chunks := chunks.push pending
    while i < chunks.size do
      let chunk := chunks[i]!
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
        for row in chunk do
          match row.materialize parts.backing parts.nameRev with
          | .ok named =>
            chunkOnly := chunkOnly.insert row.name named
            resolveNamed := resolveNamed.insert row.name named
          | .error e => materializeErrs := materializeErrs.insert row.name e
        let chunkNamed := chunkOnly
        let workEnv := { parts.env with named := chunkOnly }
        let resolveEnv := { parts.env with named := resolveNamed }
        let kenv? : Except IngressErr (MetaEnv) :=
          ingressEnvParallelWith (buildMetaWork workEnv)
            (ingressMetaWorkItem resolveEnv · true) chunkSize
        chunk.map fun row => Id.run do
          if let some e := materializeErrs.get? row.name then
            return .error row.name s!"metadata materialize failed: {e}"
          let some named := chunkNamed.get? row.name
            | return .error row.name "row lost during materialization"
          if named.original.isSome then
            return .skippedAux
          if metaHasAlteringSurgery named.constMeta then
            return .skippedSurgery
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
      i := i + 1
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
      | .error name msg =>
        report := { report with errorCount := report.errorCount + 1 }
        if report.errors.size < 50 then
          report := { report with errors := report.errors.push (name, msg) }
  return report

end Ix.Tc

end
end
