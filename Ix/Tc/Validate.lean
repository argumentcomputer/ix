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

/-! ### Gate 2: anon structural roundtrip -/

/-- Roundtrip every work item of an env (parallel over the task pool).
    Returns `(rows, firstFailure?)`; full coverage means
    `rows == env.consts.size`. -/
def anonRoundtripEnv (ixonEnv : Ixon.Env) : Nat × Option String := Id.run do
  match buildAnonWork ixonEnv with
  | .error e => return (0, some s!"work discovery failed: {e}")
  | .ok work =>
    let mut rows := 0
    let mut firstErr : Option String := none
    for t in roundtripTasks ixonEnv work do
      for r in t.get do
        rows := rows + 1
        if firstErr.isNone then
          if let some msg := r.err? then
            firstErr := some s!"{r.addr}: {msg}"
    if firstErr.isNone && rows != ixonEnv.consts.size then
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

end Ix.Tc

end
end
