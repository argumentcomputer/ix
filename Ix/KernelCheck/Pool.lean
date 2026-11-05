module

public import Ix.KernelCheck.Step

@[expose] public section

/-! # The environment check on a pool of workers (untrusted harness)

`kernel-check-ixe --jobs <n>`: the per-record check split into the fold's two
phases (`Ix.Kernel.Cached.checkDecls`), with the second on `n` workers, as
upstream con-leche's driver runs it (`Main.lean`, `checkPool`).

1. **Phase A** is the check loop (`CheckIxeStep.checkLoopWith`) with an
   install-only step (`Installer.stepRecord`): every record is read and its
   declarations installed in order (`Cached.annotDeclStep`), recording their
   value checks (`Cached.PendingCheck`) with the record they belong to. A
   record whose reading or install fails, or that depends on one, is left
   out, and an install failure is rolled back as `Checker.step` rolls back.
2. **Phase B** checks every recorded check against its prefix view from a
   fresh memo state (`Cached.checkPending`, `Cached.checkRecord`'s
   computation) on `n` dedicated worker threads that claim one check at a
   time off a shared counter. The installed environment and the checks are
   marked persistent first, so that the workers share them without
   reference counting.
3. **The rows** come from the check loop run once more over the same order,
   with phase A's readings (their failures) and a step that returns each
   record's verdict: the first of its recorded checks that failed, else its
   install failure, else none. That pass blocks the dependents of a record
   whose check failed in phase B (phase A installed them), so its rows are
   the per-record check's: the same records in the same order, with the
   same outcome and reason.

A row's `readMicros` is phase A's reading; its `micros` is the record's
install in phase A plus its recorded checks in phase B, summed over the
workers that ran them (0 for a blocked, skipped or unread record, as in the
per-record check). A recursor record read with its inductive block shares
the block's. Not a certified verdict: `Ix.Kernel.Admission.checkBytes`
is. -/

namespace Benchmarks.Kernel.CheckIxePool

open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

/-! ## Phase A -/

/-- What one declaration installed during Phase A: the constants it prepended
to `fe.env.consts`, and the slice `[pendStart, pendStop)` of `pend` it recorded. -/
structure InstalledDecl (md : Ix.Kernel.Mode := .anon) where
  consts : List (Ix.Kernel.ConstantInfo md) := []
  pendStart : Nat := 0
  pendStop : Nat := 0

/-- Phase A's step state: the installed environment, the memo state and the
fold position (as `Checker`'s), every recorded check with the record it
belongs to, the records whose install failed, and the per-declaration
constants and check slices installed for each record. -/
structure Installer (md : Ix.Kernel.Mode := .anon) where
  fe : Ix.Kernel.FEnv md := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
  cs : Ix.Kernel.Cached.CState md := {}
  pos : Nat := 0
  pend : Array (Ix.Kernel.Cached.PendingCheck md) := #[]
  owners : Array Address := #[]
  installErrors : Std.HashMap Address (Ix.Kernel.CheckError md) := {}
  installedDecls : Std.HashMap Address (Array (InstalledDecl md)) := {}
  installedCount : Nat := 0
  installedLog : Array (Address × Array (InstalledDecl md)) := #[]

instance : Inhabited (Installer md) := ⟨{}⟩

/-- A record's declarations installed in order from a fresh accumulator of
recorded checks; the first failure ends it, rolled back as `Checker.step`
rolls back (the index rebuilt from the constants before the declaration,
the memo state reset), with the checks the declarations before it recorded.
`pendOffset` is the number of checks recorded before the record, so that the
slices in `InstalledDecl` index the global accumulator. -/
def installDecls (ev : Ix.Kernel.Evidences md) (pendOffset : Nat) (recordDecls : Bool := true)
    (allowUserAxioms : Bool := false) :
    Nat → Ix.Kernel.FEnv md → Array (Ix.Kernel.Cached.PendingCheck md) →
      Array (InstalledDecl md) → Ix.Kernel.Cached.CState md →
      List (Ix.Kernel.Declaration md) →
      Nat × Ix.Kernel.FEnv md × Array (Ix.Kernel.Cached.PendingCheck md) ×
        Array (InstalledDecl md) × Ix.Kernel.Cached.CState md ×
        Option (Ix.Kernel.CheckError md)
  | pos, fe, pend, decls, cs, [] => (pos, fe, pend, decls, cs, none)
  | pos, fe, pend, decls, cs, d :: rest =>
    let before := fe.env
    let recorded := pend
    let oldLen := fe.visibleBelow
    let pStart := pendOffset + recorded.size
    let stepFn := if allowUserAxioms then
        Ix.Kernel.Cached.annotDeclStepWithUserAxioms .verified ev
      else
        Ix.Kernel.Cached.annotDeclStep .verified ev
    match stepFn (pos, fe, pend) d cs with
    | .ok ((pos', fe', pend'), cs') =>
      let decls := if recordDecls then
          let added := fe'.env.consts.take (fe'.visibleBelow - oldLen)
          let pStop := pendOffset + pend'.size
          decls.push { consts := added, pendStart := pStart, pendStop := pStop }
        else decls
      installDecls ev pendOffset recordDecls allowUserAxioms pos' fe' pend' decls cs' rest
    | .error (e, _) => (pos + 1, Ix.Kernel.mkFEnv before, recorded, decls, {}, some e)

/-- Phase A's step: install a record's declarations, recording their checks. -/
def Installer.stepRecord (ev : Ix.Kernel.Evidences md) (recordDecls : Bool := true)
    (lazyDecls : Bool := false) (allowUserAxioms : Bool := false)
    (c : Installer md) (address : Address) (rd : Read md) :
    Installer md × Option (Ix.Kernel.CheckError md) :=
  let ⟨fe, cs, pos, pend, owners, installErrors, installedDecls, installedCount, installedLog⟩ := c
  -- the record's checks go to a fresh accumulator, appended afterwards:
  -- `installDecls` keeps the accumulator from before each declaration alive
  -- across its step (its rollback), so a step pushing onto the global
  -- accumulator would copy all of it once per declaration
  let (pos, fe, recorded, decls, cs, err) :=
    installDecls ev pend.size recordDecls allowUserAxioms pos fe #[] #[] cs rd.decls.toList
  let owners := Id.run do
    let mut o := owners
    for _ in [0:recorded.size] do o := o.push address
    return o
  let pend := pend ++ recorded
  let installErrors := match err with
    | some e => installErrors.insert address e
    | none => installErrors
  let installedDecls :=
    if recordDecls && !lazyDecls then installedDecls.insert address decls else installedDecls
  let installedLog :=
    if recordDecls && lazyDecls then installedLog.push (address, decls) else installedLog
  (⟨fe, cs, pos, pend, owners, installErrors, installedDecls, installedCount + 1, installedLog⟩, err)

/-- Reconstruct the checked logical index after Phase B: if no check failed
and no installed record was later blocked, `fe` is already exact; otherwise
keep only the declarations of non-blocked records (`ran`, in execution order)
up to the first declaration in each record whose Phase B checks failed. -/
def checkedLogicalEnv (fe : Ix.Kernel.FEnv md) (failures : Nat)
    (installedDecls : Std.HashMap Address (Array (InstalledDecl md)))
    (table : Array (Option (Ix.Kernel.CheckError md) × Nat))
    (ran : Array Address)
    (installedCount : Nat := installedDecls.size)
    (installedLog : Array (Address × Array (InstalledDecl md)) := #[]) : Ix.Kernel.FEnv md := Id.run do
  if failures == 0 && ran.size == installedCount then
    return fe
  let installedDecls :=
    if installedDecls.isEmpty && !installedLog.isEmpty then
      installedLog.foldl (init := Std.HashMap.emptyWithCapacity installedLog.size)
        fun m (a, ds) => m.insert a ds
    else installedDecls
  let mut consts : List (Ix.Kernel.ConstantInfo md) := []
  for a in ran do
    for d in installedDecls.getD a #[] do
      let mut failed := false
      for k in [d.pendStart : d.pendStop] do
        if (table[k]?.bind (·.1)).isSome then
          failed := true
      if failed then
        break
      consts := d.consts ++ consts
  return Ix.Kernel.mkFEnv ⟨consts⟩

/-! ## Phase B -/

/-- A watchdog slot: the record a worker is checking, and since when. -/
abbrev Slot := IO.Ref (Option (Address × Nat))

/-- Recorded check `k` against its prefix view, from a fresh memo state:
its failure, if any, and its time. -/
def checkOne (fe : Ix.Kernel.FEnv md) (pend : Array (Ix.Kernel.Cached.PendingCheck md)) (k : Nat) :
    IO (Option (Ix.Kernel.CheckError md) × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => match pend[k]? with
    | some pc => match Ix.Kernel.Cached.checkPending .verified fe pc {} with
      | .ok _ => none
      | .error e => some e
    | none => some (.internal s!"check phase: no recorded check {k}")
  return (r, ((← IO.monoNanosNow) - t0) / 1000)

/-- A worker: claim one check at a time off `next` until it is past the
checks, with its watchdog slot set while it checks. -/
def worker (fe : Ix.Kernel.FEnv md) (pend : Array (Ix.Kernel.Cached.PendingCheck md))
    (owners : Array Address) (next : IO.Ref Nat) (slot : Slot) :
    (fuel : Nat) → Array (Nat × Option (Ix.Kernel.CheckError md) × Nat) →
      IO (Array (Nat × Option (Ix.Kernel.CheckError md) × Nat))
  | 0, acc => pure acc
  | fuel + 1, acc => do
    let k ← next.modifyGet fun a => (a, a + 1)
    if k < pend.size then
      if let some a := owners[k]? then slot.set (some (a, ← IO.monoMsNow))
      let (r, micros) ← checkOne fe pend k
      slot.set none
      worker fe pend owners next slot fuel (acc.push (k, r, micros))
    else pure acc

/-- Phase B on one dedicated worker thread per slot: every check's failure,
if any, and its time, in check order. -/
def pool (fe : Ix.Kernel.FEnv md) (pend : Array (Ix.Kernel.Cached.PendingCheck md))
    (owners : Array Address) (slots : Array Slot) :
    IO (Array (Option (Ix.Kernel.CheckError md) × Nat)) := do
  let next ← IO.mkRef 0
  let mut tasks := #[]
  for slot in slots do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) (worker fe pend owners next slot (pend.size + 1) #[]))
  let mut table : Array (Option (Ix.Kernel.CheckError md) × Nat) :=
    Array.replicate pend.size (some (.internal "check phase: check never ran"), 0)
  for t in tasks do
    for (k, r, micros) in ← IO.ofExcept (← IO.wait t) do
      table := table.set! k (r, micros)
  return table

/-! ## The run -/

/-- The environment check over `addresses` with phase B on one worker per
slot (`slots`, the watchdog's; at least one). Rows go to `emit`, in the
per-record check's order; stage lines go to `log`. Returns the actual record outcome
and failed-root map. When `tier` is supplied, tier records are deferred during
Phase A and checked in staged order against the checked logical environment
after Phase B. -/
def runOutcome {σ : Type} (src : LoopSource σ md) (ev : Ix.Kernel.Evidences md) (names : Address → Array String)
    (addresses : Array Address) (skip : Std.HashSet String) (slots : Array Slot)
    (emit : Row → IO Unit) (log : String → IO Unit)
    (progress : Nat → Std.HashMap String Nat → IO Unit := fun _ _ => pure ())
    (onRead : Address → Except ReadError (Read md) → Nat → IO Unit := fun _ _ _ => pure ())
    (spell : Ix.Kernel.Key md → String := toString)
    (tier : Option (TierHook σ (Checker md) md) := none)
    (allowUserAxioms : Bool := false) :
    IO (LoopOutcome Unit) := do
  let some slot0 := slots[0]? | throw (IO.userError "check-ixe: the pool needs a worker")
  -- phase A: what each record's rows will carry besides the verdict
  let times ← IO.mkRef (Std.HashMap.emptyWithCapacity addresses.size : Std.HashMap Address (Nat × Nat))
  let readErrors ← IO.mkRef ({} : Std.HashMap Address ReadError)
  let recOwner ← IO.mkRef ({} : Std.HashMap Address Address)
  let views ← IO.mkRef (Std.HashMap.emptyWithCapacity addresses.size : Std.HashMap Address RecordView)
  let tA ← IO.monoMsNow
  let st ← src.init
  let mut tierReads : Std.HashMap Address (Except ReadError (Ix.Kernel.Tier.TierDecl md) × Nat) := {}
  if let some th := tier then
    let knownTier := th.tierAddresses <|> src.tierAddresses
    let scanTier : Bool := match knownTier with
      | some ta => !ta.isEmpty
      | none => true
    if scanTier then
      for address in addresses do
        if let some ta := knownTier then
          unless ta.contains address do continue
        let r0 ← IO.monoNanosNow
        let res? ← IO.lazyPure fun _ => th.read st address
        if let some res := res? then
          let readMicros := ((← IO.monoNanosNow) - r0) / 1000
          tierReads := tierReads.insert address (res, readMicros)
          if let some v := src.view address then
            let v' := if res.isOk then let d := v.deps (); { v with deps := fun _ => d } else v
            views.modify (·.insert address v')
  let tierAddrSet : Std.HashSet Address :=
    tierReads.fold (fun s a _ => s.insert a) {}
  let tierHookA : Option (TierHook σ (Installer md) md) :=
    tier.map fun _ =>
      { read := fun _ a => (tierReads[a]?).map fun (res, _) => res.map fun _ => .defs .part []
        index := fun _ => Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
        tierAddresses := some tierAddrSet }
  let needDecls := tier.isSome && !tierReads.isEmpty
  let startInstaller : Installer md :=
    { pend := Array.mkEmpty addresses.size
      owners := Array.mkEmpty addresses.size
      installedLog := if needDecls then Array.mkEmpty addresses.size else #[] }
  let installed ← checkLoopWith src.view src.read src.commit st
    (Installer.stepRecord ev needDecls true allowUserAxioms) startInstaller
    names addresses skip
    (emit := fun row =>
      unless tierReads.contains row.address do
        times.modify (·.insert row.address (row.micros, row.readMicros)))
    (before := fun a => do slot0.set (some (a, ← IO.monoMsNow)))
    (after := slot0.set none)
    (progress := fun i o => progress i o.counts)
    (onRead := fun a reading micros => do
      if let .error e := reading then readErrors.modify (·.insert a e)
      onRead a reading micros)
    (tier := tierHookA)
    (onView := fun a v => do
      for r in v.recs do recOwner.modify (·.insert r a)
      views.modify (·.insert a v))
  let inst := installed.checker
  log s!"phase A: {installed.counts.toList} (accept: installed), {inst.pend.size} checks recorded, \
    {inst.fe.visibleBelow} constants, in {(← IO.monoMsNow) - tA} ms"
  -- phase B: the workers share the installed environment and the checks
  let tM ← IO.monoMsNow
  -- the memo state is only a cache; only the worker-shared inputs are marked
  -- persistent (`markPersistent` is `unsafe` because a persistent object is never freed)
  let fe := inst.fe
  let pend := inst.pend
  let owners := inst.owners
  let installErrors := inst.installErrors
  let installedDecls := inst.installedDecls
  let installedCount := inst.installedCount
  let installedLog := inst.installedLog
  let _ ← unsafe Runtime.markPersistent fe
  let _ ← unsafe Runtime.markPersistent pend
  let _ ← unsafe Runtime.markPersistent owners
  log s!"installed environment marked persistent in {(← IO.monoMsNow) - tM} ms"
  let tB ← IO.monoMsNow
  let table ← pool fe pend owners slots
  let failures := table.foldl (fun n (r, _) => if r.isSome then n + 1 else n) 0
  let summed := table.foldl (fun n (_, micros) => n + micros) 0
  log s!"phase B on {slots.size} workers: {(← IO.monoMsNow) - tB} ms wall, {summed / 1000} ms summed, \
    {failures} failed"
  -- the verdicts: a record's first failed check (in install order), else its
  -- install failure; and its checks' time
  let mut verdicts : Std.HashMap Address (Ix.Kernel.CheckError md) := {}
  let mut checkMicros : Std.HashMap Address Nat := Std.HashMap.emptyWithCapacity addresses.size
  for h : k in [0:table.size] do
    let (r, micros) := table[k]
    let some a := owners[k]? | continue
    checkMicros := checkMicros.insert a (checkMicros.getD a 0 + micros)
    if let some e := r then
      unless verdicts.contains a do verdicts := verdicts.insert a e
  for (a, e) in installErrors do
    unless verdicts.contains a do verdicts := verdicts.insert a e
  -- the rows: the loop again, over phase A's readings and the verdicts
  let times ← times.get
  let readErrors ← readErrors.get
  let recOwner ← recOwner.get
  let cachedViews ← views.get
  let rowMicros (row : Row) : Nat :=
    if row.outcome == "blocked" then 0
    else (times.getD row.address (0, 0)).1 + checkMicros.getD (recOwner.getD row.address row.address) 0
  let tierHookB : Option (TierHook Unit (Array Address) md) :=
    tier.map fun _ =>
      { read := fun _ a => (tierReads[a]?).map (·.1)
        index := fun ran =>
          checkedLogicalEnv fe failures installedDecls table ran installedCount installedLog
        tierAddresses := some tierAddrSet }
  let out ← checkLoopWith (fun a => cachedViews[a]? <|> src.view a)
    (fun (_ : Unit) a => match readErrors[a]? with
      | some e => .error e
      | none => .ok {})
    (fun _ _ _ => ()) ()
    (fun (ran : Array Address) a _ => (ran.push a, verdicts[a]?)) (Array.mkEmpty addresses.size)
    names addresses skip
    (emit := fun row =>
      match tierReads[row.address]? with
      | some (_, readMicros) =>
        emit { row with micros := if row.outcome == "blocked" then 0 else row.micros,
                        readMicros }
      | none =>
        emit { row with micros := rowMicros row,
                        readMicros := (times.getD row.address (0, 0)).2 })
    (spell := spell)
    (tier := tierHookB)
  return { checker := (), counts := out.counts, reasons := out.reasons, failed := out.failed }

/-- Compatibility count-pair API over the mode-generic pool. -/
def run {σ : Type} (src : LoopSource σ md) (ev : Ix.Kernel.Evidences md) (names : Address → Array String)
    (addresses : Array Address) (skip : Std.HashSet String) (slots : Array Slot)
    (emit : Row → IO Unit) (log : String → IO Unit)
    (progress : Nat → Std.HashMap String Nat → IO Unit := fun _ _ => pure ())
    (onRead : Address → Except ReadError (Read md) → Nat → IO Unit := fun _ _ _ => pure ())
    (spell : Ix.Kernel.Key md → String := toString)
    (tier : Option (TierHook σ (Checker md) md) := src.tierHook)
    (allowUserAxioms : Bool := false) :
    IO (Std.HashMap String Nat × Std.HashMap String Nat) := do
  let out ← runOutcome src ev names addresses skip slots emit log progress onRead spell tier allowUserAxioms
  return (out.counts, out.reasons)

end Benchmarks.Kernel.CheckIxePool
