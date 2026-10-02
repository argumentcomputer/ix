import Benchmarks.Kernel.CheckIxeStep

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
the block's. Not a certified verdict: `Ix.Ixon.KernelAdmission.checkBytes`
is. -/

namespace Benchmarks.Kernel.CheckIxePool

open Ix.Kernel.IxonReader
open Benchmarks.Kernel.CheckIxeStep

/-! ## Phase A -/

/-- Phase A's step state: the installed environment, the memo state and the
fold position (as `Checker`'s), every recorded check with the record it
belongs to, and the records whose install failed. -/
structure Installer where
  fe : Ix.Kernel.FEnv := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
  cs : Ix.Kernel.Cached.CState := {}
  pos : Nat := 0
  pend : Array Ix.Kernel.Cached.PendingCheck := #[]
  owners : Array Address := #[]
  installErrors : Std.HashMap Address Ix.Kernel.CheckError := {}

instance : Inhabited Installer := ⟨{}⟩

/-- A record's declarations installed in order from a fresh accumulator of
recorded checks; the first failure ends it, rolled back as `Checker.step`
rolls back (the index rebuilt from the constants before the declaration,
the memo state reset), with the checks the declarations before it recorded. -/
def installDecls (pins : List Ix.Kernel.NatOpPinSet) :
    Nat → Ix.Kernel.FEnv → Array Ix.Kernel.Cached.PendingCheck → Ix.Kernel.Cached.CState →
      List Ix.Kernel.Declaration →
      Nat × Ix.Kernel.FEnv × Array Ix.Kernel.Cached.PendingCheck × Ix.Kernel.Cached.CState ×
        Option Ix.Kernel.CheckError
  | pos, fe, pend, cs, [] => (pos, fe, pend, cs, none)
  | pos, fe, pend, cs, d :: rest =>
    let before := fe.env
    let recorded := pend
    match Ix.Kernel.Cached.annotDeclStep .verified pins (pos, fe, pend) d cs with
    | .ok ((pos', fe', pend'), cs') => installDecls pins pos' fe' pend' cs' rest
    | .error (e, _) => (pos + 1, Ix.Kernel.mkFEnv before, recorded, {}, some e)

/-- Phase A's step: install a record's declarations, recording their checks. -/
def Installer.stepRecord (pins : List Ix.Kernel.NatOpPinSet) (c : Installer) (address : Address)
    (rd : Read) : Installer × Option Ix.Kernel.CheckError :=
  let ⟨fe, cs, pos, pend, owners, installErrors⟩ := c
  let (pos, fe, recorded, cs, err) := installDecls pins pos fe #[] cs rd.decls.toList
  let owners := owners ++ Array.replicate recorded.size address
  let pend := pend ++ recorded
  let installErrors := match err with
    | some e => installErrors.insert address e
    | none => installErrors
  (⟨fe, cs, pos, pend, owners, installErrors⟩, err)

/-! ## Phase B -/

/-- A watchdog slot: the record a worker is checking, and since when. -/
abbrev Slot := IO.Ref (Option (Address × Nat))

/-- Recorded check `k` against its prefix view, from a fresh memo state:
its failure, if any, and its time. -/
def checkOne (fe : Ix.Kernel.FEnv) (pend : Array Ix.Kernel.Cached.PendingCheck) (k : Nat) :
    IO (Option Ix.Kernel.CheckError × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => match pend[k]? with
    | some pc => match Ix.Kernel.Cached.checkPending .verified fe pc {} with
      | .ok _ => none
      | .error e => some e
    | none => some (.internal s!"check phase: no recorded check {k}")
  return (r, ((← IO.monoNanosNow) - t0) / 1000)

/-- A worker: claim one check at a time off `next` until it is past the
checks, with its watchdog slot set while it checks. -/
def worker (fe : Ix.Kernel.FEnv) (pend : Array Ix.Kernel.Cached.PendingCheck)
    (owners : Array Address) (next : IO.Ref Nat) (slot : Slot) :
    (fuel : Nat) → Array (Nat × Option Ix.Kernel.CheckError × Nat) →
      IO (Array (Nat × Option Ix.Kernel.CheckError × Nat))
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
def pool (fe : Ix.Kernel.FEnv) (pend : Array Ix.Kernel.Cached.PendingCheck)
    (owners : Array Address) (slots : Array Slot) :
    IO (Array (Option Ix.Kernel.CheckError × Nat)) := do
  let next ← IO.mkRef 0
  let mut tasks := #[]
  for slot in slots do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) (worker fe pend owners next slot (pend.size + 1) #[]))
  let mut table : Array (Option Ix.Kernel.CheckError × Nat) :=
    Array.replicate pend.size (some (.internal "check phase: check never ran"), 0)
  for t in tasks do
    for (k, r, micros) in ← IO.ofExcept (← IO.wait t) do
      table := table.set! k (r, micros)
  return table

/-! ## The run -/

/-- The environment check over `addresses` with phase B on one worker per
slot (`slots`, the watchdog's; at least one). Rows go to `emit`, in the
per-record check's order; stage lines go to `log`. Returns the outcome and
first-cause counts. -/
def run {σ : Type} (src : LoopSource σ) (pins : List Ix.Kernel.NatOpPinSet) (names : Address → Array String)
    (addresses : Array Address) (skip : Std.HashSet String) (slots : Array Slot)
    (emit : Row → IO Unit) (log : String → IO Unit)
    (progress : Nat → Std.HashMap String Nat → IO Unit := fun _ _ => pure ())
    (onRead : Address → Except ReadError Read → Nat → IO Unit := fun _ _ _ => pure ()) :
    IO (Std.HashMap String Nat × Std.HashMap String Nat) := do
  let some slot0 := slots[0]? | throw (IO.userError "check-ixe: the pool needs a worker")
  -- phase A: what each record's rows will carry besides the verdict
  let times ← IO.mkRef ({} : Std.HashMap Address (Nat × Nat))
  let readErrors ← IO.mkRef ({} : Std.HashMap Address ReadError)
  let recOwner ← IO.mkRef ({} : Std.HashMap Address Address)
  let tA ← IO.monoMsNow
  let st ← src.init
  let installed ← checkLoopWith src.view src.read src.commit st (Installer.stepRecord pins) {}
    names addresses skip
    (emit := fun row => times.modify (·.insert row.address (row.micros, row.readMicros)))
    (before := fun a => do slot0.set (some (a, ← IO.monoMsNow)))
    (after := slot0.set none)
    (progress := fun i o => progress i o.counts)
    (onRead := fun a reading micros => do
      if let .error e := reading then readErrors.modify (·.insert a e)
      if let some v := src.view a then
        for r in v.recs do recOwner.modify (·.insert r a)
      onRead a reading micros)
  let inst := installed.checker
  log s!"phase A: {installed.counts.toList} (accept: installed), {inst.pend.size} checks recorded, \
    {inst.fe.env.consts.length} constants, in {(← IO.monoMsNow) - tA} ms"
  -- phase B: the workers share the installed environment and the checks
  let tM ← IO.monoMsNow
  -- the memo state is only a cache; the rest is used to the end of the run
  -- (`markPersistent` is `unsafe` because a persistent object is never freed)
  let inst : Installer := { inst with cs := {} }
  let _ ← unsafe Runtime.markPersistent inst
  let fe := inst.fe
  let pend := inst.pend
  let owners := inst.owners
  let installErrors := inst.installErrors
  log s!"installed environment marked persistent in {(← IO.monoMsNow) - tM} ms"
  let tB ← IO.monoMsNow
  let table ← pool fe pend owners slots
  let failures := table.foldl (fun n (r, _) => if r.isSome then n + 1 else n) 0
  let summed := table.foldl (fun n (_, micros) => n + micros) 0
  log s!"phase B on {slots.size} workers: {(← IO.monoMsNow) - tB} ms wall, {summed / 1000} ms summed, \
    {failures} failed"
  -- the verdicts: a record's first failed check (in install order), else its
  -- install failure; and its checks' time
  let mut verdicts : Std.HashMap Address Ix.Kernel.CheckError := {}
  let mut checkMicros : Std.HashMap Address Nat := {}
  for ((r, micros), k) in table.zipIdx do
    let some a := owners[k]? | continue
    checkMicros := checkMicros.insert a (checkMicros.getD a 0 + micros)
    if let some e := r then
      unless verdicts.contains a do verdicts := verdicts.insert a e
  for (a, e) in installErrors.toList do
    unless verdicts.contains a do verdicts := verdicts.insert a e
  -- the rows: the loop again, over phase A's readings and the verdicts
  let times ← times.get
  let readErrors ← readErrors.get
  let recOwner ← recOwner.get
  let rowMicros (row : Row) : Nat :=
    if row.outcome == "blocked" then 0
    else (times.getD row.address (0, 0)).1 + checkMicros.getD (recOwner.getD row.address row.address) 0
  let out ← checkLoopWith src.view
    (fun (_ : Unit) a => match readErrors[a]? with
      | some e => .error e
      | none => .ok {})
    (fun _ _ _ => ()) ()
    (fun (_ : Unit) a _ => ((), verdicts[a]?)) ()
    names addresses skip
    (emit := fun row => emit { row with micros := rowMicros row,
                                        readMicros := (times.getD row.address (0, 0)).2 })
  return (out.counts, out.reasons)

end Benchmarks.Kernel.CheckIxePool
