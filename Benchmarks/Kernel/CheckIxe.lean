import Benchmarks.Kernel.CheckIxeReadCache
import Benchmarks.Kernel.CheckIxeStream
import Benchmarks.Kernel.CheckIxePool

/-! # Environment check of a compiled Ixon environment (untrusted)

The certified checker's environment check: the verified checker, read through
the Ixon reader
(`Ix.Kernel.IxonReader`): every primary record of an `.ixe`, in
dependency order (the Ixon prelude's records first), read into kernel
declarations and installed and checked one record at a time by the
incremental step of `Benchmarks.Kernel.CheckIxeStep` (`annotDeclStep`, then
`checkPendingList` on what it left pending), continuing past failures and
reporting the dependents of a failure as blocked. Reducibility hints are the
compiler's (`Env.anonHints`). Not a certified verdict:
`Ix.Ixon.KernelAdmission.checkBytes` is.

Rows are JSONL with the fields of `kernel-check-ixe` (`address, names, kind,
outcome, reason, micros, readMicros`; a blocked row's reason is its root's
address), so `kernel-check-ixe --report` and `--summary` read them unchanged.

Usage: `kernel-check-ixe [--load stream|eager] [--jobs <n>] <input.ixe>
<output.jsonl> [limit]`.

* `--load stream` (the default) streams the records
  (`Benchmarks.Kernel.CheckIxeStream`): the `.ixe` is loaded metadata-light,
  the setup is built over record skeletons, and a record is decoded in full
  only at its turn and its bytes dropped once it is read. `--load eager`
  decodes the whole environment up front (`Ixon.deEnv`) and keeps every
  record. The rows are the same; the streaming load holds less.
* `--jobs <n>` checks in two phases (`Benchmarks.Kernel.CheckIxePool`): every
  record installed in order, then the recorded checks on `n` worker threads.
  The rows are the per-record check's, each record's `micros` its install
  plus its checks.

The watchdog (`CHECK_IXE_WATCH_MS`, default 60000; `CHECK_IXE_WATCH_MB`,
default 20000) appends a runaway record's address to `<output>.runaway` and
exits with code 3; `CHECK_IXE_SKIP` (comma-separated addresses) declines
those records unchecked, as `kernel-check-ixe --guarded` does to rerun past
runaways. `CHECK_IXE_ROOTS` (comma-separated Lean names, resolved through the
environment's metadata) restricts the run to the prelude and the dependency
closure of those constants; a `«n»` component is numeric, as the rows print
it (the `0` of a private name).

The loop (reading, stepping, rows; with `--jobs`, both phases) runs on a
dedicated thread with a fresh allocator heap, after the read-only inputs are
marked persistent, as upstream con-leche's driver runs its check phase
(`Main.lean`, `checkDeclsIO`); `CHECK_IXE_THREAD=0` runs it on the main
thread.

`CHECK_IXE_READ_CACHE=<dir>` keeps a persistent read cache
(`Benchmarks.Kernel.CheckIxeReadCache`): a full-order run (no `CHECK_IXE_ROOTS`,
no limit) writes the run's plan (every record's view and reading, keyed by
the `.ixe`'s BLAKE3 hash and the reader version), and a later run over the
same bytes maps it instead of decoding the `.ixe`, building the setup and
reading; its rows are the same, with `readMicros` the cache lookup's. The
certified entry never uses it. -/

namespace Benchmarks.Kernel.CheckIxe

open Ix.Kernel (ConstRef)
open Ix.Kernel.IxonReader
open Benchmarks.Kernel.CheckIxeStep

/-- A dot-separated name as the rows print it: `«n»` is the numeric
component `n`, every other component a string. -/
def rootName (n : String) : Lean.Name :=
  (n.splitOn ".").foldl (init := .anonymous) fun acc c =>
    let inner := ((c.drop 1).dropEnd 1).toString
    if c.startsWith "«" && c.endsWith "»" && !inner.isEmpty && inner.all Char.isDigit then
      .num acc inner.toNat!
    else .str acc c

/-- How the `.ixe` is loaded. -/
inductive Load where
  | stream
  | eager

structure Options where
  input : System.FilePath
  output : System.FilePath
  limit : Option Nat := none
  load : Load := .stream
  jobs : Option Nat := none

def usage : String :=
  "usage: kernel-check-ixe [--load stream|eager] [--jobs <n>] <input.ixe> <output.jsonl> [limit]"

/-- The options; the flags may come before or after the positional arguments. -/
def parseArgs (args : List String) : Option Options :=
  go args .stream none #[]
where
  go : List String → Load → Option Nat → Array String → Option Options
    | "--load" :: "stream" :: rest, _, jobs, pos => go rest .stream jobs pos
    | "--load" :: "eager" :: rest, _, jobs, pos => go rest .eager jobs pos
    | "--jobs" :: n :: rest, load, _, pos => do
      let k ← n.toNat?
      guard (k ≥ 1)
      go rest load (some k) pos
    | a :: rest, load, jobs, pos => if a.startsWith "--" then none else go rest load jobs (pos.push a)
    | [], load, jobs, pos => match pos.toList with
      | [input, output] => some { input, output, load, jobs }
      | [input, output, limit] => do some { input, output, limit := some (← limit.toNat?), load, jobs }
      | _ => none

/-- The order of a run: the setup's, or with `CHECK_IXE_ROOTS` the closure of
those constants, resolved through the environment's names. -/
def orderOf (s : Setup) (named : Std.HashMap Ix.Name Ixon.Named) (pre : Prelude)
    (roots : Option String) : IO (Array Address) := do
  let some list := roots | return s.ordered
  let mut starts : Array Address := pre.records.map (·.1)
  for n in (list.splitOn ",").filter (!·.isEmpty) do
    match named[Ix.Name.fromLeanName (rootName n)]? with
    | some entry => starts := starts.push entry.addr
    | none => IO.eprintln s!"check-ixe: CHECK_IXE_ROOTS: no constant {n}"
  return closure s.store s.extra starts

/-- The watchdog, every half second until `running` is false: when the
longest-running check in the slots has run longer than `watchMs`, or the
process's resident memory exceeds `watchKb` while a check runs, it appends
that check's record to `runaway` and exits with code 3. -/
def watchdog (slots : Array CheckIxePool.Slot) (running : IO.Ref Bool) (watchMs watchKb : Nat)
    (runaway : String) : IO Unit := do
  while ← running.get do
    IO.sleep 500
    let mut oldest : Option (Address × Nat) := none
    for slot in slots do
      if let some (a, since) ← slot.get then
        if oldest.all (fun (_, s) => since < s) then oldest := some (a, since)
    if let some (address, since) := oldest then
      let elapsed := (← IO.monoMsNow) - since
      let rss ← statusKb "VmRSS:"
      if elapsed > watchMs || rss > watchKb then
        IO.eprintln s!"check-ixe: watchdog: {address} ran {elapsed} ms, RSS {rss / 1024} MB; exiting"
        let file ← IO.FS.Handle.mk runaway .append
        file.putStrLn (toString address)
        file.flush
        IO.Process.exit 3

/-- The setup line of a live run. -/
def setupLine (s : Setup) (blobs pins hints : Nat) (pre : Prelude) : String :=
  s!"{s.store.size} records, {s.ordered.size} primary, {blobs} blobs, {pins} pins, \
    {s.cx.index.recs.size} recursors indexed, prelude {pre.ix.decls.size} declarations, {hints} hints"

/-- Mark a live run's read-only inputs persistent before the loop's thread
takes them (`run`). `Runtime.markPersistent` is `unsafe` because a persistent
object is never freed; these live to the end of the run. -/
def markInputs (s : Setup) (names : Std.HashMap Address (Array String)) : IO Unit := do
  let _ ← unsafe Runtime.markPersistent s
  let _ ← unsafe Runtime.markPersistent names

/-- Counts of a run: outcomes and first causes. -/
abbrev Counts := Std.HashMap String Nat × Std.HashMap String Nat

def run (args : List String) : IO UInt32 := do
  let some options := parseArgs args
    | IO.eprintln usage; return 2
  let started ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile options.input
  let natPins ← IO.ofExcept builtinNatOpPins
  let rootsEnv ← IO.getEnv "CHECK_IXE_ROOTS"
  -- the persistent read cache (`CheckIxeReadCache`): full-order runs only
  let cacheDir ← IO.getEnv "CHECK_IXE_READ_CACHE"
  let cache : Option (System.FilePath × String) := do
    let dir ← cacheDir
    guard rootsEnv.isNone
    pure (CheckIxeReadCache.planPath dir bytes)
  let plan ← match cache with
    | some (path, ixe) => CheckIxeReadCache.load path ixe
    | none => pure none
  let skip : Std.HashSet String := match ← IO.getEnv "CHECK_IXE_SKIP" with
    | some list => (list.splitOn ",").foldl (fun set a => if a.isEmpty then set else set.insert a) {}
    | none => {}
  let watchMs := ((← IO.getEnv "CHECK_IXE_WATCH_MS").bind String.toNat?).getD 60000
  let watchKb := ((← IO.getEnv "CHECK_IXE_WATCH_MB").bind String.toNat?).getD 20000 * 1024
  let thread := (← IO.getEnv "CHECK_IXE_THREAD") != some "0"
  -- one watchdog slot per worker (the per-record check has one)
  let slot0 : CheckIxePool.Slot ← IO.mkRef none
  let others : Array CheckIxePool.Slot ←
    (Array.range (options.jobs.getD 1 - 1)).mapM fun _ => IO.mkRef (none : Option (Address × Nat))
  let slots := #[slot0] ++ others
  let running ← IO.mkRef true
  let _ ← IO.asTask (prio := .dedicated)
    (watchdog slots running watchMs watchKb (options.output.toString ++ ".runaway"))
  let handle ← IO.FS.Handle.mk options.output .write
  let emit := fun (row : Row) => do handle.putStrLn row.json.compress; handle.flush
  let log := fun (line : String) => do
    IO.eprintln s!"check-ixe: {line}; at {(← IO.monoMsNow) - started} ms, \
      RSS {(← statusKb "VmRSS:") / 1024} MB, peak {(← statusKb "VmHWM:") / 1024} MB"
  let limited := fun (a : Array Address) => match options.limit with
    | some n => a.extract 0 (min n a.size)
    | none => a
  -- the loop over a source: the per-record check, or with `--jobs` the pool
  let check {σ : Type} (src : LoopSource σ) (names : Address → Array String)
      (addresses : Array Address)
      (onRead : Address → Except ReadError Read → Nat → IO Unit) : IO Counts := do
    let total := addresses.size
    let progress := fun (i : Nat) (counts : Std.HashMap String Nat) => do
      if i % 1000 == 0 then
        IO.eprintln s!"check-ixe: {i}/{total} after {(← IO.monoMsNow) - started} ms; {counts.toList}; \
          RSS {(← statusKb "VmRSS:") / 1024} MB"
    match options.jobs with
    | some _ => CheckIxePool.run src natPins names addresses skip slots emit log progress onRead
    | none => do
      let st ← src.init
      let out ← checkLoopWith src.view src.read src.commit st (Checker.stepRecord natPins) {}
        names addresses skip emit
        (before := fun a => do slot0.set (some (a, ← IO.monoMsNow)))
        (after := slot0.set none)
        (progress := fun i o => progress i o.counts) (onRead := onRead)
      pure (out.counts, out.reasons)
  -- a full-order live run records its readings and writes its plan, on the
  -- loop's own thread: readings handed to another thread would be marked
  -- multi-threaded, and every reference count on them made atomic
  let record := cache.isSome && options.limit.isNone && rootsEnv.isNone
  let live {σ : Type} (s : Setup) (src : LoopSource σ) (names : Std.HashMap Address (Array String))
      (addresses : Array Address) : IO Counts := do
    let readings ← IO.mkRef (#[] : Array (Address × Except ReadError Read))
    let out ← check src (names.getD · #[]) addresses
      (fun a r _ => if record then readings.modify (·.push (a, r)) else pure ())
    if let some (path, ixe) := cache then
      if record then
        let t0 ← IO.monoMsNow
        let header := s!"check-ixe: {s.store.size} records, {s.ordered.size} primary"
        CheckIxeReadCache.save path (CheckIxeReadCache.ofRun s ixe header names (← readings.get))
        IO.eprintln s!"check-ixe: read cache {path} written in {(← IO.monoMsNow) - t0} ms"
    pure out
  -- The loop runs as upstream con-leche's driver runs its check phase
  -- (`Main.lean`, `checkDeclsIO`): on a dedicated thread, whose allocator
  -- heap is fresh (this thread's holds the decoded inputs and the
  -- temporaries of decoding them), with the read-only inputs marked
  -- persistent first, so that handing them to the thread does not mark
  -- them multi-threaded (atomic reference counts) and the loop pays no
  -- reference counting on them at all. A plan's objects are persistent
  -- already: they live in the mapped region.
  let onThread := fun (loop : IO Counts) => do
    if thread then IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) loop)) else loop
  let (counts, reasons) ← match plan with
    | some plan => do
      let path := (cache.map (·.1.toString)).getD ""
      IO.eprintln s!"{plan.header}; read cache {path}, mapped in {(← IO.monoMsNow) - started} ms"
      let names := plan.nameMap
      onThread (check plan.source (names.getD · #[]) (plan.addresses options.limit) fun _ _ _ => pure ())
    | none => do
      let pins ← IO.ofExcept defaultPins
      let pre ← IO.ofExcept builtinPrelude
      match options.load with
      | .eager => do
        let env ← IO.ofExcept (Ixon.deEnv bytes)
        let mut store : RecordStore := {}
        for (address, lazy) in env.consts.toList do
          store := store.insert address (← IO.ofExcept lazy.get)
        let names := reportNames env store
        let hints := Hints.ofStore store env.anonHints
        let s := setup store (env.blobs[·]?) pins pre hints.lookup
        log s!"eager load: {setupLine s env.blobs.size pins.names.size hints.hints.size pre}"
        let addresses := limited (← orderOf s env.named pre rootsEnv)
        if thread then markInputs s names
        onThread (live s s.source names addresses)
      | .stream => do
        let l ← CheckIxeStream.load bytes pins pre
        let s := l.setup
        let names := reportNames l.env s.store
        log s!"streaming load: {setupLine s l.env.blobs.size pins.names.size l.env.anonHints.size pre}"
        let addresses := limited (← orderOf s l.env.named pre rootsEnv)
        -- the setup and the names only: the records' windows go to the loop
        -- unmarked, so that they are freed once it has taken their bytes
        if thread then markInputs s names
        onThread (live s l.source names addresses)
  running.set false
  let ranked := reasons.toArray.qsort (fun a b => a.2 > b.2)
  IO.eprintln s!"check-ixe: done in {(← IO.monoMsNow) - started} ms; {counts.toList}"
  IO.eprintln s!"check-ixe: peak RSS {(← statusKb "VmHWM:") / 1024} MB"
  IO.eprintln "check-ixe: first-cause reasons by frequency:"
  for (reason, count) in ranked.extract 0 25 do
    IO.eprintln s!"  {count}\t{reason}"
  return 0

end Benchmarks.Kernel.CheckIxe
