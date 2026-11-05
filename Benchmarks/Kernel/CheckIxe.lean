import Benchmarks.Kernel.CheckIxeReadCache
import Benchmarks.Kernel.CheckIxeStream
import Benchmarks.Kernel.CheckIxePool
import Benchmarks.Kernel.CheckIxeMeta
import Ix.KernelCheck.Binding
import Ix.RoleBinding.UserAxioms

/-! # Environment check of a compiled Ixon environment (untrusted)

The certified checker's environment check: the verified checker, read through
the Ixon reader
(`Ix.Kernel.Reader`): every primary record of an `.ixe`, in
dependency order (the Ixon prelude's records first), read into kernel
declarations and installed and checked one record at a time by the
incremental step of `Benchmarks.Kernel.CheckIxeStep` (`annotDeclStep`, then
`checkPendingList` on what it left pending), continuing past failures and
reporting the dependents of a failure as blocked. Reducibility hints are the
compiler's (`Env.anonHints`). Not a certified verdict:
`Ix.Kernel.Admission.checkBytes` is.

Rows are JSONL with the fields of `kernel-check-ixe` (`address, names, kind,
outcome, reason, micros, readMicros`; a blocked row's reason is its root's
address), so `kernel-check-ixe --report` and `--summary` read them unchanged.
The verdict is the `.anon` run's; a checker failure's reason is rendered by
`.meta`: its keys spelled with the names the `.ixe`'s metadata
gives them and their addresses, `Nat.add@a1b2c3d4` (`Reader.spellWith` over
`CheckIxeMeta.displayTable`; a run from the read cache spells them as
`Key.toName` does). `kernel-check-ixe --meta` runs the check at `.meta` too
and compares the two (`Benchmarks.Kernel.CheckIxeMeta`).

Usage: `kernel-check-ixe [--load stream|eager] [--jobs <n>] [--allow-user-axioms]
<input.ixe> <output.jsonl> [limit]`.

* `--load stream` (the default) uses the skeleton/pre-read loader
  (`Benchmarks.Kernel.CheckIxeStream`): the `.ixe` is loaded metadata-light
  (`Ixon.deEnvAnon`), parallel chunks decode each record to build the
  skeleton store for `setup` and pre-read context-free records into `Read`
  entries (retaining decoded `Ixon.Constant`s only for context-dependent or
  tier records), and each pre-read or decoded entry is dropped as the check
  loop consumes it. `--load eager` decodes the whole environment with full
  metadata up front (`Ixon.deEnv`) and keeps every full record in the store.
  The rows are the same.
* `--jobs <n>` checks in two phases (`Benchmarks.Kernel.CheckIxePool`): every
  record installed in order, then the recorded checks on `n` worker threads.
  The rows are the per-record check's, each record's `micros` its install
  plus its checks.
* `--allow-user-axioms` admits safe axioms beyond Lean's standard three
  (`Key.isCustomAxiomEligible`) on every path: streamed, eager, pooled and from
  the read cache. Without it the check is strict and such an axiom declines.
  The artifact's role binding must pass the kernel's role-table check for user
  axioms (`Admission.admitAxiomPolicy .allowUser`: `sorryAx`, `propext` and
  `Classical.choice` bound; `Ix.RoleBinding.UserAxioms.requireAxiomRoles`),
  which the per-record step never reaches, so it runs once before any path, or
  the run is refused with exit code 2; an accepted run lists the user axioms it
  admitted (`CONDITIONAL on K user axioms`) after its counts.

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
open Ix.Kernel.Reader
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
  input : System.FilePath := ⟨""⟩
  output : System.FilePath := ⟨""⟩
  limit : Option Nat := none
  load : Load := .stream
  jobs : Option Nat := none
  allowUserAxioms : Bool := false

def usage : String :=
  "usage: kernel-check-ixe [--load stream|eager] [--jobs <n>] [--allow-user-axioms] \
   <input.ixe> <output.jsonl> [limit]"

/-- The options; the flags may come before or after the positional arguments. -/
def parseArgs (args : List String) : Option Options :=
  go args {} #[]
where
  go : List String → Options → Array String → Option Options
    | "--load" :: "stream" :: rest, o, pos => go rest { o with load := .stream } pos
    | "--load" :: "eager" :: rest, o, pos => go rest { o with load := .eager } pos
    | "--jobs" :: n :: rest, o, pos => do
      let k ← n.toNat?
      guard (k ≥ 1)
      go rest { o with jobs := some k } pos
    | "--allow-user-axioms" :: rest, o, pos => go rest { o with allowUserAxioms := true } pos
    | a :: rest, o, pos => if a.startsWith "--" then none else go rest o (pos.push a)
    | [], o, pos => match pos.toList with
      | [input, output] => some { o with input, output }
      | [input, output, limit] => do some { o with input, output, limit := some (← limit.toNat?) }
      | _ => none

/-- The order of a run: the setup's, or with `CHECK_IXE_ROOTS` the closure of
those constants, resolved through the environment's names. -/
def orderOf (s : Setup) (named : Std.HashMap Ix.Name Ixon.Named) (pre : Prelude .anon)
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
    (runaway : String) (onExit : IO Unit := pure ()) : IO Unit := do
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
        onExit
        let file ← IO.FS.Handle.mk runaway .append
        file.putStrLn (toString address)
        file.flush
        IO.Process.exit 3

/-- The setup line of a live run. -/
def setupLine (s : Setup) (blobs roles hints : Nat) (pre : Prelude .anon) : String :=
  s!"{s.store.size} records, {s.ordered.size} primary, {blobs} blobs, {roles} roles bound, \
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
  -- `--allow-user-axioms` is refused up front, whichever path runs, unless the
  -- artifact's binding passes the kernel's role-table check for user axioms
  -- (`admitAxiomPolicy .allowUser`): the per-record step
  -- (`annotDeclStepWithUserAxioms`) never reaches admission
  if options.allowUserAxioms then
    let binding := (← IO.ofExcept (Ixon.deEnvAnon bytes)).roleBinding
    if let .error e := Ix.RoleBinding.UserAxioms.requireAxiomRoles binding then
      IO.eprintln s!"check-ixe: --allow-user-axioms: {e}"
      return 2
  -- the user axioms the run read (with their names) and the records it accepted
  let userAxioms ← IO.mkRef ({} : Std.HashMap Address (Array String))
  let accepted ← IO.mkRef ({} : Std.HashSet Address)
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
  let handle ← IO.FS.Handle.mk options.output .write
  let emitBuf ← IO.mkRef ("", 0)
  let flushEmit : IO Unit := do
    let (buf, n) ← emitBuf.modifyGet fun s => (s, ("", 0))
    if n > 0 then handle.putStr buf
    handle.flush
  let _ ← IO.asTask (prio := .dedicated)
    (watchdog slots running watchMs watchKb (options.output.toString ++ ".runaway") flushEmit)
  let emit := fun (row : Row) => do
    if options.allowUserAxioms && row.outcome == "accept" then accepted.modify (·.insert row.address)
    let line := row.jsonLine ++ "\n"
    let flushNow? ← emitBuf.modifyGet fun (buf, n) =>
      let buf' := buf ++ line
      let n' := n + 1
      if n' >= 512 then (some buf', ("", 0)) else (none, (buf', n'))
    if let some chunk := flushNow? then
      handle.putStr chunk
      handle.flush
  let log := fun (line : String) => do
    IO.eprintln s!"check-ixe: {line}; at {(← IO.monoMsNow) - started} ms, \
      RSS {(← statusKb "VmRSS:") / 1024} MB, peak {(← statusKb "VmHWM:") / 1024} MB"
  let limited := fun (a : Array Address) => match options.limit with
    | some n => a.extract 0 (min n a.size)
    | none => a
  -- the loop over a source: the per-record check, or with `--jobs` the pool;
  -- strict unless `--allow-user-axioms`, on every source (streamed, eager or
  -- the read cache's plan)
  let allowUserAxioms := options.allowUserAxioms
  let check {σ : Type} (ev : Ix.Kernel.Evidences .anon) (src : LoopSource σ) (names : Address → Array String)
      (addresses : Array Address)
      (onRead : Address → Except ReadError (Read .anon) → Nat → IO Unit)
      (spell : Ix.Kernel.Key .anon → String := toString) : IO Counts := do
    let onRead := fun (a : Address) (r : Except ReadError (Read .anon)) (n : Nat) => do
      if allowUserAxioms then
        if let .ok rd := r then
          for x in Ix.RoleBinding.UserAxioms.ofDecls rd.decls.toList do
            userAxioms.modify (·.insert x (names x))
      onRead a r n
    let total := addresses.size
    let progress := fun (i : Nat) (counts : Std.HashMap String Nat) => do
      if i % 1000 == 0 then
        IO.eprintln s!"check-ixe: {i}/{total} after {(← IO.monoMsNow) - started} ms; {counts.toList}; \
          RSS {(← statusKb "VmRSS:") / 1024} MB"
    match options.jobs with
    | some _ =>
      CheckIxePool.run src ev names addresses skip slots emit log progress onRead spell
        (tier := if cacheDir.isNone then src.tierHook else none)
        (allowUserAxioms := allowUserAxioms)
    | none => do
      let st ← src.init
      let out ← checkLoopWith src.view src.read src.commit st
        (Checker.stepRecordWithUserAxioms ev allowUserAxioms) {}
        names addresses skip emit
        (before := fun a => do slot0.set (some (a, ← IO.monoMsNow)))
        (after := slot0.set none)
        (progress := fun i o => progress i o.counts) (onRead := onRead) (spell := spell)
        (tier := if cacheDir.isNone then src.tierHook else none)
      pure (out.counts, out.reasons)
  -- a full-order live run records its readings and writes its plan, on the
  -- loop's own thread: readings handed to another thread would be marked
  -- multi-threaded, and every reference count on them made atomic
  let record := cache.isSome && options.limit.isNone && rootsEnv.isNone
  let live {σ : Type} (s : Setup) (src : LoopSource σ) (names : Std.HashMap Address (Array String))
      (addresses : Array Address) (display : Thunk (DisplayTable .anon)) : IO Counts := do
    let readings ← IO.mkRef (#[] : Array (Address × Except ReadError (Read .anon)))
    let out ← check s.evidence src (names.getD · #[]) addresses
      (fun a r _ => if record then readings.modify (·.push (a, r)) else pure ())
      (spell := fun k => spellWith display.get k)
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
      onThread (check plan.evidence plan.source (names.getD · #[]) (plan.addresses options.limit)
        fun _ _ _ => pure ())
    | none => do
      match options.load with
      | .eager => do
        let env ← IO.ofExcept (Ixon.deEnv bytes)
        let (table, pre) ← IO.ofExcept (Ix.KernelCheck.Binding.context env)
        let mut store : RecordStore := Std.HashMap.emptyWithCapacity env.consts.size
        for (address, lazy) in env.consts do
          store := store.insert address (← IO.ofExcept lazy.get)
        let names := reportNames env store
        let hints := Hints.ofStore store env.anonHints
        let s := setup store (env.blobs[·]?) table pre hints.lookup
        log s!"eager load: {setupLine s env.blobs.size s.cx.roles.names.size hints.hints.size pre}"
        let addresses := limited (← orderOf s env.named pre rootsEnv)
        if thread then markInputs s names
        onThread (live s s.source names addresses
          (Thunk.mk fun () => CheckIxeMeta.displayTable env s.cx))
      | .stream => do
        let contextEnv ← IO.ofExcept (Ixon.deEnvAnon bytes)
        let (table, pre) ← IO.ofExcept (Ix.KernelCheck.Binding.context contextEnv)
        let l ← CheckIxeStream.loadEnv contextEnv table pre
        let s := l.setup
        let names := reportNames l.env s.store
        log s!"streaming load: {setupLine s l.env.blobs.size s.cx.roles.names.size l.env.anonHints.size pre}"
        let addresses := limited (← orderOf s l.env.named pre rootsEnv)
        -- the setup and the names only: the records' windows go to the loop
        -- unmarked, so that they are freed once it has taken their bytes
        if thread then markInputs s names
        onThread (live s l.source names addresses
          (Thunk.mk fun () => CheckIxeMeta.displayTable l.env s.cx))
  running.set false
  flushEmit
  handle.flush
  let ranked := reasons.toArray.qsort (fun a b => a.2 > b.2)
  IO.eprintln s!"check-ixe: done in {(← IO.monoMsNow) - started} ms; {counts.toList}"
  IO.eprintln s!"check-ixe: peak RSS {(← statusKb "VmHWM:") / 1024} MB"
  IO.eprintln "check-ixe: first-cause reasons by frequency:"
  for (reason, count) in ranked.extract 0 25 do
    IO.eprintln s!"  {count}\t{reason}"
  if allowUserAxioms then
    let accepted ← accepted.get
    let admitted := (← userAxioms.get).toArray.filter (accepted.contains ·.1)
      |>.qsort (fun a b => compare a.1 b.1 == .lt)
    IO.eprintln s!"check-ixe: CONDITIONAL on {admitted.size} user axioms:"
    for (address, names) in admitted do
      IO.eprintln s!"  {address} {" | ".intercalate names.toList}"
  return 0

end Benchmarks.Kernel.CheckIxe
