/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.CheckIxeReadCache

/-! # Con-leche census over a compiled Ixon environment (untrusted)

The certified checker's census: con-leche's verified checker, read through
the Ixon reader
(`Ix.Kernel.IxonReader`): every primary record of an `.ixe`, in
dependency order (the Ixon prelude's records first), read into con-leche
declarations and installed and checked one record at a time by the
incremental step of `Benchmarks.Kernel.CheckIxeStep` (`annotDeclStep`, then
`checkPendingList` on what it left pending), continuing past failures and
reporting the dependents of a failure as blocked. Reducibility hints are the
compiler's (`Env.anonHints`). Not a certified verdict:
`Ix.Ixon.KernelAdmission.checkBytes` is.

Rows are JSONL with the fields of `kernel-check-ixe` (`address, names, kind,
outcome, reason, micros, readMicros`; a blocked row's reason is its root's
address), so `scripts/census-report.py` reads them unchanged.

Usage: `kernel-check-ixe <input.ixe> <output.jsonl> [limit]`. The watchdog
(`CENSUS_WATCH_MS`, default 60000; `CENSUS_WATCH_MB`, default 20000) appends a
runaway record's address to `<output>.runaway` and exits with code 3;
`CENSUS_SKIP` (comma-separated addresses) declines those records unchecked,
as for `kernel-check-ixe` and `scripts/census-guarded.sh`. `CENSUS_ROOTS`
(comma-separated Lean names, resolved through the environment's metadata)
restricts the run to the prelude and the dependency closure of those
constants; a `«n»` component is numeric, as the rows print it (the `0` of a
private name).

The loop (reading, stepping, rows) runs on a dedicated thread with a fresh
allocator heap, after the decoded inputs are marked persistent, as
con-leche's driver runs its check phase (`Main.lean`, `checkDeclsIO`);
`CENSUS_THREAD=0` runs it on the main thread, behind the decode, as before
T1.

`CENSUS_READ_CACHE=<dir>` keeps a persistent read cache
(`Benchmarks.Kernel.CheckIxeReadCache`): a full-order run (no `CENSUS_ROOTS`,
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

structure Options where
  input : System.FilePath
  output : System.FilePath
  limit : Option Nat := none

def parseArgs : List String → Option Options
  | [input, output] => some { input, output }
  | [input, output, limit] => do some { input, output, limit := some (← limit.toNat?) }
  | _ => none

/-- The census loop's inputs: from a live setup, or from a read-cache plan. -/
inductive Source where
  | live (env : Ixon.Env) (s : Setup) (names : Std.HashMap Address (Array String))
      (ordered : Array Address)
  | planned (plan : CheckIxeReadCache.Plan)

def run (args : List String) : IO UInt32 := do
  let some options := parseArgs args
    | IO.eprintln "usage: kernel-check-ixe <input.ixe> <output.jsonl> [limit]"; return 2
  let started ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile options.input
  let natPins ← IO.ofExcept builtinNatOpPins
  let rootsEnv ← IO.getEnv "CENSUS_ROOTS"
  -- the persistent read cache (`CheckIxeReadCache`): full-order runs only
  let cacheDir ← IO.getEnv "CENSUS_READ_CACHE"
  let cache : Option (System.FilePath × String) := do
    let dir ← cacheDir
    guard rootsEnv.isNone
    pure (CheckIxeReadCache.planPath dir bytes)
  let plan ← match cache with
    | some (path, ixe) => CheckIxeReadCache.load path ixe
    | none => pure none
  let source ← match plan with
    | some plan =>
      let path := (cache.map (·.1.toString)).getD ""
      IO.eprintln s!"{plan.header}; read cache {path}, mapped in {(← IO.monoMsNow) - started} ms"
      pure (Source.planned plan)
    | none => do
      let env ← IO.ofExcept (Ixon.deEnv bytes)
      let mut store : RecordStore := {}
      for (address, lazy) in env.consts.toList do
        store := store.insert address (← IO.ofExcept lazy.get)
      let names := reportNames env store
      let pins ← IO.ofExcept defaultPins
      let pre ← IO.ofExcept builtinPrelude
      let hints := Hints.ofStore store env.anonHints
      let s := setup store (env.blobs[·]?) pins pre hints.lookup
      let header := s!"census-cl: {s.store.size} records, {s.ordered.size} primary, {env.blobs.size} blobs, \
        {pins.names.size} pins, {s.cx.index.recs.size} recursors indexed, prelude {pre.ix.decls.size} declarations, \
        {hints.hints.size} hints ({hints.projAt.size} at projections)"
      IO.eprintln s!"{header}, loaded in {(← IO.monoMsNow) - started} ms"
      let ordered ← match rootsEnv with
        | none => pure s.ordered
        | some list => do
          let mut roots : Array Address := pre.records.map (·.1)
          for n in (list.splitOn ",").filter (!·.isEmpty) do
            match env.named[Ix.Name.fromLeanName (rootName n)]? with
            | some named => roots := roots.push named.addr
            | none => IO.eprintln s!"census-cl: CENSUS_ROOTS: no constant {n}"
          pure (closure s.store s.extra roots)
      pure (Source.live env s names ordered)
  let skip : Std.HashSet String := match ← IO.getEnv "CENSUS_SKIP" with
    | some list => (list.splitOn ",").foldl (fun set a => if a.isEmpty then set else set.insert a) {}
    | none => {}
  let watchMs := ((← IO.getEnv "CENSUS_WATCH_MS").bind String.toNat?).getD 60000
  let watchKb := ((← IO.getEnv "CENSUS_WATCH_MB").bind String.toNat?).getD 20000 * 1024
  let checking : IO.Ref (Option (Address × Nat)) ← IO.mkRef none
  let running ← IO.mkRef true
  let runaway := options.output.toString ++ ".runaway"
  let _ ← IO.asTask (prio := .dedicated) do
    while ← running.get do
      IO.sleep 500
      if let some (address, since) ← checking.get then
        let elapsed := (← IO.monoMsNow) - since
        let rss ← statusKb "VmRSS:"
        if elapsed > watchMs || rss > watchKb then
          IO.eprintln s!"census-cl: watchdog: {address} ran {elapsed} ms, RSS {rss / 1024} MB; exiting"
          let file ← IO.FS.Handle.mk runaway .append
          file.putStrLn (toString address)
          file.flush
          IO.Process.exit 3
  let handle ← IO.FS.Handle.mk options.output .write
  let emit := fun (row : Row) => do handle.putStrLn row.json.compress; handle.flush
  let before := fun a => do checking.set (some (a, ← IO.monoMsNow))
  let after := checking.set none
  let progressAt (total : Nat) := fun (i : Nat) (o : Outcome) => do
    if i % 1000 == 0 then
      IO.eprintln s!"census-cl: {i}/{total} after {(← IO.monoMsNow) - started} ms; {o.counts.toList}; \
        RSS {(← statusKb "VmRSS:") / 1024} MB"
  -- a full-order live run records its readings and writes its plan, on the
  -- loop's own thread: readings handed to another thread would be marked
  -- multi-threaded, and every reference count on them made atomic
  let record := cache.isSome && options.limit.isNone && rootsEnv.isNone
  let loop : IO Outcome := match source with
    | .planned plan =>
      let total := match options.limit with
        | some n => min n plan.records.size
        | none => plan.records.size
      CheckIxeReadCache.checkLoopPlan plan natPins options.limit skip emit before after (progressAt total)
    | .live _ s names ordered => do
      let total := match options.limit with | some n => min n ordered.size | none => ordered.size
      let readings ← IO.mkRef (#[] : Array (Address × Except ReadError Read))
      let out ← checkLoop s natPins (names.getD · #[]) (ordered.extract 0 total) skip emit before after
        (progressAt total)
        (onRead := fun a r _ => if record then readings.modify (·.push (a, r)) else pure ())
      if let some (path, ixe) := cache then
        if record then
          let t0 ← IO.monoMsNow
          let header := s!"census-cl: {s.store.size} records, {s.ordered.size} primary"
          CheckIxeReadCache.save path (CheckIxeReadCache.ofRun s ixe header names (← readings.get))
          IO.eprintln s!"census-cl: read cache {path} written in {(← IO.monoMsNow) - t0} ms"
      pure out
  -- The loop runs as con-leche's driver runs its check phase at `--jobs=1`
  -- (`Main.lean`, `checkDeclsIO`): on a dedicated thread, whose allocator
  -- heap is fresh (this thread's holds the decoded corpus and the
  -- temporaries of decoding it), with the read-only inputs marked
  -- persistent first, so that handing them to the thread does not mark
  -- the whole corpus multi-threaded (atomic reference counts) and the
  -- loop pays no reference counting on them at all. `CENSUS_THREAD=0`
  -- runs the loop on this thread instead. A plan's objects are persistent
  -- already: they live in the mapped region.
  let out ← if (← IO.getEnv "CENSUS_THREAD") == some "0" then loop else do
    if let .live _ s names _ := source then
      let _ ← unsafe Runtime.markPersistent s
      let _ ← unsafe Runtime.markPersistent names
    IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) loop))
  running.set false
  let ranked := out.reasons.toArray.qsort (fun a b => a.2 > b.2)
  IO.eprintln s!"census-cl: done in {(← IO.monoMsNow) - started} ms; {out.counts.toList}"
  IO.eprintln s!"census-cl: peak RSS {(← statusKb "VmHWM:") / 1024} MB"
  IO.eprintln "census-cl: first-cause reasons by frequency:"
  for (reason, count) in ranked.extract 0 25 do
    IO.eprintln s!"  {count}\t{reason}"
  return 0

end Benchmarks.Kernel.CheckIxe
