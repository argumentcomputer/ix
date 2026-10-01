/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.ConLecheStep

/-! # Con-leche census over a compiled Ixon environment (untrusted)

The certified checker's census (the per-record counterpart of the intrinsic
kernel's `Benchmarks.Kernel.Census`, retired at L6): con-leche's verified
checker, read through the L4 Ixon reader
(`Ix.Kernel.ConLecheReader`): every primary record of an `.ixe`, in
dependency order (the Ixon prelude's records first), read into con-leche
declarations and installed and checked one record at a time by the
incremental step of `Benchmarks.Kernel.ConLecheStep` (`annotDeclStep`, then
`checkPendingList` on what it left pending), continuing past failures and
reporting the dependents of a failure as blocked. Reducibility hints are the
compiler's (`Env.anonHints`). Not a certified verdict:
`Ix.Ixon.ConLecheAdmission.checkBytes` is.

Rows are JSONL with the fields of `kernel-census` (`address, names, kind,
outcome, reason, micros, readMicros`; a blocked row's reason is its root's
address), so `scripts/census-report.py` reads them unchanged.

Usage: `kernel-census-cl <input.ixe> <output.jsonl> [limit]`. The watchdog
(`CENSUS_WATCH_MS`, default 60000; `CENSUS_WATCH_MB`, default 20000) appends a
runaway record's address to `<output>.runaway` and exits with code 3;
`CENSUS_SKIP` (comma-separated addresses) declines those records unchecked,
as for `kernel-census` and `scripts/census-guarded.sh`. `CENSUS_ROOTS`
(comma-separated Lean names, resolved through the environment's metadata)
restricts the run to the prelude and the dependency closure of those
constants; a `«n»` component is numeric, as the rows print it (the `0` of a
private name).

The loop (reading, stepping, rows) runs on a dedicated thread with a fresh
allocator heap, after the decoded inputs are marked persistent, as
con-leche's driver runs its check phase (`Main.lean`, `checkDeclsIO`);
`CENSUS_THREAD=0` runs it on the main thread, behind the decode, as before
T1. -/

namespace Benchmarks.Kernel.ConLecheCensus

open Ix.Kernel (ConstRef)
open Ix.Kernel.ConLecheReader
open Benchmarks.Kernel.ConLecheStep

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

def run (args : List String) : IO UInt32 := do
  let some options := parseArgs args
    | IO.eprintln "usage: kernel-census-cl <input.ixe> <output.jsonl> [limit]"; return 2
  let started ← IO.monoMsNow
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile options.input))
  let mut store : RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let names := reportNames env store
  let pins ← IO.ofExcept defaultPins
  let pre ← IO.ofExcept builtinPrelude
  let natPins ← IO.ofExcept builtinNatOpPins
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) pins pre hints.lookup
  IO.eprintln s!"census-cl: {s.store.size} records, {s.ordered.size} primary, {env.blobs.size} blobs, \
    {pins.names.size} pins, {s.cx.index.recs.size} recursors indexed, prelude {pre.ix.decls.size} declarations, \
    {hints.hints.size} hints ({hints.projAt.size} at projections), loaded in {(← IO.monoMsNow) - started} ms"
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
  let ordered ← match ← IO.getEnv "CENSUS_ROOTS" with
    | none => pure s.ordered
    | some list => do
      let mut roots : Array Address := pre.records.map (·.1)
      for n in (list.splitOn ",").filter (!·.isEmpty) do
        match env.named[Ix.Name.fromLeanName (rootName n)]? with
        | some named => roots := roots.push named.addr
        | none => IO.eprintln s!"census-cl: CENSUS_ROOTS: no constant {n}"
      pure (closure s.store s.extra roots)
  let total := match options.limit with | some n => min n ordered.size | none => ordered.size
  let loop := censusLoop s natPins (names.getD · #[]) (ordered.extract 0 total) skip
    (emit := fun row => do handle.putStrLn row.json.compress; handle.flush)
    (before := fun a => do checking.set (some (a, ← IO.monoMsNow)))
    (after := checking.set none)
    (progress := fun i o => do
      if i % 1000 == 0 then
        IO.eprintln s!"census-cl: {i}/{total} after {(← IO.monoMsNow) - started} ms; {o.counts.toList}; \
          RSS {(← statusKb "VmRSS:") / 1024} MB")
  -- The loop runs as con-leche's driver runs its check phase at `--jobs=1`
  -- (`Main.lean`, `checkDeclsIO`): on a dedicated thread, whose allocator
  -- heap is fresh (this thread's holds the decoded corpus and the
  -- temporaries of decoding it), with the read-only inputs marked
  -- persistent first, so that handing them to the thread does not mark
  -- the whole corpus multi-threaded (atomic reference counts) and the
  -- loop pays no reference counting on them at all. `CENSUS_THREAD=0`
  -- runs the loop on this thread instead.
  let out ← if (← IO.getEnv "CENSUS_THREAD") == some "0" then loop else do
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

end Benchmarks.Kernel.ConLecheCensus
