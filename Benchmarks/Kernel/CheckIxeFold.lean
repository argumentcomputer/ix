/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.CheckIxeStep
import Ix.Ixon.KernelAdmission

/-! # The batch fold over a census's accepted records (untrusted harness)

`kernel-check-ixe --fold <input.ixe> <output.jsonl>` measures con-leche's
declaration fold `Ix.Kernel.Cached.checkDecls` run ONCE over every record the
per-record census would accept, as con-leche's own driver (`Main.lean`,
`checkDeclsIO`) runs it over a lean4export stream: phase A
(`annotDeclStep` over all declarations), then phase B (`checkPending` of
every recorded declaration against its prefix view, each from a fresh memo
state). It is the comparison point for the census's per-record step
(`CheckIxeStep.Checker.step`: phase A on one declaration, then phase B on
what that step left pending).

The records: the census order (`CheckIxeStep.setup`); a record the reader
declines or fails, and every record that depends on one, is left out, as are
the recursor and projection records of left-out blocks. What remains is read
by the certified entry's own reader path (`KernelAdmission.readStream`,
with the prelude) and prepared by `Frontend.preparePrelude`, so the fold runs
over exactly the declarations `KernelAdmission.checkConstants` would check.

Phase B runs as `Main.lean` runs it at `--jobs=1`: on a dedicated thread (a
fresh allocator heap), after marking the installed environment and the
pending checks persistent (the phase-boundary mark).

Rows (JSONL): one per phase-B record, `{name, kind, micros}` (the check and
the release of its memo state, as `Cached.checkRecord` times them), plus a
summary on stderr: reading, phase A, phase B (sum of the per-record times and
wall) and the total. Knobs (environment): `FOLD_THREAD=0` runs phase B on the
main thread, `FOLD_PERSIST=0` skips the mark, `FOLD_SHARE=1` runs
`ShareCommon.shareCommon'` over all prepared declarations before phase A
(corpus-wide sharing of every subterm, name and level), and
`FOLD_READSTATS=1` only reports the reader's per-reference work (node and
reference counts, the time of `resolve`, `Ctx.nameOf` and `keyName` over
every reference-table entry). -/

namespace Benchmarks.Kernel.CheckIxeFold

open Ix.Kernel (ConstRef)
open Ix.Kernel.IxonReader
open Benchmarks.Kernel.CheckIxeStep

/-- The records the census would accept or check (in census order), and
every recursor and projection record of their blocks. -/
def acceptedRecords (s : Setup) : Array (Address × Ixon.Constant) × Nat := Id.run do
  let mut st : State := {}
  let mut failed : Std.HashSet Address := {}
  let mut consumed : Std.HashSet Address := {}
  let mut out : Array (Address × Ixon.Constant) := #[]
  let mut dropped := 0
  for address in s.ordered do
    if consumed.contains address then continue
    let some source := s.store[address]? | continue
    let recs := recursorRecords s.cx.index address
    for r in recs do consumed := consumed.insert r
    match readRecord s.cx st address source with
    | .error _ =>
      failed := failed.insert address
      dropped := dropped + 1
    | .ok rd =>
      st := st.commit rd
      let deps := dependencies s.store s.cx.index s.extra address source
      if deps.any failed.contains then
        failed := failed.insert address
        dropped := dropped + 1
      else
        out := out.push (address, source)
        for r in recs do
          if let some c := s.store[r]? then out := out.push (r, c)
  -- projection records of the kept blocks
  let kept : Std.HashSet Address := out.foldl (fun acc (a, _) => acc.insert a) {}
  let mut projs : Array (Address × Ixon.Constant) := #[]
  for (a, c) in s.store.toArray do
    let o := owner a c
    if o != a && kept.contains o && !kept.contains a then projs := projs.push (a, c)
  projs := projs.qsort (fun x y => x.1.cmpBytes y.1 == .lt)
  return (out ++ projs, dropped)

def kindWord : Ix.Kernel.Cached.PendingCheck → String
  | pc => pc.vg.kind.word

def percentile (xs : Array Nat) (p : Nat) : Nat :=
  if xs.isEmpty then 0 else
    let s := xs.qsort (· < ·)
    s[min (s.size - 1) (s.size * p / 100)]!

/-- Phase B over `pend`, one record at a time, each timed with the release
of its memo state. -/
def phaseB (fe : Ix.Kernel.FEnv) (pend : Array Ix.Kernel.Cached.PendingCheck) :
    IO (Array Nat × Option (Ix.Kernel.CheckError × Nat)) := do
  let mut times : Array Nat := Array.mkEmpty pend.size
  for pc in pend do
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure fun _ => match Ix.Kernel.Cached.checkPending .verified fe pc {} with
      | .ok _ => none
      | .error e => some e
    let t1 ← IO.monoNanosNow
    times := times.push ((t1 - t0) / 1000)
    if let some e := r then return (times, some (e, pc.pos))
  return (times, none)

/-- Node counts of a record's expressions as the reader converts them (each
sharing entry once, then the top-level expressions): all nodes, `ref`/`prj`
nodes. -/
def nodeCounts (c : Ixon.Constant) : Nat × Nat :=
  let exprs : Array Ixon.Expr := c.sharing ++ match c.info with
    | .defn d => #[d.typ, d.value]
    | .recr r => #[r.typ] ++ r.rules.map (·.rhs)
    | .axio a => #[a.typ]
    | .quot q => #[q.typ]
    | .muts ms => ms.flatMap fun
      | .defn d => #[d.typ, d.value]
      | .indc i => #[i.typ] ++ i.ctors.map (·.typ)
      | .recr r => #[r.typ] ++ r.rules.map (·.rhs)
    | _ => #[]
  exprs.foldl go (0, 0)
where
  go (acc : Nat × Nat) : Ixon.Expr → Nat × Nat
    | .ref .. => (acc.1 + 1, acc.2 + 1)
    | .prj _ _ v => go (acc.1 + 1, acc.2 + 1) v
    | .app f a => go (go (acc.1 + 1, acc.2) f) a
    | .lam _ t b => go (go (acc.1 + 1, acc.2) t) b
    | .all _ _ t b => go (go (acc.1 + 1, acc.2) t) b
    | .letE _ t v b => go (go (go (acc.1 + 1, acc.2) t) v) b
    | _ => (acc.1 + 1, acc.2)

/-- What the reader's per-reference work costs. The reader resolves and names
a reference at every `ref`/`prj` node it converts; this reports the node and
reference counts of the kept records, and the time of `resolve`, of
`Ctx.nameOf` (a lookup in `Ctx.keys` since T1-4) and of `keyName` (what
`nameOf` spelled at every occurrence before) over every reference-table
entry once. -/
def readStats (s : Setup) (records : Array (Address × Ixon.Constant)) : IO Unit := do
  let mut nodes := 0
  let mut refNodes := 0
  let mut tableRefs := 0
  for (_, c) in records do
    let (n, r) := nodeCounts c
    nodes := nodes + n
    refNodes := refNodes + r
    tableRefs := tableRefs + c.refs.size
  IO.eprintln s!"stats: {records.size} records, {nodes} expression nodes as read, {refNodes} ref/prj \
    nodes, {tableRefs} reference-table entries"
  let t0 ← IO.monoNanosNow
  let resolved ← IO.lazyPure fun _ => records.foldl (fun acc (_, c) =>
    c.refs.foldl (fun acc a => match resolve s.cx.store a with
      | some r => acc.push r
      | none => acc) acc) (#[] : Array (ConstRef Address))
  let t1 ← IO.monoNanosNow
  let names ← IO.lazyPure fun _ => resolved.foldl (fun n r => n + (s.cx.nameOf r).hashData.toNat % 2) 0
  let t2 ← IO.monoNanosNow
  let keys ← IO.lazyPure fun _ => resolved.foldl (fun n r => n + (keyName r).hashData.toNat % 2) 0
  let t3 ← IO.monoNanosNow
  IO.eprintln s!"stats: resolve over {resolved.size} table entries {(t1 - t0) / 1000000} ms; \
    nameOf {(t2 - t1) / 1000000} ms; keyName {(t3 - t2) / 1000000} ms ({names + keys} odd)"

def run (args : List String) : IO UInt32 := do
  let [input, output] := args
    | IO.eprintln "usage: kernel-check-ixe --fold <input.ixe> <output.jsonl>"; return 2
  let started ← IO.monoMsNow
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile input))
  let mut store : RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let pins ← IO.ofExcept defaultPins
  let pre ← IO.ofExcept builtinPrelude
  let natPins ← IO.ofExcept builtinNatOpPins
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) pins pre hints.lookup
  let tLoad ← IO.monoMsNow
  let (records, dropped) ← IO.lazyPure fun _ => acceptedRecords s
  let tSelect ← IO.monoMsNow
  IO.eprintln s!"fold: {s.store.size} records, {s.ordered.size} primary; kept {records.size} \
    (dropped {dropped} primary records the census declines or blocks); load {tLoad - started} ms, \
    selection {tSelect - tLoad} ms"
  if (← IO.getEnv "FOLD_READSTATS") == some "1" then
    readStats s records
    return 0
  let blobs := env.blobs.toList
  let r0 ← IO.monoNanosNow
  let decls ← IO.lazyPure fun _ =>
    Ix.Ixon.KernelAdmission.readStream pins pre records.toList blobs hints.lookup
  let decls ← match decls with
    | .ok ds => pure ds
    | .error e => IO.eprintln s!"fold: read failed: {e}"; return 1
  let prepared ← IO.lazyPure fun _ => Ix.Kernel.Frontend.preparePrelude pre.ix decls
  let r1 ← IO.monoNanosNow
  IO.eprintln s!"fold: read {decls.size} declarations ({prepared.size} prepared) in {(r1 - r0) / 1000000} ms"
  let prepared ← if (← IO.getEnv "FOLD_SHARE") == some "1" then do
      let s0 ← IO.monoNanosNow
      let shared ← IO.lazyPure fun _ => ShareCommon.shareCommon' prepared
      IO.eprintln s!"fold: shareCommon over all declarations in {((← IO.monoNanosNow) - s0) / 1000000} ms"
      pure shared
    else pure prepared
  let a0 ← IO.monoNanosNow
  let phaseA ← IO.lazyPure fun _ =>
    (prepared.foldlM (Ix.Kernel.Cached.annotDeclStep .verified natPins)
      (0, Ix.Kernel.mkFEnv Ix.Kernel.Env.empty, #[])) {}
  let a1 ← IO.monoNanosNow
  let ((_, fe, pend), _) ← match phaseA with
    | .ok r => pure r
    | .error (e, i) => IO.eprintln s!"fold: phase A failed at {i}: {e}"; return 1
  IO.eprintln s!"fold: phase A {(a1 - a0) / 1000000} ms, {pend.size} checks pending"
  let thread := (← IO.getEnv "FOLD_THREAD") != some "0"
  if (← IO.getEnv "FOLD_PERSIST") != some "0" then
    -- `Main.lean`'s phase-boundary mark: the installed environment is
    -- read-only from here on
    let _ ← unsafe Runtime.markPersistent fe
    let _ ← unsafe Runtime.markPersistent pend
  let b0 ← IO.monoNanosNow
  let (times, err) ← if thread then
      match ← IO.wait (← IO.asTask (prio := .dedicated) (phaseB fe pend)) with
      | .ok r => pure r
      | .error e => throw e
    else phaseB fe pend
  let b1 ← IO.monoNanosNow
  if let some (e, i) := err then
    IO.eprintln s!"fold: phase B failed at {i}: {e}"
  let handle ← IO.FS.Handle.mk output .write
  for (pc, t) in pend.zip times do
    handle.putStrLn (Lean.Json.mkObj [("name", Lean.toJson (toString pc.vg.cvA.name)),
      ("kind", Lean.toJson (kindWord pc)), ("micros", Lean.toJson t)]).compress
  let sum := times.foldl (· + ·) 0
  let over100 := times.foldl (fun n t => if t > 100000 then n + 1 else n) 0
  IO.eprintln s!"fold: phase B {(b1 - b0) / 1000000} ms wall{if thread then " (dedicated thread)" else ""}, \
    per-record sum {sum / 1000} ms over {times.size} records; median {percentile times 50} us, \
    p99 {percentile times 99} us, {over100} over 100 ms"
  IO.eprintln s!"fold: done in {(← IO.monoMsNow) - started} ms; peak RSS {(← statusKb "VmHWM:") / 1024} MB"
  return 0

end Benchmarks.Kernel.CheckIxeFold
