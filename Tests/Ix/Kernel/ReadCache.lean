/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import LSpec
import Benchmarks.Kernel.CheckIxeReadCache
import Tests.Ix.Kernel.ReaderRoundtrip

/-! # The census's persistent read cache (`lake test`)

`Benchmarks.Kernel.CheckIxeReadCache` on the compiled fixture closure of
`Tests.Ix.Kernel.ReaderRoundtrip`: a census run over the closure of a few
fixture declarations (nested and mutual blocks, the modeller's records, a
nested structure) records its readings; the plan is written as a compacted
region, mapped back, and the census run from the plan gives the same rows
(address, kind, names, outcome, reason) for every record. A plan written
under another version is not used. -/

namespace Tests.Ix.Kernel.ReadCache

open LSpec
open Ix.Kernel.IxonReader
open Benchmarks.Kernel.CheckIxeStep
open Tests.Ix.Kernel.ReaderFidelity

def rowKey (r : Row) : String :=
  s!"{r.address} {r.kind} {r.names} {r.outcome} {r.reason}"

def check : IO (Nat × Array String) := do
  let (_, inp) ← Tests.Ix.Kernel.ReaderRoundtrip.input
  let pins ← IO.ofExcept defaultPins
  let pre ← IO.ofExcept builtinPrelude
  let natPins ← IO.ofExcept builtinNatOpPins
  let hints := Hints.ofStore inp.store inp.ixon.anonHints
  let s : Setup := setup inp.store (inp.ixon.blobs[·]?) pins pre hints.lookup
  let names := reportNames inp.ixon inp.store
  let roots := Tests.Ix.Kernel.ReaderRoundtrip.nestedSeeds.filterMap fun n =>
    (inp.ixon.named[_root_.Ix.Name.fromLeanName n]?).map (·.addr)
  let ordered := closure s.store s.extra (pre.records.map (fun (p : Address × Ixon.Constant) => p.1) ++ roots)
  -- a live run, recording its readings
  let liveRows ← IO.mkRef (#[] : Array Row)
  let readings ← IO.mkRef (#[] : Array (Address × Except ReadError Read))
  let _ ← checkLoop s natPins (names.getD · #[]) ordered {} (emit := fun r => liveRows.modify (·.push r))
    (onRead := fun a r _ => readings.modify (·.push (a, r)))
  -- the plan, written and mapped back
  let dir ← IO.FS.createTempDir
  let mut errors : Array String := #[]
  try
    let bytes := ByteArray.mk #[1, 2, 3]
    let (path, ixe) := Benchmarks.Kernel.CheckIxeReadCache.planPath dir bytes
    let plan := Benchmarks.Kernel.CheckIxeReadCache.ofRun s ixe "fixture" names (← readings.get)
    Benchmarks.Kernel.CheckIxeReadCache.save path plan
    let some mapped ← Benchmarks.Kernel.CheckIxeReadCache.load path ixe
      | throw (IO.userError "the written plan does not load")
    unless mapped.records.size == (← readings.get).size do
      errors := errors.push s!"{mapped.records.size} plan records for {(← readings.get).size} readings"
    let plannedRows ← IO.mkRef (#[] : Array Row)
    let _ ← Benchmarks.Kernel.CheckIxeReadCache.checkLoopPlan mapped natPins none {}
      (emit := fun r => plannedRows.modify (·.push r))
    let live := (← liveRows.get).map rowKey
    let planned := (← plannedRows.get).map rowKey
    unless live == planned do
      let first := (live.zip planned).find? (fun (a, b) => a != b)
      errors := errors.push s!"{live.size} live rows, {planned.size} planned rows; first difference {first}"
    unless (← liveRows.get).any (·.outcome == "accept") do errors := errors.push "no accepted row"
    -- a plan under another version or key is not used
    let other := dir / "other.reads"
    Benchmarks.Kernel.CheckIxeReadCache.save other { plan with version := "another-reader" }
    if (← Benchmarks.Kernel.CheckIxeReadCache.load other ixe).isSome then
      errors := errors.push "a plan of another version was used"
    if (← Benchmarks.Kernel.CheckIxeReadCache.load path "another-ixe").isSome then
      errors := errors.push "a plan of another .ixe was used"
  finally
    IO.FS.removeDirAll dir
  return ((← liveRows.get).size, errors)

def suite : List TestSeq := [
  .individualIO "read cache: a census from the mapped plan gives the live rows" none (do
    let (rows, errors) ← check
    IO.println s!"read cache: {rows} rows"
    let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
    return (errors.isEmpty, rows, 0, msg)) .done ]

end Tests.Ix.Kernel.ReadCache
