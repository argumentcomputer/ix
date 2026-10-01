/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.ConLecheStep
import Lean.CompactedRegion
import Ix.Address

/-! # A persistent read cache for the census (untrusted host tooling)

A census run decodes the whole `.ixe` (`Ixon.deEnv`), builds the record
store, the reader's index, the dependency order and the report names, and
reads every record through the Ixon reader, before and while it checks. All
of that is a function of the `.ixe`'s bytes and of the reader's code, so a
second run over the same file repeats it exactly. This cache keeps it: a
**plan** of the run (per record in the census order: its kind, the recursor
records read with it, the owners it depends on, and the reader's reading,
`Except ReadError Read`, with every declaration), written once as a Lean
compacted region (`Lean.CompactedRegion.save`, the `.olean` mechanism) and
memory-mapped by later runs, which then decode and read nothing.

**Keys.** A plan file is named by the BLAKE3 hash of the `.ixe`'s bytes and by
`version`: the cache format, Lean's githash and a digest of the sources a
reading or the plan's layout depends on (the reader, the prelude and pin
data, the imported frontend passes it runs, con-leche's syntax, the Ixon
decoder, the census order, this module), embedded at compile time
(`sourceDigest`). A file is only ever read under the key it was written
under, so a plan of another reader, layout or toolchain is never
reinterpreted. Corrupt or foreign files are refused by the region reader's
header check.

**What may use it.** The census drivers (`kernel-census`, `kernel-census-cl`:
`CENSUS_READ_CACHE=<dir>`) and other host tools. Never the certified entry
(`Ix.Ixon.Admission.checkBytes`): its theorems are about the bytes it is
given, so it decodes and reads them itself every time. Nothing here is
imported by the `IxKernel` package.

**Unsafe code.** `CompactedRegion.save`/`read` are `unsafe` in Lean core
because the root's type is erased at the extern boundary; `save` and `load`
below are the only uses, at the one type `Plan`, under the key discipline
above. The mapped objects are persistent (no reference counts) and never
freed during a run. -/

namespace Benchmarks.Kernel.ConLecheReadCache

open Ix.Kernel.ConLecheReader
open Benchmarks.Kernel.ConLecheStep

/-! ## The plan -/

/-- One record of a census run, in the census order. -/
structure PlanRecord where
  address : Address
  kind : String
  recs : Array Address
  deps : Array Address
  reading : Except ReadError Read
  deriving Inhabited

/-- A census run's plan: the setup line's counts, the report names, and the
records in order. -/
structure Plan where
  version : String
  ixe : String
  header : String
  names : Array (Address × Array String)
  records : Array PlanRecord
  deriving Inhabited

/-! ## Keys -/

/-- Bump when the plan's layout or its meaning changes in a way the source
digest would not see. -/
def formatTag : String := "conleche-read-cache-1"

/-- The sources a reading or the plan's layout depends on. -/
def sourceDigest : UInt64 := hash [
  include_str "../../Ix/Kernel/Ixon/Reader.lean",
  include_str "../../Ix/Kernel/Ixon/Prelude.lean",
  include_str "../../Ix/Kernel/Ixon/PinData.lean",
  include_str "../../Ix/Kernel/Ref.lean",
  include_str "../../Ix/Kernel/Frontend/InModel.lean",
  include_str "../../Ix/Kernel/Frontend/InModel/Kit.lean",
  include_str "../../Ix/Kernel/Frontend/InModel/Mutual.lean",
  include_str "../../Ix/Kernel/Frontend/InModel/Nested.lean",
  include_str "../../Ix/Kernel/Frontend/ProjRec.lean",
  include_str "../../Ix/Kernel/Frontend/NatOpGround.lean",
  include_str "../../Ix/Kernel/Expr.lean",
  include_str "../../Ix/Kernel/ExprOps.lean",
  include_str "../../Ix/Kernel/Level.lean",
  include_str "../../Ix/Kernel/CoreDefs.lean",
  include_str "../../Ix/Kernel/Name.lean",
  include_str "../../Ix/Kernel/Env.lean",
  include_str "../../Ix/Kernel/PropWhen.lean",
  include_str "../../Ix/Ixon.lean",
  include_str "../../Ix/Ixon/Types.lean",
  include_str "ConLecheStep.lean",
  include_str "ConLecheReadCache.lean"]

/-- The reader version a plan is written under. -/
def version : String := s!"{formatTag}-{Lean.githash}-{sourceDigest}"

/-- The plan file of an `.ixe` in a cache directory. -/
def planPath (dir : System.FilePath) (ixeBytes : ByteArray) : System.FilePath × String :=
  let ixe := toString (Address.blake3 ixeBytes)
  let tag := toString (Address.blake3 version.toUTF8)
  (dir / s!"{ixe}-{tag.take 16}.reads", ixe)

/-! ## Writing and reading -/

/-- The plan of a finished census run: its readings (in order) with each
record's view in the setup. -/
def ofRun (s : Setup) (ixe header : String) (names : Std.HashMap Address (Array String))
    (readings : Array (Address × Except ReadError Read)) : Plan := Id.run do
  let mut records : Array PlanRecord := Array.mkEmpty readings.size
  let mut nameRows : Array (Address × Array String) := #[]
  for (address, reading) in readings do
    let some v := s.view address | continue
    records := records.push { address, kind := v.kind, recs := v.recs, deps := v.deps (), reading }
    for a in #[address] ++ v.recs do
      if let some ns := names[a]? then nameRows := nameRows.push (a, ns)
  return { version, ixe, header, names := nameRows, records }

/-- Write a plan (to a temporary file, then renamed). -/
def save (path : System.FilePath) (plan : Plan) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  let tmp := path.addExtension "tmp"
  let _ ← unsafe Lean.CompactedRegion.save (α := Plan) tmp (.mkSimple plan.ixe) plan #[] none
  IO.FS.rename tmp path

/-- Map a plan written under this version, if there is one. The region is
never freed: the run uses its objects to the end. -/
def load (path : System.FilePath) (ixe : String) : IO (Option Plan) := do
  unless ← path.pathExists do return none
  let (plan, _) ← unsafe Lean.CompactedRegion.read (α := Plan) path #[]
  if plan.version == version && plan.ixe == ixe then return some plan
  IO.eprintln s!"census: read cache {path}: version or key mismatch; ignored"
  return none

/-! ## Running from a plan -/

/-- The census loop over a plan: every view and reading is the plan's, and
the reading state is not threaded (no record is read). `limit` bounds the
records, as for a live run. -/
def censusLoopPlan (plan : Plan) (pins : List Ix.Kernel.NatOpPinSet) (limit : Option Nat)
    (skip : Std.HashSet String) (emit : Row → IO Unit)
    (before : Address → IO Unit := fun _ => pure ()) (after : IO Unit := pure ())
    (progress : Nat → Outcome → IO Unit := fun _ _ => pure ()) : IO Outcome := do
  let byAddress : Std.HashMap Address PlanRecord :=
    plan.records.foldl (fun m r => m.insert r.address r) {}
  let names : Std.HashMap Address (Array String) := plan.names.foldl (fun m (a, ns) => m.insert a ns) {}
  let addresses := plan.records.map (·.address)
  let addresses := match limit with | some n => addresses.extract 0 n | none => addresses
  censusLoopWith
    (fun a => (byAddress[a]?).map fun r => { kind := r.kind, recs := r.recs, deps := fun _ => r.deps })
    (fun (_ : Unit) a => match byAddress[a]? with
      | some r => r.reading
      | none => .error (.malformed "record is missing from the read cache"))
    (fun _ _ => ()) () pins (names.getD · #[]) addresses skip emit before after progress

end Benchmarks.Kernel.ConLecheReadCache
