/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Projection
import Ix.Ixon.BlockOrder
import Tests.Ix.Kernel.ReaderFidelity

/-! # The kernel's output side against the compiler's records

The certified entries write Ixon records on one path only: projection
records, from a block member or constructor reference
(`Ix.Kernel.Egress.writeProjection`), keyed by their pure BLAKE3 address
(`Ix.Ixon.Projection.address`). `Projection.reconstruct` writes a batch's
projections from its `muts` blocks, and `BlockOrder` decides that a block's
members are in canonical order with the same addresses. This module checks
that output against real compiled environments:

1. **Records written are the compiler's** (`projections`, every environment): for
   every `muts` record, the projections `Projection.reconstruct` writes for
   that block alone are exactly the compiler's projection records of that
   block, with the same keys (pure BLAKE3 against the compiler's hash) and the
   same canonical bytes, and every compiler projection record is written this
   way. Every block also passes the certified order entry's check
   (`BlockOrder.checkRecord`): the compiler's member order is the one it
   accepts ("Block order" below).
2. **Records written are re-read to the same declarations, and agree with the
   installed environment** (`entries`, the fixture): over a set of records the
   checker accepts,
   - the reader's declarations with the compiler's projections and with the
     reconstructed ones are equal (`KernelAdmission.readStream`);
   - `KernelAdmission.checkConstants` with the compiler's projections,
     `Projection.checkBytes` with the projections omitted (reconstructed) and
     `BlockOrder.checkBytes` (reconstructed, order decided) install the same
     environment: the same constants, in the same order, of the same kinds,
     with equal types;
   - every projection record names a constant installed in that environment,
     of its own kind (a definition, theorem or opaque for a definition
     projection; an inductive, constructor or recursor for the others).

## Block order

The block-order entry checks inductive, definition and mixed `muts` blocks
against the canonical classes of `BlockOrder.canonicalClasses`, and a block of
recursors in motive order (`BlockOrder.checkMotives`): the compiler stores it
in the order of its motives (`T.rec`, `T.rec_1`, …; the members' own order for
a mutual block), which is not always the structural order (2 of the 7
recursor blocks of two or more members in the fixture closure, `Rose.rec` with
`Rose.rec_1` and `Args.rec` with `Tm.rec`, are not; none of the 3 in `Init`
and `Std`). Until 2026-10-01 the entry checked recursor blocks structurally
and refused compiled batches that contained those two; the Rust kernel checks
only inductive blocks at ingress (`crates/kernel/src/ingress.rs`: "Skip Recr
blocks (they contain primary + aux recursors, with the aux portion in
kernel-computed canonical order, not stored sort_consts)"). Every block of
every environment must now pass (`ProjectionReport.refused` is a problem), the two
named fixture blocks are required among the accepted recursor blocks
(`Tests.Ix.Kernel.ReaderRoundtrip`), and every accepted recursor block with
its first two members swapped must be refused for its motive order.

**No environment egress exists.** Nothing writes con-leche's `Env` back to
Ixon records; the intrinsic kernel's record writer over its own syntax was
retired at L6 (`plans/review/cl-l6`). What it would need is in
`plans/review/cl-fidelity/README.md` ("Egress of the environment"). -/

open Ix.Kernel (ConstRef)
open Ix.Kernel.IxonReader
open Benchmarks.Kernel.CheckIxeStep (RecordStore Hints setup Setup owner)

namespace Tests.Ix.Kernel.EgressFidelity

open Tests.Ix.Kernel.ReaderFidelity

/-! ## 1. Projection records and block order -/

/-- A `muts` block's kind, for the order findings. -/
def blockKind (ms : Array Ixon.MutConst) : String :=
  if ms.all (fun | .indc _ => true | _ => false) then "inductive"
  else if ms.all (fun | .recr _ => true | _ => false) then "recursor"
  else if ms.all (fun | .defn _ => true | _ => false) then "definition"
  else "mixed"

structure ProjectionReport where
  blocks : Nat := 0
  /-- projection records the compiler emitted, and those the writer wrote -/
  compiled : Nat := 0
  written : Nat := 0
  /-- written with the compiler's key and bytes -/
  matched : Nat := 0
  problems : Array String := #[]
  /-- blocks of two or more members, by kind, and those the order check
  (`BlockOrder.checkRecord`) refuses, by kind -/
  ordered : Std.HashMap String Nat := {}
  refused : Std.HashMap String (Array Address) := {}
  /-- recursor blocks of two or more members in motive order, and how many of
  them the check refuses with their first two members swapped -/
  motiveOrdered : Array Address := #[]
  swapsRefused : Nat := 0

def ProjectionReport.summary (r : ProjectionReport) : String :=
  let kinds := (r.ordered.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (k, n) =>
    s!"{k} {n} ({((r.refused.getD k #[]).size)} refused)"
  s!"projections: {r.blocks} blocks, {r.compiled} compiler records, {r.written} written, \
    {r.matched} identical; {r.problems.size} problems" ++
    String.join (r.problems.toList.take 20 |>.map ("\n  " ++ ·)) ++
    s!"\nblock order (blocks of two or more members): {", ".intercalate kinds}; \
    {r.motiveOrdered.size} recursor blocks in motive order, {r.swapsRefused} refused with two \
    members swapped"

/-- The order findings: any block the order check refuses (the compiler's
order is the one the certified order entry accepts), and any accepted
recursor block it does not refuse with two members swapped. -/
def ProjectionReport.orderProblems (r : ProjectionReport) : List String :=
  (r.refused.toList.filterMap fun (k, as) =>
    if as.isEmpty then none else some s!"{as.size} {k} blocks refused") ++
  (if r.swapsRefused == r.motiveOrdered.size then [] else
    [s!"{r.motiveOrdered.size - r.swapsRefused} recursor blocks accepted with two members swapped"])

/-- The Lean names of a block's members, through its projection records'
metadata (for reports). -/
def memberNames (ixon : Ixon.Env) (store : RecordStore) (block : Address) : List String := Id.run do
  let some { info := .muts ms, .. } := store[block]? | return []
  let mut byIdx : Std.HashMap Nat Address := {}
  for (a, c) in store.toList do
    match c.info with
    | .rPrj p => if p.block == block then byIdx := byIdx.insert p.idx.toNat a
    | .dPrj p => if p.block == block then byIdx := byIdx.insert p.idx.toNat a
    | .iPrj p => if p.block == block then byIdx := byIdx.insert p.idx.toNat a
    | _ => pure ()
  let mut names : Std.HashMap Address String := {}
  for (n, nd) in ixon.named.toList do
    let ln := _root_.Ix.SemanticContract.toLeanName n
    unless isBlockName ln do names := names.insert nd.addr (toString ln)
  return (List.range ms.size).map fun i => ((byIdx[i]?).bind (names[·]?)).getD s!"#{i}"

def maxProjections : Nat := 1 <<< 20

/-- Every `muts` record's projections, written by the certified writer for
that block alone, against the compiler's; and each block's canonical order. -/
def projections (store : RecordStore) (blobs : List (Address × ByteArray)) : ProjectionReport := Id.run do
  let mut byOwner : Std.HashMap Address (Array (Address × Ixon.Constant)) := {}
  let mut report : ProjectionReport := {}
  for (a, c) in store.toList do
    if Ix.Kernel.Ingress.isProjection c.info then
      byOwner := byOwner.insert (owner a c) ((byOwner.getD (owner a c) #[]).push (a, c))
      report := { report with compiled := report.compiled + 1 }
  let mut covered : Std.HashSet Address := {}
  for (a, c) in store.toList do
    let .muts ms := c.info | continue
    report := { report with blocks := report.blocks + 1 }
    match Ix.Ixon.Projection.reconstruct maxProjections [(a, c)] with
    | .error e => report := { report with problems := report.problems.push s!"{a}: {reprStr e}" }
    | .ok expanded =>
      let written := expanded.filter (·.1 != a)
      let compiled := byOwner.getD a #[]
      report := { report with written := report.written + written.length }
      for (k, w) in written do
        match compiled.find? (·.1 == k) with
        | some (_, c') =>
          if Ixon.serConstant w == Ixon.serConstant c' then
            report := { report with matched := report.matched + 1 }
            covered := covered.insert k
          else report := { report with problems := report.problems.push s!"{a}: projection {k} differs" }
        | none =>
          report := { report with problems := report.problems.push (
            s!"{a}: written projection {k} is not a compiler record") }
    if ms.size ≥ 2 then
      let kind := blockKind ms
      report := { report with ordered := report.ordered.insert kind (report.ordered.getD kind 0 + 1) }
      match Ix.Ixon.BlockOrder.checkRecord {} blobs a c with
      | .ok () =>
        if kind == "recursor" then
          report := { report with motiveOrdered := report.motiveOrdered.push a }
          -- the wrong order: the first two members swapped
          let swapped := { c with info := .muts (ms.swapIfInBounds 0 1) }
          if let .error (.motiveOrder ..) := Ix.Ixon.BlockOrder.checkRecord {} blobs a swapped then
            report := { report with swapsRefused := report.swapsRefused + 1 }
      | .error _ =>
        report := { report with refused := report.refused.insert kind ((report.refused.getD kind #[]).push a) }
  for (_, ps) in byOwner.toList do
    for (k, _) in ps do
      unless covered.contains k do
        report := { report with problems := report.problems.push (
          s!"compiler projection {k} is not written by its block") }
  return report

/-! ## 2. Re-reading and the installed environment -/

/-- A constant's kind as installed. -/
def infoKind : Ix.Kernel.ConstantInfo → String
  | .axiomInfo .. => "axiom" | .defnInfo .. => "definition" | .thmInfo .. => "theorem"
  | .indInfo .. => "inductive" | .ctorInfo .. => "constructor" | .recInfo .. => "recursor"
  | .projInfo .. => "projection table"

/-- The installed kinds a projection layout may name. -/
def layoutKinds : Ix.Kernel.Egress.ProjectionLayout → List String
  | .definition => ["definition", "theorem", "axiom"]
  | .inductive => ["inductive"]
  | .recursor => ["recursor"]
  | .constructor => ["constructor"]

/-- Two installed environments agree: the same constants in the same order,
of the same kinds, with equal types (con-leche's executed equality). -/
def envDiff (a b : Ix.Kernel.Env) : Option String :=
  if a.consts.length != b.consts.length then
    some s!"{a.consts.length} constants vs {b.consts.length}"
  else (a.consts.zip b.consts).zipIdx.findSome? fun ((x, y), i) =>
    let u := x.toConstantVal
    let v := y.toConstantVal
    if u.name != v.name then some s!"constant {i}: {u.name} vs {v.name}"
    else if infoKind x != infoKind y then some s!"{u.name}: {infoKind x} vs {infoKind y}"
    else if !CVal.beq u v then some s!"{u.name}: types differ"
    else none

/-- The reader's declarations, as entries, compared one by one. -/
def declsDiff (a b : Array Ix.Kernel.Declaration) : Option String :=
  let xs := a.flatMap entriesOf
  let ys := b.flatMap entriesOf
  if a.size != b.size || xs.size != ys.size then some s!"{a.size} declarations vs {b.size}"
  else (xs.zip ys).findSome? fun (x, y) => (entryDiff x y).map (s!"{x.name}: " ++ ·)

structure EntryReport where
  records : Nat := 0
  projectionRecords : Nat := 0
  constants : Nat := 0
  /-- projection records whose constant is installed with a matching kind -/
  projectionsInstalled : Nat := 0
  problems : Array String := #[]

def EntryReport.summary (r : EntryReport) : String :=
  s!"entries: {r.records} primary records, {r.projectionRecords} projection records, \
    {r.constants} installed constants, {r.projectionsInstalled} projections installed; \
    {r.problems.size} problems" ++ String.join (r.problems.toList.take 20 |>.map ("\n  " ++ ·))

def limits : Ix.Ixon.Admission.Limits := ⟨1 <<< 16, 1 <<< 16, 1 <<< 28, 1 <<< 22, 1 <<< 20⟩

/-- The re-reading and installed-environment checks over the primary
records `primaries` (in a dependency order the checker accepts), with all
of the store's projection records of their blocks. -/
def entries (input : Input) (primaries : Array Address) : IO EntryReport := do
  let pins ← IO.ofExcept defaultPins
  let pre ← IO.ofExcept builtinPrelude
  let hints := Hints.ofStore input.store input.ixon.anonHints
  let owners : Std.HashSet Address := primaries.foldl (·.insert ·) {}
  let prim : List (Address × Ixon.Constant) :=
    primaries.toList.filterMap fun a => (input.store[a]?).map (a, ·)
  let projs : List (Address × Ixon.Constant) :=
    (input.store.toArray.filter fun (a, c) =>
      Ix.Kernel.Ingress.isProjection c.info && owners.contains (owner a c)).qsort
      (fun x y => x.1.cmpBytes y.1 == .lt) |>.toList
  let blobs := (input.ixon.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList
  let mut report : EntryReport := { records := prim.length, projectionRecords := projs.length }
  -- the reader, with the compiler's projections and with the written ones
  let compiled := prim ++ projs
  let reconstructed ← match Ix.Ixon.Projection.reconstruct maxProjections prim with
    | .ok cs => pure cs
    | .error e => throw (IO.userError s!"reconstruct: {reprStr e}")
  let decls₁ ← IO.ofExcept ((Ix.Ixon.KernelAdmission.readStream pins pre compiled blobs hints.lookup).mapError toString)
  let decls₂ ← IO.ofExcept ((Ix.Ixon.KernelAdmission.readStream pins pre reconstructed blobs hints.lookup).mapError toString)
  if let some d := declsDiff decls₁ decls₂ then
    report := { report with problems := report.problems.push s!"re-read with written projections: {d}" }
  -- the three certified entries
  let env₁ ← IO.ofExcept ((Ix.Ixon.KernelAdmission.checkConstants compiled blobs hints.lookup).mapError
    fun e => s!"checkConstants: {e}")
  let bytes := prim.map fun (a, c) => (a, Ixon.serConstant c)
  let env₂ ← match Ix.Ixon.Projection.checkBytes maxProjections limits bytes blobs hints.lookup with
    | .ok env => pure env
    | .error (.reconstruction e) => throw (IO.userError s!"Projection.checkBytes: {reprStr e}")
    | .error (.checker e) => throw (IO.userError s!"Projection.checkBytes: {e}")
  report := { report with constants := env₁.consts.length }
  if let some d := envDiff env₁ env₂ then
    report := { report with problems := report.problems.push s!"projection entry: {d}" }
  -- the block-order entry accepts the same batch with the same environment
  match Ix.Ixon.BlockOrder.checkBytes maxProjections limits {} bytes blobs hints.lookup with
  | .ok env₃ =>
    if let some d := envDiff env₁ env₃ then
      report := { report with problems := report.problems.push s!"block-order entry: {d}" }
  | .error (.order e) =>
    report := { report with problems := report.problems.push s!"block-order entry: {reprStr e}" }
  | .error (.checker e) =>
    report := { report with problems := report.problems.push s!"block-order entry: {e}" }
  -- each projection record names an installed constant of its kind
  let cx := Ix.Ixon.KernelAdmission.streamContext pins pre compiled blobs hints.lookup
  let installed : Std.HashMap CName String := env₁.consts.foldl
    (fun m ci => m.insert ci.toConstantVal.name (infoKind ci)) {}
  for (k, p) in projs do
    match Ix.Kernel.Egress.readProjection p with
    | .error _ => report := { report with problems := report.problems.push s!"projection {k} does not read" }
    | .ok (layout, ref) =>
      let n := cx.nameOf ref
      match installed[n]? with
      | some kind =>
        if (layoutKinds layout).contains kind then
          report := { report with projectionsInstalled := report.projectionsInstalled + 1 }
        else report := { report with problems := report.problems.push (
          s!"projection {k} ({reprStr layout}) names {n}, installed as {kind}") }
      | none => report := { report with problems := report.problems.push (
          s!"projection {k} ({reprStr layout}) names {n}, which is not installed") }
  return report

/-- The records of `roots`' closure that the environment check accepts, in the
check order (the certified entries take only accepted batches). -/
def acceptedClosure (input : Input) (roots : Array Lean.Name) : IO (Array Address) := do
  let pins ← IO.ofExcept defaultPins
  let pre ← IO.ofExcept builtinPrelude
  let natPins ← IO.ofExcept builtinNatOpPins
  let hints := Hints.ofStore input.store input.ixon.anonHints
  let s : Setup := setup input.store (input.ixon.blobs[·]?) pins pre hints.lookup
  let rootAddrs := roots.filterMap fun n =>
    (input.ixon.named[_root_.Ix.Name.fromLeanName n]?).map (·.addr)
  let ordered := Benchmarks.Kernel.CheckIxeStep.closure s.store s.extra
    (pre.records.map (fun (p : Address × Ixon.Constant) => p.1) ++ rootAddrs)
  let rows ← IO.mkRef (#[] : Array Benchmarks.Kernel.CheckIxeStep.Row)
  let _ ← Benchmarks.Kernel.CheckIxeStep.checkLoop s natPins (fun _ => #[]) ordered {}
    (emit := fun row => rows.modify (·.push row))
  let accepted : Std.HashSet Address := (← rows.get).foldl
    (fun acc r => if r.outcome == "accept" then acc.insert r.address else acc) {}
  -- the compiled records only (the entry supplies the prelude's own)
  -- with each block's recursor records after it (no root reaches them: they
  -- reference their block, not the other way)
  let withRecs := ordered.flatMap fun a =>
    #[a] ++ Benchmarks.Kernel.CheckIxeStep.recursorRecords s.cx.index a
  let mut seen : Std.HashSet Address := {}
  let mut out : Array Address := #[]
  for a in withRecs do
    if accepted.contains a && input.store.contains a && !seen.contains a then
      seen := seen.insert a
      out := out.push a
  return out

end Tests.Ix.Kernel.EgressFidelity
