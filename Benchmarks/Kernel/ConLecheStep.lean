/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon
import Ix.Kernel.Ixon.Prelude
import Ix.Kernel.Cached.Installed
import Ix.Kernel.NatOpPinSet

/-! # Con-leche's fold one record at a time (untrusted harness)

The per-record step shared by the census (`Benchmarks.Kernel.ConLecheCensus`)
and the pin generator (`Benchmarks.Kernel.ConLechePinGen`): the dependency
order of an environment's primary records, the Ixon reader's declarations of
each record, and an incremental con-leche state that installs and checks
them one record at a time, continuing past failures.

**The order.** The prelude's records first, then a depth-first postorder
over table references with projections replaced by their owners, in which a
pinned `Nat` operation also depends on its certificate ground
(`natOpDeps`), as `Frontend.preparePrelude`'s hoist arranges, and a record
that contains a literal depends on the constants the literal references
(`ConLecheReader.literalEdges`: the `Nat` trio, and for a string literal the
string-support constants).

**The step.** `Checker.step` is phase A of `Ix.Kernel.Cached.checkDecls`
(`annotDeclStep`) on one declaration, then phase B (`checkPendingList`) on
the records that step left pending; phase B checks each record against the
prefix view at its install, so the verdict is the one the fold would give on
the prefix. A failing declaration is rolled back: the environment is rebuilt
from the constant list before the step and the memo state is reset (it is
only a cache), so a failure leaves no constant behind. A record that
references a failed or blocked one is blocked and not checked. Recursor
records are read with their inductive block and take its outcome. None of
this is a certified verdict; `Ix.Ixon.ConLecheAdmission.checkBytes` is. -/

namespace Benchmarks.Kernel.ConLecheStep

open Ix.Kernel (ConstRef)
open Ix.Kernel.ConLecheReader

/-! ## The per-record step -/

/-- The incremental checker state: the indexed environment, the memo
state, and the fold position. -/
structure Checker where
  fe : Ix.Kernel.FEnv := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
  cs : Ix.Kernel.Cached.CState := {}
  pos : Nat := 0

instance : Inhabited Checker := ⟨{}⟩

/-- Install and check one declaration; on failure, the state before it. -/
def Checker.step (pins : List Ix.Kernel.NatOpPinSet) (c : Checker) (d : Ix.Kernel.Declaration) :
    Checker × Option Ix.Kernel.CheckError :=
  let ⟨fe, cs, pos⟩ := c
  let before := fe.env
  match Ix.Kernel.Cached.annotDeclStep .verified pins (pos, fe, #[]) d cs with
  | .error (e, _) => (⟨Ix.Kernel.mkFEnv before, {}, pos + 1⟩, some e)
  | .ok ((pos', fe', pend), cs') =>
    match Ix.Kernel.Cached.checkPendingList .verified fe' pend.toList with
    | .ok () => (⟨fe', cs', pos'⟩, none)
    | .error (e, _) => (⟨Ix.Kernel.mkFEnv before, {}, pos'⟩, some e)

/-- One record's declarations, in order; the first failure ends it. -/
def Checker.steps (pins : List Ix.Kernel.NatOpPinSet) (c : Checker)
    (ds : Array Ix.Kernel.Declaration) : Checker × Option Ix.Kernel.CheckError := Id.run do
  let mut c := c
  for d in ds do
    let (c', e) := c.step pins d
    c := c'
    if e.isSome then return (c, e)
  return (c, none)

def checkOutcome : Ix.Kernel.CheckError → String × String
  | .invalid m => ("reject", m)
  | .notImplemented m => ("decline", m)
  | .internal m => ("decline", s!"internal: {m}")

def readOutcome : ReadError → String × String
  | .malformed m => ("reject", s!"reader: {m}")
  | .declined m => ("decline", s!"reader: {m}")

/-! ## Records and order -/

abbrev RecordStore := Std.HashMap Address Ixon.Constant

def owner (address : Address) (source : Ixon.Constant) : Address :=
  match source.info with
  | .dPrj p => p.block
  | .iPrj p => p.block
  | .rPrj p => p.block
  | .cPrj p => p.block
  | _ => address

/-- Primary records in dependency order: an iterative depth-first postorder
over table references (and the `extra` edges), with projections replaced by
their owners; `first` comes first, in its own order. -/
def order (store : RecordStore) (extra : Std.HashMap Address (Array Address))
    (first : Array Address) : Array Address := Id.run do
  let mut done : Std.HashSet Address := {}
  let mut active : Std.HashSet Address := {}
  let mut out : Array Address := #[]
  let roots := first ++ (store.toArray.qsort (fun a b => a.1.cmpBytes b.1 == .lt)).map (·.1)
  for address in roots do
    let some source := store[address]? | continue
    let root := owner address source
    if done.contains root then continue
    let mut stack : Array (Address × Bool) := #[(root, false)]
    while !stack.isEmpty do
      let (node, expanded) := stack.back!
      stack := stack.pop
      if expanded then
        active := active.erase node
        unless done.contains node do
          done := done.insert node
          out := out.push node
      else unless done.contains node || active.contains node do
        active := active.insert node
        stack := stack.push (node, true)
        let refs := (store[node]?.map (·.refs)).getD #[]
        for ref in refs ++ extra.getD node #[] do
          if let some target := store[ref]? then
            let dependency := owner ref target
            unless dependency == node || done.contains dependency || active.contains dependency do
              stack := stack.push (dependency, false)
  return out

/-- Only the records reachable from `roots` (with projections replaced by
owners), in dependency order. -/
def closure (store : RecordStore) (extra : Std.HashMap Address (Array Address))
    (roots : Array Address) : Array Address := Id.run do
  let sub := order store extra roots
  -- `order` continues with every other record after the roots' closures;
  -- keep the prefix the roots reach
  let mut reach : Std.HashSet Address := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let a := todo[todo.size - 1]
    todo := todo.pop
    let some c := store[a]? | continue
    let o := owner a c
    if reach.contains o then continue
    reach := reach.insert o
    for r in ((store[o]?.map (·.refs)).getD #[]) ++ extra.getD o #[] do
      if store.contains r then todo := todo.push r
  return sub.filter reach.contains

def kindOf (source : Ixon.Constant) : String :=
  match source.info with
  | .defn d => match d.kind with | .defn => "definition" | .thm => "theorem" | .opaq => "opaque"
  | .recr _ => "recursor"
  | .axio _ => "axiom"
  | .quot _ => "quotient"
  | .muts ms =>
    if ms.all (fun | .recr _ => true | _ => false) then "recursor"
    else if ms.size == 1 then
      match ms[0]! with
      | .indc _ => "inductive"
      | .defn d => match d.kind with | .defn => "definition" | .thm => "theorem" | .opaq => "opaque"
      | .recr _ => "recursor"
    else s!"block({ms.size})"
  | _ => "projection"

/-- The recursor records read with an inductive block. -/
def recursorRecords (index : RecIndex) (block : Address) : Array Address :=
  ((index.blocks[block]?.map (·.recs)).getD #[]).foldl (fun acc r =>
    let a := r.block
    if a == block || acc.contains a then acc else acc.push a) #[]

/-- The record owners a record depends on: its references' owners, its
recursor records' references' owners, and the extra edges. -/
def dependencies (store : RecordStore) (index : RecIndex) (extra : Std.HashMap Address (Array Address))
    (address : Address) (source : Ixon.Constant) : Array Address := Std.HashSet.toArray <| Id.run do
  let recs := recursorRecords index address
  let mut out : Std.HashSet Address := {}
  for r in #[address] ++ recs do
    let refs := if r == address then source.refs else ((store[r]?.map (·.refs)).getD #[])
    for ref in refs ++ extra.getD r #[] do
      if let some target := store[ref]? then
        let o := owner ref target
        unless o == address || recs.contains o do out := out.insert o
  return out

/-- The pinned `Nat` operations' certificate ground as extra edges
(`Frontend/NatOpGround.lean`): an operation's record depends on the records
of the operations its recurrences name. -/
def groundEdges (pins : Std.HashMap (ConstRef Address) CName) : Std.HashMap Address (Array Address) :=
  Id.run do
  let byName : Std.HashMap CName (ConstRef Address) := pins.fold (fun m r n => m.insert n r) {}
  let mut out : Std.HashMap Address (Array Address) := {}
  for (r, n) in pins.toList do
    if Ix.Kernel.natOpNames.contains n || Ix.Kernel.natDivModNames.contains n then
      for g in Ix.Kernel.natOpDeps n do
        if let some gr := byName[g]? then
          if gr.block != r.block then
            out := out.insert r.block ((out.getD r.block #[]).push gr.block)
  return out

/-- The union of two edge maps. -/
def mergeEdges (a b : Std.HashMap Address (Array Address)) : Std.HashMap Address (Array Address) :=
  b.fold (fun m k vs => m.insert k ((m.getD k #[]) ++ vs.filter (!(m.getD k #[]).contains ·))) a

/-- The host's reducibility hints, at the address the compiler registers
them under (a projection's for a block member): the projection map is built
once, from the whole store, and every lookup is two probes.

(The L4a version returned the lookup as a closure from a function of the
store; the compiler compiled it at its full arity, so every lookup rebuilt
the projection map over all ~100k records, about 55 ms per definition
record: 50.6 s of the 4,300-record prefix census's "reading".) -/
structure Hints where
  projAt : Std.HashMap (ConstRef Address) Address := {}
  hints : Std.HashMap Address Lean.ReducibilityHints := {}

def Hints.ofStore (store : RecordStore) (hints : Std.HashMap Address Lean.ReducibilityHints) :
    Hints := Id.run do
  let mut projAt : Std.HashMap (ConstRef Address) Address := {}
  for (a, c) in store.toList do
    if let .dPrj p := c.info then projAt := projAt.insert (.member p.block p.idx.toNat) a
  return { projAt, hints }

def Hints.lookup (h : Hints) (r : ConstRef Address) : Option Ix.Kernel.ReducibilityHint := do
  let conv : Lean.ReducibilityHints → Ix.Kernel.ReducibilityHint
    | .opaque => .opaque
    | .abbrev => .abbrev
    | .regular h => .regular h.toNat
  conv <$> h.hints[(h.projAt[r]?).getD r.block]?

/-! ## Rows -/

structure Row where
  address : Address
  names : Array String
  kind : String
  outcome : String
  reason : String
  micros : Nat
  readMicros : Nat := 0

def Row.json (row : Row) : Lean.Json := Lean.Json.mkObj [
  ("address", Lean.toJson (toString row.address)), ("names", Lean.toJson row.names),
  ("kind", Lean.toJson row.kind), ("outcome", Lean.toJson row.outcome),
  ("reason", Lean.toJson row.reason), ("micros", Lean.toJson row.micros),
  ("readMicros", Lean.toJson row.readMicros)]

/-- A field of `/proc/self/status` in kB (Linux only; 0 elsewhere). -/
def statusKb (field : String) : IO Nat := do
  let status ← (IO.FS.readFile "/proc/self/status" |>.toBaseIO)
  let some line := status.toOption.bind fun text => text.splitOn "\n" |>.find? (·.startsWith field)
    | return 0
  return ((line.drop field.length).trimAscii.toString.takeWhile Char.isDigit).toNat!

/-! ## The run -/

/-- What a census run reads: the store, the reader context and the order. -/
structure Setup where
  store : RecordStore
  cx : Ctx
  extra : Std.HashMap Address (Array Address)
  ordered : Array Address

/-- The store backed by the prelude's records, the reader context, and the
order (the prelude's owners first). -/
def setup (store : RecordStore) (blobs : Address → Option ByteArray)
    (pins : Pins) (pre : Prelude)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) : Setup := Id.run do
  let mut store := store
  for (a, c) in pre.records do
    unless store.contains a do store := store.insert a c
  let records := store.toArray
  let index := buildIndex (store[·]?) pins.names records
  let cx : Ctx := { store := (store[·]?), blob := blobs, pins, index, hint,
                    keys := keyNamesOf (store[·]?) pins.names records }
  let extra := mergeEdges (groundEdges pins.names) (literalEdges pins.names records)
  let first := pre.records.foldl (fun acc (a, c) =>
    let o := owner a c
    if acc.contains o then acc else acc.push o) #[]
  return ⟨store, cx, extra, order store extra first⟩

/-- The outcome of one census run over `addresses` (in order). -/
structure Outcome where
  checker : Checker
  counts : Std.HashMap String Nat := {}
  reasons : Std.HashMap String Nat := {}
  failed : Std.HashMap Address Address := {}

/-- What the census loop needs to know about a record besides its reading:
its kind, the recursor records read with it, and the record owners it
depends on (computed only for a record that reads). -/
structure RecordView where
  kind : String
  recs : Array Address
  deps : Unit → Array Address

/-- A record's view in a census setup. -/
def Setup.view (s : Setup) (address : Address) : Option RecordView := do
  let source ← s.store[address]?
  pure { kind := kindOf source, recs := recursorRecords s.cx.index address,
         deps := fun _ => dependencies s.store s.cx.index s.extra address source }

/-- Check `addresses` in order, continuing past failures; each row is passed
to `emit`. `before` runs before each record's check (the watchdog's hook).
The records' views and readings come from `view` and `read`; the reading
state `σ` is threaded through `commit` after every reading that succeeds.
`onRead` sees every reading (the persistent read cache records them). -/
def censusLoopWith {σ : Type} (view : Address → Option RecordView)
    (read : σ → Address → Except ReadError Read) (commit : σ → Read → σ) (init : σ)
    (pins : List Ix.Kernel.NatOpPinSet) (names : Address → Array String)
    (addresses : Array Address) (skip : Std.HashSet String)
    (emit : Row → IO Unit) (before : Address → IO Unit := fun _ => pure ())
    (after : IO Unit := pure ()) (progress : Nat → Outcome → IO Unit := fun _ _ => pure ())
    (onRead : Address → Except ReadError Read → Nat → IO Unit := fun _ _ _ => pure ()) :
    IO Outcome := do
  let mut out : Outcome := { checker := {} }
  let mut st : σ := init
  let mut consumed : Std.HashSet Address := {}
  let mut index := 0
  for address in addresses do
    index := index + 1
    progress index out
    if consumed.contains address then continue
    let some v := view address | continue
    let recs := v.recs
    let rowsFor (outcome reason : String) (micros readMicros : Nat) : Array Row :=
      #[⟨address, names address, v.kind, outcome, reason, micros, readMicros⟩] ++
        recs.map fun r => ⟨r, names r, "recursor", outcome, reason, micros, readMicros⟩
    for r in recs do consumed := consumed.insert r
    let r0 ← IO.monoNanosNow
    let reading ← IO.lazyPure fun _ => read st address
    let readMicros := ((← IO.monoNanosNow) - r0) / 1000
    onRead address reading readMicros
    match reading with
    | .error e =>
      let (outcome, reason) := readOutcome e
      for row in rowsFor outcome reason 0 readMicros do
        out := { out with failed := out.failed.insert row.address row.address,
                          counts := out.counts.insert outcome (out.counts.getD outcome 0 + 1) }
        emit row
      out := { out with reasons := out.reasons.insert reason (out.reasons.getD reason 0 + 1) }
    | .ok rd =>
      -- the reader's state learns from every record it reads; what a failed
      -- record taught is read only by its dependents, which are blocked
      st := commit st rd
      let deps := v.deps ()
      match deps.find? out.failed.contains with
      | some blocker =>
        let root := out.failed.getD blocker blocker
        for row in rowsFor "blocked" (toString root) 0 readMicros do
          out := { out with failed := out.failed.insert row.address root,
                            counts := out.counts.insert "blocked" (out.counts.getD "blocked" 0 + 1) }
          emit row
      | none =>
        if skip.contains (toString address) then
          let reason := "census: skipped: exceeded the watchdog's limits on an earlier run"
          for row in rowsFor "decline" reason 0 readMicros do
            out := { out with failed := out.failed.insert row.address row.address,
                              counts := out.counts.insert "decline" (out.counts.getD "decline" 0 + 1) }
            emit row
          out := { out with reasons := out.reasons.insert reason (out.reasons.getD reason 0 + 1) }
          continue
        before address
        let t0 ← IO.monoNanosNow
        let checker := out.checker
        out := { out with checker := {} }
        let (checker, err) ← IO.lazyPure fun _ => checker.steps pins rd.decls
        let micros := ((← IO.monoNanosNow) - t0) / 1000
        after
        out := { out with checker }
        match err with
        | none =>
          for row in rowsFor "accept" "" micros readMicros do
            out := { out with counts := out.counts.insert "accept" (out.counts.getD "accept" 0 + 1) }
            emit row
        | some e =>
          let (outcome, reason) := checkOutcome e
          for row in rowsFor outcome reason micros readMicros do
            out := { out with failed := out.failed.insert row.address row.address,
                              counts := out.counts.insert outcome (out.counts.getD outcome 0 + 1) }
            emit row
          out := { out with reasons := out.reasons.insert reason (out.reasons.getD reason 0 + 1) }
  return out

/-- `censusLoopWith` over a census setup: each record is read by the reader
at the state the records before it left. -/
def censusLoop (s : Setup) (pins : List Ix.Kernel.NatOpPinSet) (names : Address → Array String)
    (addresses : Array Address) (skip : Std.HashSet String)
    (emit : Row → IO Unit) (before : Address → IO Unit := fun _ => pure ())
    (after : IO Unit := pure ()) (progress : Nat → Outcome → IO Unit := fun _ _ => pure ())
    (onRead : Address → Except ReadError Read → Nat → IO Unit := fun _ _ _ => pure ()) :
    IO Outcome :=
  censusLoopWith s.view
    (fun st address => match s.store[address]? with
      | some source => readRecord s.cx st address source
      | none => .error (.malformed "record is missing"))
    State.commit {} pins names addresses skip emit before after progress onRead

/-- Names by owning record, for reporting only (at most three). -/
def reportNames (env : Ixon.Env) (store : RecordStore) : Std.HashMap Address (Array String) := Id.run do
  let mut names : Std.HashMap Address (Array String) := {}
  for (name, named) in env.named.toList do
    let root := match store[named.addr]? with
      | some source => owner named.addr source
      | none => named.addr
    let current := names.getD root #[]
    if current.size < 3 then names := names.insert root (current.push (toString name))
  return names

end Benchmarks.Kernel.ConLecheStep
