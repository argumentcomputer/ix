import Ix.Ixon
import IxC.Kernel.Ixon.Prelude
import IxC.Kernel.Cached.Installed
import IxC.Kernel.NatOpPinSet

/-! # The verified fold one record at a time (untrusted harness)

The per-record step shared by the environment check (`Benchmarks.Kernel.CheckIxe`)
and the pin generator (`Benchmarks.Kernel.PinGen`): the dependency
order of an environment's primary records, the Ixon reader's declarations of
each record, and an incremental checker state that installs and checks
them one record at a time, continuing past failures.

**The order.** The prelude's records first, then a depth-first postorder
over table references with projections replaced by their owners, in which a
pinned `Nat` operation also depends on its certificate ground
(`natOpDeps`), as `Frontend.preparePrelude`'s hoist arranges, and a record
that contains a literal depends on the constants the literal references
(`Reader.literalEdges`: the `Nat` trio, and for a string literal the
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
this is a certified verdict; `Ix.Kernel.Admission.checkBytes` is. -/

namespace Benchmarks.Kernel.CheckIxeStep

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader

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
once, from the whole store, and every lookup is two probes. (A lookup
returned as a closure from a function of the store is compiled at the
function's full arity, so every call would rebuild the projection map over
all records.) -/
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

/-- What an environment-check run reads: the store, the reader context and the order. -/
structure Setup where
  store : RecordStore
  cx : Ctx
  extra : Std.HashMap Address (Array Address)
  ordered : Array Address

/-- The store backed by the prelude's records, the reader context, and the
order (the prelude's owners first). A store of record skeletons
(`CheckIxeStream`) passes `literals`: for every record of the store, a record
with the same literal kinds (`literalKinds`), from which the literal edges
are computed instead of from the store. -/
def setup (store : RecordStore) (blobs : Address → Option ByteArray)
    (pins : Pins) (pre : Prelude)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint)
    (literals : Option (Array (Address × Ixon.Constant)) := none) : Setup := Id.run do
  let mut store := store
  let mut added : Array (Address × Ixon.Constant) := #[]
  for (a, c) in pre.records do
    unless store.contains a do
      store := store.insert a c
      added := added.push (a, c)
  let records := store.toArray
  let index := buildIndex (store[·]?) pins.names records
  let cx : Ctx := { store := (store[·]?), blob := blobs, pins, index, hint,
                    keys := keyNamesOf (store[·]?) pins.names records }
  let literalRecords := match literals with
    | some ls => ls ++ added
    | none => records
  let extra := mergeEdges (groundEdges pins.names) (literalEdges pins.names literalRecords)
  let first := pre.records.foldl (fun acc (a, c) =>
    let o := owner a c
    if acc.contains o then acc else acc.push o) #[]
  return ⟨store, cx, extra, order store extra first⟩

/-- The outcome of one check loop over `addresses` (in order): the final
step state, the outcome and first-cause counts, and every failed or blocked
record with its root. -/
structure LoopOutcome (κ : Type) where
  checker : κ
  counts : Std.HashMap String Nat := {}
  reasons : Std.HashMap String Nat := {}
  failed : Std.HashMap Address Address := {}

/-- The outcome of an environment-check run with the per-record step. -/
abbrev Outcome := LoopOutcome Checker

/-- What the check loop needs to know about a record besides its reading:
its kind, the recursor records read with it, and the record owners it
depends on (computed only for a record that reads). -/
structure RecordView where
  kind : String
  recs : Array Address
  deps : Unit → Array Address

/-- A record's view in a check setup. -/
def Setup.view (s : Setup) (address : Address) : Option RecordView := do
  let source ← s.store[address]?
  pure { kind := kindOf source, recs := recursorRecords s.cx.index address,
         deps := fun _ => dependencies s.store s.cx.index s.extra address source }

/-- The per-record step as the check loop's step: install and check the
record's declarations (`Checker.steps`). -/
def Checker.stepRecord (pins : List Ix.Kernel.NatOpPinSet) (c : Checker) (_ : Address) (rd : Read) :
    Checker × Option Ix.Kernel.CheckError :=
  c.steps pins rd.decls

/-- Check `addresses` in order, continuing past failures; each row is passed
to `emit`. The records' views and readings come from `view` and `read`; the
reading state `σ` is threaded through `commit` after every reading that
succeeds. A record that reads, depends on no failed record and is not
skipped goes to `step`, which threads the step state `κ` and returns the
record's failure, if any (`Checker.stepRecord` for the per-record check;
`CheckIxePool` installs in one pass and replays in another). `before` and
`after` run around each step (the watchdog's hooks); `onRead` sees every
reading (the persistent read cache records them). -/
def checkLoopWith {σ κ : Type} [Inhabited κ] (view : Address → Option RecordView)
    (read : σ → Address → Except ReadError Read) (commit : σ → Address → Read → σ) (init : σ)
    (step : κ → Address → Read → κ × Option Ix.Kernel.CheckError) (start : κ)
    (names : Address → Array String)
    (addresses : Array Address) (skip : Std.HashSet String)
    (emit : Row → IO Unit) (before : Address → IO Unit := fun _ => pure ())
    (after : IO Unit := pure ()) (progress : Nat → LoopOutcome κ → IO Unit := fun _ _ => pure ())
    (onRead : Address → Except ReadError Read → Nat → IO Unit := fun _ _ _ => pure ()) :
    IO (LoopOutcome κ) := do
  let mut out : LoopOutcome κ := { checker := default }
  -- the reading state and the step state live in references of the loop's
  -- own, not in its mutable variables: the `for` loop's state tuple holds
  -- those while the body runs, so `commit` and `step` would see them shared
  -- and copy what they update
  let state ← IO.mkRef init
  let stepper ← IO.mkRef start
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
    let st ← state.get
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
      state.modify (commit · address rd)
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
          let reason := "check-ixe: skipped: exceeded the watchdog's limits on an earlier run"
          for row in rowsFor "decline" reason 0 readMicros do
            out := { out with failed := out.failed.insert row.address row.address,
                              counts := out.counts.insert "decline" (out.counts.getD "decline" 0 + 1) }
            emit row
          out := { out with reasons := out.reasons.insert reason (out.reasons.getD reason 0 + 1) }
          continue
        before address
        let t0 ← IO.monoNanosNow
        let checker ← stepper.modifyGet fun c => (c, default)
        let (checker, err) ← IO.lazyPure fun _ => step checker address rd
        let micros := ((← IO.monoNanosNow) - t0) / 1000
        after
        stepper.set checker
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
  return { out with checker := ← stepper.get }

/-- A record of a check setup, read by the reader at the state `st`. -/
def Setup.read (s : Setup) (st : State) (address : Address) : Except ReadError Read :=
  match s.store[address]? with
  | some source => readRecord s.cx st address source
  | none => .error (.malformed "record is missing")

/-- What a check loop reads from: the records' views, their readings, and
the reading state, whose initial value `init` builds on the loop's own
thread. -/
structure LoopSource (σ : Type) where
  view : Address → Option RecordView
  read : σ → Address → Except ReadError Read
  commit : σ → Address → Read → σ
  init : IO σ

/-- A check setup as a loop source: every record read from the setup's store. -/
def Setup.source (s : Setup) : LoopSource State :=
  { view := s.view, read := s.read, commit := fun st _ rd => st.commit rd, init := pure {} }

/-- `checkLoopWith` over a check setup with the per-record step: each record
is read by the reader at the state the records before it left. -/
def checkLoop (s : Setup) (pins : List Ix.Kernel.NatOpPinSet) (names : Address → Array String)
    (addresses : Array Address) (skip : Std.HashSet String)
    (emit : Row → IO Unit) (before : Address → IO Unit := fun _ => pure ())
    (after : IO Unit := pure ()) (progress : Nat → Outcome → IO Unit := fun _ _ => pure ())
    (onRead : Address → Except ReadError Read → Nat → IO Unit := fun _ _ _ => pure ()) :
    IO Outcome :=
  checkLoopWith s.view s.read (fun st _ rd => st.commit rd) {} (Checker.stepRecord pins) {}
    names addresses skip emit before after progress onRead

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

end Benchmarks.Kernel.CheckIxeStep
