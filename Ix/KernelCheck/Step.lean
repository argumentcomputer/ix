module

public import Ix.Ixon
public import IxC.Kernel.Ixon.Prelude
public import IxC.Kernel.Cached.Installed
public import IxC.Kernel.Admission
public import IxC.Kernel.Admission.Tier
public import Ix.Ixon.CheckOrder

@[expose] public section

/-! # The verified fold one record at a time (untrusted harness)

The per-record step shared by the environment check (`Benchmarks.Kernel.CheckIxe`)
and the pin generator (`Benchmarks.Kernel.PinGen`): the dependency
order of an environment's primary records, the Ixon reader's declarations of
each record, and an incremental checker state that installs and checks
them one record at a time, continuing past failures.

**The order.** The prelude's records first, then a depth-first postorder
over table references with projections replaced by their owners, in which a
certified `Nat` operation also depends on its certificate ground
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
structure Checker (md : Ix.Kernel.Mode) where
  fe : Ix.Kernel.FEnv md := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
  cs : Ix.Kernel.Cached.CState md := {}
  pos : Nat := 0

instance : Inhabited (Checker md) := ⟨{}⟩

/-- Install and check one declaration; on failure, the state before it. -/
def Checker.step (ev : Ix.Kernel.Evidences md) (c : Checker md) (d : Ix.Kernel.Declaration md) :
    Checker md × Option (Ix.Kernel.CheckError md) :=
  let ⟨fe, cs, pos⟩ := c
  let before := fe.env
  match Ix.Kernel.Cached.annotDeclStep .verified ev (pos, fe, #[]) d cs with
  | .error (e, _) => (⟨Ix.Kernel.mkFEnv before, {}, pos + 1⟩, some e)
  | .ok ((pos', fe', pend), cs') =>
    match Ix.Kernel.Cached.checkPendingList .verified fe' pend.toList with
    | .ok () => (⟨fe', cs', pos'⟩, none)
    | .error (e, _) => (⟨Ix.Kernel.mkFEnv before, {}, pos'⟩, some e)

/-- One record's declarations, in order; the first failure ends it. -/
def Checker.steps (ev : Ix.Kernel.Evidences md) (c : Checker md)
    (ds : Array (Ix.Kernel.Declaration md)) : Checker md × Option (Ix.Kernel.CheckError md) := Id.run do
  let mut c := c
  for d in ds do
    let (c', e) := c.step ev d
    c := c'
    if e.isSome then return (c, e)
  return (c, none)

/-- A checker failure's outcome and reason, its keys spelled by `spell` (by
default as `Key.toName` spells them, the `.anon` and `.source` spelling). -/
def checkOutcome (e : Ix.Kernel.CheckError md) (spell : Ix.Kernel.Key md → String := toString) :
    String × String :=
  match e with
  | .invalid m => ("reject", Ix.Kernel.Msg.render spell m)
  | .notImplemented m => ("decline", Ix.Kernel.Msg.render spell m)
  | .internal m => ("decline", s!"internal: {Ix.Kernel.Msg.render spell m}")

def readOutcome : ReadError → String × String
  | .malformed m => ("reject", s!"reader: {m}")
  | .declined m => ("decline", s!"reader: {m}")

/-! ## Records and order -/

export Ixon.CheckOrder (RecordStore owner order closure recursorRecords dependencies groundEdges
  mergeEdges)

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
  cx : Ctx .anon
  extra : Std.HashMap Address (Array Address)
  ordered : Array Address
  /-- the role table the setup reads under -/
  table : Ix.Kernel.RoleTable := default
  /-- the table's evidence, resolved against the prelude's reading state
  (a theorem's value reads the same at every state: the projection rewrite
  applies only to projection functions) -/
  evidence : Ix.Kernel.Evidences .anon := []

/-- The store backed by the prelude's records, the reader context, and the
order (the prelude's owners first). A store of record skeletons
(`CheckIxeStream`) passes `literals`: for every record of the store, a record
with the same literal kinds (`literalKinds`), from which the literal edges
are computed instead of from the store. -/
def setup (store : RecordStore) (blobs : Address → Option ByteArray)
    (t : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint)
    (literals : Option (Array (Address × Ixon.Constant)) := none) : Setup := Id.run do
  let mut store := store
  let mut added : Array (Address × Ixon.Constant) := #[]
  for (a, c) in pre.records do
    unless store.contains a do
      store := store.insert a c
      added := added.push (a, c)
  let records := store.toArray
  let blobs' : Address → Option ByteArray := fun a =>
    blobs a <|> (pre.blobs.find? (·.1 == a)).map (·.2)
  -- the evidence records back the reader's store only: they are not records
  -- of the run (not ordered, not checked)
  let evidence : Std.HashMap Address Ixon.Constant := pre.evidence.foldl
    (fun m (a, c) => if store.contains a then m else m.insert a c) {}
  let look : Address → Option Ixon.Constant := fun a => store[a]? <|> evidence[a]?
  let cx : Ctx .anon := contextWith look blobs' t records hint
    (Ix.Kernel.Admission.projectionAddress Address.blake3 look)
  let roles := cx.roles
  let literalRecords := match literals with
    | some ls => ls ++ added
    | none => records
  let extra := mergeEdges (groundEdges roles.names) (literalEdges roles.names literalRecords)
  let first := pre.records.foldl (fun acc (a, c) =>
    let o := owner a c
    if acc.contains o then acc else acc.push o) #[]
  return ⟨store, cx, extra, order store extra first, t, evidenceOf cx pre.state t⟩

/-- The outcome of one check loop over `addresses` (in order): the final
step state, the outcome and first-cause counts, and every failed or blocked
record with its root. -/
structure LoopOutcome (κ : Type) where
  checker : κ
  counts : Std.HashMap String Nat := {}
  reasons : Std.HashMap String Nat := {}
  failed : Std.HashMap Address Address := {}

/-- The outcome of an environment-check run with the per-record step. -/
abbrev Outcome := LoopOutcome (Checker .anon)

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

/-! ## The typing tier

The drivers' half of `Ix.Kernel.Admission.checkBytesTiered`: a tier record
(`Admission.isTierInfo`: a partial or unsafe definition or block, an unsafe
opaque or axiom) is read by the tier reader (`Admission.readTierRecord`) at
its turn and deferred; after the logical loop, the deferred records are
checked by the tier fold's step (`Tier.checkDeclC`), staged as the tier fold
stages them (`Tier.staged`: partial blocks, then unsafe opaques at the
logical view, then the rest), from the final step state's index, each at the
index the ones before it extended, a failure rolled back. A tier record that depends
on a failed record is blocked; a logical record that names a deferred tier
record is declined (`fence: …`). A typed row's outcome is `typed`, its reason
the safety (`partial`, `unsafe`); a tier failure declines, `tier (<safety>): …`. -/

/-- What a check loop needs to run the typing tier: a record's tier
declaration, read at its turn (`none`: not a tier record), and the index of
the step state's environment. -/
structure TierHook (σ κ : Type) where
  read : σ → Address → Option (Except ReadError (Ix.Kernel.Tier.TierDecl .anon))
  index : κ → Ix.Kernel.FEnv .anon

/-- A tier record's declaration, read against `cx` (`none`: not a tier record). -/
def readTierAt (cx : Ctx md) (address : Address) (source : Ixon.Constant) :
    Option (Except ReadError (Ix.Kernel.Tier.TierDecl md)) :=
  if Ix.Kernel.Admission.isTierInfo source.info then
    some <| match Ix.Kernel.Admission.readTierRecord cx address source with
      | .ok (some d) => .ok d
      | .ok none => .error (.malformed "a tier record without a declaration")
      | .error e => .error e
  else none

/-- One tier declaration at `fe`, with `fe₀` the logical view (the index before
any tier constant); a failure leaves the index as it was (rebuilt from its
environment, as `Checker.step` rolls back). -/
def stepTier (fe₀ fe : Ix.Kernel.FEnv md) (d : Ix.Kernel.Tier.TierDecl md) :
    Ix.Kernel.FEnv md × Option (Ix.Kernel.CheckError md) :=
  let before := fe.env
  match Ix.Kernel.Tier.checkDeclC fe₀ fe d with
  | .ok (fe', _) => (fe', none)
  | .error e => (Ix.Kernel.mkFEnv before, some e)

/-- A tier declaration's safety. -/
def tierSafety (d : Ix.Kernel.Tier.TierDecl md) : Ix.Kernel.Tier.Safety := d.safety

/-- Deferred tier records in the tier fold's staged order (`Tier.staged`):
partial blocks, then unsafe opaques, then unsafe blocks and axioms, each in
the order they came. -/
def stageDeferred {α : Type} (decl : α → Ix.Kernel.Tier.TierDecl md) (xs : Array α) : Array α :=
  xs.filter (fun x => (decl x).stage == 0) ++ xs.filter (fun x => (decl x).stage == 1) ++
    xs.filter (fun x => (decl x).stage == 2)

/-- A tier failure's outcome and reason: always a decline (IxC cannot tell an
ill-typed tier declaration from one that types only by unfolding a tier
definition), the checker's message under `tier (<safety>)`. -/
def tierOutcome (s : Ix.Kernel.Tier.Safety) (e : Ix.Kernel.CheckError md)
    (spell : Ix.Kernel.Key md → String := toString) : String × String :=
  ("decline", s!"tier ({s.word}): {(checkOutcome e spell).2}")

/-- The per-record step as the check loop's step: install and check the
record's declarations (`Checker.steps`). -/
def Checker.stepRecord (ev : Ix.Kernel.Evidences .anon) (c : Checker .anon) (_ : Address) (rd : Read .anon) :
    Checker .anon × Option (Ix.Kernel.CheckError .anon) :=
  c.steps ev rd.decls

/-- Check `addresses` in order, continuing past failures; each row is passed
to `emit`. The records' views and readings come from `view` and `read`; the
reading state `σ` is threaded through `commit` after every reading that
succeeds. A record that reads, depends on no failed record and is not
skipped goes to `step`, which threads the step state `κ` and returns the
record's failure, if any (`Checker.stepRecord` for the per-record check;
`CheckIxePool` installs in one pass and replays in another). `before` and
`after` run around each step (the watchdog's hooks); `onRead` sees every
reading (the persistent read cache records them); `spell` spells the keys of
a checker failure's reason (`kernel-check-ixe` passes the `.meta` renderer,
`Reader.spellWith`, over the `.ixe`'s display table). With `tier`, the tier
records are deferred and checked by the typing tier after the loop
(`TierHook`); without it, the logical reader declines them, as before. -/
def checkLoopWith {σ κ : Type} [Inhabited κ] (view : Address → Option RecordView)
    (read : σ → Address → Except ReadError (Read .anon)) (commit : σ → Address → Read .anon → σ) (init : σ)
    (step : κ → Address → Read .anon → κ × Option (Ix.Kernel.CheckError .anon)) (start : κ)
    (names : Address → Array String)
    (addresses : Array Address) (skip : Std.HashSet String)
    (emit : Row → IO Unit) (before : Address → IO Unit := fun _ => pure ())
    (after : IO Unit := pure ()) (progress : Nat → LoopOutcome κ → IO Unit := fun _ _ => pure ())
    (onRead : Address → Except ReadError (Read .anon) → Nat → IO Unit := fun _ _ _ => pure ())
    (spell : Ix.Kernel.Key .anon → String := toString)
    (tier : Option (TierHook σ κ) := none) :
    IO (LoopOutcome κ) := do
  let mut out : LoopOutcome κ := { checker := default }
  -- the reading state and the step state live in references of the loop's
  -- own, not in its mutable variables: the `for` loop's state tuple holds
  -- those while the body runs, so `commit` and `step` would see them shared
  -- and copy what they update
  let state ← IO.mkRef init
  let stepper ← IO.mkRef start
  let mut consumed : Std.HashSet Address := {}
  -- the tier records, deferred in order: address, view, declaration,
  -- dependencies, reading time
  let mut deferred : Array (Address × RecordView × Ix.Kernel.Tier.TierDecl .anon × Array Address × Nat) := #[]
  let mut deferredSet : Std.HashSet Address := {}
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
    -- a tier record: read by the tier reader and deferred
    let tr? ← IO.lazyPure fun _ => tier.bind (·.read st address)
    if let some tr := tr? then
      let readMicros := ((← IO.monoNanosNow) - r0) / 1000
      match tr with
      | .error e =>
        let (outcome, reason) := readOutcome e
        for row in rowsFor outcome reason 0 readMicros do
          out := { out with failed := out.failed.insert row.address row.address,
                            counts := out.counts.insert outcome (out.counts.getD outcome 0 + 1) }
          emit row
        out := { out with reasons := out.reasons.insert reason (out.reasons.getD reason 0 + 1) }
      | .ok d =>
        let deps := v.deps ()
        match deps.find? out.failed.contains with
        | some blocker =>
          let root := out.failed.getD blocker blocker
          for row in rowsFor "blocked" (toString root) 0 readMicros do
            out := { out with failed := out.failed.insert row.address root,
                              counts := out.counts.insert "blocked" (out.counts.getD "blocked" 0 + 1) }
            emit row
        | none =>
          deferred := deferred.push (address, v, d, deps, readMicros)
          deferredSet := deferredSet.insert address
      continue
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
        -- the fence: a logical record that names a tier record
        if let some t := deps.find? deferredSet.contains then
          let reason := s!"fence: names the tier record {t}"
          for row in rowsFor "decline" reason 0 readMicros do
            out := { out with failed := out.failed.insert row.address row.address,
                              counts := out.counts.insert "decline" (out.counts.getD "decline" 0 + 1) }
            emit row
          out := { out with reasons := out.reasons.insert "fence" (out.reasons.getD "fence" 0 + 1) }
          continue
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
          let (outcome, reason) := checkOutcome e spell
          for row in rowsFor outcome reason micros readMicros do
            out := { out with failed := out.failed.insert row.address row.address,
                              counts := out.counts.insert outcome (out.counts.getD outcome 0 + 1) }
            emit row
          out := { out with reasons := out.reasons.insert reason (out.reasons.getD reason 0 + 1) }
  let checker ← stepper.get
  -- the typing tier, staged, from the final step state's index (also the
  -- logical view of the unsafe opaques)
  if let some th := tier then
    let logical := th.index checker
    let fe ← IO.mkRef logical
    for (address, v, d, deps, readMicros) in stageDeferred (·.2.2.1) deferred do
      let row (outcome reason : String) (micros : Nat) : Row :=
        ⟨address, names address, v.kind, outcome, reason, micros, readMicros⟩
      match deps.find? out.failed.contains with
      | some blocker =>
        let root := out.failed.getD blocker blocker
        out := { out with failed := out.failed.insert address root,
                          counts := out.counts.insert "blocked" (out.counts.getD "blocked" 0 + 1) }
        emit (row "blocked" (toString root) 0)
      | none =>
        let t0 ← IO.monoNanosNow
        let fe₀ ← fe.modifyGet fun x => (x, Ix.Kernel.mkFEnv Ix.Kernel.Env.empty)
        let (fe₁, err) ← IO.lazyPure fun _ => stepTier logical fe₀ d
        fe.set fe₁
        let micros := ((← IO.monoNanosNow) - t0) / 1000
        match err with
        | none =>
          out := { out with counts := out.counts.insert "typed" (out.counts.getD "typed" 0 + 1) }
          emit (row "typed" (tierSafety d).word micros)
        | some e =>
          let (outcome, reason) := tierOutcome (tierSafety d) e spell
          out := { out with failed := out.failed.insert address address,
                            counts := out.counts.insert outcome (out.counts.getD outcome 0 + 1),
                            reasons := out.reasons.insert reason (out.reasons.getD reason 0 + 1) }
          emit (row outcome reason micros)
  return { out with checker := checker }

/-- A record of a check setup, read by the reader at the state `st`. -/
def Setup.read (s : Setup) (st : State .anon) (address : Address) : Except ReadError (Read .anon) :=
  match s.store[address]? with
  | some source => readRecord s.cx st address source
  | none => .error (.malformed "record is missing")

/-- What a check loop reads from: the records' views, their readings, and
the reading state, whose initial value `init` builds on the loop's own
thread. -/
structure LoopSource (σ : Type) where
  view : Address → Option RecordView
  read : σ → Address → Except ReadError (Read .anon)
  commit : σ → Address → Read .anon → σ
  init : IO σ
  /-- the tier reader (`TierHook.read`), if the source runs the typing tier -/
  tier : Option (σ → Address → Option (Except ReadError (Ix.Kernel.Tier.TierDecl .anon))) := none

/-- A record of a check setup, read by the tier reader if it is a tier record. -/
def Setup.tierRead (s : Setup) (address : Address) :
    Option (Except ReadError (Ix.Kernel.Tier.TierDecl .anon)) :=
  match s.store[address]? with
  | some source => readTierAt s.cx address source
  | none => none

/-- A check setup as a loop source: every record read from the setup's store,
a tier record by the tier reader. -/
def Setup.source (s : Setup) : LoopSource (State .anon) :=
  { view := s.view, read := s.read, commit := fun st _ rd => st.commit rd, init := pure {},
    tier := some fun _ a => s.tierRead a }

/-- The per-record check's tier hook over a source's tier reader. -/
def LoopSource.tierHook (src : LoopSource σ) : Option (TierHook σ (Checker .anon)) :=
  src.tier.map fun r => { read := r, index := (·.fe) }

/-- `checkLoopWith` over a check setup with the per-record step: each record
is read by the reader at the state the records before it left; with `tier`,
the tier records are checked by the typing tier after the loop. -/
def checkLoop (s : Setup) (names : Address → Array String)
    (addresses : Array Address) (skip : Std.HashSet String)
    (emit : Row → IO Unit) (before : Address → IO Unit := fun _ => pure ())
    (after : IO Unit := pure ()) (progress : Nat → Outcome → IO Unit := fun _ _ => pure ())
    (onRead : Address → Except ReadError (Read .anon) → Nat → IO Unit := fun _ _ _ => pure ())
    (tier : Bool := false) :
    IO Outcome :=
  checkLoopWith s.view s.read (fun st _ rd => st.commit rd) {} (Checker.stepRecord s.evidence) {}
    names addresses skip emit before after progress onRead
    (tier := if tier then s.source.tierHook else none)

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
