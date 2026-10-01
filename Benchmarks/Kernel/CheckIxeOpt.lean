/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.CheckIxe

/-! # Driver-side optimizations of the environment check, measured (untrusted prototype)

`kernel-check-ixe-opt` is `kernel-check-ixe` (`Benchmarks.Kernel.CheckIxe`)
with switches for four driver-side ports, none of which touches the verified
core or the reader. It exists to measure them (`plans/review/cl-opt/`), and it
is not a certified verdict.

* `CHECK_IXE_LOAD=stream`: the metadata-light lazy load Ix.Tc uses
  (`Ixon.deEnvAnon`: the `.ixe` stays one buffer, names map to addresses, no
  metadata is decoded). Every record is decoded once up front for its
  skeleton (`skeleton`: the tables and expressions the environment check and the reader
  read of a record *other* than the one being read: info tags, references,
  recursors in full, constructor counts) and decoded again, in full, only
  when its turn comes; nothing decoded is kept but the skeletons. The default
  `CHECK_IXE_LOAD=full` is `kernel-check-ixe`'s eager `Ixon.deEnv` with every
  record decoded and kept.
* `CHECK_IXE_THREAD=1`: the check loop runs on one dedicated worker thread, so
  the checker allocates out of a fresh heap instead of the main thread's, which
  holds the decoded environment (con-leche task #269: 2.06x on a 2 GB Mathlib
  prefix at the same instruction count).
* `CHECK_IXE_MARK=1`: the store, the reader context and the order are marked
  persistent before the loop (con-leche task #265), so their reference counts
  are never touched again.
* `CHECK_IXE_PAR=n1,n2,…`: instead of the per-constant check, con-leche's two
  phases (`Cached.checkDecls`): phase A installs every record in order
  (`annotDeclStep`; a record whose reading or install fails, and every record
  that depends on it, is left out, as the environment check blocks it), then phase B
  checks the recorded declarations (`Cached.checkPending` from a fresh memo
  state, which is `Cached.checkRecord`'s computation) on a pool of `n`
  dedicated worker threads claiming one record at a time off a shared counter
  (con-leche `Main.lean`'s `checkPool`, task #260), once for every `n` listed.
  The installed environment and the records are marked persistent first
  (task #265). `PAR_MAIN=1` also runs phase B once on the calling thread.
  `PAR_ROWS=<file>` writes one JSONL row per recorded check of the first
  pool run (`address`, `micros`, `ok`).

The check rows (`address, names, kind, outcome, reason, micros,
readMicros`) are `kernel-check-ixe`'s. Every stage boundary prints the resident
set (`rss`) and its peak (`hwm`). -/

namespace Benchmarks.Kernel.CheckIxeOpt

open Ix.Kernel (ConstRef)
open Ix.Kernel.IxonReader
open Benchmarks.Kernel.CheckIxeStep

def rssMb : IO Nat := return (← statusKb "VmRSS:") / 1024
def hwmMb : IO Nat := return (← statusKb "VmHWM:") / 1024

def stage (started : Nat) (what : String) : IO Unit := do
  IO.eprintln s!"check-ixe-opt: {what} at {(← IO.monoMsNow) - started} ms; rss {← rssMb} MB, hwm {← hwmMb} MB"

/-! ## Skeletons -/

def stubExpr : Ixon.Expr := .sort 0

def stubDefn (d : Ixon.Definition) : Ixon.Definition := { d with typ := stubExpr, value := stubExpr }

def stubInd (i : Ixon.Inductive) : Ixon.Inductive :=
  { i with typ := stubExpr, ctors := i.ctors.map fun c => { c with typ := stubExpr } }

/-- What the environment check and the reader read of a record other than the one being
read: its info tag and kind (`owner`, `kindOf`, `resolveSource`), its
references (`order`, `dependencies`), an inductive's constructor count
(`inductiveAt`), and recursor records in full (`buildIndex` reads their
types; an inductive block is read with its recursor records). Expressions,
sharing and universe tables are dropped from everything else. -/
def skeleton (c : Ixon.Constant) : Ixon.Constant :=
  match c.info with
  | .defn d => { c with info := .defn (stubDefn d), sharing := #[], univs := #[] }
  | .axio a => { c with info := .axio { a with typ := stubExpr }, sharing := #[], univs := #[] }
  | .quot q => { c with info := .quot { q with typ := stubExpr }, sharing := #[], univs := #[] }
  | .muts ms =>
    if ms.any (fun | .recr _ => true | _ => false) then c
    else
      { c with
        info := .muts (ms.map fun
          | .defn d => .defn (stubDefn d)
          | .indc i => .indc (stubInd i)
          | .recr r => .recr r)
        sharing := #[], univs := #[] }
  | _ => c

/-- A stand-in that `literalKinds` reads as the original's literal kinds. -/
def literalStandIn (nat str : Bool) : Ixon.Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ := stubExpr }
    sharing := (if nat then #[Ixon.Expr.nat 0] else #[]) ++ (if str then #[Ixon.Expr.str 0] else #[])
    refs := #[], univs := #[] }

/-- The store, the setup and the record source of a run. -/
structure Loaded where
  env : Ixon.Env
  setup : Setup
  /-- the full record at an address (decoded on demand in stream mode) -/
  fetchPure : Address → Option Ixon.Constant
  /-- the same, in `IO`: in `stream-free` mode the record's bytes are
  released once it is fetched -/
  fetch : Address → IO (Option Ixon.Constant) := fun a => pure (fetchPure a)

/-- `CheckIxeStep.setup` with the literal edges supplied. -/
def setupWith (store : RecordStore) (blobs : Address → Option ByteArray) (pins : Pins) (pre : Prelude)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint)
    (lits : Array (Address × Ixon.Constant)) : Setup := Id.run do
  let mut store := store
  for (a, c) in pre.records do
    unless store.contains a do store := store.insert a c
  let records := store.toArray
  let index := buildIndex (store[·]?) pins.names records
  let cx : Ctx := { store := (store[·]?), blob := blobs, pins, index, hint }
  let extra := mergeEdges (groundEdges pins.names) (literalEdges pins.names lits)
  let first := pre.records.foldl (fun acc (a, c) =>
    let o := owner a c
    if acc.contains o then acc else acc.push o) #[]
  return ⟨store, cx, extra, order store extra first⟩

def loadFull (started : Nat) (bytes : ByteArray) (pins : Pins) (pre : Prelude) : IO Loaded := do
  let env ← IO.ofExcept (Ixon.deEnv bytes)
  stage started "decoded (deEnv)"
  let mut store : RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) pins pre hints.lookup
  stage started "setup"
  return { env, setup := s, fetchPure := (s.store[·]?) }

def loadStream (started : Nat) (bytes : ByteArray) (pins : Pins) (pre : Prelude) (free : Bool) :
    IO Loaded := do
  let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
  stage started "loaded (deEnvAnon)"
  let mut raw : Std.HashMap Address (IO.Ref (Option ByteArray)) := {}
  let mut store : RecordStore := {}
  let mut lits : Array (Address × Ixon.Constant) := #[]
  let mut canon : Std.HashMap Address Address := {}
  for (address, lazy) in env.consts.toList do
    let c ← IO.ofExcept lazy.get
    if free then raw := raw.insert address (← IO.mkRef (some lazy.rawBytes))
    let (nat, str) := literalKinds c
    if nat || str then lits := lits.push (address, literalStandIn nat str)
    let sk := skeleton c
    let mut refs : Array Address := Array.mkEmpty sk.refs.size
    for r in sk.refs do
      match canon[r]? with
      | some r' => refs := refs.push r'
      | none => canon := canon.insert r r; refs := refs.push r
    store := store.insert address { sk with refs }
  stage started s!"skeletons ({store.size} records, {lits.size} with literals)"
  let hints := Hints.ofStore store env.anonHints
  let s := setupWith store (env.blobs[·]?) pins pre hints.lookup lits
  stage started "setup"
  if free then
    -- the shared buffer goes with the slices; each record keeps its own
    -- bytes, in a reference of its own, until it is fetched. (Not a map
    -- erased from: the loop's thread sees the map marked multi-threaded,
    -- and the runtime copies a multi-threaded map on every `erase`.)
    let env := { env with consts := {} }
    let skel := s.store
    let fetch : Address → IO (Option Ixon.Constant) := fun a => do
      match raw[a]? with
      | some r =>
        match ← r.modifyGet fun v => (v, none) with
        | some b => pure (Ixon.deConstant b).toOption
        | none => pure skel[a]?
      | none => pure skel[a]?
    stage started s!"per-record bytes ({raw.size} records), shared buffer released"
    return { env, setup := s, fetchPure := fun _ => none, fetch }
  let consts := env.consts
  let fetchPure : Address → Option Ixon.Constant := fun a =>
    match consts[a]? with
    | some lc => lc.get.toOption
    | none => s.store[a]?
  return { env, setup := s, fetchPure }

/-! ## Cross-record interning (`CHECK_IXE_INTERN`)

The Ixon reader builds every record's terms afresh: a constant's name
(`ix.<hex>.i`) is a new object at every occurrence, and nothing is shared
across records, where con-leche's NDJSON parser shares names, levels and
terms stream-wide (its task #78). `CHECK_IXE_INTERN=names` replaces every name
and level in a record's declarations by one canonical object per value;
`CHECK_IXE_INTERN=all` also hash-conses the expressions (one object per
structurally equal subterm across the run). Values are unchanged, only
sharing, so no verdict can move; the tables are host state. -/

structure Interner where
  names : Std.HashMap Ix.Kernel.Name Ix.Kernel.Name := {}
  levels : Std.HashMap Ix.Kernel.Level Ix.Kernel.Level := {}
  exprs : Std.HashMap Ix.Kernel.Expr Ix.Kernel.Expr := {}
  terms : Bool := false
  deriving Inhabited

/-- The interning walk's state: the tables and the record's pointer memo. -/
abbrev InternM := StateM (Interner × Std.HashMap USize Ix.Kernel.Expr)

def internN (n : Ix.Kernel.Name) : InternM Ix.Kernel.Name := do
  match (← get).1.names[n]? with
  | some n' => pure n'
  | none => modify (fun (t, m) => ({ t with names := t.names.insert n n }, m)); pure n

partial def internL (u : Ix.Kernel.Level) : InternM Ix.Kernel.Level := do
  match (← get).1.levels[u]? with
  | some u' => pure u'
  | none =>
    let u' ← match u with
      | .zero => pure u
      | .succ v => do pure (.succ (← internL v))
      | .max a b => do pure (.max (← internL a) (← internL b))
      | .imax a b => do pure (.imax (← internL a) (← internL b))
      | .param n => do pure (.param (← internN n))
    modify (fun (t, m) => ({ t with levels := t.levels.insert u' u' }, m))
    pure u'

unsafe def internE (e : Ix.Kernel.Expr) : InternM Ix.Kernel.Expr := do
  let p := ptrAddrUnsafe e
  if let some r := (← get).2[p]? then return r
  let r ← match e with
    | .bvar _ | .lit _ => pure e
    | .fvar i t => do pure (.fvar i (← internE t))
    | .sort u => do pure (.sort (← internL u))
    | .const n us => do pure (.const (← internN n) (← us.mapM internL))
    | .app f a => do pure (.app (← internE f) (← internE a))
    | .lam t b m => do pure (.lam (← internE t) (← internE b) m)
    | .forallE t b m => do pure (.forallE (← internE t) (← internE b) m)
    | .letE t v b => do pure (.letE (← internE t) (← internE v) (← internE b))
    | .proj sn i x => do pure (.proj (← internN sn) i (← internE x))
  let t := (← get).1
  let r ← if t.terms then
      match t.exprs[r]? with
      | some r' => pure r'
      | none => modify (fun (t, m) => ({ t with exprs := t.exprs.insert r r }, m)); pure r
    else pure r
  modify fun (t, m) => (t, m.insert p r)
  return r

unsafe def internCV (cv : Ix.Kernel.ConstantVal) : InternM Ix.Kernel.ConstantVal := do
  pure { cv with name := ← internN cv.name, levelParams := ← cv.levelParams.mapM internN,
                 type := ← internE cv.type }

unsafe def internDecl : Ix.Kernel.Declaration → InternM Ix.Kernel.Declaration
  | .axiomDecl cv => do pure (.axiomDecl (← internCV cv))
  | .defnDecl cv v h => do pure (.defnDecl (← internCV cv) (← internE v) h)
  | .thmDecl cv v => do pure (.thmDecl (← internCV cv) (← internE v))
  | .opaqueDecl cv v => do pure (.opaqueDecl (← internCV cv) (← internE v))
  | d => pure d

/-- A record's declarations, interned; the record's pointer memo is dropped. -/
unsafe def internDeclsImpl (t : Interner) (ds : Array Ix.Kernel.Declaration) :
    Array Ix.Kernel.Declaration × Interner :=
  let (ds', (t', _)) := (ds.mapM internDecl).run (t, {})
  (ds', t')

@[implemented_by internDeclsImpl]
opaque internDecls (t : Interner) (ds : Array Ix.Kernel.Declaration) :
    Array Ix.Kernel.Declaration × Interner

/-! ## What the environment holds (`CHECK_IXE_SIZE`)

A walk over the expression DAGs reachable from the installed constants and
the reader's state, counting each node once (by address) with an estimate
of its heap size (Lean object header, pointer fields, the packed data word;
names, levels and literals are not counted). Roots are taken in layers, so
each layer counts only the nodes the earlier layers did not reach. -/

structure Sized where
  nodes : Nat := 0
  bytes : Nat := 0

def nodeBytes : Ix.Kernel.Expr → Nat
  | .bvar _ | .sort _ | .lit _ => 24
  | .fvar _ _ | .const _ _ | .app _ _ => 32
  | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _ | .proj _ _ _ => 48

unsafe def sizeWalk (seen : Std.HashSet USize) (acc : Sized) (e : Ix.Kernel.Expr) :
    Std.HashSet USize × Sized := Id.run do
  let mut seen := seen
  let mut acc := acc
  let mut todo : Array Ix.Kernel.Expr := #[e]
  while h : todo.size > 0 do
    let e := todo[todo.size - 1]
    todo := todo.pop
    let p := ptrAddrUnsafe e
    if seen.contains p then continue
    seen := seen.insert p
    acc := { nodes := acc.nodes + 1, bytes := acc.bytes + nodeBytes e }
    match e with
    | .fvar _ t => todo := todo.push t
    | .app f a => todo := (todo.push f).push a
    | .lam t b _ | .forallE t b _ => todo := (todo.push t).push b
    | .letE t v b => todo := ((todo.push t).push v).push b
    | .proj _ _ x => todo := todo.push x
    | _ => pure ()
  return (seen, acc)

unsafe def envLayersImpl (consts : List Ix.Kernel.ConstantInfo)
    (stateTypes : Array Ix.Kernel.Expr) : List (String × Sized) := Id.run do
  let layer (seen : Std.HashSet USize) (es : Array Ix.Kernel.Expr) : Std.HashSet USize × Sized :=
    es.foldl (fun (seen, acc) e => sizeWalk seen acc e) (seen, {})
  let types := consts.toArray.map (·.toConstantVal.type)
  let defnValues := consts.toArray.filterMap fun | .defnInfo _ v _ => some v | _ => none
  let ruleRhss := consts.toArray.flatMap fun
    | .recInfo _ _ _ rules => rules.toArray.map (·.rhs) | _ => #[]
  let thmValues := consts.toArray.filterMap fun | .thmInfo _ v => some v | _ => none
  let (seen, a) := layer {} types
  let (seen, b) := layer seen defnValues
  let (seen, c) := layer seen ruleRhss
  let (seen, d) := layer seen thmValues
  let (_, e) := layer seen stateTypes
  return [("constant types", a), ("definition values", b), ("recursor rules", c),
          ("theorem values", d), ("reader state types beyond the environment", e)]

@[implemented_by envLayersImpl]
opaque envLayers (consts : List Ix.Kernel.ConstantInfo) (stateTypes : Array Ix.Kernel.Expr) :
    List (String × Sized)

/-! ## Term statistics (`CHECK_IXE_STATS`) -/

structure Stats where
  nodes : Nat := 0
  apps : Nat := 0
  binders : Nat := 0
  lets : Nat := 0
  refNodes : Nat := 0
  nats : Nat := 0
  natBytes : Nat := 0
  strs : Nat := 0
  prjs : Nat := 0

/-- Node counts of one Ixon expression, not descending into sharing
references (each sharing entry is counted once, by itself). -/
partial def exprStats (blobSize : UInt64 → Nat) (st : Stats) : Ixon.Expr → Stats
  | .share _ => st
  | .sort _ | .var _ => { st with nodes := st.nodes + 1 }
  | .ref _ _ | .recur _ _ => { st with nodes := st.nodes + 1, refNodes := st.refNodes + 1 }
  | .prj _ _ v => exprStats blobSize { st with nodes := st.nodes + 1, prjs := st.prjs + 1 } v
  | .str _ => { st with nodes := st.nodes + 1, strs := st.strs + 1 }
  | .nat i => { st with nodes := st.nodes + 1, nats := st.nats + 1,
                        natBytes := max st.natBytes (blobSize i) }
  | .app f a => exprStats blobSize (exprStats blobSize { st with nodes := st.nodes + 1, apps := st.apps + 1 } f) a
  | .lam _ t b | .all _ _ t b =>
    exprStats blobSize (exprStats blobSize { st with nodes := st.nodes + 1, binders := st.binders + 1 } t) b
  | .letE _ t v b =>
    exprStats blobSize (exprStats blobSize (exprStats blobSize
      { st with nodes := st.nodes + 1, lets := st.lets + 1 } t) v) b

def constantStats (blobs : Address → Option ByteArray) (c : Ixon.Constant) : Stats :=
  let blobSize (i : UInt64) : Nat := match c.refs[i.toNat]? with
    | some a => ((blobs a).map (·.size)).getD 0
    | none => 0
  let roots : Array Ixon.Expr := match c.info with
    | .defn d => #[d.typ, d.value]
    | .recr r => #[r.typ] ++ r.rules.map (·.rhs)
    | .axio a => #[a.typ]
    | .quot q => #[q.typ]
    | .muts ms => ms.flatMap fun
      | .defn d => #[d.typ, d.value]
      | .indc i => #[i.typ] ++ i.ctors.map (·.typ)
      | .recr r => #[r.typ] ++ r.rules.map (·.rhs)
    | _ => #[]
  (c.sharing ++ roots).foldl (exprStats blobSize) {}

/-- `CHECK_IXE_STATS=<file>`: for every address listed in the file (one per
line), its record's term statistics and the names of the constants it
references, one JSON row each. -/
def runStats (bytes : ByteArray) (list output : System.FilePath) : IO UInt32 := do
  let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
  -- every name of an address (alpha-equivalent constants share one), at most four
  let namesOf : Std.HashMap Address (Array String) := env.named.fold (init := {}) fun m n named =>
    let cur := m.getD named.addr #[]
    if cur.size < 4 then m.insert named.addr (cur.push (toString n)) else m
  let h ← IO.FS.Handle.mk output .write
  for line in (← IO.FS.readFile list).splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty then continue
    let some a := Address.fromString line | IO.eprintln s!"check-ixe-opt: bad address {line}"
    let some lc := env.consts[a]? | IO.eprintln s!"check-ixe-opt: no record {line}"
    let c ← IO.ofExcept lc.get
    let st := constantStats (env.blobs[·]?) c
    let refNames := c.refs.toList.flatMap fun r => ((namesOf[r]?).getD #[]).toList
    h.putStrLn (Lean.Json.mkObj [
      ("address", Lean.toJson line), ("kind", Lean.toJson (kindOf c)),
      ("sharing", Lean.toJson c.sharing.size), ("refs", Lean.toJson c.refs.size),
      ("univs", Lean.toJson c.univs.size), ("nodes", Lean.toJson st.nodes),
      ("apps", Lean.toJson st.apps), ("binders", Lean.toJson st.binders),
      ("lets", Lean.toJson st.lets), ("refNodes", Lean.toJson st.refNodes),
      ("nats", Lean.toJson st.nats), ("natBytes", Lean.toJson st.natBytes),
      ("strs", Lean.toJson st.strs), ("prjs", Lean.toJson st.prjs),
      ("refNames", Lean.toJson refNames)]).compress
  return 0

/-! ## The check loop, with the record fetched in full -/

/-- `CheckIxeStep.checkLoop`, except that the record being read is
`fetch`ed (decoded in full) while the store holds skeletons. -/
def checkLoopWith (s : Setup) (fetch : Address → IO (Option Ixon.Constant))
    (pins : List Ix.Kernel.NatOpPinSet) (names : Address → Array String)
    (intern : Option Bool)
    (addresses : Array Address) (skip : Std.HashSet String)
    (emit : Row → IO Unit) (before : Address → IO Unit := fun _ => pure ())
    (after : IO Unit := pure ()) (progress : Nat → Outcome → IO Unit := fun _ _ => pure ()) :
    IO (Outcome × Nat × Interner × State) := do
  let mut out : Outcome := { checker := {} }
  let mut st : State := {}
  let mut consumed : Std.HashSet Address := {}
  let mut index := 0
  let mut interner : Interner := { terms := intern.getD false }
  let mut internMicros := 0
  for address in addresses do
    index := index + 1
    progress index out
    if consumed.contains address then continue
    let some source ← fetch address | continue
    let recs := recursorRecords s.cx.index address
    let rowsFor (outcome reason : String) (micros readMicros : Nat) : Array Row :=
      #[⟨address, names address, kindOf source, outcome, reason, micros, readMicros⟩] ++
        recs.map fun r => ⟨r, names r, "recursor", outcome, reason, micros, readMicros⟩
    for r in recs do consumed := consumed.insert r
    let r0 ← IO.monoNanosNow
    let reading ← IO.lazyPure fun _ => readRecord s.cx st address source
    let readMicros := ((← IO.monoNanosNow) - r0) / 1000
    match reading with
    | .error e =>
      let (outcome, reason) := readOutcome e
      for row in rowsFor outcome reason 0 readMicros do
        out := { out with failed := out.failed.insert row.address row.address,
                          counts := out.counts.insert outcome (out.counts.getD outcome 0 + 1) }
        emit row
      out := { out with reasons := out.reasons.insert reason (out.reasons.getD reason 0 + 1) }
    | .ok rd =>
      let rd ← if intern.isSome then do
          let i0 ← IO.monoNanosNow
          let (ds, t) ← IO.lazyPure fun _ => internDecls interner rd.decls
          interner := t
          internMicros := internMicros + ((← IO.monoNanosNow) - i0) / 1000
          pure { rd with decls := ds }
        else pure rd
      st := st.commit rd
      let deps := dependencies s.store s.cx.index s.extra address source
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
  return (out, internMicros, interner, st)

/-! ## Two phases and a pool (`CHECK_IXE_PAR`) -/

/-- Phase A's result: the installed environment, the recorded checks with
the record each belongs to, and what was left out. -/
structure Installed where
  fe : Ix.Kernel.FEnv
  pend : Array Ix.Kernel.Cached.PendingCheck
  owners : Array Address
  installedRecords : Nat := 0
  leftOut : Nat := 0

/-- One record's declarations installed in order (`annotDeclStep`), from a
fresh accumulator of recorded checks; `none` at the first failure. Every
argument is consumed, so the index and the array are updated in place. -/
def installRecord (pins : List Ix.Kernel.NatOpPinSet) :
    Nat → Ix.Kernel.FEnv → Array Ix.Kernel.Cached.PendingCheck → Ix.Kernel.Cached.CState →
      List Ix.Kernel.Declaration →
      Option (Nat × Ix.Kernel.FEnv × Array Ix.Kernel.Cached.PendingCheck × Ix.Kernel.Cached.CState)
  | pos, fe, pend, cs, [] => some (pos, fe, pend, cs)
  | pos, fe, pend, cs, d :: rest =>
    match Ix.Kernel.Cached.annotDeclStep .verified pins (pos, fe, pend) d cs with
    | .ok ((pos', fe', pend'), cs') => installRecord pins pos' fe' pend' cs' rest
    | .error _ => none

/-- Phase A over `addresses`: read and install every record, recording the
value checks; a record whose reading or install fails, or that depends on one
left out, is left out (an install is rolled back as `Checker.step` rolls
back: the index rebuilt from the constants before it, the memo state reset). -/
def phaseA (s : Setup) (fetch : Address → Option Ixon.Constant) (pins : List Ix.Kernel.NatOpPinSet)
    (addresses : Array Address) : Installed := Id.run do
  let mut fe := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
  let mut cs : Ix.Kernel.Cached.CState := {}
  let mut pos := 0
  let mut pend : Array Ix.Kernel.Cached.PendingCheck := #[]
  let mut owners : Array Address := #[]
  let mut st : State := {}
  let mut failed : Std.HashSet Address := {}
  let mut consumed : Std.HashSet Address := {}
  let mut installedRecords := 0
  let mut leftOut := 0
  for address in addresses do
    if consumed.contains address then continue
    let some source := fetch address | continue
    let recs := recursorRecords s.cx.index address
    for r in recs do consumed := consumed.insert r
    match readRecord s.cx st address source with
    | .error _ =>
      failed := failed.insert address
      for r in recs do failed := failed.insert r
      leftOut := leftOut + 1
    | .ok rd =>
      st := st.commit rd
      let deps := dependencies s.store s.cx.index s.extra address source
      if deps.any failed.contains then
        failed := failed.insert address
        for r in recs do failed := failed.insert r
        leftOut := leftOut + 1
        continue
      let before := fe.env
      match installRecord pins pos fe #[] cs rd.decls.toList with
      | some (pos', fe', recPend, cs') =>
        pos := pos'
        fe := fe'
        cs := cs'
        owners := owners ++ Array.replicate recPend.size address
        pend := pend ++ recPend
        installedRecords := installedRecords + 1
      | none =>
        fe := Ix.Kernel.mkFEnv before
        cs := {}
        pos := pos + 1
        failed := failed.insert address
        for r in recs do failed := failed.insert r
        leftOut := leftOut + 1
  return { fe, pend, owners, installedRecords, leftOut }

/-- One recorded check, timed: `(index, ok, micros)`. -/
def checkOne (inst : Installed) (k : Nat) : IO (Nat × Bool × Nat) := do
  let t0 ← IO.monoNanosNow
  let ok ← IO.lazyPure fun _ => match inst.pend[k]? with
    | some pc => (Ix.Kernel.Cached.checkPending .verified inst.fe pc {}).isOk
    | none => false
  return (k, ok, ((← IO.monoNanosNow) - t0) / 1000)

/-- A pool worker: claim one record at a time off `next` until it is past
the records (con-leche's `checkWorker`). -/
def worker (inst : Installed) (next : IO.Ref Nat) :
    (fuel : Nat) → Array (Nat × Bool × Nat) → IO (Array (Nat × Bool × Nat))
  | 0, acc => pure acc
  | fuel + 1, acc => do
    let k ← next.modifyGet fun a => (a, a + 1)
    if k < inst.pend.size then
      worker inst next fuel (acc.push (← checkOne inst k))
    else pure acc

/-- Phase B on `n` dedicated worker threads; the results in record order. -/
def pool (inst : Installed) (n : Nat) : IO (Array (Nat × Bool × Nat)) := do
  let next ← IO.mkRef 0
  let m := inst.pend.size
  let mut tasks := #[]
  for _ in [0:max 1 n] do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) (worker inst next (m + 1) #[]))
  let mut tab : Array (Nat × Bool × Nat) := Array.replicate m (0, false, 0)
  for t in tasks do
    for (k, ok, us) in ← IO.ofExcept (← IO.wait t) do
      tab := tab.set! k (k, ok, us)
  return tab

/-- Phase B on the calling thread. -/
def inThread (inst : Installed) : IO (Array (Nat × Bool × Nat)) := do
  let mut out := #[]
  for k in [0:inst.pend.size] do
    out := out.push (← checkOne inst k)
  return out

def runPar (started : Nat) (l : Loaded) (natPins : List Ix.Kernel.NatOpPinSet)
    (ordered : Array Address) (counts : List Nat) : IO UInt32 := do
  let tA ← IO.monoMsNow
  let inst ← IO.lazyPure fun _ => phaseA l.setup l.fetchPure natPins ordered
  let tA' ← IO.monoMsNow
  stage started s!"phase A: {inst.installedRecords} records installed, {inst.leftOut} left out, \
    {inst.pend.size} checks recorded, {inst.fe.env.consts.length} constants, in {tA' - tA} ms"
  let _ ← unsafe Runtime.markPersistent inst
  stage started "installed environment marked persistent"
  let rowsFile ← IO.getEnv "PAR_ROWS"
  let report (label : String) (t0 : Nat) (tab : Array (Nat × Bool × Nat)) : IO Unit := do
    let t1 ← IO.monoMsNow
    let failures := tab.foldl (fun n (_, ok, _) => if ok then n else n + 1) 0
    let summed := tab.foldl (fun n (_, _, us) => n + us) 0
    stage started s!"phase B {label}: {t1 - t0} ms wall, {summed / 1000} ms summed, {failures} failed"
  if (← IO.getEnv "PAR_MAIN") == some "1" then
    let t0 ← IO.monoMsNow
    report "on the calling thread" t0 (← inThread inst)
  let mut first := true
  for n in counts do
    let t0 ← IO.monoMsNow
    let tab ← pool inst n
    report s!"{n} workers" t0 tab
    if first then
      first := false
      if let some file := rowsFile then
        let h ← IO.FS.Handle.mk file .write
        for (k, ok, us) in tab do
          let a := (inst.owners[k]?).map toString |>.getD ""
          h.putStrLn (Lean.Json.mkObj [("address", Lean.toJson a), ("micros", Lean.toJson us),
            ("ok", Lean.toJson ok)]).compress
  return 0

/-! ## The run -/

def run (args : List String) : IO UInt32 := do
  let some options := CheckIxe.parseArgs args
    | IO.eprintln "usage: kernel-check-ixe-opt <input.ixe> <output.jsonl> [limit]"; return 2
  let started ← IO.monoMsNow
  let load := (← IO.getEnv "CHECK_IXE_LOAD").getD "full"
  let stream := load == "stream" || load == "stream-free"
  let thread := (← IO.getEnv "CHECK_IXE_THREAD") == some "1"
  let mark := (← IO.getEnv "CHECK_IXE_MARK") == some "1"
  let par : List Nat := match ← IO.getEnv "CHECK_IXE_PAR" with
    | some list => (list.splitOn ",").filterMap String.toNat?
    | none => []
  IO.eprintln s!"check-ixe-opt: load {load}, thread {thread}, mark {mark}, \
    par {par}"
  let bytes ← IO.FS.readBinFile options.input
  stage started s!"read {bytes.size} bytes"
  if let some list := ← IO.getEnv "CHECK_IXE_STATS" then
    return ← runStats bytes list options.output
  let intern : Option Bool := match ← IO.getEnv "CHECK_IXE_INTERN" with
    | some "names" => some false
    | some "all" => some true
    | _ => none
  let pins ← IO.ofExcept defaultPins
  let pre ← IO.ofExcept builtinPrelude
  let natPins ← IO.ofExcept builtinNatOpPins
  let l ← if stream then loadStream started bytes pins pre (load == "stream-free")
    else loadFull started bytes pins pre
  let s := l.setup
  let names := reportNames l.env s.store
  IO.eprintln s!"check-ixe-opt: {s.store.size} records, {s.ordered.size} primary, {l.env.blobs.size} blobs, \
    {s.cx.index.recs.size} recursors indexed"
  let ordered ← match ← IO.getEnv "CHECK_IXE_ROOTS" with
    | none => pure s.ordered
    | some list => do
      let mut roots : Array Address := pre.records.map (·.1)
      for n in (list.splitOn ",").filter (!·.isEmpty) do
        match l.env.named[Ix.Name.fromLeanName (CheckIxe.rootName n)]? with
        | some named => roots := roots.push named.addr
        | none => IO.eprintln s!"check-ixe-opt: CHECK_IXE_ROOTS: no constant {n}"
      pure (closure s.store s.extra roots)
  let total := match options.limit with | some n => min n ordered.size | none => ordered.size
  let ordered := ordered.extract 0 total
  stage started s!"ordered {total} records"
  unless par.isEmpty do
    return ← runPar started l natPins ordered par
  if mark then
    -- the setup and the name table only: in `stream-free` mode the fetch
    -- closure owns a map that must stay exclusive (a persistent map is
    -- copied by every `erase`)
    let store := l.setup.store
    let extra := l.setup.extra
    let order := l.setup.ordered
    let index := l.setup.cx.index
    let env := l.env
    let _ ← unsafe Runtime.markPersistent store
    let _ ← unsafe Runtime.markPersistent extra
    let _ ← unsafe Runtime.markPersistent order
    let _ ← unsafe Runtime.markPersistent index
    let _ ← unsafe Runtime.markPersistent env
    let _ ← unsafe Runtime.markPersistent names
    stage started "marked persistent"
  let handle ← IO.FS.Handle.mk options.output .write
  let loop : IO (Outcome × Nat × Interner × State) :=
    checkLoopWith s l.fetch natPins (names.getD · #[]) intern ordered {}
      (emit := fun row => do handle.putStrLn row.json.compress; handle.flush)
      (progress := fun i o => do
        if i % 20000 == 0 then
          IO.eprintln s!"check-ixe-opt: {i}/{total} after {(← IO.monoMsNow) - started} ms; \
            {o.counts.toList}; rss {← rssMb} MB")
  let tLoop ← IO.monoMsNow
  let (out, internMicros, interner, st) ←
    if thread then IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) loop)) else loop
  let tEnd ← IO.monoMsNow
  stage started s!"check loop done in {tEnd - tLoop} ms; {out.counts.toList}; \
    {out.checker.fe.env.consts.length} constants installed; interning {internMicros / 1000} ms \
    ({interner.names.size} names, {interner.levels.size} levels, {interner.exprs.size} terms)"
  if (← IO.getEnv "CHECK_IXE_SIZE") == some "1" then
    let consts := out.checker.fe.env.consts
    let stateTypes := st.constTypes.toArray.map (·.2.2)
    let layers ← IO.lazyPure fun _ => envLayers consts stateTypes
    for (what, z) in layers do
      IO.eprintln s!"check-ixe-opt: size: {what}: {z.nodes} nodes, ~{z.bytes / 1048576} MB"
    stage started s!"size walk done ({consts.length} constants, {st.constTypes.size} reader types, \
      {st.indBlocks.size} blocks, {st.projOwners.size} owners)"
  return 0

end Benchmarks.Kernel.CheckIxeOpt

def main (args : List String) : IO UInt32 := Benchmarks.Kernel.CheckIxeOpt.run args
