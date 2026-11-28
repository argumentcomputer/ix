import Benchmarks.Kernel.CheckIxeStep
import Ix.KernelCheck.Binding
import IxCK.Kernel.Admission

/-! # The batch fold over an environment check's accepted records (untrusted harness)

`kernel-check-ixe --fold <input.ixe> <output.jsonl>` measures the
declaration fold `Ix.Kernel.Cached.checkDecls` run ONCE over every record the
per-constant check would accept, as upstream con-leche's own driver (`Main.lean`,
`checkDeclsIO`) runs it over a lean4export stream: phase A
(`annotDeclStep` over all declarations), then phase B (`checkPending` of
every recorded declaration against its prefix view, each from a fresh memo
state). It is the comparison point for the environment check's per-record step
(`CheckIxeStep.Checker.step`: phase A on one declaration, then phase B on
what that step left pending).

The records: the check order (`CheckIxeStep.setup`); a record the reader
declines or fails, and every record that depends on one, is left out, as are
the recursor and projection records of left-out blocks. What remains is read
by the certified entry's own reader path (`Admission.readStream`,
with the prelude) and prepared by `Frontend.preparePrelude`, so the fold runs
over exactly the declarations `Admission.checkConstants` would check.

Phase B runs as `Main.lean` runs it at `--jobs=1`: on a dedicated thread (a
fresh allocator heap), after marking the installed environment and the
pending checks persistent (the phase-boundary mark).

Rows (JSONL): one per phase-B record, `{name, kind, micros}` (the check and
the release of its memo state, as `Cached.checkRecord` times them), plus a
summary on stderr: reading, phase A, phase B (sum of the per-record times and
wall) and the total. Knobs (environment): `FOLD_THREAD=0` runs phase B on the
main thread, `FOLD_PERSIST=0` skips the mark, `FOLD_SHARE=1` runs
`ShareCommon.shareCommon'` over all prepared declarations before phase A
(environment-wide sharing of every subterm, name and level), and
`FOLD_READSTATS=1` only reports the reader's per-reference work (node and
reference counts, the time of `resolve`, of `Ctx.keyAt`, of building an input
key with its hash, and of key equality over every reference-table entry). -/

namespace Benchmarks.Kernel.CheckIxeFold

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

/-- The records the environment check would accept or check (in check order), and
every recursor and projection record of their blocks. Any missing primary block,
declined/failed primary block, or unkept/orphan projection record increments `dropped`. -/
def acceptedRecords (s : Setup) : Array (Address × Ixon.Constant) × Nat := Id.run do
  let mut st : State .anon := {}
  let mut failed : Std.HashSet Address := {}
  let mut consumed : Std.HashSet Address := {}
  let mut out : Array (Address × Ixon.Constant) := #[]
  let mut dropped := 0
  for address in s.ordered do
    if consumed.contains address then continue
    let some source := s.store[address]? | do
      dropped := dropped + 1
      continue
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
  -- projection records of the kept blocks; any unkept/orphan projection is counted in `dropped`
  let kept : Std.HashSet Address := out.foldl (fun acc (a, _) => acc.insert a) {}
  let mut projs : Array (Address × Ixon.Constant) := #[]
  for (a, c) in s.store.toArray do
    let o := owner a c
    if o != a && !kept.contains a then
      if kept.contains o then
        projs := projs.push (a, c)
      else
        dropped := dropped + 1
  projs := projs.qsort (fun x y => x.1.cmpBytes y.1 == .lt)
  return (out ++ projs, dropped)

def kindWord : Ix.Kernel.Cached.PendingCheck .anon → String
  | pc => pc.vg.kind.word

def percentile (xs : Array Nat) (p : Nat) : Nat :=
  if xs.isEmpty then 0 else
    let s := xs.qsort (· < ·)
    s[min (s.size - 1) (s.size * p / 100)]!

/-- Phase B over `pend`, one record at a time, each timed with the release
of its memo state. -/
def phaseB (fe : Ix.Kernel.FEnv .anon) (pend : Array (Ix.Kernel.Cached.PendingCheck .anon)) :
    IO (Array Nat × Option (Ix.Kernel.CheckError .anon × Nat)) := do
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
    | .lam t b => go (go (acc.1 + 1, acc.2) t) b
    | .all t b => go (go (acc.1 + 1, acc.2) t) b
    | .letE _ _ t v b => go (go (go (acc.1 + 1, acc.2) t) v) b
    | _ => (acc.1 + 1, acc.2)

/-- What the reader's per-reference work costs. The reader keys a reference at
every `ref`/`prj` node it converts; this reports the node and reference
counts of the kept records, and over every reference-table entry once: the
time of `resolve`, of `Ctx.keyAt` (a lookup in `Ctx.keys`), of building the
input key `.id a` with its hash (what that lookup saves at every occurrence),
and of key equality: between equal keys that are distinct objects (the hash
guard passes and the addresses are compared) and between neighbouring keys
(mostly unequal: the hash guard decides). -/
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
  let addresses := records.foldl (fun acc (_, c) => acc ++ c.refs) (#[] : Array Address)
  let t0 ← IO.monoNanosNow
  let resolved ← IO.lazyPure fun _ => addresses.foldl (fun n a => match resolve s.cx.store a with
      | some _ => n + 1
      | none => n) 0
  let t1 ← IO.monoNanosNow
  let keys ← IO.lazyPure fun _ => addresses.filterMap fun a => (s.cx.keyAt a).toOption
  let t2 ← IO.monoNanosNow
  let fresh ← IO.lazyPure fun _ => addresses.map fun a => Ix.Kernel.Key.id (md := .anon) a
  let freshOdd := fresh.foldl (fun n k => n + k.hashData.toNat % 2) 0
  let tFresh ← IO.monoNanosNow
  -- each input key beside a new key object of the same address
  let pairs ← IO.lazyPure fun _ => addresses.filterMap fun a => match s.cx.keyAt a with
    | .ok k@(.id _) => some (k, Ix.Kernel.Key.id (md := .anon) a)
    | _ => none
  let t3 ← IO.monoNanosNow
  let same ← IO.lazyPure fun _ =>
    pairs.foldl (fun n (k, k') => if k == k' then n + 1 else n) 0
  let t4 ← IO.monoNanosNow
  let neighbours ← IO.lazyPure fun _ =>
    (keys.zip (keys.extract 1 keys.size)).foldl (fun n (k, k') => if k == k' then n + 1 else n) 0
  let t5 ← IO.monoNanosNow
  IO.eprintln s!"stats: over {addresses.size} table entries ({resolved} resolve, {keys.size} keyed): \
    resolve {(t1 - t0) / 1000000} ms; keyAt {(t2 - t1) / 1000000} ms; Key.id with its hash \
    {(tFresh - t2) / 1000000} ms ({freshOdd} odd); {pairs.size} input keys against an equal new \
    key {(t4 - t3) / 1000000} ms ({same} equal); neighbouring keys {(t5 - t4) / 1000000} ms \
    ({neighbours} equal)"

def parseRootName (n : String) : Lean.Name :=
  (n.splitOn ".").foldl (init := .anonymous) fun acc c =>
    let inner := ((c.drop 1).dropEnd 1).toString
    if c.startsWith "«" && c.endsWith "»" && !inner.isEmpty && inner.all Char.isDigit then
      .num acc inner.toNat!
    else .str acc c

/-- Parse a comma-separated `--require-roots` list into non-empty root names. -/
def parseRequireRoots (s : String) : Array String :=
  (s.splitOn ",").toArray.filterMap fun r =>
    let t := r.trimAscii.toString
    if t.isEmpty then none else some t

/-- Check that every required root name exists in `env.named`, resolves to a
kernel key in `cx`, and is installed in `installed`. Returns human-readable
failure entries for any missing or unaccepted roots. -/
def checkRequiredRoots (env : Ixon.Env) (cx : Ctx .anon)
    (installed : Std.HashSet (Ix.Kernel.Key .anon))
    (roots : Array String) : Array String := Id.run do
  let mut missing : Array String := #[]
  for name in roots do
    match env.named[Ix.Name.fromLeanName (parseRootName name)]? with
    | none =>
      missing := missing.push s!"{name} (absent from .ixe named metadata)"
    | some entry =>
      match cx.keyAt entry.addr with
      | .error e =>
        missing := missing.push s!"{name} (key resolution failed at {entry.addr}: {e})"
      | .ok key =>
        if !installed.contains key then
          missing := missing.push s!"{name} (key {key} at {entry.addr} not installed in accepted environment)"
  return missing

structure Options where
  input : System.FilePath := ⟨""⟩
  output : System.FilePath := ⟨""⟩
  strict : Bool := false
  requireRoots : Array String := #[]

def usage : String :=
  "usage: kernel-check-ixe --fold [--strict] [--require-roots <r1,r2,...>] <input.ixe> <output.jsonl>"

def parseArgs (args : List String) : Option Options :=
  go args {} #[]
where
  go : List String → Options → Array String → Option Options
    | "--strict" :: rest, o, pos => go rest { o with strict := true } pos
    | "--require-roots" :: list :: rest, o, pos =>
      let rs := parseRequireRoots list
      if rs.isEmpty then none else go rest { o with requireRoots := o.requireRoots ++ rs } pos
    | a :: rest, o, pos => if a.startsWith "--" then none else go rest o (pos.push a)
    | [], o, pos => match pos.toList with
      | [input, output] => some { o with input, output }
      | _ => none

def run (args : List String) : IO UInt32 := do
  let some options := parseArgs args
    | IO.eprintln usage; return 2
  let started ← IO.monoMsNow
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile options.input))
  let mut store : RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let (table, pre) ← IO.ofExcept (Ix.KernelCheck.Binding.context env)
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) table pre hints.lookup
  let tLoad ← IO.monoMsNow
  let (records, dropped) ← IO.lazyPure fun _ => acceptedRecords s
  let tSelect ← IO.monoMsNow
  IO.eprintln s!"fold: {s.store.size} records, {s.ordered.size} primary; kept {records.size} \
    (dropped {dropped} records the environment check declines, blocks, or orphans); load {tLoad - started} ms, \
    selection {tSelect - tLoad} ms"
  if options.strict && (dropped > 0 || records.size != s.store.size) then
    IO.eprintln s!"fold: strict failure: dropped {dropped} record(s), kept {records.size} of {s.store.size} store record(s)"
    return 1
  if (← IO.getEnv "FOLD_READSTATS") == some "1" then
    unless options.requireRoots.isEmpty do
      IO.eprintln "fold: FOLD_READSTATS=1 cannot be combined with --require-roots (skips phase A/B)"
      return 2
    readStats s records
    return 0
  let blobs := env.blobs.toList
  let r0 ← IO.monoNanosNow
  let decls ← IO.lazyPure fun _ =>
    Ix.Kernel.Admission.readStream Address.blake3 table pre records.toList blobs hints.lookup
  let (ev, decls) ← match decls with
    | .ok r => pure r
    | .error e => IO.eprintln s!"fold: read failed: {e}"; return 1
  let prepared ← IO.lazyPure fun _ => Ix.Kernel.Frontend.preparePrelude pre.ix decls
  let r1 ← IO.monoNanosNow
  IO.eprintln s!"fold: read {decls.size} declarations ({prepared.size} prepared) in {(r1 - r0) / 1000000} ms"
  let (moved, guarded) := Ix.Kernel.Frontend.prepareReport pre.ix decls
  IO.eprintln s!"fold: hoist would move {moved} records; guard fired: {guarded}"
  let prepared ← if (← IO.getEnv "FOLD_SHARE") == some "1" then do
      let s0 ← IO.monoNanosNow
      let shared ← IO.lazyPure fun _ => ShareCommon.shareCommon' prepared
      IO.eprintln s!"fold: shareCommon over all declarations in {((← IO.monoNanosNow) - s0) / 1000000} ms"
      pure shared
    else pure prepared
  let a0 ← IO.monoNanosNow
  let phaseA ← IO.lazyPure fun _ =>
    (prepared.foldlM (Ix.Kernel.Cached.annotDeclStep .verified ev)
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
  let handle ← IO.FS.Handle.mk options.output .write
  for (pc, t) in pend.zip times do
    handle.putStrLn (Lean.Json.mkObj [("name", Lean.toJson (toString pc.vg.cvA.name)),
      ("kind", Lean.toJson (kindWord pc)), ("micros", Lean.toJson t)]).compress
  let sum := times.foldl (· + ·) 0
  let over100 := times.foldl (fun n t => if t > 100000 then n + 1 else n) 0
  IO.eprintln s!"fold: phase B {(b1 - b0) / 1000000} ms wall{if thread then " (dedicated thread)" else ""}, \
    per-record sum {sum / 1000} ms over {times.size} records; median {percentile times 50} us, \
    p99 {percentile times 99} us, {over100} over 100 ms"
  IO.eprintln s!"fold: done in {(← IO.monoMsNow) - started} ms; peak RSS {(← statusKb "VmHWM:") / 1024} MB"
  if err.isSome then
    return 1
  unless options.requireRoots.isEmpty do
    let installed : Std.HashSet (Ix.Kernel.Key .anon) :=
      fe.env.consts.foldl (fun acc ci => acc.insert ci.name) {}
    let missing := checkRequiredRoots env s.cx installed options.requireRoots
    unless missing.isEmpty do
      IO.eprintln s!"fold: required roots missing or unaccepted ({missing.size}):"
      for m in missing do IO.eprintln s!"  {m}"
      return 1
  return 0

end Benchmarks.Kernel.CheckIxeFold
