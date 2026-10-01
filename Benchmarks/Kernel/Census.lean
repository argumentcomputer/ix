/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon
import Ix.Kernel

/-! # Certified kernel census over a compiled Ixon environment

An untrusted driver that measures coverage: it orders an environment's primary
records by dependency, reads each record, and checks it with `Ix.Kernel` one
declaration at a time, continuing past failures. A singleton inductive family
is checked together with its separately stored recursor, the association the
admission fold performs. A declaration that references a failed or blocked one
is reported as blocked and not checked.

The outcome of this driver is not a certified verdict about the environment;
`checkEnv` is. Each accepted row is a certified admission against the
environment of the rows accepted before it.

Usage: `kernel-census-intrinsic <input.ixe> <output.jsonl> [limit] [fuel]` (the
intrinsic reference kernel's census; from L5 `kernel-census` is the certified
checker's, `Benchmarks.Kernel.ConLecheCensus`). Rows are
written as they are produced; the summary goes to stderr.

Checks run on the main thread by default, so timings have no polling floor.
The work budget bounds charged search calls, not allocation or elapsed time;
large-corpus diagnostics should also use external time and memory limits.
Environment variables: `CENSUS_THREADED` runs each check on its own task with a
timeout instead, the environment marked persistent first so the task does not
mark it multi-threaded;
`CENSUS_PROBE=<name or address prefix>` prints why a supplied recursor differs
from the generated one.

The work budget bounds calls, not the size of the terms a call builds, so an
inline check can still outgrow memory. A watchdog thread ends the run when one
check exceeds `CENSUS_WATCH_MS` (default 60000) or the process exceeds
`CENSUS_WATCH_MB` of resident memory (default 20000): it appends the record's
address to `<output>.runaway` and exits with code 3. `CENSUS_SKIP` (comma
separated addresses) declines those records unchecked, so a driver
(`scripts/census-guarded.sh`) restarts the run with them skipped. -/

open Ix.Kernel

namespace Benchmarks.Kernel.Census

def owner (address : Address) (source : Ixon.Constant) : Address :=
  match source.info with
  | .dPrj p => p.block
  | .iPrj p => p.block
  | .rPrj p => p.block
  | .cPrj p => p.block
  | _ => address

abbrev Store := Std.HashMap Address Ixon.Constant

/-- Primary records in dependency order: an iterative depth-first postorder
over table references, with projections replaced by their owners. -/
def order (store : Store) : Array Address := Id.run do
  let mut done : Std.HashSet Address := {}
  let mut active : Std.HashSet Address := {}
  let mut out : Array Address := #[]
  let roots := store.toArray.qsort (fun a b => a.1.cmpBytes b.1 == .lt)
  for (address, source) in roots do
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
        if let some record := store[node]? then
          for ref in record.refs do
            if let some target := store[ref]? then
              let dependency := owner ref target
              unless dependency == node || done.contains dependency || active.contains dependency do
                stack := stack.push (dependency, false)
  return out

/-- The records a single record's tables reach, with projection owners. -/
def localStore (store : Store) (source : Ixon.Constant) : Ingress.Constants := Id.run do
  let mut out : Array (Address × Ixon.Constant) := #[]
  let mut seen : Std.HashSet Address := {}
  for ref in source.refs do
    if let some target := store[ref]? then
      unless seen.contains ref do
        seen := seen.insert ref
        out := out.push (ref, target)
      let root := owner ref target
      if root != ref then
        if let some block := store[root]? then
          unless seen.contains root do
            seen := seen.insert root
            out := out.push (root, block)
  return out.toList

def localBlobs (blobs : Std.HashMap Address ByteArray) (source : Ixon.Constant) : Ingress.Blobs :=
  source.refs.toList.filterMap fun ref => (blobs[ref]?).map (ref, ·)

/-- The size a record's expressions reach once sharing is expanded, as the
kernel's tree-shaped terms require. Shared entries only reference earlier
entries, so one pass over the table suffices. -/
def exprSize (shares : Array Nat) : Ixon.Expr → Nat
  | .share i => shares.getD i.toNat 1
  | .app f a => 1 + exprSize shares f + exprSize shares a
  | .lam _ t b => 1 + exprSize shares t + exprSize shares b
  | .all _ _ t b => 1 + exprSize shares t + exprSize shares b
  | .letE _ t v b => 1 + exprSize shares t + exprSize shares v + exprSize shares b
  | .prj _ _ v => 1 + exprSize shares v
  | _ => 1

def infoExprs : Ixon.ConstantInfo → List Ixon.Expr
  | .defn d => [d.typ, d.value]
  | .recr r => r.typ :: r.rules.toList.map (·.rhs)
  | .axio a => [a.typ]
  | .quot q => [q.typ]
  | .muts members => members.toList.flatMap fun
    | .defn d => [d.typ, d.value]
    | .indc i => i.typ :: i.ctors.toList.map (·.typ)
    | .recr r => r.typ :: r.rules.toList.map (·.rhs)
  | _ => []

def expandedSize (source : Ixon.Constant) : Nat := Id.run do
  let mut shares : Array Nat := #[]
  for entry in source.sharing do
    shares := shares.push (exprSize shares entry)
  return (infoExprs source.info).foldl (fun total e => total + exprSize shares e) 0

def kindOf (block : Block Address) : String :=
  match block.members with
  | [.defn _ .definition _ _ _] => "definition"
  | [.defn _ .theorem _ _ _] => "theorem"
  | [.defn _ .opaque _ _ _] => "opaque"
  | [.induct ..] => "inductive"
  | [.recursor ..] => "recursor"
  | [.axiom ..] => "axiom"
  | [.quot ..] => "quotient"
  | members => s!"block({members.length})"

def refBlock : ConstRef Address → Address
  | .member block _ => block
  | .ctor block _ _ => block

/-! ## Probe: why a supplied recursor differs from the generated one -/

partial def levelString : VLevel → String
  | .zero => "0"
  | .succ l => s!"({levelString l})+1"
  | .max a b => s!"max({levelString a},{levelString b})"
  | .imax a b => s!"imax({levelString a},{levelString b})"
  | .param i => s!"u{i}"

def headString : VExpr Address → String
  | .bvar i => s!"bvar {i}"
  | .sort l => s!"sort {levelString l}"
  | .const r ls => s!"const {toString (refBlock r) |>.take 12}… [{", ".intercalate (ls.map levelString)}]"
  | .app .. => "app"
  | .lam .. => "lam"
  | .forallE .. => "forallE"
  | .letE .. => "letE"
  | .proj _ i _ => s!"proj {i}"
  | .natLit _ n => s!"natLit {n}"

/-- The first subterm where two terms differ, with its path. -/
partial def firstDiff (path : String) : VExpr Address → VExpr Address → Option String
  | .app f a, .app f' a' => firstDiff (path ++ ".fn") f f' <|> firstDiff (path ++ ".arg") a a'
  | .lam t b, .lam t' b' => firstDiff (path ++ ".dom") t t' <|> firstDiff (path ++ ".body") b b'
  | .forallE t b, .forallE t' b' => firstDiff (path ++ ".dom") t t' <|> firstDiff (path ++ ".body") b b'
  | .letE t v b, .letE t' v' b' =>
    firstDiff (path ++ ".type") t t' <|> firstDiff (path ++ ".val") v v' <|> firstDiff (path ++ ".body") b b'
  | .proj r i e, .proj r' i' e' =>
    if r == r' && i == i' then firstDiff (path ++ ".struct") e e' else some s!"{path}: {headString (.proj r i e)} vs {headString (.proj r' i' e')}"
  | e, e' => if e == e' then none else some s!"{path}: supplied {headString e} vs generated {headString e'}"

def probeRecursor (supplied generated : Const Address) : List String :=
  match supplied, generated with
  | .recursor u p i m n t rs k sf, .recursor u' p' i' m' n' t' rs' k' sf' =>
    [s!"universes {u}/{u'} params {p}/{p'} indices {i}/{i'} motives {m}/{m'} minors {n}/{n'} \
      rules {rs.length}/{rs'.length} k {k}/{k'} safe {sf == sf'}"] ++
    ((firstDiff "type" t t').map (s!"type differs at {·}")).toList ++
    ((rs.zip rs').zipIdx.filterMap fun ((r, r'), j) =>
      if r.nfields != r'.nfields then some s!"rule {j} fields {r.nfields}/{r'.nfields}"
      else (firstDiff s!"rule {j}" r.rhs r'.rhs).map (s!"rule {j} differs at {·}"))
  | _, _ => ["not a recursor pair"]

structure Row where
  address : Address
  names : Array String
  kind : String
  outcome : String
  reason : String
  micros : Nat
  /-- Time spent reading the record (Ixon to kernel terms). -/
  readMicros : Nat := 0

def Row.json (row : Row) : Lean.Json := Lean.Json.mkObj [
  ("address", Lean.toJson (toString row.address)), ("names", Lean.toJson row.names),
  ("kind", Lean.toJson row.kind), ("outcome", Lean.toJson row.outcome),
  ("reason", Lean.toJson row.reason), ("micros", Lean.toJson row.micros),
  ("readMicros", Lean.toJson row.readMicros)]

def searchOutcome : SearchFailure → String × String
  | .exhausted => ("decline", "ingress: out of fuel")
  | .unsupported r => ("decline", s!"ingress: {r}")
  | .unresolved r => ("decline", s!"ingress: {r}")
  | .malformed r => ("reject", s!"ingress: {r}")
  | .noMatch => ("decline", "ingress: no applicable rule")

/-- Lean's reducibility hint as a kernel unfolding height. -/
def hintHeight : Lean.ReducibilityHints → Nat
  | .opaque => 0
  | .abbrev => abbrevHeight
  | .regular h => h.toNat

def errorOutcome : Error → String × String
  | .rejected r => ("reject", r)
  | .declined r => ("decline", r)

structure Options where
  input : System.FilePath
  output : System.FilePath
  limit : Option Nat := none
  fuel : Nat := ({} : Config).fuel
  /-- Records whose expanded expressions exceed this many nodes are reported,
  not read: the kernel's terms do not share structure. -/
  maxExpanded : Nat := 2000000
  /-- A check running longer than this is reported as a timeout and abandoned. -/
  timeoutMs : UInt32 := 20000
  /-- Abandoned checks keep running; at most this many may be alive. -/
  maxOrphans : Nat := 4
  /-- Above this resident size (kB), wait for abandoned checks to finish. -/
  maxResidentKb : Nat := 16000000

/-- A field of `/proc/self/status` in kB (Linux only; 0 elsewhere). -/
def statusKb (field : String) : IO Nat := do
  let status ← (IO.FS.readFile "/proc/self/status" |>.toBaseIO)
  let some line := status.toOption.bind fun text => text.splitOn "\n" |>.find? (·.startsWith field)
    | return 0
  return ((line.drop field.length).trimAscii.toString.takeWhile Char.isDigit).toNat!

def parseArgs : List String → Option Options
  | [input, output] => some { input, output }
  | [input, output, limit] => do some { input, output, limit := some (← limit.toNat?) }
  | [input, output, limit, fuel] => do
    some { input, output, limit := some (← limit.toNat?), fuel := ← fuel.toNat? }
  | _ => none

def run (args : List String) : IO UInt32 := do
  let some options := parseArgs args
    | IO.eprintln "usage: kernel-census-intrinsic <input.ixe> <output.jsonl> [limit] [fuel]"; return 2
  let started ← IO.monoMsNow
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile options.input))
  let mut store : Store := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  -- Names by owning record, for reporting only.
  let mut names : Std.HashMap Address (Array String) := {}
  for (name, named) in env.named.toList do
    let root := match store[named.addr]? with
      | some source => owner named.addr source
      | none => named.addr
    let current := names.getD root #[]
    if current.size < 3 then names := names.insert root (current.push (toString name))
  let resolveName (name : Lean.Name) : Option (ConstRef Address) := do
    let named ← env.named[Ix.Name.fromLeanName name]?
    let source ← store[named.addr]?
    let root := owner named.addr source
    Ingress.reference [(named.addr, source), (root, ← store[root]?)] named.addr
  let natFamily := resolveName `Nat
  let strings : Option (StringRefs Address) := do
    return { char := ← resolveName `Char, charOfNat := ← resolveName `Char.ofNat,
             natural := ← natFamily, stringOfList := ← resolveName `String.ofList,
             listNil := ← resolveName `List.nil, listCons := ← resolveName `List.cons }
  let ordered := order store
  let cfg : Config := { fuel := options.fuel }
  let probe ← IO.getEnv "CENSUS_PROBE"
  -- The default checks on the main thread. `CENSUS_THREADED` opts into
  -- tasks with a timeout; external caps also bound the inline process.
  let inline := (← IO.getEnv "CENSUS_THREADED").isNone
  IO.eprintln s!"census: {store.size} records, {ordered.size} primary, {env.blobs.size} blobs, \
    Nat family {natFamily.isSome}, string constants {strings.isSome}, loaded in {(← IO.monoMsNow) - started} ms"
  let read (address : Address) : Except SearchFailure (Block Address) :=
    let source := store[address]!
    let context := Ingress.context (localStore store source) (localBlobs env.blobs source)
      natFamily strings (address, source)
    Ingress.readBlock context cfg.fuel
  -- Separately stored recursors by the family their major premise names.
  let mut recursors : Std.HashMap Address (Array (Address × Const Address)) := {}
  for address in ordered do
    let source := store[address]!
    if let .recr _ := source.info then
      if expandedSize source ≤ options.maxExpanded then
        if let .ok ⟨[recursor@(.recursor ..)]⟩ := read address then
          if let some (.member family 0) := recursorMajor recursor then
            recursors := recursors.insert family ((recursors.getD family #[]).push (address, recursor))
  IO.eprintln s!"census: recursors indexed after {(← IO.monoMsNow) - started} ms"
  let skip : Std.HashSet String := match ← IO.getEnv "CENSUS_SKIP" with
    | some list => (list.splitOn ",").foldl (fun set a => if a.isEmpty then set else set.insert a) {}
    | none => {}
  let watchMs := ((← IO.getEnv "CENSUS_WATCH_MS").bind String.toNat?).getD 60000
  let watchKb := ((← IO.getEnv "CENSUS_WATCH_MB").bind String.toNat?).getD 20000 * 1024
  -- The record being checked inline and when its check started.
  let checking : IO.Ref (Option (Address × Nat)) ← IO.mkRef none
  let running ← IO.mkRef true
  if inline then
    let runaway := options.output.toString ++ ".runaway"
    let _ ← IO.asTask (prio := .dedicated) do
      while ← running.get do
        IO.sleep 500
        if let some (address, since) ← checking.get then
          let elapsed := (← IO.monoMsNow) - since
          let rss ← statusKb "VmRSS:"
          if elapsed > watchMs || rss > watchKb then
            IO.eprintln s!"census: watchdog: {address} ran {elapsed} ms, RSS {rss / 1024} MB; exiting"
            let file ← IO.FS.Handle.mk runaway .append
            file.putStrLn (toString address)
            file.flush
            IO.Process.exit 3
  let handle ← IO.FS.Handle.mk options.output .write
  let mut kenv : Env Address := Env.emptyWith Ingress.addressKeyHash
  let mut failed : Std.HashMap Address Address := {}
  let mut consumed : Std.HashSet Address := {}
  let mut counts : Std.HashMap String Nat := {}
  let mut reasons : Std.HashMap String Nat := {}
  let mut index := 0
  let mut orphans : Array (Task (Except IO.Error (Except Error (Env Address)))) := #[]
  let total := match options.limit with | some n => min n ordered.size | none => ordered.size
  let emit (row : Row) : IO Unit := do
    handle.putStrLn row.json.compress
    handle.flush
  for address in ordered.extract 0 total do
    index := index + 1
    if index % 1000 == 0 then
      IO.eprintln s!"census: {index}/{total} after {(← IO.monoMsNow) - started} ms; {counts.toList}; \
        RSS {(← statusKb "VmRSS:") / 1024} MB; {orphans.size} abandoned checks running"
    if consumed.contains address then continue
    let label := names.getD address #[]
    let size := expandedSize store[address]!
    if size > options.maxExpanded then
      let reason := s!"census: expanded term size exceeds {options.maxExpanded} nodes"
      failed := failed.insert address address
      counts := counts.insert "decline" (counts.getD "decline" 0 + 1)
      reasons := reasons.insert reason (reasons.getD reason 0 + 1)
      emit ⟨address, label, "unread", "decline", s!"{reason} ({size})", 0, 0⟩
      continue
    let r0 ← IO.monoNanosNow
    let reading ← IO.lazyPure fun _ => read address
    let readMicros := ((← IO.monoNanosNow) - r0) / 1000
    match reading with
    | .error failure =>
      let (outcome, reason) := searchOutcome failure
      failed := failed.insert address address
      counts := counts.insert outcome (counts.getD outcome 0 + 1)
      reasons := reasons.insert reason (reasons.getD reason 0 + 1)
      emit ⟨address, label, "unread", outcome, reason, 0, readMicros⟩
    | .ok block =>
      let kind := kindOf block
      let dependencies := block.refs.map refBlock |>.filter (· != address)
      match dependencies.find? failed.contains with
      | some blocker =>
        failed := failed.insert address (failed.getD blocker blocker)
        counts := counts.insert "blocked" (counts.getD "blocked" 0 + 1)
        emit ⟨address, label, kind, "blocked", toString (failed.getD blocker blocker), 0, readMicros⟩
      | none =>
        if skip.contains (toString address) then
          let reason := "census: skipped: exceeded the watchdog's limits on an earlier run"
          failed := failed.insert address address
          counts := counts.insert "decline" (counts.getD "decline" 0 + 1)
          reasons := reasons.insert reason (reasons.getD reason 0 + 1)
          emit ⟨address, label, kind, "decline", reason, 0, readMicros⟩
          continue
        let pair : Option (Address × Const Address × Const Address) := match block.members with
          | [family@(.induct ..)] => do
            let (recAddress, recursor) ← (recursors.getD address #[]).find? (!consumed.contains ·.1)
            some (recAddress, family, recursor)
          | _ => none
        let t0 ← IO.monoNanosNow
        -- A check on a separate task would mark the shared environment
        -- multi-threaded, making every reference-count update atomic.
        -- Persistent objects skip reference counting; every object an
        -- abandoned check can reach was marked before that check started.
        let current ← if inline then pure kenv else unsafe Runtime.markPersistent kenv
        let check : Unit → Except Error (Env Address) := fun _ => match pair with
          | some (recAddress, family, recursor) =>
            (checkInductiveC.{0,1} cfg current address (.member recAddress 0) family recursor).map Subtype.val
          | none => checkDecl.{0,1} cfg current ⟨address, block⟩ (hintHeight <$> env.anonHints[address]?)
        checking.set (some (address, ← IO.monoMsNow))
        let task ← if inline then pure (Task.pure (.ok (check ())))
          else IO.asTask (prio := .dedicated) (IO.lazyPure check)
        -- Poll rather than start a timer task: a sleeping timer would hold a
        -- worker of the shared task pool for the whole timeout.
        let deadline := t0 + options.timeoutMs.toNat * 1000000
        let mut pause : UInt32 := 0
        while !(← IO.hasFinished task) && (← IO.monoNanosNow) < deadline do
          IO.sleep pause
          pause := min 5 (pause + 1)
        let finished ← if ← IO.hasFinished task then pure (some task.get) else pure none
        checking.set none
        let micros := ((← IO.monoNanosNow) - t0) / 1000
        let result : Except Error (Env Address) ← match finished with
          | some (.ok r) => pure r
          | some (.error e) => pure (.error (.declined s!"census: check raised {e}"))
          | none =>
            orphans := orphans.push task
            pure (.error (.declined s!"census: check exceeded {options.timeoutMs} ms"))
        -- Bound the CPU spent by abandoned checks.
        orphans ← orphans.filterM fun t => return !(← IO.hasFinished t)
        while orphans.size ≥ options.maxOrphans ||
            (!orphans.isEmpty && (← statusKb "VmRSS:") > options.maxResidentKb) do
          IO.sleep 1000
          orphans ← orphans.filterM fun t => return !(← IO.hasFinished t)
        if let some target := probe then
          if label.contains target || (toString address).startsWith target then
            if let some (recAddress, family, recursor) := pair then
              match Certified.Ordinary.readBlock.{0,1} cfg.fuel kenv.toEnvironment address ⟨[family, recursor]⟩ with
              | .ok reading =>
                let generated := reading.shape.recursorSource address reading.mode reading.k (.member recAddress 0)
                IO.eprintln s!"probe {target}: family matches {family == reading.shape.source address}"
                for line in probeRecursor recursor generated do IO.eprintln s!"probe {target}: {line}"
              | .error failure => IO.eprintln s!"probe {target}: reading failed {repr failure}"
        let rows : List (Address × String) := match pair with
          | some (recAddress, _, _) => [(address, kind), (recAddress, "recursor")]
          | none => [(address, kind)]
        match result with
        | .ok next =>
          kenv := next
          for (rowAddress, rowKind) in rows do
            consumed := consumed.insert rowAddress
            counts := counts.insert "accept" (counts.getD "accept" 0 + 1)
            emit ⟨rowAddress, names.getD rowAddress #[], rowKind, "accept", "", micros, readMicros⟩
        | .error err =>
          let (outcome, reason) := errorOutcome err
          for (rowAddress, rowKind) in rows do
            consumed := consumed.insert rowAddress
            failed := failed.insert rowAddress rowAddress
            counts := counts.insert outcome (counts.getD outcome 0 + 1)
            emit ⟨rowAddress, names.getD rowAddress #[], rowKind, outcome, reason, micros, readMicros⟩
          reasons := reasons.insert reason (reasons.getD reason 0 + 1)
  running.set false
  let ranked := reasons.toArray.qsort (fun a b => a.2 > b.2)
  IO.eprintln s!"census: done in {(← IO.monoMsNow) - started} ms; {counts.toList}"
  IO.eprintln s!"census: peak RSS {(← statusKb "VmHWM:") / 1024} MB"
  IO.eprintln "census: first-cause reasons by frequency:"
  for (reason, count) in ranked.extract 0 25 do
    IO.eprintln s!"  {count}\t{reason}"
  return 0

end Benchmarks.Kernel.Census
