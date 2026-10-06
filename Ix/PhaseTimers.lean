/-
  Ix.PhaseTimers: opt-in phase timers for the Lean compiler.

  Off by default. `IX_PHASE_TIMERS=1` (any value other than empty or `0`)
  turns them on for the whole process; `ix compile-lean` then prints a phase
  table on stderr after the compile. Nothing here touches compiler output:
  every hook returns its argument unchanged, and with the flag off each hook
  is one test of a value read once from the environment.

  Two kinds of measurement:

  - **Wall phases** (`wall`): sequential steps on the driving thread
    (import, source-contract preparation, Pass 1's canonicalisation, graph,
    groundedness and condensation, the wave driver, serialisation), recorded
    in order with their milliseconds.
  - **Worker phases** (`Phase`): exclusive time inside the per-block compile,
    summed over threads. Each thread keeps a stack of open phases; entering a
    phase charges the elapsed time to the phase on top of the stack, so a
    nested phase (sharing inside an auxiliary compile, kernel ingress inside
    the aux-gen tail) is never counted twice. The sum of the worker phases is
    the total thread time spent in block compiles (a sum over up to
    `--workers` threads, so it exceeds the wall time of the driver).

  The hooks are pure functions with `@[implemented_by]` side effects. Order
  is enforced by data dependencies: `enterV ph x` returns `x`, and the timed
  computation consumes that `x` (for `CompileM`, its block state), so the
  clock is read before the computation; `exitV y` takes the computation's
  result, so the clock is read after it. Only the *logical* definitions are
  visible to proofs: they are the identity.

  Counters for the aux-gen tail's kernel (`Ix.Tc`) ingress: per tail, the
  number of constants the bridge kenv holds when the tail ends (ingested)
  and the number of those `Ix.Tc` ever read through `KEnv.get?` (looked up),
  summed over tails.
-/
module
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace Ix.PhaseTimers

/-- Worker-side phases of a block compile (exclusive time). -/
inductive Phase where
  /-- A block's compile outside every phase below (driver glue). -/
  | blockOther
  /-- `sortConsts`: the classes (collapse) of a block, everywhere. -/
  | classes
  /-- The primary compile of a block's constants (expressions, metadata). -/
  | exprCompile
  /-- The canonical sharing construction, everywhere. -/
  | sharing
  /-- The aux-gen tail outside its sub-phases: generation and glue. -/
  | auxTail
  /-- Kernel ingress into the tail's `Ix.Tc` environment (eager walks,
      fault-ins, type stubs). -/
  | auxIngress
  /-- `Ix.Tc` calls of the tail (whnf, infer, defeq). -/
  | auxTc
  /-- Compile of the generated auxiliary blocks. -/
  | auxCompile
  /-- Call-site plan computation after the tail. -/
  | callSitePlans
  /-- The second, no-aux compile of Lean's original auxiliary forms, and
      `promote_aux`. -/
  | noAux
  /-- The driver's merge of a block outcome (driving thread). -/
  | merge
  /-- Pass 3: `Ix.Compile.Pass.prepareBlock` outside the clique hook (the
      block's views, call-site rewrite and overlay; M1-h). -/
  | p3Prepare
  /-- Pass 3: the changed-clique hook (`prepareCliques`, with its rewrite). -/
  | p3Cliques
  /-- Pass 3: `compileImageBlock` (the images of a changed block's Lean
      auxiliaries, compiled under their Lean names). -/
  | p3Image
  deriving Inhabited, BEq, Repr

def Phase.idx : Phase → Nat
  | .blockOther => 0 | .classes => 1 | .exprCompile => 2 | .sharing => 3
  | .auxTail => 4 | .auxIngress => 5 | .auxTc => 6 | .auxCompile => 7
  | .callSitePlans => 8 | .noAux => 9 | .merge => 10
  | .p3Prepare => 11 | .p3Cliques => 12 | .p3Image => 13

def phaseCount : Nat := 14

def Phase.all : Array Phase :=
  #[.blockOther, .classes, .exprCompile, .sharing, .auxTail, .auxIngress, .auxTc,
    .auxCompile, .callSitePlans, .noAux, .merge, .p3Prepare, .p3Cliques, .p3Image]

def Phase.label : Phase → String
  | .blockOther => "block glue (outside the phases below)"
  | .classes => "Pass 1 classes (sortConsts)"
  | .exprCompile => "ordinary expression compile (primary blocks)"
  | .sharing => "sharing construction"
  | .auxTail => "aux-gen tail: generation and glue"
  | .auxIngress => "aux-gen tail: kernel ingress into Ix.Tc"
  | .auxTc => "aux-gen tail: Ix.Tc calls (whnf/infer/defeq)"
  | .auxCompile => "aux-gen tail: compile of the auxiliaries"
  | .callSitePlans => "call-site plans"
  | .noAux => "no-aux compile of original forms (promote_aux)"
  | .merge => "driver merge of block outcomes (driving thread)"
  | .p3Prepare => "Pass 3 prepareBlock (views, rewrite; outside the clique hook)"
  | .p3Cliques => "Pass 3 clique hook (prepareCliques)"
  | .p3Image => "Pass 3 compileImageBlock"

/-- One thread's accumulators. -/
structure ThreadAcc where
  ns : Array Nat := Array.replicate phaseCount 0
  calls : Array Nat := Array.replicate phaseCount 0
  stack : Array Nat := #[]
  last : Nat := 0
  /-- Hashes of the `KId`s `Ix.Tc` found through `KEnv.get?` since the
      current tail began. -/
  lookups : Std.HashSet UInt64 := {}
  tails : Nat := 0
  ingested : Nat := 0
  lookedUp : Nat := 0
  maxKenv : Nat := 0
  deriving Inhabited

def ThreadAcc.charge (a : ThreadAcc) (now : Nat) : ThreadAcc :=
  match a.stack.back? with
  | some top => { a with ns := a.ns.modify top (· + (now - a.last)) }
  | none => a

/-- Process-wide state: the wall phases. -/
structure Global where
  wall : Array (String × Nat) := #[]
  deriving Inhabited

/-- Per-thread accumulators live in `IO.Ref`s found through `shardCount`
    shards keyed by thread id, so threads do not contend on one map. -/
def shardCount : Nat := 256

/-- 0: not read yet; 1: off; 2: on. -/
@[noinline] private unsafe def flagRef : IO.Ref UInt8 := unsafeBaseIO (IO.mkRef 0)

@[noinline] private unsafe def globalRef : IO.Ref Global := unsafeBaseIO (IO.mkRef {})

@[noinline] private unsafe def shardRefs : Array (IO.Ref (Std.HashMap UInt64 (IO.Ref ThreadAcc))) :=
  unsafeBaseIO ((Array.range shardCount).mapM fun _ => IO.mkRef {})

private unsafe def readFlag : BaseIO Bool := do
  let v ← flagRef.get
  if v != 0 then return v == 2
  let on := match ← IO.getEnv "IX_PHASE_TIMERS" with
    | some s => s != "" && s != "0"
    | none => false
  flagRef.set (if on then 2 else 1)
  return on

@[noinline] private unsafe def enabledImpl (_ : Unit) : Bool := unsafeBaseIO readFlag

/-- Whether the timers are on (`IX_PHASE_TIMERS`). Logically `false`. -/
@[expose, implemented_by enabledImpl] def enabled (_ : Unit) : Bool := false

/-- `enabled` in `IO`. -/
def isEnabled : BaseIO Bool := pure (enabled ())

private unsafe def threadAcc : BaseIO (IO.Ref ThreadAcc) := do
  let tid ← IO.getTID
  let some shard := shardRefs[tid.toNat % shardCount]? | IO.mkRef {}
  match (← shard.get).get? tid with
  | some r => return r
  | none =>
    let r ← IO.mkRef {}
    shard.modify (·.insert tid r)
    return r

private unsafe def enterIO (ph : Nat) : BaseIO Unit := do
  let now ← IO.monoNanosNow
  let r ← threadAcc
  r.modify fun a =>
    let a := a.charge now
    { a with stack := a.stack.push ph, calls := a.calls.modify ph (· + 1), last := now }

private unsafe def exitIO : BaseIO Unit := do
  let now ← IO.monoNanosNow
  let r ← threadAcc
  r.modify fun a =>
    let a := a.charge now
    { a with stack := a.stack.pop, last := now }

@[noinline] private unsafe def enterVImpl {α : Type} (ph : Phase) (x : α) : α :=
  unsafeBaseIO (do enterIO ph.idx; pure x)

@[noinline] private unsafe def exitVImpl {α : Type} (x : α) : α :=
  unsafeBaseIO (do exitIO; pure x)

/-- Open phase `ph` on this thread; returns `x`. Logically the identity. -/
@[expose, implemented_by enterVImpl] def enterV {α : Type} (_ph : Phase) (x : α) : α := x

/-- Close this thread's innermost phase; returns `x`. Logically the
    identity. -/
@[expose, implemented_by exitVImpl] def exitV {α : Type} (x : α) : α := x

/-- Run `k` on `x` inside phase `ph` (when the timers are on). `k` must
    consume its argument: that is what orders the clock reads around it. -/
@[expose, inline] def withPhase {α : Type} {β : Type} (ph : Phase) (x : α) (k : α → β) : β :=
  if enabled () then exitV (k (enterV ph x)) else k x

@[noinline] private unsafe def noteLookupImpl {α : Type} (h : UInt64) (r : Option α) :
    Option α :=
  if r.isNone then r else unsafeBaseIO do
    let a ← threadAcc
    a.modify fun a => { a with lookups := a.lookups.insert h }
    pure r

/-- Record that `Ix.Tc` found the constant with key hash `h`; returns `r`. -/
@[implemented_by noteLookupImpl] def noteLookup {α : Type} (_h : UInt64) (r : Option α) :
    Option α := r

@[noinline] private unsafe def tailBeginImpl {α : Type} {β : Type} (_key : β) (x : α) : α :=
  unsafeBaseIO do
    if !(← readFlag) then return x
    let a ← threadAcc
    a.modify fun a => { a with lookups := {} }
    pure x

/-- An aux-gen tail starts on this thread (`key` is any per-block value: it
    keeps the call from being shared between blocks); returns `x`. -/
@[implemented_by tailBeginImpl] def tailBegin {α : Type} {β : Type} (_key : β) (x : α) : α :=
  x

@[noinline] private unsafe def tailEndImpl {α : Type} (kenvSize : Nat) (x : α) : α :=
  unsafeBaseIO do
    if !(← readFlag) then return x
    let a ← threadAcc
    a.modify fun a =>
      { a with tails := a.tails + 1, ingested := a.ingested + kenvSize
               lookedUp := a.lookedUp + a.lookups.size, maxKenv := max a.maxKenv kenvSize
               lookups := {} }
    pure x

/-- The tail ended with `kenvSize` constants in its kenv; returns `x`. -/
@[implemented_by tailEndImpl] def tailEnd {α : Type} (_kenvSize : Nat) (x : α) : α := x

private unsafe def wallIO (label : String) (ms : Nat) : BaseIO Unit :=
  globalRef.modify fun g => { g with wall := g.wall.push (label, ms) }

@[noinline] private unsafe def wallImpl (label : String) (ms : Nat) : BaseIO Unit := do
  if ← readFlag then wallIO label ms

/-- Record a wall phase of `ms` milliseconds (when the timers are on). -/
@[implemented_by wallImpl] def wall (_label : String) (_ms : Nat) : BaseIO Unit := pure ()

/-- Time an `IO` step as a wall phase. -/
def timeWall {α : Type} (label : String) (act : IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let r ← act
  wall label ((← IO.monoMsNow) - t0)
  return r

private def fmtSecs (ns : Nat) : String :=
  let ms := ns / 1000000
  let frac := ms % 1000
  let pad := if frac < 10 then "00" else if frac < 100 then "0" else ""
  s!"{ms / 1000}.{pad}{frac}"

private def pct (part whole : Nat) : String :=
  if whole == 0 then "-" else
    let t := part * 1000 / whole
    s!"{t / 10}.{t % 10}%"

private unsafe def reportImpl : BaseIO (Array String) := do
  if !(← readFlag) then return #[]
  let g ← globalRef.get
  let mut tot : ThreadAcc := {}
  let mut accs : Array ThreadAcc := #[]
  for shard in shardRefs do
    for (_, r) in (← shard.get) do
      accs := accs.push (← r.get)
  let nThreads := accs.size
  for a in accs do
    for i in [0:phaseCount] do
      tot := { tot with ns := tot.ns.modify i (· + a.ns[i]!),
                        calls := tot.calls.modify i (· + a.calls[i]!) }
    tot := { tot with tails := tot.tails + a.tails, ingested := tot.ingested + a.ingested
                      lookedUp := tot.lookedUp + a.lookedUp
                      maxKenv := max tot.maxKenv a.maxKenv }
  let mut out : Array String := #["[phase-timers] wall phases (driving thread):"]
  -- Labels starting with a space are sub-steps of the entry above them.
  let wallTotal := g.wall.foldl (fun s (l, ms) => if l.startsWith " " then s else s + ms) 0
  for (l, ms) in g.wall do
    out := out.push s!"[phase-timers]   {l}: {fmtSecs (ms * 1000000)} s ({pct ms wallTotal})"
  out := out.push s!"[phase-timers]   total of the wall phases: {fmtSecs (wallTotal * 1000000)} s"
  let workerTotal := tot.ns.foldl (· + ·) 0
  out := out.push s!"[phase-timers] worker phases (exclusive thread time, summed over \
{nThreads} threads):"
  for ph in Phase.all do
    let ns := tot.ns[ph.idx]!
    out := out.push s!"[phase-timers]   {ph.label}: {fmtSecs ns} s ({pct ns workerTotal}), \
{tot.calls[ph.idx]!} entries"
  out := out.push s!"[phase-timers]   total thread time in block compiles: {fmtSecs workerTotal} s"
  out := out.push s!"[phase-timers] aux-gen tail kernel ingress: {tot.tails} tails, \
{tot.ingested} constants ingested (sum over tails), {tot.lookedUp} of them looked up by \
Ix.Tc ({pct tot.lookedUp tot.ingested}), largest tail kenv {tot.maxKenv}"
  return out

/-- The phase table (empty when the timers are off). -/
@[implemented_by reportImpl] def report : BaseIO (Array String) := pure #[]

end Ix.PhaseTimers

end
