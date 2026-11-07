import IxCCTests.Fir.Support
import IxCC.Rt.Lower
import IxCC.Rt.Readback
import IxCC.Lir.Semantics
import IxCC.Lir.WellFormed
import IxCC.Lir.Print

/-! Shared support for the runtime suite (`tests-rt`, M1.F6): the Lir-level
region with `cx_init` run on it, Cfg and Lir side by side, the value
relation, typed readback, and the clock relation.

**The region.** The Lir models map one region at `base` (64 KiB unless a
test asks for less), zero-filled as a fresh `mmap` is, with `ctx = base +
64` (04 §6). `cx_init` runs on it through `Lir.eval`, and its effect is
checked against an independent expectation of the context block; runs then
start from a copy of that memory whose bytes are a table (`X86.Memory` is a
closure chain, so the ~600 bytes `cx_init` writes would otherwise be walked
on every later read).

**Cfg against Lir** (04 §8, 06 S32). Cfg's clock is total and charges the
entry, calls, tail calls and back edges; Lir charges calls, tail calls and
backward edges, and `Lir.eval` enters `main` without a charge. `Rt.lower`
maps each Cfg charge after the entry to exactly one Lir charge, so a run's
least Lir clock is its least Cfg clock minus one, and the timeout clause
reads "Cfg times out at `k + 1` ⇒ Lir times out at `k`, or fails with an
allowed resource" (identity from the entry on). A Cfg value is related to
the Lir word and memory by `relate` (04 §8 `ValRel` with `ImmortalAt`: the
immediates' words, and cells at distinct, disjoint, aligned addresses in
`[start, bump)` with the immortal header and related fields), the object
area holds exactly Cfg's cells (`bump − start` is their total size), and
typed readback (`Rt.readback`) equals `Own.Heap.readback` when the result
type is known. Lir may also fail with `heap` (exactly when Cfg's cells do
not fit) or `natOverflow`. -/

namespace IxCCTests.Rt

open IxCC IxCCTests.Src IxCCTests.Lam IxCCTests.Anf IxCCTests.Fir
open IxCC.Sem (Result Obs)

abbrev Word := Lir.Word

/-! ## The region -/

def base : Word := 0x10000
def ctx : Word := base + 64
def defaultSize : Nat := 0x10000
def defaultBudget : Word := 0xE0000

def inRegion (size : Nat) (a : Word) : Bool := base ≤ a && a < base + UInt64.ofNat size

/-- A zero-filled region of `size` bytes. -/
def region (size : Nat) : X86.Memory :=
  { bytes := fun _ => 0, readable := inRegion size, writable := inRegion size }

/-- The first object address, and the region's end. -/
def start : Word := UInt64.ofNat (Rt.objectsStart base.toNat)
def limitOf (size : Nat) : Word := base + UInt64.ofNat size

/-- The bytes of the context block (and the padding to the first object). -/
def blockBytes : Nat := (start - base).toNat

/-- What `cx_init` must leave in the context block: the four fields, the
rest zero (04 §6). -/
def expectedBlock (size : Nat) (budget : Word) : List UInt8 :=
  let fields : List (Int × Word) :=
    [(Rt.stackBudgetOff, budget), (Rt.bumpOff, start), (Rt.limitOff, limitOf size), (Rt.regionBaseOff, base)]
  (List.range blockBytes).map fun (i : Nat) =>
    let off : Int := Int.ofNat i - Int.ofNat Rt.ctxOffset
    match fields.find? fun (o, _) => o ≤ off && off < o + 8 with
    | some (o, v) => (v >>> UInt64.ofNat (8 * (off - o).toNat)).toUInt8
    | none => 0

/-- A region whose context block holds `block` (all else zero). -/
def withBlock (size : Nat) (block : Array UInt8) : X86.Memory :=
  { bytes := fun a => if base ≤ a && a < base + UInt64.ofNat block.size then block[(a - base).toNat]! else 0
    readable := inRegion size, writable := inRegion size }

/-- Run `cx_init` at Lir on a fresh region and check its result and the
context block; the memory to start runs from. -/
def initRegion (l : IxCC.Rt.Lowered) (size : Nat := defaultSize) (budget : Word := defaultBudget) :
    Except String X86.Memory := do
  match Lir.eval { l.program with main := l.init } 10 [UInt64.ofNat size, budget] (region size) ctx with
  | .ok ([free], m) =>
    unless free == limitOf size - start do throw s!"cx_init returned {free}, not {limitOf size - start}"
    let block := (List.range blockBytes).map fun i => m.bytes (base + UInt64.ofNat i)
    unless block == expectedBlock size budget do throw "cx_init left an unexpected context block"
    pure (withBlock size block.toArray)
  | .resource r => throw s!"cx_init failed: {repr r}"
  | _ => throw "cx_init did not return one word"

/-- `cx_init`'s checks: a region below 4 KiB, misaligned or wrapping fails
with `heap`. -/
def initFails (l : IxCC.Rt.Lowered) (at_ : Word) (size : Nat) : Bool :=
  let mem : X86.Memory := { bytes := fun _ => 0, readable := fun _ => true, writable := fun _ => true }
  match Lir.eval { l.program with main := l.init } 10 [UInt64.ofNat size, defaultBudget] mem (at_ + 64) with
  | .resource .heap => true
  | _ => false

/-- The memory with `limit` lowered to `start + bytes` (a small object
area, for heap exhaustion). -/
def withLimit (m : X86.Memory) (bytes : Nat) : X86.Memory :=
  m.write64 (ctx - 32) (start + UInt64.ofNat bytes)

/-! ## Words and runs -/

def tag (n : Nat) : Word := UInt64.ofNat (2 * n + 1)

def runLir (l : IxCC.Rt.Lowered) (root : Nat) (k : Nat) (args : List Nat) (m : X86.Memory) : IO Lir.Outcome :=
  IO.lazyPure fun _ => Lir.eval { l.program with main := root } k (args.map tag) m ctx

def lirOutcome : Lir.Outcome → String
  | .ok (vs, _) => s!"ok {vs.map (·.toNat)}"
  | .timeout => "timeout"
  | .stuck => "stuck"
  | .trap => "trap"
  | .resource r => s!"resource {repr r}"

/-- An extra target outcome `Rt.lower_correct` allows anywhere (04 §8). -/
def allowed : Lir.Outcome → Bool
  | .resource .heap | .resource .natOverflow => true
  | _ => false

/-! ## The value relation -/

/-- A placement: each location's address. -/
abbrev Placement := List (Nat × Word)

/-- Own's value against a Lir word (04 §8 `ValRel`, cells `ImmortalAt`):
the placement grows as cells are met, stays injective, and every cell lies,
8-aligned, in `[lo, hi)` with the immortal header and related fields. -/
def relate (H : Own.Heap) (m : X86.Memory) (lo hi : Word) : Nat → Placement → Own.RVal → Word → Option Placement
  | _, P, .lit (.nat n), w => if Rt.natWord n == some w then some P else none
  | _, _, .lit (.str _), _ => none
  | _, P, .ctor0 c, w => if w == Rt.ctor0Word c.tag then some P else none
  | _, P, .erased, w => if w == Rt.erasedWord then some P else none
  | 0, _, .loc _, _ => none
  | fuel + 1, P, .loc ℓ, w =>
    match P.lookup ℓ with
    | some w' => if w == w' then some P else none
    | none =>
      if P.any (·.2 == w) then none else
      match H.cell? ℓ with
      | some (.live _ .static b) =>
        let n := b.fields.length
        if w % 8 != 0 || w < lo || hi < w + UInt64.ofNat (Rt.cellBytes n) then none else
        match m.read64? w with
        | .ok h =>
          if h != Rt.immortalHeader n b.ctor.tag then none else
          b.fields.zipIdx.foldlM (init := (ℓ, w) :: P) fun P (v, i) =>
            match m.read64? (w + UInt64.ofNat (8 + 8 * i)) with
            | .ok x => relate H m lo hi fuel P v x
            | .error _ => none
        | .error _ => none
      | _ => none

/-- The placed cells do not overlap. -/
def disjoint (H : Own.Heap) (P : Placement) : Bool :=
  let spans := P.map fun (ℓ, w) =>
    let n := match H.cell? ℓ with
      | some (.live _ _ b) => b.fields.length
      | _ => 0
    (w, w + UInt64.ofNat (Rt.cellBytes n))
  let sorted := spans.mergeSort fun a b => a.1 ≤ b.1
  (sorted.zip (sorted.drop 1)).all fun (a, b) => a.2 ≤ b.1

/-- The object area's size for Cfg's cells. -/
def heapBytes (H : Own.Heap) : Nat :=
  H.cells.foldl (fun n c => match c with
    | .live _ _ b => n + Rt.cellBytes b.fields.length
    | .dead => n) 0

/-! ## Result types -/

/-- The signature of `Nat`, `Bool` (inductive 0, by the program's tags)
results. -/
def boolSig (P : Cfg.Program) : Rt.Sig :=
  let tagOf := fun (k : Option Key.CtorKey) => (k.bind (Fir.CtorInfo.ofKey P.ctors)).map (·.tag)
  let n := match tagOf P.known.boolFalse, tagOf P.known.boolTrue with
    | some f, some t => max f t + 1
    | _, _ => 2
  { inds := [List.replicate n []] }

/-- A first-order constant's result type from its Src type: `Nat` or `Bool`. -/
def resultTy (p : Src.Program) (c : Src.CId) : Option Rt.FoTy := do
  let d ← p.decl? c
  match (Src.Term.pis d.type).2 with
  | .const r [] => if some r == p.known.nat then some .nat else if some r == p.known.bool then some (.ind 0) else none
  | _ => none

/-! ## Levels -/

/-- An Anf program lowered to Cfg and to Lir. -/
structure Staged where
  levels : Levels
  lir : IxCC.Rt.Lowered
  /-- The memory runs start from (after `cx_init`). -/
  mem : X86.Memory

def lowerAll (A : AProgram) (names : List String := []) : Except String Staged := do
  let L ← lower A
  let l ← (Rt.lower { names } L.cfg).mapError (·.render)
  let mem ← initRegion l
  pure { levels := L, lir := l, mem }

/-- The functions a Cfg function calls or tail-calls. -/
def callees (fd : Cfg.Fun) : List Nat :=
  fd.blocks.flatMap fun b =>
    b.body.filterMap (fun | .bind _ (.fir (.call g _)) => some g | _ => none) ++
      match b.term with
      | .tcall g _ => [g]
      | _ => []

/-- Whether a root reaches a primitive `Rt.lower` calls a runtime procedure
for (`natPow`, `natGcd`), whose loops add Lir charges. -/
def reachesProcs (C : CProgram) (root : Nat) : Bool := Id.run do
  let mut seen : List Nat := []
  let mut todo := [root]
  for _ in [0:C.instrs + C.size + 1] do
    match todo with
    | [] => break
    | f :: rest =>
      todo := rest
      if seen.contains f then continue
      seen := f :: seen
      if let some fd := C.fun? f then
        todo := callees fd ++ todo
  seen.any fun f => match C.fun? f with
    | some fd => fd.blocks.any fun b => b.body.any fun
      | .bind _ (.fir (.prim .natPow _)) | .bind _ (.fir (.prim .natGcd _)) => true
      | _ => false
    | none => false

/-- `Lir.WellFormed` with the reason. -/
def checkLir (a : Assert) (l : IxCC.Rt.Lowered) (label : String) : IO Unit := do
  match l.program.check with
  | .ok () => expect a true ""
  | .error e => expect a false s!"{label}: Lir not WellFormed: {e}\n{l.program.text}"
  -- nothing left for the splitter
  expect a (l.program.funcs.toList.all fun f => f.splitCriticalEdges == f)
    s!"{label}: Lir has a critical edge"

/-! ## Cfg against Lir -/

structure Tally where
  runs : Nat := 0
  ok : Nat := 0
  trap : Nat := 0
  timeout : Nat := 0
  stuck : Nat := 0
  /-- Lir's allowed extra outcomes. -/
  heap : Nat := 0
  natOverflow : Nat := 0
  /-- Runs whose least Lir clock is the least Cfg clock minus one. -/
  exact : Nat := 0
  /-- Timeout-clause instances checked. -/
  clause : Nat := 0
  /-- Typed readbacks compared, cells related. -/
  typed : Nat := 0
  cells : Nat := 0
  deriving Inhabited

def Tally.render (t : Tally) : String :=
  s!"{t.runs} runs: ok {t.ok}, trap {t.trap}, timeout {t.timeout}, stuck {t.stuck}; " ++
  s!"Lir heap {t.heap}, natOverflow {t.natOverflow}; {t.exact} clock-exact (Lir = Cfg − 1), " ++
  s!"{t.clause} timeout-clause instances; {t.typed} typed readbacks, {t.cells} cells related"

def Tally.add (t u : Tally) : Tally :=
  { runs := t.runs + u.runs, ok := t.ok + u.ok, trap := t.trap + u.trap, timeout := t.timeout + u.timeout
    stuck := t.stuck + u.stuck, heap := t.heap + u.heap, natOverflow := t.natOverflow + u.natOverflow
    exact := t.exact + u.exact, clause := t.clause + u.clause, typed := t.typed + u.typed
    cells := t.cells + u.cells }

/-- One run to compare. -/
structure Run where
  label : String
  cfg : CProgram
  lir : IxCC.Rt.Lowered
  /-- The root: Cfg's function and Lir's (the same id). -/
  root : Nat
  args : List Nat
  mem : X86.Memory
  /-- The object area's size (default: the whole region). -/
  capacity : Nat := (limitOf defaultSize - start).toNat
  ty : Option (Rt.Sig × Rt.FoTy) := none
  /-- The program calls no runtime procedure, so Lir's charges are Cfg's
  after the entry. -/
  exact : Bool := true

/-- Check a Lir success against Cfg's value and heap. -/
def checkValue (a : Assert) (r : Run) (v : Own.RVal) (H : Own.Heap) (w : Word) (m : X86.Memory)
    (msg : String → String) (t : Tally) : IO Tally := do
  let bump := m.read64 (ctx - 40)
  expect a (bump - start == UInt64.ofNat (heapBytes H))
    (msg s!"the object area holds {bump - start} bytes, Cfg's {H.cells.size} cells {heapBytes H}")
  match relate H m start bump (H.size + 1) [] v w with
  | some P =>
    expect a (disjoint H P) (msg "cells overlap")
    let t := { t with cells := t.cells + P.length }
    match r.ty with
    | some (sig, ty) =>
      let got := Rt.readback sig ((limitOf defaultSize - base).toNat / 8) m ty w
      expect a (got == H.readback v) (msg s!"typed readback {repr got}, Cfg {repr (H.readback v)}")
      pure { t with typed := t.typed + 1 }
    | none => pure t
  | none => do expect a false (msg s!"the Lir word {w} is not related to Cfg's {v.shape}"); pure t

/-- Compare Cfg (the reference, at total clock `clock`) with Lir on one run. -/
def compare (a : Assert) (r : Run) (clock : Nat) (t : Tally) : IO Tally := do
  let rc ← runCfg .immortal r.cfg clock r.root r.args
  let t := { t with runs := t.runs + 1 }
  let msg := fun (s : String) => s!"{r.label} {r.args}: {s} (Cfg {ownOutcome rc})"
  let lir := fun k => runLir r.lir r.root k r.args r.mem
  -- the timeout clause at a clock: Cfg timing out at k + 1 means Lir times out at k
  let clause := fun (k : Nat) (t : Tally) => do
    let c ← runCfg .immortal r.cfg (k + 1) r.root r.args
    if isTimeout c then
      let l ← lir k
      expect a (isTimeout l || allowed l) (msg s!"Cfg times out at {k + 1}, Lir at {k} gives {lirOutcome l}")
      pure { t with clause := t.clause + 1 }
    else pure t
  match rc with
  | .ok (v, H) =>
    let some kc ← leastUp (fun k => do return !isTimeout (← runCfg .immortal r.cfg k r.root r.args)) 0 (1 <<< 40)
      | do expect a false (msg "no least Cfg clock"); pure t
    expect a (kc > 0) (msg "Cfg finishes at clock 0")
    let some kl ← leastUp (fun k => do return !isTimeout (← lir k)) (kc - 1) (1 <<< 40)
      | do expect a false (msg "Lir never finishes"); pure t
    match ← lir kl with
    | .resource .heap =>
      expect a (heapBytes H > r.capacity) (msg s!"Lir fails with heap, but Cfg's {heapBytes H} bytes fit {r.capacity}")
      pure { t with heap := t.heap + 1 }
    | .resource .natOverflow => pure { t with natOverflow := t.natOverflow + 1 }
    | .ok ([w], m) =>
      expect a (heapBytes H ≤ r.capacity) (msg s!"Cfg's {heapBytes H} bytes do not fit {r.capacity}, yet Lir succeeds")
      let t ← checkValue a r v H w m msg t
      -- the least Lir clock is one below Cfg's (the entry), or above it by
      -- the runtime procedures' charges
      if r.exact then expect a (kl + 1 == kc) (msg s!"least clocks: Lir {kl}, Cfg {kc}")
      else expect a (kl + 1 ≥ kc) (msg s!"least clocks: Lir {kl} below Cfg's {kc} − 1")
      if kl > 0 then
        let below ← lir (kl - 1)
        expect a (isTimeout below) (msg s!"Lir below {kl} gives {lirOutcome below}")
      let mut t := if kl + 1 == kc then { t with exact := t.exact + 1 } else t
      for k in (if kl ≤ 6 then List.range (kl + 1) else [0, 1, kl / 2, kl - 1, kl]) do
        t ← clause k t
      pure { t with ok := t.ok + 1 }
    | l => do expect a false (msg s!"Lir at its least clock {kl} gives {lirOutcome l}"); pure t
  | .trap =>
    let l ← lir clock
    expect a (l matches .trap || allowed l) (msg s!"a Cfg trap is Lir {lirOutcome l}")
    pure { t with trap := t.trap + 1 }
  | .timeout =>
    let t ← clause (clock - 1) t
    pure { t with timeout := t.timeout + 1 }
  | .stuck => pure { t with stuck := t.stuck + 1 }
  | .resource _ => do expect a false (msg "Cfg never fails with a resource"); pure t

end IxCCTests.Rt
