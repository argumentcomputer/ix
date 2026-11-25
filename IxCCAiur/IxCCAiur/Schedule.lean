import IxCC.Ixon.Address
import IxCC.Fir.Syntax
import Aiur.Optimized.Basic

/-! # Circuit Schedule & Cost-Model Control Surface (`IxCCAiur.Schedule`)

Purely operational, untrusted scheduling directives that control how a
`Fir.Program` is lowered to Formal Aiur circuits without touching the
certified soundness contract:

* **Zero TCB**: every directive affects only performance (inlining, range-check
  table sizing, chip grouping, degree cap, fail-closed budgets). A wrong or
  suboptimal schedule can never make a false proof accept; at worst it bloats a
  circuit or fails a budget check.
* **Address-keyed sidecar** (following `MeasureHint`, never mutating Ixon
  content addresses): Phase 2's `open scoped Ix.Circuit` frontend exports a
  `CircuitSchedule` keyed by `Ixon.Address`, alongside optional `FunId` / name
  overrides for direct `Fir`-level scheduling.
* **Budget enforcement**: `CircuitSummary.checkBudget` fails closed before
  proving if any chip or total circuit count exceeds its declared ceiling. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.Schedule

open IxCC.Ixon

/-- Range-check table strategy for `< 2^56` natural checks. -/
inductive RangeCheckMode where
  /-- 7 lookups into `UInt8::byte_inputs` (256 fixed rows): ideal for small and
  medium programs that do not already require the 65,536-row byte-pair tables. -/
  | smallTable
  /-- 4 lookups into `UInt8::pair_inputs` (65,536 fixed rows): halves range-check
  lookups once byte-pair tables (XOR/ADD/SUB) are already active or check volume
  amortizes the 65k table. -/
  | pairTable
  /-- Automatic selection: uses `pairTable` iff bitwise/word pair ops are linked
  in the program, otherwise `smallTable` (256 rows). -/
  | auto
  deriving DecidableEq, Repr, Inhabited

/-- Inlining policy for a lowered Aiur function or lifted join point. -/
inductive InlinePolicy where
  /-- Follow sharing-aware compiler heuristics (inline single-call non-recursive
  join points and tiny non-recursive leaf functions). -/
  | auto
  /-- Mark the lowered Aiur function `isInline := true` (non-recursive only;
  Formal Aiur's `Inlining.prepare` rejects recursive cycles safely). -/
  | always
  /-- Keep as a dedicated memoized chip (`isInline := false`). -/
  | never
  deriving DecidableEq, Repr, Inhabited

/-- Per-function scheduling directives. -/
structure FnSchedule where
  inline : InlinePolicy := .auto
  /-- Optional named chip group to co-pack this function's chip with peers. -/
  group : Option String := none
  /-- Optional compile-time unroll factor for countdown loops (Phase 2/3). -/
  unroll : Option Nat := none
  /-- Optional horizontal vectorization width `K` (Phase 3). -/
  lanes : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- Fail-closed circuit compilation budget. `none` leaves a bound unchecked. -/
structure Budget where
  maxChips : Option Nat := none
  maxColumns : Option Nat := none
  maxCallsPerChip : Option Nat := none
  maxMemoryPerChip : Option Nat := none
  maxTotalColumns : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- Measured summary of one compiled chip. -/
structure ChipMetrics where
  name : String
  columns : Nat
  calls : Nat
  memory : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Measured summary of a compiled circuit system, checked against `Budget`. -/
structure CircuitSummary where
  chips : List ChipMetrics
  deriving DecidableEq, Repr, Inhabited

def CircuitSummary.totalChips (s : CircuitSummary) : Nat := s.chips.length
def CircuitSummary.maxColumns (s : CircuitSummary) : Nat :=
  s.chips.foldl (fun acc c => max acc c.columns) 0
def CircuitSummary.totalColumns (s : CircuitSummary) : Nat :=
  s.chips.foldl (fun acc c => acc + c.columns) 0
def CircuitSummary.maxCalls (s : CircuitSummary) : Nat :=
  s.chips.foldl (fun acc c => max acc c.calls) 0
def CircuitSummary.maxMemory (s : CircuitSummary) : Nat :=
  s.chips.foldl (fun acc c => max acc c.memory) 0

/-- Check `s` against `b`, returning `.error` naming the first exceeded ceiling. -/
def CircuitSummary.checkBudget (s : CircuitSummary) (b : Budget) : Except String Unit := do
  if let some lim := b.maxChips then
    if s.totalChips > lim then
      throw s!"circuit budget exceeded: {s.totalChips} chips > maxChips {lim}"
  if let some lim := b.maxColumns then
    for c in s.chips do
      if c.columns > lim then
        throw s!"circuit budget exceeded: chip {c.name} has {c.columns} columns > maxColumns {lim}"
  if let some lim := b.maxCallsPerChip then
    for c in s.chips do
      if c.calls > lim then
        throw s!"circuit budget exceeded: chip {c.name} has {c.calls} calls > maxCallsPerChip {lim}"
  if let some lim := b.maxMemoryPerChip then
    for c in s.chips do
      if c.memory > lim then
        throw s!"circuit budget exceeded: chip {c.name} has {c.memory} memory lookups > maxMemoryPerChip {lim}"
  if let some lim := b.maxTotalColumns then
    if s.totalColumns > lim then
      throw s!"circuit budget exceeded: {s.totalColumns} total columns > maxTotalColumns {lim}"
  return ()

/-- **Circuit schedule sidecar**: controls lowering, inlining, range-check table
sizing, Aiur optimizer settings, chip grouping, and fail-closed budgets. -/
structure CircuitSchedule where
  /-- Range-check table strategy (`smallTable` 256 rows vs `pairTable` 65k rows). -/
  rangeCheck : RangeCheckMode := .auto
  /-- Inline small non-recursive helpers & single-use non-recursive join points. -/
  autoInline : Bool := true
  /-- Maximum AST node count for automatic function/join-point inlining. -/
  inlineMaxNodes : Nat := 48
  /-- Automatically filter join-point captures to transitive free variables. -/
  filterJpCaptures : Bool := true
  /-- Link only the `UInt8`/`UInt32`/`UInt64` library slices actually referenced. -/
  demandLink : Bool := true
  /-- Per-content-address directives (populated by `open scoped Ix.Circuit`). -/
  byAddress : List (Address × FnSchedule) := []
  /-- Per-`FunId` overrides (direct `Fir`-level scheduling). -/
  byFun : List (Fir.FunId × FnSchedule) := []
  /-- Explicit chip grouping plan `(groupName, [chipNames...])`. -/
  groups : List (String × List String) := []
  /-- Formal Aiur optimizer configuration (degree cap, dedup, propagation). -/
  aiurConfig : Aiur.Optimized.Config := {}
  /-- Fail-closed circuit size budget. -/
  budget : Budget := {}
  deriving Inhabited

/-- Default typed/unboxed schedule: demand-linked, auto range-check table,
free-variable join-point capture filtering, sharing-aware auto-inlining. -/
def CircuitSchedule.default : CircuitSchedule := {}

/-- Resolve the `FnSchedule` for a `Fir.FunId` (preferring `byFun`, then
`byAddress` via optional address map, else default). -/
def CircuitSchedule.forFun (sched : CircuitSchedule) (f : Fir.FunId)
    (addr? : Option Address := none) : FnSchedule :=
  match sched.byFun.find? (·.1 == f) with
  | some (_, fs) => fs
  | none =>
    match addr?.bind (fun a => sched.byAddress.find? (·.1 == a)) with
    | some (_, fs) => fs
    | none => {}

end IxCC.AiurBackend.Schedule
