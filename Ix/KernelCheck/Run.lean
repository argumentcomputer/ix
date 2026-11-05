module

public import Ix.KernelCheck.Pool

@[expose] public section

/-! A normal per-record run of the host checker, at either Ixon mode.
The report contains actual outcomes; it does not compare modes or certify
aggregate byte admission. In particular, `typed` is distinct from `accept`.
The caller supplies the reading source, dependency order and display names;
selection, byte authentication and CLI policy remain outside this harness. -/

namespace Benchmarks.Kernel.CheckIxeStep

open Ix.Kernel.Reader

/-- Requested execution: `none` uses the incremental checker, `some n` the
worker pool. With tier support, the incremental checker runs whatever
`workers` asks for. -/
structure RunConfig where
  workers : Option Nat := none
  tier : Bool := false
  allowUserAxioms : Bool := false
  skip : Std.HashSet String := {}

/-- The path actually taken. Tier fallback records the original request;
no caller should describe that run as parallel tier checking. -/
inductive Execution where
  | serial
  | pool (workers : Nat)
  | serialTier (requestedWorkers : Option Nat)
  deriving BEq, Repr

def Execution.workers : Execution → Nat
  | .pool n => n
  | .serial | .serialTier _ => 1

/-- Actual per-address rows in emission order, with the loop's outcome,
reason and failed-root maps. No Boolean success erases the distinction
between accept, typed, reject, decline and blocked. This report is an
untrusted harness result, not the certified aggregate admission theorem. -/
structure RunReport where
  rows : Array Row
  counts : Std.HashMap String Nat
  reasons : Std.HashMap String Nat
  failed : Std.HashMap Address Address
  execution : Execution

/-- Run the supplied record source at its mode. Without tier support, `some n`
workers run the pool (`CheckIxePool.runOutcome`) with its install/check/replay
protocol. With tier support this harness always runs the serial loop, whose
tier checks see the per-record checked state; the pool's own tier path
(rebuilding the checked logical index after phase B) is used only by
`kernel-check-ixe --jobs`. The returned execution path is explicit,
even when a source happens to contain no tier records. Pool progress reports
provisional phase-A install counts; only the returned report has the replayed
verdicts. The report retains every emitted row, so its memory is linear in
the number of rows. -/
def runRecords (src : LoopSource σ md) (ev : Ix.Kernel.Evidences md)
    (names : Address → Array String) (addresses : Array Address) (cfg : RunConfig := {})
    (emit : Row → IO Unit := fun _ => pure ()) (log : String → IO Unit := fun _ => pure ())
    (progress : Nat → Std.HashMap String Nat → IO Unit := fun _ _ => pure ())
    (onRead : Address → Except ReadError (Read md) → Nat → IO Unit := fun _ _ _ => pure ())
    (spell : Ix.Kernel.Key md → String := toString) : IO RunReport := do
  if cfg.workers == some 0 then throw (IO.userError "record check: the pool needs a worker")
  let rows ← IO.mkRef (#[] : Array Row)
  let note := fun row => do rows.modify (·.push row); emit row
  let execution := if cfg.tier then Execution.serialTier cfg.workers else
    match cfg.workers with
    | none => .serial
    | some n => .pool n
  let out : LoopOutcome Unit ← match execution with
    | .pool n => do
      let slots ← (Array.range n).mapM fun _ => IO.mkRef (none : Option (Address × Nat))
      CheckIxePool.runOutcome src ev names addresses cfg.skip slots note log progress onRead spell
        (allowUserAxioms := cfg.allowUserAxioms)
    | .serial | .serialTier _ => do
      let out ← checkLoopWith src.view src.read src.commit (← src.init)
        (Checker.stepRecordWithUserAxioms ev cfg.allowUserAxioms) {}
        names addresses cfg.skip note (progress := fun i o => progress i o.counts)
        (onRead := onRead) (spell := spell) (tier := if cfg.tier then src.tierHook else none)
      pure { checker := (), counts := out.counts, reasons := out.reasons, failed := out.failed }
  return { rows := ← rows.get, counts := out.counts, reasons := out.reasons,
           failed := out.failed, execution }

end Benchmarks.Kernel.CheckIxeStep
