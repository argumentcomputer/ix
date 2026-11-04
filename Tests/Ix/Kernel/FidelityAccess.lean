import LSpec
import Tests.Ix.Kernel.ReaderRoundtrip

namespace Tests.Ix.Kernel.FidelityAccess

open LSpec _root_.Ix.KernelFidelity Tests.Ix.Kernel.EgressFidelity

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- Compare every report field, including the order of recorded diagnostics. -/
private def same (a b : ProjectionReport) : Bool :=
  a.blocks == b.blocks && a.compiled == b.compiled && a.written == b.written &&
  a.matched == b.matched && a.problems == b.problems &&
  a.ordered.toArray.qsort (fun x y => x.1 < y.1) == b.ordered.toArray.qsort (fun x y => x.1 < y.1) &&
  a.refused.toArray.qsort (fun x y => x.1 < y.1) == b.refused.toArray.qsort (fun x y => x.1 < y.1) &&
  a.motiveOrdered == b.motiveOrdered && a.swapsRefused == b.swapsRefused

private def expectError (r : Except String α) (message : String) : IO Unit :=
  match r with
  | .error got => ensure (got == message) s!"wrong access error: {got}; expected {message}"
  | .ok _ => throw (IO.userError s!"access error was hidden: {message}")

private def participates : Ixon.ConstTag → Bool
  | .muts | .iPrj | .cPrj | .rPrj | .dPrj => true
  | _ => false

private def check : IO Nat := do
  let (_, inp) ← Tests.Ix.Kernel.ReaderRoundtrip.input
  let bytes ← IO.ofExcept (Ixon.serEnv inp.ixon)
  let parts ← IO.ofExcept (Ixon.deEnvVerifiedLazy bytes)
  let eager := RecordAccess.ofStore inp.store inp.ixon.blobs.toList
  let streamed := RecordAccess.ofParts parts
  ensure (eager.addresses == streamed.addresses) "eager/lazy enumeration order differs"
  for a in eager.addresses do
    ensure ((← IO.ofExcept (eager.tag a)) == (← IO.ofExcept (streamed.tag a))) "record tags differ"
  let baseline := projections inp.store inp.ixon.blobs.toList
  ensure (baseline.problems.isEmpty && baseline.compiled > 0 && baseline.matched == baseline.compiled &&
    baseline.orderProblems.isEmpty && !baseline.motiveOrdered.isEmpty) "fixture projection fidelity failed"
  let some projection := eager.addresses.find? (fun a => (eager.tag a).toOption == some .cPrj)
    | throw (IO.userError "fixture has no constructor projection")
  let block := baseline.motiveOrdered[0]!
  let proj ← IO.ofExcept (eager.get projection)
  let bc ← IO.ofExcept (eager.get block)
  let .muts ms := bc.info | throw (IO.userError "recursor owner is not a mutual block")
  for view in [eager, streamed] do
    ensure (same baseline (← IO.ofExcept (projectionsAccess view))) "eager/lazy report differs"
    -- Other constant bodies are irrelevant here and must never be materialized.
    let selective : RecordAccess :=
      { view with get := fun a => do
        unless participates (← view.tag a) do throw "ordinary body was decoded"
        view.get a }
    ensure (same baseline (← IO.ofExcept (projectionsAccess selective))) "ordinary-body guard changed fidelity"
    let absent : RecordAccess :=
      { view with get := fun a => if a == block then .error "planted missing body" else view.get a }
    expectError (projectionsAccess absent) s!"fidelity: record {block}: planted missing body"
    let changed : RecordAccess :=
      { view with get := fun a => if a == block then .ok proj else view.get a }
    expectError (projectionsAccess changed) s!"fidelity: record tag changed at {block}"
    let omitted : RecordAccess := { view with addresses := view.addresses.filter (· != projection) }
    let missing ← IO.ofExcept (projectionsAccess omitted)
    ensure (missing.problems.contains s!"{Ixon.CheckOrder.owner projection proj}: written projection {projection} is not a compiler record")
      "omitted projection was not reported"
    let altered : RecordAccess :=
      { view with get := fun a => if a == projection then .ok { proj with refs := #[block] } else view.get a }
    let different ← IO.ofExcept (projectionsAccess altered)
    ensure (different.problems.contains s!"{Ixon.CheckOrder.owner projection proj}: projection {projection} differs")
      "altered projection bytes were accepted"
    let orphaned : RecordAccess :=
      { view with addresses := view.addresses.filter (· != Ixon.CheckOrder.owner projection proj) }
    let orphan ← IO.ofExcept (projectionsAccess orphaned)
    ensure (orphan.problems.contains s!"compiler projection {projection} is not written by its block")
      "orphaned projection was not reported"
    let swapped : RecordAccess :=
      { view with get := fun a => if a == block then .ok { bc with info := .muts (ms.swapIfInBounds 0 1) } else view.get a }
    let wrongOrder ← IO.ofExcept (projectionsAccess swapped)
    ensure ((wrongOrder.refused.getD "recursor" #[]).contains block && !wrongOrder.orderProblems.isEmpty)
      "swapped recursor block was not refused"
  let absentAddr := Address.blake3 "fidelity-access absent record".toUTF8
  ensure (!eager.addresses.contains absentAddr) "missing-record control collides with fixture"
  for view in [eager, streamed] do
    expectError (view.get absentAddr) s!"missing record {absentAddr}"
    expectError (projectionsAccess { view with addresses := view.addresses.push absentAddr })
      s!"fidelity: tag {absentAddr}: missing record {absentAddr}"
  let broken : Ixon.LazyConstant := { buf := .empty, len := 0 }
  let brokenParts := { parts with env := { parts.env with consts := parts.env.consts.insert projection broken } }
  expectError (projectionsAccess (RecordAccess.ofParts brokenParts))
    s!"fidelity: tag {projection}: LazyConstant.peekTag: empty bytes"
  let some window := parts.env.consts[projection]? | throw (IO.userError "projection window missing")
  let truncated : Ixon.LazyConstant := { buf := (ByteArray.empty.push bytes[window.off]!), len := 1 }
  let parseError ← match truncated.get with
    | .error e => pure e | .ok _ => throw (IO.userError "truncated projection decoded")
  let truncatedParts := { parts with env := { parts.env with consts := parts.env.consts.insert projection truncated } }
  expectError (projectionsAccess (RecordAccess.ofParts truncatedParts))
    s!"fidelity: record {projection}: {parseError}"
  let damaged := bytes.set! window.off (bytes[window.off]! ^^^ 1)
  match Ixon.deEnvVerifiedLazy damaged with
  | .error e => ensure (e.startsWith "Env.get: const bytes hash mismatch") "tamper failed for the wrong reason"
  | .ok _ => throw (IO.userError "caller authentication accepted damaged bytes")
  IO.println s!"projection access: {baseline.blocks} blocks, {baseline.compiled} projections; eager/lazy parity and strict faults"
  return baseline.compiled

def suite : List TestSeq := [
  .individualIO "lazy projection fidelity preserves exact reports and refuses access faults" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Kernel.FidelityAccess
