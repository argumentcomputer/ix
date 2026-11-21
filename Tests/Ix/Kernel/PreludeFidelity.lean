import LSpec
import Ix.CompileCertified
import Ix.EnvScope
import Tests.Ix.Kernel.ReaderRoundtrip

/-!
  Prelude fidelity regression suite (`kernel-prelude-fidelity`).
-/

namespace Tests.Ix.Kernel.PreludeFidelity

open LSpec Tests.Ix.Kernel.ReaderFidelity Tests.Ix.Kernel.ReaderRoundtrip
open Ix.Kernel.Reader (defaultTable preludeFor)
open Benchmarks.Kernel.CheckIxeStep (owner RecordStore)

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def complete (r : Report) (expected : Nat) : Bool :=
  r.constants == expected && expected > 0 && r.problems.isEmpty &&
    r.unexplained.isEmpty && r.unmatched.isEmpty

private def check : IO Nat := do
  let (lean, full) ← input
  let table ← IO.ofExcept defaultTable
  let pre ← IO.ofExcept (preludeFor table (md := .anon))
  -- The exact namespace-selection collector used by validate-lean, without
  -- adding the roundtrip fixture's explicit prelude seeds.
  let seeds := lean.constants.toList.filterMap fun (n, _) =>
    if defsModule.isPrefixOf n then some n else none
  let out ← IO.ofExcept (← _root_.Ix.CompileM.compileCertified lean
    (_root_.Ix.EnvScope.collectSelectedDeps lean seeds) 1)
  ensure out.failures.isEmpty "selected closure has compile failures"
  let outBytes ← IO.ofExcept (Ixon.serEnv out.env)
  let parts ← IO.ofExcept (Ixon.deEnvVerifiedLazy outBytes)
  let access ← IO.ofExcept (InputAccess.ofParts lean parts)
  let injected := pre.records.filter fun (a, _) => !access.store.contains a
  ensure (!injected.isEmpty) "selected closure exercises no setup-only prelude records"
  let baseline ← runAccess access
  ensure (complete baseline access.names.size && baseline.records > 0 && baseline.readFailures > 0 &&
    baseline.count "declined: partial definition" > 0 && baseline.count "declined: unsafe definition" > 0)
    s!"selected closure lost coverage or expected declines:\n{baseline.summary}"
  let ordinary ← runAccess { access with names := access.names.filter (· != defs "twice") }
  ensure (!ordinary.unmatched.isEmpty) "ordinary input without a source mapping was exempted"
  -- Once stored in the actual input, this same prelude record must regain
  -- the ordinary unmatched-entry failure, even though setup also knows it.
  let some (qa, qc) := injected.find? (fun (_, c) => match c.info with
      | .quot q => q.kind == .ind | _ => false)
    | throw (IO.userError "selected closure must omit Quot.ind")
  let stored := { access with store := access.store.insert qa qc, records := {
    access.records with
    addresses := access.records.addresses.push qa
    tag := fun a => if a == qa then .ok (_root_.Ix.KernelFidelity.recordTag qc) else access.records.tag a
    get := fun a => if a == qa then .ok qc else access.records.get a } }
  let storedReport ← runAccess stored
  ensure (storedReport.constants == access.names.size && storedReport.unmatched.size == 1 &&
    storedReport.problems.isEmpty && storedReport.unexplained.isEmpty)
    "stored prelude record's unmatched entry was exempted"
  -- Source-labelled entries are still compared when a projection obtains
  -- its missing owner from setup. Only the synthetic block label is absent.
  let fullAccess := InputAccess.ofInput full
  let emptyName := _root_.Ix.Name.fromLeanName `Empty
  let emptyAddr := full.ixon.named[emptyName]!.addr
  let emptyBlock := owner emptyAddr full.store[emptyAddr]!
  ensure (pre.records.any (·.1 == emptyBlock) && emptyAddr != emptyBlock &&
    !(fullAccess.names.any fun n => fullAccess.address (_root_.Ix.Name.fromLeanName n) == some emptyBlock))
    "Empty control is not a source projection into a setup block"
  let borrowed ← runAccess { fullAccess with
    store := fullAccess.store.erase emptyBlock
    headers := fullAccess.headers.filter (·.2 != emptyBlock) }
  ensure (complete borrowed fullAccess.names.size) "source entries of setup-only block were skipped"
  -- A malformed stored recursor prevents a setup-only inductive from
  -- reading. That reader error must surface, not disappear with its entries.
  -- The recursor keeps its type, so it is still filed under its block, and
  -- carries one rule too many, which the block's reading refuses. (Removing
  -- the recursor is no malformation: a block of one inductive that no
  -- recursor eliminates reads without one.)
  let some (ra, rc, r) := pre.records.findSome? (fun (a, c) => match c.info with
      | .recr r => some (a, c, r) | _ => none)
    | throw (IO.userError "prelude has no standalone recursor")
  let bad := { rc with info := .recr { r with rules := r.rules.push ⟨0, .sort 0⟩ } }
  let badStore : RecordStore := ({} : RecordStore).insert ra bad
  let broken := { fullAccess with
    names := #[], headers := #[], foreign := #[], store := badStore
    records := _root_.Ix.KernelFidelity.RecordAccess.ofStore badStore full.ixon.blobs.toList }
  let failure ← try let _ ← runAccess broken; pure none catch e => pure (some e.toString)
  ensure (failure.any (·.startsWith "fidelity: setup-only prelude record "))
    s!"setup-only reader failure was hidden or misclassified: {failure}"
  IO.println s!"prelude fidelity: {baseline.constants}/{access.names.size} selected-source comparisons; \
    {injected.size} setup-only records; ordinary/stored-prelude unmatched refusals, \
    {borrowed.constants} borrowed-owner source comparisons and explicit setup reader failure"
  return baseline.constants

def suite : List TestSeq := [
  .individualIO "setup-only prelude preserves source coverage and every input/error refusal" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Kernel.PreludeFidelity
