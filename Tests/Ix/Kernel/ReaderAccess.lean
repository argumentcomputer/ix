import LSpec
import Tests.Ix.Kernel.ReaderRoundtrip

namespace Tests.Ix.Kernel.ReaderAccess

open LSpec Tests.Ix.Kernel.ReaderFidelity Tests.Ix.Kernel.ReaderRoundtrip

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- Every report field and diagnostic order; only measured milliseconds are
normalized. Slow-record labels remain compared, not discarded. -/
private def same (a b : Report) : Bool :=
  let a : Report := { a with readMs := 0, compareMs := 0, slow := a.slow.map fun (n, _) => (n, 0) }
  let b : Report := { b with readMs := 0, compareMs := 0, slow := b.slow.map fun (n, _) => (n, 0) }
  a.records == b.records && a.readFailures == b.readFailures && a.constants == b.constants &&
  a.counts.toArray == b.counts.toArray && a.projRewrites == b.projRewrites &&
  a.generated == b.generated && a.foreign == b.foreign && a.renamedAux == b.renamedAux &&
  a.reorderedBlocks == b.reorderedBlocks && a.unmatched == b.unmatched &&
  a.problems == b.problems &&
  a.unexplained == b.unexplained && a.verdicts.toArray == b.verdicts.toArray &&
  a.pairs.toArray == b.pairs.toArray && a.examples.toArray == b.examples.toArray &&
  a.readMs == b.readMs && a.compareMs == b.compareMs && a.slow == b.slow

private def expectError (action : IO α) (messagePrefix : String) : IO Unit := do
  let error ← try let _ ← action; pure none catch e => pure (some e.toString)
  match error with
  | some e => ensure (e.startsWith messagePrefix) s!"wrong access error: {e}; expected {messagePrefix}"
  | none => throw (IO.userError s!"access error was hidden: {messagePrefix}")

private def check : IO Nat := do
  let (lean, inp) ← input
  let bytes ← IO.ofExcept (Ixon.serEnv inp.ixon)
  let parts ← IO.ofExcept (Ixon.deEnvVerifiedLazy bytes)
  let eager := InputAccess.ofInput inp
  let lazy ← IO.ofExcept (InputAccess.ofParts lean parts)
  ensure (parts.env.named.isEmpty && Ixon.Env.envelopeVersion inp.ixon == 5 &&
    !parts.env.originals.isEmpty) "fixture must exercise lazy metadata and compiled v5 originals"
  ensure (eager.store.toArray.map (·.1) == lazy.store.toArray.map (·.1)) "lazy record enumeration/collision order changed"
  ensure (eager.headers == lazy.headers) "lazy header enumeration/collision order changed"
  ensure (eager.names == lazy.names && eager.foreign == lazy.foreign) "lazy source/foreign enumeration changed"
  let mut recursors := 0
  let mut mutualRecursors := 0
  for (a, c) in inp.store.toArray do
    ensure (lazy.store[a]? == some (Benchmarks.Kernel.CheckIxeStream.skeleton c)) "wrong skeleton"
    if c.info matches .recr _ then
      recursors := recursors + 1
      ensure (lazy.store[a]? == some c) "standalone recursor was abbreviated"
    if let .muts ms := c.info then
      if ms.any (fun | .recr _ => true | _ => false) then
        mutualRecursors := mutualRecursors + 1
        ensure (lazy.store[a]? == some c) "mutual recursor body was abbreviated"
  ensure (recursors > 0 && mutualRecursors > 0) "full recursor controls were empty"
  let baseline ← run inp (keep := fun _ => true)
  ensure (baseline.records > 0 && baseline.constants > 0 && baseline.projRewrites > 0 &&
    baseline.generated > 0 && baseline.unexplained.isEmpty && baseline.unmatched.isEmpty &&
    baseline.problems.isEmpty && uncaught baseline == []) "source/reader baseline failed"
  for (n, verdict) in expected do
    ensure (baseline.verdicts[n]? == some verdict) s!"expected verdict changed for {n}"
  let v4 ← IO.ofExcept (Ixon.serEnv { inp.ixon with originals := {}, originalHintOverrides := {} })
  ensure (v4[0]? == some 0xE4 && bytes[0]? == some 0xE5) "wrong envelope versions"
  for view in [eager, lazy, ← IO.ofExcept (InputAccess.ofBytes lean v4)] do
    ensure (same baseline (← runAccess view (keep := fun _ => true))) "complete report differs"
  let roots := #[(eager.address (_root_.Ix.Name.fromLeanName (defs "Rose.size"))).get!]
  for limit in [none, some 10] do
    ensure (same (← runAccess eager limit (fun _ => true) (some roots))
      (← runAccess lazy limit (fun _ => true) (some roots))) "rooted/limited report differs"
  let n := defs "twice"
  let ixn := _root_.Ix.Name.fromLeanName n
  let a := (eager.address ixn).get!
  let c := inp.store[a]!
  let .defn d := c.info | throw (IO.userError "twice is not a definition")
  let some (block, bc) := inp.store.toArray.find? (fun (_, c) => match c.info with
    | .muts ms => ms.any (fun | .recr _ => true | _ => false) | _ => false)
    | throw (IO.userError "mutual recursor block missing")
  let .muts members := bc.info | throw (IO.userError "wrong block")
  let changed := { bc with info := .muts (members.map fun
    | .recr r => .recr { r with rules := r.rules.push { fields := 0, rhs := .sort 0 } }
    | m => m) }
  for view in [eager, lazy] do
    let only := { view with names := #[n] }
    let replace (address : Address) (result : Except String Ixon.Constant) : InputAccess :=
      { view with records := { view.records with
          get := fun k => if k == address then result else view.records.get k } }
    expectError (runAccess { only with address := fun k => if k == ixn then none else view.address k })
      "fidelity: missing source-name header"
    expectError (runAccess { only with store := view.store.erase a }) "fidelity: source record"
    expectError (runAccess { only with metadata := fun _ => .error "planted metadata failure" })
      "planted metadata failure"
    expectError (runAccess { only with metadata := fun k => do
      return { (← view.metadata k) with addr := block } }) "fidelity: metadata address changed"
    expectError (runAccess (replace a (.error "planted missing body")))
      s!"fidelity: record {a}: planted missing body"
    expectError (runAccess (replace a (.ok bc))) s!"fidelity: record tag changed at {a}"
    expectError (runAccess (replace block (.ok changed))) s!"fidelity: record structure changed at {block}"
    let altered ← runAccess (replace a (.ok { c with info := .defn { d with value := d.typ } }))
    ensure (altered.unexplained.any (·.1 == n)) "altered definition escaped source comparison"
    let missing := { view with names := #[], headers := #[], foreign := #[], store := view.store.erase block }
    expectError (runAccess missing) s!"fidelity: ordered record {block} is missing"
    expectError (runAccess { missing with headers := #[(_root_.Ix.Name.fromLeanName `Ix.synthetic, block)] })
      s!"fidelity: named record {block}"
  let missingRow := { parts with rowIdx := parts.rowIdx.erase ixn }
  expectError (do
    let view ← IO.ofExcept (InputAccess.ofParts lean missingRow)
    runAccess { view with names := #[n] }) "fidelity: missing named metadata"
  let row := parts.rowIdx[ixn]!
  let brokenMeta := { parts with namedRows := parts.namedRows.modify row fun r =>
    { r with metaOff := bytes.size, metaLen := 0 } }
  expectError (do
    let view ← IO.ofExcept (InputAccess.ofParts lean brokenMeta)
    runAccess { view with names := #[n] }) s!"fidelity: metadata {ixn.pretty}:"
  let broken : Ixon.LazyConstant := { buf := .empty, len := 0 }
  let brokenBody := { parts with env := { parts.env with consts := parts.env.consts.insert a broken } }
  expectError (IO.ofExcept (InputAccess.ofParts lean brokenBody)) s!"fidelity: tag {a}:"
  let window := parts.env.consts[a]!
  let truncated : Ixon.LazyConstant := { buf := ByteArray.empty.push bytes[window.off]!, len := 1 }
  let truncatedBody := { parts with env := { parts.env with consts := parts.env.consts.insert a truncated } }
  expectError (IO.ofExcept (InputAccess.ofParts lean truncatedBody)) s!"fidelity: record {a}:"
  expectError (IO.ofExcept (InputAccess.ofBytes lean (bytes.set! window.off (bytes[window.off]! ^^^ 1))))
    "Env.get: const bytes hash mismatch"
  let unmatched ← runAccess { lazy with names := #[] }
  ensure (!unmatched.unmatched.isEmpty) "unmatched reader coverage disappeared"
  IO.println s!"reader access: {baseline.records} records, {baseline.constants} source comparisons; \
    {recursors} full recursors, {mutualRecursors} full mutual recursor blocks; 5 report-parity runs, 26 fault/coverage controls"
  return baseline.constants

def suite : List TestSeq := [
  .individualIO "lazy reader fidelity preserves reports, recursors and explicit access failures" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Kernel.ReaderAccess
