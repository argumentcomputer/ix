import Ix.CompileM
import Tests.Ix.Kernel.SourceIngressStep

/-! # Source-mode verdicts against the Ixon path's (untrusted harness)

The same Lean environment checked both ways, constant by constant: the
Source-mode run (`Tests.Ix.Kernel.SourceIngressStep`) and the environment
check of its Ixon compilation (`Benchmarks.Kernel.CheckIxeStep`: the Ixon
reader, the prelude's records first, one record at a time, the compiler's
hints), under the default role table and its evidence
(`Ix.Kernel.Reader.defaultTable`). A Lean name
gets the verdict of the record its compiled constant resolves to (a block
member's projection resolves to its block, a recursor to its recursor
record's row). -/

namespace Tests.Ix.Kernel.SourceIngressCompare

open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

/-- The verdicts of the Ixon environment check of `ixon`, by Lean name (the
checker's spelling of it). -/
def ixonVerdicts (ixon : Ixon.Env) :
    IO (Std.HashMap CName (String × String)) := do
  let mut store : RecordStore := {}
  for (address, lazy) in ixon.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let table ← IO.ofExcept defaultTable
  let pre ← IO.ofExcept (preludeFor table)
  let hints := Hints.ofStore store ixon.anonHints
  let s := setup store (ixon.blobs[·]?) table pre hints.lookup
  let rows ← IO.mkRef (Std.HashMap.emptyWithCapacity (α := Address) (β := String × String) 0)
  let names := reportNames ixon store
  let total := s.ordered.size
  let _ ← checkLoop s (names.getD · #[]) s.ordered {}
    (fun row => rows.modify (·.insert row.address (row.outcome, row.reason)))
    (progress := fun i _ => do
      if i % 10000 == 0 then IO.eprintln s!"source-ingress: ixon check {i}/{total}")
  let rows ← rows.get
  let mut out : Std.HashMap CName (String × String) := {}
  for (name, named) in ixon.named.toList do
    let root := match store[named.addr]? with
      | some source => owner named.addr source
      | none => named.addr
    match rows[named.addr]? <|> rows[root]? with
    | some v => out := out.insert (Ix.LeanIngress.ingressKey name) v
    | none => pure ()
  return out

/-- A comparison: per pair of outcomes (Source, Ixon) the constants, and the
differing constants with both reasons. -/
structure Comparison where
  pairs : Std.HashMap (String × String) Nat := {}
  differing : Array (CName × String × String × String × String) := #[]
  /-- Source constants with no Ixon verdict -/
  unmatched : Nat := 0

def compare (rows : Array Tests.Ix.Kernel.SourceIngressStep.Row)
    (ixon : Std.HashMap CName (String × String)) : Comparison := Id.run do
  let mut c : Comparison := {}
  for row in rows do
    for n in row.names do
      match ixon[n]? with
      | none => c := { c with unmatched := c.unmatched + 1 }
      | some (o, why) =>
        let key := (row.outcome, o)
        c := { c with pairs := c.pairs.insert key (c.pairs.getD key 0 + 1) }
        unless row.outcome == o do
          c := { c with differing := c.differing.push (n, row.outcome, row.reason, o, why) }
  return c

end Tests.Ix.Kernel.SourceIngressCompare
