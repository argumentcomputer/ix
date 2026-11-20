import IxAIData

/-! Load an extraction with `IxAIData.readExtraction`, then curate a slice of its items
(the first `LIMIT` in declaration order) with `IxAIData.curate`. -/

open IxAIData

def main (args : List String) : IO UInt32 := do
  let dir :: limit :: test := args | IO.eprintln "usage: Dry DIR LIMIT TEST-MODULE…"; return 2
  let t0 ← IO.monoMsNow
  let ex ← readExtraction dir
  let t1 ← IO.monoMsNow
  IO.println s!"read {t1 - t0} ms: modules {ex.modules.size}, library theorems {ex.library.size}, scope theorems {ex.items.size}, names {ex.names.size}, unaddressed names {ex.unjoined}"
  let policy ← match policyOf ex with
    | .ok p => pure p
    | .error e => IO.eprintln e; return 1
  let slice := { ex with items := ex.items.extract 0 limit.toNat! }
  let testIdx := (List.range ex.modules.size).filter fun i => test.contains (ex.modules[i]!.name)
  let c := curate slice policy (testIdx.contains ·)
  let t2 ← IO.monoMsNow
  IO.println s!"curate {t2 - t1} ms on {slice.items.size} items: accepted {c.accepted.length}, refused {c.refusals.map fun (r, n) => s!"{repr r} {n}"}, deduped {c.deduped.length}, with premises {c.nonempty.length}, train {c.train.length}, test {c.test.length}, disjoint {c.disjoint}"
  return 0
