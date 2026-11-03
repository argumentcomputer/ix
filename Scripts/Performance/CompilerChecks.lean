import Tests.Ix.Compile.Performance

/-! Native entry for the source-unit and family-check cache regressions and
scale fixtures. Arguments: `test`, `unit COUNT`, or `family COUNT`.
Construction is outside each measurement. Family timing compares the cached
entry to the direct, unchanged `familyBlockOk` reference helper.
-/

open Tests.Ix.Compile.Performance

private def benchMeasure (label : String) (action : Unit → α) : IO α := do
  let start ← IO.monoNanosNow
  let result ← IO.lazyPure action
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"{label} ns={elapsed}"
  return result

private def unitScale (count : Nat) : IO Unit := do
  let data ← unitFixture count
  let indexed ← benchMeasure s!"unit-index auxiliaries={count}" fun _ =>
    (Ix.EnvScope.unitIndex data.env.constants).getD data.root #[]
  unless indexed.size == count do throw (IO.userError "unit index omitted auxiliaries")
  let reference ← benchMeasure s!"raw-closure auxiliaries={count}" fun _ =>
    (Ix.EnvScope.collectDeps data.env data.expected).map (·.1)
  let selected ← benchMeasure s!"selected-closure auxiliaries={count}" fun _ =>
    (Ix.EnvScope.collectSelectedDeps data.env [data.root]).map (·.1)
  unless selected == reference && selected.length == 2 * count + 1 do
    throw (IO.userError "selected closure lost auxiliary dependencies or gained unrelated input")

private def familyScale (count : Nat) : IO Unit := do
  let data ← IO.lazyPure fun _ => familyFixture count
  let reference ← benchMeasure s!"family-reference constructors={count}" fun _ =>
    familyReference data.env data.blocks {}
  let cached ← benchMeasure s!"family-cached constructors={count}" fun _ =>
    Ix.Cert.strayFamilyMemberWithCached data.env data.blocks {}
  unless reference.isNone && decide (cached = reference) do
    throw (IO.userError "valid family was rejected or cached result differs")

def main (args : List String) : IO UInt32 := do
  match args with
  | ["test"] => Tests.Ix.Compile.Performance.run
  | ["unit", count] => unitScale count.toNat!
  | ["family", count] => familyScale count.toNat!
  | _ => throw (IO.userError "expected test, unit COUNT, or family COUNT")
  return 0
