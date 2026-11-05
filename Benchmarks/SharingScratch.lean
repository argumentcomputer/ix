import Tests.Ix.SharingScratch

/-! Native regression fixture for DAG-sized scratch copies during subset
parallelism. Run `lake exe sharing-scratch 64 8`, then `64 20`: the latter
adds an unrelated subtree while preserving the component evaluation work. -/

private def argument (args : List String) (index fallback : Nat) : IO Nat :=
  match args[index]? with
  | none => pure fallback
  | some text => match text.toNat? with
    | some value => pure value
    | none => throw (IO.userError s!"expected a natural number, got {text}")

/-- Borrow the prepared graph until after the clock read, keeping teardown
of its large tables outside the measured component fold. -/
@[noinline] private def timeComponents (prepared : @& Tests.SharingScratch.Prepared) :
    IO (Except Ix.Sharing.Exact.SharingError Ix.Sharing.Family.MeterState × Nat) := do
  let start ← IO.monoNanosNow
  let outcome ← IO.lazyPure fun _ => prepared.run
  let elapsed := (← IO.monoNanosNow) - start
  return (outcome, elapsed)

def main (args : List String) : IO Unit := do
  unless args.length ≤ 2 do
    throw (IO.userError "usage: sharing-scratch [COMPONENTS [PADDING_DEPTH]]")
  let copies ← argument args 0 64
  let depth ← argument args 1 8
  let prepared ← IO.ofExcept ((Tests.SharingScratch.prepare copies depth).mapError toString)
  let parallel := prepared.parallelComponents
  IO.println s!"nodes={prepared.expanded.dag.size} components={prepared.stage.comps.size} parallel={parallel}"
  (← IO.getStdout).flush
  let (outcome, elapsed) ← timeComponents prepared
  let (results, states, work) ← IO.ofExcept (outcome.mapError toString)
  let selected := results.foldl (fun count result => count + result.bestSet.size) 0
  IO.println s!"ns={elapsed} states={states} work={work} selected={selected}"
