import Tests.Ix.SharingUniform

/-! Differential test of the uncertain-component pass.

`ufFind` and `uncertainComponents` are written as folds so that their
partition can be proved. The originals (a bounded loop, and a hash-map
grouping sorted by smallest term) are kept here as test-only references:
on generated sharing inputs at every width, on random classifications of
the same DAGs and on arbitrary parent arrays, both versions must return the
same values. -/

namespace Tests.SharingComponents

open LSpec Ixon Ix.Sharing.Exact Tests.SharingExact

private def ensure (condition : Bool) (why : String) : IO Unit :=
  unless condition do throw (IO.userError why)

/-- The original union-find root lookup (a bounded loop). -/
def ufFindLoop (parent : Array Nat) (x : Nat) : Nat := Id.run do
  let mut cur := x
  for _ in [0:parent.size + 1] do
    let q := parent[cur]!
    if q == cur then break
    cur := q
  return cur

/-- The original component pass: union-find over loops, then grouping by
root through a hash map, sorted by each group's smallest term. -/
def uncertainComponentsHashed (dag : Dag) (cls : Array UClass) : Array (Array Nat) := Id.run do
  let n := dag.size
  let mut uf : Array Nat := Array.range n
  let mut reps : Array (Array Nat) := Array.replicate n #[]
  for t in [0:n] do
    if cls[t]! == .certainStored then continue
    let mut rs : Array Nat := #[]
    for c in (dag.node t).children do
      for r in reps[c]! do
        let fr := ufFindLoop uf r
        unless rs.contains fr do rs := rs.push fr
    if cls[t]! == .uncertain then
      for r in rs do
        let a := ufFindLoop uf t
        let b := ufFindLoop uf r
        if a != b then
          if a < b then uf := uf.set! b a else uf := uf.set! a b
      reps := reps.set! t #[t]
    else
      reps := reps.set! t rs
  let mut groups : Std.HashMap Nat (Array Nat) := {}
  for t in [0:n] do
    if cls[t]! == .uncertain then
      let r := ufFindLoop uf t
      groups := groups.insert r ((groups.getD r #[]).push t)
  let comps := groups.toArray.map (·.2)
  return comps.qsort fun a b => a[0]! < b[0]!

private def genClass : RGen UClass := do
  match ← rand 5 with
  | 0 => pure .certainStored
  | 1 => pure .certainExcluded
  | 2 => pure .lowDegree
  | _ => pure .uncertain

private def genClasses (n : Nat) : RGen (Array UClass) := do
  let mut out := #[]
  for _ in [0:n] do
    out := out.push (← genClass)
  return out

/-- Arbitrary parent arrays, including pointers up and out of range. -/
private def genParents : RGen (Array Nat) := do
  let n ← rand 12
  let mut out := #[]
  for i in [0:n] do
    let choice ← rand 4
    let below ← rand (i + 1)
    let wild ← rand (n + 3)
    out := out.push (match choice with
      | 0 => i
      | 1 => below
      | 2 => wild
      | _ => i / 2)
  return out

private def componentControls : IO Nat := do
  let inputs := runGen 83 ((List.range 40).mapM fun _ => Tests.SharingUniform.genSearchRoots)
  let mut tested := 0
  let mut nonempty := 0
  for (roots, seed) in inputs.zipIdx do
    let ex ← IO.ofExcept ((expand {} #[] roots false).mapError toString)
    for width in [1, 2, 3] do
      let stage := uniformStage width ex (Prep.ofDag ex.dag)
      let comps := uncertainComponents ex.dag stage.cls
      ensure (comps == uncertainComponentsHashed ex.dag stage.cls)
        s!"stage components differ from the hashed reference (input {seed}, width {width})"
      tested := tested + 1
      if !comps.isEmpty then nonempty := nonempty + 1
    for trial in [0:4] do
      let cls := runGen (1000 * seed + trial) (genClasses ex.dag.size)
      ensure (uncertainComponents ex.dag cls == uncertainComponentsHashed ex.dag cls)
        s!"random-class components differ from the hashed reference (input {seed}, trial {trial})"
      tested := tested + 1
  ensure (nonempty > 0) "no generated stage had an uncertain component"
  let parents := runGen 97 ((List.range 400).mapM fun _ => genParents)
  for parent in parents do
    for x in [0:parent.size + 2] do
      ensure (ufFind parent x == ufFindLoop parent x) "ufFind differs from the loop reference"
  IO.println s!"uncertain components: {tested} DAG/classification cases, {parents.length} parent arrays; equal to the hashed reference"
  return tested

def suite : List TestSeq := [
  .individualIO "uncertain components match the original hashed grouping" none (do
    let tested ← componentControls
    return (true, tested, 0, none)) .done]

end Tests.SharingComponents
