import Tests.Ix.SharingUniform
import Ix.Sharing.FamilyPrototypeFast

namespace Tests.SharingFamilyPrototype

open LSpec Ixon Ix.Sharing.Exact Ix.Sharing.FamilyPrototype Tests.SharingExact

private def ensure (condition : Bool) (why : String) : IO Unit :=
  unless condition do throw (IO.userError why)

/-- Independent mask enumeration, used only on tiny test components. -/
private def brute (cost : Cost) (members : Array Nat) : CTable := Id.run do
  let mut out : CTable := Array.replicate (members.size + 1) none
  for mask in [0:2 ^ members.size] do
    let selected := (members.zipIdx.filter (fun (_, i) => mask.testBit i)).map (·.1)
    let candidate := (cost selected, selected)
    let improve := match out[selected.size]! with
      | none => true
      | some (d, s) => candidate.1 < d || (candidate.1 == d && setPrec selected s)
    if improve then out := out.set! selected.size (some candidate)
  return out

private def interaction (s : Array Nat) : _root_.Int :=
  if s.size == 0 then 0
  else if s == #[0] then -5 else if s == #[1] then -4 else if s == #[2] then -3
  else if s == #[0, 1] then 10 else if s == #[0, 2] then 12
  else if s == #[1, 2] then -20 else -1

private def genericControls : IO Unit := do
  let members := [0, 1, 2]
  let zero : Cost := fun _ => 0
  ensure (greedyOrder zero members == [2, 1, 0]) "setPrec tie convention changed"
  ensure (greedyOrder zero members.reverse == [2, 1, 0]) "tie result depends on scan order"
  ensure (chain interaction members == [#[], #[0], #[0, 1], #[0, 1, 2]])
    "greedy chain stopped on an expensive extension or used initial gains"
  let exactRows := table ⟨3⟩ interaction members
  let chainRows := table ⟨2⟩ interaction members
  ensure (exactRows == brute interaction members.toArray && exactRows[2]! == some (-20, #[1, 2]))
    "exact family missed the interacting optimum"
  ensure (chainRows[2]! == some (10, #[0, 1]) && chainRows[3]! == some (-1, #[0, 1, 2]))
    "fallback lost per-count rows after a cost increase"
  ensure (table ⟨0⟩ zero [] == #[some (0, #[])]) "empty component lost its endpoint"
  for n in [1:7] do
    let ms := List.range n
    let cost : Cost := fun s => (s.foldl (fun a x => a + x * x) 0 : Nat) - (3 * s.size : Nat)
    ensure (table ⟨n⟩ cost ms == brute cost ms.toArray) "mask and recursive enumeration disagree"
    let rows := table ⟨0⟩ cost ms
    ensure (rows.size == n + 1 && rows.zipIdx.all (fun (r, k) =>
      r.any fun (d, s) => s.size == k && strictInc s && d == cost s)) "greedy count/row invariant"
    ensure (rows[n]!.any (fun (_, s) => s == ms.toArray)) "greedy endpoint is not the full component"

private def modelControls : IO Nat := do
  let inputs := runGen 71 ((List.range 60).mapM fun _ => Tests.SharingUniform.genSearchRoots)
  let mut tested := 0
  let mut interacting := 0
  for roots in inputs do
    let ex ← IO.ofExcept ((expand {} #[] roots false).mapError toString)
    for width in [1, 2, 3] do
      let stage := uniformStage width ex (Prep.ofDag ex.dag)
      for (members, i) in stage.comps.zipIdx do
        if members.size > 8 then continue
        let cx := componentContext ex stage members
        let positions := localPositions cx
        ensure positions.isSome "valid initial context bypassed the closure-local evaluator"
        let baseline := (cx.phiE (fun _ => false) #[]).1
        let cost := componentDelta cx baseline
        ensure (cost #[] == 0) "empty-subset delta is not zero"
        let precise := component ⟨members.size⟩ ex stage width i members
        let fallback := component ⟨members.size - 1⟩ ex stage width i members
        ensure (precise.exact && precise.rows == brute cost members) "exact component rows differ"
        ensure (!fallback.exact && fallback.rows.size == members.size + 1) "K/K+1 gate or full chain failed"
        for row in fallback.rows do
          ensure (row.any fun (d, s) => d == cost s && s.all members.contains && strictInc s)
            "fallback row cost/membership is not actual phiE"
          if let some (_, set) := row then
            ensure (localPhi cx positions set.contains set == cx.phiE set.contains set)
              "local evaluator changed the cost/work pair"
        let badSize := { cx with cand := #[] }
        ensure ((localPositions badSize).isNone &&
          localPhi badSize (localPositions badSize) members.contains members ==
            badSize.phiE members.contains members) "bad-size evaluator fallback changed"
        let missing := { cx with area := #[] }
        ensure (localSearchOK missing && (localPositions missing).isNone &&
          localPhi missing (localPositions missing) members.contains members ==
            missing.phiE members.contains members) "missing-member evaluator fallback changed"
        let (reference, _, _) ← IO.ofExcept ((searchComponentRef stage.up stage.f stage.opaq
          ex.roots stage.slack {} members 0 0).mapError toString)
        let kept (rows : CTable) := (rows.trim stage.slack).zipIdx.filterMap fun (r, k) => r.map (k, ·)
        ensure (kept precise.rows == kept reference.bySize)
          "full-closure delta differs from the existing independent area evaluator"
        ensure ((precise.tsv "fixture").startsWith s!"component\tfixture\t{width}\t{i}\texact\t")
          "shared trace schema changed"
        tested := tested + 1
        if members.size > 1 then interacting := interacting + 1
  ensure (tested > 0 && interacting > 0) "model controls did not exercise uncertain interactions"
  IO.println s!"family prototype: {tested} component/width cases; {interacting} non-singletons; exact/chain, actual deltas and area parity"
  return tested

def suite : List TestSeq := [
  .individualIO "experimental component families preserve costs, counts and canonical ties" none (do
    genericControls
    let tested ← modelControls
    return (true, tested, 0, none)) .done]

end Tests.SharingFamilyPrototype
