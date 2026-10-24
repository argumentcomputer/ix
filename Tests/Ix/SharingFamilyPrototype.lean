import Tests.Ix.SharingUniform
import Ix.Sharing.FamilyNormalizeArea

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
      -- Repeated/reordered components and an empty endpoint expose stale
      -- positions without requiring a large corpus or changing any family.
      let repeated := { stage with comps := stage.comps ++ stage.comps.reverse ++ #[#[]] }
      for experimentK in [0, 3] do
        let cfg : Config := ⟨experimentK⟩
        let reference := repeated.comps.mapIdx fun j ms => component cfg ex repeated width j ms
        let cached := componentsCachedWith cfg ex repeated width
        ensure (cached.map (·.tsv "cached") == reference.map (·.tsv "cached"))
          "cached stage changed full traces after repeated/reordered components"
        let parents := parentsOf ex.dag
        let zeroA := Array.replicate repeated.up.prep.dag.size 0
        let zeroC := Array.replicate ex.dag.size 0
        let mut state : CacheState := (#[], zeroA, zeroC)
        for item in repeated.comps.zipIdx do
          state := cachedStep cfg ex repeated width parents state item
          ensure (state.2.1 == zeroA && state.2.2 == zeroC)
            "cached component left touched positions uncleared"
        ensure (state.1.map (·.tsv "cached") == reference.map (·.tsv "cached"))
          "cached step fold differs from the stage loop"
        let bad := { repeated with cand := #[] }
        let badReference := bad.comps.mapIdx fun j ms => component cfg ex bad width j ms
        ensure ((componentsCachedWith cfg ex bad width).map (·.tsv "fallback") ==
          badReference.map (·.tsv "fallback")) "cached representation fallback changed traces"
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

private def meterImage (outcome : Except SharingError MeterState) :=
  outcome.map fun (results, states, work) =>
    (results.map (fun (r : CompResult) => (r.members, r.bestDelta, r.bestSet, r.bySize)), states, work)

private def sameOutcome [BEq α] (a b : Except SharingError α) : Bool :=
  match a, b with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def areaControls : IO Nat := do
  let inputs := runGen 712 ((List.range 12).mapM fun _ => Tests.SharingUniform.genSearchRoots)
  let mut exercised := 0
  for roots in inputs do
    let ex ← IO.ofExcept ((expand {} #[] roots false).mapError toString)
    for width in [1, 2, 3] do
      let sg := uniformStageF width ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      let sg := { sg with comps := sg.comps ++ sg.comps.reverse ++ #[#[]] }
      let parents := parentsOf ex.dag
      let tb := TBase.ofPrep sg.up.prep sg.up.w sg.up.opaq
      for k in [0, 3, 8] do
        let cfg : Config := ⟨k⟩
        for limits in [({} : Limits), { maxStates := 0 }, { maxCostEvals := 0 }] do
          ensure (sameOutcome (meterImage (familyComponentsArea cfg limits ex sg width parents))
            (meterImage (familyComponents cfg limits ex sg width parents)))
            "area fold changed retained rows, counters, or exact refusal after repeated components"
        if ex.dag.size > 0 then
          -- Preserve every array bound while violating the opacity premise:
          -- the first DAG term is a leaf whose inline cost is below this width.
          let badStage := { sg with up := { sg.up with
            opaq := sg.up.opaq.set! 0 true, w := tb.inl[0]! + 1 } }
          ensure (!tStageOK badStage.up.prep badStage.up.w badStage.up.opaq
            (TBase.ofPrep badStage.up.prep badStage.up.w badStage.up.opaq)) "bad stage passed the guard"
          ensure (sameOutcome (meterImage (familyComponentsArea cfg {} ex badStage width parents))
            (meterImage (familyComponents cfg {} ex badStage width parents))) "stage fallback changed result"
        if !tStageOK sg.up.prep sg.up.w sg.up.opaq tb then continue
        for (members, index) in sg.comps.zipIdx do
          let cx := componentContext ex sg members
          let zero := Array.replicate ex.dag.size 0
          let posA := setPositions zero cx.area
          let posC := setPositions zero cx.closure
          let (actual, a, c) := familyAreaEvaluation cfg ex cx tb parents width index members zero posC
          let (expected, ea, ec) := cachedEvaluation cfg cx width index members zero posC
          ensure (actual.tsv "area" == expected.tsv "area" && a == ea && c == ec && a == zero && c == zero)
            "area evaluator changed a full trace or left touched positions uncleared"
          if familyAreaOK ex cx parents posA posC && !members.isEmpty then
            exercised := exercised + 1
            let aux := familyAreaAux ex cx posA tb
            for row in expected.rows do
              if let some (_, selected) := row then
                ensure (phiA { cx with closure := #[], rootsC := #[], storedInC := #[] }
                    posA tb aux (fun _ => (cx, posC)) selected.contains selected ==
                  phiEL2 cx posA posC selected.contains selected) "area cost/work pair changed"
            let badArea := { cx with area := #[] }
            ensure (!familyAreaOK ex badArea parents zero posC &&
              (familyTraceArea cfg ex badArea tb parents width index members zero posC).tsv "bad" ==
                (traceWithPositions cfg badArea width index members zero posC).tsv "bad")
              "missing-member area did not retain the closure fallback"
          let badCx := { cx with cand := #[] }
          if ex.dag.size > 0 then
            let (bad, _, _) := familyAreaEvaluation cfg ex badCx tb parents width index members zero posC
            ensure (!localSearchOK badCx && bad.tsv "bad" ==
              (traceWithPhi cfg badCx width index members badCx.phiE).tsv "bad")
              "malformed context bypassed the specification fallback"
  -- A real leaf deliberately mislabeled opaque at width 3 must fail the
  -- per-evaluation opacity test, independently of the outer stage guard.
  let ex ← IO.ofExcept ((expand {} #[] #[.var 0] false).mapError toString)
  let sg := uniformStageF 3 ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
  let original := componentContext ex sg #[0]
  let cx := { original with up := { original.up with opaq := #[true] } }
  let tb := TBase.ofPrep cx.up.prep cx.up.w cx.up.opaq
  let posA := setPositions #[0] cx.area
  let posC := setPositions #[0] cx.closure
  let aux := familyAreaAux ex cx posA tb
  let (cost, inl, sides, _) := areaFold cx.up.prep cx.up.opaq tb cx.up.w cx.area posA (memberFlags cx posA (fun _ => false))
  ensure (!aux.storedA.all (tGuard cx.up.prep tb.tTail cx.up.w (rdA posA cost tb.cost)
    (rdA posA inl tb.inl) (rdA posA sides tb.sides))) "opacity negative control did not reject"
  ensure (phiA { cx with closure := #[], rootsC := #[], storedInC := #[] } posA tb aux
      (fun _ => (cx, posC)) (fun _ => false) #[] == phiEL2 cx posA posC (fun _ => false) #[])
    "per-evaluation opacity fallback changed the full cost/work pair"
  ensure (exercised > 0) "area controls never exercised a nonempty guarded area"
  IO.println s!"family area: {exercised} nonempty guarded traces; full pairs, repeated folds, refusals and fallbacks"
  return exercised

def suite : List TestSeq := [
  .individualIO "experimental component families preserve costs, counts and canonical ties" none (do
    genericControls
    let tested ← modelControls
    let areaTested ← areaControls
    return (true, tested + areaTested, 0, none)) .done]

end Tests.SharingFamilyPrototype
