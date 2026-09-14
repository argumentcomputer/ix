module

public import Tests.Aiur.Aiur

public section

open LSpec Aiur

namespace AiurTests.CallOrder

def graphToplevel (graph : Array (Array Bool)) : Bytecode.Toplevel where
  functions := graph.map fun edges => {
    body := {
      ops := (edges.mapIdx fun i edge => if edge then #[.call i #[] 0 false] else #[]).flatten
      ctrl := .return 0 #[] }
    layout := ⟨0, 1, 7, 4⟩
    entry := true
    constrained := true }
  memorySizes := #[]

/-- Floyd-Warshall is an independent reachability oracle for the DFS-based
component producer. Exhaust all 512 directed graphs on three vertices,
including self-loops, disconnected cycles and multiple components. -/
def allThreeVertexGraphs : Bool := Id.run do
  for bits in [:512] do
    let graph := (Array.range 3).map fun i =>
      (Array.range 3).map fun j => bits / 2 ^ (3 * i + j) % 2 == 1
    let top := graphToplevel graph
    let components := top.findCallComponents
    if !({ top with callComponents := components }).validCallComponents then return false
    let mut reach := graph
    for k in [:3] do
      for i in [:3] do
        for j in [:3] do
          if reach[i]![k]! && reach[k]![j]! then
            reach := reach.set! i (reach[i]!.set! j true)
    for i in [:3] do
      if components[i]!.ranked != reach[i]![i]! then return false
      for j in [:3] do
        let same := components[i]!.order == components[j]!.order
        if same != (i == j || (reach[i]![j]! && reach[j]![i]!)) then return false
  return true

def graphChecks : TestSeq :=
  let cyclic := graphToplevel #[#[true]]
  let advice : Bytecode.Toplevel := { cyclic with
    functions := cyclic.functions.map fun (f : Bytecode.Function) =>
      { f with body := { f.body with ops := #[.call 0 #[] 0 true] } } }
  test "component producer agrees with reachability on all three-vertex graphs"
    allThreeVertexGraphs ++
  test "an unconstrained call does not introduce a recursive component"
    (!(advice.findCallComponents[0]!).ranked) ++
  test "an unranked self-cycle fails the independent certificate checker"
    (!({ cyclic with callComponents := #[⟨0, false⟩] }).validCallComponents) ++
  test "a ranked self-cycle passes the static checker and retains dynamic checks"
    (({ cyclic with callComponents := #[⟨0, true⟩] } : Bytecode.Toplevel).validCallComponents)

def structureChecks (base specialized : CompiledToplevel) : TestSeq :=
  let t := specialized.bytecode
  let idx := fun name => specialized.getFuncIdx name |>.get!
  let ranked := fun name => t.callComponents[idx name]!.ranked
  let callRank := fun parent child => (t.callRanksFor (idx parent))[idx child]!
  test "generic Aiur retains the default dynamic layout" base.bytecode.callComponents.isEmpty ++
  test "specialized bytecode carries a valid component certificate" t.validCallComponents ++
  test "acyclic group members omit row ranks"
    (!ranked `grouped_double && !ranked `grouped_pick && !ranked `calls_grouped) ++
  test "recursive group member retains its row rank" (ranked `grouped_sum_range) ++
  test "acyclic callees use rank zero" (callRank `calls_grouped `grouped_pick == .zero) ++
  test "a boundary call binds the recursive callee rank"
    (callRank `calls_grouped `grouped_sum_range == .bound) ++
  test "recursive internal calls retain ordered gaps"
    (callRank `grouped_sum_range `grouped_sum_range == .ordered) ++
  test "specialization preserves indices, inputs and selectors and never widens a function"
    (t.functions.size == base.bytecode.functions.size &&
      (t.functions.mapIdx fun i f =>
        let old := base.bytecode.functions[i]!.layout
        f.layout.inputSize == old.inputSize && f.layout.selectors == old.selectors &&
        f.layout.auxiliaries ≤ old.auxiliaries && f.layout.lookups ≤ old.lookups).all id)

/-- Run the existing proving corpus with component layouts as well as the
generic layout. It covers nested shared continuations, empty branches,
early returns, memories, advice and grouped recursion through the FFI. -/
def suite : IO UInt32 := do
  let .ok base := toplevel.compile | IO.eprintln "Generic Aiur compilation failed"; return 1
  let source := { toplevel with componentRanks := true }
  let .ok env := AiurTestEnv.build (pure source)
    | IO.eprintln "Aiur component setup failed"; return 1
  let r1 ← LSpec.lspecIO
    (.ofList [("aiur-components", [graphChecks, structureChecks base env.compiled])]) []
  let r2 ← LSpec.lspecEachIO aiurTestCases fun tc => pure (env.runTestCase tc)
  let .ok grouped := AiurTestEnv.build (pure source) testGroups
    | IO.eprintln "Grouped Aiur component setup failed"; return 1
  let r3 ← LSpec.lspecEachIO groupedTestCases fun tc => pure (grouped.runTestCase tc)
  let r4 ← LSpec.lspecIO
    (.ofList [("aiur-component-groups", [groupingStructureChecks grouped.compiled])]) []
  return if r1 == 0 && r2 == 0 && r3 == 0 && r4 == 0 then 0 else 1

end AiurTests.CallOrder

end
