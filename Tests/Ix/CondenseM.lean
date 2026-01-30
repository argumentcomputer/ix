/-
  Tests for Ix.CondenseM module.
  - Unit tests for SCC computation mirroring Rust test cases
  - Cross-implementation tests comparing Lean vs Rust SCC results
-/

import Ix.GraphM
import Ix.CondenseM
import Ix.Environment
import Ix.Meta
import LSpec

open LSpec Ix

namespace Tests.Ix.CondenseM

/-! ## Helper functions -/

/-- Create a simple Ix.Name from a string -/
def mkName (s : String) : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon s

/-- Build a reference graph from adjacency list -/
def buildGraph (edges : List (String × List String)) : Map Ix.Name (Set Ix.Name) :=
  edges.foldl (init := {}) fun acc (src, dsts) =>
    let srcName := mkName src
    let dstSet := dsts.foldl (init := {}) fun s d => s.insert (mkName d)
    acc.insert srcName dstSet

/-- Extract SCC structure as sorted list of sorted lists (for deterministic comparison) -/
def sccsToSorted (blocks : CondensedBlocks) : List (List String) :=
  let sccs := blocks.blocks.toList.map fun (_, members) =>
    (members.toList.map toString).mergeSort
  sccs.mergeSort

/-- Check if two SCC results are equivalent (same SCCs, ignoring order) -/
def sccsEq (actual expected : List (List String)) : Bool :=
  actual.length == expected.length &&
  actual.all (expected.contains ·)

/-! ## Test cases (mirroring Rust's src/ix/condense.rs tests) -/

/-- Test 1: Single node with no edges → one SCC containing just that node -/
def testSingleNode : TestSeq :=
  let graph := buildGraph [("A", [])]
  let sccs := Ix.CondenseM.run graph
  let result := sccsToSorted sccs
  test "single node: 1 SCC" (result.length == 1) ++
  test "single node: SCC contains A" (result == [["A"]])

/-- Test 2: Simple cycle A→B→A → one SCC containing both -/
def testSimpleCycle : TestSeq :=
  let graph := buildGraph [("A", ["B"]), ("B", ["A"])]
  let sccs := Ix.CondenseM.run graph
  let result := sccsToSorted sccs
  test "simple cycle: 1 SCC" (result.length == 1) ++
  test "simple cycle: SCC contains A,B" (result == [["A", "B"]])

/-- Test 3: Chain with no cycle A→B→C → three separate SCCs -/
def testChainNoCycle : TestSeq :=
  let graph := buildGraph [("A", ["B"]), ("B", ["C"]), ("C", [])]
  let sccs := Ix.CondenseM.run graph
  let result := sccsToSorted sccs
  test "chain: 3 SCCs" (result.length == 3) ++
  test "chain: each singleton" (sccsEq result [["A"], ["B"], ["C"]])

/-- Test 4: Two cycles connected: A↔B→C↔D → two SCCs -/
def testTwoCyclesConnected : TestSeq :=
  let graph := buildGraph [
    ("A", ["B"]),
    ("B", ["A", "C"]),
    ("C", ["D"]),
    ("D", ["C"])
  ]
  let sccs := Ix.CondenseM.run graph
  let result := sccsToSorted sccs
  test "two cycles: 2 SCCs" (result.length == 2) ++
  test "two cycles: correct SCCs" (sccsEq result [["A", "B"], ["C", "D"]])

/-- Test 5: Complex graph with 8 nodes → 3 SCCs
    Graph: A→B, B→{C,E,F}, C→{D,G}, D→{C,H}, E→{A,F}, F→G, G→F, H→{D,G}
    Expected SCCs: {A,B,E}, {C,D,H}, {F,G} -/
def testComplexGraph : TestSeq :=
  let graph := buildGraph [
    ("A", ["B"]),
    ("B", ["C", "E", "F"]),
    ("C", ["D", "G"]),
    ("D", ["C", "H"]),
    ("E", ["A", "F"]),
    ("F", ["G"]),
    ("G", ["F"]),
    ("H", ["D", "G"])
  ]
  let sccs := Ix.CondenseM.run graph
  let result := sccsToSorted sccs
  test "complex: 3 SCCs" (result.length == 3) ++
  test "complex: correct SCCs" (sccsEq result [["A", "B", "E"], ["C", "D", "H"], ["F", "G"]])

/-! ## Additional edge case tests -/

/-- Empty graph -/
def testEmptyGraph : TestSeq :=
  let graph : Map Ix.Name (Set Ix.Name) := {}
  let sccs := Ix.CondenseM.run graph
  let result := sccsToSorted sccs
  test "empty: 0 SCCs" (result.length == 0)

/-- Self-loop: A→A -/
def testSelfLoop : TestSeq :=
  let graph := buildGraph [("A", ["A"])]
  let sccs := Ix.CondenseM.run graph
  let result := sccsToSorted sccs
  test "self-loop: 1 SCC" (result.length == 1) ++
  test "self-loop: contains A" (result == [["A"]])

/-- Multiple disconnected components -/
def testDisconnected : TestSeq :=
  let graph := buildGraph [
    ("A", ["B"]),
    ("B", ["A"]),
    ("C", ["D"]),
    ("D", ["C"]),
    ("E", [])
  ]
  let sccs := Ix.CondenseM.run graph
  let result := sccsToSorted sccs
  test "disconnected: 3 SCCs" (result.length == 3) ++
  test "disconnected: correct SCCs" (sccsEq result [["A", "B"], ["C", "D"], ["E"]])

/-- Linear chain -/
def testLinearChain : TestSeq :=
  let graph := buildGraph [
    ("A", ["B"]),
    ("B", ["C"]),
    ("C", ["D"]),
    ("D", ["E"]),
    ("E", [])
  ]
  let sccs := Ix.CondenseM.run graph
  let result := sccsToSorted sccs
  test "linear: 5 SCCs" (result.length == 5) ++
  test "linear: all singletons" (result.all (·.length == 1))

/-- Large cycle -/
def testLargeCycle : TestSeq :=
  let graph := buildGraph [
    ("A", ["B"]),
    ("B", ["C"]),
    ("C", ["D"]),
    ("D", ["E"]),
    ("E", ["A"])
  ]
  let sccs := Ix.CondenseM.run graph
  let result := sccsToSorted sccs
  test "large cycle: 1 SCC" (result.length == 1) ++
  test "large cycle: contains all 5" (result == [["A", "B", "C", "D", "E"]])

/-! ## Test lowLinks correctness -/

def testLowLinksSimpleCycle : TestSeq :=
  let graph := buildGraph [("A", ["B"]), ("B", ["A"])]
  let sccs := Ix.CondenseM.run graph
  -- All nodes in the same SCC should have the same lowLink
  let aLow := sccs.lowLinks.get? (mkName "A")
  let bLow := sccs.lowLinks.get? (mkName "B")
  test "lowLinks: A has lowLink" aLow.isSome ++
  test "lowLinks: B has lowLink" bLow.isSome ++
  test "lowLinks: A and B same root" (aLow == bLow)

def testLowLinksChain : TestSeq :=
  let graph := buildGraph [("A", ["B"]), ("B", ["C"]), ("C", [])]
  let sccs := Ix.CondenseM.run graph
  -- Each node should be its own root in a chain
  let aLow := sccs.lowLinks.get? (mkName "A")
  let bLow := sccs.lowLinks.get? (mkName "B")
  let cLow := sccs.lowLinks.get? (mkName "C")
  test "chain lowLinks: A is own root" (aLow == some (mkName "A")) ++
  test "chain lowLinks: B is own root" (bLow == some (mkName "B")) ++
  test "chain lowLinks: C is own root" (cLow == some (mkName "C"))

/-! ## Test blockRefs correctness -/

def testBlockRefsChain : TestSeq :=
  let graph := buildGraph [("A", ["B"]), ("B", ["C"]), ("C", [])]
  let sccs := Ix.CondenseM.run graph
  -- A's block should reference B's block
  let aBlockRefs := sccs.blockRefs.get? (mkName "A")
  let bBlockRefs := sccs.blockRefs.get? (mkName "B")
  let cBlockRefs := sccs.blockRefs.get? (mkName "C")
  test "blockRefs: A refs B" (aBlockRefs.map (·.contains (mkName "B")) |>.getD false) ++
  test "blockRefs: B refs C" (bBlockRefs.map (·.contains (mkName "C")) |>.getD false) ++
  test "blockRefs: C refs nothing" (cBlockRefs.map (·.isEmpty) |>.getD true)

def testBlockRefsTwoCycles : TestSeq :=
  let graph := buildGraph [
    ("A", ["B"]),
    ("B", ["A", "C"]),
    ("C", ["D"]),
    ("D", ["C"])
  ]
  let sccs := Ix.CondenseM.run graph
  -- The {A,B} SCC should reference the {C,D} SCC
  -- Find the root of A's SCC
  let aRoot := sccs.lowLinks.get? (mkName "A")
  match aRoot with
  | some root =>
    let blockRefs := sccs.blockRefs.get? root
    -- Should contain C (which is in the other SCC)
    test "blockRefs: AB SCC refs C" (blockRefs.map (·.contains (mkName "C")) |>.getD false)
  | none => test "blockRefs: found A's root" false

/-! ## Full Test Suite (unit tests) -/

def suite : List TestSeq := [
  group "basic SCCs" (
    testSingleNode ++
    testSimpleCycle ++
    testChainNoCycle ++
    testTwoCyclesConnected ++
    testComplexGraph
  ),
  group "edge cases" (
    testEmptyGraph ++
    testSelfLoop ++
    testDisconnected ++
    testLinearChain ++
    testLargeCycle
  ),
  group "lowLinks" (
    testLowLinksSimpleCycle ++
    testLowLinksChain
  ),
  group "blockRefs" (
    testBlockRefsChain ++
    testBlockRefsTwoCycles
  )
]

/-! ## Cross-Implementation Tests (Lean vs Rust) -/

/-- Canonicalize environment in Rust (fast). Returns Ix.RawEnvironment. -/
@[extern "rs_canonicalize_env_to_ix"]
opaque rsCanonicalizeEnvToIxRaw :
  @& List (Lean.Name × Lean.ConstantInfo) → IO Ix.RawEnvironment

/-- Compute SCCs in Rust.
    Returns RustCondensedBlocks (defined in Ix.CondenseM) -/
@[extern "rs_compute_sccs"]
opaque rsComputeSccs : @& List (Lean.Name × Lean.ConstantInfo) →
  IO Ix.RustCondensedBlocks

/-- Convert Rust lowLinks array to HashMap. -/
def rustLowLinksToMap (arr : Array (Ix.Name × Ix.Name))
    : Std.HashMap Ix.Name Ix.Name := Id.run do
  let mut m : Std.HashMap Ix.Name Ix.Name := {}
  for (name, root) in arr do
    m := m.insert name root
  return m

/-- Convert Rust's blocks array to a HashMap. -/
def rustBlocksToMap (arr : Array (Ix.Name × Array Ix.Name))
    : Std.HashMap Ix.Name (Std.HashSet Ix.Name) := Id.run do
  let mut m : Std.HashMap Ix.Name (Std.HashSet Ix.Name) := {}
  for (name, members) in arr do
    let memberSet := members.foldl (init := {}) fun s n => s.insert n
    m := m.insert name memberSet
  return m

/-- Convert Lean's CondensedBlocks.blocks to a HashMap. -/
def leanBlocksToHashMap (m : Ix.Map Ix.Name (Ix.Set Ix.Name))
    : Std.HashMap Ix.Name (Std.HashSet Ix.Name) := Id.run do
  let mut result : Std.HashMap Ix.Name (Std.HashSet Ix.Name) := {}
  for (name, members) in m do
    let memberSet : Std.HashSet Ix.Name := members.fold (init := {}) fun s n => s.insert n
    result := result.insert name memberSet
  return result

/-- Compare SCC results efficiently by checking block counts and sizes.
    Returns (matches, totalChecked, mismatches). -/
def compareSCCResults
    (leanBlocks rustBlocks : Std.HashMap Ix.Name (Std.HashSet Ix.Name))
    (rustLowLinks : Std.HashMap Ix.Name Ix.Name)
    : Bool × Nat × Array String := Id.run do
  let mut mismatches : Array String := #[]
  let mut checked : Nat := 0

  -- Check that block counts match
  if leanBlocks.size != rustBlocks.size then
    mismatches := mismatches.push s!"Block count mismatch: Lean={leanBlocks.size}, Rust={rustBlocks.size}"
    return (false, 0, mismatches)

  -- For each Lean block, find corresponding Rust block and compare sizes
  for (_leanRoot, leanMembers) in leanBlocks do
    checked := checked + 1
    -- Find any member's Rust root
    let someMember := leanMembers.fold (init := none) fun acc n =>
      if acc.isNone then some n else acc
    match someMember with
    | none => continue
    | some member =>
      match rustLowLinks.get? member with
      | none =>
        if mismatches.size < 5 then
          mismatches := mismatches.push s!"Member {member} not in Rust lowLinks"
      | some rustRoot =>
        match rustBlocks.get? rustRoot with
        | none =>
          if mismatches.size < 5 then
            mismatches := mismatches.push s!"Rust root {rustRoot} not in blocks"
        | some rustMembers =>
          if leanMembers.size != rustMembers.size then
            if mismatches.size < 5 then
              mismatches := mismatches.push s!"Size mismatch for SCC containing {member}: Lean={leanMembers.size}, Rust={rustMembers.size}"

  return (mismatches.isEmpty, checked, mismatches)

/-- Cross-implementation test: compare Lean and Rust SCC computation -/
def testSccComparison : TestSeq :=
  .individualIO "SCC Computation: Lean vs Rust" (do
    let env ← get_env!
    let numConsts := env.constants.toList.length

    IO.println s!"[Test] SCC Computation Comparison Test"
    IO.println s!"[Test] Environment has {numConsts} constants"
    IO.println ""

    -- Step 0: Canonicalize environment using Rust FFI (fast)
    IO.println s!"[Test] Step 0: Canonicalizing environment via Rust FFI..."
    let canonStart ← IO.monoMsNow
    let rawEnv ← rsCanonicalizeEnvToIxRaw env.constants.toList
    let ixEnv := rawEnv.toEnvironment
    let canonTime := (← IO.monoMsNow) - canonStart
    IO.println s!"[Test]   Canonicalized {ixEnv.consts.size} constants in {canonTime}ms"
    IO.println ""

    -- Step 1: Compute SCCs in Rust
    IO.println s!"[Test] Step 1: Computing SCCs in Rust..."
    let rustStart ← IO.monoMsNow
    let rustSccs ← rsComputeSccs env.constants.toList
    let rustTime := (← IO.monoMsNow) - rustStart
    IO.println s!"[Test]   Rust: {rustSccs.blocks.size} SCCs, {rustSccs.lowLinks.size} lowLinks in {rustTime}ms"

    -- Step 2: Compute SCCs in Lean (using pre-canonicalized environment)
    IO.println s!"[Test] Step 2: Computing SCCs in Lean..."
    let leanStart ← IO.monoMsNow
    let leanRefMap := Ix.GraphM.envParallel ixEnv
    let sccs := Ix.CondenseM.run leanRefMap
    IO.print s!"[Test]   Lean: {sccs.blocks.size} SCCs, {sccs.lowLinks.size} lowLinks "
    let leanTime := (← IO.monoMsNow) - leanStart
    IO.println s!"in {leanTime}ms"
    IO.println ""

    -- Step 3: Compare SCC content
    IO.println s!"[Test] Step 3: Comparing SCC content..."
    let rustBlocksMap := rustBlocksToMap rustSccs.blocks
    let leanBlocksMap := leanBlocksToHashMap sccs.blocks
    let rustLowLinksMap := rustLowLinksToMap rustSccs.lowLinks

    let (sccsMatch, checkedCount, mismatches) :=
      compareSCCResults leanBlocksMap rustBlocksMap rustLowLinksMap

    for msg in mismatches do
      IO.println s!"[Test]   {msg}"

    IO.println ""
    IO.println s!"[Test] Summary:"
    IO.println s!"[Test]   Canon time: {canonTime}ms"
    IO.println s!"[Test]   Rust SCC time: {rustTime}ms"
    IO.println s!"[Test]   Lean SCC time: {leanTime}ms"
    IO.println s!"[Test]   Checked {checkedCount} SCCs"
    IO.println s!"[Test]   SCCs match: {sccsMatch}"

    if !sccsMatch then
      return (false, some s!"SCCs do not match: {mismatches.size} mismatches")

    return (true, none)
  ) .done

/-- Cross-implementation test suite (expensive, run with --ignored) -/
def suiteIO : List TestSeq := [
  testSccComparison
]

end Tests.Ix.CondenseM
