/-
  Tests for Ix.CondenseM module.
  - Unit tests for SCC computation mirroring Rust test cases
  - Cross-implementation tests comparing Lean vs Rust SCC results
-/

module
public import Ix.GraphM
public import Ix.CondenseM
public import Ix.Environment
public import Ix.Meta
public import LSpec

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

/-! ## References outside the keys, and large graphs -/

/-- A reference to a name that is not a key is not an edge: it joins no
component and has no representative, but stays in its block's `blockRefs`. -/
def testOutsideRefs : TestSeq :=
  let graph := buildGraph [("A", ["B", "X"]), ("B", ["A", "Y"]), ("C", ["X", "A"])]
  let sccs := Ix.CondenseM.run graph
  let aRoot := sccs.lowLinks.get? (mkName "A")
  let cRoot := sccs.lowLinks.get? (mkName "C")
  let refsOf := fun (r : Option Ix.Name) =>
    ((r.bind sccs.blockRefs.get?).getD {}).toList.map toString |>.mergeSort
  test "outside refs: SCCs" (sccsToSorted sccs == [["A", "B"], ["C"]]) ++
  test "outside refs: no representative for X, Y"
    (!sccs.lowLinks.contains (mkName "X") && !sccs.lowLinks.contains (mkName "Y")) ++
  test "outside refs: AB block refs X, Y" (refsOf aRoot == ["X", "Y"]) ++
  test "outside refs: C block refs A, X" (refsOf cRoot == ["A", "X"])

/-- A chain and a cycle of 100,000 nodes: the total Tarjan keeps its own
call stack, so depth costs no native stack. -/
def testLargeGraphs : TestSeq :=
  let n := 100000
  let chain : Map Ix.Name (Set Ix.Name) := (List.range n).foldl (init := {}) fun m i =>
    m.insert (mkName s!"n{i}") (if i + 1 < n then {mkName s!"n{i+1}"} else {})
  let cycle : Map Ix.Name (Set Ix.Name) := (List.range n).foldl (init := {}) fun m i =>
    m.insert (mkName s!"n{i}") {mkName s!"n{(i + 1) % n}"}
  let c1 := Ix.CondenseM.run chain
  let c2 := Ix.CondenseM.run cycle
  test "100k chain: 100k singleton blocks"
    (c1.blocks.size == n && c1.lowLinks.size == n && c1.blocks.toList.all (·.2.size == 1)) ++
  test "100k cycle: one block of 100k"
    (c2.blocks.size == 1 && c2.lowLinks.size == n && c2.blocks.toList.all (·.2.size == n))

/-! ## The total Tarjan on index graphs -/

/-- `Ix.Compile.Canon.tarjan` on small graphs (components compared as sets). -/
def testTarjan : TestSeq :=
  let norm := fun (cs : Array (Array Nat)) => (cs.map (·.qsort (· < ·))).qsort
    (fun a b => a[0]?.getD 0 < b[0]?.getD 0)
  let cases : List (Array (Array Nat) × Array (Array Nat)) := [
    (#[], #[]),
    (#[#[]], #[#[0]]),
    (#[#[1], #[0]], #[#[0, 1]]),
    (#[#[1], #[2], #[]], #[#[0], #[1], #[2]]),
    (#[#[1], #[0, 2], #[3], #[2]], #[#[0, 1], #[2, 3]]),
    (#[#[1], #[2], #[0, 3], #[4], #[5], #[3], #[7], #[6]],
      #[#[0, 1, 2], #[3, 4, 5], #[6, 7]]),
    (#[#[0]], #[#[0]]),
    -- out-of-range successors are ignored
    (#[#[1, 7], #[0, 9]], #[#[0, 1]])]
  cases.foldl (init := .done) fun t (g, want) =>
    t ++ test s!"tarjan {g}" ((Ix.Compile.Canon.tarjan g).map norm == some (norm want))

/-! ## The former `partial` Tarjan, as a reference

`Former.run` is the implementation `CondenseM.run` replaced, kept verbatim
except that `visit` takes fuel (the number of keys plus one, more than the
recursion depth) instead of being `partial`. `CondenseM.run` must reproduce
its three maps exactly: contents and iteration orders, which downstream
compilation and Source-mode ingress depend on. -/

namespace Former

structure CondenseEnv where
  validNames: Set Ix.Name
  outRefs: Map Ix.Name (Set Ix.Name)

structure CondenseState where
  names: Map Ix.Name UInt64
  ids: Map UInt64 Ix.Name
  lowLink: Map UInt64 UInt64
  stack: Array UInt64
  onStack: Set UInt64
  id : UInt64

def CondenseState.init : CondenseState := ⟨{}, {}, {}, #[], {}, 0⟩

abbrev CondenseM := ReaderT CondenseEnv <| StateT CondenseState Id

def visit : Nat → Ix.Name → CondenseM Unit
| 0, _ => pure ()
| fuel + 1, name => do
  if !(<- read).validNames.contains name then return ()
  let refs := match (<- read).outRefs.get? name with
    | .some x => x
    | .none => {}
  let id := (<- get).id
  modify fun stt => { stt with
    names := stt.names.insert name id
    ids := stt.ids.insert id name
    stack := stt.stack.push id
    onStack := stt.onStack.insert id
    lowLink := stt.lowLink.insert id id
    id := id + 1
  }
  for ref in refs do
    if !(<- read).validNames.contains ref then continue
    match (<- get).names.get? ref with
    | .none => do
      visit fuel ref
      modify fun stt =>
        let ll := stt.lowLink.get! id
        let rll := stt.lowLink.get! (stt.names.get! ref)
        { stt with lowLink := stt.lowLink.insert id (min ll rll) }
    | .some id' => if (<- get).onStack.contains id' then
      modify fun stt =>
        let ll := stt.lowLink.get! id
        { stt with lowLink := stt.lowLink.insert id (min ll id') }
  if id == (<- get).lowLink.get! id then
    let mut stack := (<- get).stack
    if !stack.isEmpty then
      while true do
        let top := stack.back!
        stack := stack.pop
        modify fun stt => { stt with
          lowLink := stt.lowLink.insert top id
          onStack := stt.onStack.erase top
        }
        if top == id then break
    modify fun stt => { stt with stack := stack }

def condense (fuel : Nat) : CondenseM CondensedBlocks := do
  for (name, _) in (<- read).outRefs do
    match (<- get).names.get? name with
    | .some _ => continue
    | .none => visit fuel name
  let mut blocks : Map Ix.Name (Set Ix.Name) := {}
  let mut lowLinks := {}
  for (i, low) in (<- get).lowLink do
    let name := (<- get).ids.get! i
    let lowName := (<- get).ids.get! low
    lowLinks := lowLinks.insert name lowName
    blocks := blocks.alter lowName fun x => match x with
      | .some s => .some (s.insert name)
      | .none => .some {name}
  let mut blockRefs := {}
  let refs := (<- read).outRefs
  for (lo, all) in blocks do
    let mut rs: Set Ix.Name := {}
    for a in all do
      rs := rs.union (refs.get! a)
    rs := rs.filter (!all.contains ·)
    blockRefs := blockRefs.insert lo rs
  return ⟨lowLinks, blocks, blockRefs⟩

def run (refs : Map Ix.Name (Set Ix.Name)) : CondensedBlocks :=
  let validNames : Set Ix.Name := refs.fold (init := {}) fun acc k _ => acc.insert k
  Id.run (StateT.run (ReaderT.run (condense (refs.size + 1)) ⟨validNames, refs⟩)
    CondenseState.init).1

end Former

/-- The three maps in their iteration orders, member sets included. -/
def layout (cb : CondensedBlocks) :
    Array (Ix.Name × Ix.Name) × Array (Ix.Name × Array Ix.Name) ×
      Array (Ix.Name × Array Ix.Name) := Id.run do
  let mut lows := #[]
  for p in cb.lowLinks do lows := lows.push p
  let mut blocks := #[]
  for (k, s) in cb.blocks do
    let mut ms := #[]
    for m in s do ms := ms.push m
    blocks := blocks.push (k, ms)
  let mut refs := #[]
  for (k, s) in cb.blockRefs do
    let mut rs := #[]
    for r in s do rs := rs.push r
    refs := refs.push (k, rs)
  return (lows, blocks, refs)

/-- A pseudo-random graph on `n` keys: up to `deg` references per key, some
to the key itself and some to names outside the keys. -/
def randomGraph (seed n deg : Nat) : Map Ix.Name (Set Ix.Name) := Id.run do
  let mut s := seed
  let mut m : Map Ix.Name (Set Ix.Name) := {}
  for i in [0:n] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
    let k := (s / 65536) % (deg + 1)
    let mut rs : Set Ix.Name := {}
    for _ in [0:k] do
      s := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
      let j := (s / 65536) % (n + n / 8 + 1)
      rs := rs.insert (if j < n then mkName s!"n{j}" else mkName s!"x{j}")
    m := m.insert (mkName s!"n{i}") rs
  return m

/-- `CondenseM.run` against the former implementation on a fixed list of
graphs: equal maps, member sets and iteration orders. -/
def testAgainstFormer : TestSeq := Id.run do
  let mut graphs : Array (String × Map Ix.Name (Set Ix.Name)) := #[
    ("complex", buildGraph [("A", ["B"]), ("B", ["C", "E", "F"]), ("C", ["D", "G"]),
      ("D", ["C", "H"]), ("E", ["A", "F"]), ("F", ["G"]), ("G", ["F"]), ("H", ["D", "G"])]),
    ("outside", buildGraph [("A", ["B", "X"]), ("B", ["A", "Y"]), ("C", ["X", "A"])]),
    ("self", buildGraph [("A", ["A"]), ("B", ["A", "B"])])]
  for n in [0, 1, 2, 3, 5, 8, 13, 40, 200, 1000, 3000] do
    for deg in [1, 2, 4] do
      for seed in [1, 7, 42] do
        graphs := graphs.push (s!"random n={n} deg={deg} seed={seed}", randomGraph seed n deg)
  let mut t : TestSeq := .done
  for (label, g) in graphs do
    t := t ++ test s!"same maps as the former Tarjan: {label}"
      (layout (Ix.CondenseM.run g) == layout (Former.run g))
  return t

/-! ## Full Test Suite (unit tests) -/

public def suite : List TestSeq := [
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
  ),
  group "outside references" testOutsideRefs,
  group "large graphs" testLargeGraphs,
  group "total Tarjan" testTarjan,
  group "former implementation" testAgainstFormer
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
  .individualIO "SCC Computation: Lean vs Rust" none (do
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
      return (false, 0, 0, some s!"SCCs do not match: {mismatches.size} mismatches")

    return (true, 0, 0, none)
  ) .done

/-- `CondenseM.run` against the former implementation on the reference graph
of the test binary's environment: equal maps, member sets and iteration
orders. -/
def testFormerOnEnv : TestSeq :=
  .individualIO "CondenseM.run vs the former Tarjan on the environment" none (do
    let env ← get_env!
    let rawEnv ← rsCanonicalizeEnvToIxRaw env.constants.toList
    let refs := Ix.GraphM.envParallel rawEnv.toEnvironment
    let mine := layout (Ix.CondenseM.run refs)
    let former := layout (Former.run refs)
    let same := mine == former
    IO.println s!"[Test]   {refs.size} nodes, {mine.2.1.size} blocks; \
      same maps and orders: {same}"
    if !same then
      return (false, 0, 0, some "the maps differ from the former implementation's")
    return (true, 0, 0, none)
  ) .done

/-- Cross-implementation test suite (expensive, run with --ignored) -/
public def suiteIO : List TestSeq := [
  testSccComparison,
  testFormerOnEnv
]

end Tests.Ix.CondenseM
