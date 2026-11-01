module
public import Ix.CanonM
public import Ix.Environment
public import Ix.Meta
public import LSpec

/-!
  Unit tests for CanonM module - verifies canonicalization roundtrips.
-/

open LSpec Ix.CanonM

namespace Tests.CanonM

/-! ## Name roundtrip tests -/

def testNameRoundtrip : TestSeq :=
  let names : List Lean.Name := [
    .anonymous,
    .str .anonymous "foo",
    .str .anonymous "bar",
    .str (.str .anonymous "Foo") "bar",
    .num .anonymous 0,
    .num .anonymous 42,
    .num (.str .anonymous "test") 123
  ]
  group "name roundtrip" <| names.foldl (init := .done) fun acc n =>
    let stt : CanonState := {}
    let (name, _stt') := StateT.run (canonName n) stt
    let ustt : UncanonState := { names := {}, levels := {}, exprs := {} }
    let (leanName, _) := StateT.run (uncanonName name) ustt
    acc ++ test s!"{n}" (n == leanName)

/-! ## Level roundtrip tests -/

def testLevelRoundtrip : TestSeq :=
  let levels : List Lean.Level := [
    .zero,
    .succ .zero,
    .succ (.succ .zero),
    .max .zero .zero,
    .max (.succ .zero) .zero,
    .imax .zero .zero,
    .param `u,
    .param `v,
    .max (.param `u) (.succ (.param `v))
  ]
  group "level roundtrip" <| levels.foldl (init := .done) fun acc l =>
    let stt : CanonState := {}
    let (level, _stt') := StateT.run (canonLevel l) stt
    let ustt : UncanonState := { names := {}, levels := {}, exprs := {} }
    let (leanLevel, _) := StateT.run (uncanonLevel level) ustt
    acc ++ test s!"{l}" (l == leanLevel)

/-! ## Expr roundtrip tests -/

def testExprRoundtrip : TestSeq :=
  let exprs : List Lean.Expr := [
    .bvar 0,
    .bvar 42,
    .sort .zero,
    .sort (.succ .zero),
    .const `Nat [],
    .const `List [.zero],
    .const `Eq [.param `u],
    .app (.const `Nat.succ []) (.bvar 0),
    .lam `x (.const `Nat []) (.bvar 0) .default,
    .forallE `x (.const `Nat []) (.const `Nat []) .default,
    .lit (.natVal 0),
    .lit (.natVal 42),
    .lit (.strVal "hello"),
    .lit (.strVal "")
  ]
  group "expr roundtrip" <| exprs.foldl (init := .done) fun acc e =>
    let stt : CanonState := {}
    let (expr, _stt') := StateT.run (canonExpr e) stt
    let ustt : UncanonState := { names := {}, levels := {}, exprs := {} }
    let (leanExpr, _) := StateT.run (uncanonExpr expr) ustt
    acc ++ test s!"{e}" (e == leanExpr)

/-! ## Hash determinism tests -/

def testHashDeterminism : TestSeq :=
  group "hash determinism" <|
    let n1 := Ix.Name.mkAnon
    let n2 := Ix.Name.mkAnon
    test "mkAnon same hash" (n1.getHash == n2.getHash) ++
    let n3 := Ix.Name.mkStr Ix.Name.mkAnon "foo"
    let n4 := Ix.Name.mkStr Ix.Name.mkAnon "foo"
    test "mkStr same hash" (n3.getHash == n4.getHash) ++
    let n5 := Ix.Name.mkStr Ix.Name.mkAnon "foo"
    let n6 := Ix.Name.mkStr Ix.Name.mkAnon "bar"
    test "different strings different hash" (n5.getHash != n6.getHash) ++
    let l1 := Ix.Level.mkZero
    let l2 := Ix.Level.mkZero
    test "mkZero same hash" (l1.getHash == l2.getHash) ++
    let l3 := Ix.Level.mkSucc Ix.Level.mkZero
    let l4 := Ix.Level.mkSucc Ix.Level.mkZero
    test "mkSucc same hash" (l3.getHash == l4.getHash)

/-! ## Interning tests -/

def testInterning : TestSeq :=
  group "interning" <|
    -- Same Lean name should produce same pointer
    let stt : CanonState := {}
    let n := Lean.Name.mkStr .anonymous "test"
    let (name1, stt') := StateT.run (canonName n) stt
    let (name2, _) := StateT.run (canonName n) stt'
    -- They should have the same hash
    test "same name same hash" (name1.getHash == name2.getHash)

/-! ## Full suite -/

public def suite : TestSeq :=
  group "CanonM" <|
    testNameRoundtrip ++
    testLevelRoundtrip ++
    testExprRoundtrip ++
    testHashDeterminism ++
    testInterning

/-! ## Pure Lean canonicalization roundtrip test

This test verifies canonicalization and uncanonicalization work correctly
in pure Lean:
1. Get Lean.Environment
2. Canonicalize via Lean → Ix.Environment
3. Uncanonicalize back to Lean.Environment
4. Compare roundtripped environment to original
-/

/-- Run the pure Lean canonicalization roundtrip test. -/
def testPureLeanRoundtrip : TestSeq :=
  .individualIO "pure Lean canonicalization roundtrip" none (do
    let env ← get_env!
    let numConsts := env.constants.toList.length

    IO.println s!"[Test] Starting pure Lean canonicalization roundtrip test"
    IO.println s!"[Test] Environment has {numConsts} constants"
    IO.println ""

    -- Step 1: Canonicalize in Lean
    IO.println s!"[Test] Step 1: Canonicalizing in Lean..."
    let canonStart ← IO.monoMsNow
    let (ixEnv, _) := StateT.run (canonEnv env) {}
    IO.println s!"[Test]   Canonicalized {ixEnv.consts.size} consts"
    let canonTime := (← IO.monoMsNow) - canonStart
    IO.println s!"  in {formatTime canonTime}"

    -- Step 2: Uncanonicalize back to Lean
    IO.println s!"[Test] Step 2: Uncanonicalize back to Lean..."
    let uncanonStart ← IO.monoMsNow
    let (env2, _) := StateT.run (uncanonEnv ixEnv) {}
    IO.println s!"[Test]   Uncanonicalized {env2.size} constants"
    let uncanonTime := (← IO.monoMsNow) - uncanonStart
    IO.println s!"  in {formatTime uncanonTime}"

    -- Step 3: Compare roundtripped to original (parallel)
    IO.println s!"[Test] Step 3: Comparing roundtripped to original (parallel)..."
    let verifyStart ← IO.monoMsNow
    let origMap : Std.HashMap Lean.Name Lean.ConstantInfo :=
      env.constants.fold (init := {}) fun acc name const => acc.insert name const
    let (mismatches, missing, mismatchNames, missingNames) := compareEnvsParallel origMap env2
    for name in missingNames.toList.take 5 do
      IO.println s!"[Test]   Missing after roundtrip: {name}"
    for name in mismatchNames.toList.take 5 do
      IO.println s!"[Test]   Mismatch after roundtrip: {name}"
    let verifyTime := (← IO.monoMsNow) - verifyStart
    IO.println s!"[Test]   Verified {numConsts}: {missing} missing, {mismatches} mismatches ({formatTime verifyTime})"
    IO.println ""

    -- Summary
    let totalTime := canonTime + uncanonTime + verifyTime
    IO.println s!"[Test] Summary:"
    IO.println s!"[Test]   Total time: {formatTime totalTime}"
    IO.println s!"[Test]   Canonicalize: {formatTime canonTime}"
    IO.println s!"[Test]   Uncanonicalize: {formatTime uncanonTime}"
    IO.println s!"[Test]   Verify: {formatTime verifyTime}"
    IO.println ""

    let success := missing == 0 && mismatches == 0
    let failMsg := if !success then
      some s!"missing={missing}, mismatches={mismatches}"
    else none

    pure (success, 0, 0, failMsg)
  ) .done

/-! ## Parallel Lean canonicalization roundtrip test

This test verifies parallel canonicalization using ShardMap:
1. Get Lean.Environment
2. Canonicalize via ParallelCanonM → Ix.Environment
3. Uncanonicalize back to Lean.Environment
4. Compare roundtripped environment to original
-/

/-- Run the parallel Lean canonicalization roundtrip test. -/
def testParallelLeanRoundtrip : TestSeq :=
  .individualIO "parallel Lean canonicalization roundtrip" none (do
    let env ← get_env!
    let numConsts := env.constants.toList.length

    IO.println s!"[Test] Starting parallel Lean canonicalization roundtrip test"
    IO.println s!"[Test] Environment has {numConsts} constants"
    IO.println ""

    -- Step 1: Canonicalize in parallel
    IO.println s!"[Test] Step 1: Canonicalizing in parallel..."
    let canonStart ← IO.monoMsNow
    let ixConsts := canonEnvParallel env
    IO.println s!"[Test]   Canonicalized {ixConsts.size} consts"
    let canonTime := (← IO.monoMsNow) - canonStart
    IO.println s!"  in {formatTime canonTime}"

    -- Step 2: Uncanonicalize back to Lean (parallel)
    IO.println s!"[Test] Step 2: Uncanonicalize back to Lean (parallel)..."
    let uncanonStart ← IO.monoMsNow
    let env2 := uncanonEnvParallel ixConsts
    IO.println s!"[Test]   Uncanonicalized {env2.size} constants"
    let uncanonTime := (← IO.monoMsNow) - uncanonStart
    IO.println s!"  in {formatTime uncanonTime}"

    -- Step 3: Compare roundtripped to original (parallel)
    IO.println s!"[Test] Step 3: Comparing roundtripped to original (parallel)..."
    let verifyStart ← IO.monoMsNow
    let origMap : Std.HashMap Lean.Name Lean.ConstantInfo :=
      env.constants.fold (init := {}) fun acc name const => acc.insert name const
    let (mismatches, missing, mismatchNames, missingNames) := compareEnvsParallel origMap env2
    for name in missingNames.toList.take 5 do
      IO.println s!"[Test]   Missing after roundtrip: {name}"
    for name in mismatchNames.toList.take 5 do
      IO.println s!"[Test]   Mismatch after roundtrip: {name}"
    let verifyTime := (← IO.monoMsNow) - verifyStart
    IO.println s!"[Test]   Verified {numConsts}: {missing} missing, {mismatches} mismatches ({formatTime verifyTime})"
    IO.println ""

    -- Summary
    let totalTime := canonTime + uncanonTime + verifyTime
    IO.println s!"[Test] Summary:"
    IO.println s!"[Test]   Total time: {formatTime totalTime}"
    IO.println s!"[Test]   Canonicalize: {formatTime canonTime}"
    IO.println s!"[Test]   Uncanonicalize: {formatTime uncanonTime}"
    IO.println s!"[Test]   Verify: {formatTime verifyTime}"
    IO.println ""

    let success := missing == 0 && mismatches == 0
    let failMsg := if !success then
      some s!"missing={missing}, mismatches={mismatches}"
    else none

    pure (success, 0, 0, failMsg)
  ) .done

public section

def serialSuiteIO : List TestSeq := [
  testPureLeanRoundtrip
]

def parallelSuiteIO : List TestSeq := [
  testParallelLeanRoundtrip
]

end

end Tests.CanonM

