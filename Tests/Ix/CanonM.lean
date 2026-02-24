/-
  Unit tests for CanonM module - verifies canonicalization roundtrips.
-/

import Ix.CanonM
import Ix.Environment
import Ix.Meta
import LSpec

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

def suite : TestSeq :=
  group "CanonM" <|
    testNameRoundtrip ++
    testLevelRoundtrip ++
    testExprRoundtrip ++
    testHashDeterminism ++
    testInterning

/-! ## Environment canonicalization test (IO) -/

/-- FFI to canonicalize environment in Rust and return Ix.RawEnvironment.
    Takes the original environment as List (Lean.Name × Lean.ConstantInfo),
    returns arrays of pairs that Lean converts to HashMaps. -/
@[extern "rs_canonicalize_env_to_ix"]
opaque rsCanonicalizeEnvToIxRaw :
  @& List (Lean.Name × Lean.ConstantInfo) →
  IO Ix.RawEnvironment

/-- Canonicalize environment in Rust and convert to Ix.Environment. -/
def rsCanonicalizeEnvToIx (consts : List (Lean.Name × Lean.ConstantInfo)) : IO Ix.Environment := do
  let raw ← rsCanonicalizeEnvToIxRaw consts
  pure raw.toEnvironment

/-! ## Ix.ConstantInfo comparison -/

/-- Compare two Ix.ConstantVal for equality. -/
def ixConstantValEq (a b : Ix.ConstantVal) : Bool :=
  a.name == b.name &&
  a.levelParams == b.levelParams &&
  a.type == b.type

/-- Compare two Ix.RecursorRule for equality. -/
def ixRecursorRuleEq (a b : Ix.RecursorRule) : Bool :=
  a.ctor == b.ctor && a.nfields == b.nfields && a.rhs == b.rhs

/-- Compare two Ix.ConstantInfo for full equality. -/
def ixConstInfoEq (a b : Ix.ConstantInfo) : Bool :=
  match a, b with
  | .axiomInfo v1, .axiomInfo v2 =>
    ixConstantValEq v1.cnst v2.cnst && v1.isUnsafe == v2.isUnsafe
  | .defnInfo v1, .defnInfo v2 =>
    ixConstantValEq v1.cnst v2.cnst &&
    v1.value == v2.value &&
    v1.hints == v2.hints &&
    v1.safety == v2.safety &&
    v1.all == v2.all
  | .thmInfo v1, .thmInfo v2 =>
    ixConstantValEq v1.cnst v2.cnst &&
    v1.value == v2.value &&
    v1.all == v2.all
  | .opaqueInfo v1, .opaqueInfo v2 =>
    ixConstantValEq v1.cnst v2.cnst &&
    v1.value == v2.value &&
    v1.isUnsafe == v2.isUnsafe &&
    v1.all == v2.all
  | .quotInfo v1, .quotInfo v2 =>
    ixConstantValEq v1.cnst v2.cnst && v1.kind == v2.kind
  | .inductInfo v1, .inductInfo v2 =>
    ixConstantValEq v1.cnst v2.cnst &&
    v1.numParams == v2.numParams &&
    v1.numIndices == v2.numIndices &&
    v1.all == v2.all &&
    v1.ctors == v2.ctors &&
    v1.numNested == v2.numNested &&
    v1.isRec == v2.isRec &&
    v1.isUnsafe == v2.isUnsafe &&
    v1.isReflexive == v2.isReflexive
  | .ctorInfo v1, .ctorInfo v2 =>
    ixConstantValEq v1.cnst v2.cnst &&
    v1.induct == v2.induct &&
    v1.cidx == v2.cidx &&
    v1.numParams == v2.numParams &&
    v1.numFields == v2.numFields &&
    v1.isUnsafe == v2.isUnsafe
  | .recInfo v1, .recInfo v2 =>
    ixConstantValEq v1.cnst v2.cnst &&
    v1.all == v2.all &&
    v1.numParams == v2.numParams &&
    v1.numIndices == v2.numIndices &&
    v1.numMotives == v2.numMotives &&
    v1.numMinors == v2.numMinors &&
    v1.rules.size == v2.rules.size &&
    (v1.rules.zip v2.rules |>.all fun (r1, r2) => ixRecursorRuleEq r1 r2) &&
    v1.k == v2.k &&
    v1.isUnsafe == v2.isUnsafe
  | _, _ => false

/-- Describe which field differs between two Ix.ConstantInfo. -/
def ixConstInfoDiff (a b : Ix.ConstantInfo) : String :=
  match a, b with
  | .axiomInfo v1, .axiomInfo v2 =>
    if v1.cnst.name != v2.cnst.name then "name"
    else if v1.cnst.levelParams != v2.cnst.levelParams then "levelParams"
    else if v1.cnst.type != v2.cnst.type then "type"
    else if v1.isUnsafe != v2.isUnsafe then "isUnsafe"
    else "unknown"
  | .defnInfo v1, .defnInfo v2 =>
    if v1.cnst.name != v2.cnst.name then "name"
    else if v1.cnst.levelParams != v2.cnst.levelParams then "levelParams"
    else if v1.cnst.type != v2.cnst.type then "type"
    else if v1.value != v2.value then "value"
    else if v1.hints != v2.hints then "hints"
    else if v1.safety != v2.safety then "safety"
    else if v1.all != v2.all then "all"
    else "unknown"
  | .thmInfo v1, .thmInfo v2 =>
    if v1.cnst.name != v2.cnst.name then "name"
    else if v1.cnst.type != v2.cnst.type then "type"
    else if v1.value != v2.value then "value"
    else "unknown"
  | _, _ => s!"variant mismatch: {a.getCnst.name} vs {b.getCnst.name}"

/-! ## Consolidated canonicalization roundtrip test

This test verifies the full canonicalization pipeline:
1. Get Lean.Environment
2. Canonicalize via Rust FFI → Ix.Environment
3. Compare Rust Ix.Environment against original env (iterate env.constants)
4. Canonicalize via Lean → Ix.Environment
5. Compare Lean Ix.Environment against Rust (should be identical)
6. Uncanonicalize back to Lean.Environment
7. Compare roundtripped environment to original (iterate env.constants)
-/

/-- Run the full canonicalization roundtrip test. -/
def testFullCanonRoundtrip : TestSeq :=
  .individualIO "full canonicalization roundtrip" none (do
    let env ← get_env!
    let numConsts := env.constants.toList.length

    IO.println s!"[Test] Starting canonicalization roundtrip test"
    IO.println s!"[Test] Environment has {numConsts} constants"
    IO.println ""

    -- Step 1: Canonicalize in Rust
    IO.println s!"[Test] Step 1: Canonicalizing in Rust..."
    let rustStart ← IO.monoMsNow
    let rustIxEnv ← rsCanonicalizeEnvToIx env.constants.toList
    let rustTime := (← IO.monoMsNow) - rustStart
    IO.println s!"[Test]   Rust: {rustIxEnv.consts.size} consts in {formatTime rustTime}"
    IO.println ""

    -- Step 2: Canonicalize in Lean (parallel)
    IO.println s!"[Test] Step 2: Canonicalizing in Lean (parallel)..."
    let leanStart ← IO.monoMsNow
    let leanIxConsts := canonEnvParallel env
    IO.println s!"[Test]   Lean: {leanIxConsts.size} consts"
    let leanTime := (← IO.monoMsNow) - leanStart
    IO.println s!"  in {formatTime leanTime}"
    IO.println ""

    -- Step 3: Compare Rust vs Lean by iterating env.constants
    IO.println s!"[Test] Step 3: Comparing Rust vs Lean..."
    let compareStart ← IO.monoMsNow
    let mut mismatches := 0
    let mut rustMissing := 0
    let mut leanMissing := 0
    let mut processed := 0
    let mut lastReport := 0

    for (name, _) in env.constants do
      -- Compute canonical name to look up in both environments
      let stt : CanonState := {}
      let (ixName, _) := StateT.run (canonName name) stt

      -- Direct HashMap lookup (now that Hashable matches Rust)
      let rustResult := rustIxEnv.consts.get? ixName
      let leanResult := leanIxConsts.get? ixName

      match rustResult, leanResult with
      | some rustConst, some leanConst =>
        if !ixConstInfoEq rustConst leanConst then
          if mismatches < 5 then
            let diff := ixConstInfoDiff rustConst leanConst
            IO.println s!"[Test]   Mismatch: {name} ({diff})"
          mismatches := mismatches + 1
      | none, some _ =>
        if rustMissing < 5 then
          IO.println s!"[Test]   Missing in Rust: {name}"
        rustMissing := rustMissing + 1
      | some _, none =>
        if leanMissing < 5 then
          IO.println s!"[Test]   Missing in Lean: {name}"
        leanMissing := leanMissing + 1
      | none, none =>
        -- Both missing - this shouldn't happen since we're iterating env.constants
        if mismatches < 5 then
          IO.println s!"[Test]   Missing in both: {name}"
        mismatches := mismatches + 1

      processed := processed + 1
      if processed - lastReport >= 10000 then
        IO.print s!"\r[Test]   Compared {processed}/{numConsts}...        "
        (← IO.getStdout).flush
        lastReport := processed

    let compareTime := (← IO.monoMsNow) - compareStart
    IO.println s!"\r[Test]   Compared {processed}: {mismatches} mismatches, {rustMissing} missing in Rust, {leanMissing} missing in Lean ({formatTime compareTime})"

    if rustMissing > 0 || leanMissing > 0 || mismatches > 0 then
      return (false, 0, 0, some s!"Rust vs Lean: {mismatches} mismatches, {rustMissing} missing in Rust, {leanMissing} missing in Lean")
    IO.println ""

    -- Step 4: Uncanonicalize Lean's Ix constants back to Lean (parallel)
    IO.println s!"[Test] Step 4: Uncanonicalize Lean's Ix constants (parallel)..."
    let uncanonStart ← IO.monoMsNow
    let roundtripped := uncanonEnvParallel leanIxConsts
    IO.println s!"[Test]   Uncanonicalized {roundtripped.size}"
    let uncanonTime := (← IO.monoMsNow) - uncanonStart
    IO.println s!"  in {formatTime uncanonTime}"
    IO.println ""

    -- Step 5: Compare roundtripped to original (parallel with pointer-pair caching)
    IO.println s!"[Test] Step 5: Comparing roundtripped to original (parallel)..."
    let verifyStart ← IO.monoMsNow
    -- Convert env.constants (SMap) to HashMap for parallel comparison
    let origMap : Std.HashMap Lean.Name Lean.ConstantInfo :=
      env.constants.fold (init := {}) fun acc name const => acc.insert name const
    let (rtMismatches, rtMissing, mismatchNames, missingNames) := compareEnvsParallel origMap roundtripped
    for name in missingNames.toList.take 5 do
      IO.println s!"[Test]   Missing after roundtrip: {name}"
    for name in mismatchNames.toList.take 5 do
      IO.println s!"[Test]   Mismatch after roundtrip: {name}"
    let verifyTime := (← IO.monoMsNow) - verifyStart
    IO.println s!"[Test]   Verified {numConsts}: {rtMissing} missing, {rtMismatches} mismatches ({formatTime verifyTime})"
    IO.println ""

    -- Summary
    let totalTime := rustTime + leanTime + compareTime + uncanonTime + verifyTime
    let speedup := if rustTime > 0 then leanTime / rustTime else 0
    IO.println s!"[Test] Summary:"
    IO.println s!"[Test]   Total time: {formatTime totalTime}"
    IO.println s!"[Test]   Rust canonicalize: {formatTime rustTime}"
    IO.println s!"[Test]   Lean canonicalize: {formatTime leanTime}"
    IO.println s!"[Test]   Rust speedup: ~{speedup}x"
    IO.println ""

    let success := rustMissing == 0 && leanMissing == 0 && mismatches == 0 && rtMissing == 0 && rtMismatches == 0
    let failMsg := if !success then
      some s!"rustMissing={rustMissing}, leanMissing={leanMissing}, mismatches={mismatches}, rtMissing={rtMissing}, rtMismatches={rtMismatches}"
    else none

    pure (success, 0, 0, failMsg)
  ) .done

/-! ## Pure Lean canonicalization roundtrip test

This test verifies canonicalization and uncanonicalization work correctly
in pure Lean without any Rust FFI:
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

/-- Full canonicalization roundtrip test suite (expensive, in ignored tests). -/
def rustSuiteIO : List TestSeq := [
  testFullCanonRoundtrip,
]

def serialSuiteIO : List TestSeq := [
  testPureLeanRoundtrip
]

def parallelSuiteIO : List TestSeq := [
  testParallelLeanRoundtrip
]

end Tests.CanonM
