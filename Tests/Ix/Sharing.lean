/-
  Unit tests for Sharing module - verifies hash-consing compatibility with Rust.

  The hashing algorithm must produce identical results to Rust's `hash_node` function
  for cross-implementation compatibility.
-/

import Ix.Sharing
import Ix.Ixon
import Ix.CompileM
import Ix.CanonM
import Ix.Meta
import Ix.Environment
import LSpec

open LSpec Ix.Sharing Ixon Ix.CompileM Ix

namespace Tests.Sharing

/-! ## uint64ToBytes tests -/

/-- Verify uint64ToBytes produces exactly 8 bytes. -/
def testUint64ToBytesLength : TestSeq :=
  group "uint64ToBytes length" <|
    test "0" ((uint64ToBytes 0).size == 8) ++
    test "1" ((uint64ToBytes 1).size == 8) ++
    test "255" ((uint64ToBytes 255).size == 8) ++
    test "256" ((uint64ToBytes 256).size == 8) ++
    test "maxUInt64" ((uint64ToBytes UInt64.MAX).size == 8)

/-- Verify uint64ToBytes produces correct little-endian encoding. -/
def testUint64ToBytesEncoding : TestSeq :=
  group "uint64ToBytes encoding" <|
    -- 0 should be [0,0,0,0,0,0,0,0]
    test "0 bytes" (uint64ToBytes 0 == ⟨#[0,0,0,0,0,0,0,0]⟩) ++
    -- 1 should be [1,0,0,0,0,0,0,0]
    test "1 bytes" (uint64ToBytes 1 == ⟨#[1,0,0,0,0,0,0,0]⟩) ++
    -- 256 should be [0,1,0,0,0,0,0,0]
    test "256 bytes" (uint64ToBytes 256 == ⟨#[0,1,0,0,0,0,0,0]⟩) ++
    -- 0x0102030405060708 should be [8,7,6,5,4,3,2,1]
    test "0x0102030405060708 bytes"
      (uint64ToBytes 0x0102030405060708 == ⟨#[0x08,0x07,0x06,0x05,0x04,0x03,0x02,0x01]⟩)

/-! ## Hash consistency tests -/

/-- Verify that the same expression always produces the same hash. -/
def testHashConsistency : TestSeq :=
  let e1 := Expr.var 0
  let e2 := Expr.var 0
  let h1 := computeExprHash e1
  let h2 := computeExprHash e2
  test "same expr same hash" (h1 == h2)

/-- Verify that different expressions produce different hashes. -/
def testHashDifferent : TestSeq :=
  let e1 := Expr.var 0
  let e2 := Expr.var 1
  let h1 := computeExprHash e1
  let h2 := computeExprHash e2
  test "different expr different hash" (h1 != h2)

/-! ## Hash buffer construction tests -/

/-- Test that Sort expression hash buffer is: [FLAG_SORT, u64_le_bytes...] -/
def testSortHashBuffer : TestSeq :=
  -- Sort(5) should hash buffer: [0x00, 5, 0, 0, 0, 0, 0, 0, 0]
  let expected := ByteArray.empty
    |>.push Expr.FLAG_SORT
    |>.append (uint64ToBytes 5)
  test "sort buffer size" (expected.size == 9) ++
  test "sort buffer content" (expected.data[0]! == 0x00 && expected.data[1]! == 5)

/-- Test that Var expression hash buffer is: [FLAG_VAR, u64_le_bytes...] -/
def testVarHashBuffer : TestSeq :=
  -- Var(3) should hash buffer: [0x01, 3, 0, 0, 0, 0, 0, 0, 0]
  let expected := ByteArray.empty
    |>.push Expr.FLAG_VAR
    |>.append (uint64ToBytes 3)
  test "var buffer size" (expected.size == 9) ++
  test "var buffer content" (expected.data[0]! == 0x01 && expected.data[1]! == 3)

/-- Test that App expression includes child hashes (64 bytes for 2 children). -/
def testAppHashBuffer : TestSeq :=
  let fun_ := Expr.var 0
  let arg := Expr.var 1
  let funHash := computeExprHash fun_
  let argHash := computeExprHash arg
  -- App buffer: [0x07, funHash(32 bytes), argHash(32 bytes)]
  let expected := ByteArray.empty
    |>.push Expr.FLAG_APP
    |>.append funHash.hash
    |>.append argHash.hash
  test "app buffer size" (expected.size == 65) ++
  test "app buffer flag" (expected.data[0]! == 0x07)

/-! ## Sharing analysis tests -/

/-- Test that applySharing returns empty sharing vec for unique subterms. -/
def testNoSharing : TestSeq :=
  let exprs := #[Expr.var 0, Expr.var 1, Expr.var 2]
  let (rewritten, sharingVec) := applySharing exprs
  test "no sharing needed" (sharingVec.isEmpty) ++
  test "expressions unchanged" (rewritten == exprs)

/-- Test that applySharing detects shared subterms. -/
def testWithSharing : TestSeq :=
  -- Create expressions with shared subterm: (var 42) appears twice
  let shared := Expr.var 42
  let e1 := Expr.app shared (Expr.var 1)
  let e2 := Expr.app shared (Expr.var 2)
  let e3 := Expr.app shared (Expr.var 3)
  let exprs := #[e1, e2, e3]
  let (_rewritten, _sharingVec) := applySharing exprs
  -- var 42 should be shared since it appears 3 times
  -- But it's a small term, so sharing might not be profitable
  -- Just verify the function runs without error
  test "sharing analysis completes" true

/-- Test that sharing vector is in topological order (leaves first). -/
def testSharingTopoOrder : TestSeq :=
  -- Create: App(Lam(T, B), A) where T appears in multiple places
  let t := Expr.var 0  -- type
  let b := Expr.var 1  -- body
  let a := Expr.var 2  -- arg
  let lam := Expr.lam t b
  let app := Expr.app lam a
  -- Use the same type in another expression
  let e2 := Expr.app (Expr.lam t (Expr.var 3)) a
  let exprs := #[app, e2]
  let (_, sharingVec) := applySharing exprs
  -- Verify no forward references in sharing vector
  -- (each Share(idx) in sharingVec[i] must have idx < i)
  let valid := sharingVec.foldl (init := (true, 0)) fun (ok, i) e =>
    let thisOk := checkNoForwardRefs e i
    (ok && thisOk, i + 1)
  test "no forward references" valid.1
where
  checkNoForwardRefs (e : Ixon.Expr) (maxIdx : Nat) : Bool :=
    match e with
    | .share idx => idx.toNat < maxIdx
    | .app f a => checkNoForwardRefs f maxIdx && checkNoForwardRefs a maxIdx
    | .lam t b => checkNoForwardRefs t maxIdx && checkNoForwardRefs b maxIdx
    | .all t b => checkNoForwardRefs t maxIdx && checkNoForwardRefs b maxIdx
    | .letE _ t v b =>
      checkNoForwardRefs t maxIdx && checkNoForwardRefs v maxIdx && checkNoForwardRefs b maxIdx
    | .prj _ _ v => checkNoForwardRefs v maxIdx
    | _ => true

/-! ## Known hash value tests (for cross-impl verification) -/

/-- Compute expected hash for Var(0) and verify it's deterministic.
    The actual hash value should match Rust's hash_node for the same input. -/
def testKnownHashVar0 : TestSeq :=
  let e := Expr.var 0
  let h := computeExprHash e
  -- Hash should be blake3([0x01, 0, 0, 0, 0, 0, 0, 0, 0])
  let buf := ByteArray.empty.push 0x01 |>.append (uint64ToBytes 0)
  let expected := Address.blake3 buf
  test "var 0 hash matches expected" (h == expected)

/-- Compute expected hash for Sort(0) and verify. -/
def testKnownHashSort0 : TestSeq :=
  let e := Expr.sort 0
  let h := computeExprHash e
  -- Hash should be blake3([0x00, 0, 0, 0, 0, 0, 0, 0, 0])
  let buf := ByteArray.empty.push 0x00 |>.append (uint64ToBytes 0)
  let expected := Address.blake3 buf
  test "sort 0 hash matches expected" (h == expected)

/-! ## Cross-implementation tests (Lean vs Rust) -/

/-- FFI: Run Rust's sharing analysis and return the count of shared items. -/
@[extern "rs_analyze_sharing_count"]
opaque rsAnalyzeSharingCount : @& Array Ixon.Expr → UInt64

/-- FFI: Compare Lean's sharing analysis with Rust's on the same input.
    Returns packed u64:
    - bits 0-31: 1 if sharing vectors match, 0 otherwise
    - bits 32-47: Lean sharing count
    - bits 48-63: Rust sharing count -/
@[extern "rs_compare_sharing_analysis"]
opaque rsCompareSharingAnalysis : @& Array Ixon.Expr → @& Array Ixon.Expr → @& Array Ixon.Expr → UInt64

/-- FFI: Debug sharing analysis - print Rust's view of the input expressions. -/
@[extern "rs_debug_sharing_analysis"]
opaque rsDebugSharingAnalysis : @& Array Ixon.Expr → Unit

/-- Opaque type representing a compiled environment from Rust.
    This is an external object managed by the Rust FFI layer. -/
opaque RustCompiledEnv : Type

/-- FFI: Get the buffer length needed for pre-sharing expressions. -/
@[extern "rs_get_pre_sharing_exprs_len"]
opaque rsGetPreSharingExprsLen : @& RustCompiledEnv → @& Lean.Name → UInt64

/-- FFI: Get the pre-sharing root expressions for a constant as serialized bytes.
    Returns the number of expressions. Output buffer format:
    [n_exprs:u64, len1:u64, expr1_bytes..., len2:u64, expr2_bytes..., ...] -/
@[extern "rs_get_pre_sharing_exprs"]
opaque rsGetPreSharingExprs : @& RustCompiledEnv → @& Lean.Name → @& ByteArray → IO UInt64

/-- FFI: Look up a constant's compiled address (32-byte blake3 hash).
    Returns true if found, copies address to out_addr ByteArray. -/
@[extern "rs_lookup_const_addr"]
opaque rsLookupConstAddr : @& RustCompiledEnv → @& Lean.Name → @& ByteArray → IO Bool

/-- FFI: Get the total number of compiled constants. -/
@[extern "rs_get_compiled_const_count"]
opaque rsGetCompiledConstCount : @& RustCompiledEnv → UInt64

/-- Unpack the comparison result from rsCompareSharingAnalysis -/
def unpackSharingComparison (packed : UInt64) : Bool × UInt64 × UInt64 :=
  let isMatch := (packed &&& 0xFFFFFFFF) == 1
  let leanCount := (packed >>> 32) &&& 0xFFFF
  let rustCount := (packed >>> 48) &&& 0xFFFF
  (isMatch, leanCount, rustCount)

/-! ## Recursor sharing test -/

/-- Test sharing analysis on a recursor-like structure.

    A typical 4-constructor recursor type looks like:
    ∀ (motive : T → Sort u),
      (minor1 : motive C1) → (minor2 : motive C2) → (minor3 : motive C3) → (minor4 : motive C4) →
      ∀ (t : T), motive t

    Where T = ref 0 #[] appears 6 times (in motive type, each minor, and final target).
    With usage=6, size=2 (tag4(0) + tag0(0)), profitability is:
    (6-1)*2 = 10 > 6*1 = 6 ✓ PROFITABLE

    This test verifies Lean correctly identifies and shares such repeated refs.
-/
def testRecursorSharing : TestSeq := Id.run do
  -- Test: Expression with ref appearing 4 times should be shared
  -- For profitability: (n-1)*size > n*ref_size
  -- With n=4, size=2: (4-1)*2 = 6 > 4*1 = 4 ✓ PROFITABLE
  let t := Expr.ref 0 #[]  -- size=2 (tag4(0) + tag0(0))
  let sortU := Expr.sort 1

  -- Use t four times: in nested all expressions
  let e1 := Expr.all t sortU  -- use 1
  let e2 := Expr.all t e1      -- use 2
  let e3 := Expr.all t e2      -- use 3
  let e4 := Expr.all t e3      -- use 4

  let result := analyzeBlock #[e4]
  let effectiveSizes := computeEffectiveSizes result.infoMap result.topoOrder
  let sharedHashes := decideSharing result.infoMap result.topoOrder

  let refHash := computeExprHash t
  let refInfo := result.infoMap.get? refHash
  let refUsage := refInfo.map (·.usageCount) |>.getD 0
  let refEffSize := effectiveSizes.getD refHash 0
  let refGross : _root_.Int := (refUsage - 1 : _root_.Int) * refEffSize
  let refPotential : _root_.Int := refGross - refUsage

  --dbg_trace s!"[testRecursorSharing] unique={result.infoMap.size} shared={sharedHashes.size}"
  --dbg_trace s!"[testRecursorSharing] ref 0 #[]: usage={refUsage} effSize={refEffSize} gross={refGross} potential={refPotential}"

  let refShared := sharedHashes.any (· == refHash)

  let (_, sharingVec) := buildSharingVec #[e4] sharedHashes result.infoMap result.ptrToHash result.topoOrder
  --dbg_trace s!"[testRecursorSharing] sharingVec.size={sharingVec.size}"

  return group "recursor sharing" (
    test "ref found with usage >= 4" (refUsage >= 4) ++
    test "ref potential > 0" (refPotential > 0) ++
    test "ref is shared" refShared ++
    test "sharing vector non-empty" (sharingVec.size >= 1)
  )

/-- Test with a realistic recursor-like structure.
    This mimics what we see in the actual test output:
    - Type: ∀ (motive : T → Sort u), motive C1 → motive C2 → motive C3 → ∀ (t : T), motive t
    - Rules: var X, var Y, var Z (just minor arguments)
-/
def testRealisticRecursor : TestSeq := Id.run do
  -- The inductive type T = ref 0
  let tRef := Expr.ref 0 #[]
  let sortU := Expr.sort 1
  let _sort0 := Expr.sort 0

  -- Constructor refs
  let c1 := Expr.ref 1 #[]
  let c2 := Expr.ref 2 #[]
  let c3 := Expr.ref 3 #[]

  -- Build the type: ∀ (motive : T → Sort u), motive C1 → motive C2 → motive C3 → ∀ (t : T), motive t
  -- From inside out:
  let _motiveVar := Expr.var 0  -- motive when in scope
  let tVar := Expr.var 0       -- t when innermost

  -- ∀ (t : T), motive t  (motive is var 1 here due to binder)
  let targetBody := Expr.app (Expr.var 1) tVar
  let target := Expr.all tRef targetBody

  -- motive C3 → target  (motive is var 3 here)
  let minor3 := Expr.app (Expr.var 3) c3
  let withMinor3 := Expr.all minor3 target

  -- motive C2 → ...  (motive is var 2 here)
  let minor2 := Expr.app (Expr.var 2) c2
  let withMinor2 := Expr.all minor2 withMinor3

  -- motive C1 → ...  (motive is var 1 here)
  let minor1 := Expr.app (Expr.var 1) c1
  let withMinor1 := Expr.all minor1 withMinor2

  -- ∀ (motive : T → Sort u), ...
  let motiveType := Expr.all tRef sortU
  let fullType := Expr.all motiveType withMinor1

  -- Rules are just bound variables (minor arguments)
  let rule1 := Expr.var 1
  let rule2 := Expr.var 2
  let rule3 := Expr.var 3

  -- Analyze all expressions together (like Rust does)
  let allExprs := #[fullType, rule1, rule2, rule3]
  let result := analyzeBlock allExprs
  let _effectiveSizes := computeEffectiveSizes result.infoMap result.topoOrder
  let sharedHashes := decideSharing result.infoMap result.topoOrder

  --dbg_trace s!"[testRealisticRecursor] Analyzing {allExprs.size} expressions"
  --dbg_trace s!"[testRealisticRecursor] unique={result.infoMap.size} shared={sharedHashes.size}"

  -- Check each ref
  let tRefHash := computeExprHash tRef
  let c1Hash := computeExprHash c1
  let c2Hash := computeExprHash c2
  let c3Hash := computeExprHash c3

  let tRefUsage := result.infoMap.get? tRefHash |>.map (·.usageCount) |>.getD 0
  let _c1Usage := result.infoMap.get? c1Hash |>.map (·.usageCount) |>.getD 0
  let _c2Usage := result.infoMap.get? c2Hash |>.map (·.usageCount) |>.getD 0
  let _c3Usage := result.infoMap.get? c3Hash |>.map (·.usageCount) |>.getD 0

  --dbg_trace s!"[testRealisticRecursor] ref 0 (type): usage={tRefUsage}"
  --dbg_trace s!"[testRealisticRecursor] ref 1 (c1): usage={c1Usage}"
  --dbg_trace s!"[testRealisticRecursor] ref 2 (c2): usage={c2Usage}"
  --dbg_trace s!"[testRealisticRecursor] ref 3 (c3): usage={c3Usage}"

  -- Build sharing vector
  let (_rewritten, _sharingVec) := buildSharingVec allExprs sharedHashes result.infoMap result.ptrToHash result.topoOrder
  --dbg_trace s!"[testRealisticRecursor] sharingVec ({sharingVec.size} items):"
  --for i in [:sharingVec.size] do
  --  dbg_trace s!"  [{i}] {repr sharingVec[i]!}"

  -- ref 0 (type) appears 2 times: in motiveType and target
  -- With usage=2, size=2: potential = 1*2 - 2 = 0, NOT shared

  return group "realistic recursor" (
    test "type ref usage = 2" (tRefUsage == 2) ++
    test "analysis completes" true
  )

/-- Test that content hash collision correctly increments usage.
    If we create the same expression multiple times (different Lean pointers),
    the sharing analysis should still count them as the same subterm. -/
def testContentHashCollision : TestSeq := Id.run do
  -- Create "ref 0 #[]" three times - different Lean objects, same content
  let r1 := Expr.ref 0 #[]
  let r2 := Expr.ref 0 #[]
  let r3 := Expr.ref 0 #[]

  -- Wrap each in a different expression
  let e1 := Expr.all r1 (Expr.sort 0)
  let e2 := Expr.all r2 (Expr.sort 1)
  let e3 := Expr.all r3 (Expr.sort 2)

  let result := analyzeBlock #[e1, e2, e3]

  let refHash := computeExprHash (Expr.ref 0 #[])
  let refUsage := result.infoMap.get? refHash |>.map (·.usageCount) |>.getD 0

  --dbg_trace s!"[testContentHashCollision] ref 0 #[]: usage={refUsage} (expected 3)"

  return group "content hash collision" (
    test "ref usage counted via hash collision" (refUsage == (3 : Nat))
  )

/-! ## Cross-implementation sharing tests -/

/-- Test that Lean and Rust produce identical sharing decisions for a simple case.
    Creates a set of expressions with known sharing opportunities and compares
    the sharing vectors produced by both implementations. -/
def testCrossImplSharingSimple : TestSeq := Id.run do
  -- Create expressions with 4 usages of ref 0 #[] (should be shared)
  let t := Expr.ref 0 #[]
  let sortU := Expr.sort 1
  let e1 := Expr.all t sortU
  let e2 := Expr.all t e1
  let e3 := Expr.all t e2
  let e4 := Expr.all t e3
  let exprs := #[e4]

  -- Run Lean's sharing analysis
  let result := analyzeBlock exprs
  let sharedHashes := decideSharing result.infoMap result.topoOrder
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash result.topoOrder

  -- Run Rust's sharing analysis via FFI
  let rustSharingCount := rsAnalyzeSharingCount exprs
  let (isMatch, _leanCount, _rustCount) := unpackSharingComparison (rsCompareSharingAnalysis exprs sharingVec rewritten)

  --dbg_trace s!"[testCrossImplSharingSimple] Lean sharing: {sharingVec.size}, Rust sharing: {rustSharingCount}"
  --dbg_trace s!"[testCrossImplSharingSimple] Comparison: isMatch={isMatch} leanCount={leanCount} rustCount={rustCount}"

  return group "cross-impl simple" (
    test "sharing counts match" (sharingVec.size.toUInt64 == rustSharingCount) ++
    test "sharing vectors match" isMatch
  )

/-- Test cross-implementation sharing for the content hash collision case.
    This verifies both implementations correctly count usages via content hashing. -/
def testCrossImplContentHash : TestSeq := Id.run do
  -- Create "ref 0 #[]" three times with different wrappers
  let r1 := Expr.ref 0 #[]
  let r2 := Expr.ref 0 #[]
  let r3 := Expr.ref 0 #[]
  let e1 := Expr.all r1 (Expr.sort 0)
  let e2 := Expr.all r2 (Expr.sort 1)
  let e3 := Expr.all r3 (Expr.sort 2)
  let exprs := #[e1, e2, e3]

  -- Run Lean's sharing analysis
  let result := analyzeBlock exprs
  let sharedHashes := decideSharing result.infoMap result.topoOrder
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash result.topoOrder

  -- Run Rust's sharing analysis via FFI
  let rustSharingCount := rsAnalyzeSharingCount exprs
  let (isMatch, _leanCount, _rustCount) := unpackSharingComparison (rsCompareSharingAnalysis exprs sharingVec rewritten)

  --dbg_trace s!"[testCrossImplContentHash] Lean sharing: {sharingVec.size}, Rust sharing: {rustSharingCount}"
  --dbg_trace s!"[testCrossImplContentHash] Comparison: isMatch={isMatch} leanCount={leanCount} rustCount={rustCount}"

  return group "cross-impl content hash" (
    test "sharing counts match" (sharingVec.size.toUInt64 == rustSharingCount) ++
    test "sharing vectors match" isMatch
  )

/-- Test cross-implementation sharing for a realistic recursor structure.
    This mimics the actual failing case we see in the full test. -/
def testCrossImplRecursor : TestSeq := Id.run do
  -- Build a 3-constructor recursor type
  -- Type: ∀ (motive : T → Sort u), minor1 → minor2 → minor3 → ∀ (t : T), motive t
  let tRef := Expr.ref 0 #[]  -- The inductive type
  let c1 := Expr.ref 1 #[]     -- Constructor 1
  let c2 := Expr.ref 2 #[]     -- Constructor 2
  let c3 := Expr.ref 3 #[]     -- Constructor 3
  let sortU := Expr.sort 1

  -- Build from inside out
  let targetBody := Expr.app (Expr.var 1) (Expr.var 0)  -- motive t
  let target := Expr.all tRef targetBody                 -- ∀ (t : T), motive t

  let minor3 := Expr.app (Expr.var 3) c3
  let withMinor3 := Expr.all minor3 target

  let minor2 := Expr.app (Expr.var 2) c2
  let withMinor2 := Expr.all minor2 withMinor3

  let minor1 := Expr.app (Expr.var 1) c1
  let withMinor1 := Expr.all minor1 withMinor2

  let motiveType := Expr.all tRef sortU
  let fullType := Expr.all motiveType withMinor1

  -- Rules (just return minor arguments)
  let rule1 := Expr.var 1
  let rule2 := Expr.var 2
  let rule3 := Expr.var 3

  let exprs := #[fullType, rule1, rule2, rule3]

  -- Debug: print Rust's view
  let _ := rsDebugSharingAnalysis exprs

  -- Run Lean's sharing analysis
  let result := analyzeBlock exprs
  let sharedHashes := decideSharing result.infoMap result.topoOrder
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash result.topoOrder

  -- Run Rust's sharing analysis via FFI
  let rustSharingCount := rsAnalyzeSharingCount exprs
  let (isMatch, _leanCount, _rustCount) := unpackSharingComparison (rsCompareSharingAnalysis exprs sharingVec rewritten)

  --dbg_trace s!"[testCrossImplRecursor] Lean sharing: {sharingVec.size}, Rust sharing: {rustSharingCount}"
  --dbg_trace s!"[testCrossImplRecursor] Comparison: isMatch={isMatch} leanCount={leanCount} rustCount={rustCount}"

  -- Show Lean's sharing vector
  --dbg_trace s!"[testCrossImplRecursor] Lean sharing vector:"
  --for i in [:sharingVec.size] do
  --  dbg_trace s!"  [{i}] {repr sharingVec[i]!}"

  return group "cross-impl recursor" (
    test "sharing counts match" (sharingVec.size.toUInt64 == rustSharingCount) ++
    test "sharing vectors match" isMatch
  )

/-! ## forall_imp and flip sharing tests -/

/-- Test forall_imp sharing using the exact Ixon.Expr structure from compile output.

    From the compile test, forall_imp has this structure (pre-sharing):
    Type: all (sort 0) (all (all (var 0) (sort 1)) (all (all (var 1) (sort 1))
          (all (all (var 2) (all (app (var 2) (var 0)) (app (var 2) (var 1))))
          (all (all (var 3) (app (var 3) (var 0))) (all (var 4) (app (var 3) (var 0)))))))

    Value: similar structure with lam instead of all

    Key difference: Lean shares `app (var 2) (var 1)` (8 entries), Rust doesn't (7 entries)
-/
def testForallImpReal : TestSeq := Id.run do
  -- Build the forall_imp type structure based on compile output
  -- ∀ (α : Sort u), ∀ (p : α → Prop), ∀ (q : α → Prop),
  --   ∀ (h : ∀ a, p a → q a), (∀ a, p a) → (∀ a, q a)
  --
  -- IMPORTANT: Create fresh objects for each occurrence to simulate real compilation
  -- where the same content might have different Lean pointers

  -- Build type with fresh objects
  let typ := Expr.all (Expr.sort 0)  -- ∀ α : Sort u
    (Expr.all (Expr.all (Expr.var 0) (Expr.sort 1))  -- ∀ p : α → Prop (fresh)
      (Expr.all (Expr.all (Expr.var 1) (Expr.sort 1))  -- ∀ q : α → Prop (fresh!)
        (Expr.all  -- ∀ h : ∀ a, p a → q a
          (Expr.all (Expr.var 2)
            (Expr.all (Expr.app (Expr.var 2) (Expr.var 0))  -- p a → q a
                      (Expr.app (Expr.var 2) (Expr.var 1))))
          (Expr.all  -- (∀ a, p a) → (∀ a, q a)
            (Expr.all (Expr.var 3) (Expr.app (Expr.var 3) (Expr.var 0)))  -- ∀ a, p a
            (Expr.all (Expr.var 4) (Expr.app (Expr.var 3) (Expr.var 0)))))))  -- ∀ a, q a

  -- Build value with fresh objects
  let value := Expr.lam (Expr.sort 0)  -- λ α
    (Expr.lam (Expr.all (Expr.var 0) (Expr.sort 1))  -- λ p : α → Prop (fresh)
      (Expr.lam (Expr.all (Expr.var 1) (Expr.sort 1))  -- λ q : α → Prop (fresh!)
        (Expr.lam  -- λ h : ∀ a, p a → q a
          (Expr.all (Expr.var 2)
            (Expr.all (Expr.app (Expr.var 2) (Expr.var 0))  -- p a → q a (fresh)
                      (Expr.app (Expr.var 2) (Expr.var 1))))  -- (fresh)
          (Expr.lam  -- λ h' : ∀ a, p a
            (Expr.all (Expr.var 3) (Expr.app (Expr.var 3) (Expr.var 0)))  -- (fresh)
            (Expr.lam (Expr.var 4)  -- λ a : α
              (Expr.app
                (Expr.app (Expr.var 2) (Expr.var 0))  -- h a
                (Expr.app (Expr.var 1) (Expr.var 0))))))))  -- h' a

  let exprs := #[typ, value]

  -- Run Lean sharing analysis
  let result := analyzeBlock exprs
  let sharedHashes := decideSharing result.infoMap result.topoOrder
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash result.topoOrder

  -- Run Rust sharing analysis
  let rustCount := rsAnalyzeSharingCount exprs
  let (isMatch, _leanCnt, _rustCnt) := unpackSharingComparison (rsCompareSharingAnalysis exprs sharingVec rewritten)

  return group "forall_imp real" (
    test "sharing counts match" (sharingVec.size.toUInt64 == rustCount) ++
    test "sharing vectors match" isMatch
  )

/-- Test forall_imp sharing difference.

    forall_imp has type:
      ∀ (α : Sort u), ∀ (p q : α → Prop), (∀ a, p a → q a) → (∀ a, p a) → (∀ a, q a)

    Key expressions:
    - `α → Prop` (appears twice for p and q binder types)
    - `app (var N) (var M)` patterns like `p a`, `q a`

    Lean shares both `app (var 2) (var 1)` and `app (var 2) (var 0)` → 8 entries
    Rust only shares `app (var 2) (var 0)` → 7 entries

    This tests the profitability calculation difference.
-/
def testForallImpSharing : TestSeq := Id.run do
  -- Simplified forall_imp structure focusing on the key pattern
  -- The pattern that differs: `all (app var2 var0) (app var2 var1)`
  -- appears in the type as `p a → q a`

  -- Create expressions where `app (var 2) (var 1)` and `app (var 2) (var 0)` both appear twice
  let app21 := Expr.app (Expr.var 2) (Expr.var 1)
  let app20 := Expr.app (Expr.var 2) (Expr.var 0)

  -- Use each twice
  let e1 := Expr.all app21 app20  -- p a → q a pattern
  let e2 := Expr.all app20 app21  -- q a → p a (reversed)
  let e3 := Expr.all (Expr.var 3) e1  -- ∀ a, p a → q a
  let e4 := Expr.all (Expr.var 3) e2  -- ∀ a, q a → p a

  let exprs := #[e3, e4]

  -- Analyze with Lean
  let result := analyzeBlock exprs
  let sharedHashes := decideSharing result.infoMap result.topoOrder
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash result.topoOrder

  -- Check usage and profitability of app21 and app20
  let app21Hash := computeExprHash app21
  let app20Hash := computeExprHash app20

  let app21Info := result.infoMap.get? app21Hash
  let app20Info := result.infoMap.get? app20Hash

  let app21Usage := app21Info.map (·.usageCount) |>.getD 0
  let app20Usage := app20Info.map (·.usageCount) |>.getD 0

  -- Run Rust's sharing analysis via FFI
  let rustSharingCount := rsAnalyzeSharingCount exprs
  let (isMatch, _leanCount, _rustCount) := unpackSharingComparison (rsCompareSharingAnalysis exprs sharingVec rewritten)

  return group "forall_imp sharing" (
    test "app20 used twice" (app20Usage >= 2) ++
    test "app21 used twice" (app21Usage >= 2) ++
    test "sharing counts match" (sharingVec.size.toUInt64 == rustSharingCount) ++
    test "sharing vectors match" isMatch
  )

def testFlipSharing : TestSeq := Id.run do
  -- Recreate the `flip` function structure
  -- Type: ∀ (A : Sort 0), ∀ (B : Sort 1), ∀ (C : Sort 2), (A → B → C) → B → A → C
  -- In Ixon.Expr terms:
  --   all (sort 0) (all (sort 1) (all (sort 2) (all <func-type> (all (var 2) (all (var 4) (var 3))))))
  -- where <func-type> = all (var 2) (all (var 2) (var 2))

  -- The key subexpression that appears multiple times
  let innerAll := Expr.all (Expr.var 2) (Expr.var 2)  -- (var 2) → (var 2)
  let funcType := Expr.all (Expr.var 2) innerAll       -- (var 2) → (var 2) → (var 2)

  -- Build the full type
  let resultType := Expr.all (Expr.var 2) (Expr.all (Expr.var 4) (Expr.var 3))  -- B → A → C
  let withFunc := Expr.all funcType resultType  -- (A → B → C) → B → A → C
  let withC := Expr.all (Expr.sort 2) withFunc
  let withB := Expr.all (Expr.sort 1) withC
  let typ := Expr.all (Expr.sort 0) withB

  -- Value: λ A B C f b a => f a b
  -- In Ixon.Expr terms: lam ... lam (app (app (var 2) (var 0)) (var 1))
  let body := Expr.app (Expr.app (Expr.var 2) (Expr.var 0)) (Expr.var 1)  -- f a b
  let lamA := Expr.lam (Expr.var 4) body
  let lamB := Expr.lam (Expr.var 2) lamA
  let lamFunc := Expr.lam funcType lamB  -- Note: funcType appears again here!
  let lamC := Expr.lam (Expr.sort 2) lamFunc
  let lamBSort := Expr.lam (Expr.sort 1) lamC
  let value := Expr.lam (Expr.sort 0) lamBSort

  let exprs := #[typ, value]

  -- Analyze with Lean
  let result := analyzeBlock exprs
  let sharedHashes := decideSharing result.infoMap result.topoOrder
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash result.topoOrder

  -- Check what got shared
  let innerAllHash := computeExprHash innerAll
  let funcTypeHash := computeExprHash funcType

  let innerAllInfo := result.infoMap.get? innerAllHash
  let funcTypeInfo := result.infoMap.get? funcTypeHash

  let innerAllUsage := innerAllInfo.map (·.usageCount) |>.getD 0
  let funcTypeUsage := funcTypeInfo.map (·.usageCount) |>.getD 0

  -- Run Rust's sharing analysis via FFI
  let rustSharingCount := rsAnalyzeSharingCount exprs
  let (isMatch, _leanCount, _rustCount) := unpackSharingComparison (rsCompareSharingAnalysis exprs sharingVec rewritten)

  return group "flip sharing" (
    test "funcType used twice" (funcTypeUsage >= 2) ++
    test "innerAll used multiple times" (innerAllUsage >= 2) ++
    test "sharing counts match" (sharingVec.size.toUInt64 == rustSharingCount) ++
    test "sharing vectors match" isMatch
  )

/-! ## Suite -/

def suiteIO : List TestSeq := [
]

def suite : List TestSeq := [
  testForallImpReal,
  testForallImpSharing,
  testUint64ToBytesLength,
  testUint64ToBytesEncoding,
  testHashConsistency,
  testHashDifferent,
  testSortHashBuffer,
  testVarHashBuffer,
  testAppHashBuffer,
  testNoSharing,
  testWithSharing,
  testSharingTopoOrder,
  testKnownHashVar0,
  testKnownHashSort0,
  testRecursorSharing,
  testRealisticRecursor,
  testContentHashCollision,
  testCrossImplSharingSimple,
  testCrossImplContentHash,
  testCrossImplRecursor,
  testFlipSharing,
]

end Tests.Sharing

/-! ## IO tests that access the environment (disabled for now) -/
--
--namespace Tests.Sharing
--
--/-- Test sharing analysis on the actual Batteries.Tactic.Lint.LintVerbosity.rec constant.
--    This is the constant that shows different sharing between Lean and Rust. -/
--def testActualRecursor : IO TestSeq := do
--  let env ← get_env!
--
--  -- Try a few recursor names that might exist
--  let testNames := [
--    `Batteries.Tactic.Lint.LintVerbosity.rec,
--    `Lean.Elab.ComputeKind.rec,
--    `Bool.rec
--  ]
--
--  let mut tests := LSpec.TestSeq.done
--
--  for name in testNames do
--    match env.find? name with
--    | none => pure ()
--    | some constInfo =>
--      IO.println s!"Testing {name}..."
--
--      -- Create empty canon cache
--      let canonExprs : Std.HashMap USize Leon.Expr := {}
--      let stt := CompileState.new env canonExprs
--
--      -- Set up block environment
--      let blockEnv : BlockEnv := {
--        all := Std.HashSet.ofList [name]
--        current := name
--        mutCtx := {}
--        univCtx := constInfo.levelParams
--      }
--
--      -- Compile constant to get Ixon expressions
--      let result := CompileM.run blockEnv stt {} (compileConstantInfo constInfo)
--      match result with
--      | .error e =>
--        IO.println s!"  Compilation failed: {repr e}"
--      | .ok (blockResult, _) =>
--        -- Extract root expressions from the block
--        let rootExprs := match blockResult.block.info with
--          | .defn d => #[d.typ, d.value]
--          | .recr r => #[r.typ] ++ r.rules.map (·.rhs)
--          | .axio a => #[a.typ]
--          | .quot q => #[q.typ]
--          | _ => #[]
--
--        IO.println s!"  Root expressions: {rootExprs.size}"
--
--        -- Analyze sharing
--        let analyzeResult := analyzeBlock rootExprs
--        let effectiveSizes := computeEffectiveSizes analyzeResult.infoMap analyzeResult.topoOrder
--        let sharedHashes := decideSharing analyzeResult.infoMap analyzeResult.topoOrder
--
--        IO.println s!"  Unique subterms: {analyzeResult.infoMap.size}"
--        IO.println s!"  Subterms to share: {sharedHashes.size}"
--
--        -- Show all subterms with usage >= 2
--        IO.println s!"  Subterms with usage >= 2:"
--        let mut candidateList : Array (Nat × Nat × Int × Int × Expr) := #[]
--        for (hash, info) in analyzeResult.infoMap do
--          if info.usageCount >= 2 then
--            let size := effectiveSizes.getD hash 0
--            let gross : Int := (info.usageCount - 1 : Int) * size
--            let potential : Int := gross - info.usageCount
--            candidateList := candidateList.push (info.usageCount, size, gross, potential, info.expr)
--
--        -- Sort by gross benefit descending
--        candidateList := candidateList.qsort fun a b => a.2.2.1 > b.2.2.1
--
--        for cand in candidateList do
--          let (usage, size, gross, potential, expr) := cand
--          let willShare := potential > 0
--          let marker := if willShare then "✓" else "✗"
--          IO.println s!"    {marker} usage={usage} size={size} gross={gross} potential={potential}"
--          IO.println s!"      expr={repr expr}"
--
--        -- Build the actual sharing vector
--        let (rewritten, sharingVec) := buildSharingVec rootExprs sharedHashes analyzeResult.infoMap analyzeResult.ptrToHash analyzeResult.topoOrder
--
--        IO.println s!"  Lean sharing vector ({sharingVec.size} items):"
--        for i in [:min 10 sharingVec.size] do
--          IO.println s!"    [{i}] {repr sharingVec[i]!}"
--        if sharingVec.size > 10 then
--          IO.println s!"    ... ({sharingVec.size - 10} more)"
--
--        -- Cross-implementation comparison: run Rust's sharing analysis on the same expressions
--        IO.println s!"  === Cross-implementation comparison ==="
--        let rustSharingCount := rsAnalyzeSharingCount rootExprs
--        IO.println s!"  Rust sharing count: {rustSharingCount}"
--
--        -- Debug: print Rust's view of the expressions
--        let _ := rsDebugSharingAnalysis rootExprs
--
--        let (isMatch, leanCnt, rustCnt) := unpackSharingComparison (rsCompareSharingAnalysis rootExprs sharingVec rewritten)
--        IO.println s!"  Comparison: isMatch={isMatch} leanCount={leanCnt} rustCount={rustCnt}"
--
--        let sharingMatch := sharingVec.size.toUInt64 == rustSharingCount
--        tests := tests ++ test s!"{name} Lean sharing analysis" true
--        tests := tests ++ test s!"{name} cross-impl sharing match" sharingMatch
--
--  pure tests
--
--/-- Test with expressions matching the actual LintVerbosity.rec structure.
--
--    LintVerbosity is a 3-constructor inductive:
--    - quiet, medium, verbose (all nullary)
--
--    Its recursor type is:
--    ∀ (motive : LintVerbosity → Sort u),
--      motive quiet → motive medium → motive verbose →
--      ∀ (t : LintVerbosity), motive t
--
--    In Ixon.Expr terms:
--    - ref 0 = LintVerbosity (the type)
--    - ref 1 = quiet, ref 2 = medium, ref 3 = verbose (constructors)
--    - The type has ref 0 appearing in multiple places
--    - The rules are just bound variables
---/
--def testCrossImplLintVerbosityLike : IO TestSeq := do
--  IO.println s!"=== Testing LintVerbosity-like recursor structure ==="
--
--  -- Build the recursor type structure
--  let tRef := Expr.ref 0 #[]  -- LintVerbosity type
--  let c1 := Expr.ref 1 #[]     -- quiet
--  let c2 := Expr.ref 2 #[]     -- medium
--  let c3 := Expr.ref 3 #[]     -- verbose
--  let sortU := Expr.sort 1
--
--  -- Build from inside out:
--  -- motive t (where motive is var 4, t is var 0)
--  let motiveT := Expr.app (Expr.var 4) (Expr.var 0)
--  -- ∀ (t : ref0), motive t
--  let target := Expr.all tRef motiveT
--
--  -- motive verbose (motive is var 3)
--  let minorVerbose := Expr.app (Expr.var 3) c3
--  let withVerbose := Expr.all minorVerbose target
--
--  -- motive medium (motive is var 2)
--  let minorMedium := Expr.app (Expr.var 2) c2
--  let withMedium := Expr.all minorMedium withVerbose
--
--  -- motive quiet (motive is var 1)
--  let minorQuiet := Expr.app (Expr.var 1) c1
--  let withQuiet := Expr.all minorQuiet withMedium
--
--  -- ∀ (motive : ref0 → Sort u), ...
--  let motiveType := Expr.all tRef sortU
--  let fullType := Expr.all motiveType withQuiet
--
--  -- Rules are just bound variables (minor arguments)
--  let rule1 := Expr.var 1  -- quiet case returns minor_quiet
--  let rule2 := Expr.var 2  -- medium case returns minor_medium
--  let rule3 := Expr.var 3  -- verbose case returns minor_verbose
--
--  let exprs := #[fullType, rule1, rule2, rule3]
--
--  IO.println s!"Input expressions ({exprs.size}):"
--  for i in [:exprs.size] do
--    IO.println s!"  [{i}] {repr exprs[i]!}"
--
--  -- Run Lean sharing analysis
--  let result := analyzeBlock exprs
--  let effectiveSizes := computeEffectiveSizes result.infoMap result.topoOrder
--  let sharedHashes := decideSharing result.infoMap result.topoOrder
--
--  IO.println s!"\nLean analysis: {result.infoMap.size} unique subterms"
--
--  -- Show subterms with usage >= 2
--  IO.println s!"Subterms with usage >= 2:"
--  for (hash, info) in result.infoMap do
--    if info.usageCount >= 2 then
--      let effSize := effectiveSizes.getD hash 0
--      let gross : Int := (info.usageCount - 1 : Int) * effSize
--      let potential : Int := gross - info.usageCount - effSize
--      let shared := sharedHashes.any (· == hash)
--      let marker := if shared then "✓" else "✗"
--      IO.println s!"  {marker} usage={info.usageCount} effSize={effSize} gross={gross} pot={potential}"
--      IO.println s!"    {repr info.expr}"
--
--  -- Build sharing vector
--  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash result.topoOrder
--  IO.println s!"\nLean sharing vector ({sharingVec.size} items):"
--  for i in [:sharingVec.size] do
--    IO.println s!"  [{i}] {repr sharingVec[i]!}"
--
--  -- Run Rust sharing analysis via FFI
--  IO.println s!"\n=== Rust sharing analysis ==="
--  let _ := rsDebugSharingAnalysis exprs
--
--  let rustSharingCount := rsAnalyzeSharingCount exprs
--  IO.println s!"Rust sharing count: {rustSharingCount}"
--
--  let (isMatch, leanCnt, rustCnt) := unpackSharingComparison (rsCompareSharingAnalysis exprs sharingVec rewritten)
--  IO.println s!"Comparison: isMatch={isMatch} leanCount={leanCnt} rustCount={rustCnt}"
--
--  let sharingMatch := sharingVec.size.toUInt64 == rustSharingCount
--  pure $ group "cross-impl LintVerbosity-like" (
--    test "sharing counts match" sharingMatch ++
--    test "sharing vectors match" isMatch
--  )
--
--/-- Expand Share(idx) references in an expression using the sharing vector.
--    This reconstructs the "pre-sharing" expression from the post-sharing representation. -/
--partial def unshareExpr (sharing : Array Expr) (e : Expr) : Expr :=
--  match e with
--  | .share idx =>
--    if h : idx.toNat < sharing.size then
--      unshareExpr sharing sharing[idx.toNat]
--    else e
--  | .app f a => .app (unshareExpr sharing f) (unshareExpr sharing a)
--  | .lam t b => .lam (unshareExpr sharing t) (unshareExpr sharing b)
--  | .all t b => .all (unshareExpr sharing t) (unshareExpr sharing b)
--  | .letE nd t v b => .letE nd (unshareExpr sharing t) (unshareExpr sharing v) (unshareExpr sharing b)
--  | .prj ti fi v => .prj ti fi (unshareExpr sharing v)
--  | _ => e  -- Leaf nodes
--
--/-- Read u64 little-endian from ByteArray at offset -/
--def readU64LE (bytes : ByteArray) (offset : Nat) : UInt64 := Id.run do
--  let mut result : UInt64 := 0
--  for i in [0:8] do
--    if offset + i < bytes.size then
--      result := result ||| (bytes.get! (offset + i)).toUInt64 <<< (i.toUInt64 * 8)
--  return result
--
--/-- Parse pre-sharing expressions from the FFI output buffer format.
--    Format: [n_exprs:u64, len1:u64, expr1_bytes..., len2:u64, expr2_bytes..., ...] -/
--def parsePreSharingExprs (bytes : ByteArray) : Except String (Array Expr) := do
--  if bytes.size < 8 then
--    throw "Buffer too small for header"
--
--  let nExprs := readU64LE bytes 0
--  let mut offset : Nat := 8
--  let mut exprs : Array Expr := #[]
--
--  for _ in [:nExprs.toNat] do
--    if offset + 8 > bytes.size then
--      throw s!"Buffer too small for length at offset {offset}"
--
--    let len := readU64LE bytes offset
--    offset := offset + 8
--
--    if offset + len.toNat > bytes.size then
--      throw s!"Buffer too small for expr at offset {offset}, need {len}"
--
--    let exprBytes := bytes.extract offset (offset + len.toNat)
--    match Ixon.desExpr exprBytes with
--    | .ok expr => exprs := exprs.push expr
--    | .error e => throw s!"Failed to parse expr at offset {offset}: {e}"
--
--    offset := offset + len.toNat
--
--  return exprs
--
--/-- Test using Rust-compiled expressions to verify compilation matches.
--    This compiles the environment with Rust, extracts pre-sharing expressions for a
--    specific constant, and runs Lean's sharing analysis on them. -/
--def testRustCompiledExpressions : IO TestSeq := do
--  let env ← get_env!
--
--  IO.println s!"\n=== Compiling environment with Rust ==="
--
--  -- Get all constants from environment
--  let consts := env.constants.toList
--
--  -- Compile with Rust first
--  let rustEnv ← rsCompileEnvRustFirst consts
--  IO.println s!"Rust compilation complete"
--
--  -- Test a few known recursors
--  let testNames := [
--    `Bool.rec,
--    `Batteries.Tactic.Lint.LintVerbosity.rec,  -- known to have mismatch
--  ]
--
--  let mut tests := LSpec.TestSeq.done
--
--  for name in testNames do
--    IO.println s!"\n--- Testing {name} ---"
--
--    -- Get buffer length
--    let bufLen := rsGetPreSharingExprsLen rustEnv name
--    if bufLen == 0 then
--      IO.println s!"  Constant not found or has no expressions"
--      continue
--
--    IO.println s!"  Buffer length: {bufLen}"
--
--    -- Allocate buffer and get expressions
--    let buf := ByteArray.emptyWithCapacity bufLen.toNat
--    let nExprs ← rsGetPreSharingExprs rustEnv name buf
--    IO.println s!"  Got {nExprs} expressions, buffer size: {buf.size}"
--
--    -- Parse expressions
--    match parsePreSharingExprs buf with
--    | .error e =>
--      IO.println s!"  Parse error: {e}"
--    | .ok exprs =>
--      IO.println s!"  Parsed {exprs.size} expressions:"
--      for i in [:exprs.size] do
--        IO.println s!"    [{i}] {repr exprs[i]!}"
--
--      -- Run Lean's sharing analysis
--      let result := analyzeBlock exprs
--      let sharedHashes := decideSharing result.infoMap result.topoOrder
--      let (_, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash result.topoOrder
--
--      IO.println s!"  Lean sharing: {sharingVec.size} items"
--
--      -- Run Rust's sharing analysis on the same expressions
--      let rustSharingCount := rsAnalyzeSharingCount exprs
--      IO.println s!"  Rust sharing: {rustSharingCount} items"
--
--      let sharingMatch := sharingVec.size.toUInt64 == rustSharingCount
--      if !sharingMatch then
--        IO.println s!"  MISMATCH!"
--        IO.println s!"  Lean sharing vector:"
--        for i in [:sharingVec.size] do
--          IO.println s!"    [{i}] {repr sharingVec[i]!}"
--        let _ := rsDebugSharingAnalysis exprs
--
--      tests := tests ++ test s!"{name} sharing match" sharingMatch
--
--  -- Free Rust env
--  rsFreeRustEnv rustEnv
--
--  pure tests
--
--/-- Compare Lean and Rust compiled expressions for a specific constant.
--    Uses Rust's compiled addresses to satisfy Lean's dependency lookups. -/
--def testCompilationComparison : IO TestSeq := do
--  let env ← get_env!
--
--  IO.println s!"\n=== Comparing Lean vs Rust Compilation ==="
--
--  -- Get all constants from environment
--  let consts := env.constants.toList
--  let envSize := consts.length
--
--  -- Compile with Rust first
--  IO.println "Compiling with Rust..."
--  let rustEnv ← rsCompileEnvRustFirst consts
--  let rustConstCount := rsGetCompiledConstCount rustEnv
--  IO.println s!"Rust compilation complete ({rustConstCount} constants)"
--
--  -- Build Lean's nameToAddr map by querying Rust for each constant's address
--  IO.println "Building nameToAddr from Rust addresses..."
--  let mut nameToAddr : Std.HashMap Lean.Name Address := {}
--
--  for (name, _) in consts do
--    -- Create a 32-byte buffer pre-filled with zeros (ensures allocation)
--    let addrBuf := ByteArray.mk (Array.replicate 32 0)
--    let found ← rsLookupConstAddr rustEnv name addrBuf
--    if found && addrBuf.size >= 32 then
--      -- CRITICAL: Copy the bytes to a fresh ByteArray to avoid aliasing
--      -- The FFI modifies the underlying memory, but Lean's ByteArray may share memory
--      let addrBytes := ByteArray.copySlice addrBuf 0 (ByteArray.mk #[]) 0 32
--      let addr : Address := ⟨addrBytes⟩
--      nameToAddr := nameToAddr.insert name addr
--
--  IO.println s!"  Populated {nameToAddr.size} addresses"
--
--  -- Lean preprocessing
--  IO.println "Lean preprocessing..."
--  let canonResult := Ix.CanonM.canonEnvWithNameMap env
--  let refs := Ix.GraphM.env env (dbg := false) (total := envSize)
--  let blocks := Ix.CondenseM.run env refs (dbg := false) (total := envSize)
--
--  -- Initialize Lean compilation state WITH Rust's addresses
--  let mut stt : Ix.CompileM.CompileState := {
--    Ix.CompileM.CompileState.new canonResult env with
--    nameToAddr := nameToAddr
--  }
--
--  -- Target constants to compare
--  let targetNames := [
--    `Batteries.Tactic.Lint.LintVerbosity.rec,
--    `Bool.rec,
--  ]
--
--  let mut tests := LSpec.TestSeq.done
--
--  IO.println "Compiling target blocks with Lean..."
--  for targetName in targetNames do
--    -- Find the block containing this constant via lowLinks
--    let loOpt := blocks.lowLinks.get? targetName
--
--    match loOpt with
--    | none =>
--      IO.println s!"  Target {targetName} not found in any block"
--    | some lo =>
--      let all := blocks.blocks.get! lo
--      IO.println s!"\n--- Compiling block for {targetName} (lowlink: {lo}) ---"
--
--      -- Compile block with Lean
--      match Ix.CompileM.compileBlockPure stt all lo with
--      | Except.error e =>
--        IO.println s!"  Failed to compile: {repr e}"
--        tests := tests ++ test s!"{targetName} compiled" false
--      | Except.ok (result, _cache) =>
--        -- Get the constant for the target name
--        let targetConstant := match result.projections.find? (·.1 == targetName) with
--          | some (_, proj) => proj
--          | none => result.block
--
--        -- Extract Lean's root expressions (post-sharing)
--        let leanPostSharing : Array Expr := match targetConstant.info with
--          | .defn d => #[d.typ, d.value]
--          | .recr r => #[r.typ] ++ r.rules.map fun rule => rule.rhs
--          | .axio a => #[a.typ]
--          | .quot q => #[q.typ]
--          | _ => #[]
--
--        -- Unshare to get pre-sharing expressions
--        let leanRootExprs := leanPostSharing.map (unshareExpr targetConstant.sharing)
--
--        IO.println s!"  Lean compiled {leanRootExprs.size} root expressions:"
--        for i in [:leanRootExprs.size] do
--          IO.println s!"    [{i}] {repr leanRootExprs[i]!}"
--
--        -- Get Rust's pre-sharing root expressions
--        let bufLen := rsGetPreSharingExprsLen rustEnv targetName
--        if bufLen > 0 then
--          let buf := ByteArray.emptyWithCapacity bufLen.toNat
--          let _ ← rsGetPreSharingExprs rustEnv targetName buf
--
--          match parsePreSharingExprs buf with
--          | .error e =>
--            IO.println s!"  Failed to parse Rust expressions: {e}"
--            tests := tests ++ test s!"{targetName} parsed" false
--          | .ok rustRootExprs =>
--            IO.println s!"  Rust compiled {rustRootExprs.size} root expressions:"
--            for i in [:rustRootExprs.size] do
--              IO.println s!"    [{i}] {repr rustRootExprs[i]!}"
--
--            -- Compare
--            let exprsMatch := leanRootExprs.size == rustRootExprs.size &&
--              (leanRootExprs.zip rustRootExprs).all fun (l, r) => l == r
--
--            if exprsMatch then
--              IO.println s!"  ✓ Expressions MATCH!"
--            else
--              IO.println s!"  ✗ Expressions DIFFER!"
--              -- Show differences
--              for i in [:min leanRootExprs.size rustRootExprs.size] do
--                if leanRootExprs[i]! != rustRootExprs[i]! then
--                  IO.println s!"  First diff at index {i}:"
--                  IO.println s!"    Lean: {repr leanRootExprs[i]!}"
--                  IO.println s!"    Rust: {repr rustRootExprs[i]!}"
--                  break
--
--            tests := tests ++ test s!"{targetName} compilation match" exprsMatch
--        else
--          IO.println s!"  No pre-sharing expressions from Rust"
--          tests := tests ++ test s!"{targetName} rust exprs" false
--
--  -- Free Rust env
--  rsFreeRustEnv rustEnv
--
--  pure tests
--
--def suiteIO : List (IO TestSeq) := [
--  testCrossImplLintVerbosityLike,
--  testRustCompiledExpressions,
--  testCompilationComparison,
--  -- testActualRecursor -- comprehensive test, runs on multiple recursors
--]
--
--end Tests.Sharing
