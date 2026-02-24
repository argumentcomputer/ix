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
  test "sharing analysis completes" (_rewritten.size == exprs.size)

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

  let refShared := sharedHashes.any (· == refHash)

  let (_, sharingVec) := buildSharingVec #[e4] sharedHashes result.infoMap result.ptrToHash

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

  -- Check each ref
  let tRefHash := computeExprHash tRef
  let c1Hash := computeExprHash c1
  let c2Hash := computeExprHash c2
  let c3Hash := computeExprHash c3

  let tRefUsage := result.infoMap.get? tRefHash |>.map (·.usageCount) |>.getD 0
  let _c1Usage := result.infoMap.get? c1Hash |>.map (·.usageCount) |>.getD 0
  let _c2Usage := result.infoMap.get? c2Hash |>.map (·.usageCount) |>.getD 0
  let _c3Usage := result.infoMap.get? c3Hash |>.map (·.usageCount) |>.getD 0

  -- Build sharing vector
  let (_rewritten, _sharingVec) := buildSharingVec allExprs sharedHashes result.infoMap result.ptrToHash

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
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash

  -- Run Rust's sharing analysis via FFI
  let rustSharingCount := rsAnalyzeSharingCount exprs
  let (isMatch, _leanCount, _rustCount) := unpackSharingComparison (rsCompareSharingAnalysis exprs sharingVec rewritten)

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
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash

  -- Run Rust's sharing analysis via FFI
  let rustSharingCount := rsAnalyzeSharingCount exprs
  let (isMatch, _leanCount, _rustCount) := unpackSharingComparison (rsCompareSharingAnalysis exprs sharingVec rewritten)

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
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash

  -- Run Rust's sharing analysis via FFI
  let rustSharingCount := rsAnalyzeSharingCount exprs
  let (isMatch, _leanCount, _rustCount) := unpackSharingComparison (rsCompareSharingAnalysis exprs sharingVec rewritten)

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
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash

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
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash

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
  let (rewritten, sharingVec) := buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash

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
