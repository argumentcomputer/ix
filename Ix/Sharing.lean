/-
  Sharing Analysis for expression deduplication within mutual blocks.

  This module provides alpha-invariant sharing analysis using Merkle-tree hashing.
  Expressions that are structurally identical get the same hash, and we decide
  which subterms to share based on a profitability heuristic.

  Algorithm:
  1. Post-order traversal with Merkle hashing (blake3)
  2. Count usage of each unique subterm
  3. Profitability: share if (count - 1) * size > count * ref_size
  4. Build sharing vector in topological order (leaves first)
  5. Rewrite expressions with Share(idx) references
-/

import Ix.Ixon
import Ix.Address
import Ix.Common
import Std.Data.HashMap
import Blake3

namespace Ix.Sharing

/-- Convert UInt64 to ByteArray (little-endian, fixed 8 bytes).
    This MUST match Rust's `u64.to_le_bytes()` for hash compatibility. -/
def uint64ToBytes (x : UInt64) : ByteArray :=
  let arr : Array UInt8 := #[
    (x &&& 0xFF).toUInt8,
    ((x >>> 8) &&& 0xFF).toUInt8,
    ((x >>> 16) &&& 0xFF).toUInt8,
    ((x >>> 24) &&& 0xFF).toUInt8,
    ((x >>> 32) &&& 0xFF).toUInt8,
    ((x >>> 40) &&& 0xFF).toUInt8,
    ((x >>> 48) &&& 0xFF).toUInt8,
    ((x >>> 56) &&& 0xFF).toUInt8
  ]
  ByteArray.mk arr

/-- Compute encoded size of Tag0 (variable-length u64).
    If value < 128: 1 byte, else 1 + byteCount bytes.
    Must match Rust's Tag0::encoded_size(). -/
def tag0EncodedSize (value : UInt64) : Nat :=
  if value < 128 then 1 else 1 + value.byteCount.toNat

/-- Compute encoded size of Tag4 (4-bit flag + variable-length size).
    If size < 8: 1 byte, else 1 + byteCount bytes.
    Must match Rust's Tag4::encoded_size(). -/
def tag4EncodedSize (size : UInt64) : Nat :=
  if size < 8 then 1 else 1 + size.byteCount.toNat

/-- Compute the sharing hash for an expression node given its child hashes.
    This is the single source of truth for sharing hash computation.
    MUST match Rust's `hash_node` exactly for hash compatibility. -/
def computeNodeHash (e : Ixon.Expr) (childHashes : Array Address) : Address :=
  let buf := ByteArray.emptyWithCapacity 100
  let buf := match e with
    | .sort univIdx =>
      buf.push Ixon.Expr.FLAG_SORT |>.append (uint64ToBytes univIdx)
    | .var idx =>
      buf.push Ixon.Expr.FLAG_VAR |>.append (uint64ToBytes idx)
    | .ref refIdx univIndices =>
      let base := buf.push Ixon.Expr.FLAG_REF
        |>.append (uint64ToBytes refIdx)
        |>.append (uint64ToBytes univIndices.size.toUInt64)
      univIndices.foldl (fun buf idx => buf.append (uint64ToBytes idx)) base
    | .recur recIdx univIndices =>
      let base := buf.push Ixon.Expr.FLAG_RECUR
        |>.append (uint64ToBytes recIdx)
        |>.append (uint64ToBytes univIndices.size.toUInt64)
      univIndices.foldl (fun buf idx => buf.append (uint64ToBytes idx)) base
    | .prj typeRefIdx fieldIdx _ =>
      buf.push Ixon.Expr.FLAG_PRJ
        |>.append (uint64ToBytes typeRefIdx)
        |>.append (uint64ToBytes fieldIdx)
        |>.append childHashes[0]!.hash
    | .str refIdx =>
      buf.push Ixon.Expr.FLAG_STR |>.append (uint64ToBytes refIdx)
    | .nat refIdx =>
      buf.push Ixon.Expr.FLAG_NAT |>.append (uint64ToBytes refIdx)
    | .app _ _ =>
      buf.push Ixon.Expr.FLAG_APP
        |>.append childHashes[0]!.hash
        |>.append childHashes[1]!.hash
    | .lam _ _ =>
      buf.push Ixon.Expr.FLAG_LAM
        |>.append childHashes[0]!.hash
        |>.append childHashes[1]!.hash
    | .all _ _ =>
      buf.push Ixon.Expr.FLAG_ALL
        |>.append childHashes[0]!.hash
        |>.append childHashes[1]!.hash
    | .letE nonDep _ _ _ =>
      buf.push Ixon.Expr.FLAG_LET
        |>.push (if nonDep then 1 else 0)
        |>.append childHashes[0]!.hash
        |>.append childHashes[1]!.hash
        |>.append childHashes[2]!.hash
    | .share idx =>
      buf.push Ixon.Expr.FLAG_SHARE |>.append (uint64ToBytes idx)
  Address.blake3 buf

/-- Compute the sharing hash of an expression recursively (for testing).
    Uses computeNodeHash as the single source of truth. -/
partial def computeExprHash (e : Ixon.Expr) : Address :=
  let childHashes := match e with
    | .sort _ | .var _ | .ref _ _ | .recur _ _ | .str _ | .nat _ | .share _ => #[]
    | .prj _ _ val => #[computeExprHash val]
    | .app fun_ arg => #[computeExprHash fun_, computeExprHash arg]
    | .lam ty body | .all ty body => #[computeExprHash ty, computeExprHash body]
    | .letE _ ty val body => #[computeExprHash ty, computeExprHash val, computeExprHash body]
  computeNodeHash e childHashes

/-- Information about a subterm for sharing analysis. -/
structure SubtermInfo where
  /-- Base size of this node alone (Tag4 header, not including children) for Ixon format -/
  baseSize : Nat
  /-- Number of occurrences within this block -/
  usageCount : Nat
  /-- Canonical representative expression -/
  expr : Ixon.Expr
  /-- Hashes of child subterms (for topological ordering) -/
  children : Array Address
  deriving Inhabited

/-- Compute the base size of a node (Tag4 header size) for Ixon serialization. -/
def computeBaseSize (e : Ixon.Expr) : Nat :=
  match e with
  | .sort univIdx =>
    if univIdx < 8 then 1 else 1 + univIdx.byteCount.toNat
  | .var idx =>
    if idx < 8 then 1 else 1 + idx.byteCount.toNat
  | .ref refIdx univIndices =>
    -- Tag4 for size + Tag0 for refIdx + Tag0 for each universe index
    tag4EncodedSize univIndices.size.toUInt64
    + tag0EncodedSize refIdx
    + univIndices.foldl (fun acc idx => acc + tag0EncodedSize idx) 0
  | .recur recIdx univIndices =>
    -- Tag4 for size + Tag0 for recIdx + Tag0 for each universe index
    tag4EncodedSize univIndices.size.toUInt64
    + tag0EncodedSize recIdx
    + univIndices.foldl (fun acc idx => acc + tag0EncodedSize idx) 0
  | .prj typeRefIdx fieldIdx _ =>
    let tagSize := if fieldIdx < 8 then 1 else 1 + fieldIdx.byteCount.toNat
    let refIdxSize := if typeRefIdx < 128 then 1 else 1 + typeRefIdx.byteCount.toNat
    tagSize + refIdxSize
  | .str refIdx =>
    if refIdx < 8 then 1 else 1 + refIdx.byteCount.toNat
  | .nat refIdx =>
    if refIdx < 8 then 1 else 1 + refIdx.byteCount.toNat
  | .app _ _ => 1  -- telescope count >= 1
  | .lam _ _ => 1
  | .all _ _ => 1
  | .letE _ _ _ _ => 1  -- size encodes non_dep flag
  | .share idx =>
    if idx < 8 then 1 else 1 + idx.byteCount.toNat

/-- Get the memory address of an expression for identity-based caching.
    This is safe because we only use it within a single analysis pass
    where expressions are not modified. -/
@[inline]
def exprPtr (e : Ixon.Expr) : USize := unsafe ptrAddrUnsafe e

/-- State for the analysis monad. -/
structure AnalyzeState where
  /-- Map from content hash to subterm info -/
  infoMap : Std.HashMap Address SubtermInfo := {}
  /-- Map from expression pointer to its content hash (for O(1) lookup during rewrite) -/
  ptrToHash : Std.HashMap USize Address := {}
  /-- Topological order built during traversal (leaves first) -/
  topoOrder : Array Address := #[]
  deriving Inhabited

/-- Analysis monad. -/
abbrev AnalyzeM := StateM AnalyzeState

/-- Hash an expression and its children recursively, returning the content hash.
    Phase 1 of the efficient algorithm: builds DAG structure without computing usage counts.
    Uses computeNodeHash as the single source of truth for hash computation. -/
partial def hashAndAnalyze (e : Ixon.Expr) : AnalyzeM Address := do
  -- Check if we've already processed this exact pointer
  let st ← get
  let ptr := exprPtr e
  if let some hash := st.ptrToHash.get? ptr then
    -- Already processed - just return the hash (no subtree walk needed)
    return hash

  -- Recursively process children first and collect their hashes
  let childHashes ← match e with
    | .sort _ | .var _ | .ref _ _ | .recur _ _ | .str _ | .nat _ | .share _ =>
      pure #[]
    | .prj _ _ val =>
      let valHash ← hashAndAnalyze val
      pure #[valHash]
    | .app fun_ arg =>
      let funHash ← hashAndAnalyze fun_
      let argHash ← hashAndAnalyze arg
      pure #[funHash, argHash]
    | .lam ty body | .all ty body =>
      let tyHash ← hashAndAnalyze ty
      let bodyHash ← hashAndAnalyze body
      pure #[tyHash, bodyHash]
    | .letE _ ty val body =>
      let tyHash ← hashAndAnalyze ty
      let valHash ← hashAndAnalyze val
      let bodyHash ← hashAndAnalyze body
      pure #[tyHash, valHash, bodyHash]

  -- Compute the content hash using the single source of truth
  let hash := computeNodeHash e childHashes

  -- Update state: add to pointer cache
  let st ← get
  set { st with ptrToHash := st.ptrToHash.insert ptr hash }

  -- Add to info map if not already present (same content hash from different pointer)
  let st ← get
  if !st.infoMap.contains hash then
    let baseSize := computeBaseSize e
    set { st with
      infoMap := st.infoMap.insert hash {
        baseSize
        usageCount := 0  -- Will be computed in phase 2
        expr := e
        children := childHashes
      }
      topoOrder := st.topoOrder.push hash
    }

  return hash

/-- Result of sharing analysis. -/
structure AnalyzeResult where
  /-- Map from content hash to subterm info -/
  infoMap : Std.HashMap Address SubtermInfo
  /-- Map from expression pointer to content hash -/
  ptrToHash : Std.HashMap USize Address
  /-- Topological order (leaves first) - built during traversal -/
  topoOrder : Array Address

/-- Analyze expressions for sharing opportunities within a block.
    Uses a two-phase O(n) algorithm:
    1. Build DAG structure via post-order traversal with Merkle-tree hashing
    2. Propagate usage counts structurally from roots to leaves
    Returns AnalyzeResult with infoMap, ptrToHash, and topoOrder. -/
def analyzeBlock (exprs : Array Ixon.Expr) : AnalyzeResult := Id.run do
  -- Phase 1: Build DAG structure
  let mut st : AnalyzeState := {}
  for e in exprs do
    (_, st) := hashAndAnalyze e |>.run st

  -- Phase 2: Propagate usage counts structurally from roots to leaves
  -- This is O(n) total - no subtree walks needed

  -- Count root contributions
  let mut infoMap := st.infoMap
  for e in exprs do
    let ptr := exprPtr e
    if let some hash := st.ptrToHash.get? ptr then
      if let some info := infoMap.get? hash then
        infoMap := infoMap.insert hash { info with usageCount := info.usageCount + 1 }

  -- Propagate counts from roots to leaves (reverse topological order)
  for hash in st.topoOrder.reverse do
    if let some info := infoMap.get? hash then
      let count := info.usageCount
      for childHash in info.children do
        if let some childInfo := infoMap.get? childHash then
          infoMap := infoMap.insert childHash { childInfo with usageCount := childInfo.usageCount + count }

  { infoMap, ptrToHash := st.ptrToHash, topoOrder := st.topoOrder }

/-- Visit state for topological sort. -/
inductive VisitState where
  | inProgress
  | done

/-- Topological sort of subterms (leaves first, parents last).
    CRITICAL: Keys are sorted by hash bytes for deterministic output.
    This ensures Lean and Rust produce the same topological order. -/
partial def topologicalSort (infoMap : Std.HashMap Address SubtermInfo) : Array Address := Id.run do
  let mut state : Std.HashMap Address VisitState := {}
  let mut result : Array Address := #[]

  -- Sort keys deterministically by hash bytes (lexicographic comparison)
  let sortedKeys := infoMap.toArray.map (·.1) |>.qsort fun a b =>
    a.hash.data < b.hash.data

  for hash in sortedKeys do
    (state, result) := visit hash infoMap state result

  result
where
  visit (hash : Address) (infoMap : Std.HashMap Address SubtermInfo)
      (state : Std.HashMap Address VisitState) (result : Array Address)
      : Std.HashMap Address VisitState × Array Address := Id.run do
    let mut state := state
    let mut result := result

    match state.get? hash with
    | some .done => return (state, result)
    | some .inProgress => return (state, result)  -- Cycle (shouldn't happen)
    | none => pure ()

    state := state.insert hash .inProgress

    if let some info := infoMap.get? hash then
      for child in info.children do
        (state, result) := visit child infoMap state result

    state := state.insert hash .done
    result := result.push hash
    (state, result)

/-- Compute effective sizes for all subterms in topological order.
    Returns a map from hash to effective size (total serialized bytes). -/
def computeEffectiveSizes (infoMap : Std.HashMap Address SubtermInfo)
    (topoOrder : Array Address) : Std.HashMap Address Nat := Id.run do
  let mut sizes : Std.HashMap Address Nat := {}

  for hash in topoOrder do
    if let some info := infoMap.get? hash then
      let mut size := info.baseSize
      for childHash in info.children do
        size := size + sizes.getD childHash 0
      sizes := sizes.insert hash size

  sizes

/-- Compute the encoded size of a Share(idx) tag. -/
def shareRefSize (idx : Nat) : Nat :=
  let idx64 := idx.toUInt64
  if idx64 < 8 then 1 else 1 + idx64.byteCount.toNat

/-- Candidate for sharing: (hash, term_size, usage_count, potential_savings). -/
structure SharingCandidate where
  hash : Address
  termSize : Nat
  usageCount : Nat
  potential : _root_.Int  -- (N-1) * size - N (assuming ref_size=1)
  deriving Inhabited

/-- Decide which subterms to share based on profitability.

    Sharing is profitable when: (N - 1) * term_size > N * share_ref_size
    where N is usage count, term_size is effective size, and share_ref_size
    is the size of a Share(idx) reference at the current index.

    Returns a set of hashes to share. -/
def decideSharing (infoMap : Std.HashMap Address SubtermInfo)
    (topoOrder : Array Address) : Array Address := Id.run do
  let effectiveSizes := computeEffectiveSizes infoMap topoOrder

  -- Pre-filter and collect candidates
  let mut candidates : Array SharingCandidate := #[]
  for (hash, info) in infoMap do
    if info.usageCount < 2 then continue
    let termSize := effectiveSizes.getD hash 0
    let n := info.usageCount
    -- Potential savings assuming ref_size = 1 (minimum)
    let potential : _root_.Int := (n - 1 : _root_.Int) * termSize - n
    if potential > 0 then
      candidates := candidates.push { hash, termSize, usageCount := n, potential }

  -- Sort by decreasing gross benefit ((n-1) * size), with hash bytes as tie-breaker
  -- NOTE: Rust sorts by gross benefit, not net potential. Hash tie-breaker ensures determinism.
  candidates := candidates.qsort fun a b =>
    let grossA := (a.usageCount - 1) * a.termSize
    let grossB := (b.usageCount - 1) * b.termSize
    if grossA != grossB then grossA > grossB
    else a.hash.hash.data < b.hash.hash.data  -- lexicographic tie-breaker

  let mut shared : Array Address := #[]

  -- Process ALL candidates - don't break early!
  for cand in candidates do
    let nextIdx := shared.size
    let nextRefSize := shareRefSize nextIdx
    let n := cand.usageCount
    let savings : _root_.Int := (n - 1 : _root_.Int) * cand.termSize - n * nextRefSize
    if savings > 0 then
      shared := shared.push cand.hash

  shared

/-- Rewrite an expression tree to use Share(idx) references.
    Uses pointer-based caching like Rust: cache rewritten expressions by pointer,
    and only check hashToIdx if pointer is in ptrToHash (no hash recomputation). -/
partial def rewriteWithSharing (e : Ixon.Expr) (hashToIdx : Std.HashMap Address Nat)
    (ptrToHash : Std.HashMap USize Address)
    (cache : Std.HashMap USize Ixon.Expr) : Ixon.Expr × Std.HashMap USize Ixon.Expr :=
  let ptr := exprPtr e
  -- Check cache first
  match cache.get? ptr with
  | some cached => (cached, cache)
  | none =>
    -- Check if this expression should become a Share reference
    -- Only if pointer is in ptrToHash (was seen during analysis)
    match ptrToHash.get? ptr with
    | some hash =>
      match hashToIdx.get? hash with
      | some idx =>
        let result := Ixon.Expr.share idx.toUInt64
        (result, cache.insert ptr result)
      | none => rewriteChildren e hashToIdx ptrToHash cache ptr
    | none => rewriteChildren e hashToIdx ptrToHash cache ptr
where
  rewriteChildren (e : Ixon.Expr) (hashToIdx : Std.HashMap Address Nat)
      (ptrToHash : Std.HashMap USize Address)
      (cache : Std.HashMap USize Ixon.Expr) (ptr : USize)
      : Ixon.Expr × Std.HashMap USize Ixon.Expr :=
    -- Rewrite children, but reuse original if nothing changed (like Rust's Arc::ptr_eq optimization)
    let (result, cache') := match e with
      | .sort _ | .var _ | .ref _ _ | .recur _ _ | .str _ | .nat _ | .share _ =>
        (e, cache)
      | .prj typeRefIdx fieldIdx val =>
        let (val', cache') := rewriteWithSharing val hashToIdx ptrToHash cache
        -- Reuse original if child unchanged
        let result := if exprPtr val == exprPtr val' then e else .prj typeRefIdx fieldIdx val'
        (result, cache')
      | .app fun_ arg =>
        let (fun', cache') := rewriteWithSharing fun_ hashToIdx ptrToHash cache
        let (arg', cache'') := rewriteWithSharing arg hashToIdx ptrToHash cache'
        -- Reuse original if both children unchanged
        let result := if exprPtr fun_ == exprPtr fun' && exprPtr arg == exprPtr arg'
                      then e else .app fun' arg'
        (result, cache'')
      | .lam ty body =>
        let (ty', cache') := rewriteWithSharing ty hashToIdx ptrToHash cache
        let (body', cache'') := rewriteWithSharing body hashToIdx ptrToHash cache'
        let result := if exprPtr ty == exprPtr ty' && exprPtr body == exprPtr body'
                      then e else .lam ty' body'
        (result, cache'')
      | .all ty body =>
        let (ty', cache') := rewriteWithSharing ty hashToIdx ptrToHash cache
        let (body', cache'') := rewriteWithSharing body hashToIdx ptrToHash cache'
        let result := if exprPtr ty == exprPtr ty' && exprPtr body == exprPtr body'
                      then e else .all ty' body'
        (result, cache'')
      | .letE nonDep ty val body =>
        let (ty', cache') := rewriteWithSharing ty hashToIdx ptrToHash cache
        let (val', cache'') := rewriteWithSharing val hashToIdx ptrToHash cache'
        let (body', cache''') := rewriteWithSharing body hashToIdx ptrToHash cache''
        let result := if exprPtr ty == exprPtr ty' && exprPtr val == exprPtr val' && exprPtr body == exprPtr body'
                      then e else .letE nonDep ty' val' body'
        (result, cache''')
    (result, cache'.insert ptr result)

/-- Rewrite expressions to use Share(idx) references for shared subterms.

    Returns the rewritten expressions and the sharing vector.
    The sharing vector is sorted in topological order (leaves first). -/
def buildSharingVec (exprs : Array Ixon.Expr) (sharedHashes : Array Address)
    (infoMap : Std.HashMap Address SubtermInfo)
    (ptrToHash : Std.HashMap USize Address)
    (_topoOrder : Array Address) : Array Ixon.Expr × Array Ixon.Expr := Id.run do

  -- CRITICAL: Re-sort shared_hashes in topological order (leaves first).
  -- Use topologicalSort instead of filtering topoOrder from traversal.
  -- This ensures deterministic ordering by sorting keys by hash bytes.
  let topoOrder := topologicalSort infoMap
  let sharedSet : Std.HashMap Address Unit := sharedHashes.foldl (init := {}) fun s h => s.insert h ()
  let sharedInTopoOrder : Array Address := topoOrder.filter fun h => sharedSet.contains h

  -- Build sharing vector incrementally to avoid forward references
  let mut sharingVec : Array Ixon.Expr := #[]
  let mut hashToIdx : Std.HashMap Address Nat := {}

  for h in sharedInTopoOrder do
    if let some info := infoMap.get? h then
      -- Clear cache each iteration - hashToIdx changed, so cached rewrites are invalid
      let rewriteCache : Std.HashMap USize Ixon.Expr := {}
      let (rewritten, _) := rewriteWithSharing info.expr hashToIdx ptrToHash rewriteCache

      let idx := sharingVec.size
      sharingVec := sharingVec.push rewritten
      hashToIdx := hashToIdx.insert h idx

  -- Rewrite the root expressions (can use all Share indices)
  -- Fresh cache for root expressions since hashToIdx is now complete
  let mut rewriteCache : Std.HashMap USize Ixon.Expr := {}
  let mut rewrittenExprs : Array Ixon.Expr := #[]
  for e in exprs do
    let (rewritten, cache') := rewriteWithSharing e hashToIdx ptrToHash rewriteCache
    rewriteCache := cache'
    rewrittenExprs := rewrittenExprs.push rewritten

  (rewrittenExprs, sharingVec)

/-- Apply sharing analysis to a set of expressions.
    Returns (rewritten_exprs, sharing_vector). -/
def applySharing (exprs : Array Ixon.Expr) (dbg : Bool := false)
    : Array Ixon.Expr × Array Ixon.Expr := Id.run do
  let result := analyzeBlock exprs
  let sharedHashes := decideSharing result.infoMap result.topoOrder
  if dbg then
    dbg_trace s!"[Sharing] analyzed {exprs.size} exprs, found {result.infoMap.size} unique subterms, {sharedHashes.size} to share"
    dbg_trace s!"[Sharing] ptrToHash has {result.ptrToHash.size} entries"
    -- Debug: show usage counts for all subterms with usage >= 2
    let effectiveSizes := computeEffectiveSizes result.infoMap result.topoOrder
    for (hash, info) in result.infoMap do
      if info.usageCount >= 2 then
        let size := effectiveSizes.getD hash 0
        let potential : _root_.Int := (info.usageCount - 1 : _root_.Int) * size - info.usageCount
        dbg_trace s!"  usage={info.usageCount} size={size} potential={potential} expr={repr info.expr}"
  if sharedHashes.isEmpty then
    return (exprs, #[])
  else
    return buildSharingVec exprs sharedHashes result.infoMap result.ptrToHash result.topoOrder

end Ix.Sharing
