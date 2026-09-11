import Ix.Compiler.Ixon.Hash
import Ix.Compiler.Ixon.Sharing.Basic
import Ix.Compiler.Ixon.Work

/-!
# Deterministic Ixon-v2 sharing compression

This is the proof-facing, collision-safe port of ix's sharing policy. It keeps
structural `Expr` representatives as the analysis keys; BLAKE3 is used only for
deterministic ordering. Consequently a digest collision can affect an ordering
tie but can never identify two expressions or cause an unsound rewrite.

The policy is deliberately frozen in explicit stages:

1. enumerate every unfolded subterm and its occurrence count;
2. retain telescope-safe, serializer-profitable repeated candidates;
3. sort by ix's decreasing gross-benefit policy with deterministic tie-breaks;
4. put admitted representatives in leaves-first order and rewrite backward;
5. repeatedly delete any table entry that does not pay for itself under the
   real v2 expression serializer.

The final audit makes deletion-local profitability a checked postcondition and
absorbs telescope/header effects omitted by the greedy size model.
-/

namespace Ix.Compiler.Ixon.Sharing

/-- Stable external identifier for the compressor decisions frozen by the
parity corpus. Bump only with an intentional, documented policy change. -/
def compressorPolicyId : String := "compilatrix/ixon-v2-sharing/1"

/-- Exact upstream ix revision used for the v2 wire/address golden capture and
sharing-policy comparison. The literal capture artifacts live in `Tests.lean`;
this is the single source of truth for their revision. -/
def ixParityRevision : String :=
  "6f18ea907b78d06f7dc0917c43beb385561c35f4"

/-- External sharing policy recognized at ix catalog ingress.  It is pinned to
the exact upstream revision whose writer/checker artifacts form the parity
corpus, and is deliberately distinct from `compressorPolicyId`. -/
def ixonV2PolicyId : String := "ix/ixon-v2-sharing@" ++ ixParityRevision

/-! ## V2 Merkle ordering key -/

/-- Fixed-width little-endian scalar encoding used by ix's sharing Merkle key. -/
def uint64LE (x : UInt64) : ByteArray :=
  ByteArray.mk #[
    x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8,
    (x >>> 32).toUInt8, (x >>> 40).toUInt8, (x >>> 48).toUInt8,
    (x >>> 56).toUInt8]

/-- Node preimage for the internal sharing-order hash. Binder mode bytes are
included exactly as they appear in Ixon v2. -/
def nodeBytes (e : Expr) (childHashes : Array Address) : ByteArray :=
  let child (n : Nat) : ByteArray :=
    (childHashes[n]?.map (·.hash)).getD ByteArray.empty
  match e with
  | .sort u => (ByteArray.empty.push Expr.FLAG_SORT) ++ uint64LE u
  | .var i => (ByteArray.empty.push Expr.FLAG_VAR) ++ uint64LE i
  | .ref r us => us.foldl (fun b u => b ++ uint64LE u)
      ((ByteArray.empty.push Expr.FLAG_REF) ++ uint64LE r
        ++ uint64LE us.size.toUInt64)
  | .recur r us => us.foldl (fun b u => b ++ uint64LE u)
      ((ByteArray.empty.push Expr.FLAG_REC) ++ uint64LE r
        ++ uint64LE us.size.toUInt64)
  | .prj t f _ => (ByteArray.empty.push Expr.FLAG_PRJ) ++ uint64LE t
      ++ uint64LE f ++ child 0
  | .str r => (ByteArray.empty.push Expr.FLAG_STR) ++ uint64LE r
  | .nat r => (ByteArray.empty.push Expr.FLAG_NAT) ++ uint64LE r
  | .app _ _ => (ByteArray.empty.push Expr.FLAG_APP) ++ child 0 ++ child 1
  | .lam u _ _ => ((ByteArray.empty.push Expr.FLAG_LAM).push u.toBits)
      ++ child 0 ++ child 1
  | .all u o _ _ => ((ByteArray.empty.push Expr.FLAG_ALL).push
      (u.toBits ||| (o.toBits <<< 2))) ++ child 0 ++ child 1
  | .letE nd _ _ _ => ((ByteArray.empty.push Expr.FLAG_LET).push
      (if nd then 1 else 0)) ++ child 0 ++ child 1 ++ child 2
  | .share i => (ByteArray.empty.push Expr.FLAG_SHARE) ++ uint64LE i

/-- Structural Merkle hash used only as a deterministic ordering key. -/
def exprHash : Expr → Address
  | e@(.sort _) | e@(.var _) | e@(.ref _ _) | e@(.recur _ _)
  | e@(.str _) | e@(.nat _) | e@(.share _) =>
    .blake3 (nodeBytes e #[])
  | e@(.prj _ _ v) =>
    .blake3 (nodeBytes e #[exprHash v])
  | e@(.app f a) =>
    .blake3 (nodeBytes e #[exprHash f, exprHash a])
  | e@(.lam _ t b) =>
    .blake3 (nodeBytes e #[exprHash t, exprHash b])
  | e@(.all _ _ d c) =>
    .blake3 (nodeBytes e #[exprHash d, exprHash c])
  | e@(.letE _ t v b) =>
    .blake3 (nodeBytes e #[exprHash t, exprHash v, exprHash b])

/-! ## Structural occurrence analysis -/

structure Occurrence where
  expr : Expr
  /-- False at a position where replacing this occurrence would split an
  application or binder telescope. -/
  telescopeMaximal : Bool

/-- Enumerate occurrences in fixed constructor-field order. -/
def occurrences (atMaximalPosition : Bool) : Expr → List Occurrence
  | e@(.sort _) | e@(.var _) | e@(.ref _ _) | e@(.recur _ _)
  | e@(.str _) | e@(.nat _) | e@(.share _) =>
    [⟨e, atMaximalPosition⟩]
  | e@(.prj _ _ v) =>
    ⟨e, atMaximalPosition⟩ :: occurrences true v
  | e@(.app f a) =>
    ⟨e, atMaximalPosition⟩ :: (occurrences false f ++ occurrences true a)
  | e@(.lam _ t b) =>
    let bodyMax := match b with | .lam .. => false | _ => true
    ⟨e, atMaximalPosition⟩ :: (occurrences true t ++ occurrences bodyMax b)
  | e@(.all _ _ d c) =>
    let codMax := match c with | .all .. => false | _ => true
    ⟨e, atMaximalPosition⟩ :: (occurrences true d ++ occurrences codMax c)
  | e@(.letE _ t v b) =>
    ⟨e, atMaximalPosition⟩ ::
      (occurrences true t ++ occurrences true v ++ occurrences true b)

def blockOccurrences (exprs : Array Expr) : List Occurrence :=
  exprs.toList.flatMap (occurrences true)

def occurrenceCount (needle : Expr) (os : List Occurrence) : Nat :=
  os.countP fun o => o.expr == needle

/-- A candidate is telescope-safe only when every occurrence can be replaced
without splitting a maximal app/lam/all encoding run. -/
def telescopeSafe (needle : Expr) (os : List Occurrence) : Bool :=
  os.all fun o => if o.expr == needle then o.telescopeMaximal else true

/-- Direct children, in the same order used by `nodeBytes`. -/
def children : Expr → List Expr
  | .prj _ _ v => [v]
  | .app f a => [f, a]
  | .lam _ t b => [t, b]
  | .all _ _ d c => [d, c]
  | .letE _ t v b => [t, v, b]
  | _ => []

/-- Structural postorder. Concatenating this for hash-sorted keys and removing
duplicates implements ix's deterministic DFS topological order without maps. -/
def postorder : Expr → List Expr
  | e@(.sort _) | e@(.var _) | e@(.ref _ _) | e@(.recur _ _)
  | e@(.str _) | e@(.nat _) | e@(.share _) => [e]
  | e@(.prj _ _ v) => postorder v ++ [e]
  | e@(.app f a) => postorder f ++ postorder a ++ [e]
  | e@(.lam _ t b) => postorder t ++ postorder b ++ [e]
  | e@(.all _ _ d c) => postorder d ++ postorder c ++ [e]
  | e@(.letE _ t v b) => postorder t ++ postorder v ++ postorder b ++ [e]

structure Candidate where
  expr : Expr
  termSize : Nat
  usageCount : Nat
  digest : Address

def candidateGross (c : Candidate) : Nat :=
  (c.usageCount - 1) * c.termSize

/-- Digest order is collision-safe: structurally different equal digests fall
back to their canonical expression bytes. -/
def exprKeyLT (a b : Expr) : Bool :=
  let ah := exprHash a
  let bh := exprHash b
  if ah == bh then (ser a).data < (ser b).data
  else ah.hash.data < bh.hash.data

def candidateLT (a b : Candidate) : Bool :=
  let ga := candidateGross a
  let gb := candidateGross b
  if ga != gb then ga > gb
  else if a.digest == b.digest then (ser a.expr).data < (ser b.expr).data
  else a.digest.hash.data < b.digest.hash.data

/-- Exact v2 size of a `.share idx` reference. -/
def shareRefSize (idx : Nat) : Nat :=
  (ser (.share idx.toUInt64 : Expr)).size

/-- Per-node size model used by the pinned upstream compressor.  It predates
the flattened app/lam/all writer and therefore sums one AST-node header at a
time; reproducing that heuristic (including its overestimate on long spines)
is load-bearing for exact external table recognition. -/
def ixonV2NodeBaseSize : Expr → Nat
  | .sort u => (tag4Bytes ⟨Expr.FLAG_SORT, u⟩).size
  | .var i => (tag4Bytes ⟨Expr.FLAG_VAR, i⟩).size
  | .ref r us | .recur r us =>
    (tag4Bytes ⟨0, us.size.toUInt64⟩).size +
      (tag0Bytes ⟨r⟩).size +
      us.foldl (fun size u => size + (tag0Bytes ⟨u⟩).size) 0
  | .prj t f _ =>
    (tag4Bytes ⟨Expr.FLAG_PRJ, f⟩).size + (tag0Bytes ⟨t⟩).size
  | .str r => (tag4Bytes ⟨Expr.FLAG_STR, r⟩).size
  | .nat r => (tag4Bytes ⟨Expr.FLAG_NAT, r⟩).size
  | .app _ _ => 1
  | .lam _ _ _ | .all _ _ _ _ => 2
  | .letE _ _ _ _ => 1
  | .share i => (tag4Bytes ⟨Expr.FLAG_SHARE, i⟩).size

/-- Upstream's effective serialized-size estimate: node base size plus the
effective size of every structural child. -/
def ixonV2EffectiveSize : Expr → Nat
  | e@(.sort _) | e@(.var _) | e@(.ref _ _) | e@(.recur _ _)
  | e@(.str _) | e@(.nat _) | e@(.share _) => ixonV2NodeBaseSize e
  | e@(.prj _ _ v) => ixonV2NodeBaseSize e + ixonV2EffectiveSize v
  | e@(.app f a) =>
    ixonV2NodeBaseSize e + ixonV2EffectiveSize f + ixonV2EffectiveSize a
  | e@(.lam _ t b) | e@(.all _ _ t b) =>
    ixonV2NodeBaseSize e + ixonV2EffectiveSize t + ixonV2EffectiveSize b
  | e@(.letE _ t v b) =>
    ixonV2NodeBaseSize e + ixonV2EffectiveSize t +
      ixonV2EffectiveSize v + ixonV2EffectiveSize b

/-- Greedy ix-style admission on structural representatives. Candidate size is
the exact standalone v2 serialization; the final audit handles context effects. -/
def decideSharing (exprs : Array Expr) : Array Expr :=
  let os := blockOccurrences exprs
  let representatives := (os.map (·.expr)).eraseDups
  let candidates := representatives.foldl (init := #[]) fun out e =>
    let n := occurrenceCount e os
    let size := (ser e).size
    if n ≥ 2 && telescopeSafe e os && (n - 1) * size > n then
      out.push ⟨e, size, n, exprHash e⟩
    else out
  let candidates := candidates.qsort candidateLT
  candidates.foldl (init := #[]) fun selected cand =>
    if (cand.usageCount - 1) * cand.termSize >
        cand.usageCount * shareRefSize selected.size then
      selected.push cand.expr
    else selected

/-- Exact candidate admission used by the pinned upstream ixon-v2 compressor.
Unlike Ix.Compiler's local policy, it neither filters non-maximal telescope
suffixes nor runs the later exact-deletion audit.  The remaining machinery is
shared and collision-safe: structural equality, rather than a digest alone,
identifies representatives. -/
def decideIxonV2Sharing (exprs : Array Expr) : Array Expr :=
  let os := blockOccurrences exprs
  let representatives := (os.map (·.expr)).eraseDups
  let candidates := representatives.foldl (init := #[]) fun out e =>
    let n := occurrenceCount e os
    let size := ixonV2EffectiveSize e
    if n ≥ 2 && (n - 1) * size > n then
      out.push ⟨e, size, n, exprHash e⟩
    else out
  let candidates := candidates.qsort candidateLT
  candidates.foldl (init := #[]) fun selected cand =>
    if (cand.usageCount - 1) * cand.termSize >
        cand.usageCount * shareRefSize selected.size then
      selected.push cand.expr
    else selected

/-- Deterministic leaves-first order for the selected representatives. -/
def selectedTopological (exprs selected : Array Expr) : List Expr :=
  let all := ((blockOccurrences exprs).map (·.expr)).eraseDups.toArray
  let sortedKeys := all.qsort exprKeyLT
  let topo := (sortedKeys.toList.flatMap postorder).eraseDups
  topo.filter fun e => selected.contains e

/-! ## Backward rewriting -/

def findExprIndex? (needle : Expr) : List Expr → Option Nat
  | [] => none
  | e :: es =>
    if e = needle then some 0
    else (findExprIndex? needle es).map (· + 1)

theorem findExprIndex?_getElem? {needle : Expr} {shared : List Expr} {i : Nat}
    (h : findExprIndex? needle shared = some i) :
    shared[i]? = some needle := by
  induction shared generalizing i with
  | nil => simp [findExprIndex?] at h
  | cons e es ih =>
    simp only [findExprIndex?] at h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h
      subst i
      subst e
      simp
    · rename_i hne
      cases htail : findExprIndex? needle es with
      | none => simp [htail] at h
      | some j =>
        simp [htail] at h
        subst i
        rw [List.getElem?_cons_succ]
        exact ih htail

theorem findExprIndex?_lt {needle : Expr} {shared : List Expr} {i : Nat}
    (h : findExprIndex? needle shared = some i) :
    i < shared.length := by
  induction shared generalizing i with
  | nil => simp [findExprIndex?] at h
  | cons e es ih =>
    simp only [findExprIndex?] at h
    split at h
    · simp only [Option.some.injEq] at h
      have hi : i = 0 := h.symm
      subst i
      simp
    · cases htail : findExprIndex? needle es with
      | none => simp [htail] at h
      | some j =>
        simp [htail] at h
        subst i
        have := ih htail
        simp only [List.length_cons]
        omega

theorem substSharesList_found {needle : Expr} {shared : List Expr} {i : Nat}
    (hfind : findExprIndex? needle shared = some i)
    (hsize : shared.length < UInt64.size) :
    substSharesList shared (.share i.toUInt64) = needle := by
  have hi : i < shared.length := findExprIndex?_lt hfind
  have hi64 : i < UInt64.size := Nat.lt_trans hi hsize
  have hround : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt hi64
  simp only [substSharesList, hround]
  rw [findExprIndex?_getElem? hfind]
  rfl

/-- Rewrite every selected representative to its table index. Structural
equality, rather than its digest, authorizes replacement. -/
def rewriteWith (shared : List Expr) : Expr → Expr
  | e@(.sort _) | e@(.var _) | e@(.ref _ _) | e@(.recur _ _)
  | e@(.str _) | e@(.nat _) | e@(.share _) =>
    match findExprIndex? e shared with
    | some i => .share i.toUInt64
    | none => e
  | e@(.prj r f v) =>
    match findExprIndex? e shared with
    | some i => .share i.toUInt64
    | none => .prj r f (rewriteWith shared v)
  | e@(.app f a) =>
    match findExprIndex? e shared with
    | some i => .share i.toUInt64
    | none => .app (rewriteWith shared f) (rewriteWith shared a)
  | e@(.lam u t b) =>
    match findExprIndex? e shared with
    | some i => .share i.toUInt64
    | none => .lam u (rewriteWith shared t) (rewriteWith shared b)
  | e@(.all u o d c) =>
    match findExprIndex? e shared with
    | some i => .share i.toUInt64
    | none => .all u o (rewriteWith shared d) (rewriteWith shared c)
  | e@(.letE nd t v b) =>
    match findExprIndex? e shared with
    | some i => .share i.toUInt64
    | none => .letE nd (rewriteWith shared t) (rewriteWith shared v)
        (rewriteWith shared b)

/-- Rewriting against a representable structural table and immediately
substituting that same table is the identity on share-free expressions. -/
theorem substSharesList_rewriteWith (shared : List Expr) (e : Expr)
    (hsize : shared.length < UInt64.size)
    (hfree : shareFree e = true) :
    substSharesList shared (rewriteWith shared e) = e := by
  induction e with
  | sort u =>
    cases hfind : findExprIndex? (.sort u) shared with
    | none => simp [rewriteWith, hfind, substSharesList]
    | some i =>
      simp only [rewriteWith, hfind]
      exact substSharesList_found hfind hsize
  | var v =>
    cases hfind : findExprIndex? (.var v) shared with
    | none => simp [rewriteWith, hfind, substSharesList]
    | some i =>
      simp only [rewriteWith, hfind]
      exact substSharesList_found hfind hsize
  | ref r us =>
    cases hfind : findExprIndex? (.ref r us) shared with
    | none => simp [rewriteWith, hfind, substSharesList]
    | some i =>
      simp only [rewriteWith, hfind]
      exact substSharesList_found hfind hsize
  | recur r us =>
    cases hfind : findExprIndex? (.recur r us) shared with
    | none => simp [rewriteWith, hfind, substSharesList]
    | some i =>
      simp only [rewriteWith, hfind]
      exact substSharesList_found hfind hsize
  | str r =>
    cases hfind : findExprIndex? (.str r) shared with
    | none => simp [rewriteWith, hfind, substSharesList]
    | some i =>
      simp only [rewriteWith, hfind]
      exact substSharesList_found hfind hsize
  | nat r =>
    cases hfind : findExprIndex? (.nat r) shared with
    | none => simp [rewriteWith, hfind, substSharesList]
    | some i =>
      simp only [rewriteWith, hfind]
      exact substSharesList_found hfind hsize
  | share i => simp [shareFree] at hfree
  | prj r f v ih =>
    cases hfind : findExprIndex? (.prj r f v) shared with
    | some i =>
      simp only [rewriteWith, hfind]
      exact substSharesList_found hfind hsize
    | none =>
      simp only [shareFree] at hfree
      simp only [rewriteWith, hfind, substSharesList]
      rw [ih hfree]
  | app f a ihf iha =>
    cases hfind : findExprIndex? (.app f a) shared with
    | some i =>
      simp only [rewriteWith, hfind]
      exact substSharesList_found hfind hsize
    | none =>
      simp only [shareFree, Bool.and_eq_true] at hfree
      simp only [rewriteWith, hfind, substSharesList]
      rw [ihf hfree.1, iha hfree.2]
  | lam u t b iht ihb =>
    cases hfind : findExprIndex? (.lam u t b) shared with
    | some i =>
      simp only [rewriteWith, hfind]
      exact substSharesList_found hfind hsize
    | none =>
      simp only [shareFree, Bool.and_eq_true] at hfree
      simp only [rewriteWith, hfind, substSharesList]
      rw [iht hfree.1, ihb hfree.2]
  | all u o d c ihd ihc =>
    cases hfind : findExprIndex? (.all u o d c) shared with
    | some i =>
      simp only [rewriteWith, hfind]
      exact substSharesList_found hfind hsize
    | none =>
      simp only [shareFree, Bool.and_eq_true] at hfree
      simp only [rewriteWith, hfind, substSharesList]
      rw [ihd hfree.1, ihc hfree.2]
  | letE nd t v b iht ihv ihb =>
    cases hfind : findExprIndex? (.letE nd t v b) shared with
    | some i =>
      simp only [rewriteWith, hfind]
      exact substSharesList_found hfind hsize
    | none =>
      simp only [shareFree, Bool.and_eq_true] at hfree
      simp only [rewriteWith, hfind, substSharesList]
      rw [iht hfree.1.1, ihv hfree.1.2, ihb hfree.2]

/-- Build entries against only the already-emitted structural prefix. -/
def buildTable (prior : List Expr) : List Expr → List Expr
  | [] => []
  | e :: es => rewriteWith prior e :: buildTable (prior ++ [e]) es

theorem buildTable_length (prior rest : List Expr) :
    (buildTable prior rest).length = rest.length := by
  induction rest generalizing prior with
  | nil => simp [buildTable]
  | cons e es ih => simp [buildTable, ih]

/-- Incremental table construction inlines to the structural representatives
accumulated so far followed by the remaining representatives. -/
theorem inlineEntries_buildTable (prior rest : List Expr)
    (hsize : (prior ++ rest).length < UInt64.size)
    (hfree : ∀ e ∈ rest, shareFree e = true) :
    inlineEntries prior (buildTable prior rest) = prior ++ rest := by
  induction rest generalizing prior with
  | nil => simp [buildTable, inlineEntries]
  | cons e es ih =>
    have heFree : shareFree e = true := hfree e (by simp)
    have hprior : prior.length < UInt64.size := by
      have hp : prior.length ≤ (prior ++ e :: es).length := by simp
      omega
    have htailFree : ∀ x ∈ es, shareFree x = true := by
      intro x hx
      exact hfree x (by simp [hx])
    have htailSize : ((prior ++ [e]) ++ es).length < UInt64.size := by
      simpa [List.append_assoc] using hsize
    simp only [buildTable, inlineEntries]
    rw [substSharesList_rewriteWith prior e hprior heFree]
    rw [ih (prior ++ [e]) htailSize htailFree]
    simp [List.append_assoc]

/-- The fully inlined generated table is exactly its structural representative
list. -/
theorem inlineTable_buildTable (reps : List Expr)
    (hsize : reps.length < UInt64.size)
    (hfree : ∀ e ∈ reps, shareFree e = true) :
    inlineTable (buildTable [] reps).toArray = reps.toArray := by
  simp [inlineTable, inlineEntries_buildTable [] reps hsize hfree]

/-- A root rewritten against a generated table inlines to the original root. -/
theorem inlineExpr_rewriteWith_buildTable (reps : List Expr) (e : Expr)
    (hsize : reps.length < UInt64.size)
    (hreps : ∀ x ∈ reps, shareFree x = true)
    (he : shareFree e = true) :
    inlineExpr (buildTable [] reps).toArray (rewriteWith reps e) = e := by
  simp only [inlineExpr, substShares]
  rw [inlineTable_buildTable reps hsize hreps]
  simpa using substSharesList_rewriteWith reps e hsize he

structure Compression where
  bodies : Array Expr
  table : Array Expr
  deriving BEq, Repr

def Compression.expanded (c : Compression) : Array Expr :=
  c.bodies.map (inlineExpr c.table)

def compressionReps (exprs : Array Expr) : List Expr :=
  (selectedTopological exprs (decideSharing exprs)).filter fun e => shareFree e

theorem compressionReps_shareFree (exprs : Array Expr) :
    ∀ e ∈ compressionReps exprs, shareFree e = true := by
  intro e he
  exact (List.mem_filter.mp he).2

def buildCompression (exprs : Array Expr) : Compression :=
  let reps := compressionReps exprs
  { bodies := exprs.map (rewriteWith reps)
    table := (buildTable [] reps).toArray }

theorem buildCompression_table_size (exprs : Array Expr) :
    (buildCompression exprs).table.size = (compressionReps exprs).length := by
  simp [buildCompression, buildTable_length]

/-- Raw greedy construction (before the deletion audit) recovers every
share-free input when its generated indices fit the wire representation. -/
theorem inline_buildCompression (exprs : Array Expr)
    (hfree : exprs.all shareFree = true)
    (hindex : (buildCompression exprs).table.size < UInt64.size) :
    (buildCompression exprs).bodies.map
      (inlineExpr (buildCompression exprs).table) = exprs := by
  let reps := compressionReps exprs
  have hreps : ∀ e ∈ reps, shareFree e = true :=
    compressionReps_shareFree exprs
  have hrepsSize : reps.length < UInt64.size := by
    simpa [reps, buildCompression_table_size] using hindex
  apply Array.ext
  · simp [buildCompression]
  · intro i hiLeft hiRight
    have hi : i < exprs.size := by simpa [buildCompression] using hiLeft
    have heFree : shareFree exprs[i] = true :=
      (Array.all_eq_true.mp hfree) i hi
    simpa [buildCompression, reps] using
      inlineExpr_rewriteWith_buildTable reps exprs[i] hrepsSize hreps heFree

/-! ## Pinned upstream ixon-v2 construction -/

def ixonV2CompressionReps (exprs : Array Expr) : List Expr :=
  (selectedTopological exprs (decideIxonV2Sharing exprs)).filter shareFree

theorem ixonV2CompressionReps_shareFree (exprs : Array Expr) :
    ∀ e ∈ ixonV2CompressionReps exprs, shareFree e = true := by
  intro e he
  exact (List.mem_filter.mp he).2

/-- Deterministic image of the pinned upstream ixon-v2 sharing compressor.
This intentionally stops before Ix.Compiler's telescope filter and exact
deletion audit. -/
def buildIxonV2Compression (exprs : Array Expr) : Compression :=
  let reps := ixonV2CompressionReps exprs
  { bodies := exprs.map (rewriteWith reps)
    table := (buildTable [] reps).toArray }

theorem buildIxonV2Compression_table_size (exprs : Array Expr) :
    (buildIxonV2Compression exprs).table.size =
      (ixonV2CompressionReps exprs).length := by
  simp [buildIxonV2Compression, buildTable_length]

theorem inline_buildIxonV2Compression (exprs : Array Expr)
    (hfree : exprs.all shareFree = true)
    (hindex : (buildIxonV2Compression exprs).table.size < UInt64.size) :
    (buildIxonV2Compression exprs).expanded = exprs := by
  let reps := ixonV2CompressionReps exprs
  have hreps : ∀ e ∈ reps, shareFree e = true :=
    ixonV2CompressionReps_shareFree exprs
  have hrepsSize : reps.length < UInt64.size := by
    simpa [reps, buildIxonV2Compression_table_size] using hindex
  apply Array.ext
  · simp [Compression.expanded, buildIxonV2Compression]
  · intro i hiLeft hiRight
    have hi : i < exprs.size := by
      simpa [Compression.expanded, buildIxonV2Compression] using hiLeft
    have heFree : shareFree exprs[i] = true :=
      (Array.all_eq_true.mp hfree) i hi
    simpa [Compression.expanded, buildIxonV2Compression, reps] using
      inlineExpr_rewriteWith_buildTable reps exprs[i] hrepsSize hreps heFree

/-! ## Exact serializer-priced audit -/

/-- Replace a deleted index by its entry and shift every later index down. The
replacement can mention only earlier entries for a table produced above. -/
def eraseShare (idx : Nat) (replacement : Expr) : Expr → Expr
  | .share j =>
    if j.toNat == idx then replacement
    else if idx < j.toNat then .share (j.toNat - 1).toUInt64
    else .share j
  | .app f a => .app (eraseShare idx replacement f) (eraseShare idx replacement a)
  | .lam u t b => .lam u (eraseShare idx replacement t) (eraseShare idx replacement b)
  | .all u o d c =>
    .all u o (eraseShare idx replacement d) (eraseShare idx replacement c)
  | .letE nd t v b => .letE nd (eraseShare idx replacement t)
      (eraseShare idx replacement v) (eraseShare idx replacement b)
  | .prj r f v => .prj r f (eraseShare idx replacement v)
  | e => e

def eraseTableEntry (idx : Nat) (replacement : Expr) (table : List Expr) :
    List Expr :=
  (table.eraseIdx idx).map (eraseShare idx replacement)

def deleteEntry? (c : Compression) (idx : Nat) : Option Compression := do
  let replacement ← c.table[idx]?
  pure { bodies := c.bodies.map (eraseShare idx replacement)
         table := (eraseTableEntry idx replacement c.table.toList).toArray }

theorem deleteEntry_table_size {c smaller : Compression} {idx : Nat}
    (h : deleteEntry? c idx = some smaller) :
    smaller.table.size + 1 = c.table.size := by
  unfold deleteEntry? at h
  cases hget : c.table[idx]? with
  | none => simp [hget] at h
  | some replacement =>
    have hi : idx < c.table.size :=
      (Array.getElem?_eq_some_iff.mp hget).choose
    simp [hget] at h
    subst smaller
    simp [eraseTableEntry, List.length_eraseIdx_of_lt hi]
    omega

/-- Exact bytes controlled by sharing selection: the table count/header, every
table entry, and every body expression. Constant-info framing is unchanged. -/
def sharingPayloadSize (c : Compression) : Nat :=
  let tableHeader := (runPut (putTag0 ⟨c.table.size.toUInt64⟩)).size
  tableHeader
    + c.table.foldl (fun n e => n + (ser e).size) 0
    + c.bodies.foldl (fun n e => n + (ser e).size) 0

def firstNonPayingFrom (c : Compression) (currentSize : Nat) : Nat → Nat →
    Option Compression
  | 0, _ => none
  | fuel + 1, idx =>
    match deleteEntry? c idx with
    | some smaller =>
      if _hsemantic : smaller.expanded = c.expanded then
        if sharingPayloadSize smaller ≤ currentSize then some smaller
        else firstNonPayingFrom c currentSize fuel (idx + 1)
      else firstNonPayingFrom c currentSize fuel (idx + 1)
    | none => none

def firstNonPaying? (c : Compression) : Option Compression :=
  firstNonPayingFrom c (sharingPayloadSize c) c.table.size 0

theorem firstNonPayingFrom_expanded (c out : Compression)
    (currentSize fuel idx : Nat)
    (h : firstNonPayingFrom c currentSize fuel idx = some out) :
    out.expanded = c.expanded := by
  induction fuel generalizing idx with
  | zero => simp [firstNonPayingFrom] at h
  | succ fuel ih =>
    simp only [firstNonPayingFrom] at h
    cases hd : deleteEntry? c idx with
    | none => simp [hd] at h
    | some smaller =>
      simp only [hd] at h
      split at h
      · rename_i hsemantic
        split at h
        · simp only [Option.some.injEq] at h
          subst out
          exact hsemantic
        · exact ih (idx + 1) h
      · exact ih (idx + 1) h

theorem firstNonPayingFrom_table_size (c out : Compression)
    (currentSize fuel idx : Nat)
    (h : firstNonPayingFrom c currentSize fuel idx = some out) :
    out.table.size + 1 = c.table.size := by
  induction fuel generalizing idx with
  | zero => simp [firstNonPayingFrom] at h
  | succ fuel ih =>
    simp only [firstNonPayingFrom] at h
    cases hd : deleteEntry? c idx with
    | none => simp [hd] at h
    | some smaller =>
      simp only [hd] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst out
          exact deleteEntry_table_size hd
        · exact ih (idx + 1) h
      · exact ih (idx + 1) h

theorem firstNonPaying_expanded (c out : Compression)
    (h : firstNonPaying? c = some out) :
    out.expanded = c.expanded := by
  exact firstNonPayingFrom_expanded c out (sharingPayloadSize c)
    c.table.size 0 h

theorem firstNonPaying_table_size (c out : Compression)
    (h : firstNonPaying? c = some out) :
    out.table.size + 1 = c.table.size := by
  exact firstNonPayingFrom_table_size c out (sharingPayloadSize c)
    c.table.size 0 h

/-- Remove the first non-paying entry, then restart because deletion changes
indices and telescope contexts. At most the initial table size can be removed. -/
def auditFuel : Nat → Compression → Compression
  | 0, c => c
  | fuel + 1, c =>
    match firstNonPaying? c with
    | none => c
    | some smaller => auditFuel fuel smaller

def audit (c : Compression) : Compression :=
  auditFuel c.table.size c

theorem auditFuel_expanded (fuel : Nat) (c : Compression) :
    (auditFuel fuel c).expanded = c.expanded := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    simp only [auditFuel]
    cases hnext : firstNonPaying? c with
    | none => rfl
    | some smaller =>
      exact (ih smaller).trans (firstNonPaying_expanded c smaller hnext)

theorem auditFuel_table_size_le (fuel : Nat) (c : Compression) :
    (auditFuel fuel c).table.size ≤ c.table.size := by
  induction fuel generalizing c with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    simp only [auditFuel]
    cases hnext : firstNonPaying? c with
    | none => exact Nat.le_refl _
    | some smaller =>
      change (auditFuel fuel smaller).table.size ≤ c.table.size
      have hrec := ih smaller
      have hshrink := firstNonPaying_table_size c smaller hnext
      omega

theorem audit_expanded (c : Compression) :
    (audit c).expanded = c.expanded := by
  exact auditFuel_expanded c.table.size c

theorem audit_table_size_le (c : Compression) :
    (audit c).table.size ≤ c.table.size := by
  exact auditFuel_table_size_le c.table.size c

/-- The search has no remaining semantically validated non-paying deletion. -/
def auditFixpoint (c : Compression) : Bool :=
  (firstNonPaying? c).isNone

theorem auditFuel_firstNonPaying_none (fuel : Nat) (c : Compression)
    (hsize : c.table.size ≤ fuel) :
    firstNonPaying? (auditFuel fuel c) = none := by
  induction fuel generalizing c with
  | zero =>
    have hc : c.table.size = 0 := Nat.eq_zero_of_le_zero hsize
    simp [auditFuel, firstNonPaying?, hc, firstNonPayingFrom]
  | succ fuel ih =>
    simp only [auditFuel]
    cases hnext : firstNonPaying? c with
    | none => exact hnext
    | some smaller =>
      apply ih smaller
      have hshrink := firstNonPaying_table_size c smaller hnext
      omega

theorem audit_firstNonPaying_none (c : Compression) :
    firstNonPaying? (audit c) = none := by
  exact auditFuel_firstNonPaying_none c.table.size c (Nat.le_refl _)

theorem audit_fixpoint (c : Compression) :
    auditFixpoint (audit c) = true := by
  simp [auditFixpoint, audit_firstNonPaying_none]

/-- Strong diagnostic for well-formed tables: every syntactically available
single-entry deletion increases bytes. The certified audit postcondition below
additionally requires that the deletion preserve expansion. -/
def allEntriesPay (c : Compression) : Bool :=
  (List.range c.table.size).all fun i =>
    match deleteEntry? c i with
    | some smaller => sharingPayloadSize c < sharingPayloadSize smaller
    | none => false

/-- Exact deletion-local optimality: no single deletion that validates as
semantics-preserving is non-paying. -/
def deletionLocalOptimal (c : Compression) : Bool :=
  auditFixpoint c

theorem deletionLocalOptimal_audit (c : Compression) :
    deletionLocalOptimal (audit c) = true := by
  exact audit_fixpoint c

def compressUnchecked (exprs : Array Expr) : Compression :=
  audit (buildCompression exprs)

theorem compressUnchecked_table_size_le (exprs : Array Expr) :
    (compressUnchecked exprs).table.size ≤ (buildCompression exprs).table.size := by
  exact audit_table_size_le (buildCompression exprs)

theorem deletionLocalOptimal_compressUnchecked (exprs : Array Expr) :
    deletionLocalOptimal (compressUnchecked exprs) = true := by
  exact deletionLocalOptimal_audit (buildCompression exprs)

/-- Full raw mechanism recovery: the exact-byte audit preserves the recovery
proved for the greedy table builder. -/
theorem inline_compressUnchecked (input : Array Expr)
    (hfree : input.all shareFree = true)
    (hindex : (buildCompression input).table.size < UInt64.size) :
    (compressUnchecked input).expanded = input := by
  exact (audit_expanded (buildCompression input)).trans
    (inline_buildCompression input hfree hindex)

/-! ## Certified totalization -/

/-- Semantics-preserving fallback used only if the heuristic violates layer 1.
It is deliberately visible in the specification and parity tests. -/
def identityCompression (input : Array Expr) : Compression :=
  { bodies := input, table := #[] }

theorem identityCompression_expanded (input : Array Expr)
    (hfree : input.all shareFree = true) :
    (identityCompression input).expanded = input := by
  apply Array.ext
  · simp [identityCompression, Compression.expanded]
  · intro i hiLeft hiRight
    have hi : i < input.size := by
      simpa [identityCompression, Compression.expanded] using hiLeft
    have heFree := (Array.all_eq_true.mp hfree) i hi
    simpa [identityCompression, Compression.expanded] using
      inlineExpr_eq_self_of_shareFree #[] input[i] heFree

/-- Retain the heuristic output when it satisfies layer 1; otherwise use the
identity representation. This is a correctness fallback, not a policy change
on accepted heuristic outputs. -/
def certifyLayer1 (input : Array Expr) (candidate : Compression) : Compression :=
  if _h : layer1WF candidate.table candidate.bodies = true then candidate
  else identityCompression input

def compressCertified (input : Array Expr) : Compression :=
  certifyLayer1 input (compressUnchecked input)

theorem layer1_compressCertified (input : Array Expr)
    (hfree : input.all shareFree = true) :
    layer1WF (compressCertified input).table
      (compressCertified input).bodies = true := by
  unfold compressCertified certifyLayer1
  split
  · assumption
  · exact layer1WF_empty_of_shareFree input hfree

theorem inline_compressCertified (input : Array Expr)
    (hfree : input.all shareFree = true)
    (hindex : (buildCompression input).table.size < UInt64.size) :
    (compressCertified input).expanded = input := by
  unfold compressCertified certifyLayer1
  split
  · exact inline_compressUnchecked input hfree hindex
  · exact identityCompression_expanded input hfree

theorem deletionLocalOptimal_identityCompression (input : Array Expr) :
    deletionLocalOptimal (identityCompression input) = true := by
  rfl

theorem deletionLocalOptimal_compressCertified (input : Array Expr) :
    deletionLocalOptimal (compressCertified input) = true := by
  unfold compressCertified certifyLayer1
  split
  · exact deletionLocalOptimal_compressUnchecked input
  · exact deletionLocalOptimal_identityCompression input

theorem compressCertified_table_size_le (input : Array Expr) :
    (compressCertified input).table.size ≤ (buildCompression input).table.size := by
  unfold compressCertified certifyLayer1
  split
  · exact compressUnchecked_table_size_le input
  · simp [identityCompression]

/-! ## Exact pinned ixon-v2 recognizer -/

/-- Reproduce the pinned upstream ixon-v2 compressor and certify the
safety-critical table invariant plus exact inline recovery.  This is an
external-format recognizer, not Ix.Compiler's local compressor. -/
def compressIxonV2? (exprs : Array Expr) : Option Compression :=
  if !exprs.all shareFree then none
  else
    let out := buildIxonV2Compression exprs
    if _hstructural : structuralWF out.table out.bodies = true then
      if _hindex : out.table.size < UInt64.size then
        if _hinline : out.expanded = exprs then some out
        else none
      else none
    else none

/-- Exact-image predicate for external constants written by the pinned
upstream ixon-v2 compressor. -/
def ixonV2Canonical (bodies table : Array Expr) : Bool :=
  if !structuralWF table bodies then false
  else
    let expanded := bodies.map (inlineExpr table)
    match compressIxonV2? expanded with
    | some out => decide (out.bodies = bodies ∧ out.table = table)
    | none => false

theorem inline_compressIxonV2 (input : Array Expr) (out : Compression)
    (h : compressIxonV2? input = some out) :
    out.expanded = input := by
  unfold compressIxonV2? at h
  split at h <;> simp_all
  rcases h with ⟨_, _, hinline, rfl⟩
  exact hinline

theorem structural_compressIxonV2 (input : Array Expr) (out : Compression)
    (h : compressIxonV2? input = some out) :
    structuralWF out.table out.bodies = true := by
  unfold compressIxonV2? at h
  split at h <;> simp_all
  rcases h with ⟨hstructural, _, _, rfl⟩
  exact hstructural

theorem ixonV2Canonical_compress (input : Array Expr) (out : Compression)
    (h : compressIxonV2? input = some out) :
    ixonV2Canonical out.bodies out.table = true := by
  have hstructural := structural_compressIxonV2 input out h
  have hinline := inline_compressIxonV2 input out h
  change out.bodies.map (inlineExpr out.table) = input at hinline
  simp [ixonV2Canonical, hstructural, hinline, h]

/-- Public compressor. Share-freedom is enforced at the API boundary, and the
result is accepted only when layer 1, the exact audit postcondition, and exact
inline recovery all hold. The last check is stated as propositional equality so
its successful branch carries the proof consumed below. -/
def compress? (exprs : Array Expr) : Option Compression :=
  if !exprs.all shareFree then none
  else
    let out := compressCertified exprs
    if _hlayer : layer1WF out.table out.bodies = true then
      if _hoptimal : deletionLocalOptimal out = true then
        if _hindex : out.table.size < UInt64.size then
          if _hinline : out.bodies.map (inlineExpr out.table) = exprs then some out
          else none
        else none
      else none
    else none

/-- Layer 2: exact recompression image. This is intentionally more expensive
than decoder-enforced layer 1 and belongs at content-address/store ingestion. -/
def canonical (bodies table : Array Expr) : Bool :=
  if !layer1WF table bodies then false
  else
    let expanded := bodies.map (inlineExpr table)
    match compress? expanded with
    | some out => decide (out.bodies = bodies ∧ out.table = table)
    | none => false

/-! ## Resource-bounded executable boundaries -/

/-- Inclusive structural limits for content-address canonicalization.  The
compressor cap is intentionally much tighter than the wire-size cap: the
frozen collision-safe policy performs repeated structural comparisons and an
exact deletion audit. -/
structure ResourceLimits where
  maxLayer1NodeVisits : Nat := 16 * 1024 * 1024
  maxCompressionInputUnits : Nat := 4096
  deriving BEq, DecidableEq, Repr

def defaultResourceLimits : ResourceLimits := {}

/-- Run the public compressor only after a linear input-size preflight. -/
def compressWithLimit (maxInputUnits : Nat) (exprs : Array Expr) :
    Except Work.Exceeded (Option Compression) :=
  match Work.ensure .compressionInputUnits (Work.exprArrayUnits exprs)
      maxInputUnits with
  | .error exceeded => .error exceeded
  | .ok _ => .ok (compress? exprs)

/-- Resource-bounded layer-2 recognizer.  The fully inlined size is computed
from the backward table without allocating the expanded expression forest;
only an admitted input reaches `inlineExpr` and the compressor. -/
def canonicalWith (limits : ResourceLimits) (bodies table : Array Expr) :
    Except Work.Exceeded Bool :=
  match Work.ensure .layer1NodeVisits (Work.layer1NodeVisits table bodies)
      limits.maxLayer1NodeVisits with
  | .error exceeded => .error exceeded
  | .ok _ =>
    match Work.expandedUnits? table bodies with
    | none => .ok false
    | some units =>
      match Work.ensure .compressionInputUnits units
          limits.maxCompressionInputUnits with
      | .error exceeded => .error exceeded
      | .ok _ => .ok (canonical bodies table)

/-- Resource-bounded exact-image recognizer for the pinned upstream ixon-v2
compressor.  It uses the same conservative expansion and compressor-input
budgets as the local recognizer. -/
def ixonV2CanonicalWith (limits : ResourceLimits)
    (bodies table : Array Expr) : Except Work.Exceeded Bool :=
  match Work.ensure .layer1NodeVisits (Work.layer1NodeVisits table bodies)
      limits.maxLayer1NodeVisits with
  | .error exceeded => .error exceeded
  | .ok _ =>
    match Work.expandedUnits? table bodies with
    | none => .ok false
    | some units =>
      match Work.ensure .compressionInputUnits units
          limits.maxCompressionInputUnits with
      | .error exceeded => .error exceeded
      | .ok _ => .ok (ixonV2Canonical bodies table)

def canonicalBounded (bodies table : Array Expr) :
    Except Work.Exceeded Bool :=
  canonicalWith defaultResourceLimits bodies table

def ixonV2CanonicalBounded (bodies table : Array Expr) :
    Except Work.Exceeded Bool :=
  ixonV2CanonicalWith defaultResourceLimits bodies table

theorem compressWithLimit_sound {maxInputUnits : Nat} {exprs : Array Expr}
    {out : Option Compression}
    (h : compressWithLimit maxInputUnits exprs = .ok out) :
    compress? exprs = out := by
  unfold compressWithLimit at h
  cases hbudget : Work.ensure .compressionInputUnits
      (Work.exprArrayUnits exprs) maxInputUnits with
  | error exceeded => simp_all
  | ok result =>
    cases result
    simp_all

theorem canonicalWith_true {limits : ResourceLimits}
    {bodies table : Array Expr}
    (h : canonicalWith limits bodies table = .ok true) :
    canonical bodies table = true := by
  unfold canonicalWith at h
  cases hlayer : Work.ensure .layer1NodeVisits
      (Work.layer1NodeVisits table bodies) limits.maxLayer1NodeVisits with
  | error exceeded => simp_all
  | ok layerResult =>
    cases layerResult
    cases hexpanded : Work.expandedUnits? table bodies with
    | none => simp_all
    | some units =>
      cases hcompression : Work.ensure .compressionInputUnits units
          limits.maxCompressionInputUnits with
      | error exceeded => simp_all
      | ok compressionResult =>
        cases compressionResult
        simp_all

theorem ixonV2CanonicalWith_true {limits : ResourceLimits}
    {bodies table : Array Expr}
    (h : ixonV2CanonicalWith limits bodies table = .ok true) :
    ixonV2Canonical bodies table = true := by
  unfold ixonV2CanonicalWith at h
  cases hlayer : Work.ensure .layer1NodeVisits
      (Work.layer1NodeVisits table bodies) limits.maxLayer1NodeVisits with
  | error exceeded => simp_all
  | ok layerResult =>
    cases layerResult
    cases hexpanded : Work.expandedUnits? table bodies with
    | none => simp_all
    | some units =>
      cases hcompression : Work.ensure .compressionInputUnits units
          limits.maxCompressionInputUnits with
      | error exceeded => simp_all
      | ok compressionResult =>
        cases compressionResult
        simp_all

/-! ## Executable proof contracts for S4 -/

def InlineCompressLaw : Prop :=
  ∀ input out, compress? input = some out →
    out.bodies.map (inlineExpr out.table) = input

def CompressCanonicalLaw : Prop :=
  ∀ input out, compress? input = some out → canonical out.bodies out.table = true

/-- Totality contract: the checked boundary never rejects a feasible
share-free input. The certified identity fallback makes this provable even if
the optimization heuristic violates an internal invariant. -/
def CompressTotalLaw : Prop :=
  ∀ input, input.all shareFree = true →
    (buildCompression input).table.size < UInt64.size →
    ∃ out, compress? input = some out

/-- The central raw-mechanism lemma from which `CompressTotalLaw`'s recovery
gate follows; unlike `InlineCompressLaw`, this speaks before validation. -/
def UncheckedInlineLaw : Prop :=
  ∀ input, input.all shareFree = true →
    (buildCompression input).table.size < UInt64.size →
    (compressUnchecked input).expanded = input

/-- The public checked compressor is semantically sound: every successful
result inlines exactly to its share-free input. -/
theorem inline_compress (input : Array Expr) (out : Compression)
    (h : compress? input = some out) :
    out.bodies.map (inlineExpr out.table) = input := by
  unfold compress? at h
  split at h <;> simp_all
  rcases h with ⟨_, _, _, hinline, rfl⟩
  exact hinline

/-- Every successful public result satisfies decoder-enforced layer 1. -/
theorem layer1_compress (input : Array Expr) (out : Compression)
    (h : compress? input = some out) :
    layer1WF out.table out.bodies = true := by
  unfold compress? at h
  split at h <;> simp_all
  rcases h with ⟨hlayer, _, _, _, rfl⟩
  exact hlayer

/-- Every successful public result is a fixpoint of the exact deletion audit. -/
theorem deletionLocalOptimal_compress (input : Array Expr) (out : Compression)
    (h : compress? input = some out) :
    deletionLocalOptimal out = true := by
  unfold compress? at h
  split at h <;> simp_all
  rcases h with ⟨_, hoptimal, _, _, rfl⟩
  exact hoptimal

/-- Every successful table index is representable by the wire's `UInt64`. -/
theorem indexable_compress (input : Array Expr) (out : Compression)
    (h : compress? input = some out) :
    out.table.size < UInt64.size := by
  unfold compress? at h
  split at h <;> simp_all
  rcases h with ⟨_, _, hindex, _, rfl⟩
  exact hindex

/-- Successful compression is idempotent under the exact layer-2 recognizer. -/
theorem canonical_compress (input : Array Expr) (out : Compression)
    (h : compress? input = some out) :
    canonical out.bodies out.table = true := by
  have hlayer := layer1_compress input out h
  have hinline := inline_compress input out h
  simp [canonical, hlayer, hinline, h]

theorem inlineCompressLaw : InlineCompressLaw := by
  intro input out h
  exact inline_compress input out h

theorem compressCanonicalLaw : CompressCanonicalLaw := by
  intro input out h
  exact canonical_compress input out h

theorem uncheckedInlineLaw : UncheckedInlineLaw := by
  intro input hfree hindex
  exact inline_compressUnchecked input hfree hindex

/-- Every feasible share-free input is accepted. The heuristic result is used
when layer 1 validates; the proved identity fallback makes correctness total
without hiding parity failures in the runtime corpus. -/
theorem compressTotalLaw : CompressTotalLaw := by
  intro input hfree hbuildIndex
  refine ⟨compressCertified input, ?_⟩
  have hlayer := layer1_compressCertified input hfree
  have hoptimal := deletionLocalOptimal_compressCertified input
  have hindex : (compressCertified input).table.size < UInt64.size :=
    Nat.lt_of_le_of_lt (compressCertified_table_size_le input) hbuildIndex
  have hinline := inline_compressCertified input hfree hbuildIndex
  unfold compress?
  simp [hfree, hlayer, hoptimal, hindex, Compression.expanded] at hinline ⊢
  exact hinline

/-! Pure guards for the rewriting/audit substrate. BLAKE3-dependent compressor
fixtures run in the compiled `Tests.lean` executable. -/

#guard uint64LE 0x0102030405060708 == ByteArray.mk #[8, 7, 6, 5, 4, 3, 2, 1]
#guard nodeBytes (.lam .many (.sort 0) (.var 0)) #[] !=
  nodeBytes (.lam .linear (.sort 0) (.var 0)) #[]
#guard nodeBytes (.all .many .shared (.sort 0) (.var 0)) #[] !=
  nodeBytes (.all .many .unique (.sort 0) (.var 0)) #[]

private def auditFixture : Compression :=
  { bodies := #[.app (.share 0) (.share 0)]
    table := #[.sort 0] }

#guard deleteEntry? auditFixture 0 == some
  { bodies := #[.app (.sort 0) (.sort 0)], table := #[] }
#guard !deletionLocalOptimal auditFixture
#guard deletionLocalOptimal (audit auditFixture)

end Ix.Compiler.Ixon.Sharing
