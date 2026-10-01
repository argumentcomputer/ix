import Ix.CompileM

/-!
# Sharing corpus study

Loads a serialized `Ixon.Env` (`.ixe`) and, for every stored constant:

1. Expands the stored sharing table left to right. Entry `i` may reference
   only entries `j < i`; each `Share j` is replaced by the *same* in-memory
   expansion of entry `j`, so repeated indices share one subtree and the
   expanded roots form a DAG whose size is linear in the stored bytes.
   The ordered roots come from `Ix.CompileM.constantInfoRootExprs`.
2. Rebuilds the constant with the production route
   (`Ix.CompileM.buildConstantWithSharing` under `compilerSharingLimits` on the
   expanded roots, i.e. the canonical tiered construction) and checks that
   `Ixon.serConstant` reproduces the stored bytes exactly. It also checks the
   plain decode/encode roundtrip.
3. Hash-conses the expanded roots with `analyzeBlock` (blake3 Merkle hashes;
   hash equality is treated as structural equality; a harness-local copy of the
   analysis the removed heuristic used) and measures, per constant:
   * `N`: distinct subterms, leaves included;
   * `occ(t)`: `SubtermInfo.usageCount`, i.e. structural occurrences in the
     fully expanded roots, counted through every DAG edge with multiplicity
     plus one per root occurrence (`countRootUsages` +
     `propagateUsageCounts`);
   * `size(t)`: the standalone unshared `putExpr` length of `t`, computed
     compositionally on the DAG with the App/Lam/All telescope rules;
   * candidates after R1/R2 (`occ ≥ 2 ∧ size > 1`) and those with size > 2
     and > 3;
   * the unshared complete-Constant size, the stored and canonical table
     sizes and byte lengths; the longest App/Lam/All telescope.
4. Validates the compositional unshared size against `serConstant` of the
   actual unshared constant whenever the unshared root bytes are at most
   `--validate-max` (so no exponential tree is ever serialized).
5. Checks `usageCount` against a brute-force walk of the expanded roots as
   trees whenever the unshared root bytes are at most `--occ-check-max`.
6. Builds the "maximal structural sharing" (MSS) encoding (see `mssBuild`),
   serializes it with `serConstant`, decodes and expands it again and checks
   the expanded roots equal the original ones exactly, and compares it with
   the canonical encoding. The `docs/sharing-minimum.md` §2 witnesses are run
   through the same path at startup.

With `--meta` it instead runs the metadata study (see `metaStudy`).

```
lake exe sharing-study <corpus.ixe> [--md <path>] [--csv <path>]
                       [--limit <n>] [--validate-max <bytes>]
                       [--occ-check-max <bytes>] [--progress <n>]
                       [--meta] [--meta-crosscheck]
```
-/

namespace Benchmarks.SharingStudy

open Ixon (Expr Constant ConstantInfo MutConst)

/-! ## Hash-consing analysis

Harness-local copy of the structural analysis the removed heuristic sharing
pass used: blake3 Merkle hashes over the canonical node headers, a
pointer-to-hash cache, a leaves-first traversal order and structural
occurrence counts. Production sharing is the canonical tiered construction
(`Ix.Sharing.Exact`); nothing here is on the compiler route. -/

/-- Canonical scalar/contract bytes of one node, without its children. -/
def putNodeHeader : Expr → Ixon.PutM Unit
  | e@(.sort _) | e@(.var _) | e@(.ref ..) | e@(.recur ..) |
      e@(.str _) | e@(.nat _) | e@(.share _) => Ixon.putExpr e
  | .prj idx field _ => do
    Ixon.putTagN 4 Ixon.Expr.FLAG_PRJ field
    Ixon.putTagN 0 0 idx
  | .app .. => Ixon.putTagN 4 Ixon.Expr.FLAG_APP 1
  | .lam contract .. => do
    Ixon.putTagN 4 Ixon.Expr.FLAG_LAM 1
    Ixon.putBinderContract contract
  | .all contract result .. => do
    Ixon.putTagN 4 Ixon.Expr.FLAG_ALL 1
    Ixon.putU8 (Ixon.packAllContract contract result)
  | .letE contract .. => do
    Ixon.putTagN 4 Ixon.Expr.FLAG_LET contract.flags
    Ixon.putBinderContract contract.binder

def computeNodeHash (e : Expr) (childHashes : Array Address) : Address :=
  Address.blake3 <| childHashes.foldl (fun bytes h => bytes ++ h.hash)
    (Ixon.runPut (putNodeHeader e))

/-- One hash-consed subterm. -/
structure SubtermInfo where
  /-- Node header bytes (`putNodeHeader`), children excluded. -/
  baseSize : Nat
  /-- Structural occurrences in the fully expanded roots. -/
  usageCount : Nat
  /-- First representative seen. -/
  expr : Expr
  children : Array Address
  deriving Inhabited

@[inline] def exprPtr (e : Expr) : USize := Ix.Sharing.Exact.exprPtr e

structure AnalyzeState where
  infoMap : Std.HashMap Address SubtermInfo := {}
  ptrToHash : Std.HashMap USize Address := {}
  /-- Leaves-first traversal order of the distinct subterms. -/
  topoOrder : Array Address := #[]
  deriving Inhabited

abbrev AnalyzeM := StateM AnalyzeState

def recordAnalyzedNode (e : Expr) (childHashes : Array Address) : AnalyzeM Address := do
  let hash := computeNodeHash e childHashes
  modify fun st => { st with ptrToHash := st.ptrToHash.insert (exprPtr e) hash }
  let st ← get
  if !st.infoMap.contains hash then
    set { st with
      infoMap := st.infoMap.insert hash
        { baseSize := (Ixon.runPut (putNodeHeader e)).size, usageCount := 0,
          expr := e, children := childHashes }
      topoOrder := st.topoOrder.push hash }
  return hash

partial def hashAndAnalyze (e : Expr) : AnalyzeM Address := do
  if let some hash := (← get).ptrToHash.get? (exprPtr e) then return hash
  let childHashes ← match e with
    | .sort _ | .var _ | .ref _ _ | .recur _ _ | .str _ | .nat _ | .share _ => pure #[]
    | .prj _ _ val => do pure #[← hashAndAnalyze val]
    | .app f a => do pure #[← hashAndAnalyze f, ← hashAndAnalyze a]
    | .lam _ ty body | .all _ _ ty body => do
      pure #[← hashAndAnalyze ty, ← hashAndAnalyze body]
    | .letE _ ty val body => do
      pure #[← hashAndAnalyze ty, ← hashAndAnalyze val, ← hashAndAnalyze body]
  recordAnalyzedNode e childHashes

structure AnalyzeResult where
  infoMap : Std.HashMap Address SubtermInfo
  ptrToHash : Std.HashMap USize Address
  topoOrder : Array Address

def addUsage (infoMap : Std.HashMap Address SubtermInfo) (hash : Address) (count : Nat) :
    Std.HashMap Address SubtermInfo :=
  match infoMap.get? hash with
  | some info => infoMap.insert hash { info with usageCount := info.usageCount + count }
  | none => infoMap

/-- One use per root occurrence. -/
def countRootUsages (exprs : Array Expr) (ptrToHash : Std.HashMap USize Address)
    (infoMap : Std.HashMap Address SubtermInfo) : Std.HashMap Address SubtermInfo :=
  exprs.foldl (init := infoMap) fun infoMap expr =>
    match ptrToHash.get? (exprPtr expr) with
    | some hash => addUsage infoMap hash 1
    | none => infoMap

/-- Push each subterm's count to its children, parents before children. -/
def propagateUsageCounts (topoOrder : Array Address)
    (infoMap : Std.HashMap Address SubtermInfo) : Std.HashMap Address SubtermInfo :=
  topoOrder.reverse.foldl (init := infoMap) fun infoMap hash =>
    match infoMap.get? hash with
    | some info =>
      info.children.foldl (init := infoMap) fun infoMap c => addUsage infoMap c info.usageCount
    | none => infoMap

/-- Hash-cons `exprs` (left to right) and count structural occurrences. -/
def analyzeBlock (exprs : Array Expr) : AnalyzeResult :=
  let st := exprs.foldl (init := ({} : AnalyzeState)) fun st e => ((hashAndAnalyze e).run st).2
  let infoMap := countRootUsages exprs st.ptrToHash st.infoMap
  let infoMap := propagateUsageCounts st.topoOrder infoMap
  { infoMap, ptrToHash := st.ptrToHash, topoOrder := st.topoOrder }

/-- Replace every occurrence of a stored subterm by its `Share`. -/
partial def rewriteWithSharing (e : Expr) (hashToIdx : Std.HashMap Address Nat)
    (ptrToHash : Std.HashMap USize Address) : Expr :=
  match (ptrToHash.get? (exprPtr e)).bind (hashToIdx.get? ·) with
  | some idx => .share idx.toUInt64
  | none =>
    let go x := rewriteWithSharing x hashToIdx ptrToHash
    match e with
    | .prj t f v => .prj t f (go v)
    | .app f a => .app (go f) (go a)
    | .lam c t b => .lam c (go t) (go b)
    | .all c r t b => .all c r (go t) (go b)
    | .letE c t v b => .letE c (go t) (go v) (go b)
    | _ => e

structure SharingBuildState where
  sharingVec : Array Expr := #[]
  hashToIdx : Std.HashMap Address Nat := {}

/-- Emit the entries for `hashes` in order, each rewritten against the entries
before it. -/
def buildSharingEntries (hashes : Array Address) (infoMap : Std.HashMap Address SubtermInfo)
    (ptrToHash : Std.HashMap USize Address) : SharingBuildState :=
  hashes.foldl (init := {}) fun st hash =>
    match infoMap.get? hash with
    | some info =>
      { sharingVec := st.sharingVec.push (rewriteWithSharing info.expr st.hashToIdx ptrToHash)
        hashToIdx := st.hashToIdx.insert hash st.sharingVec.size }
    | none => st

def rewriteExprs (exprs : Array Expr) (hashToIdx : Std.HashMap Address Nat)
    (ptrToHash : Std.HashMap USize Address) : Array Expr :=
  exprs.map fun e => rewriteWithSharing e hashToIdx ptrToHash


/-! ## Stored-table expansion -/

/-- Replace every `Share i` with `i < limit` by `tbl[i]` (itself already
expanded), reusing that object so repeated indices share memory. -/
partial def expandExpr (tbl : Array Expr) (limit : Nat) : Expr → Except String Expr
  | .share i =>
    if i.toNat < limit then .ok tbl[i.toNat]!
    else .error s!"Share {i} is not below {limit}"
  | .prj t f v => return .prj t f (← expandExpr tbl limit v)
  | .app f a => return .app (← expandExpr tbl limit f) (← expandExpr tbl limit a)
  | .lam c t b => return .lam c (← expandExpr tbl limit t) (← expandExpr tbl limit b)
  | .all c r t b =>
    return .all c r (← expandExpr tbl limit t) (← expandExpr tbl limit b)
  | .letE c t v b =>
    return .letE c (← expandExpr tbl limit t) (← expandExpr tbl limit v)
      (← expandExpr tbl limit b)
  | e => .ok e

/-- Expand a stored table. Entry `i` may only reference entries `j < i`
(the backward-reference class of §3.1); anything else is an error. -/
def expandTable (sharing : Array Expr) : Except String (Array Expr) := do
  let mut out : Array Expr := Array.mkEmpty sharing.size
  for i in [0:sharing.size] do
    let e ← (expandExpr out i sharing[i]!).mapError (s!"table entry {i}: " ++ ·)
    out := out.push e
  return out

/-- First differing byte offset, or `none` when the arrays are equal. -/
def firstDiff (a b : ByteArray) : Option Nat := Id.run do
  let n := min a.size b.size
  for i in [0:n] do
    if a[i]! != b[i]! then return some i
  if a.size == b.size then none else some n

/-- Put `roots` back into `info` in `constantInfoRootExprs` order, reusing
the production cursor helpers. -/
def replaceRoots (info : ConstantInfo) (roots : Array Expr) : ConstantInfo :=
  match info with
  | .defn d => .defn { d with typ := roots[0]!, value := roots[1]! }
  | .axio a => .axio { a with typ := roots[0]! }
  | .quot q => .quot { q with typ := roots[0]! }
  | .recr r =>
    .recr { r with typ := roots[0]!,
                   rules := (Ix.CompileM.updateRecursorRules r.rules roots 1).1 }
  | .muts ms => .muts (Ix.CompileM.updateMutConsts ms roots)
  | other => other

/-! ## Compositional unshared sizes on the hash-consed DAG -/

/-- Telescope family of a node: 0 other, 1 App, 2 Lam, 3 All. -/
structure NodeSz where
  /-- Standalone unshared `putExpr` length. -/
  sz : Nat
  fam : UInt8 := 0
  /-- Number of nodes in the maximal same-family telescope headed here. -/
  tele : Nat := 0
  /-- `sz` minus this telescope's TagN (`f = 4`) header. -/
  payload : Nat := 0
  deriving Inhabited

def tag4Size (n : Nat) : Nat := Ixon.tagNByteWidth 4 n
def tag0Size (n : Nat) : Nat := Ixon.tagNByteWidth 0 n

structure DagStats where
  n : Nat := 0
  occ2 : Nat := 0
  cand : Nat := 0
  cand2 : Nat := 0
  cand3 : Nat := 0
  maxApp : Nat := 0
  maxLam : Nat := 0
  maxAll : Nat := 0
  rootSizes : Array Nat := #[]
  /-- Brute-force check of `usageCount` against a walk of the fully expanded
  roots; `none` when the unshared roots exceed the bound. -/
  occCheck : Option Bool := none
  deriving Inhabited

/-- Occurrence counts by walking the expanded roots as trees (following every
shared pointer again). Exponential in general; only used on small inputs.
The second component counts nodes whose pointer the analysis never saw. -/
partial def countOcc (ptrToHash : Std.HashMap USize Address) (e : Expr)
    (acc : Std.HashMap Address Nat × Nat) : Std.HashMap Address Nat × Nat :=
  let (m, missing) := acc
  let acc := match ptrToHash.get? (exprPtr e) with
    | some h => (m.insert h (m.getD h 0 + 1), missing)
    | none => (m, missing + 1)
  match e with
  | .prj _ _ v => countOcc ptrToHash v acc
  | .app f a => countOcc ptrToHash a (countOcc ptrToHash f acc)
  | .lam _ t b | .all _ _ t b => countOcc ptrToHash b (countOcc ptrToHash t acc)
  | .letE _ t v b =>
    countOcc ptrToHash b (countOcc ptrToHash v (countOcc ptrToHash t acc))
  | _ => acc

/-- Hash-cons the roots and compute `N`, candidate counts, telescope maxima and
root unshared sizes. Mirrors `putExpr`: an App telescope writes
`TagN4(#args)`, its head, then its arguments; Lam/All telescopes write
`TagN4(#binders)`, then one contract byte and the type per binder, then the
body. Prj/Let/leaves are the node header (`SubtermInfo.baseSize`, which is
`putNodeHeader`, i.e. the full `putExpr` for leaves) plus the children. -/
def dagStats (res : AnalyzeResult) (roots : Array Expr) (occCheckMax : Nat) :
    DagStats × Std.HashMap Address NodeSz := Id.run do
  let mut sizes : Std.HashMap Address NodeSz := Std.HashMap.emptyWithCapacity res.infoMap.size
  let mut st : DagStats := { n := res.infoMap.size }
  for h in res.topoOrder do
    let some info := res.infoMap.get? h | continue
    let child (i : Nat) : NodeSz := sizes.getD info.children[i]! default
    let node : NodeSz := match info.expr with
      | .app .. =>
        let f := child 0
        let a := child 1
        let tele := if f.fam == 1 then f.tele + 1 else 1
        let payload := (if f.fam == 1 then f.payload else f.sz) + a.sz
        { sz := tag4Size tele + payload, fam := 1, tele, payload }
      | .lam .. =>
        let t := child 0
        let b := child 1
        let tele := if b.fam == 2 then b.tele + 1 else 1
        let payload := 1 + t.sz + (if b.fam == 2 then b.payload else b.sz)
        { sz := tag4Size tele + payload, fam := 2, tele, payload }
      | .all .. =>
        let t := child 0
        let b := child 1
        let tele := if b.fam == 3 then b.tele + 1 else 1
        let payload := 1 + t.sz + (if b.fam == 3 then b.payload else b.sz)
        { sz := tag4Size tele + payload, fam := 3, tele, payload }
      | _ =>
        { sz := info.children.foldl (init := info.baseSize) fun acc c =>
            acc + (sizes.getD c default).sz }
    if node.fam == 1 then st := { st with maxApp := max st.maxApp node.tele }
    else if node.fam == 2 then st := { st with maxLam := max st.maxLam node.tele }
    else if node.fam == 3 then st := { st with maxAll := max st.maxAll node.tele }
    if info.usageCount ≥ 2 then
      st := { st with occ2 := st.occ2 + 1 }
      if node.sz > 1 then st := { st with cand := st.cand + 1 }
      if node.sz > 2 then st := { st with cand2 := st.cand2 + 1 }
      if node.sz > 3 then st := { st with cand3 := st.cand3 + 1 }
    sizes := sizes.insert h node
  let rootSizes := roots.map fun r =>
    match res.ptrToHash.get? (exprPtr r) with
    | some h => (sizes.getD h default).sz
    | none => 0
  let occCheck :=
    if rootSizes.foldl (· + ·) 0 ≤ occCheckMax then
      let (counts, missing) := roots.foldl (init := ({}, 0)) fun acc r =>
        countOcc res.ptrToHash r acc
      some (missing == 0 && counts.size == res.infoMap.size &&
        res.infoMap.fold (init := true) fun ok h info =>
          ok && counts.getD h 0 == info.usageCount)
    else none
  return ({ st with rootSizes, occCheck }, sizes)

/-- Share references in an unexpanded expression, bucketed by index: `< lo`,
`lo..hi-1`, `≥ hi`. -/
partial def countShareRefsBy (lo hi : UInt64) (e : Expr) (acc : Nat × Nat × Nat) :
    Nat × Nat × Nat :=
  match e with
  | .share i =>
    if i < lo then (acc.1 + 1, acc.2)
    else if i < hi then (acc.1, acc.2.1 + 1, acc.2.2)
    else (acc.1, acc.2.1, acc.2.2 + 1)
  | .prj _ _ v => countShareRefsBy lo hi v acc
  | .app f a => countShareRefsBy lo hi a (countShareRefsBy lo hi f acc)
  | .lam _ t b | .all _ _ t b => countShareRefsBy lo hi b (countShareRefsBy lo hi t acc)
  | .letE _ t v b =>
    countShareRefsBy lo hi b (countShareRefsBy lo hi v (countShareRefsBy lo hi t acc))
  | _ => acc

def countShareRefs (e : Expr) (acc : Nat × Nat × Nat) : Nat × Nat × Nat :=
  countShareRefsBy 8 1032 e acc

/-! ## Maximal structural sharing (MSS)

The in-degree rule measured against the canonical encoding:

1. `deg(t)`: incoming edges of `t` in the compact hash-consed DAG, counted with
   multiplicity (`App(x,x)` contributes 2 to `x`), plus the number of roots
   equal to `t`. This is the compact indegree, not the expanded `occ`.
2. Store exactly the terms with `deg ≥ 2` and standalone unshared size > 1;
   every occurrence of a stored term (in roots and in other entries) is a Share.
3. Order: priority topological order. Among stored terms whose stored body
   dependencies (stored terms reachable through unstored nodes) are already
   emitted, emit the one with the largest `deg`, ties by smaller blake3 hash
   bytes. By induction the emitted set stays closed under stored proper
   subterms, so this is the same order as requiring all stored proper
   subterms first.
4. Materialize with `buildSharingEntries` and `rewriteExprs` (above), then
   serialize with `serConstant`. -/

structure MssResult where
  /-- Rewritten table in emission order. -/
  table : Array Expr := #[]
  /-- Rewritten roots. -/
  roots : Array Expr := #[]
  /-- Stored terms that never occur as a root and whose every DAG occurrence
  is a same-family telescope continuation: the function child of an App when
  the term is an App, or the body of a Lam (All) when the term is a Lam (All). -/
  cont : Nat := 0
  /-- Continuation-only entries whose MSS entry body, minus its TagN header, is
  at most 2 bytes. -/
  contP2 : Nat := 0
  /-- Continuation-only entries whose unshared payload (`NodeSz.payload`) is at
  most 2 bytes. -/
  contP2u : Nat := 0
  /-- Share nodes in the MSS table and roots by TagN index width (`< 8`: 1 byte,
  `8..1031`: 2 bytes, `≥ 1032`), counted on the materialized encoding. -/
  refs : Nat × Nat × Nat := (0, 0, 0)
  /-- `Σ deg(t)` over the stored terms (expected to equal the Share count). -/
  degSum : Nat := 0
  deriving Inhabited

/-- Telescope count `putExpr` writes for an expression. -/
def teleCount : Expr → Nat
  | e@(.app ..) => e.collectAppArgs.1.length
  | e@(.lam ..) => e.collectLamBinders.1.length
  | e@(.all ..) => e.collectAllBinders.1.length
  | _ => 0

def mssBuild (res : AnalyzeResult) (sizes : Std.HashMap Address NodeSz)
    (roots : Array Expr) : Except String MssResult := do
  -- 1. Compact-DAG indegree with multiplicity plus root occurrences, and whether
  --    every occurrence is a same-family telescope continuation.
  let mut deg : Std.HashMap Address Nat := Std.HashMap.emptyWithCapacity res.infoMap.size
  let mut nonCont : Std.HashSet Address := {}
  for r in roots do
    let some h := res.ptrToHash.get? (exprPtr r) | throw "root not analyzed"
    deg := deg.insert h (deg.getD h 0 + 1)
    nonCont := nonCont.insert h
  for (_, info) in res.infoMap do
    let pf : UInt8 := match info.expr with
      | .app .. => 1 | .lam .. => 2 | .all .. => 3 | _ => 0
    for i in [0:info.children.size] do
      let c := info.children[i]!
      deg := deg.insert c (deg.getD c 0 + 1)
      let cf := (sizes.getD c default).fam
      unless pf != 0 && cf == pf && i == (if pf == 1 then 0 else 1) do
        nonCont := nonCont.insert c
  -- 2. Stored set, indexed in traversal order.
  let mut stored : Array Address := #[]
  let mut idxOf : Std.HashMap Address Nat := {}
  for h in res.topoOrder do
    if deg.getD h 0 ≥ 2 && (sizes.getD h default).sz > 1 then
      idxOf := idxOf.insert h stored.size
      stored := stored.push h
  let n := stored.size
  -- 3. Body dependencies (stored terms reachable through unstored nodes),
  --    with multiplicity on both sides.
  let mut dependents : Array (Array Nat) := Array.replicate n #[]
  let mut pending : Array Nat := Array.replicate n 0
  for k in [0:n] do
    let some info := res.infoMap.get? stored[k]! | throw "stored term not analyzed"
    let mut stack : Array Address := info.children
    while !stack.isEmpty do
      let c := stack.back!
      stack := stack.pop
      match idxOf.get? c with
      | some j =>
        dependents := dependents.modify j (·.push k)
        pending := pending.modify k (· + 1)
      | none =>
        if let some ci := res.infoMap.get? c then stack := stack ++ ci.children
  -- 4. Priority topological order: largest `deg`, then smaller hash bytes.
  let byRank := (Array.range n).qsort fun a b =>
    let da := deg.getD stored[a]! 0
    let db := deg.getD stored[b]! 0
    da > db || (da == db && Address.cmpBytes stored[a]! stored[b]! == .lt)
  let mut rank : Array Nat := Array.replicate n 0
  for r in [0:n] do
    rank := rank.set! byRank[r]! r
  let mut ready : Std.TreeSet Nat := {}
  for k in [0:n] do
    if pending[k]! == 0 then ready := ready.insert rank[k]!
  let mut order : Array Address := Array.mkEmpty n
  while true do
    match ready.min? with
    | none => break
    | some r =>
      ready := ready.erase r
      let k := byRank[r]!
      order := order.push stored[k]!
      for j in dependents[k]! do
        pending := pending.modify j (· - 1)
        if pending[j]! == 0 then ready := ready.insert rank[j]!
  if order.size != n then throw s!"MSS order incomplete ({order.size}/{n})"
  -- 5. Materialize with the production rewrite helpers.
  let st := buildSharingEntries order res.infoMap res.ptrToHash
  let newRoots := rewriteExprs roots st.hashToIdx res.ptrToHash
  -- 6. Continuation-only entries.
  let refs := newRoots.foldl (fun acc e => countShareRefs e acc)
    (st.sharingVec.foldl (fun acc e => countShareRefs e acc) (0, 0, 0))
  let degSum := stored.foldl (fun a h => a + deg.getD h 0) 0
  let mut out : MssResult :=
    { table := st.sharingVec, roots := newRoots, refs, degSum }
  for h in stored do
    unless nonCont.contains h do
      let entry := st.sharingVec[st.hashToIdx.getD h 0]!
      let payload := (Ixon.serExpr entry).size - tag4Size (teleCount entry)
      out := { out with
        cont := out.cont + 1
        contP2 := out.contP2 + (if payload ≤ 2 then 1 else 0)
        contP2u := out.contP2u + (if (sizes.getD h default).payload ≤ 2 then 1 else 0) }
  return out

/-- Exact structural equality of two expression DAGs, memoized on pointer
pairs (both DAGs stay alive for the whole comparison). -/
partial def eqDag (a b : Expr) : StateM (Std.HashSet (USize × USize)) Bool := do
  let pa := exprPtr a
  let pb := exprPtr b
  if pa == pb then return true
  if (← get).contains (pa, pb) then return true
  let r ← match a, b with
    | .prj t1 f1 v1, .prj t2 f2 v2 => do
      if t1 != t2 || f1 != f2 then return false
      eqDag v1 v2
    | .app f1 x1, .app f2 x2 => do
      if !(← eqDag f1 f2) then return false
      eqDag x1 x2
    | .lam c1 t1 b1, .lam c2 t2 b2 => do
      if c1 != c2 then return false
      if !(← eqDag t1 t2) then return false
      eqDag b1 b2
    | .all c1 r1 t1 b1, .all c2 r2 t2 b2 => do
      if c1 != c2 || r1 != r2 then return false
      if !(← eqDag t1 t2) then return false
      eqDag b1 b2
    | .letE c1 t1 v1 b1, .letE c2 t2 v2 b2 => do
      if c1 != c2 then return false
      if !(← eqDag t1 t2) then return false
      if !(← eqDag v1 v2) then return false
      eqDag b1 b2
    | .share _, _ | _, .share _ => pure false
    | x, y => pure (x == y)
  if r then modify (·.insert (pa, pb))
  return r

/-- Decode MSS bytes, check they re-encode identically, expand the table and
compare the expanded roots with the original roots exactly. -/
def mssCheck (bytes : ByteArray) (roots : Array Expr) : Except String Unit := do
  let c ← Ixon.deConstant bytes
  if (firstDiff (Ixon.serConstant c) bytes).isSome then throw "re-encode differs"
  let tbl ← expandTable c.sharing
  let rs ← (Ix.CompileM.constantInfoRootExprs c.info).mapM (expandExpr tbl tbl.size)
  if rs.size != roots.size then throw s!"root count {rs.size} vs {roots.size}"
  let cmp : StateM (Std.HashSet (USize × USize)) Bool := do
    for (x, y) in rs.zip roots do
      if !(← eqDag x y) then return false
    return true
  let ok : Bool := Id.run (cmp.run' {})
  unless ok do throw "expanded MSS roots differ from the original roots"

/-! ## Per-constant row -/

def kindOf : ConstantInfo → String
  | .defn _ => "defn" | .recr _ => "recr" | .axio _ => "axio" | .quot _ => "quot"
  | .cPrj _ => "cPrj" | .rPrj _ => "rPrj" | .iPrj _ => "iPrj" | .dPrj _ => "dPrj"
  | .muts _ => "muts"

/-- Member composition of a mutual block, e.g. `1i+3c+1r+0d`. -/
def mutsDetail : ConstantInfo → String
  | .muts ms => Id.run do
    let mut i := 0; let mut c := 0; let mut r := 0; let mut d := 0
    for m in ms do
      match m with
      | .indc ind => i := i + 1; c := c + ind.ctors.size
      | .recr _ => r := r + 1
      | .defn _ => d := d + 1
    return s!"{i}i+{c}c+{r}r+{d}d"
  | _ => ""

structure Row where
  addr : Address
  name : String
  kind : String
  detail : String
  roots : Nat
  n : Nat
  occ2 : Nat
  cand : Nat
  cand2 : Nat
  cand3 : Nat
  /-- Stored table entries and bytes. -/
  table : Nat
  raw : Nat
  unshared : Nat
  /-- Canonical (production route) complete-Constant bytes and table entries. -/
  canonical : Nat
  canonicalTable : Nat
  /-- Canonical bytes equal the stored bytes. -/
  rebuildOk : Bool
  firstDiff : Option Nat
  roundtripOk : Bool
  maxApp : Nat
  maxLam : Nat
  maxAll : Nat
  /-- `none`: unshared roots larger than `--validate-max`, not serialized. -/
  validated : Option Bool
  serUnsharedSize : Nat
  occCheck : Option Bool
  /-- MSS complete-Constant bytes, table size and continuation counts. -/
  mss : Nat := 0
  mssTable : Nat := 0
  /-- `some e`: MSS construction or its decode/expand check failed. -/
  mssErr : Option String := none
  cont : Nat := 0
  contP2 : Nat := 0
  contP2u : Nat := 0
  /-- Share nodes in the MSS encoding by TagN index width, and `Σ deg`. -/
  mssRefs : Nat × Nat × Nat := (0, 0, 0)
  mssDegSum : Nat := 0
  ns : Nat := 0
  deriving Inhabited

/-- Everything measured for one constant. Pure; errors are skips. -/
def measure (addr : Address) (name : String) (raw : ByteArray) (c : Constant)
    (validateMax occCheckMax : Nat) : Except String Row := do
  let roundtrip := Ixon.serConstant c
  let tbl ← expandTable c.sharing
  let stored := Ix.CompileM.constantInfoRootExprs c.info
  let roots ← stored.mapM (expandExpr tbl tbl.size) |>.mapError (s!"root: " ++ ·)
  -- 1. Canonical rebuild from the expanded roots (the production route).
  let rebuilt ← (Ix.CompileM.buildConstantWithSharing Ix.CompileM.compilerSharingLimits
      (replaceRoots c.info roots) c.refs c.univs).mapError (s!"canonical: " ++ toString ·)
  let rebuiltBytes := Ixon.serConstant rebuilt
  let diff := firstDiff rebuiltBytes raw
  -- 2. DAG statistics.
  let res := analyzeBlock roots
  let (ds, sizes) := dagStats res roots occCheckMax
  -- 3. Unshared complete-Constant size: bytes outside expressions are fixed.
  let storedExprBytes :=
    c.sharing.foldl (fun acc e => acc + (Ixon.serExpr e).size) 0 +
    stored.foldl (fun acc e => acc + (Ixon.serExpr e).size) 0
  let overhead := tag0Size c.sharing.size + storedExprBytes
  if overhead > raw.size then
    throw s!"stored expression bytes {overhead} exceed constant bytes {raw.size}"
  let fixed := raw.size - overhead
  let rootTotal := ds.rootSizes.foldl (· + ·) 0
  let unshared := fixed + tag0Size 0 + rootTotal
  let (validated, serUnsharedSize) :=
    if rootTotal ≤ validateMax then
      let u : Constant :=
        { info := replaceRoots c.info roots, sharing := #[], refs := c.refs, univs := c.univs }
      let s := (Ixon.serConstant u).size
      (some (s == unshared), s)
    else (none, 0)
  -- 4. Maximal structural sharing, serialized and checked.
  let (mss, mssTable, mssErr, mssCounts, mssRefs, mssDegSum) :=
    match mssBuild res sizes roots with
    | .error e => (0, 0, some s!"build: {e}", (0, 0, 0), (0, 0, 0), 0)
    | .ok m =>
      let mc : Constant :=
        { info := replaceRoots c.info m.roots, sharing := m.table, refs := c.refs, univs := c.univs }
      let b := Ixon.serConstant mc
      let err := match mssCheck b roots with
        | .ok () => none
        | .error e => some s!"check: {e}"
      (b.size, m.table.size, err, (m.cont, m.contP2, m.contP2u), m.refs, m.degSum)
  return {
    mss, mssTable, mssErr, mssRefs, mssDegSum
    cont := mssCounts.1, contP2 := mssCounts.2.1, contP2u := mssCounts.2.2
    addr, name, kind := kindOf c.info, detail := mutsDetail c.info
    roots := roots.size, n := ds.n, occ2 := ds.occ2, cand := ds.cand
    cand2 := ds.cand2, cand3 := ds.cand3, table := c.sharing.size
    raw := raw.size, unshared, canonical := rebuiltBytes.size
    canonicalTable := rebuilt.sharing.size, rebuildOk := diff.isNone
    firstDiff := diff, roundtripOk := (firstDiff roundtrip raw).isNone
    maxApp := ds.maxApp, maxLam := ds.maxLam, maxAll := ds.maxAll
    validated, serUnsharedSize, occCheck := ds.occCheck }

/-! ## Plan §2 witnesses -/

structure Witness where
  label : String
  unshared : Nat
  canonical : Nat
  mss : Nat
  mssHex : String
  canonicalHex : String
  check : Option String
  expectedMss : String

/-- `P = Sort 0`, `T0 = P`, `T(k+1) = All(P, Tk)`, default contracts. -/
def witnessT (n : Nat) : Expr :=
  let p : Expr := .sort 0
  (List.range n).foldl (fun acc _ => Expr.all .many .shared p acc) p

/-- `Axio(false, 0, root)` with empty refs and the given univs. -/
def witnessAxiom (root : Expr) (univs : Array Ixon.Univ) : Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ := root },
    sharing := #[], refs := #[], univs }

def runWitness (label expected : String) (c : Constant) : Except String Witness := do
  let roots := Ix.CompileM.constantInfoRootExprs c.info
  let res := analyzeBlock roots
  let (_, sizes) := dagStats res roots 0
  let m ← mssBuild res sizes roots
  let mb := Ixon.serConstant { c with info := replaceRoots c.info m.roots, sharing := m.table }
  let canon ← (Ix.CompileM.buildConstantWithSharing Ix.CompileM.compilerSharingLimits
      c.info c.refs c.univs).mapError (s!"canonical: " ++ toString ·)
  let cb := Ixon.serConstant canon
  let check := match mssCheck mb roots with | .ok () => none | .error e => some e
  return { label, unshared := (Ixon.serConstant c).size, canonical := cb.size, mss := mb.size,
           mssHex := hexOfBytes mb, canonicalHex := hexOfBytes cb, check,
           expectedMss := expected }

def witnesses : Array (Except String Witness) :=
  let t2 := witnessT 2
  let t16 := witnessT 16
  let p : Expr := .sort 0
  let a : Expr := .all .many .shared p p
  let b : Expr := .all .many .shared p (.sort 1)
  #[runWitness "`T2 → T2`" "17 (plan: exact minimum `d200009117b0b001921700170000000100`)"
      (witnessAxiom (.all .many .shared t2 t2) #[.zero]),
    runWitness "`T16 → T16`" "46 (plan: feasible improvement)"
      (witnessAxiom (.all .many .shared t16 t16) #[.zero]),
    runWitness "`A → A → B → B`, `A = Prop → Prop`, `B = Prop → Type`" "25 (plan: minimum, two tied orders)"
      (witnessAxiom (.all .many .shared a (.all .many .shared a (.all .many .shared b b)))
        #[.zero, .succ .zero])]

/-- Negative controls for `mssCheck`: the `T2 → T2` MSS bytes must be rejected
against roots that differ in one leaf, and against the `T16 → T16` roots. -/
def negativeControls : Array (String × Bool) :=
  let p : Expr := .sort 0
  let t2 := witnessT 2
  let t2' : Expr := .all .many .shared p (.all .many .shared p (.sort 1))
  let c := witnessAxiom (.all .many .shared t2 t2) #[.zero]
  let roots := Ix.CompileM.constantInfoRootExprs c.info
  let res := analyzeBlock roots
  let (_, sizes) := dagStats res roots 0
  match mssBuild res sizes roots with
  | .error e => #[(s!"MSS build failed: {e}", false)]
  | .ok m =>
    let mb := Ixon.serConstant { c with info := replaceRoots c.info m.roots, sharing := m.table }
    let rejects (rs : Array Expr) : Bool :=
      match mssCheck mb rs with | .ok () => false | .error _ => true
    #[("`T2 → T2` MSS bytes vs roots `T2 → T2'` (one leaf `Sort 0` replaced by `Sort 1`)",
        rejects #[.all .many .shared t2 t2']),
      ("`T2 → T2` MSS bytes vs roots `T16 → T16`",
        rejects #[.all .many .shared (witnessT 16) (witnessT 16)]),
      ("`T2 → T2` MSS bytes vs its own roots (must be accepted)", !rejects roots)]

/-! ## Statistics -/

/-- Nearest-rank percentile of a sorted array (`p` in percent). -/
def pct (s : Array Nat) (p : Nat) : Nat :=
  if s.isEmpty then 0 else s[(max 1 ((p * s.size + 99) / 100)) - 1]!

def fmtMean (sum count : Nat) : String :=
  if count == 0 then "0" else
    let q := (sum * 100 + count / 2) / count
    let frac := q % 100
    s!"{q / 100}.{if frac < 10 then "0" else ""}{frac}"

def fmtPct (part whole : Nat) : String :=
  if whole == 0 then "0" else
    let q := (part * 1000 + whole / 2) / whole
    s!"{q / 10}.{q % 10}%"

def distRow (label : String) (xs : Array Nat) : String :=
  let s := xs.qsort (· < ·)
  let sum := s.foldl (· + ·) 0
  s!"| {label} | {s[0]?.getD 0} | {pct s 50} | {pct s 90} | {pct s 99} | {s.back?.getD 0} | {fmtMean sum s.size} |"

def distTable (rows : Array Row) : String :=
  let hdr := "| Metric | min | median | p90 | p99 | max | mean |\n|---|---:|---:|---:|---:|---:|---:|"
  let lines := #[
    distRow "`N` (distinct subterms)" (rows.map (·.n)),
    distRow "`occ ≥ 2` (R1 only)" (rows.map (·.occ2)),
    distRow "candidates (R1+R2: occ ≥ 2, size > 1)" (rows.map (·.cand)),
    distRow "candidates with size > 2" (rows.map (·.cand2)),
    distRow "candidates with size > 3" (rows.map (·.cand3)),
    distRow "stored table size" (rows.map (·.table)),
    distRow "canonical table size" (rows.map (·.canonicalTable)),
    distRow "`rawBytes.size`" (rows.map (·.raw)),
    distRow "canonical Constant bytes" (rows.map (·.canonical)),
    distRow "unshared Constant bytes" (rows.map (·.unshared)),
    distRow "max telescope length" (rows.map fun r => max r.maxApp (max r.maxLam r.maxAll)),
    distRow "roots" (rows.map (·.roots))]
  hdr ++ "\n" ++ "\n".intercalate lines.toList

def bucketTable (rows : Array Row) (field : Row → Nat) : String := Id.run do
  let total := rows.size
  let mut out := "| candidates | constants | share |\n|---|---:|---:|"
  for b in [8, 16, 24, 32, 64, 128] do
    let k := (rows.filter fun r => field r ≤ b).size
    out := out ++ s!"\n| ≤ {b} | {k} | {fmtPct k total} |"
  let k := (rows.filter fun r => field r > 128).size
  out := out ++ s!"\n| > 128 | {k} | {fmtPct k total} |"
  return out

/-- Repriced minus current bytes over integer classes `lo..hi-1`. -/
def csvEscape (s : String) : String := "\"" ++ s.replace "\"" "\"\"" ++ "\""

def csvHeader : String :=
  "addr,name,kind,members,roots,N,occ_ge2,cand,cand_gt2,cand_gt3,table,raw_bytes," ++
  "unshared_bytes,canonical_bytes,canonical_table,rebuild_ok,roundtrip_ok,unshared_validated," ++
  "occ_checked,max_app,max_lam,max_all,us," ++
  "mss_bytes,mss_table,mss_ok,mss_cont,mss_cont_p2,mss_cont_p2u," ++
  "mss_refs_lt8,mss_refs_8_1031,mss_refs_ge1032,mss_deg_sum"

def csvLine (r : Row) : String :=
  let v := match r.validated with | some true => "1" | some false => "0" | none => ""
  let o := match r.occCheck with | some true => "1" | some false => "0" | none => ""
  s!"{(toString r.addr).take 16},{csvEscape r.name},{r.kind},{r.detail},{r.roots},{r.n}," ++
  s!"{r.occ2},{r.cand},{r.cand2},{r.cand3},{r.table},{r.raw},{r.unshared}," ++
  s!"{r.canonical},{r.canonicalTable}," ++
  s!"{if r.rebuildOk then 1 else 0},{if r.roundtripOk then 1 else 0},{v},{o}," ++
  s!"{r.maxApp},{r.maxLam},{r.maxAll},{r.ns / 1000}," ++
  s!"{r.mss},{r.mssTable},{if r.mssErr.isNone then 1 else 0},{r.cont},{r.contP2},{r.contP2u}," ++
  s!"{r.mssRefs.1},{r.mssRefs.2.1},{r.mssRefs.2.2},{r.mssDegSum}"

def kindOrder : Array String :=
  #["defn", "recr", "axio", "quot", "muts", "iPrj", "cPrj", "rPrj", "dPrj"]

/-- Nearest-rank percentile of a sorted `Int` array. -/
def pctInt (s : Array Int) (p : Nat) : Int :=
  if s.isEmpty then 0 else s[(max 1 ((p * s.size + 99) / 100)) - 1]!

def fmtSignedPct (num : Int) (den : Nat) : String :=
  if den == 0 then "0" else
    let q := (num.natAbs * 1000 + den / 2) / den
    s!"{if num < 0 then "−" else "+"}{q / 10}.{q % 10}%"

def fmtSignedPct2 (num : Int) (den : Nat) : String :=
  if den == 0 then "0" else
    let q := (num.natAbs * 10000 + den / 2) / den
    let frac := q % 100
    s!"{if num < 0 then "−" else "+"}{q / 100}.{if frac < 10 then "0" else ""}{frac}%"

/-- Share nodes of the MSS encoding over all index widths. -/
def mssRefTotal (r : Row) : Nat := r.mssRefs.1 + r.mssRefs.2.1 + r.mssRefs.2.2

/-- The MSS section of the generated report. -/
def mssReport (rows : Array Row) (ws : Array (Except String Witness)) : String := Id.run do
  let wr := rows.filter (·.roots > 0)
  let mut md := "## Maximal structural sharing (MSS)\n\n"
  md := md ++ "Rule: store exactly the subterms with compact-DAG indegree `deg ≥ 2` (edges with multiplicity plus root occurrences) and unshared size > 1; every occurrence of a stored term is a Share; order by priority topological order (largest `deg`, then smaller blake3 hash bytes). Built with the harness-local `buildSharingEntries`/`rewriteExprs`, placed with the production root cursor helpers, serialized with `serConstant`.\n\n"
  md := md ++ "### Witnesses from the plan (§2)\n\n| fixture | unshared B | canonical B | MSS B | expected MSS | MSS decode/expand check | MSS bytes | canonical bytes |\n|---|---:|---:|---:|---|---|---|---|\n"
  for w in ws do
    match w with
    | .ok w =>
      md := md ++ s!"| {w.label} | {w.unshared} | {w.canonical} | {w.mss} | {w.expectedMss} | {w.check.getD "ok"} | `{w.mssHex}` | `{w.canonicalHex}` |\n"
    | .error e => md := md ++ s!"| (witness failed) | | | | | {e} | | |\n"
  md := md ++ "\nNegative controls for the MSS decode/expand/equality check:\n\n"
  for (label, ok) in negativeControls do
    md := md ++ s!"- {label}: {if ok then "behaves as expected" else "**UNEXPECTED**"}\n"
  let errs := rows.filter (·.mssErr.isSome)
  md := md ++ s!"\n### Corpus verification\n\n- MSS built for {rows.size} constants; decode, re-encode (byte-identical), table expansion and exact pointer-memoized structural equality of the expanded roots with the original expanded roots: {rows.size - errs.size} ok, **{errs.size}** failed.\n"
  for r in errs.extract 0 10 do
    md := md ++ s!"  - `{r.name}`: {r.mssErr.getD ""}\n"
  let sRaw : Nat := wr.foldl (· + ·.canonical) 0
  let sMss : Nat := wr.foldl (· + ·.mss) 0
  let sUn : Nat := wr.foldl (· + ·.unshared) 0
  let dTot : Int := (sMss : Int) - sRaw
  md := md ++ s!"\n### Totals over the {wr.size} constants with at least one root\n\n| encoding | total bytes | vs canonical |\n|---|---:|---:|\n"
  md := md ++ s!"| canonical (production route) | {sRaw} | |\n| MSS | {sMss} | {dTot} ({fmtSignedPct dTot sRaw}) |\n| unshared | {sUn} | {(sUn : Int) - sRaw} |\n\n"
  let better := wr.filter fun r => r.mss < r.canonical
  let equal := wr.filter fun r => r.mss == r.canonical
  let worse := wr.filter fun r => r.mss > r.canonical
  let savings := (better.map fun r => r.canonical - r.mss).qsort (· < ·)
  let losses := (worse.map fun r => r.mss - r.canonical).qsort (· < ·)
  let sSav := savings.foldl (· + ·) 0
  let sLoss := losses.foldl (· + ·) 0
  md := md ++ "### MSS − canonical per constant\n\n| outcome | constants | share | bytes |\n|---|---:|---:|---:|\n"
  md := md ++ s!"| MSS smaller | {better.size} | {fmtPct better.size wr.size} | −{sSav} |\n"
  md := md ++ s!"| equal | {equal.size} | {fmtPct equal.size wr.size} | 0 |\n"
  md := md ++ s!"| MSS larger | {worse.size} | {fmtPct worse.size wr.size} | +{sLoss} |\n\n"
  md := md ++ s!"- Losses (MSS − canonical) over the {worse.size} larger constants: p50 {pct losses 50}, p90 {pct losses 90}, p99 {pct losses 99}, max {losses.back?.getD 0}, mean {fmtMean sLoss losses.size}.\n"
  md := md ++ s!"- Savings (canonical − MSS) over the {better.size} smaller constants: p50 {pct savings 50}, p90 {pct savings 90}, p99 {pct savings 99}, max {savings.back?.getD 0}, mean {fmtMean sSav savings.size}.\n"
  let deltas : Array Int := (wr.map fun r => (r.mss : Int) - r.canonical).qsort (· < ·)
  md := md ++ s!"- Signed Δ = MSS − canonical over all {wr.size} rooted constants: min {deltas[0]?.getD 0}, p1 {pctInt deltas 1}, p10 {pctInt deltas 10}, p50 {pctInt deltas 50}, p90 {pctInt deltas 90}, p99 {pctInt deltas 99}, max {deltas.back?.getD 0}.\n"
  let overUn := wr.filter fun r => r.mss > r.unshared
  let excess := overUn.foldl (fun acc r => acc + (r.mss - r.unshared)) 0
  let maxEx := overUn.foldl (fun acc r => max acc (r.mss - r.unshared)) 0
  md := md ++ s!"- MSS larger than unshared: {overUn.size} constants, total excess {excess} bytes, max {maxEx}. (Canonical larger than unshared: {(wr.filter fun r => r.canonical > r.unshared).size}.)\n\n"
  md := md ++ "### Table sizes (rooted constants)\n\n| Metric | min | median | p90 | p99 | max | mean |\n|---|---:|---:|---:|---:|---:|---:|\n"
  md := md ++ distRow "MSS table size" (wr.map (·.mssTable)) ++ "\n"
  md := md ++ distRow "canonical table size" (wr.map (·.canonicalTable)) ++ "\n"
  md := md ++ distRow "MSS continuation-only entries" (wr.map (·.cont)) ++ "\n"
  md := md ++ distRow "… with MSS entry payload ≤ 2" (wr.map (·.contP2)) ++ "\n"
  md := md ++ distRow "… with unshared payload ≤ 2" (wr.map (·.contP2u)) ++ "\n\n"
  md := md ++ s!"- Total MSS entries {wr.foldl (· + ·.mssTable) 0}; canonical entries {wr.foldl (· + ·.canonicalTable) 0}.\n"
  let withCont := wr.filter (·.contP2 > 0)
  md := md ++ s!"- Continuation-only entries (never a root; every occurrence is the function child of an App for an App term, or the body of a Lam/All for a Lam/All term): {wr.foldl (· + ·.cont) 0} in total; with MSS entry payload ≤ 2: {wr.foldl (· + ·.contP2) 0}; with unshared payload ≤ 2: {wr.foldl (· + ·.contP2u) 0}.\n"
  md := md ++ s!"- Constants with at least one continuation-only entry of MSS payload ≤ 2: {withCont.size}; of these, MSS larger than canonical: {(withCont.filter fun r => r.mss > r.canonical).size}, equal: {(withCont.filter fun r => r.mss == r.canonical).size}, smaller: {(withCont.filter fun r => r.mss < r.canonical).size}.\n"
  md := md ++ s!"- Of the {worse.size} constants where MSS is larger, {(worse.filter (·.contP2 > 0)).size} have such an entry; of the {better.size} where MSS is smaller, {(better.filter (·.contP2 > 0)).size}.\n\n"
  md := md ++ "### MSS by ConstantInfo kind (rooted constants)\n\n| kind | constants | canonical B | MSS B | unshared B | MSS/canonical | MSS smaller | equal | MSS larger |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|\n"
  for k in kindOrder do
    let ks := wr.filter (·.kind == k)
    unless ks.isEmpty do
      let r := ks.foldl (· + ·.canonical) 0
      let m := ks.foldl (· + ·.mss) 0
      let u := ks.foldl (· + ·.unshared) 0
      md := md ++ s!"| {k} | {ks.size} | {r} | {m} | {u} | {fmtPct m r} | {(ks.filter fun x => x.mss < x.canonical).size} | {(ks.filter fun x => x.mss == x.canonical).size} | {(ks.filter fun x => x.mss > x.canonical).size} |\n"
  let hdr := "| # | constant | kind | canonical B | MSS B | Δ | unshared B | canonical table | MSS table | cont. p≤2 |\n|---:|---|---|---:|---:|---:|---:|---:|---:|---:|\n"
  let line (j : Nat) (r : Row) : String :=
    s!"| {j + 1} | `{r.name}` | {r.kind} | {r.canonical} | {r.mss} | {(r.mss : Int) - r.canonical} | {r.unshared} | {r.canonicalTable} | {r.mssTable} | {r.contP2} |\n"
  md := md ++ "\n### Ten largest MSS losses (MSS − canonical)\n\n" ++ hdr
  let wl := (worse.qsort fun a b =>
    let da := a.mss - a.canonical; let db := b.mss - b.canonical
    da > db || (da == db && a.name < b.name)).extract 0 10
  for h : j in [0:wl.size] do md := md ++ line j wl[j]
  md := md ++ "\n### Ten largest MSS wins (canonical − MSS)\n\n" ++ hdr
  let bw := (better.qsort fun a b =>
    let da := a.canonical - a.mss; let db := b.canonical - b.mss
    da > db || (da == db && a.name < b.name)).extract 0 10
  for h : j in [0:bw.size] do md := md ++ line j bw[j]
  return md


/-! ## Metadata study (`--meta`)

Streams a whole `.ixe` section by section with the production readers
(`getExprMetaNode`, `getExpr`, `getUniv`, `getFusedHint`, …), recording the
exact bytes of every component, and analyses each `ConstantMeta.metaSharing`
against its constant's primary sharing table. Constants are parsed only when a
`Named` entry needs them, so the file is never materialized as a whole `Env`.
The byte categories must sum to the file size. -/

/-- Run a reader at a byte offset of a shared buffer. -/
def runAt (buf : ByteArray) (off : Nat) (m : Ixon.GetM α) : Except String (α × Nat) :=
  match m.run { idx := off, bytes := buf } with
  | .ok a st => .ok (a, st.idx)
  | .error e _ => .error e

def getPos : Ixon.GetM Nat := do return (← get).idx

def arenaKindNames : Array String :=
  #["leaf", "app", "binder", "letBinder", "ref", "prj", "mdata", "callSite", "etaCallSite"]

def arenaKind : Ixon.ExprMetaData → Nat
  | .leaf => 0 | .app .. => 1 | .binder .. => 2 | .letBinder .. => 3 | .ref .. => 4
  | .prj .. => 5 | .mdata .. => 6 | .callSite .. => 7 | .etaCallSite .. => 8

/-! ### ExprMeta arena structure: child deltas and duplication -/

/-- Child arena indices of a node, with a slot id: 0 App function, 1 App
argument, 2 Binder type, 3 Binder body, 4 Let type, 5 Let value, 6 Let body,
7 Prj child, 8 Mdata child, 9 call-site metadata references (not in the delta
study). -/
def arenaChildren : Ixon.ExprMetaData → Array (Nat × UInt64)
  | .leaf | .ref _ => #[]
  | .app f a => #[(0, f), (1, a)]
  | .binder _ _ t b => #[(2, t), (3, b)]
  | .letBinder _ t v b => #[(4, t), (5, v), (6, b)]
  | .prj _ c => #[(7, c)]
  | .mdata _ c => #[(8, c)]
  | .callSite _ es cm oh =>
    (es.map fun e => match e with | .kept _ m | .collapsed _ m => (9, m)) ++
      cm.map (9, ·) ++ (match oh with | some (_, m) => #[(9, m)] | none => #[])
  | .etaCallSite _ _ es cm w =>
    (es.map fun e => match e with | .kept _ m | .collapsed _ m => (9, m)) ++
      cm.map (9, ·) ++ #[(9, w)]

def arenaSlotNames : Array String :=
  #["App function", "App argument", "Binder type", "Binder body", "Let type", "Let value",
    "Let body", "Prj child", "Mdata child"]

/-- Hash-consing key of an arena node: kind, payload, canonical child IDs. -/
structure ArenaKey where
  kind : UInt8
  name : Address := ⟨ByteArray.empty⟩
  info : UInt8 := 0
  kids : Array Nat := #[]
  extra : String := ""
  deriving BEq, Hashable, Repr

def binderInfoCode : Lean.BinderInfo → UInt8
  | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3

def arenaKey (node : Ixon.ExprMetaData) (kids : Array Nat) : ArenaKey :=
  match node with
  | .leaf => { kind := 0 }
  | .app .. => { kind := 1, kids }
  | .binder n bi .. => { kind := 2, name := n, info := binderInfoCode bi, kids }
  | .letBinder n .. => { kind := 3, name := n, kids }
  | .ref n => { kind := 4, name := n }
  | .prj n _ => { kind := 5, name := n, kids }
  | .mdata md _ => { kind := 6, extra := reprStr md, kids }
  | .callSite n es cm oh =>
    let shape := es.map fun e => match e with | .kept c _ => (0, c) | .collapsed s _ => (1, s)
    { kind := 7, name := n, kids, extra := reprStr (shape, cm.size, oh.map (·.1)) }
  | .etaCallSite k n es cm _ =>
    let shape := es.map fun e => match e with | .kept c _ => (0, c) | .collapsed s _ => (1, s)
    { kind := 8, name := n, kids, extra := reprStr (k, shape, cm.size) }

/-- Arena statistics. `slots` is flat, 10 numbers per slot (0..8): children,
deltas = 1, 2–7, 8–127, 128–1023, 1024–16383, ≥ 16384, not backward, current
child-field bytes (`Tag0`), delta bytes (TagN-byte). -/
structure ArenaStudy where
  slots : Array Nat := Array.replicate 90 0
  nodes : Nat := 0
  bytes : Nat := 0
  dupNodes : Nat := 0
  dupBytes : Nat := 0
  appNodes : Nat := 0
  appBytes : Nat := 0
  appDupNodes : Nat := 0
  appDupBytes : Nat := 0
  /-- Maximal duplicate subtrees: duplicate nodes with no duplicate parent. -/
  maxRoots : Nat := 0
  maxNodes : Nat := 0
  maxBytes : Nat := 0
  /-- Sizes (duplicate nodes) of maximal duplicate subtrees: 1, 2–7, 8–63,
  64–1023, ≥ 1024. -/
  maxHist : Array Nat := Array.replicate 5 0
  appMaxRoots : Nat := 0
  appMaxNodes : Nat := 0
  appMaxBytes : Nat := 0
  /-- Children (any slot, including call-site references) that do not point
  strictly backward. -/
  notBackward : Nat := 0
  arenas : Nat := 0
  /-- Independent check on arenas of at most 256 nodes: duplicates recounted by
  comparing full subtree strings (equal / different / skipped for size). -/
  checkEq : Nat := 0
  checkNe : Nat := 0
  checkSkip : Nat := 0
  deriving Inhabited

def ArenaStudy.add (a b : ArenaStudy) : ArenaStudy :=
  let z (x y : Array Nat) := (x.zip y).map fun (p, q) => p + q
  { slots := z a.slots b.slots, nodes := a.nodes + b.nodes, bytes := a.bytes + b.bytes,
    dupNodes := a.dupNodes + b.dupNodes, dupBytes := a.dupBytes + b.dupBytes,
    appNodes := a.appNodes + b.appNodes, appBytes := a.appBytes + b.appBytes,
    appDupNodes := a.appDupNodes + b.appDupNodes, appDupBytes := a.appDupBytes + b.appDupBytes,
    maxRoots := a.maxRoots + b.maxRoots, maxNodes := a.maxNodes + b.maxNodes,
    maxBytes := a.maxBytes + b.maxBytes, maxHist := z a.maxHist b.maxHist,
    appMaxRoots := a.appMaxRoots + b.appMaxRoots, appMaxNodes := a.appMaxNodes + b.appMaxNodes,
    appMaxBytes := a.appMaxBytes + b.appMaxBytes, notBackward := a.notBackward + b.notBackward,
    arenas := a.arenas + b.arenas, checkEq := a.checkEq + b.checkEq,
    checkNe := a.checkNe + b.checkNe, checkSkip := a.checkSkip + b.checkSkip }

/-- One arena: child deltas per slot, and duplication by bottom-up hash-consing
(kind, payload, canonical child IDs). A node is a duplicate when its canonical ID
occurred earlier in the arena. A maximal duplicate subtree is rooted at a
duplicate node that no duplicate node references; its size is the number of
duplicate nodes reachable from it through duplicate nodes (each counted once). -/
def arenaStudy (nodes : Array Ixon.ExprMetaData) (sizes : Array Nat) : ArenaStudy := Id.run do
  let n := nodes.size
  let mut st : ArenaStudy := { arenas := 1, nodes := n, bytes := sizes.foldl (· + ·) 0 }
  let mut slots := st.slots
  let mut canon : Array Nat := Array.mkEmpty n
  let mut isDup : Array Bool := Array.mkEmpty n
  let mut map : Std.HashMap ArenaKey Nat := {}
  let mut kidsOf : Array (Array Nat) := Array.mkEmpty n
  for i in [0:n] do
    let node := nodes[i]!
    let ch := arenaChildren node
    let mut kids : Array Nat := #[]
    let mut valid : Array Nat := #[]
    for (slot, c64) in ch do
      let c := c64.toNat
      if c < i then
        kids := kids.push canon[c]!
        valid := valid.push c
      else
        kids := kids.push (UInt64.size + c)
        st := { st with notBackward := st.notBackward + 1 }
      if slot < 9 then
        let base := slot * 10
        let d := i - c
        let b := if c ≥ i then 7 else if d == 1 then 1 else if d < 8 then 2 else if d < 128 then 3
          else if d < 1024 then 4 else if d < 16384 then 5 else 6
        slots := slots.modify base (· + 1) |>.modify (base + b) (· + 1)
          |>.modify (base + 8) (· + tag0Size c)
          |>.modify (base + 9) (· + (if c < i then tag0Size d else tag0Size c))
    kidsOf := kidsOf.push valid
    let key := arenaKey node kids
    let isApp := match node with | .app .. => true | _ => false
    if isApp then st := { st with appNodes := st.appNodes + 1, appBytes := st.appBytes + sizes[i]! }
    match map.get? key with
    | some id =>
      canon := canon.push id
      isDup := isDup.push true
      st := { st with dupNodes := st.dupNodes + 1, dupBytes := st.dupBytes + sizes[i]! }
      if isApp then
        st := { st with appDupNodes := st.appDupNodes + 1, appDupBytes := st.appDupBytes + sizes[i]! }
    | none =>
      let id := map.size
      map := map.insert key id
      canon := canon.push id
      isDup := isDup.push false
  -- Maximal duplicate subtrees.
  let mut dupParent : Array Bool := Array.replicate n false
  for i in [0:n] do
    if isDup[i]! then
      for c in kidsOf[i]! do
        dupParent := dupParent.set! c true
  let mut seen : Array Bool := Array.replicate n false
  for j in [0:n] do
    let r := n - 1 - j
    if isDup[r]! && !dupParent[r]! then
      let mut cnt := 0
      let mut byt := 0
      let mut stack : Array Nat := #[r]
      while !stack.isEmpty do
        let t := stack.back!
        stack := stack.pop
        if seen[t]! || !isDup[t]! then continue
        seen := seen.set! t true
        cnt := cnt + 1
        byt := byt + sizes[t]!
        stack := stack ++ kidsOf[t]!
      let h := if cnt ≤ 1 then 0 else if cnt < 8 then 1 else if cnt < 64 then 2
        else if cnt < 1024 then 3 else 4
      st := { st with maxRoots := st.maxRoots + 1, maxNodes := st.maxNodes + cnt,
                      maxBytes := st.maxBytes + byt, maxHist := st.maxHist.modify h (· + 1) }
      if (match nodes[r]! with | .app .. => true | _ => false) then
        st := { st with appMaxRoots := st.appMaxRoots + 1, appMaxNodes := st.appMaxNodes + cnt,
                        appMaxBytes := st.appMaxBytes + byt }
  -- Independent recount on small arenas: full subtree strings.
  if n ≤ 256 then
    let mut strs : Array String := Array.mkEmpty n
    let mut tooBig := false
    for i in [0:n] do
      let node := nodes[i]!
      let base := reprStr (arenaKey node #[])
      let kids := (arenaChildren node).map fun (_, c) =>
        if c.toNat < i then strs[c.toNat]! else s!"!{c}"
      let s := base ++ "(" ++ ",".intercalate kids.toList ++ ")"
      if s.length > 100000 then tooBig := true
      strs := strs.push (if tooBig then "" else s)
    if tooBig then
      st := { st with checkSkip := st.checkSkip + 1 }
    else
      let distinct := (strs.foldl (fun (h : Std.HashSet String) s => h.insert s) {}).size
      if n - distinct == st.dupNodes then st := { st with checkEq := st.checkEq + 1 }
      else st := { st with checkNe := st.checkNe + 1 }
  else
    st := { st with checkSkip := st.checkSkip + 1 }
  return { st with slots }

/-- Byte breakdown of one `ConstantMeta`. -/
structure MetaBreak where
  info : Nat := 0
  arena : Nat := 0
  kindBytes : Array Nat := Array.replicate 9 0
  kindCount : Array Nat := Array.replicate 9 0
  sharingBytes : Nat := 0
  sharing : Array (Expr × Nat) := #[]
  refs : Nat := 0
  nRefs : Nat := 0
  univs : Nat := 0
  nUnivs : Nat := 0
  patches : Nat := 0
  ast : ArenaStudy := {}
  deriving Inhabited

/-- The arena, node by node, mirroring `getExprMetaArenaIndexed`. -/
def getArenaBreak (rev : Ixon.NameReverseIndex) (mb : MetaBreak) : Ixon.GetM MetaBreak := do
  let p0 ← getPos
  let len := (← Ixon.getTagN 0).value.toNat
  let mut kb := mb.kindBytes
  let mut kc := mb.kindCount
  let mut nodes : Array Ixon.ExprMetaData := Array.mkEmpty len
  let mut sizes : Array Nat := Array.mkEmpty len
  let mut lo : Array Nat := Array.mkEmpty len
  for i in [0:len] do
    let a ← getPos
    let (node, top) ← Ixon.getExprMetaNode rev i lo
    lo := lo.push top
    let b ← getPos
    let k := arenaKind node
    kb := kb.modify k (· + (b - a))
    kc := kc.modify k (· + 1)
    nodes := nodes.push node
    sizes := sizes.push (b - a)
  let p1 ← getPos
  return { mb with arena := mb.arena + (p1 - p0), kindBytes := kb, kindCount := kc,
                   ast := mb.ast.add (arenaStudy nodes sizes) }

/-- The variant payload, mirroring `getConstantMetaInfoIndexed`; the arena is
measured separately. -/
def getInfoBreak (rev : Ixon.NameReverseIndex) : Ixon.GetM MetaBreak := do
  let p0 ← getPos
  let mut mb : MetaBreak := {}
  match ← Ixon.getU8 with
  | 255 => pure ()
  | 0 =>
    let _ ← Ixon.getIdx rev
    for _ in [0:3] do let _ ← Ixon.getIdxVec rev
    mb ← getArenaBreak rev mb
    let _ ← Ixon.getTagN 0
    let _ ← Ixon.getTagN 0
  | 1 | 2 =>
    let _ ← Ixon.getIdx rev
    let _ ← Ixon.getIdxVec rev
    mb ← getArenaBreak rev mb
    let _ ← Ixon.getTagN 0
  | 3 =>
    let _ ← Ixon.getIdx rev
    for _ in [0:4] do let _ ← Ixon.getIdxVec rev
    mb ← getArenaBreak rev mb
    let _ ← Ixon.getTagN 0
  | 4 =>
    let _ ← Ixon.getIdx rev
    let _ ← Ixon.getIdxVec rev
    let _ ← Ixon.getIdx rev
    mb ← getArenaBreak rev mb
    let _ ← Ixon.getTagN 0
  | 5 =>
    let _ ← Ixon.getIdx rev
    for _ in [0:4] do let _ ← Ixon.getIdxVec rev
    mb ← getArenaBreak rev mb
    let _ ← Ixon.getTagN 0
    let n := (← Ixon.getTagN 0).value.toNat
    for _ in [0:n] do let _ ← Ixon.getTagN 0
  | 6 =>
    let n := (← Ixon.getTagN 0).value.toNat
    for _ in [0:n] do let _ ← Ixon.getIdxVec rev
    match ← Ixon.getU8 with
    | 0 => pure ()
    | 1 =>
      for _ in [0:2] do
        let k := (← Ixon.getTagN 0).value.toNat
        for _ in [0:k] do let _ ← Ixon.getTagN 0
      let k := (← Ixon.getTagN 0).value.toNat
      for _ in [0:k] do let _ ← Ixon.getU8
    | x => throw s!"invalid aux_layout tag {x}"
  | x => throw s!"invalid ConstantMeta tag {x}"
  let p1 ← getPos
  return { mb with info := (p1 - p0) - mb.arena }

/-- One `ConstantMeta`, mirroring `getConstantMetaIndexed`. -/
def getMetaBreak (rev : Ixon.NameReverseIndex) : Ixon.GetM MetaBreak := do
  let mb ← getInfoBreak rev
  let a ← getPos
  let n := (← Ixon.getTagN 0).value.toNat
  let mut sh : Array (Expr × Nat) := #[]
  for _ in [0:n] do
    let s ← getPos
    let e ← Ixon.getExpr
    let t ← getPos
    sh := sh.push (e, t - s)
  let b ← getPos
  let nr := (← Ixon.getTagN 0).value.toNat
  for _ in [0:nr] do let _ ← Ixon.Serialize.get (α := Address)
  let c ← getPos
  let nu := (← Ixon.getTagN 0).value.toNat
  for _ in [0:nu] do let _ ← Ixon.getUniv
  let d ← getPos
  let np := (← Ixon.getTagN 0).value.toNat
  for _ in [0:np] do
    let _ ← Ixon.getTagN 0
    let k := (← Ixon.getTagN 0).value.toNat
    for _ in [0:k] do let _ ← Ixon.getTagN 0
  let e ← getPos
  return { mb with sharingBytes := b - a, sharing := sh, refs := c - b, nRefs := nr,
                   univs := d - c, nUnivs := nu, patches := e - d }

/-- `metaSharing` of one constant against its primary table. -/
structure MSAnalysis where
  constants : Nat := 0
  entries : Nat := 0
  bytes : Nat := 0
  shareNodes : Nat := 0
  unshared : Nat := 0
  reenc : Nat := 0
  distinct : Nat := 0
  bytesDedup : Nat := 0
  reencDedup : Nat := 0
  matched : Nat := 0
  matchedBytes : Nat := 0
  matchedTable : Nat := 0
  deriving Inhabited

def MSAnalysis.add (a b : MSAnalysis) : MSAnalysis :=
  { constants := a.constants + b.constants, entries := a.entries + b.entries,
    bytes := a.bytes + b.bytes, shareNodes := a.shareNodes + b.shareNodes,
    unshared := a.unshared + b.unshared, reenc := a.reenc + b.reenc,
    distinct := a.distinct + b.distinct, bytesDedup := a.bytesDedup + b.bytesDedup,
    reencDedup := a.reencDedup + b.reencDedup, matched := a.matched + b.matched,
    matchedBytes := a.matchedBytes + b.matchedBytes, matchedTable := a.matchedTable + b.matchedTable }

/-- Expand the primary table, the primary roots and the `metaSharing` entries
into one canonical DAG (Share nodes in entries resolve against the primary table,
as in decompilation), then:
* count entries equal to a subterm of the primary roots, or to a table entry;
* re-encode every entry optimally with the primary table as a fixed dictionary
  at its current index widths (`Prep.materializeWith`), checking that the output
  re-expands to the same terms and that its bytes equal the predicted `C_M`;
* deduplicate equal entries. -/
def metaSharingAnalysis (c : Constant) (entries : Array (Expr × Nat)) :
    Except String MSAnalysis := do
  let limits : Ix.Sharing.Exact.Limits :=
    { maxNodes := 1 <<< 24, maxExprVisits := 1 <<< 28, maxMaterialize := 1 <<< 28,
      maxDepth := 1 <<< 16 }
  let es := entries.map (·.1)
  let primRoots := Ix.Sharing.Exact.constantInfoRoots c.info
  let ex ← (Ix.Sharing.Exact.expand limits c.sharing (primRoots ++ es) true).mapError toString
  let k := primRoots.size
  let metaIds := ex.roots.extract k ex.roots.size
  let n := ex.dag.size
  let mut reach : Array Bool := Array.replicate n false
  let mut stack : Array Nat := ex.roots.extract 0 k
  while !stack.isEmpty do
    let t := stack.back!
    stack := stack.pop
    if reach[t]! then continue
    reach := reach.set! t true
    stack := stack ++ (ex.dag.node t).children
  let (entryIds, _, _) ← (Ix.Sharing.Exact.reexpand limits ex.dag c.sharing #[]).mapError toString
  let mut index : Array (Option Nat) := Array.replicate n none
  for i in [0:entryIds.size] do
    let t := entryIds[i]!
    if (index[t]!).isNone then index := index.set! t (some i)
  let width := Ix.Sharing.Exact.widthsOfIndex index
  let p := Ix.Sharing.Exact.Prep.ofDag ex.dag
  let (out, cost, _) ← (p.materializeWith index width metaIds limits).mapError toString
  let (_, outIds, _) ← (Ix.Sharing.Exact.reexpand limits ex.dag c.sharing out).mapError toString
  unless outIds == metaIds do throw "re-encoded entries do not expand to the original entries"
  let outBytes := out.foldl (fun a e => a + (Ixon.serExpr e).size) 0
  let reenc := metaIds.foldl (fun a t => a + cost[t]!) 0
  unless outBytes == reenc do throw s!"re-encoded bytes {outBytes} differ from C_M {reenc}"
  let mut seen : Std.HashSet Nat := {}
  let mut r : MSAnalysis := { constants := 1, entries := entries.size, reenc }
  for i in [0:metaIds.size] do
    let t := metaIds[i]!
    let b := entries[i]!.2
    let refs := countShareRefs entries[i]!.1 (0, 0, 0)
    r := { r with
      bytes := r.bytes + b, unshared := r.unshared + p.base[t]!
      shareNodes := r.shareNodes + refs.1 + refs.2.1 + refs.2.2
      matched := r.matched + (if reach[t]! then 1 else 0)
      matchedBytes := r.matchedBytes + (if reach[t]! then b else 0)
      matchedTable := r.matchedTable + (if (index[t]!).isSome then 1 else 0) }
    unless seen.contains t do
      seen := seen.insert t
      r := { r with distinct := r.distinct + 1, bytesDedup := r.bytesDedup + b,
                    reencDedup := r.reencDedup + cost[t]! }
  return r

/-- Byte categories of the whole file. -/
def metaCatNames : Array String := #[
  "header: version, consts Merkle root, main, assumptions",
  "§1 blobs: count, addresses, length prefixes",
  "§1 blobs: payload",
  "§2 constants: count, addresses, length prefixes",
  "§2 constants: bodies (the anonymous constants)",
  "§3 anonymous hints",
  "§4 names: count and addresses",
  "§4 names: components (tag, parent address, string/number bytes)",
  "§5 Named: count, name and constant keys",
  "§5 Named: per-name hints",
  "§5 Named: metadata blob length prefixes",
  "§5 ConstantMeta info (variant fields, name indices, root indices)",
  "§5 ExprMeta arena",
  "§5 metaSharing expressions (with count)",
  "§5 metaRefs (with count)",
  "§5 metaUnivs (with count)",
  "§5 univPatches (with count)",
  "§5 original: tag and address",
  "§5 original ConstantMeta info",
  "§5 original ExprMeta arena",
  "§5 original metaSharing expressions",
  "§5 original metaRefs",
  "§5 original metaUnivs",
  "§5 original univPatches",
  "§6 comms"]

structure MetaStudy where
  fileSize : Nat := 0
  cats : Array Nat := Array.replicate 25 0
  blobs : Nat := 0
  consts : Nat := 0
  names : Nat := 0
  named : Nat := 0
  withOriginal : Nat := 0
  comms : Nat := 0
  kindBytes : Array Nat := Array.replicate 9 0
  kindCount : Array Nat := Array.replicate 9 0
  okindBytes : Array Nat := Array.replicate 9 0
  okindCount : Array Nat := Array.replicate 9 0
  nonEmpty : Nat := 0
  nonEmptyOrig : Nat := 0
  entryCounts : Array Nat := #[]
  ms : MSAnalysis := {}
  msOrig : MSAnalysis := {}
  nRefs : Nat := 0
  nUnivs : Nat := 0
  errors : Array String := #[]
  msEntries : Nat := 0
  msBytes : Nat := 0
  msOrigEntries : Nat := 0
  /-- Non-empty metaSharing tables: (§4 name index, §2 rank, entries, bytes). -/
  nonEmptyList : Array (Nat × Nat × Nat × Nat) := #[]
  nonEmptyNameAddrs : Array Address := #[]
  arenaP : ArenaStudy := {}
  arenaO : ArenaStudy := {}
  deriving Inhabited

def MetaStudy.bump (st : MetaStudy) (cat n : Nat) : MetaStudy :=
  { st with cats := st.cats.modify cat (· + n) }

/-- Add one `ConstantMeta` breakdown to the totals (`orig` for `Named.original`). -/
def MetaStudy.addMeta (st : MetaStudy) (mb : MetaBreak) (orig : Bool) : MetaStudy :=
  let base := if orig then 18 else 11
  let st := st.bump base mb.info |>.bump (base + 1) mb.arena |>.bump (base + 2) mb.sharingBytes
    |>.bump (base + 3) mb.refs |>.bump (base + 4) mb.univs |>.bump (base + 5) mb.patches
  let z (x y : Array Nat) := (x.zip y).map fun (p, q) => p + q
  if orig then
    { st with okindBytes := z st.okindBytes mb.kindBytes, okindCount := z st.okindCount mb.kindCount,
              arenaO := st.arenaO.add mb.ast }
  else
    { st with kindBytes := z st.kindBytes mb.kindBytes, kindCount := z st.kindCount mb.kindCount,
              nRefs := st.nRefs + mb.nRefs, nUnivs := st.nUnivs + mb.nUnivs,
              arenaP := st.arenaP.add mb.ast }

/-- Binary search for an address in the ascending §2 address array. -/
def findRank (addrs : Array Address) (a : Address) : Option Nat := Id.run do
  let mut lo := 0
  let mut hi := addrs.size
  while lo < hi do
    let mid := (lo + hi) / 2
    match Address.cmpBytes addrs[mid]! a with
    | .lt => lo := mid + 1
    | .gt => hi := mid
    | .eq => return some mid
  return none

def liftExcept (e : Except String α) : IO α :=
  match e with | .ok a => pure a | .error err => throw (IO.userError err)

def metaStudy (path : String) (progress : Nat) : IO MetaStudy := do
  let buf ← IO.FS.readBinFile path
  let mut st : MetaStudy := { fileSize := buf.size }
  -- Header.
  let (_, off) ← liftExcept <| runAt buf 0 do
    let _ ← Ixon.getTagN 4
    let _ ← Ixon.Serialize.get (α := Address)
    if (← Ixon.getU8) == 1 then let _ ← Ixon.Serialize.get (α := Address)
    let n := (← Ixon.getTagN 0).value.toNat
    for _ in [0:n] do let _ ← Ixon.Serialize.get (α := Address)
  st := st.bump 0 off
  -- §1 blobs.
  let (nb, o2) ← liftExcept <| runAt buf off do return (← Ixon.getTagN 0).value.toNat
  let mut cur := o2
  let mut ovh := o2 - off
  let mut payload := 0
  for _ in [0:nb] do
    let (len, o) ← liftExcept <| runAt buf cur do
      let _ ← Ixon.Serialize.get (α := Address)
      return (← Ixon.getTagN 0).value.toNat
    ovh := ovh + (o - cur)
    payload := payload + len
    cur := o + len
  st := { (st.bump 1 ovh |>.bump 2 payload) with blobs := nb }
  IO.println s!"[meta] blobs {nb}, {payload} payload bytes"
  -- §2 constants.
  let s2 := cur
  let (nc, o3) ← liftExcept <| runAt buf cur do return (← Ixon.getTagN 0).value.toNat
  cur := o3
  let mut addrs : Array Address := Array.mkEmpty nc
  let mut offs : Array Nat := Array.mkEmpty nc
  let mut bodies := 0
  for _ in [0:nc] do
    let ((a, len), o) ← liftExcept <| runAt buf cur do
      let a ← Ixon.Serialize.get (α := Address)
      return (a, (← Ixon.getTagN 0).value.toNat)
    addrs := addrs.push a
    offs := offs.push o
    bodies := bodies + len
    cur := o + len
  st := { (st.bump 3 (cur - s2 - bodies) |>.bump 4 bodies) with consts := nc }
  IO.println s!"[meta] constants {nc}, {bodies} body bytes"
  -- §3 anonymous hints.
  let s3 := cur
  let (_, o4) ← liftExcept <| runAt buf cur do
    let n := (← Ixon.getTagN 0).value.toNat
    for _ in [0:n] do
      let _ ← Ixon.getTagN 0
      let _ ← Ixon.getFusedHint
  cur := o4
  st := st.bump 5 (cur - s3)
  -- §4 names: keep the reverse index for name-indexed metadata.
  let s4 := cur
  let (nn, o5) ← liftExcept <| runAt buf cur do return (← Ixon.getTagN 0).value.toNat
  cur := o5
  let mut rev : Ixon.NameReverseIndex := Array.mkEmpty nn
  let mut comp := 0
  for _ in [0:nn] do
    let (a, o) ← liftExcept <| runAt buf cur do Ixon.Serialize.get (α := Address)
    rev := rev.push a
    let (_, o') ← liftExcept <| runAt buf o do
      match ← Ixon.getU8 with
      | 0 => pure ()
      | 1 | 2 =>
        let _ ← Ixon.Serialize.get (α := Address)
        let len := (← Ixon.getTagN 0).value.toNat
        let _ ← Ixon.getBytes len
      | t => throw s!"invalid name component tag {t}"
    comp := comp + (o' - o)
    cur := o'
  st := { (st.bump 6 (cur - s4 - comp) |>.bump 7 comp) with names := nn }
  IO.println s!"[meta] names {nn}"
  -- §5 Named.
  let (nm, o6) ← liftExcept <| runAt buf cur do return (← Ixon.getTagN 0).value.toNat
  st := st.bump 8 (o6 - cur)
  cur := o6
  -- Primary constant of a named entry: its constant, or the block of a projection.
  let primary (rank : Nat) : Except String Constant := do
    let c ← Ixon.deConstantAt buf offs[rank]!
    let blk? : Option Address := match c.info with
      | .iPrj p => some p.block | .rPrj p => some p.block
      | .dPrj p => some p.block | .cPrj p => some p.block
      | _ => none
    match blk? with
    | none => pure c
    | some blk =>
      match findRank addrs blk with
      | some r => Ixon.deConstantAt buf offs[r]!
      | none => throw "projection block not stored"
  let t0 ← IO.monoMsNow
  for i in [0:nm] do
    let ((nameIdx, rank), o) ← liftExcept <| runAt buf cur do
      let ni := (← Ixon.getTagN 0).value.toNat
      return (ni, (← Ixon.getTagN 0).value.toNat)
    st := st.bump 8 (o - cur)
    let (_, oh) ← liftExcept <| runAt buf o Ixon.getFusedOptHint
    st := st.bump 9 (oh - o)
    let (len, ob) ← liftExcept <| runAt buf oh do return (← Ixon.getTagN 0).value.toNat
    st := st.bump 10 (ob - oh)
    let (mb, om) ← liftExcept <| runAt buf ob (getMetaBreak rev)
    st := { st.addMeta mb false with
      named := st.named + 1, msEntries := st.msEntries + mb.sharing.size
      msBytes := st.msBytes + mb.sharing.foldl (fun a x => a + x.2) 0 }
    let (tag, ot) ← liftExcept <| runAt buf om Ixon.getU8
    let mut endOff := ot
    let mut origMb : Option (MetaBreak × Address) := none
    if tag == 1 then
      let (oa, oo) ← liftExcept <| runAt buf ot (Ixon.Serialize.get (α := Address))
      let (omb, oe) ← liftExcept <| runAt buf oo (getMetaBreak rev)
      st := { (st.bump 17 (oo - om)).addMeta omb true with
        withOriginal := st.withOriginal + 1, msOrigEntries := st.msOrigEntries + omb.sharing.size }
      origMb := some (omb, oa)
      endOff := oe
    else if tag == 0 then
      st := st.bump 17 (ot - om)
    else throw (IO.userError s!"invalid Named.original tag {tag}")
    unless endOff - ob == len do
      throw (IO.userError s!"§5 entry {i}: blob length {len}, parsed {endOff - ob}")
    cur := endOff
    -- metaSharing analysis.
    if !mb.sharing.isEmpty then
      st := { st with
        nonEmpty := st.nonEmpty + 1
        entryCounts := st.entryCounts.push mb.sharing.size
        nonEmptyList := st.nonEmptyList.push
          (nameIdx, rank, mb.sharing.size, mb.sharing.foldl (fun a x => a + x.2) 0)
        nonEmptyNameAddrs := st.nonEmptyNameAddrs.push (rev[nameIdx]?.getD default) }
      match primary rank >>= fun c => metaSharingAnalysis c mb.sharing with
      | .ok r => st := { st with ms := st.ms.add r }
      | .error e => st := { st with errors := st.errors.push s!"named entry {i} (rank {rank}): {e}" }
    if let some (omb, oa) := origMb then
      if !omb.sharing.isEmpty then
        st := { st with nonEmptyOrig := st.nonEmptyOrig + 1 }
        match findRank addrs oa with
        | none => st := { st with errors := st.errors.push s!"named entry {i}: original constant not stored" }
        | some r =>
          match primary r >>= fun c => metaSharingAnalysis c omb.sharing with
          | .ok res => st := { st with msOrig := st.msOrig.add res }
          | .error e => st := { st with errors := st.errors.push s!"named entry {i} original: {e}" }
    if progress > 0 && (i + 1) % progress == 0 then
      IO.println s!"[meta] named {i + 1}/{nm}, {(← IO.monoMsNow) - t0} ms, metaSharing constants {st.nonEmpty}"
      (← IO.getStdout).flush
  -- §6 comms.
  let s6 := cur
  let (nco, o7) ← liftExcept <| runAt buf cur do
    let n := (← Ixon.getTagN 0).value.toNat
    for _ in [0:n] do
      let _ ← Ixon.Serialize.get (α := Address)
      let _ ← Ixon.getComm
    return n
  cur := o7
  st := { st.bump 24 (cur - s6) with comms := nco }
  unless cur == buf.size do
    throw (IO.userError s!"scanner stopped at {cur}, file has {buf.size} bytes")
  return st

/-- Cross-check of the scanner against a full `deEnv` load (small files only). -/
def metaCrossCheck (path : String) (st : MetaStudy) : IO String := do
  let buf ← IO.FS.readBinFile path
  let env ← IO.ofExcept (Ixon.deEnv buf)
  let mut nonEmpty := 0
  let mut entries := 0
  let mut bytes := 0
  let mut nRefs := 0
  let mut nUnivs := 0
  let mut withOrig := 0
  let mut origEntries := 0
  for (_, nmd) in env.named do
    let m := nmd.constMeta
    if !m.metaSharing.isEmpty then nonEmpty := nonEmpty + 1
    entries := entries + m.metaSharing.size
    bytes := bytes + m.metaSharing.foldl (fun a e => a + (Ixon.serExpr e).size) 0
    nRefs := nRefs + m.metaRefs.size
    nUnivs := nUnivs + m.metaUnivs.size
    if let some (_, om) := nmd.original then
      withOrig := withOrig + 1
      origEntries := origEntries + om.metaSharing.size
  let scanEntries := st.msEntries
  let sharingExprBytes := st.msBytes
  let ok := env.named.size == st.named && env.blobs.size == st.blobs &&
    env.consts.size == st.consts && nonEmpty == st.nonEmpty && entries == scanEntries &&
    bytes == sharingExprBytes && nRefs == st.nRefs && nUnivs == st.nUnivs &&
    withOrig == st.withOriginal && origEntries == st.msOrigEntries
  return s!"- Cross-check against a full `Ixon.deEnv` load: named {env.named.size} vs {st.named}, blobs {env.blobs.size} vs {st.blobs}, constants {env.consts.size} vs {st.consts}, non-empty metaSharing {nonEmpty} vs {st.nonEmpty}, metaSharing entries {entries} vs {scanEntries}, metaSharing expression bytes (`serExpr`) {bytes} vs {sharingExprBytes}, metaRefs {nRefs} vs {st.nRefs}, metaUnivs {nUnivs} vs {st.nUnivs}, entries with `original` {withOrig} vs {st.withOriginal}, original metaSharing entries {origEntries} vs {st.msOrigEntries}: **{if ok then "all equal" else "DIFFERENT"}**.\n"

/-- Unsigned percentage with two decimals. -/
def fmtPct2 (part whole : Nat) : String :=
  if whole == 0 then "0" else
    let q := (part * 10000 + whole / 2) / whole
    let frac := q % 100
    s!"{q / 100}.{if frac < 10 then "0" else ""}{frac}%"

/-- ExprMeta arena structure: child deltas and duplication (primary and
`original` arenas together; the split is given in a line). -/
def arenaReport (st : MetaStudy) : String := Id.run do
  let file := st.fileSize
  let a := st.arenaP.add st.arenaO
  let pc (x : Nat) : String := fmtPct2 x file
  let mut md := "\n### ExprMeta arena structure: child deltas and duplication\n\n"
  md := md ++ s!"- Arenas: {a.arenas} ({st.arenaO.arenas} of them in `original` metadata); nodes {a.nodes}; node bytes {a.bytes} ({pc a.bytes} of the file; the per-arena count prefixes are not included). Children that do not point strictly backward (any slot): {a.notBackward}.\n"
  let kindSum := st.kindBytes.foldl (· + ·) 0 + st.okindBytes.foldl (· + ·) 0
  md := md ++ s!"- Node bytes equal the per-kind arena bytes above ({kindSum}): **{if kindSum == a.bytes then "yes" else "NO"}**.\n\n"
  md := md ++ "Child deltas (parent index − child index) per child slot, and the child-field bytes today (`Tag0` of the absolute index) and as backward deltas with TagN-byte widths:\n\n| slot | children | Δ = 1 | 2–7 | 8–127 | 128–1023 | 1024–16383 | ≥ 16384 | not backward | bytes today | delta bytes | change | change, % of file |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n"
  let mut tot : Array Nat := Array.replicate 10 0
  for h : s in [0:arenaSlotNames.size] do
    let row := (List.range 10).toArray.map fun j => a.slots[s * 10 + j]!
    tot := (tot.zip row).map fun (p, q) => p + q
    let d : Int := (row[9]! : Int) - row[8]!
    md := md ++ s!"| {arenaSlotNames[s]} | {row[0]!} | {row[1]!} | {row[2]!} | {row[3]!} | {row[4]!} | {row[5]!} | {row[6]!} | {row[7]!} | {row[8]!} | {row[9]!} | {d} | {fmtSignedPct2 d file} |\n"
  let dt : Int := (tot[9]! : Int) - tot[8]!
  md := md ++ s!"| **all slots** | {tot[0]!} | {tot[1]!} | {tot[2]!} | {tot[3]!} | {tot[4]!} | {tot[5]!} | {tot[6]!} | {tot[7]!} | {tot[8]!} | {tot[9]!} | {dt} | {fmtSignedPct2 dt file} |\n"
  let appT := (List.range 10).toArray.map fun j => a.slots[j]! + a.slots[10 + j]!
  let da : Int := (appT[9]! : Int) - appT[8]!
  md := md ++ s!"| App slots only | {appT[0]!} | {appT[1]!} | {appT[2]!} | {appT[3]!} | {appT[4]!} | {appT[5]!} | {appT[6]!} | {appT[7]!} | {appT[8]!} | {appT[9]!} | {da} | {fmtSignedPct2 da file} |\n\n"
  md := md ++ s!"- Children that are exactly the immediately preceding node (Δ = 1): {tot[1]!} of {tot[0]!} ({fmtPct2 tot[1]! tot[0]!}); App children: {appT[1]!} of {appT[0]!}.\n\n"
  md := md ++ "Duplication within each arena (bottom-up hash-consing on kind, payload and canonical child IDs; a duplicate is a node whose canonical ID occurred earlier in the same arena):\n\n| nodes | total | duplicates | duplicate bytes | % of file | maximal duplicate subtrees | duplicate nodes in them | bytes in them | % of file |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|\n"
  md := md ++ s!"| all kinds | {a.nodes} | {a.dupNodes} | {a.dupBytes} | {pc a.dupBytes} | {a.maxRoots} | {a.maxNodes} | {a.maxBytes} | {pc a.maxBytes} |\n"
  md := md ++ s!"| App nodes (subtrees rooted at an App) | {a.appNodes} | {a.appDupNodes} | {a.appDupBytes} | {pc a.appDupBytes} | {a.appMaxRoots} | {a.appMaxNodes} | {a.appMaxBytes} | {pc a.appMaxBytes} |\n\n"
  md := md ++ s!"- Distinct nodes per arena summed: {a.nodes - a.dupNodes} of {a.nodes} ({fmtPct2 (a.nodes - a.dupNodes) a.nodes}); distinct App nodes: {a.appNodes - a.appDupNodes} of {a.appNodes}.\n"
  md := md ++ s!"- Maximal duplicate subtree sizes (duplicate nodes): 1: {a.maxHist[0]!}, 2–7: {a.maxHist[1]!}, 8–63: {a.maxHist[2]!}, 64–1023: {a.maxHist[3]!}, ≥ 1024: {a.maxHist[4]!}.\n"
  md := md ++ s!"- Independent check on arenas of at most 256 nodes (duplicates recounted by comparing full subtree strings): agree for {a.checkEq} arenas, **differ for {a.checkNe}**; {a.checkSkip} arenas not checked (more than 256 nodes, or a subtree string over 100,000 characters).\n"
  md := md ++ s!"- Split: primary arenas {st.arenaP.nodes} nodes, {st.arenaP.dupNodes} duplicates ({st.arenaP.dupBytes} B); `original` arenas {st.arenaO.nodes} nodes, {st.arenaO.dupNodes} duplicates ({st.arenaO.dupBytes} B).\n"
  return md

def msRow (label : String) (m : MSAnalysis) (file : Nat) : String :=
  s!"| {label} | {m.constants} | {m.entries} | {m.bytes} ({fmtSignedPct2 m.bytes file |>.drop 1} of file) | {m.unshared} | {m.reenc} | {m.distinct} | {m.bytesDedup} | {m.reencDedup} | {m.matched} ({m.matchedBytes} B) | {m.matchedTable} | {m.shareNodes} |\n"

def metaReport (path : String) (st : MetaStudy) (cross : String) (ms : Nat)
    (names : Array String := #[]) : String := Id.run do
  let file := st.fileSize
  let mut md := s!"## Metadata study: `{path}`\n\n"
  md := md ++ s!"- File: {file} bytes; blobs {st.blobs}; anonymous constants {st.consts}; names {st.names}; Named entries {st.named} ({st.withOriginal} with `original`); comms {st.comms}. Scan time {ms} ms.\n"
  let total := st.cats.foldl (· + ·) 0
  md := md ++ s!"- Byte categories sum to {total} bytes: **{if total == file then "equal to the file size" else "DIFFERENT from the file size"}**.\n"
  md := md ++ cross
  md := md ++ "\n| component | bytes | % of file |\n|---|---:|---:|\n"
  for h : i in [0:metaCatNames.size] do
    md := md ++ s!"| {metaCatNames[i]} | {st.cats[i]!} | {fmtSignedPct2 st.cats[i]! file |>.drop 1} |\n"
  let named := (List.range 17).foldl (fun a i => if i ≥ 8 then a + st.cats[i]! else a) 0 +
    (List.range 25).foldl (fun a i => if i ≥ 17 && i ≤ 23 then a + st.cats[i]! else a) 0
  md := md ++ s!"\n- Section totals: §2 constants {st.cats[3]! + st.cats[4]!} ({fmtSignedPct2 (st.cats[3]! + st.cats[4]!) file |>.drop 1}); §5 Named {named} ({fmtSignedPct2 named file |>.drop 1}); §4 names {st.cats[6]! + st.cats[7]!} ({fmtSignedPct2 (st.cats[6]! + st.cats[7]!) file |>.drop 1}); §1 blobs {st.cats[1]! + st.cats[2]!} ({fmtSignedPct2 (st.cats[1]! + st.cats[2]!) file |>.drop 1}).\n"
  md := md ++ "\nExprMeta arena by node kind (primary metadata; `original` metadata in the last two columns):\n\n| node kind | nodes | bytes | % of file | original nodes | original bytes |\n|---|---:|---:|---:|---:|---:|\n"
  for h : k in [0:arenaKindNames.size] do
    md := md ++ s!"| {arenaKindNames[k]} | {st.kindCount[k]!} | {st.kindBytes[k]!} | {fmtSignedPct2 st.kindBytes[k]! file |>.drop 1} | {st.okindCount[k]!} | {st.okindBytes[k]!} |\n"
  let ec := st.entryCounts.qsort (· < ·)
  md := md ++ s!"\n### metaSharing\n\n- Named entries with non-empty `metaSharing`: {st.nonEmpty} of {st.named}; with non-empty `original` metaSharing: {st.nonEmptyOrig}. Entries per non-empty table: min {ec[0]?.getD 0}, median {pct ec 50}, p90 {pct ec 90}, p99 {pct ec 99}, max {ec.back?.getD 0}.\n"
  md := md ++ s!"- metaRefs entries: {st.nRefs}; metaUnivs entries: {st.nUnivs}.\n"
  unless st.nonEmptyList.isEmpty do
    md := md ++ "\n| Named entry | §2 rank | metaSharing entries | bytes |\n|---|---:|---:|---:|\n"
    for h : i in [0:st.nonEmptyList.size] do
      let (_, rank, n, b) := st.nonEmptyList[i]
      md := md ++ s!"| `{names[i]?.getD "?"}` | {rank} | {n} | {b} |\n"
    md := md ++ "\n"
  md := md ++ s!"- Analysis errors (constants not analysed): {st.errors.size}.\n"
  for e in st.errors.extract 0 10 do md := md ++ s!"  - {e}\n"
  md := md ++ "\n| metadata | constants | entries | current bytes | unshared bytes | re-encoded against the primary table | distinct entries | current, deduplicated | re-encoded, deduplicated | entries equal to a primary subterm | equal to a primary table entry | Share nodes in entries |\n|---|---:|---:|---|---:|---:|---:|---:|---:|---|---:|---:|\n"
  md := md ++ msRow "primary `ConstantMeta`" st.ms file
  md := md ++ msRow "`Named.original`" st.msOrig file
  md := md ++ arenaReport st
  return md

/-! ## Driver -/

structure Opts where
  corpus : String := ""
  md : Option String := none
  csv : Option String := none
  limit : Option Nat := none
  validateMax : Nat := 16777216
  occCheckMax : Nat := 65536
  progress : Nat := 5000
  /-- Run the metadata study instead of the per-constant study. -/
  metaMode : Bool := false
  /-- Cross-check the metadata scanner against a full `deEnv` load. -/
  metaCross : Bool := false

def parseArgs : List String → Opts → Except String Opts
  | [], o => if o.corpus.isEmpty then .error "missing corpus path" else .ok o
  | "--meta" :: rest, o => parseArgs rest { o with metaMode := true }
  | "--meta-crosscheck" :: rest, o => parseArgs rest { o with metaCross := true }
  | "--md" :: p :: rest, o => parseArgs rest { o with md := some p }
  | "--csv" :: p :: rest, o => parseArgs rest { o with csv := some p }
  | "--limit" :: n :: rest, o => parseArgs rest { o with limit := n.toNat? }
  | "--validate-max" :: n :: rest, o =>
    parseArgs rest { o with validateMax := n.toNat?.getD o.validateMax }
  | "--occ-check-max" :: n :: rest, o =>
    parseArgs rest { o with occCheckMax := n.toNat?.getD o.occCheckMax }
  | "--progress" :: n :: rest, o =>
    parseArgs rest { o with progress := n.toNat?.getD o.progress }
  | p :: rest, o =>
    if p.startsWith "--" then .error s!"unknown flag {p}"
    else parseArgs rest { o with corpus := p }

def projBlock? : ConstantInfo → Option Address
  | .iPrj p => some p.block | .cPrj p => some p.block
  | .rPrj p => some p.block | .dPrj p => some p.block
  | _ => none

def main (args : List String) : IO UInt32 := do
  let opts ← match parseArgs args {} with
    | .ok o => pure o
    | .error e =>
      IO.eprintln s!"sharing-study: {e}\nusage: sharing-study <corpus.ixe> [--md p] [--csv p] [--limit n] [--validate-max bytes] [--occ-check-max bytes] [--progress n] [--meta] [--meta-crosscheck]"
      return 2
  if opts.metaMode then
    let t0 ← IO.monoMsNow
    let st ← metaStudy opts.corpus opts.progress
    let t1 ← IO.monoMsNow
    let cross ← if opts.metaCross then metaCrossCheck opts.corpus st else pure ""
    -- Names of the entries with non-empty metaSharing (lazy anonymous loader).
    let names ← if st.nonEmptyNameAddrs.isEmpty then pure #[] else do
      let buf ← IO.FS.readBinFile opts.corpus
      let env ← IO.ofExcept (Ixon.deEnvAnon buf)
      let want : Std.HashSet Address := st.nonEmptyNameAddrs.foldl (·.insert ·) {}
      let mut m : Std.HashMap Address String := {}
      for (nm, _) in env.named do
        if want.contains nm.getHash then m := m.insert nm.getHash (toString nm)
      pure (st.nonEmptyNameAddrs.map fun a => m.getD a "?")
    let md := metaReport opts.corpus st cross (t1 - t0) names
    IO.println md
    if let some p := opts.md then
      IO.FS.writeFile p md
      IO.println s!"[sharing-study] wrote {p}"
    let total := st.cats.foldl (· + ·) 0
    return (if total == st.fileSize && st.errors.isEmpty then 0 else 1)
  let ws := witnesses
  for w in ws do
    match w with
    | .ok w => IO.println s!"[sharing-study] witness {w.label}: unshared {w.unshared} B, canonical {w.canonical} B, MSS {w.mss} B (expected {w.expectedMss}), check {w.check.getD "ok"}, MSS bytes {w.mssHex}"
    | .error e => IO.println s!"[sharing-study] witness FAILED: {e}"
  let t0 ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile opts.corpus
  let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
  let tLoad ← IO.monoMsNow
  IO.println s!"[sharing-study] loaded {opts.corpus}: {bytes.size} bytes, {env.consts.size} constants, {env.named.size} names in {tLoad - t0} ms"
  let entries := env.consts.toArray.qsort fun a b => Address.cmpBytes a.1 b.1 == .lt
  -- Names for anonymous mutual blocks: the least projection name pointing at them.
  let mut blockNames : Std.HashMap Address String := {}
  for (addr, lc) in entries do
    match lc.peekTag with
    | .ok .iPrj | .ok .cPrj | .ok .rPrj | .ok .dPrj =>
      if let .ok c := lc.get then
        if let some blk := projBlock? c.info then
          if let some nm := env.addrToName.get? addr then
            let s := toString nm
            let s := match blockNames.get? blk with
              | some old => if s < old then s else old
              | none => s
            blockNames := blockNames.insert blk s
    | _ => pure ()
  let nameOf (addr : Address) : String :=
    match env.addrToName.get? addr with
    | some n => toString n
    | none => match blockNames.get? addr with
      | some s => s!"{s} [block]"
      | none => "<unnamed>"
  let todo := match opts.limit with
    | some n => entries.extract 0 n
    | none => entries
  let mut rows : Array Row := Array.mkEmpty todo.size
  let mut skipped : Array (String × String) := #[]
  let mut mismatches := 0
  let mut i := 0
  for (addr, lc) in todo do
    i := i + 1
    let name := nameOf addr
    let raw := lc.rawBytes
    let c ← match lc.get with
      | .ok c => pure c
      | .error e =>
        skipped := skipped.push (name, s!"decode: {e}")
        continue
    let s ← IO.monoNanosNow
    match measure addr name raw c opts.validateMax opts.occCheckMax with
    | .error e => skipped := skipped.push (name, e)
    | .ok row =>
      let e ← IO.monoNanosNow
      let row := { row with ns := e - s }
      unless row.rebuildOk do
        mismatches := mismatches + 1
        if mismatches ≤ 10 then
          IO.println s!"[sharing-study] MISMATCH {name} ({row.kind}): stored {row.raw} B / table {row.table}, canonical {row.canonical} B / table {row.canonicalTable}, first diff at {row.firstDiff}"
      if let some e := row.mssErr then
        IO.println s!"[sharing-study] MSS FAILURE {name} ({row.kind}): {e}"
      if row.ns > 2000000000 then
        IO.println s!"[sharing-study] slow: {name} ({row.kind}) {row.ns / 1000000} ms, N={row.n}"
      rows := rows.push row
    if opts.progress > 0 && i % opts.progress == 0 then
      let now ← IO.monoMsNow
      IO.println s!"[sharing-study] {i}/{todo.size} constants, {now - tLoad} ms, mismatches {mismatches}, skipped {skipped.size}"
      (← IO.getStdout).flush
  let tEnd ← IO.monoMsNow
  IO.println s!"[sharing-study] processed {rows.size} constants, skipped {skipped.size}, mismatches {mismatches} in {tEnd - tLoad} ms (total {tEnd - t0} ms)"

  -- Summary ----------------------------------------------------------------
  let withRoots := rows.filter (·.roots > 0)
  let rtFail := rows.filter (!·.roundtripOk)
  let valOk := (rows.filter (·.validated == some true)).size
  let valFail := rows.filter (·.validated == some false)
  let valSkip := rows.filter (·.validated.isNone)
  let occOk := (rows.filter (·.occCheck == some true)).size
  let occFail := rows.filter (·.occCheck == some false)
  let occSkip := (rows.filter (·.occCheck.isNone)).size
  let worse := withRoots.filter fun r => r.raw > r.unshared
  let sumRaw := rows.foldl (· + ·.raw) 0
  let sumUn := rows.foldl (· + ·.unshared) 0
  let mut md := "## Results\n\n"
  md := md ++ s!"- Corpus: `{opts.corpus}` ({bytes.size} bytes), {env.consts.size} stored constants (distinct addresses), {env.named.size} names.\n"
  md := md ++ s!"- Constants processed: {rows.size}; skipped: {skipped.size}; with at least one expression root: {withRoots.size}.\n"
  md := md ++ s!"- Harness wall time: load {tLoad - t0} ms, measurement {tEnd - tLoad} ms, total {tEnd - t0} ms.\n"
  md := md ++ s!"- Canonical rebuild (`buildConstantWithSharing compilerSharingLimits` on the expanded roots, then `serConstant`) differs from `rawBytes`: **{mismatches}** constants (0 when the corpus was compiled on the canonical route).\n"
  md := md ++ s!"- Decode/encode roundtrip (`serConstant ∘ get`) differs from `rawBytes`: {rtFail.size} constants.\n"
  md := md ++ s!"- Compositional unshared size checked against `serConstant` of the real unshared Constant: {valOk} equal, {valFail.size} different, {valSkip.size} not checked (unshared roots > {opts.validateMax} bytes).\n"
  md := md ++ s!"- `usageCount` (occ) checked against a brute-force walk of the fully expanded roots: {occOk} equal, {occFail.size} different, {occSkip} not checked (unshared roots > {opts.occCheckMax} bytes).\n"
  md := md ++ s!"- Constants whose stored bytes exceed their unshared bytes: {worse.size}.\n"
  md := md ++ s!"- Total `rawBytes.size`: {sumRaw}; total canonical Constant bytes: {rows.foldl (· + ·.canonical) 0}; total unshared Constant bytes: {sumUn}.\n\n"
  unless mismatches == 0 do
    md := md ++ "### Rebuild mismatches (first 20)\n\n| constant | kind | stored B | stored table | canonical B | canonical table | first diff |\n|---|---|---:|---:|---:|---:|---:|\n"
    for r in (rows.filter (!·.rebuildOk)).extract 0 20 do
      md := md ++ s!"| `{r.name}` | {r.kind} | {r.raw} | {r.table} | {r.canonical} | {r.canonicalTable} | {r.firstDiff} |\n"
    md := md ++ "\n"
  unless valFail.isEmpty do
    md := md ++ "### Unshared-size validation failures (first 20)\n\n| constant | compositional | serConstant |\n|---|---:|---:|\n"
    for r in valFail.extract 0 20 do
      md := md ++ s!"| `{r.name}` | {r.unshared} | {r.serUnsharedSize} |\n"
    md := md ++ "\n"
  unless valSkip.isEmpty do
    md := md ++ "### Constants whose unshared size was not validated by serialization\n\n| constant | kind | unshared bytes | stored bytes |\n|---|---|---:|---:|\n"
    for r in (valSkip.qsort fun a b => a.unshared > b.unshared).extract 0 20 do
      md := md ++ s!"| `{r.name}` | {r.kind} | {r.unshared} | {r.raw} |\n"
    md := md ++ "\n"
  unless skipped.isEmpty do
    md := md ++ "### Skipped constants\n\n| constant | reason |\n|---|---|\n"
    for (n, why) in skipped do
      md := md ++ s!"| `{n}` | {why} |\n"
    md := md ++ "\n"
  md := md ++ s!"### Distributions over constants with at least one root ({withRoots.size})\n\n"
  md := md ++ distTable withRoots ++ "\n\n"
  md := md ++ s!"### Distributions over all processed constants ({rows.size}, projections included)\n\n"
  md := md ++ distTable rows ++ "\n\n"
  md := md ++ s!"### Candidate-count buckets (R1+R2), constants with at least one root ({withRoots.size}), cumulative\n\n"
  md := md ++ bucketTable withRoots (·.cand) ++ "\n\n"
  md := md ++ s!"### Candidates with size > 3, constants with at least one root, cumulative\n\n"
  md := md ++ bucketTable withRoots (·.cand3) ++ "\n\n"
  md := md ++ "### Ten constants with the most candidates\n\n| # | constant | kind | `N` | `occ≥2` | candidates | size>2 | size>3 | table | stored B | unshared B | max telescope |\n|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n"
  let top := (rows.qsort fun a b => a.cand > b.cand || (a.cand == b.cand && a.name < b.name)).extract 0 10
  for h : j in [0:top.size] do
    let r := top[j]
    let k := if r.detail.isEmpty then r.kind else s!"{r.kind} ({r.detail})"
    md := md ++ s!"| {j + 1} | `{r.name}` | {k} | {r.n} | {r.occ2} | {r.cand} | {r.cand2} | {r.cand3} | {r.table} | {r.raw} | {r.unshared} | {max r.maxApp (max r.maxLam r.maxAll)} |\n"
  md := md ++ "\n### Totals by ConstantInfo kind\n\n| kind | constants | `rawBytes.size` | unshared bytes | stored/unshared | table entries | candidates | stored > unshared |\n|---|---:|---:|---:|---:|---:|---:|---:|\n"
  for k in kindOrder do
    let ks := rows.filter (·.kind == k)
    unless ks.isEmpty do
      let r := ks.foldl (· + ·.raw) 0
      let u := ks.foldl (· + ·.unshared) 0
      let t := ks.foldl (· + ·.table) 0
      let cnd := ks.foldl (· + ·.cand) 0
      let w := (ks.filter fun x => x.raw > x.unshared).size
      md := md ++ s!"| {k} | {ks.size} | {r} | {u} | {fmtPct r u} | {t} | {cnd} | {w} |\n"
  md := md ++ s!"| **all** | {rows.size} | {sumRaw} | {sumUn} | {fmtPct sumRaw sumUn} | {rows.foldl (· + ·.table) 0} | {rows.foldl (· + ·.cand) 0} | {worse.size} |\n\n"
  md := md ++ "### Longest telescopes\n\n"
  let maxBy (f : Row → Nat) : String :=
    match rows.foldl (init := none) (fun (acc : Option Row) r =>
        match acc with | some a => if f r > f a then some r else acc | none => some r) with
    | some r => s!"{f r} (`{r.name}`)"
    | none => "0"
  md := md ++ s!"- App spine: {maxBy (·.maxApp)}\n- Lam telescope: {maxBy (·.maxLam)}\n- All telescope: {maxBy (·.maxAll)}\n\n"
  md := md ++ "### Slowest constants in this harness (all steps above, per constant)\n\n| constant | kind | ms | `N` | stored B |\n|---|---|---:|---:|---:|\n"
  for r in (rows.qsort fun a b => a.ns > b.ns).extract 0 5 do
    md := md ++ s!"| `{r.name}` | {r.kind} | {r.ns / 1000000} | {r.n} | {r.raw} |\n"
  md := md ++ "\n" ++ mssReport rows ws
  IO.println md
  if let some p := opts.md then
    IO.FS.writeFile p md
    IO.println s!"[sharing-study] wrote {p}"
  if let some p := opts.csv then
    let h ← IO.FS.Handle.mk p .write
    h.putStrLn csvHeader
    for r in rows do h.putStrLn (csvLine r)
    h.flush
    IO.println s!"[sharing-study] wrote {p}"
  let mssFail := rows.any (·.mssErr.isSome) || ws.any (fun w => match w with
    | .ok w => w.check.isSome
    | .error _ => true) || negativeControls.any (!·.2)
  return (if mismatches == 0 && skipped.isEmpty && valFail.isEmpty && rtFail.isEmpty &&
    occFail.isEmpty && !mssFail &&
    !rows.any (fun r => mssRefTotal r != r.mssDegSum) then 0 else 1)

end Benchmarks.SharingStudy

def main (args : List String) : IO UInt32 := Benchmarks.SharingStudy.main args
