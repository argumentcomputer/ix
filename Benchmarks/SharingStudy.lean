import Ix.CompileM
import Ix.Sharing.Exact

/-!
# Sharing corpus study (gate P1.5 of `docs/sharing-minimum.md`)

Loads a serialized `Ixon.Env` (`.ixe`) and, for every stored constant:

1. Expands the stored sharing table left to right. Entry `i` may reference
   only entries `j < i`; each `Share j` is replaced by the *same* in-memory
   expansion of entry `j`, so repeated indices share one subtree and the
   expanded roots form a DAG whose size is linear in the stored bytes.
   The ordered roots come from `Ix.CompileM.constantInfoRootExprs`.
2. Rebuilds the constant with the production path
   (`Ix.CompileM.buildConstantWithSharing` on the expanded roots, i.e. the
   current heuristic) and checks that `Ixon.serConstant` reproduces the
   stored bytes exactly. It also checks the plain decode/encode roundtrip.
3. Hash-conses the expanded roots with `Ix.Sharing.analyzeBlock` (blake3
   Merkle hashes; hash equality is treated as structural equality) and
   measures, per constant:
   * `N`: distinct subterms, leaves included;
   * `occ(t)`: `SubtermInfo.usageCount`, i.e. structural occurrences in the
     fully expanded roots, counted through every DAG edge with multiplicity
     plus one per root occurrence (`countRootUsages` +
     `propagateUsageCounts`);
   * `size(t)`: the standalone unshared `putExpr` length of `t`, computed
     compositionally on the DAG with the App/Lam/All telescope rules;
   * candidates after R1/R2 (`occ ≥ 2 ∧ size > 1`) and those with size > 2
     and > 3;
   * the unshared complete-Constant size, the current table size and the
     stored byte length; the longest App/Lam/All telescope.
4. Validates the compositional unshared size against `serConstant` of the
   actual unshared constant whenever the unshared root bytes are at most
   `--validate-max` (so no exponential tree is ever serialized).
5. Checks `usageCount` against a brute-force walk of the expanded roots as
   trees whenever the unshared root bytes are at most `--occ-check-max`.
6. Builds the "maximal structural sharing" (MSS) encoding (see `mssBuild`),
   serializes it with `serConstant`, decodes and expands it again and checks
   the expanded roots equal the original ones exactly. The plan §2 witnesses
   are run through the same path at startup.
7. Classifies the MSS candidates as certain-stored, certain-excluded or
   uncertain under a uniform Share width `w ∈ {1, 2, 3}` and measures the
   components of uncertain nodes (see `classify`), and counts the Share
   references of the stored encoding by index width.
8. Prices the Share references of the MSS encoding under seven width
   schemes (current index tiers; one width per constant from the entry
   count; the same with a 1-byte class; one width per constant with a
   nibble-sized index in the tag byte; three alternative index tiers),
   see `schemeReport`.
9. Runs W1's exact uniform-width optimizer (`Ix.Sharing.Exact`) for
   `w ∈ {1, 2, 3}` under explicit limits, serializes and checks its output, and
   compares its classes with a reimplementation of its definitions
   (`classifyW1Mode`), see `uniformReport`.
10. Reprices every `Tag4`, `Tag0` and `Tag2` integer of the stored encoding under
   TagN, TagN-byte and the Tag2 variant, see `ladConstant` and `tagNReport`.

```
lake exe sharing-study <corpus.ixe> [--md <path>] [--csv <path>]
                       [--limit <n>] [--validate-max <bytes>]
                       [--occ-check-max <bytes>] [--progress <n>]
                       [--no-uniform] [--uni-max-states <n>]
```
-/

namespace Benchmarks.SharingStudy

open Ixon (Expr Constant ConstantInfo MutConst)

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
  /-- `sz` minus this telescope's Tag4 header. -/
  payload : Nat := 0
  deriving Inhabited

def tag4Size (n : Nat) : Nat := Ix.Sharing.tag4EncodedSize n.toUInt64
def tag0Size (n : Nat) : Nat := Ix.Sharing.tag0EncodedSize n.toUInt64

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
  let acc := match ptrToHash.get? (Ix.Sharing.exprPtr e) with
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
`Tag4(#args)`, its head, then its arguments; Lam/All telescopes write
`Tag4(#binders)`, then one contract byte and the type per binder, then the
body. Prj/Let/leaves are the node header (`SubtermInfo.baseSize`, which is
`putNodeHeader`, i.e. the full `putExpr` for leaves) plus the children. -/
def dagStats (res : Ix.Sharing.AnalyzeResult) (roots : Array Expr) (occCheckMax : Nat) :
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
    match res.ptrToHash.get? (Ix.Sharing.exprPtr r) with
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

/-- Share references in an unexpanded expression, bucketed by the index width
they pay: `< 8` (1 byte), `8..255` (2), `≥ 256` (3 below 65536). -/
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
  countShareRefsBy 8 256 e acc

/-! ## Maximal structural sharing (MSS)

The candidate polynomial rule measured for the coordinator's follow-up:

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
4. Materialize with the production helpers `Ix.Sharing.buildSharingEntries`
   and `Ix.Sharing.rewriteExprs`, then serialize with `serConstant`. -/

structure MssResult where
  /-- Rewritten table in emission order. -/
  table : Array Expr := #[]
  /-- Rewritten roots. -/
  roots : Array Expr := #[]
  /-- Stored terms that never occur as a root and whose every DAG occurrence
  is a same-family telescope continuation: the function child of an App when
  the term is an App, or the body of a Lam (All) when the term is a Lam (All). -/
  cont : Nat := 0
  /-- Continuation-only entries whose MSS entry body, minus its Tag4 header, is
  at most 2 bytes. -/
  contP2 : Nat := 0
  /-- Continuation-only entries whose unshared payload (`NodeSz.payload`) is at
  most 2 bytes. -/
  contP2u : Nat := 0
  /-- Share nodes in the MSS table and roots by index width (`< 8`,
  `8..255`, `≥ 256`), counted on the materialized encoding. -/
  refs : Nat × Nat × Nat := (0, 0, 0)
  /-- Share nodes by index `< 15`, `15..4110`, `≥ 4111` (scheme E tiers). -/
  refsE : Nat × Nat × Nat := (0, 0, 0)
  /-- Share nodes by index `< 8`, `8..1031`, `≥ 1032` (scheme F tiers). -/
  refsF : Nat × Nat × Nat := (0, 0, 0)
  /-- Share nodes by index `< 14`, `14..269`, `≥ 270` (scheme G tiers). -/
  refsG : Nat × Nat × Nat := (0, 0, 0)
  /-- `Σ deg(t)` over the stored terms (expected to equal the Share count). -/
  degSum : Nat := 0
  deriving Inhabited

/-- Telescope count `putExpr` writes for an expression. -/
def teleCount : Expr → Nat
  | e@(.app ..) => e.collectAppArgs.1.length
  | e@(.lam ..) => e.collectLamBinders.1.length
  | e@(.all ..) => e.collectAllBinders.1.length
  | _ => 0

def mssBuild (res : Ix.Sharing.AnalyzeResult) (sizes : Std.HashMap Address NodeSz)
    (roots : Array Expr) : Except String MssResult := do
  -- 1. Compact-DAG indegree with multiplicity plus root occurrences, and whether
  --    every occurrence is a same-family telescope continuation.
  let mut deg : Std.HashMap Address Nat := Std.HashMap.emptyWithCapacity res.infoMap.size
  let mut nonCont : Std.HashSet Address := {}
  for r in roots do
    let some h := res.ptrToHash.get? (Ix.Sharing.exprPtr r) | throw "root not analyzed"
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
  let st := Ix.Sharing.buildSharingEntries order res.infoMap res.ptrToHash
  let newRoots := Ix.Sharing.rewriteExprs roots st.hashToIdx res.ptrToHash
  -- 6. Continuation-only entries.
  let refs := newRoots.foldl (fun acc e => countShareRefs e acc)
    (st.sharingVec.foldl (fun acc e => countShareRefs e acc) (0, 0, 0))
  let degSum := stored.foldl (fun a h => a + deg.getD h 0) 0
  let refsE := newRoots.foldl (fun acc e => countShareRefsBy 15 4111 e acc)
    (st.sharingVec.foldl (fun acc e => countShareRefsBy 15 4111 e acc) (0, 0, 0))
  let mut out : MssResult :=
    { table := st.sharingVec, roots := newRoots, refs, refsE, degSum,
      refsF := newRoots.foldl (fun acc e => countShareRefsBy 8 1032 e acc)
        (st.sharingVec.foldl (fun acc e => countShareRefsBy 8 1032 e acc) (0, 0, 0)),
      refsG := newRoots.foldl (fun acc e => countShareRefsBy 14 270 e acc)
        (st.sharingVec.foldl (fun acc e => countShareRefsBy 14 270 e acc) (0, 0, 0)) }
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
  let pa := Ix.Sharing.exprPtr a
  let pb := Ix.Sharing.exprPtr b
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

/-! ## Uniform-reference-width classification

For a fixed Share width `w` (every reference costs `w`; the table-count prefix
is ignored), each candidate `t` (`deg ≥ 2`, unshared size > 1) is classified
with the gain `g(n, H, b) = (n−1)·b + (H−1)·hdr(t) − n·w`:

* CERTAIN-STORED if `g(deg, headdeg, payloadMin) > 0`;
* CERTAIN-EXCLUDED if `g(occ, occ, payloadMax) < 0`, or `t` is a leaf with
  `(occ−1)·size < occ·w`;
* UNCERTAIN otherwise.

`headdeg` counts the `deg` occurrences that pay `t`'s own header: an App that
is the function child of an App, and a Lam (All) that is the body of a Lam
(All), are continuations, not heads; roots are heads. `payloadMin` is the
width-aware recursive lower bound, computed bottom-up for each `w`: a leaf has
`inlineMin = size`; an internal node has `payloadMin = scalar + Σ childCost`
(scalar: Lam/All/Let contract byte, Prj `Tag0` type index, 0 for App), where
a head-position child costs `cmin` and a continuation-position child (App
function child that is an App, Lam/All body of the same kind) costs
`cminCont`, and `inlineMin = hdr + payloadMin`; for a candidate
`cmin = min(w, inlineMin)` and `cminCont = min(w, payloadMin)`, otherwise
`cmin = inlineMin` and `cminCont = payloadMin`. (The first version used one
byte per child.) `payloadMax` is the unshared size minus the node's own Tag4
header; leaves use their full size for both and `hdr = 0`, internal nodes
`hdr = 1`. All arithmetic is exact (`Nat`/`Int`, no capping of `occ`).

Two uncertain nodes are related when a directed DAG path joins them whose
intermediate nodes are not certain-stored; components are the transitive
closure. Computed by union-find: call a node that is neither certain-stored
nor uncertain "transparent"; it is "activated" when an uncertain node or an
activated transparent node is its parent, and has `below` when an uncertain
node is reachable under it through transparent nodes. Uncertain nodes and
activated transparent nodes with `below` are united with every child that is
uncertain or transparent with `below`. (A transparent node without `below`,
such as a shared leaf, must not join its parents.) For DAGs with at most
`bruteMaxN` nodes the largest component is recomputed by a literal walk from
every uncertain node through all non-certain-stored nodes. -/

structure WStats where
  cand : Nat := 0
  cs : Nat := 0
  ce : Nat := 0
  unc : Nat := 0
  /-- Uncertain nodes in the largest component. -/
  comp : Nat := 0
  /-- Candidates satisfying both certain conditions (counted as stored). -/
  conflicts : Nat := 0
  /-- Candidates whose `payloadMin` exceeds `payloadMax` (sanity; expect 0). -/
  minGtMax : Nat := 0
  /-- Candidates whose class changes when every function-child occurrence
  (not only an App inside an App spine) is treated as a non-head. -/
  litDiff : Nat := 0
  /-- Largest component recomputed by the literal brute force (`none` when
  the DAG exceeds the brute-force bound). -/
  compCheck : Option Bool := none
  deriving Inhabited

def gain (n h b hdr w : Nat) : Int :=
  ((n : Int) - 1) * b + ((h : Int) - 1) * hdr - (n : Int) * w

def ufFind (parent : Array Nat) (i : Nat) : Nat := Id.run do
  let mut x := i
  while parent[x]! != x do
    x := parent[x]!
  return x

def classify (res : Ix.Sharing.AnalyzeResult) (sizes : Std.HashMap Address NodeSz)
    (roots : Array Expr) (bruteMaxN : Nat := 1000) : Except String (Array WStats) := do
  let order := res.topoOrder
  let n := order.size
  let mut idxOf : Std.HashMap Address Nat := Std.HashMap.emptyWithCapacity n
  for i in [0:n] do
    idxOf := idxOf.insert order[i]! i
  -- Per-node data; kinds: 0 leaf, 1 App, 2 Lam, 3 All, 4 Let, 5 Prj.
  let mut kids : Array (Array Nat) := Array.mkEmpty n
  let mut kind : Array UInt8 := Array.mkEmpty n
  let mut occ : Array Nat := Array.mkEmpty n
  let mut sz : Array Nat := Array.mkEmpty n
  let mut scalar : Array Nat := Array.mkEmpty n
  let mut pMax : Array Nat := Array.mkEmpty n
  let mut hdr : Array Nat := Array.mkEmpty n
  for i in [0:n] do
    let some info := res.infoMap.get? order[i]! | throw "node not analyzed"
    let ks ← info.children.mapM fun c =>
      match idxOf.get? c with | some j => pure j | none => throw "child not analyzed"
    let ns := sizes.getD order[i]! default
    let (k, sc, hi, hd) : UInt8 × Nat × Nat × Nat := match info.expr with
      | .app .. => (1, 0, ns.payload, 1)
      | .lam .. => (2, 1, ns.payload, 1)
      | .all .. => (3, 1, ns.payload, 1)
      | .letE c .. => (4, 1, ns.sz - tag4Size c.flags.toNat, 1)
      | .prj t f _ => (5, tag0Size t.toNat, ns.sz - tag4Size f.toNat, 1)
      | _ => (0, 0, ns.sz, 0)
    kids := kids.push ks; kind := kind.push k; occ := occ.push info.usageCount
    sz := sz.push ns.sz; scalar := scalar.push sc; pMax := pMax.push hi; hdr := hdr.push hd
  let mut deg : Array Nat := Array.replicate n 0
  let mut head : Array Nat := Array.replicate n 0
  let mut headLit : Array Nat := Array.replicate n 0
  for p in [0:n] do
    let pk := kind[p]!
    let ks := kids[p]!
    for pos in [0:ks.size] do
      let c := ks[pos]!
      let ck := kind[c]!
      deg := deg.modify c (· + 1)
      let appFn := pk == 1 && pos == 0
      let sameBody := (pk == 2 && pos == 1 && ck == 2) || (pk == 3 && pos == 1 && ck == 3)
      unless (appFn && ck == 1) || sameBody do head := head.modify c (· + 1)
      unless appFn || sameBody do headLit := headLit.modify c (· + 1)
  for r in roots do
    let some h := res.ptrToHash.get? (Ix.Sharing.exprPtr r) | throw "root not analyzed"
    let some i := idxOf.get? h | throw "root not indexed"
    deg := deg.modify i (· + 1)
    head := head.modify i (· + 1)
    headLit := headLit.modify i (· + 1)
  let mut out : Array WStats := #[]
  for w in [1, 2, 3] do
    -- 0 non-candidate, 1 certain-stored, 2 certain-excluded, 3 uncertain
    let mut cls : Array UInt8 := Array.replicate n 0
    let mut st : WStats := {}
    -- Width-aware recursive lower bound, children first.
    let mut pMin : Array Nat := Array.replicate n 0
    let mut cmin : Array Nat := Array.replicate n 0
    let mut cminCont : Array Nat := Array.replicate n 0
    for i in [0:n] do
      let isCand := deg[i]! ≥ 2 && sz[i]! > 1
      let k := kind[i]!
      if k == 0 then
        let v := sz[i]!
        pMin := pMin.set! i v
        cmin := cmin.set! i (if isCand then min w v else v)
        cminCont := cminCont.set! i (if isCand then min w v else v)
      else
        let ks := kids[i]!
        let mut pay := scalar[i]!
        for pos in [0:ks.size] do
          let ch := ks[pos]!
          let ck := kind[ch]!
          let cont := (k == 1 && pos == 0 && ck == 1) || (k == 2 && pos == 1 && ck == 2) ||
            (k == 3 && pos == 1 && ck == 3)
          pay := pay + (if cont then cminCont[ch]! else cmin[ch]!)
        pMin := pMin.set! i pay
        let inl := hdr[i]! + pay
        cmin := cmin.set! i (if isCand then min w inl else inl)
        cminCont := cminCont.set! i (if isCand then min w pay else pay)
    for i in [0:n] do
      if deg[i]! ≥ 2 && sz[i]! > 1 then
        if pMin[i]! > pMax[i]! then st := { st with minGtMax := st.minGtMax + 1 }
        let stored := gain deg[i]! head[i]! pMin[i]! hdr[i]! w > 0
        let leafEx := hdr[i]! == 0 &&
          ((occ[i]! : Int) - 1) * sz[i]! < (occ[i]! : Int) * w
        let excluded := gain occ[i]! occ[i]! pMax[i]! hdr[i]! w < 0 || leafEx
        let c : UInt8 := if stored then 1 else if excluded then 2 else 3
        let storedLit := gain deg[i]! headLit[i]! pMin[i]! hdr[i]! w > 0
        let cLit : UInt8 := if storedLit then 1 else if excluded then 2 else 3
        cls := cls.set! i c
        st := { st with
          cand := st.cand + 1
          cs := st.cs + (if c == 1 then 1 else 0)
          ce := st.ce + (if c == 2 then 1 else 0)
          unc := st.unc + (if c == 3 then 1 else 0)
          conflicts := st.conflicts + (if stored && excluded then 1 else 0)
          litDiff := st.litDiff + (if c != cLit then 1 else 0) }
    -- Activation, parents before children (reverse topological order).
    let mut act : Array Bool := Array.replicate n false
    for j in [0:n] do
      let p := n - 1 - j
      let cp := cls[p]!
      if cp == 3 || (cp != 1 && act[p]!) then
        for c in kids[p]! do
          if cls[c]! == 0 || cls[c]! == 2 then act := act.set! c true
    -- `below[x]`: an uncertain node is reachable from the non-stored,
    -- non-uncertain node `x` through such nodes (children first).
    let mut below : Array Bool := Array.replicate n false
    for p in [0:n] do
      if cls[p]! == 0 || cls[p]! == 2 then
        let hit := kids[p]!.any fun c =>
          cls[c]! == 3 || ((cls[c]! == 0 || cls[c]! == 2) && below[c]!)
        below := below.set! p hit
    -- Union-find (union by size) along edges out of uncertain/activated nodes
    -- into uncertain children or into non-stored children with `below`.
    let mut parent : Array Nat := Array.range n
    let mut usz : Array Nat := Array.replicate n 1
    for p in [0:n] do
      let cp := cls[p]!
      if cp == 3 || (cp != 1 && act[p]! && below[p]!) then
        for c in kids[p]! do
          if cls[c]! == 3 || ((cls[c]! == 0 || cls[c]! == 2) && below[c]!) then
            let a := ufFind parent p
            let b := ufFind parent c
            if a != b then
              if usz[a]! < usz[b]! then
                parent := parent.set! a b
                usz := usz.set! b (usz[a]! + usz[b]!)
              else
                parent := parent.set! b a
                usz := usz.set! a (usz[a]! + usz[b]!)
    let mut compSize : Std.HashMap Nat Nat := {}
    for i in [0:n] do
      if cls[i]! == 3 then
        let r := ufFind parent i
        compSize := compSize.insert r (compSize.getD r 0 + 1)
    let comp := compSize.fold (init := 0) fun m _ v => max m v
    -- Literal brute force on small DAGs: from every uncertain node, walk
    -- down through every node that is not certain-stored and relate it to
    -- each uncertain node reached; components by a separate union-find.
    let compCheck : Option Bool := if n > bruteMaxN then none else Id.run do
      let mut par : Array Nat := Array.range n
      for u in [0:n] do
        if cls[u]! == 3 then
          let mut seen : Array Bool := Array.replicate n false
          let mut stack : Array Nat := kids[u]!
          while !stack.isEmpty do
            let c := stack.back!
            stack := stack.pop
            if seen[c]! || cls[c]! == 1 then continue
            seen := seen.set! c true
            if cls[c]! == 3 then
              let a := ufFind par u
              let b := ufFind par c
              if a != b then par := par.set! a b
            stack := stack ++ kids[c]!
      let mut cnt : Std.HashMap Nat Nat := {}
      for i in [0:n] do
        if cls[i]! == 3 then
          let r := ufFind par i
          cnt := cnt.insert r (cnt.getD r 0 + 1)
      return some (cnt.fold (init := 0) (fun m _ v => max m v) == comp)
    out := out.push { st with comp, compCheck }
  return out

/-! ## W1's uniform-width classification, reimplemented on this harness's DAG

An independent reimplementation of the definitions in `Ix/Sharing/Exact/Uniform.lean`
(module doc and `classify`), on the blake3 hash-consed DAG of this harness, to compare
per constant with the classes the W1 optimizer reports:

* CERTAIN-EXCLUDED: `(occ−1)·size < occ·w`, for every term;
* low degree: not certain-excluded and `deg < 2`;
* candidates (may be stored): `deg ≥ 2` and not certain-excluded;
* bounds bottom-up: a non-telescope node has `inl⁻ = own header bytes + Σ headLB`;
  a telescope node has `merged = sideExtra + headLB(side) + (contLB(next) if next
  continues the telescope else headLB(next))` and `inl⁻ = 1 + merged`; a candidate's
  `headLB`/`contLB` are `min(w, ·)` of these;
* CERTAIN-STORED when `g ≥ 2`: non-telescope `(deg−1)·inl⁻ − deg·w`; telescope with
  `headDeg ≥ 1` `(deg−1)·merged + (headDeg−1) − deg·w`; telescope with `headDeg = 0`
  `(deg−1)·merged − tag4Size(spine length) − deg·w`;
* components as in `classify` above. -/

structure ClassCounts where
  cs : Nat := 0
  ce : Nat := 0
  unc : Nat := 0
  low : Nat := 0
  comp : Nat := 0
  ncomps : Nat := 0
  deriving Inhabited, BEq, Repr

/-- Largest component and number of components of the uncertain nodes (class
3), joined by directed DAG paths through nodes that are not certain-stored
(class 1). Classes 0 and 2 are transparent. -/
def uncertainComponentsOf (n : Nat) (kids : Array (Array Nat)) (cls : Array UInt8) :
    Nat × Nat := Id.run do
  let transparent (i : Nat) : Bool := cls[i]! == 0 || cls[i]! == 2
  let mut act : Array Bool := Array.replicate n false
  for j in [0:n] do
    let p := n - 1 - j
    if cls[p]! == 3 || (transparent p && act[p]!) then
      for c in kids[p]! do
        if transparent c then act := act.set! c true
  let mut below : Array Bool := Array.replicate n false
  for p in [0:n] do
    if transparent p then
      below := below.set! p (kids[p]!.any fun c => cls[c]! == 3 || (transparent c && below[c]!))
  let mut parent : Array Nat := Array.range n
  let mut usz : Array Nat := Array.replicate n 1
  for p in [0:n] do
    if cls[p]! == 3 || (transparent p && act[p]! && below[p]!) then
      for c in kids[p]! do
        if cls[c]! == 3 || (transparent c && below[c]!) then
          let a := ufFind parent p
          let b := ufFind parent c
          if a != b then
            if usz[a]! < usz[b]! then
              parent := parent.set! a b
              usz := usz.set! b (usz[a]! + usz[b]!)
            else
              parent := parent.set! b a
              usz := usz.set! a (usz[a]! + usz[b]!)
  let mut compSize : Std.HashMap Nat Nat := {}
  for i in [0:n] do
    if cls[i]! == 3 then
      let r := ufFind parent i
      compSize := compSize.insert r (compSize.getD r 0 + 1)
  return (compSize.fold (init := 0) fun m _ v => max m v, compSize.size)

def classifyW1Mode (res : Ix.Sharing.AnalyzeResult) (sizes : Std.HashMap Address NodeSz)
    (roots : Array Expr) : Except String (Array ClassCounts) := do
  let order := res.topoOrder
  let n := order.size
  let mut idxOf : Std.HashMap Address Nat := Std.HashMap.emptyWithCapacity n
  for i in [0:n] do
    idxOf := idxOf.insert order[i]! i
  -- kinds: 0 non-telescope, 1 App, 2 Lam, 3 All
  let mut kids : Array (Array Nat) := Array.mkEmpty n
  let mut kind : Array UInt8 := Array.mkEmpty n
  let mut occ : Array Nat := Array.mkEmpty n
  let mut sz : Array Nat := Array.mkEmpty n
  let mut own : Array Nat := Array.mkEmpty n
  let mut tele : Array Nat := Array.mkEmpty n
  for i in [0:n] do
    let some info := res.infoMap.get? order[i]! | throw "node not analyzed"
    let ks ← info.children.mapM fun c =>
      match idxOf.get? c with | some j => pure j | none => throw "child not analyzed"
    let ns := sizes.getD order[i]! default
    let k : UInt8 := match info.expr with
      | .app .. => 1 | .lam .. => 2 | .all .. => 3 | _ => 0
    kids := kids.push ks; kind := kind.push k; occ := occ.push info.usageCount
    sz := sz.push ns.sz; own := own.push info.baseSize; tele := tele.push ns.tele
  let mut deg : Array Nat := Array.replicate n 0
  let mut head : Array Nat := Array.replicate n 0
  for p in [0:n] do
    let pk := kind[p]!
    let ks := kids[p]!
    for pos in [0:ks.size] do
      let c := ks[pos]!
      let ck := kind[c]!
      deg := deg.modify c (· + 1)
      let cont := pk != 0 && ck == pk && pos == (if pk == 1 then 0 else 1)
      unless cont do head := head.modify c (· + 1)
  for r in roots do
    let some h := res.ptrToHash.get? (Ix.Sharing.exprPtr r) | throw "root not analyzed"
    let some i := idxOf.get? h | throw "root not indexed"
    deg := deg.modify i (· + 1)
    head := head.modify i (· + 1)
  let mut out : Array ClassCounts := #[]
  for w in [1, 2, 3] do
    let ce : Array Bool := (Array.range n).map fun t => (occ[t]! - 1) * sz[t]! < occ[t]! * w
    let cand : Array Bool := (Array.range n).map fun t => !ce[t]! && deg[t]! ≥ 2
    let mut inl : Array Nat := Array.replicate n 0
    let mut merged : Array Nat := Array.replicate n 0
    let mut headLB : Array Nat := Array.replicate n 0
    let mut contLB : Array Nat := Array.replicate n 0
    for t in [0:n] do
      let k := kind[t]!
      let ks := kids[t]!
      let (i, m) :=
        if k == 0 then
          let i := ks.foldl (fun acc c => acc + headLB[c]!) own[t]!
          (i, i)
        else
          let (nxt, side, extra) := if k == 1 then (ks[0]!, ks[1]!, 0) else (ks[1]!, ks[0]!, 1)
          let rest := if kind[nxt]! == k then contLB[nxt]! else headLB[nxt]!
          let m := extra + headLB[side]! + rest
          (1 + m, m)
      inl := inl.set! t i
      merged := merged.set! t m
      headLB := headLB.set! t (if cand[t]! then min w i else i)
      contLB := contLB.set! t (if cand[t]! then min w m else m)
    let mut cls : Array UInt8 := Array.replicate n 0
    let mut cc : ClassCounts := {}
    for t in [0:n] do
      let d : Int := deg[t]!
      let g : Int :=
        if kind[t]! == 0 then (d - 1) * inl[t]! - d * w
        else if head[t]! ≥ 1 then (d - 1) * merged[t]! + ((head[t]! : Int) - 1) - d * w
        else (d - 1) * merged[t]! - tag4Size tele[t]! - d * w
      let c : UInt8 :=
        if ce[t]! then 2 else if deg[t]! < 2 then 0 else if g ≥ 2 then 1 else 3
      cls := cls.set! t c
      cc := match c with
        | 1 => { cc with cs := cc.cs + 1 }
        | 2 => { cc with ce := cc.ce + 1 }
        | 3 => { cc with unc := cc.unc + 1 }
        | _ => { cc with low := cc.low + 1 }
    let (comp, ncomps) := uncertainComponentsOf n kids cls
    out := out.push { cc with comp, ncomps }
  return out

/-! ## Running the W1 uniform optimizer -/

/-- One uniform-width optimizer run on one constant. -/
structure UniStats where
  ok : Bool := false
  err : String := ""
  /-- Wall time of the optimizer call. -/
  ns : Nat := 0
  counts : ClassCounts := {}
  /-- W1's distinct subterms. -/
  n : Nat := 0
  states : Nat := 0
  lowerBracket : Bool := false
  /-- Complete-Constant model length: fixed bytes + `modelBytes`. -/
  model : Nat := 0
  /-- Real serialized length of the produced Constant (current Tag4 tiers). -/
  real : Nat := 0
  /-- The same table under scheme F widths. -/
  realF : Nat := 0
  table : Nat := 0
  /-- `real = fixed + variableBytes`. -/
  variableOk : Bool := false
  /-- Decode / re-encode / expand / exact-equality check of the output. -/
  checkErr : Option String := none
  deriving Inhabited

def uniStats (c : Constant) (roots : Array Expr) (fixed : Nat)
    (u : Ix.Sharing.Exact.UniformSharingResult) (ns : Nat) : UniStats :=
  let mc : Constant :=
    { info := replaceRoots c.info u.result.roots, sharing := u.result.sharing,
      refs := c.refs, univs := c.univs }
  let b := Ixon.serConstant mc
  let count (lo hi : UInt64) :=
    u.result.roots.foldl (fun acc e => countShareRefsBy lo hi e acc)
      (u.result.sharing.foldl (fun acc e => countShareRefsBy lo hi e acc) (0, 0, 0))
  let a := count 8 256
  let f := count 8 1032
  let aBytes := a.1 + 2 * a.2.1 + 3 * a.2.2
  let fBytes := f.1 + 2 * f.2.1 + 3 * f.2.2
  { ok := true, ns
    counts := { cs := u.certainStored.size, ce := u.certainExcluded.size,
                unc := u.uncertain.size, low := u.lowDegree.size,
                comp := u.components.foldl (fun m x => max m x.size) 0,
                ncomps := u.components.size }
    n := u.result.stats.distinctSubterms, states := u.statesVisited
    lowerBracket := u.lowerBracket
    model := fixed + u.result.modelBytes, real := b.size, realF := b.size - aBytes + fBytes
    table := u.result.sharing.size
    variableOk := b.size == fixed + u.result.variableBytes
    checkErr := match mssCheck b roots with | .ok () => none | .error e => some e }

/-! ## Integer repricing: TagN, TagN-byte and the Tag2 variant

Walks the stored (heuristic) encoding of a Constant exactly as `putConstant` /
`putExpr` / `putUniv` write it (telescope counts as written by `collectAppArgs` and
the binder collectors; successor chains as one `Tag2`), classifies every `Tag4`,
`Tag0` and `Tag2` integer, and prices it under the current codes
(`tag4EncodedSize`, `tag0EncodedSize`, `putTag2`) and under:

* TagN (replaces every `Tag4`): 1 byte below 8, 2 below 8 + 1024, 3 below
  1032 + 65536, 5 below that + 2^32, 9 beyond;
* TagN-byte (replaces every `Tag0`): 1 byte below 128, 2 below 128 + 16384, 3 below
  16512 + 65536, 5 below that + 2^32, 9 beyond;
* the Tag2 variant of TagN (replaces every `Tag2`): 1 byte below 32, 2 below
  32 + 4096, 3 below 4128 + 65536, 5 below that + 2^32, 9 beyond.

All other bytes (flag and contract bytes, addresses) are counted as `other`. The sum
of every part must equal the stored byte length. -/

def tagNSize (v : Nat) : Nat :=
  if v < 8 then 1 else if v < 1032 then 2 else if v < 66568 then 3
  else if v < 66568 + 4294967296 then 5 else 9

def tagNByteSize (v : Nat) : Nat :=
  if v < 128 then 1 else if v < 16512 then 2 else if v < 82048 then 3
  else if v < 82048 + 4294967296 then 5 else 9

def tagN2Size (v : Nat) : Nat :=
  if v < 32 then 1 else if v < 4128 then 2 else if v < 69664 then 3
  else if v < 69664 + 4294967296 then 5 else 9

/-- Integer classes. `Tag4` classes: 0 Share index, 1 Var index, 2 Sort level,
3 App argument count, 4 Lam/All binder count, 5 Ref/Recur universe-list length,
6 Prj field, 7 Str/Nat index, 8 Let flags, 9 ConstantInfo header. `Tag0` classes:
10 Ref/Recur index, 11 Ref/Recur universe index, 12 Prj type index, 13 table counts
(sharing, refs, univs), 14 ConstantInfo scalar fields. `Tag2`: 15 universe terms. -/
def intClassNames : Array String := #[
  "Share indices (Tag4)", "Var indices (Tag4)", "Sort levels (Tag4)",
  "App argument counts (Tag4)", "Lam/All binder counts (Tag4)",
  "Ref/Recur universe-list lengths (Tag4)", "Prj fields (Tag4)", "Str/Nat indices (Tag4)",
  "Let flags (Tag4)", "ConstantInfo header: variant / mutual member count (Tag4)",
  "Ref/Recur indices (Tag0)", "Ref/Recur universe indices (Tag0)", "Prj type indices (Tag0)",
  "table counts: sharing, refs, univs (Tag0)",
  "ConstantInfo scalar fields: lvls, params, indices, motives, minors, rule fields and counts, constructor counts and fields, cidx, projection idx (Tag0)",
  "universe terms: zero/succ-chain, max, imax, var headers (Tag2)"]

structure LadAcc where
  cnt : Array Nat := Array.replicate 16 0
  cur : Array Nat := Array.replicate 16 0
  new : Array Nat := Array.replicate 16 0
  gain : Array Nat := Array.replicate 16 0
  loss : Array Nat := Array.replicate 16 0
  /-- Histograms by width (index = bytes, 0..9). -/
  h4cur : Array Nat := Array.replicate 10 0
  h4new : Array Nat := Array.replicate 10 0
  h0cur : Array Nat := Array.replicate 10 0
  h0new : Array Nat := Array.replicate 10 0
  h2cur : Array Nat := Array.replicate 10 0
  h2new : Array Nat := Array.replicate 10 0
  other : Nat := 0
  deriving Inhabited

def LadAcc.addInt (a : LadAcc) (cls cur new : Nat) : LadAcc :=
  { a with
    cnt := a.cnt.modify cls (· + 1)
    cur := a.cur.modify cls (· + cur)
    new := a.new.modify cls (· + new)
    gain := a.gain.modify cls (· + (cur - new))
    loss := a.loss.modify cls (· + (new - cur)) }

def LadAcc.add4 (a : LadAcc) (cls : Nat) (v : UInt64) : LadAcc :=
  let cur := Ix.Sharing.tag4EncodedSize v
  let new := tagNSize v.toNat
  let a := a.addInt cls cur new
  { a with h4cur := a.h4cur.modify cur (· + 1), h4new := a.h4new.modify new (· + 1) }

def LadAcc.add0 (a : LadAcc) (cls : Nat) (v : UInt64) : LadAcc :=
  let cur := Ix.Sharing.tag0EncodedSize v
  let new := tagNByteSize v.toNat
  let a := a.addInt cls cur new
  { a with h0cur := a.h0cur.modify cur (· + 1), h0new := a.h0new.modify new (· + 1) }

/-- `Tag2` size as written by `putTag2`. -/
def tag2Size (v : UInt64) : Nat := if v < 32 then 1 else 1 + (Ixon.u64ByteCount v).toNat

def LadAcc.add2 (a : LadAcc) (v : UInt64) : LadAcc :=
  let cur := tag2Size v
  let new := tagN2Size v.toNat
  let a := a.addInt 15 cur new
  { a with h2cur := a.h2cur.modify cur (· + 1), h2new := a.h2new.modify new (· + 1) }

def LadAcc.addOther (a : LadAcc) (n : Nat) : LadAcc := { a with other := a.other + n }

def LadAcc.merge (a b : LadAcc) : LadAcc :=
  let z (x y : Array Nat) := (x.zip y).map fun (p, q) => p + q
  { cnt := z a.cnt b.cnt, cur := z a.cur b.cur, new := z a.new b.new,
    gain := z a.gain b.gain, loss := z a.loss b.loss,
    h4cur := z a.h4cur b.h4cur, h4new := z a.h4new b.h4new,
    h0cur := z a.h0cur b.h0cur, h0new := z a.h0new b.h0new,
    h2cur := z a.h2cur b.h2cur, h2new := z a.h2new b.h2new, other := a.other + b.other }

def LadAcc.total (a : LadAcc) : Nat := a.cur.foldl (· + ·) 0 + a.other

/-- Universe term, mirroring `putUniv` (successor chains as one `Tag2`). -/
partial def ladUniv (a : LadAcc) : Ixon.Univ → LadAcc
  | .zero => a.add2 0
  | u@(.succ _) => ladUniv (a.add2 u.succCount) u.succBase
  | .max x y => ladUniv (ladUniv (a.add2 0) x) y
  | .imax x y => ladUniv (ladUniv (a.add2 0) x) y
  | .var i => a.add2 i

/-- Expression, mirroring `putExpr`. -/
partial def ladExpr (a : LadAcc) : Expr → LadAcc
  | .sort i => a.add4 2 i
  | .var i => a.add4 1 i
  | .ref r us | .recur r us =>
    us.foldl (fun a u => a.add0 11 u) ((a.add4 5 us.size.toUInt64).add0 10 r)
  | .prj t f v => ladExpr ((a.add4 6 f).add0 12 t) v
  | .str i | .nat i => a.add4 7 i
  | e@(.app ..) =>
    let (args, head) := e.collectAppArgs
    args.foldl ladExpr (ladExpr (a.add4 3 args.length.toUInt64) head)
  | e@(.lam ..) =>
    let (bs, body) := e.collectLamBinders
    let a := (a.add4 4 bs.length.toUInt64).addOther bs.length
    ladExpr (bs.foldl (fun a b => ladExpr a b.2) a) body
  | e@(.all ..) =>
    let (bs, body) := e.collectAllBinders
    let a := (a.add4 4 bs.length.toUInt64).addOther bs.length
    ladExpr (bs.foldl (fun a b => ladExpr a b.2.2) a) body
  | .letE c t v b => ladExpr (ladExpr (ladExpr ((a.add4 8 c.flags).addOther 1) t) v) b
  | .share i => a.add4 0 i

def ladDefinition (a : LadAcc) (d : Ixon.Definition) : LadAcc :=
  ladExpr (ladExpr ((a.addOther 1).add0 14 d.lvls) d.typ) d.value

def ladRecursor (a : LadAcc) (r : Ixon.Recursor) : LadAcc :=
  let a := (a.addOther 1).add0 14 r.lvls |>.add0 14 r.params |>.add0 14 r.indices
    |>.add0 14 r.motives |>.add0 14 r.minors
  let a := (ladExpr a r.typ).add0 14 r.rules.size.toUInt64
  r.rules.foldl (fun a rule => ladExpr (a.add0 14 rule.fields) rule.rhs) a

def ladInductive (a : LadAcc) (i : Ixon.Inductive) : LadAcc :=
  let a := (a.addOther 1).add0 14 i.lvls |>.add0 14 i.params |>.add0 14 i.indices
  let a := (ladExpr a i.typ).add0 14 i.ctors.size.toUInt64
  i.ctors.foldl (fun a c =>
    ladExpr ((a.addOther 1).add0 14 c.lvls |>.add0 14 c.cidx |>.add0 14 c.params
      |>.add0 14 c.fields) c.typ) a

/-- Constant, mirroring `putConstant`. -/
def ladConstant (c : Constant) : LadAcc := Id.run do
  let mut a : LadAcc := {}
  a := match c.info with
    | .defn d => ladDefinition (a.add4 9 0) d
    | .recr r => ladRecursor (a.add4 9 1) r
    | .axio x => ladExpr (((a.add4 9 2).addOther 1).add0 14 x.lvls) x.typ
    | .quot q => ladExpr (((a.add4 9 3).addOther 1).add0 14 q.lvls) q.typ
    | .cPrj p => (((a.add4 9 4).add0 14 p.idx).add0 14 p.cidx).addOther 32
    | .rPrj p => ((a.add4 9 5).add0 14 p.idx).addOther 32
    | .iPrj p => ((a.add4 9 6).add0 14 p.idx).addOther 32
    | .dPrj p => ((a.add4 9 7).add0 14 p.idx).addOther 32
    | .muts ms => ms.foldl (fun a m =>
        let a := a.addOther 1
        match m with
        | .defn d => ladDefinition a d
        | .indc i => ladInductive a i
        | .recr r => ladRecursor a r) (a.add4 9 ms.size.toUInt64)
  a := a.add0 13 c.sharing.size.toUInt64
  a := c.sharing.foldl ladExpr a
  a := (a.add0 13 c.refs.size.toUInt64).addOther (32 * c.refs.size)
  a := a.add0 13 c.univs.size.toUInt64
  a := c.univs.foldl ladUniv a
  return a

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
  table : Nat
  raw : Nat
  unshared : Nat
  rebuiltSize : Nat
  rebuiltTable : Nat
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
  /-- Share nodes in the MSS encoding by current index width, and `Σ deg`. -/
  mssRefs : Nat × Nat × Nat := (0, 0, 0)
  /-- Share nodes of the MSS encoding by index `< 15`, `15..4110`, `≥ 4111`. -/
  mssRefsE : Nat × Nat × Nat := (0, 0, 0)
  /-- Share nodes of the MSS encoding in the scheme F and G index buckets. -/
  mssRefsF : Nat × Nat × Nat := (0, 0, 0)
  mssRefsG : Nat × Nat × Nat := (0, 0, 0)
  mssDegSum : Nat := 0
  /-- Uniform-width classification for `w = 1, 2, 3` (empty on failure). -/
  uw : Array WStats := #[]
  uwErr : Option String := none
  /-- Share references in the stored encoding with index `< 8`, `8..255`,
  `≥ 256`. -/
  refs0 : Nat := 0
  refs1 : Nat := 0
  refs2 : Nat := 0
  /-- Bytes outside the expressions (root/table-independent). -/
  fixed : Nat := 0
  /-- W1's uniform classification reimplemented here, for `w = 1, 2, 3`. -/
  w1mode : Array ClassCounts := #[]
  w1modeErr : Option String := none
  /-- W1 uniform optimizer runs for `w = 1, 2, 3` (empty when not run). -/
  uni : Array UniStats := #[]
  /-- TagN / TagN-byte repricing of the stored encoding. -/
  lad : LadAcc := {}
  ns : Nat := 0
  deriving Inhabited

/-- Everything measured for one constant. Pure; errors are skips. -/
def measure (addr : Address) (name : String) (raw : ByteArray) (c : Constant)
    (validateMax occCheckMax : Nat) : Except String Row := do
  let roundtrip := Ixon.serConstant c
  let tbl ← expandTable c.sharing
  let stored := Ix.CompileM.constantInfoRootExprs c.info
  let roots ← stored.mapM (expandExpr tbl tbl.size) |>.mapError (s!"root: " ++ ·)
  -- 1. Production rebuild from the expanded roots.
  let rebuilt := Ix.CompileM.buildConstantWithSharing c.info roots c.refs c.univs
  let rebuiltBytes := Ixon.serConstant rebuilt
  let diff := firstDiff rebuiltBytes raw
  -- 2. DAG statistics.
  let res := Ix.Sharing.analyzeBlock roots
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
  let (mss, mssTable, mssErr, mssCounts, mssRefs, mssRefsE, mssDegSum, mssRefsF, mssRefsG) :=
    match mssBuild res sizes roots with
    | .error e =>
      (0, 0, some s!"build: {e}", (0, 0, 0), (0, 0, 0), (0, 0, 0), 0, (0, 0, 0), (0, 0, 0))
    | .ok m =>
      let mc : Constant :=
        { info := replaceRoots c.info m.roots, sharing := m.table, refs := c.refs, univs := c.univs }
      let b := Ixon.serConstant mc
      let err := match mssCheck b roots with
        | .ok () => none
        | .error e => some s!"check: {e}"
      (b.size, m.table.size, err, (m.cont, m.contP2, m.contP2u), m.refs, m.refsE, m.degSum,
        m.refsF, m.refsG)
  -- 5. Uniform-reference-width classification and stored reference widths.
  let (uw, uwErr) := match classify res sizes roots with
    | .ok s => (s, none)
    | .error e => (#[], some e)
  let refCounts := stored.foldl (fun acc e => countShareRefs e acc)
    (c.sharing.foldl (fun acc e => countShareRefs e acc) (0, 0, 0))
  let (w1mode, w1modeErr) := match classifyW1Mode res sizes roots with
    | .ok s => (s, none)
    | .error e => (#[], some e)
  return {
    lad := ladConstant c
    fixed, w1mode, w1modeErr
    uw, uwErr, refs0 := refCounts.1, refs1 := refCounts.2.1, refs2 := refCounts.2.2
    mss, mssTable, mssErr, mssRefs, mssRefsE, mssDegSum, mssRefsF, mssRefsG
    cont := mssCounts.1, contP2 := mssCounts.2.1, contP2u := mssCounts.2.2
    addr, name, kind := kindOf c.info, detail := mutsDetail c.info
    roots := roots.size, n := ds.n, occ2 := ds.occ2, cand := ds.cand
    cand2 := ds.cand2, cand3 := ds.cand3, table := c.sharing.size
    raw := raw.size, unshared, rebuiltSize := rebuiltBytes.size
    rebuiltTable := rebuilt.sharing.size, rebuildOk := diff.isNone
    firstDiff := diff, roundtripOk := (firstDiff roundtrip raw).isNone
    maxApp := ds.maxApp, maxLam := ds.maxLam, maxAll := ds.maxAll
    validated, serUnsharedSize, occCheck := ds.occCheck }

/-! ## Plan §2 witnesses -/

structure Witness where
  label : String
  unshared : Nat
  heuristic : Nat
  mss : Nat
  mssHex : String
  heuristicHex : String
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
  let res := Ix.Sharing.analyzeBlock roots
  let (_, sizes) := dagStats res roots 0
  let m ← mssBuild res sizes roots
  let mb := Ixon.serConstant { c with info := replaceRoots c.info m.roots, sharing := m.table }
  let hb := Ixon.serConstant (Ix.CompileM.buildConstantWithSharing c.info roots c.refs c.univs)
  let check := match mssCheck mb roots with | .ok () => none | .error e => some e
  return { label, unshared := (Ixon.serConstant c).size, heuristic := hb.size, mss := mb.size,
           mssHex := hexOfBytes mb, heuristicHex := hexOfBytes hb, check,
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
  let res := Ix.Sharing.analyzeBlock roots
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
    distRow "current table size" (rows.map (·.table)),
    distRow "`rawBytes.size`" (rows.map (·.raw)),
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
def ladChange (a : LadAcc) (lo hi : Nat) : Int :=
  (List.range (hi - lo)).foldl (fun s i => s + ((a.new[lo + i]! : Int) - a.cur[lo + i]!)) 0

def csvEscape (s : String) : String := "\"" ++ s.replace "\"" "\"\"" ++ "\""

def csvHeader : String :=
  "addr,name,kind,members,roots,N,occ_ge2,cand,cand_gt2,cand_gt3,table,raw_bytes," ++
  "unshared_bytes,rebuild_ok,roundtrip_ok,unshared_validated,occ_checked,max_app,max_lam,max_all,us," ++
  "mss_bytes,mss_table,mss_ok,mss_cont,mss_cont_p2,mss_cont_p2u," ++
  "w1_cs,w1_ce,w1_unc,w1_comp,w2_cs,w2_ce,w2_unc,w2_comp,w3_cs,w3_ce,w3_unc,w3_comp," ++
  "refs_lt8,refs_8_255,refs_ge256,mss_refs_lt8,mss_refs_8_255,mss_refs_ge256,mss_deg_sum," ++
  "mss_refs_lt15,mss_refs_15_4110,mss_refs_ge4111," ++
  "mss_refs_lt8f,mss_refs_8_1031,mss_refs_ge1032,mss_refs_lt14,mss_refs_14_269,mss_refs_ge270," ++
  ",".intercalate ((List.range 3).map fun k =>
    let w := k + 1
    s!"u{w}_ok,u{w}_us,u{w}_cs,u{w}_ce,u{w}_unc,u{w}_comp,u{w}_states,u{w}_model,u{w}_real,u{w}_realF,u{w}_table") ++
  ",w1m1_comp,w1m2_comp,w1m3_comp,tagn_change,tagnbyte_change,tagn2_change"

def uwCsv (r : Row) : String :=
  ",".intercalate <| (List.range 3).map fun k =>
    match r.uw[k]? with
    | some s => s!"{s.cs},{s.ce},{s.unc},{s.comp}"
    | none => ",,,"

def csvLine (r : Row) : String :=
  let v := match r.validated with | some true => "1" | some false => "0" | none => ""
  let o := match r.occCheck with | some true => "1" | some false => "0" | none => ""
  s!"{(toString r.addr).take 16},{csvEscape r.name},{r.kind},{r.detail},{r.roots},{r.n}," ++
  s!"{r.occ2},{r.cand},{r.cand2},{r.cand3},{r.table},{r.raw},{r.unshared}," ++
  s!"{if r.rebuildOk then 1 else 0},{if r.roundtripOk then 1 else 0},{v},{o}," ++
  s!"{r.maxApp},{r.maxLam},{r.maxAll},{r.ns / 1000}," ++
  s!"{r.mss},{r.mssTable},{if r.mssErr.isNone then 1 else 0},{r.cont},{r.contP2},{r.contP2u}," ++
  s!"{uwCsv r},{r.refs0},{r.refs1},{r.refs2}," ++
  s!"{r.mssRefs.1},{r.mssRefs.2.1},{r.mssRefs.2.2},{r.mssDegSum}," ++
  s!"{r.mssRefsE.1},{r.mssRefsE.2.1},{r.mssRefsE.2.2}," ++
  s!"{r.mssRefsF.1},{r.mssRefsF.2.1},{r.mssRefsF.2.2}," ++
  s!"{r.mssRefsG.1},{r.mssRefsG.2.1},{r.mssRefsG.2.2}," ++
  ",".intercalate ((List.range 3).map fun k =>
    match r.uni[k]? with
    | some u =>
      if u.ok then
        s!"1,{u.ns / 1000},{u.counts.cs},{u.counts.ce},{u.counts.unc},{u.counts.comp},{u.states}," ++
        s!"{u.model},{u.real},{u.realF},{u.table}"
      else s!"0,{u.ns / 1000},,,,,,,,,"
    | none => ",,,,,,,,,,") ++
  s!",{(r.w1mode[0]?.map (·.comp)).getD 0},{(r.w1mode[1]?.map (·.comp)).getD 0},{(r.w1mode[2]?.map (·.comp)).getD 0}," ++
  s!"{ladChange r.lad 0 10},{ladChange r.lad 10 15},{ladChange r.lad 15 16}"

def kindOrder : Array String :=
  #["defn", "recr", "axio", "quot", "muts", "iPrj", "cPrj", "rPrj", "dPrj"]

/-- Nearest-rank percentile of a sorted `Int` array. -/
def pctInt (s : Array Int) (p : Nat) : Int :=
  if s.isEmpty then 0 else s[(max 1 ((p * s.size + 99) / 100)) - 1]!

def fmtSignedPct (num : Int) (den : Nat) : String :=
  if den == 0 then "0" else
    let q := (num.natAbs * 1000 + den / 2) / den
    s!"{if num < 0 then "−" else "+"}{q / 10}.{q % 10}%"

/-- The MSS section of the generated report. -/
def mssReport (rows : Array Row) (ws : Array (Except String Witness)) : String := Id.run do
  let wr := rows.filter (·.roots > 0)
  let mut md := "## Maximal structural sharing (MSS)\n\n"
  md := md ++ "Rule: store exactly the subterms with compact-DAG indegree `deg ≥ 2` (edges with multiplicity plus root occurrences) and unshared size > 1; every occurrence of a stored term is a Share; order by priority topological order (largest `deg`, then smaller blake3 hash bytes). Built with `Ix.Sharing.buildSharingEntries`/`rewriteExprs`, placed with the production root cursor helpers, serialized with `serConstant`.\n\n"
  md := md ++ "### Witnesses from the plan (§2)\n\n| fixture | unshared B | heuristic B | MSS B | expected MSS | MSS decode/expand check | MSS bytes | heuristic bytes |\n|---|---:|---:|---:|---|---|---|---|\n"
  for w in ws do
    match w with
    | .ok w =>
      md := md ++ s!"| {w.label} | {w.unshared} | {w.heuristic} | {w.mss} | {w.expectedMss} | {w.check.getD "ok"} | `{w.mssHex}` | `{w.heuristicHex}` |\n"
    | .error e => md := md ++ s!"| (witness failed) | | | | | {e} | | |\n"
  md := md ++ "\nNegative controls for the MSS decode/expand/equality check:\n\n"
  for (label, ok) in negativeControls do
    md := md ++ s!"- {label}: {if ok then "behaves as expected" else "**UNEXPECTED**"}\n"
  let errs := rows.filter (·.mssErr.isSome)
  md := md ++ s!"\n### Corpus verification\n\n- MSS built for {rows.size} constants; decode, re-encode (byte-identical), table expansion and exact pointer-memoized structural equality of the expanded roots with the original expanded roots: {rows.size - errs.size} ok, **{errs.size}** failed.\n"
  for r in errs.extract 0 10 do
    md := md ++ s!"  - `{r.name}`: {r.mssErr.getD ""}\n"
  let sRaw : Nat := wr.foldl (· + ·.raw) 0
  let sMss : Nat := wr.foldl (· + ·.mss) 0
  let sUn : Nat := wr.foldl (· + ·.unshared) 0
  let dTot : Int := (sMss : Int) - sRaw
  md := md ++ s!"\n### Totals over the {wr.size} constants with at least one root\n\n| encoding | total bytes | vs heuristic |\n|---|---:|---:|\n"
  md := md ++ s!"| heuristic (stored `rawBytes`) | {sRaw} | |\n| MSS | {sMss} | {dTot} ({fmtSignedPct dTot sRaw}) |\n| unshared | {sUn} | {(sUn : Int) - sRaw} |\n\n"
  let better := wr.filter fun r => r.mss < r.raw
  let equal := wr.filter fun r => r.mss == r.raw
  let worse := wr.filter fun r => r.mss > r.raw
  let savings := (better.map fun r => r.raw - r.mss).qsort (· < ·)
  let losses := (worse.map fun r => r.mss - r.raw).qsort (· < ·)
  let sSav := savings.foldl (· + ·) 0
  let sLoss := losses.foldl (· + ·) 0
  md := md ++ "### MSS − heuristic per constant\n\n| outcome | constants | share | bytes |\n|---|---:|---:|---:|\n"
  md := md ++ s!"| MSS smaller | {better.size} | {fmtPct better.size wr.size} | −{sSav} |\n"
  md := md ++ s!"| equal | {equal.size} | {fmtPct equal.size wr.size} | 0 |\n"
  md := md ++ s!"| MSS larger | {worse.size} | {fmtPct worse.size wr.size} | +{sLoss} |\n\n"
  md := md ++ s!"- Losses (MSS − heuristic) over the {worse.size} larger constants: p50 {pct losses 50}, p90 {pct losses 90}, p99 {pct losses 99}, max {losses.back?.getD 0}, mean {fmtMean sLoss losses.size}.\n"
  md := md ++ s!"- Savings (heuristic − MSS) over the {better.size} smaller constants: p50 {pct savings 50}, p90 {pct savings 90}, p99 {pct savings 99}, max {savings.back?.getD 0}, mean {fmtMean sSav savings.size}.\n"
  let deltas : Array Int := (wr.map fun r => (r.mss : Int) - r.raw).qsort (· < ·)
  md := md ++ s!"- Signed Δ = MSS − heuristic over all {wr.size} rooted constants: min {deltas[0]?.getD 0}, p1 {pctInt deltas 1}, p10 {pctInt deltas 10}, p50 {pctInt deltas 50}, p90 {pctInt deltas 90}, p99 {pctInt deltas 99}, max {deltas.back?.getD 0}.\n"
  let overUn := wr.filter fun r => r.mss > r.unshared
  let excess := overUn.foldl (fun acc r => acc + (r.mss - r.unshared)) 0
  let maxEx := overUn.foldl (fun acc r => max acc (r.mss - r.unshared)) 0
  md := md ++ s!"- MSS larger than unshared: {overUn.size} constants, total excess {excess} bytes, max {maxEx}. (Heuristic larger than unshared: {(wr.filter fun r => r.raw > r.unshared).size}.)\n\n"
  md := md ++ "### Table sizes (rooted constants)\n\n| Metric | min | median | p90 | p99 | max | mean |\n|---|---:|---:|---:|---:|---:|---:|\n"
  md := md ++ distRow "MSS table size" (wr.map (·.mssTable)) ++ "\n"
  md := md ++ distRow "heuristic table size" (wr.map (·.table)) ++ "\n"
  md := md ++ distRow "MSS continuation-only entries" (wr.map (·.cont)) ++ "\n"
  md := md ++ distRow "… with MSS entry payload ≤ 2" (wr.map (·.contP2)) ++ "\n"
  md := md ++ distRow "… with unshared payload ≤ 2" (wr.map (·.contP2u)) ++ "\n\n"
  md := md ++ s!"- Total MSS entries {wr.foldl (· + ·.mssTable) 0}; heuristic entries {wr.foldl (· + ·.table) 0}.\n"
  let withCont := wr.filter (·.contP2 > 0)
  md := md ++ s!"- Continuation-only entries (never a root; every occurrence is the function child of an App for an App term, or the body of a Lam/All for a Lam/All term): {wr.foldl (· + ·.cont) 0} in total; with MSS entry payload ≤ 2: {wr.foldl (· + ·.contP2) 0}; with unshared payload ≤ 2: {wr.foldl (· + ·.contP2u) 0}.\n"
  md := md ++ s!"- Constants with at least one continuation-only entry of MSS payload ≤ 2: {withCont.size}; of these, MSS larger than heuristic: {(withCont.filter fun r => r.mss > r.raw).size}, equal: {(withCont.filter fun r => r.mss == r.raw).size}, smaller: {(withCont.filter fun r => r.mss < r.raw).size}.\n"
  md := md ++ s!"- Of the {worse.size} constants where MSS is larger, {(worse.filter (·.contP2 > 0)).size} have such an entry; of the {better.size} where MSS is smaller, {(better.filter (·.contP2 > 0)).size}.\n\n"
  md := md ++ "### MSS by ConstantInfo kind (rooted constants)\n\n| kind | constants | heuristic B | MSS B | unshared B | MSS/heuristic | MSS smaller | equal | MSS larger |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|\n"
  for k in kindOrder do
    let ks := wr.filter (·.kind == k)
    unless ks.isEmpty do
      let r := ks.foldl (· + ·.raw) 0
      let m := ks.foldl (· + ·.mss) 0
      let u := ks.foldl (· + ·.unshared) 0
      md := md ++ s!"| {k} | {ks.size} | {r} | {m} | {u} | {fmtPct m r} | {(ks.filter fun x => x.mss < x.raw).size} | {(ks.filter fun x => x.mss == x.raw).size} | {(ks.filter fun x => x.mss > x.raw).size} |\n"
  let hdr := "| # | constant | kind | heuristic B | MSS B | Δ | unshared B | heuristic table | MSS table | cont. p≤2 |\n|---:|---|---|---:|---:|---:|---:|---:|---:|---:|\n"
  let line (j : Nat) (r : Row) : String :=
    s!"| {j + 1} | `{r.name}` | {r.kind} | {r.raw} | {r.mss} | {(r.mss : Int) - r.raw} | {r.unshared} | {r.table} | {r.mssTable} | {r.contP2} |\n"
  md := md ++ "\n### Ten largest MSS losses (MSS − heuristic)\n\n" ++ hdr
  let wl := (worse.qsort fun a b =>
    let da := a.mss - a.raw; let db := b.mss - b.raw
    da > db || (da == db && a.name < b.name)).extract 0 10
  for h : j in [0:wl.size] do md := md ++ line j wl[j]
  md := md ++ "\n### Ten largest MSS wins (heuristic − MSS)\n\n" ++ hdr
  let bw := (better.qsort fun a b =>
    let da := a.raw - a.mss; let db := b.raw - b.mss
    da > db || (da == db && a.name < b.name)).extract 0 10
  for h : j in [0:bw.size] do md := md ++ line j bw[j]
  return md

/-- The uniform-reference-width section of the generated report. -/
def uwReport (rows : Array Row) : String := Id.run do
  let wr := rows.filter (·.roots > 0)
  let errs := rows.filter (·.uwErr.isSome)
  let mut md := "## Uniform-reference-width classification\n\n"
  md := md ++ "Candidates are the subterms with compact `deg ≥ 2` and unshared size > 1 (the MSS stored set). For `w ∈ {1, 2, 3}` each candidate is CERTAIN-STORED if `g(deg, headdeg, payloadMin) > 0`, CERTAIN-EXCLUDED if `g(occ, occ, payloadMax) < 0` or it is a leaf with `(occ−1)·size < occ·w`, and UNCERTAIN otherwise, where `g(n, H, b) = (n−1)·b + (H−1)·hdr − n·w`. `payloadMin` is the width-aware recursive lower bound (a candidate child costs at most `w`, a non-candidate child its own recursive minimum; continuation children without their header). `headdeg` treats only an App in App-function position and a Lam/All in same-kind body position as continuations. Uncertain nodes are in one component when a directed DAG path whose intermediate nodes are not certain-stored joins them (transitively). Arithmetic is exact; `occ` is not capped.\n\n"
  md := md ++ s!"- Classification errors: {errs.size}.\n"
  for r in errs.extract 0 10 do
    md := md ++ s!"  - `{r.name}`: {r.uwErr.getD ""}\n"
  let get (k : Nat) (r : Row) : WStats := r.uw[k]?.getD {}
  md := md ++ "- Witnesses (cs/ce/unc/largest component for w = 1 | 2 | 3):\n"
  let p : Expr := .sort 0
  let a : Expr := .all .many .shared p p
  let b : Expr := .all .many .shared p (.sort 1)
  let wit : Array (String × Expr) := #[
    ("`T2 → T2`", .all .many .shared (witnessT 2) (witnessT 2)),
    ("`T16 → T16`", .all .many .shared (witnessT 16) (witnessT 16)),
    ("`A → A → B → B`", .all .many .shared a (.all .many .shared a (.all .many .shared b b)))]
  for (label, root) in wit do
    let res := Ix.Sharing.analyzeBlock #[root]
    let (_, sizes) := dagStats res #[root] 0
    match classify res sizes #[root] with
    | .ok ss =>
      let cells := ss.toList.map fun s => s!"{s.cs}/{s.ce}/{s.unc}/{s.comp}"
      md := md ++ s!"  - {label}: {" | ".intercalate cells} (candidates {(ss[0]?.map (·.cand)).getD 0})\n"
    | .error e => md := md ++ s!"  - {label}: error {e}\n"
  md := md ++ s!"- Candidates over the {wr.size} rooted constants: {wr.foldl (fun a r => a + (get 0 r).cand) 0} (MSS table entries: {wr.foldl (· + ·.mssTable) 0}).\n\n"
  for k in [0:3] do
    let w := k + 1
    let sum (f : WStats → Nat) : Nat := wr.foldl (fun a r => a + f (get k r)) 0
    md := md ++ s!"### w = {w}\n\n"
    md := md ++ s!"- Totals: certain-stored {sum (·.cs)} ({fmtPct (sum (·.cs)) (sum (·.cand))} of candidates), certain-excluded {sum (·.ce)} ({fmtPct (sum (·.ce)) (sum (·.cand))}), uncertain {sum (·.unc)} ({fmtPct (sum (·.unc)) (sum (·.cand))}); nodes meeting both certain conditions {sum (·.conflicts)}; candidates with `payloadMin > payloadMax` {sum (·.minGtMax)}; candidates whose class changes when every function-child occurrence counts as a non-head {sum (·.litDiff)}.\n"
    let chk := wr.map fun r => (get k r).compCheck
    md := md ++ s!"- Largest component recomputed by the literal brute force (DAGs with ≤ 1000 nodes): {(chk.filter (· == some true)).size} equal, **{(chk.filter (· == some false)).size}** different, {(chk.filter (·.isNone)).size} not checked.\n\n"
    md := md ++ "| Metric | min | median | p90 | p99 | max | mean |\n|---|---:|---:|---:|---:|---:|---:|\n"
    md := md ++ distRow "certain-stored" (wr.map fun r => (get k r).cs) ++ "\n"
    md := md ++ distRow "certain-excluded" (wr.map fun r => (get k r).ce) ++ "\n"
    md := md ++ distRow "uncertain" (wr.map fun r => (get k r).unc) ++ "\n"
    md := md ++ distRow "largest uncertain component" (wr.map fun r => (get k r).comp) ++ "\n\n"
    md := md ++ "| bucket | constants by `uncertain` | share | constants by largest component | share |\n|---|---:|---:|---:|---:|\n"
    let bucket (label : String) (p : Nat → Bool) : String :=
      let a := (wr.filter fun r => p (get k r).unc).size
      let b := (wr.filter fun r => p (get k r).comp).size
      s!"| {label} | {a} | {fmtPct a wr.size} | {b} | {fmtPct b wr.size} |\n"
    md := md ++ bucket "= 0" (· == 0) ++ bucket "≤ 8" (· ≤ 8) ++ bucket "≤ 16" (· ≤ 16) ++
      bucket "≤ 32" (· ≤ 32) ++ bucket "> 32" (· > 32) ++ bucket "> 128" (· > 128) ++
      bucket "> 1024" (· > 1024)
    md := md ++ s!"\nTen constants with the largest uncertain component (w = {w}):\n\n| # | constant | kind | `N` | candidates | certain-stored | certain-excluded | uncertain | largest component |\n|---:|---|---|---:|---:|---:|---:|---:|---:|\n"
    let top := (wr.qsort fun a b =>
      (get k a).comp > (get k b).comp || ((get k a).comp == (get k b).comp && a.name < b.name)).extract 0 10
    for h : j in [0:top.size] do
      let r := top[j]
      let s := get k r
      md := md ++ s!"| {j + 1} | `{r.name}` | {r.kind} | {r.n} | {s.cand} | {s.cs} | {s.ce} | {s.unc} | {s.comp} |\n"
    md := md ++ "\n"
  let s0 (xs : Array Row) : Nat := xs.foldl (· + ·.refs0) 0
  let s1 (xs : Array Row) : Nat := xs.foldl (· + ·.refs1) 0
  let s2 (xs : Array Row) : Nat := xs.foldl (· + ·.refs2) 0
  let t8 := rows.filter fun r => r.table ≥ 1 && r.table ≤ 8
  let t9 := rows.filter fun r => r.table ≥ 9 && r.table ≤ 255
  let tBig := rows.filter fun r => r.table > 255
  md := md ++ "### Reference-width loss in the current stored encoding\n\n"
  md := md ++ s!"Share references counted syntactically in the stored roots and stored table entries of every constant (current heuristic encoding). The largest stored table has {rows.foldl (fun m r => max m r.table) 0} entries, so every index ≥ 256 is 3 bytes.\n\n"
  md := md ++ "| stored table entries | constants | refs to 0–7 (1 B) | refs to 8–255 (2 B) | refs to ≥ 256 (3 B) | loss under the uniform width |\n|---|---:|---:|---:|---:|---|\n"
  md := md ++ s!"| 1–8 | {t8.size} | {s0 t8} | {s1 t8} | {s2 t8} | (not requested; {s0 t8} if these cost 2 B) |\n"
  md := md ++ s!"| 9–255 | {t9.size} | {s0 t9} | {s1 t9} | {s2 t9} | w = 2: **{s0 t9}** bytes |\n"
  md := md ++ s!"| > 255 | {tBig.size} | {s0 tBig} | {s1 tBig} | {s2 tBig} | w = 3: 2·{s0 tBig} + {s1 tBig} = **{2 * s0 tBig + s1 tBig}** bytes |\n\n"
  md := md ++ s!"- Total stored bytes over all constants: {rows.foldl (· + ·.raw) 0}; total Share references: {s0 rows + s1 rows + s2 rows}.\n"
  return md

/-! ## Share-width schemes on the MSS encoding -/

def mssRefTotal (r : Row) : Nat := r.mssRefs.1 + r.mssRefs.2.1 + r.mssRefs.2.2
/-- Scheme A: current tiers by index (1 byte `< 8`, 2 `< 256`, 3 `< 65536`). -/
def mssRefsA (r : Row) : Nat := r.mssRefs.1 + 2 * r.mssRefs.2.1 + 3 * r.mssRefs.2.2
/-- Scheme B: one width per constant, 2 if the MSS entry count is ≤ 2048, else 3. -/
def widthB (r : Row) : Nat := if r.mssTable ≤ 2048 then 2 else 3
/-- Scheme C: as B, with a 1-byte class for at most 8 entries. -/
def widthC (r : Row) : Nat := if r.mssTable ≤ 8 then 1 else widthB r
def mssRefsB (r : Row) : Nat := mssRefTotal r * widthB r
def mssRefsC (r : Row) : Nat := mssRefTotal r * widthC r
/-- Scheme D: one width per constant with the tag byte's whole low nibble used
for index bits: 1 byte for ≤ 16 entries (4-bit index), 2 for ≤ 4096 (12-bit),
else 3 (20-bit). -/
def widthD (r : Row) : Nat :=
  if r.mssTable ≤ 16 then 1 else if r.mssTable ≤ 4096 then 2 else 3
def mssRefsD (r : Row) : Nat := mssRefTotal r * widthD r
/-- Scheme E: position tiers with a nibble escape, by index in MSS order:
1 byte below 15, 2 below 15 + 4096, else 3. -/
def refBytesE (r : Row) : Nat := r.mssRefsE.1 + 2 * r.mssRefsE.2.1 + 3 * r.mssRefsE.2.2
def mssRefTotalE (r : Row) : Nat := r.mssRefsE.1 + r.mssRefsE.2.1 + r.mssRefsE.2.2
/-- Scheme F: two marker bits (1 byte below index 8, 2 below 8 + 1024, else 3). -/
def refBytesF (r : Row) : Nat := r.mssRefsF.1 + 2 * r.mssRefsF.2.1 + 3 * r.mssRefsF.2.2
/-- Scheme G: nibble values 14 and 15 as escapes (1 byte below 14, 2 below
14 + 256, else 3). -/
def refBytesG (r : Row) : Nat := r.mssRefsG.1 + 2 * r.mssRefsG.2.1 + 3 * r.mssRefsG.2.2
def bucketTotal (t : Nat × Nat × Nat) : Nat := t.1 + t.2.1 + t.2.2

def fmtSignedPct2 (num : Int) (den : Nat) : String :=
  if den == 0 then "0" else
    let q := (num.natAbs * 10000 + den / 2) / den
    let frac := q % 100
    s!"{if num < 0 then "−" else "+"}{q / 100}.{if frac < 10 then "0" else ""}{frac}%"

def schemeReport (rows : Array Row) : String := Id.run do
  let wr := rows.filter (·.roots > 0)
  let mut md := "## Share-width schemes on the MSS encoding\n\n"
  md := md ++ "Every occurrence of an MSS entry is a Share. Scheme A: the current tiers by index in MSS order (1 byte below index 8, 2 below 256, 3 below 65536). Scheme B: one width per constant, 2 bytes if the MSS entry count (= candidate count) is ≤ 2048, else 3. Scheme C: as B, but 1 byte if the count is ≤ 8. Scheme D: one width per constant using the tag byte's whole low nibble: 1 byte if the count is ≤ 16, 2 if ≤ 4096, else 3. Scheme E: position tiers with a nibble escape, by index in MSS order: 1 byte below index 15, 2 below 15 + 4096, else 3 (as specified; not realizable with a 4-bit Share flag). Scheme F: realizable position tiers with two marker bits: 1 byte below index 8, 2 below 8 + 1024, else 3. Scheme G: realizable position tiers with nibble values 14 and 15 as escapes: 1 byte below index 14, 2 below 14 + 256, else 3. Constant bytes under a scheme are MSS bytes − refbytes(A) + refbytes(scheme). Share nodes are counted on the materialized MSS encoding.\n\n"
  let mismatch := wr.filter fun r => mssRefTotal r != r.mssDegSum
  md := md ++ s!"- Share nodes in the MSS encoding vs `Σ deg` over MSS entries: {wr.size - mismatch.size} equal, **{mismatch.size}** different.\n"
  for r in mismatch.extract 0 10 do
    md := md ++ s!"  - `{r.name}`: {mssRefTotal r} Share nodes, Σ deg {r.mssDegSum}\n"
  let sum (f : Row → Nat) (xs : Array Row) : Nat := xs.foldl (fun a r => a + f r) 0
  let refs := sum mssRefTotal wr
  let sMss := sum (·.mss) wr
  let sHeur := sum (·.raw) wr
  let sA := sum mssRefsA wr
  let sB := sum mssRefsB wr
  let sC := sum mssRefsC wr
  let sD := sum mssRefsD wr
  let sE := sum refBytesE wr
  let sF := sum refBytesF wr
  let sG := sum refBytesG wr
  let mismatchFG := wr.filter fun r =>
    bucketTotal r.mssRefsF != mssRefTotal r || bucketTotal r.mssRefsG != mssRefTotal r
  md := md ++ s!"- Share nodes counted in the scheme-F and scheme-G index buckets vs the scheme-A buckets: {wr.size - mismatchFG.size} equal totals, **{mismatchFG.size}** different.\n"
  let mismatchE := wr.filter fun r => mssRefTotalE r != mssRefTotal r
  md := md ++ s!"- Share nodes counted in the scheme-E index buckets vs the scheme-A buckets: {wr.size - mismatchE.size} equal totals, **{mismatchE.size}** different.\n"
  let big := wr.filter (·.mssTable > 2048)
  md := md ++ s!"- Rooted constants: {wr.size}; Share references in their MSS encodings: {refs}; constants with more than 2048 MSS entries (width 3 under B and C): {big.size}; with at most 8 entries (width 1 under C): {(wr.filter (·.mssTable ≤ 8)).size}.\n\n"
  md := md ++ "| scheme | reference bytes | MSS constant bytes | Δ vs A | Δ / MSS total (A) | Δ / heuristic total |\n|---|---:|---:|---:|---:|---:|\n"
  for (label, s) in [("A (index tiers)", sA), ("B (2 or 3 per constant)", sB), ("C (1, 2 or 3 per constant)", sC), ("D (nibble: ≤ 16 / ≤ 4096 / more)", sD), ("E (index tiers < 15 / < 4111 / more)", sE), ("F (index tiers < 8 / < 1032 / more)", sF), ("G (index tiers < 14 / < 270 / more)", sG)] do
    let d : Int := (s : Int) - sA
    md := md ++ s!"| {label} | {s} | {(sMss : Int) - sA + s} | {d} | {fmtSignedPct2 d sMss} | {fmtSignedPct2 d sHeur} |\n"
  md := md ++ s!"\nTotals for reference: MSS bytes (scheme A, the real encoding) {sMss}; heuristic stored bytes {sHeur}.\n\n"
  let delta (f : Row → Nat) (r : Row) : Int := (f r : Int) - mssRefsA r
  let cmpLine (label : String) (f : Row → Nat) : String :=
    let better := (wr.filter fun r => delta f r < 0).size
    let equal := (wr.filter fun r => delta f r == 0).size
    let worse := (wr.filter fun r => delta f r > 0).size
    s!"| {label} | {better} | {equal} | {worse} |\n"
  md := md ++ "| comparison | better (fewer bytes) | equal | worse |\n|---|---:|---:|---:|\n"
  md := md ++ cmpLine "B vs A" mssRefsB ++ cmpLine "C vs A" mssRefsC ++
    cmpLine "D vs A" mssRefsD ++ cmpLine "E vs A" refBytesE ++
    cmpLine "F vs A" refBytesF ++ cmpLine "G vs A" refBytesG ++ "\n"
  let d1 := (wr.filter fun r => r.mssTable ≤ 16).size
  let d2 := (wr.filter fun r => r.mssTable > 16 && r.mssTable ≤ 4096).size
  let d3 := (wr.filter fun r => r.mssTable > 4096).size
  md := md ++ s!"Width classes under D: 1 byte (≤ 16 entries) {d1} constants, 2 bytes (17–4096) {d2}, 3 bytes (> 4096) {d3}.\n\n"
  let hdr := "| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–255 / ≥ 256 | A ref bytes | B ref bytes | Δ (B − A) | MSS bytes (A) |\n|---:|---|---|---:|---:|---|---:|---:|---:|---:|\n"
  let line (j : Nat) (r : Row) : String :=
    s!"| {j + 1} | `{r.name}` | {r.kind} | {r.mssTable} | {mssRefTotal r} | {r.mssRefs.1} / {r.mssRefs.2.1} / {r.mssRefs.2.2} | {mssRefsA r} | {mssRefsB r} | {delta mssRefsB r} | {r.mss} |\n"
  md := md ++ "### Ten largest losses under B (B − A)\n\n" ++ hdr
  let worst := (wr.qsort fun a b =>
    delta mssRefsB a > delta mssRefsB b ||
      (delta mssRefsB a == delta mssRefsB b && a.name < b.name)).extract 0 10
  for h : j in [0:worst.size] do md := md ++ line j worst[j]
  md := md ++ "\n### Ten largest gains under B (A − B)\n\n" ++ hdr
  let best := (wr.qsort fun a b =>
    delta mssRefsB a < delta mssRefsB b ||
      (delta mssRefsB a == delta mssRefsB b && a.name < b.name)).extract 0 10
  for h : j in [0:best.size] do md := md ++ line j best[j]
  let t255 := wr.filter (·.table > 255)
  let tA := sum mssRefsA t255
  let tB := sum mssRefsB t255
  let dB : Int := (tB : Int) - tA
  md := md ++ s!"\n### B − A restricted to constants whose current heuristic table exceeds 255 entries\n\n"
  md := md ++ s!"- Constants: {t255.size}; their MSS bytes {sum (·.mss) t255}, heuristic bytes {sum (·.raw) t255}; MSS entries: min {(t255.map (·.mssTable)).foldl min (t255[0]?.map (·.mssTable) |>.getD 0)}, max {(t255.map (·.mssTable)).foldl max 0}; with more than 2048 MSS entries: {(t255.filter (·.mssTable > 2048)).size}.\n"
  md := md ++ s!"- Reference bytes: A {tA}, B {tB}; Δ (B − A) {dB} ({fmtSignedPct2 dB (sum (·.mss) t255)} of their MSS bytes, {fmtSignedPct2 dB (sum (·.raw) t255)} of their heuristic bytes).\n"
  md := md ++ s!"- B vs A: better {(t255.filter fun r => delta mssRefsB r < 0).size}, equal {(t255.filter fun r => delta mssRefsB r == 0).size}, worse {(t255.filter fun r => delta mssRefsB r > 0).size}.\n"
  -- Scheme D in detail.
  let hdrD := "| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–255 / ≥ 256 | A ref bytes | D ref bytes | Δ (D − A) | MSS bytes (A) |\n|---:|---|---|---:|---:|---|---:|---:|---:|---:|\n"
  let lineD (j : Nat) (r : Row) : String :=
    s!"| {j + 1} | `{r.name}` | {r.kind} | {r.mssTable} | {mssRefTotal r} | {r.mssRefs.1} / {r.mssRefs.2.1} / {r.mssRefs.2.2} | {mssRefsA r} | {mssRefsD r} | {delta mssRefsD r} | {r.mss} |\n"
  md := md ++ "\n### Ten largest losses under D (D − A)\n\n" ++ hdrD
  let worstD := (wr.qsort fun a b =>
    delta mssRefsD a > delta mssRefsD b ||
      (delta mssRefsD a == delta mssRefsD b && a.name < b.name)).extract 0 10
  for h : j in [0:worstD.size] do md := md ++ lineD j worstD[j]
  md := md ++ "\n### Ten largest gains under D (A − D)\n\n" ++ hdrD
  let bestD := (wr.qsort fun a b =>
    delta mssRefsD a < delta mssRefsD b ||
      (delta mssRefsD a == delta mssRefsD b && a.name < b.name)).extract 0 10
  for h : j in [0:bestD.size] do md := md ++ lineD j bestD[j]
  -- Scheme E in detail.
  let hdrE := "| # | constant | kind | MSS entries | Share refs | refs < 15 / 15–4110 / ≥ 4111 | A ref bytes | E ref bytes | Δ (E − A) | MSS bytes (A) |\n|---:|---|---|---:|---:|---|---:|---:|---:|---:|\n"
  let lineE (j : Nat) (r : Row) : String :=
    s!"| {j + 1} | `{r.name}` | {r.kind} | {r.mssTable} | {mssRefTotal r} | {r.mssRefsE.1} / {r.mssRefsE.2.1} / {r.mssRefsE.2.2} | {mssRefsA r} | {refBytesE r} | {delta refBytesE r} | {r.mss} |\n"
  md := md ++ "\n### Ten largest losses under E (E − A)\n\n" ++ hdrE
  let worstE := (wr.qsort fun a b =>
    delta refBytesE a > delta refBytesE b ||
      (delta refBytesE a == delta refBytesE b && a.name < b.name)).extract 0 10
  for h : j in [0:worstE.size] do md := md ++ lineE j worstE[j]
  md := md ++ "\n### Ten largest gains under E (A − E)\n\n" ++ hdrE
  let bestE := (wr.qsort fun a b =>
    delta refBytesE a < delta refBytesE b ||
      (delta refBytesE a == delta refBytesE b && a.name < b.name)).extract 0 10
  for h : j in [0:bestE.size] do md := md ++ lineE j bestE[j]
  -- Schemes F and G in detail.
  let tierDetail (name bucketLabel : String) (f : Row → Nat)
      (buckets : Row → Nat × Nat × Nat) : String := Id.run do
    let hdrX := s!"| # | constant | kind | MSS entries | Share refs | refs {bucketLabel} | A ref bytes | {name} ref bytes | Δ ({name} − A) | MSS bytes (A) |\n|---:|---|---|---:|---:|---|---:|---:|---:|---:|\n"
    let lineX (j : Nat) (r : Row) : String :=
      let b := buckets r
      s!"| {j + 1} | `{r.name}` | {r.kind} | {r.mssTable} | {mssRefTotal r} | {b.1} / {b.2.1} / {b.2.2} | {mssRefsA r} | {f r} | {delta f r} | {r.mss} |\n"
    let worse := wr.filter fun r => delta f r > 0
    let maxDelta := wr.foldl (fun m r => max m (delta f r)) (0 : Int)
    let mut out := s!"\n### Scheme {name} vs A\n\n- Constants worse than A under {name}: **{worse.size}**; largest per-constant Δ ({name} − A): {maxDelta}.\n"
    for r in worse.extract 0 10 do
      out := out ++ s!"  - `{r.name}`: Δ {delta f r}\n"
    out := out ++ s!"\nTen largest gains under {name} (A − {name}):\n\n" ++ hdrX
    let bestX := (wr.qsort fun a b =>
      delta f a < delta f b || (delta f a == delta f b && a.name < b.name)).extract 0 10
    for h : j in [0:bestX.size] do out := out ++ lineX j bestX[j]
    return out
  md := md ++ tierDetail "F" "< 8 / 8–1031 / ≥ 1032" refBytesF (·.mssRefsF)
  md := md ++ tierDetail "G" "< 14 / 14–269 / ≥ 270" refBytesG (·.mssRefsG)
  let tD := sum mssRefsD t255
  let dD : Int := (tD : Int) - tA
  md := md ++ s!"\n### D − A restricted to constants whose current heuristic table exceeds 255 entries\n\n"
  md := md ++ s!"- Constants: {t255.size}; width classes under D: 1 byte {(t255.filter fun r => r.mssTable ≤ 16).size}, 2 bytes {(t255.filter fun r => r.mssTable > 16 && r.mssTable ≤ 4096).size}, 3 bytes {(t255.filter fun r => r.mssTable > 4096).size}.\n"
  md := md ++ s!"- Reference bytes: A {tA}, D {tD}; Δ (D − A) {dD} ({fmtSignedPct2 dD (sum (·.mss) t255)} of their MSS bytes, {fmtSignedPct2 dD (sum (·.raw) t255)} of their heuristic bytes).\n"
  md := md ++ s!"- D vs A: better {(t255.filter fun r => delta mssRefsD r < 0).size}, equal {(t255.filter fun r => delta mssRefsD r == 0).size}, worse {(t255.filter fun r => delta mssRefsD r > 0).size}.\n"
  return md

/-! ## TagN / TagN-byte report -/

def tagNReport (rows : Array Row) : String := Id.run do
  let acc := rows.foldl (fun a r => a.merge r.lad) ({} : LadAcc)
  let stored := rows.foldl (· + ·.raw) 0
  let bad := rows.filter fun r => r.lad.total != r.raw
  let range (lo hi : Nat) (f : Nat → Nat) : Nat :=
    (List.range (hi - lo)).foldl (fun s i => s + f (lo + i)) 0
  let cnt4 := range 0 10 (acc.cnt[·]!)
  let cur4 := range 0 10 (acc.cur[·]!)
  let new4 := range 0 10 (acc.new[·]!)
  let cnt0 := range 10 15 (acc.cnt[·]!)
  let cur0 := range 10 15 (acc.cur[·]!)
  let new0 := range 10 15 (acc.new[·]!)
  let d4 : Int := (new4 : Int) - cur4
  let d0 : Int := (new0 : Int) - cur0
  let d2 : Int := (acc.new[15]! : Int) - acc.cur[15]!
  let mut md := "## Integer repricing: TagN, TagN-byte and the Tag2 variant\n\n"
  md := md ++ "The stored (heuristic) encoding of every constant is walked exactly as `putConstant`/`putExpr`/`putUniv` write it, and every integer is priced under the current codes (`tag4EncodedSize`, `tag0EncodedSize`, `putTag2`) and under TagN (replacing every `Tag4`: 1 byte below 8, 2 below 8 + 1024, 3 below 1032 + 65536, 5 below that + 2^32, 9 beyond), TagN-byte (replacing every `Tag0`: 1 byte below 128, 2 below 128 + 16384, 3 below 16512 + 65536, 5 below that + 2^32, 9 beyond) and the Tag2 variant of TagN (replacing every `Tag2`: 1 byte below 32, 2 below 32 + 4096, 3 below 4128 + 65536, 5 below that + 2^32, 9 beyond).\n\n"
  md := md ++ s!"- Walker check: integer bytes + other bytes = `rawBytes.size` for {rows.size - bad.size} of {rows.size} constants (**{bad.size}** different).\n"
  for r in bad.extract 0 10 do
    md := md ++ s!"  - `{r.name}`: walker {r.lad.total}, stored {r.raw}\n"
  md := md ++ s!"- Stored bytes: {stored}. `Tag4` integers: {cnt4} ({cur4} bytes). `Tag0` integers: {cnt0} ({cur0} bytes). `Tag2` integers: {acc.cnt[15]!} ({acc.cur[15]!} bytes). Other bytes: {acc.other}.\n"
  md := md ++ s!"- TagN alone: {new4} bytes for the `Tag4` integers, change {d4} ({fmtSignedPct2 d4 stored} of stored bytes; gained {range 0 10 (acc.gain[·]!)}, lost {range 0 10 (acc.loss[·]!)}).\n"
  md := md ++ s!"- TagN-byte alone: {new0} bytes for the `Tag0` integers, change {d0} ({fmtSignedPct2 d0 stored}; gained {range 10 15 (acc.gain[·]!)}, lost {range 10 15 (acc.loss[·]!)}).\n"
  md := md ++ s!"- Tag2 variant alone: {acc.new[15]!} bytes for the `Tag2` integers, change {d2} ({fmtSignedPct2 d2 stored}; gained {acc.gain[15]!}, lost {acc.loss[15]!}).\n"
  md := md ++ s!"- TagN and TagN-byte together: change {d4 + d0} ({fmtSignedPct2 (d4 + d0) stored}). All three: change {d4 + d0 + d2} ({fmtSignedPct2 (d4 + d0 + d2) stored} of stored bytes).\n\n"
  md := md ++ "| field class | integers | current bytes | repriced bytes | change | bytes gained | bytes lost |\n|---|---:|---:|---:|---:|---:|---:|\n"
  for h : i in [0:intClassNames.size] do
    let d : Int := (acc.new[i]! : Int) - acc.cur[i]!
    md := md ++ s!"| {intClassNames[i]} | {acc.cnt[i]!} | {acc.cur[i]!} | {acc.new[i]!} | {d} | {acc.gain[i]!} | {acc.loss[i]!} |\n"
  md := md ++ "\nIntegers by width (bytes), per tag family, now and repriced:\n\n| width | `Tag4` now | TagN | `Tag0` now | TagN-byte | `Tag2` now | Tag2 variant |\n|---:|---:|---:|---:|---:|---:|---:|\n"
  for wd in [1:10] do
    md := md ++ s!"| {wd} | {acc.h4cur[wd]!} | {acc.h4new[wd]!} | {acc.h0cur[wd]!} | {acc.h0new[wd]!} | {acc.h2cur[wd]!} | {acc.h2new[wd]!} |\n"
  return md

/-! ## W1 uniform optimizer report -/

/-- Ten largest gains and losses of the uniform output against MSS. -/
def uniformTopTables (ok : Array Row) (k : Nat) : String := Id.run do
  let w := k + 1
  let get (r : Row) : UniStats := r.uni[k]?.getD {}
  let d (r : Row) : Int := ((get r).real : Int) - r.mss
  let better := ok.filter fun r => d r < 0
  let worse := ok.filter fun r => d r > 0
  let hdr := "| # | constant | kind | heuristic B | MSS B | uniform real B | Δ (uniform − MSS) | uniform table | MSS table | largest comp. |\n|---:|---|---|---:|---:|---:|---:|---:|---:|---:|\n"
  let line (j : Nat) (r : Row) : String :=
    s!"| {j + 1} | `{r.name}` | {r.kind} | {r.raw} | {r.mss} | {(get r).real} | {d r} | {(get r).table} | {r.mssTable} | {(get r).counts.comp} |\n"
  let mut md := s!"Ten largest gains of uniform w = {w} over MSS:\n\n" ++ hdr
  let bg := (better.qsort fun a b => d a < d b || (d a == d b && a.name < b.name)).extract 0 10
  for j in [0:bg.size] do
    md := md ++ line j bg[j]!
  md := md ++ s!"\nTen largest losses of uniform w = {w} against MSS:\n\n" ++ hdr
  let bl := (worse.qsort fun a b => d a > d b || (d a == d b && a.name < b.name)).extract 0 10
  for j in [0:bl.size] do
    md := md ++ line j bl[j]!
  return md

def sumRows (f : Row → Nat) (xs : Array Row) : Nat := xs.foldl (fun a r => a + f r) 0

/-- One width's part of the uniform report. -/
def uniformSectionW (wr : Array Row) (k : Nat) : String := Id.run do
  let sum := sumRows
  let mut md := ""
  let w := k + 1
  let get (r : Row) : UniStats := r.uni[k]?.getD {}
  let ran := wr.filter fun r => r.uni.size > k
  let ok := ran.filter fun r => (get r).ok
  let fail := ran.filter fun r => !(get r).ok
  md := md ++ s!"### w = {w}\n\n- Certified: **{ok.size}** of {ran.size}; failures: **{fail.size}**.\n"
  let mut errs : Std.HashMap String Nat := {}
  for r in fail do
    errs := errs.insert (get r).err (errs.getD (get r).err 0 + 1)
  for (e, cnt) in errs.toArray.qsort (fun a b => a.2 > b.2) do
    md := md ++ s!"  - `{e}`: {cnt}\n"
  for r in fail.extract 0 10 do
    md := md ++ s!"    - `{r.name}` (N {r.n}, {(get r).ns / 1000000} ms): `{(get r).err}`\n"
  let varOk := (ok.filter fun r => (get r).variableOk).size
  let chkBad := ok.filter fun r => (get r).checkErr.isSome
  let nOk := (ok.filter fun r => (get r).n == r.n).size
  let clsBad := ok.filter fun r => r.w1mode[k]? != some (get r).counts
  md := md ++ s!"- Output checks on certified constants: real length = fixed + `variableBytes` for {varOk}; decode/re-encode/expand/exact equality ok for {ok.size - chkBad.size}, **{chkBad.size}** failed; W1 distinct subterms = this harness's `N` for {nOk}; class counts and components equal to this harness's reimplementation of W1's definitions for {ok.size - clsBad.size}, **{clsBad.size}** different.\n"
  for r in chkBad.extract 0 10 do
    md := md ++ s!"  - check failure `{r.name}`: {(get r).checkErr.getD ""}\n"
  for r in clsBad.extract 0 10 do
    md := md ++ s!"  - class difference `{r.name}`: W1 {reprStr (get r).counts}; reimplementation {reprStr r.w1mode[k]?}\n"
  md := md ++ s!"- Classes (W1, certified): certain-stored {sum (fun r => (get r).counts.cs) ok}, certain-excluded {sum (fun r => (get r).counts.ce) ok}, uncertain {sum (fun r => (get r).counts.unc) ok}, low degree {sum (fun r => (get r).counts.low) ok}; components {sum (fun r => (get r).counts.ncomps) ok}; lower count bracket chosen in {(ok.filter fun r => (get r).lowerBracket).size} constants.\n\n"
  md := md ++ "| Metric | min | median | p90 | p99 | max | mean |\n|---|---:|---:|---:|---:|---:|---:|\n"
  md := md ++ distRow "largest uncertain component (W1)" (ok.map fun r => (get r).counts.comp) ++ "\n"
  md := md ++ distRow "search states" (ok.map fun r => (get r).states) ++ "\n"
  md := md ++ distRow "uniform table size" (ok.map fun r => (get r).table) ++ "\n"
  md := md ++ distRow "optimizer wall time (µs), all runs" (ran.map fun r => (get r).ns / 1000) ++ "\n\n"
  let sRaw := sum (·.raw) ok
  let sMss := sum (·.mss) ok
  let sUn := sum (·.unshared) ok
  let sReal := sum (fun r => (get r).real) ok
  let sF := sum (fun r => (get r).realF) ok
  let sModel := sum (fun r => (get r).model) ok
  md := md ++ s!"Totals over the {ok.size} certified constants:\n\n| encoding | total bytes | vs heuristic | vs MSS |\n|---|---:|---:|---:|\n"
  for (label, s) in [("heuristic (stored)", sRaw), ("MSS (current tiers)", sMss),
      (s!"uniform w = {w}, real (current tiers)", sReal), (s!"uniform w = {w}, scheme F widths", sF),
      (s!"uniform w = {w}, model length", sModel), ("unshared", sUn)] do
    let dh : Int := (s : Int) - sRaw
    let dm : Int := (s : Int) - sMss
    md := md ++ s!"| {label} | {s} | {dh} ({fmtSignedPct2 dh sRaw}) | {dm} ({fmtSignedPct2 dm sMss}) |\n"
  let d (r : Row) : Int := ((get r).real : Int) - r.mss
  let better := ok.filter fun r => d r < 0
  let equal := ok.filter fun r => d r == 0
  let worse := ok.filter fun r => d r > 0
  let gains := (better.map fun r => (r.mss - (get r).real)).qsort (· < ·)
  let losses := (worse.map fun r => ((get r).real - r.mss)).qsort (· < ·)
  md := md ++ s!"\nUniform w = {w} (real) vs MSS per constant: better {better.size}, equal {equal.size}, worse {worse.size}. Gains p50 {pct gains 50}, p90 {pct gains 90}, max {gains.back?.getD 0}; losses p50 {pct losses 50}, p90 {pct losses 90}, max {losses.back?.getD 0}. Versus the heuristic: better {(ok.filter fun r => (get r).real < r.raw).size}, equal {(ok.filter fun r => (get r).real == r.raw).size}, worse {(ok.filter fun r => (get r).real > r.raw).size}.\n\n"
  md := md ++ uniformTopTables ok k
  md := md ++ "\n"
  return md

/-- The ten slowest optimizer runs. -/
def uniformSlowSection (wr : Array Row) : String := Id.run do
  let mut md := ""
  let runs : Array (Row × Nat × UniStats) := wr.foldl (init := #[]) fun acc r =>
    (List.range r.uni.size).foldl (fun acc k => acc.push (r, k + 1, r.uni[k]!)) acc
  md := md ++ s!"### Ten slowest optimizer runs (of {runs.size})\n\n| # | constant | w | ms | certified | `N` | largest comp. | states | error |\n|---:|---|---:|---:|---|---:|---:|---:|---|\n"
  let slow := (runs.qsort fun a b => a.2.2.ns > b.2.2.ns).extract 0 10
  for h : j in [0:slow.size] do
    let (r, w, u) := slow[j]
    md := md ++ s!"| {j + 1} | `{r.name}` | {w} | {u.ns / 1000000} | {u.ok} | {r.n} | {u.counts.comp} | {u.states} | {u.err} |\n"
  md := md ++ s!"\nTotal optimizer wall time over all runs: {runs.foldl (fun a x => a + x.2.2.ns) 0 / 1000000} ms.\n\n"
  return md

/-- Real lengths against the w = 1 model optimum. -/
def uniformGapSection (wr : Array Row) : String := Id.run do
  let sum := sumRows
  let mut md := ""
  let all3 := wr.filter fun r => r.uni.size == 3 && r.uni.all (·.ok)
  let m1 (r : Row) : Nat := r.uni[0]!.model
  let best (r : Row) : Nat := r.uni.foldl (fun m u => min m u.real) (min r.raw r.mss)
  md := md ++ s!"### Lower-bound gap: real lengths minus the w = 1 model optimum\n\nOver the {all3.size} rooted constants certified at w = 1, 2 and 3. Σ model(w = 1) = {sum m1 all3}.\n\n| encoding (current tiers) | Σ bytes | Σ (bytes − model w=1) | % of Σ model | constants below the model |\n|---|---:|---:|---:|---:|\n"
  let encs : List (String × (Row → Nat)) := [("heuristic (stored)", (·.raw)), ("MSS", (·.mss)),
    ("uniform w = 1 output", fun r => r.uni[0]!.real), ("uniform w = 2 output", fun r => r.uni[1]!.real),
    ("uniform w = 3 output", fun r => r.uni[2]!.real),
    ("best of the above, per constant", best)]
  for (label, f) in encs do
    let s := sum f all3
    let gap : Int := (s : Int) - sum m1 all3
    let below := (all3.filter fun r => f r < m1 r).size
    md := md ++ s!"| {label} | {s} | {gap} | {fmtSignedPct2 gap (sum m1 all3)} | {below} |\n"
  return md

/-- W1's classes against this harness's own classification. -/
def uniformClassSection (wr : Array Row) : String := Id.run do
  let all3 := wr.filter fun r => r.uni.size == 3 && r.uni.all (·.ok)
  let mut md := ""
  md := md ++ "\n### W1 classes vs this harness's own classification (corrected `payloadMin`)\n\nTotals over the constants certified at all three widths. The definitions differ (see the hand-written section), so equality is not expected.\n\n| w | own certain-stored | W1 certain-stored | own certain-excluded (candidates) | W1 certain-excluded (all terms) | own uncertain | W1 uncertain | own max component | W1 max component |\n|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n"
  for k in [0:3] do
    let own (f : WStats → Nat) : Nat := all3.foldl (fun a r => a + f (r.uw[k]?.getD {})) 0
    let w1 (f : ClassCounts → Nat) : Nat := all3.foldl (fun a r => a + f r.uni[k]!.counts) 0
    let ownMax := all3.foldl (fun m r => max m (r.uw[k]?.getD {}).comp) 0
    let w1Max := all3.foldl (fun m r => max m r.uni[k]!.counts.comp) 0
    md := md ++ s!"| {k + 1} | {own (·.cs)} | {w1 (·.cs)} | {own (·.ce)} | {w1 (·.ce)} | {own (·.unc)} | {w1 (·.unc)} | {ownMax} | {w1Max} |\n"
  return md

def uniformReport (rows : Array Row) (maxStates : Nat) : String := Id.run do
  let wr := rows.filter (·.roots > 0)
  let lim : Ix.Sharing.Exact.Limits := { maxStates }
  let mut md := "## Exact uniform-width optimizer (W1) on the corpus\n\n"
  md := md ++ s!"Every rooted constant, w = 1, 2, 3: `Ix.Sharing.Exact.optimizeSharingUniformTable w c.sharing (constantInfoRoots c.info) limits` with maxStates {lim.maxStates}, maxCostEvals {lim.maxCostEvals}, maxNodes {lim.maxNodes}, maxDepth {lim.maxDepth}, maxExprVisits {lim.maxExprVisits}, maxMaterialize {lim.maxMaterialize}, maxOutputBytes {lim.maxOutputBytes} (W1 defaults except maxStates). Output roots are placed with the production cursor helpers and serialized with `serConstant` (current Tag4 tiers); the bytes are decoded, re-encoded, expanded and compared exactly with the original expanded roots. Model length = fixed bytes + `modelBytes`; real = serialized size; F = the same table and roots with scheme F Share widths. Wall time is the optimizer call only.\n\n"
  for k in [0:3] do
    md := md ++ uniformSectionW wr k
  md := md ++ uniformSlowSection wr ++ uniformGapSection wr ++ uniformClassSection wr
  return md

/-! ## Metadata study (`--meta`)

Streams a whole `.ixe` section by section with the production readers
(`getExprMetaDataIndexed`, `getExpr`, `getUniv`, `getFusedHint`, …), recording the
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
          |>.modify (base + 8) (· + Ix.Sharing.tag0EncodedSize c64)
          |>.modify (base + 9) (· + (if c < i then tagNByteSize d else Ix.Sharing.tag0EncodedSize c64))
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
  for _ in [0:len] do
    let a ← getPos
    let node ← Ixon.getExprMetaDataIndexed rev
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
  /-- Run the W1 uniform-width optimizer for `w = 1, 2, 3`. -/
  uniform : Bool := true
  /-- `maxStates` for the uniform optimizer (other limits: W1 defaults). -/
  uniMaxStates : Nat := ({} : Ix.Sharing.Exact.Limits).maxStates
  /-- Run the metadata study instead of the per-constant study. -/
  metaMode : Bool := false
  /-- Cross-check the metadata scanner against a full `deEnv` load. -/
  metaCross : Bool := false

def parseArgs : List String → Opts → Except String Opts
  | [], o => if o.corpus.isEmpty then .error "missing corpus path" else .ok o
  | "--no-uniform" :: rest, o => parseArgs rest { o with uniform := false }
  | "--meta" :: rest, o => parseArgs rest { o with metaMode := true }
  | "--meta-crosscheck" :: rest, o => parseArgs rest { o with metaCross := true }
  | "--uni-max-states" :: n :: rest, o =>
    parseArgs rest { o with uniMaxStates := n.toNat?.getD o.uniMaxStates }
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
      IO.eprintln s!"sharing-study: {e}\nusage: sharing-study <corpus.ixe> [--md p] [--csv p] [--limit n] [--validate-max bytes] [--occ-check-max bytes] [--progress n] [--no-uniform] [--uni-max-states n] [--meta] [--meta-crosscheck]"
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
    | .ok w => IO.println s!"[sharing-study] witness {w.label}: unshared {w.unshared} B, heuristic {w.heuristic} B, MSS {w.mss} B (expected {w.expectedMss}), check {w.check.getD "ok"}, MSS bytes {w.mssHex}"
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
          IO.println s!"[sharing-study] MISMATCH {name} ({row.kind}): stored {row.raw} B / table {row.table}, rebuilt {row.rebuiltSize} B / table {row.rebuiltTable}, first diff at {row.firstDiff}"
      if let some e := row.mssErr then
        IO.println s!"[sharing-study] MSS FAILURE {name} ({row.kind}): {e}"
      if row.ns > 2000000000 then
        IO.println s!"[sharing-study] slow: {name} ({row.kind}) {row.ns / 1000000} ms, N={row.n}"
      -- W1 uniform-width optimizer, timed per call.
      let mut row := row
      if opts.uniform && row.roots > 0 then
        let rootsE := (do
          let tbl ← expandTable c.sharing
          (Ix.CompileM.constantInfoRootExprs c.info).mapM (expandExpr tbl tbl.size))
        let rootsE := match rootsE with | .ok r => r | .error _ => #[]
        let limits : Ix.Sharing.Exact.Limits := { maxStates := opts.uniMaxStates }
        let sharingIn := c.sharing
        let rootsIn := Ix.Sharing.Exact.constantInfoRoots c.info
        let mut uni : Array UniStats := #[]
        for w in [1, 2, 3] do
          let t0 ← IO.monoNanosNow
          match Ix.Sharing.Exact.optimizeSharingUniformTable w sharingIn rootsIn limits with
          | .error err =>
            let t1 ← IO.monoNanosNow
            uni := uni.push { err := toString err, ns := t1 - t0 }
          | .ok u =>
            let t1 ← IO.monoNanosNow
            let st := uniStats c rootsE row.fixed u (t1 - t0)
            if st.checkErr.isSome || !st.variableOk then
              IO.println s!"[sharing-study] UNIFORM CHECK FAILURE {name} w={w}: {st.checkErr}, variableOk={st.variableOk}"
            if t1 - t0 > 2000000000 then
              IO.println s!"[sharing-study] slow uniform: {name} w={w} {(t1 - t0) / 1000000} ms, largest component {st.counts.comp}, states {st.states}"
            uni := uni.push st
        row := { row with uni }
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
  md := md ++ s!"- Production rebuild (`buildConstantWithSharing` on expanded roots, then `serConstant`) differs from `rawBytes`: **{mismatches}** constants.\n"
  md := md ++ s!"- Decode/encode roundtrip (`serConstant ∘ get`) differs from `rawBytes`: {rtFail.size} constants.\n"
  md := md ++ s!"- Compositional unshared size checked against `serConstant` of the real unshared Constant: {valOk} equal, {valFail.size} different, {valSkip.size} not checked (unshared roots > {opts.validateMax} bytes).\n"
  md := md ++ s!"- `usageCount` (occ) checked against a brute-force walk of the fully expanded roots: {occOk} equal, {occFail.size} different, {occSkip} not checked (unshared roots > {opts.occCheckMax} bytes).\n"
  md := md ++ s!"- Constants whose stored (heuristic) bytes exceed their unshared bytes: {worse.size}.\n"
  md := md ++ s!"- Total `rawBytes.size`: {sumRaw}; total unshared Constant bytes: {sumUn}.\n\n"
  unless mismatches == 0 do
    md := md ++ "### Rebuild mismatches (first 20)\n\n| constant | kind | stored B | stored table | rebuilt B | rebuilt table | first diff |\n|---|---|---:|---:|---:|---:|---:|\n"
    for r in (rows.filter (!·.rebuildOk)).extract 0 20 do
      md := md ++ s!"| `{r.name}` | {r.kind} | {r.raw} | {r.table} | {r.rebuiltSize} | {r.rebuiltTable} | {r.firstDiff} |\n"
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
  md := md ++ "\n" ++ uwReport rows
  md := md ++ "\n" ++ schemeReport rows
  if opts.uniform then
    md := md ++ "\n" ++ uniformReport rows opts.uniMaxStates
  md := md ++ "\n" ++ tagNReport rows
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
    occFail.isEmpty && !mssFail && !rows.any (·.uwErr.isSome) &&
    !rows.any (fun r => r.uw.any (·.compCheck == some false)) &&
    !rows.any (fun r => mssRefTotal r != r.mssDegSum) &&
    !rows.any (fun r => mssRefTotalE r != mssRefTotal r) &&
    !rows.any (fun r => bucketTotal r.mssRefsF != mssRefTotal r ||
      bucketTotal r.mssRefsG != mssRefTotal r) &&
    !rows.any (fun r => r.lad.total != r.raw) &&
    !rows.any (fun r => r.uni.any fun u => u.ok && (u.checkErr.isSome || !u.variableOk)) then 0 else 1)

end Benchmarks.SharingStudy

def main (args : List String) : IO UInt32 := Benchmarks.SharingStudy.main args
