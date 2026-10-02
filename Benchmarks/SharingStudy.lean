import Ix.CompileM

/-!
# Sharing corpus study

Loads a serialized `Ixon.Env` (`.ixe`) and, for every stored constant:

1. Expands the stored sharing table left to right. Entry `i` may reference
   only entries `j < i`; each `Share j` is replaced by the *same* in-memory
   expansion of entry `j`, so repeated indices share one subtree and the
   expanded roots form a DAG whose size is linear in the stored bytes.
   The ordered roots come from `Ix.Sharing.Exact.constantInfoRoots`.
2. Rebuilds the constant with the production route
   (`Ix.CompileM.buildConstantWithSharing` under `compilerSharingLimits` on the
   expanded roots, i.e. the canonical tiered construction) and checks that
   `Ixon.serConstant` reproduces the stored bytes exactly. It also checks the
   plain decode/encode roundtrip. This is the Lean side's whole-corpus rebuild
   check; the harness exits 1 on any mismatch.
3. Hash-conses the expanded roots (`analyzeBlock`: blake3 Merkle hashes; hash
   equality is treated as structural equality) and computes, per constant, the
   distinct subterm count `N`, the longest App/Lam/All telescope and the
   standalone unshared `putExpr` length of every subterm, compositionally on
   the DAG with the App/Lam/All telescope rules. The unshared complete-Constant
   size is checked against `serConstant` of the actual unshared constant
   whenever the unshared root bytes are at most `--validate-max` (so no
   exponential tree is ever serialized).
4. Builds the "maximal structural sharing" (MSS) baseline encoding (see
   `mssBuild`), serializes it with `serConstant`, decodes and expands it again
   and checks the expanded roots equal the original ones exactly, and compares
   it with the canonical encoding. The `docs/sharing-minimum.md` §2 witnesses
   are run through the same path at startup.

```
lake exe sharing-study <corpus.ixe> [--md <path>] [--csv <path>]
                       [--limit <n>] [--validate-max <bytes>] [--progress <n>]
```
-/

namespace Benchmarks.SharingStudy

open Ixon (Expr Constant ConstantInfo MutConst)

/-! ## Hash-consing analysis

Harness-local structural analysis: blake3 Merkle hashes over the canonical node
headers, a pointer-to-hash cache and a leaves-first traversal order. Production
sharing is the canonical tiered construction (`Ix.Sharing.Exact`); nothing here
is on the compiler route. -/

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
        { baseSize := (Ixon.runPut (putNodeHeader e)).size, expr := e,
          children := childHashes }
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

/-- Hash-cons `exprs`, left to right. -/
def analyzeBlock (exprs : Array Expr) : AnalyzeResult :=
  let st := exprs.foldl (init := ({} : AnalyzeState)) fun st e => ((hashAndAnalyze e).run st).2
  { infoMap := st.infoMap, ptrToHash := st.ptrToHash, topoOrder := st.topoOrder }

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

/-- Put `roots` back into `info` in `Ix.Sharing.Exact.constantInfoRoots` order
(`Ix.Sharing.Exact.withRoots`, which checks the root count). -/
def replaceRoots (info : ConstantInfo) (roots : Array Expr) : Except String ConstantInfo :=
  (Ix.Sharing.Exact.withRoots info roots).mapError toString

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

/-- Width of a TagN integer with a 4-bit flag (an expression header). -/
def tagN4Size (n : Nat) : Nat := Ixon.tagNByteWidth 4 n
/-- Width of a flagless TagN integer (counts and indices). -/
def tagN0Size (n : Nat) : Nat := Ixon.tagNByteWidth 0 n

structure DagStats where
  n : Nat := 0
  maxApp : Nat := 0
  maxLam : Nat := 0
  maxAll : Nat := 0
  rootSizes : Array Nat := #[]
  deriving Inhabited

/-- Hash-cons the roots and compute `N`, telescope maxima and root unshared
sizes. Mirrors `putExpr`: an App telescope writes `TagN4(#args)`, its head,
then its arguments; Lam/All telescopes write `TagN4(#binders)`, then one
contract byte and the type per binder, then the body. Prj/Let/leaves are the
node header (`SubtermInfo.baseSize`, which is `putNodeHeader`, i.e. the full
`putExpr` for leaves) plus the children. -/
def dagStats (res : AnalyzeResult) (roots : Array Expr) :
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
        { sz := tagN4Size tele + payload, fam := 1, tele, payload }
      | .lam .. =>
        let t := child 0
        let b := child 1
        let tele := if b.fam == 2 then b.tele + 1 else 1
        let payload := 1 + t.sz + (if b.fam == 2 then b.payload else b.sz)
        { sz := tagN4Size tele + payload, fam := 2, tele, payload }
      | .all .. =>
        let t := child 0
        let b := child 1
        let tele := if b.fam == 3 then b.tele + 1 else 1
        let payload := 1 + t.sz + (if b.fam == 3 then b.payload else b.sz)
        { sz := tagN4Size tele + payload, fam := 3, tele, payload }
      | _ =>
        { sz := info.children.foldl (init := info.baseSize) fun acc c =>
            acc + (sizes.getD c default).sz }
    if node.fam == 1 then st := { st with maxApp := max st.maxApp node.tele }
    else if node.fam == 2 then st := { st with maxLam := max st.maxLam node.tele }
    else if node.fam == 3 then st := { st with maxAll := max st.maxAll node.tele }
    sizes := sizes.insert h node
  let rootSizes := roots.map fun r =>
    match res.ptrToHash.get? (exprPtr r) with
    | some h => (sizes.getD h default).sz
    | none => 0
  return ({ st with rootSizes }, sizes)

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
   equal to `t`. This is the compact indegree, not the number of occurrences
   in the expanded roots.
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
  -- 5. Materialize with the harness-local rewrite helpers.
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
      let payload := (Ixon.serExpr entry).size - tagN4Size (teleCount entry)
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
  let rs ← (Ix.Sharing.Exact.constantInfoRoots c.info).mapM (expandExpr tbl tbl.size)
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
    (validateMax : Nat) : Except String Row := do
  let roundtrip := Ixon.serConstant c
  let tbl ← expandTable c.sharing
  let stored := Ix.Sharing.Exact.constantInfoRoots c.info
  let roots ← stored.mapM (expandExpr tbl tbl.size) |>.mapError (s!"root: " ++ ·)
  let expanded ← replaceRoots c.info roots
  -- 1. Canonical rebuild from the expanded roots (the production route).
  let rebuilt ← (Ix.CompileM.buildConstantWithSharing Ix.CompileM.compilerSharingLimits
      expanded c.refs c.univs).mapError (s!"canonical: " ++ toString ·)
  let rebuiltBytes := Ixon.serConstant rebuilt
  let diff := firstDiff rebuiltBytes raw
  -- 2. DAG statistics.
  let res := analyzeBlock roots
  let (ds, sizes) := dagStats res roots
  -- 3. Unshared complete-Constant size: bytes outside expressions are fixed.
  let storedExprBytes :=
    c.sharing.foldl (fun acc e => acc + (Ixon.serExpr e).size) 0 +
    stored.foldl (fun acc e => acc + (Ixon.serExpr e).size) 0
  let overhead := tagN0Size c.sharing.size + storedExprBytes
  if overhead > raw.size then
    throw s!"stored expression bytes {overhead} exceed constant bytes {raw.size}"
  let fixed := raw.size - overhead
  let rootTotal := ds.rootSizes.foldl (· + ·) 0
  let unshared := fixed + tagN0Size 0 + rootTotal
  let (validated, serUnsharedSize) :=
    if rootTotal ≤ validateMax then
      let u : Constant :=
        { info := expanded, sharing := #[], refs := c.refs, univs := c.univs }
      let s := (Ixon.serConstant u).size
      (some (s == unshared), s)
    else (none, 0)
  -- 4. Maximal structural sharing, serialized and checked.
  let (mss, mssTable, mssErr, mssCounts, mssRefs, mssDegSum) :=
    match mssBuild res sizes roots with
    | .error e => (0, 0, some s!"build: {e}", (0, 0, 0), (0, 0, 0), 0)
    | .ok m =>
      match replaceRoots c.info m.roots with
      | .error e => (0, 0, some s!"roots: {e}", (0, 0, 0), (0, 0, 0), 0)
      | .ok info =>
        let mc : Constant :=
          { info, sharing := m.table, refs := c.refs, univs := c.univs }
        let b := Ixon.serConstant mc
        let err := match mssCheck b roots with
          | .ok () => none
          | .error e => some s!"check: {e}"
        (b.size, m.table.size, err, (m.cont, m.contP2, m.contP2u), m.refs, m.degSum)
  return {
    mss, mssTable, mssErr, mssRefs, mssDegSum
    cont := mssCounts.1, contP2 := mssCounts.2.1, contP2u := mssCounts.2.2
    addr, name, kind := kindOf c.info, detail := mutsDetail c.info
    roots := roots.size, n := ds.n, table := c.sharing.size
    raw := raw.size, unshared, canonical := rebuiltBytes.size
    canonicalTable := rebuilt.sharing.size, rebuildOk := diff.isNone
    firstDiff := diff, roundtripOk := (firstDiff roundtrip raw).isNone
    maxApp := ds.maxApp, maxLam := ds.maxLam, maxAll := ds.maxAll
    validated, serUnsharedSize }

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

/-- The MSS encoding of an unshared constant: its bytes and its roots. -/
def mssBytes (c : Constant) : Except String (ByteArray × Array Expr) := do
  let roots := Ix.Sharing.Exact.constantInfoRoots c.info
  let res := analyzeBlock roots
  let (_, sizes) := dagStats res roots
  let m ← mssBuild res sizes roots
  let info ← replaceRoots c.info m.roots
  return (Ixon.serConstant { c with info, sharing := m.table }, roots)

def runWitness (label expected : String) (c : Constant) : Except String Witness := do
  let (mb, roots) ← mssBytes c
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
  match mssBytes (witnessAxiom (.all .many .shared t2 t2) #[.zero]) with
  | .error e => #[(s!"MSS build failed: {e}", false)]
  | .ok (mb, roots) =>
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
    distRow "stored table size" (rows.map (·.table)),
    distRow "canonical table size" (rows.map (·.canonicalTable)),
    distRow "`rawBytes.size`" (rows.map (·.raw)),
    distRow "canonical Constant bytes" (rows.map (·.canonical)),
    distRow "unshared Constant bytes" (rows.map (·.unshared)),
    distRow "max telescope length" (rows.map fun r => max r.maxApp (max r.maxLam r.maxAll)),
    distRow "roots" (rows.map (·.roots))]
  hdr ++ "\n" ++ "\n".intercalate lines.toList

def csvEscape (s : String) : String := "\"" ++ s.replace "\"" "\"\"" ++ "\""

def csvHeader : String :=
  "addr,name,kind,members,roots,N,table,raw_bytes," ++
  "unshared_bytes,canonical_bytes,canonical_table,rebuild_ok,roundtrip_ok,unshared_validated," ++
  "max_app,max_lam,max_all,us," ++
  "mss_bytes,mss_table,mss_ok,mss_cont,mss_cont_p2,mss_cont_p2u," ++
  "mss_refs_lt8,mss_refs_8_1031,mss_refs_ge1032,mss_deg_sum"

def csvLine (r : Row) : String :=
  let v := match r.validated with | some true => "1" | some false => "0" | none => ""
  s!"{(toString r.addr).take 16},{csvEscape r.name},{r.kind},{r.detail},{r.roots},{r.n}," ++
  s!"{r.table},{r.raw},{r.unshared}," ++
  s!"{r.canonical},{r.canonicalTable}," ++
  s!"{if r.rebuildOk then 1 else 0},{if r.roundtripOk then 1 else 0},{v}," ++
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
  md := md ++ "Rule: store exactly the subterms with compact-DAG indegree `deg ≥ 2` (edges with multiplicity plus root occurrences) and unshared size > 1; every occurrence of a stored term is a Share; order by priority topological order (largest `deg`, then smaller blake3 hash bytes). Built with the harness-local `buildSharingEntries`/`rewriteExprs`, placed with `Ix.Sharing.Exact.withRoots`, serialized with `serConstant`.\n\n"
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

/-! ## Driver -/

structure Opts where
  corpus : String := ""
  md : Option String := none
  csv : Option String := none
  limit : Option Nat := none
  validateMax : Nat := 16777216
  progress : Nat := 5000

def parseArgs : List String → Opts → Except String Opts
  | [], o => if o.corpus.isEmpty then .error "missing corpus path" else .ok o
  | "--md" :: p :: rest, o => parseArgs rest { o with md := some p }
  | "--csv" :: p :: rest, o => parseArgs rest { o with csv := some p }
  | "--limit" :: n :: rest, o => parseArgs rest { o with limit := n.toNat? }
  | "--validate-max" :: n :: rest, o =>
    parseArgs rest { o with validateMax := n.toNat?.getD o.validateMax }
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
      IO.eprintln s!"sharing-study: {e}\nusage: sharing-study <corpus.ixe> [--md p] [--csv p] [--limit n] [--validate-max bytes] [--progress n]"
      return 2
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
    match measure addr name raw c opts.validateMax with
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
  md := md ++ "### Totals by ConstantInfo kind\n\n| kind | constants | `rawBytes.size` | unshared bytes | stored/unshared | table entries | stored > unshared |\n|---|---:|---:|---:|---:|---:|---:|\n"
  for k in kindOrder do
    let ks := rows.filter (·.kind == k)
    unless ks.isEmpty do
      let r := ks.foldl (· + ·.raw) 0
      let u := ks.foldl (· + ·.unshared) 0
      let t := ks.foldl (· + ·.table) 0
      let w := (ks.filter fun x => x.raw > x.unshared).size
      md := md ++ s!"| {k} | {ks.size} | {r} | {u} | {fmtPct r u} | {t} | {w} |\n"
  md := md ++ s!"| **all** | {rows.size} | {sumRaw} | {sumUn} | {fmtPct sumRaw sumUn} | {rows.foldl (· + ·.table) 0} | {worse.size} |\n\n"
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
    !mssFail &&
    !rows.any (fun r => mssRefTotal r != r.mssDegSum) then 0 else 1)

end Benchmarks.SharingStudy

def main (args : List String) : IO UInt32 := Benchmarks.SharingStudy.main args
