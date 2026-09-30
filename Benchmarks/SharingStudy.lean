import Ix.CompileM

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

```
lake exe sharing-study <corpus.ixe> [--md <path>] [--csv <path>]
                       [--limit <n>] [--validate-max <bytes>]
                       [--occ-check-max <bytes>] [--progress <n>]
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
  let mut out : MssResult := { table := st.sharingVec, roots := newRoots }
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
  let (mss, mssTable, mssErr, mssCounts) :=
    match mssBuild res sizes roots with
    | .error e => (0, 0, some s!"build: {e}", (0, 0, 0))
    | .ok m =>
      let mc : Constant :=
        { info := replaceRoots c.info m.roots, sharing := m.table, refs := c.refs, univs := c.univs }
      let b := Ixon.serConstant mc
      let err := match mssCheck b roots with
        | .ok () => none
        | .error e => some s!"check: {e}"
      (b.size, m.table.size, err, (m.cont, m.contP2, m.contP2u))
  return {
    mss, mssTable, mssErr
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

def csvEscape (s : String) : String := "\"" ++ s.replace "\"" "\"\"" ++ "\""

def csvHeader : String :=
  "addr,name,kind,members,roots,N,occ_ge2,cand,cand_gt2,cand_gt3,table,raw_bytes," ++
  "unshared_bytes,rebuild_ok,roundtrip_ok,unshared_validated,occ_checked,max_app,max_lam,max_all,us," ++
  "mss_bytes,mss_table,mss_ok,mss_cont,mss_cont_p2,mss_cont_p2u"

def csvLine (r : Row) : String :=
  let v := match r.validated with | some true => "1" | some false => "0" | none => ""
  let o := match r.occCheck with | some true => "1" | some false => "0" | none => ""
  s!"{(toString r.addr).take 16},{csvEscape r.name},{r.kind},{r.detail},{r.roots},{r.n}," ++
  s!"{r.occ2},{r.cand},{r.cand2},{r.cand3},{r.table},{r.raw},{r.unshared}," ++
  s!"{if r.rebuildOk then 1 else 0},{if r.roundtripOk then 1 else 0},{v},{o}," ++
  s!"{r.maxApp},{r.maxLam},{r.maxAll},{r.ns / 1000}," ++
  s!"{r.mss},{r.mssTable},{if r.mssErr.isNone then 1 else 0},{r.cont},{r.contP2},{r.contP2u}"

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

/-! ## Driver -/

structure Opts where
  corpus : String := ""
  md : Option String := none
  csv : Option String := none
  limit : Option Nat := none
  validateMax : Nat := 16777216
  occCheckMax : Nat := 65536
  progress : Nat := 5000

def parseArgs : List String → Opts → Except String Opts
  | [], o => if o.corpus.isEmpty then .error "missing corpus path" else .ok o
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
      IO.eprintln s!"sharing-study: {e}\nusage: sharing-study <corpus.ixe> [--md p] [--csv p] [--limit n] [--validate-max bytes] [--occ-check-max bytes] [--progress n]"
      return 2
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
    occFail.isEmpty && !mssFail then 0 else 1)

end Benchmarks.SharingStudy

def main (args : List String) : IO UInt32 := Benchmarks.SharingStudy.main args
