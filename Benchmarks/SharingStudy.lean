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
def dagStats (roots : Array Expr) (occCheckMax : Nat) : DagStats := Id.run do
  let res := Ix.Sharing.analyzeBlock roots
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
  return { st with rootSizes, occCheck }

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
  ns : Nat := 0
  deriving Inhabited

def firstDiff (a b : ByteArray) : Option Nat := Id.run do
  let n := min a.size b.size
  for i in [0:n] do
    if a[i]! != b[i]! then return some i
  if a.size == b.size then none else some n

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
  let ds := dagStats roots occCheckMax
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
  return {
    addr, name, kind := kindOf c.info, detail := mutsDetail c.info
    roots := roots.size, n := ds.n, occ2 := ds.occ2, cand := ds.cand
    cand2 := ds.cand2, cand3 := ds.cand3, table := c.sharing.size
    raw := raw.size, unshared, rebuiltSize := rebuiltBytes.size
    rebuiltTable := rebuilt.sharing.size, rebuildOk := diff.isNone
    firstDiff := diff, roundtripOk := (firstDiff roundtrip raw).isNone
    maxApp := ds.maxApp, maxLam := ds.maxLam, maxAll := ds.maxAll
    validated, serUnsharedSize, occCheck := ds.occCheck }

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
  "unshared_bytes,rebuild_ok,roundtrip_ok,unshared_validated,occ_checked,max_app,max_lam,max_all,us"

def csvLine (r : Row) : String :=
  let v := match r.validated with | some true => "1" | some false => "0" | none => ""
  let o := match r.occCheck with | some true => "1" | some false => "0" | none => ""
  s!"{(toString r.addr).take 16},{csvEscape r.name},{r.kind},{r.detail},{r.roots},{r.n}," ++
  s!"{r.occ2},{r.cand},{r.cand2},{r.cand3},{r.table},{r.raw},{r.unshared}," ++
  s!"{if r.rebuildOk then 1 else 0},{if r.roundtripOk then 1 else 0},{v},{o}," ++
  s!"{r.maxApp},{r.maxLam},{r.maxAll},{r.ns / 1000}"

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

def kindOrder : Array String :=
  #["defn", "recr", "axio", "quot", "muts", "iPrj", "cPrj", "rPrj", "dPrj"]

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
  return (if mismatches == 0 && skipped.isEmpty && valFail.isEmpty && rtFail.isEmpty &&
    occFail.isEmpty then 0 else 1)

end Benchmarks.SharingStudy

def main (args : List String) : IO UInt32 := Benchmarks.SharingStudy.main args
