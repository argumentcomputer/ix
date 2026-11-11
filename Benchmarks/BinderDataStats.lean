import Ix.Ixon
import Ix.Ixon.CheckOrder
import IxC.Ixon.WireCheck

/-!
# Binder-data sections of a compiled environment (manual measurement)

`binder-data-stats stats A.ixe` reports the sections the records of `A` carry:
their sizes (median, p90, p99, max, total), blocks, extra variants, undecided
nodes, canonical form, and the BLAKE3 compressions they add to their records'
hashes.

`binder-data-stats compare A.ixe B.ixe` compares, name by name, the binder data
of the records (the blocks owning them) in two compiles of the same source:
each root's data in pre-order, every share node replaced by its entry's data at
the variant it names (at most `IX_BDS_NODES` data per root, default 1000000).
It says how many owners agree, and lists the first that do not.
-/

namespace Benchmarks.BinderDataStats

/-- BLAKE3 compressions of a `len`-byte message: 64-byte blocks per 1024-byte
chunk (at least one), plus one per parent node of the chunk tree. -/
def compressions (len : Nat) : Nat :=
  if len == 0 then 1 else
  let chunks := (len + 1023) / 1024
  let rest := len % 1024
  let blocks := (len / 1024) * 16 + (if rest == 0 then 0 else (rest + 63) / 64)
  blocks + (chunks - 1)

def pct (sorted : Array Nat) (p : Nat) : Nat :=
  if sorted.isEmpty then 0 else sorted[min (sorted.size - 1) (sorted.size * p / 100)]!

def load (path : String) : IO Ixon.Env := do
  IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))

def records (env : Ixon.Env) : IO (Array (Address × Ixon.Constant × Nat)) := do
  let mut out := #[]
  for (a, lc) in env.consts do
    match lc.get with
    | .ok c => out := out.push (a, c, lc.rawBytes.size)
    | .error e => throw (IO.userError s!"record {a} does not decode: {e}")
  return out

def stats (path : String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let env ← load path
  let recs ← records env
  let mut sizes : Array Nat := #[]
  let mut totalSection := 0
  let mut totalRecord := 0
  let mut withData := 0
  let mut blocks := 0
  let mut extraVariants := 0
  let mut nodes := 0
  let mut undecidedNodes := 0
  let mut undecidedRecords := 0
  let mut noncanonical := 0
  let mut incomplete := 0
  let mut compRecord := 0
  let mut compAdded := 0
  let mut addedSizes : Array Nat := #[]
  for (_, c, len) in recs do
    let sec := (Ixon.runPut (Ixon.putBinders c.binders)).size
    totalSection := totalSection + sec
    totalRecord := totalRecord + len
    let full := compressions len
    let without := compressions (len + 1 - sec)
    compRecord := compRecord + full
    compAdded := compAdded + (full - without)
    unless c.bindersCanonical do noncanonical := noncanonical + 1
    unless c.bindersComplete do incomplete := incomplete + 1
    unless c.binders.isEmpty do
      withData := withData + 1
      sizes := sizes.push sec
      addedSizes := addedSizes.push (full - without)
      blocks := blocks + c.binders.size
      extraVariants := extraVariants + (c.binders.filter (·.variant > 0)).size
      let u := c.binders.foldl (fun n b => n + (b.nodes.filter (· == .undecided)).size) (0 : Nat)
      nodes := c.binders.foldl (fun n b => n + b.nodes.size) nodes
      undecidedNodes := undecidedNodes + u
      if u > 0 then undecidedRecords := undecidedRecords + 1
  let sorted := sizes.qsort (· < ·)
  let added := addedSizes.qsort (· < ·)
  IO.println s!"BDSTATS {path}: records={recs.size} with_data={withData} record_bytes={totalRecord} \
section_bytes={totalSection} section_bytes_over_empty={totalSection - recs.size} \
median={pct sorted 50} p90={pct sorted 90} p99={pct sorted 99} max={sorted.back?.getD 0} \
blocks={blocks} extra_variants={extraVariants} nodes={nodes} undecided_nodes={undecidedNodes} \
undecided_records={undecidedRecords} noncanonical={noncanonical} incomplete={incomplete} \
blake3_record={compRecord} blake3_added={compAdded} added_median={pct added 50} \
added_p90={pct added 90} added_max={added.back?.getD 0} ({(← IO.monoMsNow) - t0}ms)"
  return 0

/-! ## Comparing two compiles -/

/-- The data of `e` in pre-order, each binderful share replaced by its entry's
data at the variant the section names; `none` where the section does not fit. -/
partial def expand (c : Ixon.Constant) (full : Array Bool)
    (blocks : Std.HashMap (Bool × UInt64 × UInt64) (Array Ixon.BinderNode)) (limit : Nat) :
    Ixon.Expr → Array Ixon.BinderNode → Nat → Array Ixon.BinderNode → Option (Nat × Array Ixon.BinderNode)
  | e, nodes, ord, out => do
    if out.size > limit then return (ord, out)
    match e with
    | .lam _ t b | .all _ _ t b =>
      let n ← nodes[ord]?
      if let .share _ := n then none
      let (ord, out) ← expand c full blocks limit t nodes (ord + 1) (out.push n)
      expand c full blocks limit b nodes ord out
    | .app f a =>
      let (ord, out) ← expand c full blocks limit f nodes ord out
      expand c full blocks limit a nodes ord out
    | .letE _ t v b =>
      let (ord, out) ← expand c full blocks limit t nodes ord out
      let (ord, out) ← expand c full blocks limit v nodes ord out
      expand c full blocks limit b nodes ord out
    | .prj _ _ v => expand c full blocks limit v nodes ord out
    | .share n =>
      if !(full[n.toNat]?.getD false) then return (ord, out)
      let .share v ← nodes[ord]? | none
      let entry ← c.sharing[n.toNat]?
      let sub ← blocks[(true, n, v)]?
      let (_, out) ← expand c full blocks limit entry sub 0 out
      return (ord + 1, out)
    | _ => return (ord, out)

/-- Every root's expanded data. -/
def expanded (c : Ixon.Constant) (limit : Nat) : Option (Array (Array Ixon.BinderNode)) := do
  let full := Ixon.binderfulEntries c.sharing
  let blocks : Std.HashMap (Bool × UInt64 × UInt64) (Array Ixon.BinderNode) :=
    c.binders.foldl (fun m b => m.insert (b.shared, b.index, b.variant) b.nodes) {}
  let roots := c.info.binderRoots
  let mut out := #[]
  for h : r in [:roots.size] do
    let nodes := blocks[(false, r.toUInt64, (0 : UInt64))]?.getD #[]
    let (_, data) ← expand c full blocks limit roots[r] nodes 0 #[]
    out := out.push data
  return out

def ownerOf (env : Ixon.Env) (a : Address) : Option (Address × Ixon.Constant) := do
  let c ← env.getConst? a
  let o := Ixon.CheckOrder.owner a c
  return (o, ← env.getConst? o)

def compare (pathA pathB : String) : IO UInt32 := do
  let limit := ((← IO.getEnv "IX_BDS_NODES").bind (·.toNat?)).getD 1000000
  let a ← load pathA
  let b ← load pathB
  let mut seen : Std.HashSet Address := {}
  let mut compared := 0
  let mut equalSections := 0
  let mut equalData := 0
  let mut differ := 0
  let mut unreadable := 0
  let mut missing := 0
  let mut binders := 0
  let mut shown := 0
  for (n, named) in a.named do
    let some (oa, ca) := ownerOf a named.addr | continue
    if seen.contains oa then continue
    seen := seen.insert oa
    let some nb := b.named.get? n | missing := missing + 1; continue
    let some (_, cb) := ownerOf b nb.addr | missing := missing + 1; continue
    compared := compared + 1
    if ca.binders == cb.binders then
      equalSections := equalSections + 1
      equalData := equalData + 1
      continue
    match expanded ca limit, expanded cb limit with
    | some da, some db =>
      binders := binders + da.foldl (· + ·.size) 0
      if da == db then equalData := equalData + 1
      else
        differ := differ + 1
        if shown < 20 then
          shown := shown + 1
          let r := (List.range da.size).find? (fun i => da[i]? != db[i]?) |>.getD 0
          let j := (List.range ((da[r]?.getD #[]).size)).find?
            (fun j => (da[r]?.getD #[])[j]? != (db[r]?.getD #[])[j]?) |>.getD 0
          IO.println s!"BDCMP differs {n.pretty} root {r} datum {j}: \
{repr ((da[r]?.getD #[])[j]?)} vs {repr ((db[r]?.getD #[])[j]?)}"
    | _, _ =>
      unreadable := unreadable + 1
      if shown < 20 then
        shown := shown + 1
        IO.println s!"BDCMP unreadable section {n.pretty}"
  IO.println s!"BDCMP {pathA} vs {pathB}: owners={compared} equal_sections={equalSections} \
equal_data={equalData} differ={differ} unreadable={unreadable} missing={missing} \
data_compared_in_differing_sections={binders}"
  return if differ == 0 && unreadable == 0 then 0 else 1

/-! ## Why two compiles' sections differ -/

/-- The refs table is strictly ascending by address bytes. -/
def refsSorted (c : Ixon.Constant) : Bool :=
  (List.range (c.refs.size - 1)).all fun i => (c.refs[i]!.cmpBytes c.refs[i + 1]!) == .lt

/-- For owners whose sections differ, whether their payloads, sharing and refs
order agree; the names one artifact has and the other lacks. -/
def diag (pathA pathB : String) : IO UInt32 := do
  let a ← load pathA
  let b ← load pathB
  let mut seen : Std.HashSet Address := {}
  let mut differ := 0
  let mut sameInfo := 0
  let mut sameSharing := 0
  let mut sameRefs := 0
  let mut sortedA := 0
  let mut sortedB := 0
  let mut completeA := 0
  let mut completeB := 0
  let mut shown := 0
  let mut missing : Array String := #[]
  for (n, named) in a.named do
    let some (oa, ca) := ownerOf a named.addr | continue
    if seen.contains oa then continue
    seen := seen.insert oa
    let some nb := b.named.get? n | do missing := missing.push n.pretty; continue
    let some (_, cb) := ownerOf b nb.addr | do missing := missing.push s!"{n.pretty} (no owner)"; continue
    if ca.binders == cb.binders then continue
    differ := differ + 1
    if ca.info == cb.info then sameInfo := sameInfo + 1
    if ca.sharing == cb.sharing then sameSharing := sameSharing + 1
    if ca.refs.size == cb.refs.size then sameRefs := sameRefs + 1
    if refsSorted ca then sortedA := sortedA + 1
    if refsSorted cb then sortedB := sortedB + 1
    if ca.bindersComplete then completeA := completeA + 1
    if cb.bindersComplete then completeB := completeB + 1
    if shown < 5 && ca.info == cb.info && ca.sharing == cb.sharing then
      shown := shown + 1
      IO.println s!"BDDIAG same payload, sections differ: {n.pretty}\n  A {repr ca.binders}\n  B {repr cb.binders}"
  let unsortedA := (← records a).filter (fun (_, c, _) => !refsSorted c) |>.size
  let unsortedB := (← records b).filter (fun (_, c, _) => !refsSorted c) |>.size
  IO.println s!"BDDIAG {pathA} vs {pathB}: owners with different sections={differ} same_info={sameInfo} \
same_sharing={sameSharing} same_refs_count={sameRefs} refs_sorted_A={sortedA} refs_sorted_B={sortedB} \
complete_A={completeA} complete_B={completeB}; records with unsorted refs: A={unsortedA} B={unsortedB}; \
missing in B={missing.size}"
  for m in missing.extract 0 20 do IO.println s!"BDDIAG missing in B: {m}"
  return 0

end Benchmarks.BinderDataStats

def main (args : List String) : IO UInt32 := do
  match args with
  | ["stats", path] => Benchmarks.BinderDataStats.stats path
  | ["compare", a, b] => Benchmarks.BinderDataStats.compare a b
  | ["diag", a, b] => Benchmarks.BinderDataStats.diag a b
  | _ =>
    IO.eprintln "usage: binder-data-stats stats A.ixe | compare A.ixe B.ixe"
    return 2
