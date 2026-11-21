import Ix.Ixon
import Ix.Ixon.CheckOrder
import IxC.Ixon.WireCheck
import Ix.Compile.BinderData

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
      let u := c.binders.foldl (fun n b => n + (b.nodes.filter (·.isUndecided)).size) (0 : Nat)
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
    | .lam t b | .all t b =>
      let n ← nodes[ord]?
      if let .share _ := n then none
      let (ord, out) ← expand c full blocks limit t nodes (ord + 1) (out.push n)
      expand c full blocks limit b nodes ord out
    | .app f a =>
      let (ord, out) ← expand c full blocks limit f nodes ord out
      expand c full blocks limit a nodes ord out
    | .letE _ _ t v b =>
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

/-! ## Two artifacts' records, by address -/

/-- The records two artifacts hold, by address (an address is the hash of the
record's bytes, so a record whose bytes differ is in one only): how many each
holds that the other does not, how many names sit at different addresses, the
first few records of `A` that `B` lacks (with the names `A` gives them, if
any), and each artifact's role-binding address. -/
def addrs (pathA pathB : String) : IO UInt32 := do
  let a ← load pathA
  let b ← load pathB
  let onlyA := a.consts.fold (init := #[]) fun out addr _ =>
    if b.consts.contains addr then out else out.push addr
  let onlyB := b.consts.fold (init := 0) fun n addr _ => if a.consts.contains addr then n else n + 1
  let mut namesAt : Std.HashMap Address (Array String) := {}
  let mut moved := 0
  for (n, named) in a.named do
    namesAt := namesAt.insert named.addr ((namesAt.getD named.addr #[]).push n.pretty)
    match b.named.get? n with
    | some nb => if nb.addr != named.addr then moved := moved + 1
    | none => pure ()
  let shown := (onlyA.qsort (fun x y => x.cmpBytes y == .lt)).extract 0 12
  for addr in shown do
    let names := (namesAt.getD addr #[]).extract 0 3
    IO.println s!"BDADDR only in A: {addr} names={names}"
  let bind (e : Ixon.Env) : String := match e.roleBinding with
    | some r => toString r.address
    | none => "none"
  IO.println s!"BDADDR {pathA} vs {pathB}: records A={a.consts.size} B={b.consts.size} \
only_A={onlyA.size} only_B={onlyB} names_at_other_addresses={moved} binding_A={bind a} \
binding_B={bind b}"
  return if onlyA.isEmpty && onlyB == 0 then 0 else 1

/-- Whether a member of `c` is unsafe or partial (such records carry the undecided section). -/
def unsafeOrPartial (c : Ixon.Constant) : Bool :=
  let defn (d : Ixon.Definition) : Bool := match d.safety with
    | .safe => false
    | _ => true
  match c.info with
  | .defn d => defn d
  | .recr r => r.isUnsafe
  | .axio a => a.isUnsafe
  | .muts ms => ms.any fun
    | .defn d => defn d
    | .indc i => i.isUnsafe || i.ctors.any (·.isUnsafe)
    | .recr r => r.isUnsafe
  | _ => false

/-- **The safe records of an artifact with an undecided binder**, named. -/
def undecided (path : String) : IO UInt32 := do
  let e ← load path
  let mut addrs : Array Address := #[]
  for (a, lc) in e.consts do
    if let some c := lc.get? then
      if !unsafeOrPartial c && c.binders.any (·.nodes.any (·.isUndecided)) then
        addrs := addrs.push a
  let names := Ix.Compile.BinderData.namesOf e (addrs.foldl (·.insert ·) {})
  IO.println s!"BDUND {path}: safe_undecided={addrs.size}"
  for a in addrs do IO.println s!"BDUND {names.getD a "?"} {a}"
  return 0

/-- The refs-table indices an expression names (`ref` targets and projection
types), through the record's shares. -/
partial def refIdxs (c : Ixon.Constant) (seen : Std.HashSet Nat) (acc : Std.HashSet Nat) :
    Ixon.Expr → Std.HashSet Nat × Std.HashSet Nat
  | .ref i _ => (seen, acc.insert i.toNat)
  | .prj i _ v => refIdxs c seen (acc.insert i.toNat) v
  | .app f a =>
    let (seen, acc) := refIdxs c seen acc f
    refIdxs c seen acc a
  | .lam t b | .all t b =>
    let (seen, acc) := refIdxs c seen acc t
    refIdxs c seen acc b
  | .letE _ _ t v b =>
    let (seen, acc) := refIdxs c seen acc t
    let (seen, acc) := refIdxs c seen acc v
    refIdxs c seen acc b
  | .share n =>
    if seen.contains n.toNat then (seen, acc) else
    match c.sharing[n.toNat]? with
    | some e => refIdxs c (seen.insert n.toNat) acc e
    | none => (seen, acc)
  | _ => (seen, acc)

/-- The constants a record needs installed for what reads it: a theorem's type's
(nothing reduces its value), every other record's whole refs table. -/
def neededRefs (c : Ixon.Constant) : Array Address :=
  let typeOnly (ts : Array Ixon.Expr) : Array Address :=
    let (_, idxs) := ts.foldl (fun (s, a) t => refIdxs c s a t) ({}, {})
    idxs.toArray.filterMap (c.refs[·]?)
  let isThm (d : Ixon.Definition) : Bool := match d.kind with | .thm => true | _ => false
  match c.info with
  | .defn d => if isThm d then typeOnly #[d.typ] else c.refs
  | .muts ms =>
    if ms.all (fun | .defn d => isThm d | _ => false) then
      typeOnly (ms.filterMap fun | .defn d => some d.typ | _ => none)
    else c.refs
  | _ => c.refs

/-- **The dependency closure of a set of records** (named in `namesFile`, one per
line): every record they reference, and transitively what installing those needs
(`neededRefs`). Prints its size against the artifact's, and writes the names of
its constants to `outFile`. -/
def closure (path namesFile outFile : String) : IO UInt32 := do
  let e ← load path
  let wanted : Std.HashSet String := (← IO.FS.lines namesFile).foldl (·.insert ·) {}
  let ownerOf (a : Address) : Address := match e.getConst? a with
    | some c => Ixon.CheckOrder.owner a c
    | none => a
  let mut work : Array Address := #[]
  let mut seeds : Std.HashSet Address := {}
  for (n, entry) in e.named do
    if wanted.contains n.pretty then
      let o := ownerOf entry.addr
      unless seeds.contains o do
        seeds := seeds.insert o
        if let some c := e.getConst? o then
          for r in c.refs do work := work.push (ownerOf r)
  let mut seen : Std.HashSet Address := seeds
  while h : work.size > 0 do
    let a := work[work.size - 1]
    work := work.pop
    if seen.contains a then continue
    seen := seen.insert a
    if let some c := e.getConst? a then
      for r in neededRefs c do
        let o := ownerOf r
        unless seen.contains o do work := work.push o
  let mut names : Array String := #[]
  for (n, entry) in e.named do
    if seen.contains (ownerOf entry.addr) then names := names.push n.pretty
  IO.FS.writeFile outFile (String.intercalate "\n" names.toList ++ "\n")
  let owners := e.consts.fold (fun (s : Std.HashSet Address) a c =>
    match c.get? with
    | some k => s.insert (Ixon.CheckOrder.owner a k)
    | none => s) {}
  IO.println s!"BDCLOS {path}: seeds={seeds.size} closure_records={seen.size} records={owners.size} \
    closure_names={names.size} names={e.named.size}"
  return 0

/-- The records whose members `namesFile` names (one a line), and their sections'
binder nodes (every node but a share's), against the artifact's records and nodes. -/
def residual (path namesFile : String) : IO UInt32 := do
  let e ← load path
  let wanted : Std.HashSet String := (← IO.FS.lines namesFile).foldl (·.insert ·) {}
  let ownerOf (a : Address) : Address := match e.getConst? a with
    | some c => Ixon.CheckOrder.owner a c
    | none => a
  let binders (c : Ixon.Constant) : Nat :=
    c.binders.foldl (fun acc b => acc + (b.nodes.filter fun
      | .share _ => false
      | _ => true).size) 0
  let mut owners : Std.HashSet Address := {}
  for (n, entry) in e.named do
    if wanted.contains n.pretty then owners := owners.insert (ownerOf entry.addr)
  let mut resBinders := 0
  for o in owners do
    if let some c := e.getConst? o then resBinders := resBinders + binders c
  let mut allRecords := 0
  let mut allBinders := 0
  for (a, lc) in e.consts do
    if let some c := lc.get? then
      if Ixon.CheckOrder.owner a c == a then
        allRecords := allRecords + 1
        allBinders := allBinders + binders c
  IO.println s!"BDRES {path}: residual_records={owners.size} residual_binder_nodes={resBinders} \
    records={allRecords} binder_nodes={allBinders}"
  return 0

end Benchmarks.BinderDataStats

def main (args : List String) : IO UInt32 := do
  match args with
  | ["stats", path] => Benchmarks.BinderDataStats.stats path
  | ["undecided", path] => Benchmarks.BinderDataStats.undecided path
  | ["closure", path, names, out] => Benchmarks.BinderDataStats.closure path names out
  | ["residual", path, names] => Benchmarks.BinderDataStats.residual path names
  | ["compare", a, b] => Benchmarks.BinderDataStats.compare a b
  | ["diag", a, b] => Benchmarks.BinderDataStats.diag a b
  | ["addrs", a, b] => Benchmarks.BinderDataStats.addrs a b
  | ["binding", a] => do
    let e ← Benchmarks.BinderDataStats.load a
    IO.println s!"BDBIND {a}: records={e.consts.size} binding={(e.roleBinding.map (toString ·.address)).getD "none"}"
    return 0
  | _ =>
    IO.eprintln "usage: binder-data-stats stats A.ixe | undecided A.ixe | closure A.ixe NAMES OUT | residual A.ixe NAMES | compare A.ixe B.ixe | diag A.ixe B.ixe | \
addrs A.ixe B.ixe | binding A.ixe"
    return 2
