module

public import Ix.IxVM.PwHints
public import Ix.RoleBinding.Publication

public section

/-!
# The compiler's binder data (the Ixon v5 section)

Every record carries the binder data of its `lam` and `all` nodes
(`Ixon.Constant.binders`): the zero-ness of each binder's codomain sort, as
IxC's annotation pass writes it (`BinderMeta.pw`). The record's address hashes
them with the rest of its bytes. `apply` computes them for a compiled
environment and re-addresses it:

1. **Annotate** every record of the environment, under its own role table and
   the prelude read from its own records (the compiled records are not the
   committed prelude's: the committed prelude is a compile of these records with
   their data). The annotator is IxC's pass over the Ixon tree
   (`IxVM.PwHints.annotateKernel`), in tainting mode: where IxC's datum function
   cannot run and the record's declared type does not give the datum, the node
   is `undecided` (wire tag 4), and so is every binder above it. A datum is
   never guessed.
2. **Write the sections** in the canonical form (`Ixon.Constant.bindersCanonical`):
   the numbered nodes are the `lam` and `all` nodes and the `share` nodes whose
   entry has a binder, in pre-order; one block per root with a numbered node
   (variant 0), one per sharing entry and variant a numbered share names; a
   sharing entry's variants are its distinct node lists in order of first
   occurrence; blocks sorted by `(shared, index, variant)`.
3. **Re-address bottom-up**: a record's data depend on the types of what it
   references, not on their addresses, so the data are computed once, at the old
   addresses. In an order with every record after the records its refs table
   (and a projection's block) names, each record's refs are replaced by their
   new addresses, its section is set, and it is hashed.
4. **Rewrite** everything keyed by a record address: the names (`named`,
   `original`, `addrToName`), the reducibility hints, the role binding (its
   bound roles and proof evidence; its address is the hash of its new bytes),
   `main` and the assumptions.
-/

namespace Ix.Compile.BinderData

open IxVM.PwHints

/-! ## Sections -/

/-- The annotator's numbering of `e`'s numbered nodes (every `lam`, `all` and
`share` in pre-order, a `share` not entered), appended to `out`: `none` at a
binder, `some n` at a share of entry `n`. -/
def kinds (out : Array (Option Nat)) : Ixon.Expr → Array (Option Nat)
  | .lam _ t b => kinds (kinds (out.push none) t) b
  | .all _ _ t b => kinds (kinds (out.push none) t) b
  | .app f a => kinds (kinds out f) a
  | .letE _ t v b => kinds (kinds (kinds out t) v) b
  | .prj _ _ v => kinds out v
  | .share n => out.push (some n.toNat)
  | _ => out

/-- The parameters of an `ifAllZero` datum, ascending and without repeats. -/
def canonicalParams (ps : Array Nat) : Array UInt64 :=
  let sorted := ps.qsort (· < ·)
  (sorted.foldl (fun out p => if out.back? == some p then out else out.push p) #[]).map
    (·.toUInt64)

/-- A node in the section's spelling: "always zero" is `.zero`. -/
def nodeOf : Node → Ixon.BinderNode
  | .binder none => .never
  | .binder (some ps) =>
    let params := canonicalParams ps
    if params.isEmpty then .zero else .ifAllZero params
  | .share v => .share v.toUInt64
  | .undecided => .undecided

/-- The section of record `c` from the annotator's blocks: the share nodes of
entries without a binder dropped, the blocks of those entries and the roots
without a numbered node left out, the rest sorted. -/
def sectionOf (c : Ixon.Constant) (blocks : Array Block) : Except String (Array Ixon.BinderBlock) := do
  let full := binderful c.sharing
  let rs := roots c
  let mut out : Array Ixon.BinderBlock := #[]
  for b in blocks do
    let shared := b.ekind == 1
    if shared && !(full[b.eidx]?.getD false) then continue
    let some tree := (if shared then c.sharing[b.eidx]? else rs[b.eidx]?)
      | throw s!"binder data: no expression ({b.ekind}, {b.eidx})"
    let ks := kinds #[] tree
    unless ks.size == b.nodes.size do
      throw s!"binder data: expression ({b.ekind}, {b.eidx}) has {ks.size} numbered nodes, \
        the annotator {b.nodes.size}"
    let mut nodes : Array Ixon.BinderNode := #[]
    for (node, k) in b.nodes.zip ks do
      match k, node with
      | none, .share _ => throw s!"binder data: a share datum at a binder of ({b.ekind}, {b.eidx})"
      | some _, .binder _ | some _, .undecided =>
        throw s!"binder data: a binder datum at a share of ({b.ekind}, {b.eidx})"
      | none, _ => nodes := nodes.push (nodeOf node)
      | some n, _ => if full[n]?.getD false then nodes := nodes.push (nodeOf node)
    if nodes.isEmpty then continue
    out := out.push { shared, index := b.eidx.toUInt64, variant := b.variant.toUInt64, nodes }
  return out.qsort (fun x y => x.keyLt y)

/-- An undecided binder: the record (its address before re-addressing), the
block and the node's position in the block. -/
structure Undecided where
  address : Address
  shared : Bool
  index : Nat
  variant : Nat
  node : Nat
  deriving Inhabited

/-- The undecided binders of a section. -/
def undecidedOf (a : Address) (blocks : Array Ixon.BinderBlock) : Array Undecided := Id.run do
  let mut out := #[]
  for b in blocks do
    for (node, i) in b.nodes.zipIdx do
      if node == .undecided then
        out := out.push ⟨a, b.shared, b.index.toNat, b.variant.toNat, i⟩
  return out

/-! ## Annotation -/

/-- The records of `env`, decoded, sorted by address. -/
def recordsOf (env : Ixon.Env) : Except String (Array (Address × Ixon.Constant)) := do
  let mut out := #[]
  for (a, lc) in env.consts do
    match lc.get with
    | .ok c => out := out.push (a, c)
    | .error e => throw s!"binder data: record {a} does not decode: {e}"
  return out.qsort (fun x y => x.1.cmpBytes y.1 == .lt)

/-- The role table of `env`'s binding and the prelude read from `env`'s own
records under it. -/
def preludeOf (env : Ixon.Env) (store : Std.HashMap Address Ixon.Constant) :
    Except String (Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon) := do
  let some binding := env.roleBinding | throw "binder data: the environment has no role binding"
  let some table := Ix.Kernel.RoleTable.ofBytes binding.bytes
    | throw "binder data: the role binding does not decode"
  let preRecords ← Ix.RoleBinding.preludeRecords table (store[·]?) Ix.Kernel.preludeShape
  let blobs := (env.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList
  let pre ← Ix.Kernel.Reader.readPrelude (md := .anon) table preRecords #[] blobs
  Ix.Kernel.Reader.checkPreludeShape pre
  return (table, pre)

/-- What annotating an environment found. -/
structure Report where
  /-- the annotator's counts -/
  stats : Stats := {}
  /-- records with a non-empty section -/
  sections : Nat := 0
  blocks : Nat := 0
  nodes : Nat := 0
  /-- the undecided binders, by the records' addresses after re-addressing -/
  undecided : Array Undecided := #[]
  /-- the records the kernel refused, why, by their addresses after re-addressing -/
  refused : Array (Address × String) := #[]
  deriving Inhabited

/-- Every record's section (only records with a non-empty one), keyed by the
record's address in `env`, and the report (addresses still `env`'s). -/
def annotate (env : Ixon.Env) (records : Array (Address × Ixon.Constant)) :
    Except String (Std.HashMap Address (Array Ixon.BinderBlock) × Report) := do
  let store : Std.HashMap Address Ixon.Constant := records.foldl (fun m (a, c) => m.insert a c) {}
  let prelude ← preludeOf env store
  let view : View := {
    records, blobs := env.blobs, hints := env.anonHints,
    table := env.roleBinding.map (·.bytes) }
  let k ← KernelEnv.ofView view (prelude? := some prelude)
  let (tables, stats) := annotateKernel k (taint := true)
  let mut sections : Std.HashMap Address (Array Ixon.BinderBlock) := {}
  let mut report : Report := { stats, refused := k.failures }
  for (a, blocks) in tables do
    let some c := store[a]? | continue
    let sec ← sectionOf c blocks
    if sec.isEmpty then continue
    sections := sections.insert a sec
    report := { report with
      sections := report.sections + 1, blocks := report.blocks + sec.size
      nodes := sec.foldl (fun n b => n + b.nodes.size) report.nodes
      undecided := report.undecided ++ undecidedOf a sec }
  return (sections, report)

/-! ## Re-addressing -/

/-- The records a record names by address: its refs table, and a projection's
block. -/
def targets (c : Ixon.Constant) : Array Address :=
  match c.info with
  | .iPrj p => c.refs.push p.block
  | .cPrj p => c.refs.push p.block
  | .rPrj p => c.refs.push p.block
  | .dPrj p => c.refs.push p.block
  | _ => c.refs

/-- The records in an order with every record after the records it names
(an iterative depth-first postorder from the records in address order). A
cycle is an error: a record names another only by its address, the hash of
bytes holding the other's address. -/
def bottomUp (store : Std.HashMap Address Ixon.Constant) (records : Array (Address × Ixon.Constant)) :
    Except String (Array Address) := do
  let mut done : Std.HashSet Address := Std.HashSet.emptyWithCapacity records.size
  let mut active : Std.HashSet Address := {}
  let mut out : Array Address := Array.mkEmpty records.size
  for (root, _) in records do
    if done.contains root then continue
    let mut stack : Array (Address × Bool) := #[(root, false)]
    while !stack.isEmpty do
      let (node, expanded) := stack.back!
      stack := stack.pop
      if expanded then
        active := active.erase node
        unless done.contains node do
          done := done.insert node
          out := out.push node
      else if done.contains node then
        pure ()
      else if active.contains node then
        throw s!"binder data: records name each other in a cycle through {node}"
      else
        active := active.insert node
        stack := stack.push (node, true)
        for dep in (store[node]?.map targets).getD #[] do
          if dep != node && store.contains dep && !done.contains dep then
            if active.contains dep then
              throw s!"binder data: records name each other in a cycle through {dep}"
            stack := stack.push (dep, false)
  return out

/-- A record with its references renamed by `rename` and its section set. -/
def rewriteRecord (rename : Address → Address) (c : Ixon.Constant)
    (binders : Array Ixon.BinderBlock) : Ixon.Constant :=
  let info : Ixon.ConstantInfo := match c.info with
    | .iPrj p => .iPrj { p with block := rename p.block }
    | .cPrj p => .cPrj { p with block := rename p.block }
    | .rPrj p => .rPrj { p with block := rename p.block }
    | .dPrj p => .dPrj { p with block := rename p.block }
    | i => i
  { c with info, refs := c.refs.map rename, binders }

/-- The role table with its record addresses renamed. -/
def renameTable (rename : Address → Address) (t : Ix.Kernel.RoleTable) : Ix.Kernel.RoleTable :=
  { t with
    bound := t.bound.map fun (r, a) => (r, rename a)
    evidence := t.evidence.map fun (r, es) => (r, es.map fun
      | .proof a => .proof (rename a)
      | .defeq => .defeq) }

/-- **`env` with every record's section, re-addressed**, and what was found
(addresses in the report are the new ones). -/
def apply (env : Ixon.Env) : Except String (Ixon.Env × Report) := do
  unless env.comms.isEmpty do throw "binder data: commitments are not re-addressed"
  unless env.modelRecords.isEmpty && env.models.isEmpty do
    throw "binder data: the environment carries model records"
  let records ← recordsOf env
  let (sections, report) ← annotate env records
  let store : Std.HashMap Address Ixon.Constant := records.foldl (fun m (a, c) => m.insert a c) {}
  let order ← bottomUp store records
  let mut renamed : Std.HashMap Address Address := Std.HashMap.emptyWithCapacity records.size
  let mut consts : Std.HashMap Address Ixon.LazyConstant := Std.HashMap.emptyWithCapacity records.size
  for a in order do
    let some c := store[a]? | continue
    let rename (x : Address) : Address := renamed.getD x x
    let c' := rewriteRecord rename c (sections.getD a #[])
    let bytes := Ixon.serConstant c'
    let a' := Address.blake3 bytes
    if consts.contains a' then
      throw s!"binder data: two records re-address to {a'}"
    consts := consts.insert a' { buf := bytes, len := bytes.size, cache := some c' }
    renamed := renamed.insert a a'
  let rename (x : Address) : Address := renamed.getD x x
  let named := env.named.fold (init := ({} : Std.HashMap Ix.Name Ixon.Named)) fun m n entry =>
    m.insert n { entry with
      addr := rename entry.addr
      original := entry.original.map fun (a, cm) => (rename a, cm) }
  let addrToName := env.addrToName.fold (init := ({} : Std.HashMap Address Ix.Name)) fun m a n =>
    m.insert (rename a) n
  let anonHints := env.anonHints.fold
    (init := ({} : Std.HashMap Address Lean.ReducibilityHints)) fun m a h => m.insert (rename a) h
  let roleBinding ← match env.roleBinding with
    | none => pure none
    | some b => do
      let some t := Ix.Kernel.RoleTable.ofBytes b.bytes
        | throw "binder data: the role binding does not decode"
      let bytes := (renameTable rename t).toBytes
      pure (some { address := Address.blake3 bytes, bytes })
  let env' := { env with
    consts, named, addrToName, anonHints, roleBinding
    main := env.main.map rename
    assumptions := env.assumptions.fold (init := ({} : Std.HashSet Address)) fun s a =>
      s.insert (rename a) }
  let report := { report with
    undecided := report.undecided.map fun u => { u with address := rename u.address }
    refused := report.refused.map fun (a, why) => (rename a, why) }
  return (env', report)

/-- The report's summary line. -/
def Report.summary (r : Report) : String :=
  s!"{r.sections} records with binder data, {r.blocks} blocks, {r.nodes} nodes, \
    {r.undecided.size} undecided; kernel installed {r.stats.installed}, refused {r.refused.size}, \
    data inherited from declared types {r.stats.inherited}"

/-- One line per undecided binder, named by `nameOf`. -/
def Report.undecidedLines (r : Report) (nameOf : Address → String) : Array String :=
  r.undecided.map fun u =>
    s!"undecided binder: {nameOf u.address} ({u.address}), \
      {if u.shared then "sharing entry" else "root"} {u.index} variant {u.variant}, node {u.node}"

/-- A record's names in `env` (a block's: those of the projections into it), for
reports. -/
def namesOf (env : Ixon.Env) (wanted : Std.HashSet Address) : Std.HashMap Address String := Id.run do
  let mut out : Std.HashMap Address String := {}
  for (n, entry) in env.named do
    let owner := match env.getConst? entry.addr with
      | some c => Ixon.CheckOrder.owner entry.addr c
      | none => entry.addr
    if wanted.contains owner && !out.contains owner then out := out.insert owner n.pretty
  return out

/-- Print the summary, and each undecided binder by name (at most `limit`, to
stderr) and each record the kernel refused (at most `limit`). -/
def Report.print (r : Report) (env : Ixon.Env) (tag : String) (limit : Nat := 50) : IO Unit := do
  IO.println s!"[{tag}] binder data: {r.summary}"
  if r.undecided.isEmpty && r.refused.isEmpty then return
  let wanted : Std.HashSet Address :=
    (r.undecided.map (·.address) ++ r.refused.map (·.1)).foldl (·.insert ·) {}
  let names := namesOf env wanted
  let nameOf (a : Address) : String := names.getD a "?"
  let lines := r.undecidedLines nameOf
  for l in lines.extract 0 limit do IO.eprintln s!"[{tag}] {l}"
  if lines.size > limit then IO.eprintln s!"[{tag}] … and {lines.size - limit} more undecided"
  for (a, why) in r.refused.extract 0 limit do
    IO.eprintln s!"[{tag}] binder data: the kernel refused {nameOf a} ({a}): {why}"

end Ix.Compile.BinderData

end
