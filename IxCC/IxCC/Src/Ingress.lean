import IxCC.Src.Syntax
import IxCC.Src.Pinned
import IxCC.Src.Hints
import IxCC.Ixon.V3.Keys
import IxCC.Ixon.V3.Support
import Std.Data.HashMap
import Std.Data.HashSet

/-! # Src ingress

Reads the records of a decoded Ixon v5 closure that its seeds reach into the
table-free `Src.Program` (the front end accepts the whole closure by the
certified kernel separately, `Recheck.ingress`; this reading itself runs no
typing). It reads only what the seeds reach (`reach`): an artifact `ix
compile` writes holds a structure's or inductive's whole logical unit and every
lemma its proofs use, and IxCC's limits on what it reads must not refuse a
record nothing reaches. The seeds are wider than the roots a compile chooses
(below): a record over IxCC's limits that another sidecar root reaches, or that
a proposed equation's proof uses, refuses every compile of the artifact with
that sidecar.

**What is read.** From the seeds (`Seeds.of`: every root the sidecar names, not
only the roots a compile chooses; the constants the role table binds to the
identities IxCC pins; and, read with their proofs, the equation theorem of
every sidecar proposal whose subject is reached), across every reference of
what is read, a projection record reaching its block. An address that is not a
record the artifact stores is not read: a block member named by its projection
address is read only if the artifact stores that projection record (`ix
compile` writes one for every member and constructor) or something else
reaches the block. A record is read *with proofs* when a proof seed reaches it
(the table checks walk their proofs, `Table.checkAxiomClosure`), and otherwise
*by statement*: whole, except that a theorem's proof is not read and its
references are not followed. A theorem so read keeps its type and is recorded
in `Program.byStatement`, its value `Term.unreadProof`. Not followed: the
recursors of a reached inductive (a reached recursor is reached by reference),
and the proof of a theorem read by statement. The result is the least fixpoint
of these rules, a function of the records, the sidecar and the role table,
whatever order the walk takes; IxCC's consumer budget (`V3.Constant.withinBudget`)
applies to what is read of each record, and a reached record over it is refused.

**How it is read (Ixon v5).** Every reached record must carry a complete
binder-data section (`V3.Constant.bindersComplete`) and canonical modes
(`V3.Constant.modesCanonical`). `lam` and `all` binder modes and stored
zero-ness data are read from the record's binder-data section by `V3.BinderPos`
(`(shared, index, variant, ordinal)`). Share nodes expand through a per-constant
cache keyed by `(index, variant)`, walking through `.share` everywhere
(including leading telescopes). `ref` resolves through the constant's `refs`
table and the program's address map, `recur` through the block's members, `nat`
blobs must be canonical little-endian (`V3.decodeNatBlob`), `str` blobs must be
valid UTF-8, and universe indices resolve through `univs`. Stored zero-ness
data are cross-checked fail-closed against computed `PropWhen` values via
`checkStoredDatum` / `checkTermBinderData` (N2).

Every member of a mutual block gets a `CRef.member`, every constructor a
`CRef.ctor`; each is addressed by its projection constant's address (the
block-member keys, `V3.defnProjAddr` and its siblings), so projection
constants are aliases. A standalone constant is a singleton block. Constants
are numbered in address order over the records read, a block member by member,
then constructor by constructor. Each `Item` keeps its exact starting root
index in `V3.ConstantInfo.binderRoots`. -/

namespace IxCC.Src.Ingress

open IxCC.Ixon

/-- One declaration to convert, with the index of the stored constant whose
tables it uses and its starting root index in `V3.ConstantInfo.binderRoots`. -/
inductive Item where
  | defn (d : V3.Definition) (src : Nat) (rootIdx : UInt64)
  | recr (r : V3.Recursor) (src : Nat) (rootIdx : UInt64)
  | indc (ind : V3.Inductive) (src : Nat) (rootIdx : UInt64) (ctors : Array CId)
  | ctor (c : V3.Constructor) (src : Nat) (rootIdx : UInt64) (ind : CId)
  | quot (q : V3.Quotient) (src : Nat) (rootIdx : UInt64)
  | axio (a : V3.Axiom) (src : Nat) (rootIdx : UInt64)
  deriving Inhabited

def Item.src : Item → Nat
  | .defn _ s _ | .recr _ s _ | .indc _ s _ _ | .ctor _ s _ _ | .quot _ s _ | .axio _ s _ => s

def Item.rootIdx : Item → UInt64
  | .defn _ _ r | .recr _ _ r | .indc _ _ r _ | .ctor _ _ r _ | .quot _ _ r | .axio _ _ r => r

/-- A stored constant with the member `CId`s that resolve its `recur`s,
whether its theorems' proofs are read, and which sharing entries contain a
binder directly or transitively. -/
structure Source where
  constant : V3.Constant
  members : Array CId
  proofs : Bool := true
  binderful : Array Bool := #[]
  deriving Inhabited

structure Layout where
  refs : Array CRef := #[]
  addrs : Array Ixon.Address := #[]
  items : Array Item := #[]
  sources : Array Source := #[]
  byAddr : Std.HashMap Ixon.Address CId := {}
  deriving Inhabited

namespace Layout

def push (l : Layout) (ref : CRef) (addr : Ixon.Address) (item : Item) : Layout × CId :=
  let id := l.refs.size
  ({ l with refs := l.refs.push ref, addrs := l.addrs.push addr, items := l.items.push item
            byAddr := l.byAddr.insert addr id }, id)

/-- Lay out one stored constant. Projections are aliases and add nothing.
Root indices follow `V3.ConstantInfo.binderRoots` exactly (in a mutual block,
each inductive's constructors immediately follow that inductive's type). -/
def add (l : Layout) (address : Ixon.Address) (c : V3.Constant) (proofs : Bool := true) :
    Layout := Id.run do
  let src := l.sources.size
  let binderful := c.binderfulEntries
  match c.info with
  | .muts members =>
    -- Members first (their ids resolve `recur`), constructors after.
    let base := l.refs.size
    let mut l := l
    let memberIds : Array CId := (Array.range members.size).map (base + ·)
    -- Constructor ids follow the members, in member order.
    let mut next := base + members.size
    let mut ctorIds : Array (Array CId) := #[]
    for h : i in [0:members.size] do
      match members[i] with
      | .indc ind =>
        ctorIds := ctorIds.push ((Array.range ind.ctors.size).map (next + ·))
        next := next + ind.ctors.size
      | _ => ctorIds := ctorIds.push #[]
    -- Track `ConstantInfo.binderRoots` offsets while pushing members.
    let mut rootIdx : UInt64 := 0
    let mut ctorRootStarts : Array UInt64 := #[]
    for h : i in [0:members.size] do
      let idx := i.toUInt64
      match members[i] with
      | .defn d =>
        l := (l.push (.member address i) (V3.defnProjAddr address idx) (.defn d src rootIdx)).1
        ctorRootStarts := ctorRootStarts.push 0
        rootIdx := rootIdx + 2
      | .recr r =>
        l := (l.push (.member address i) (V3.recrProjAddr address idx) (.recr r src rootIdx)).1
        ctorRootStarts := ctorRootStarts.push 0
        rootIdx := rootIdx + 1 + r.rules.size.toUInt64
      | .indc ind =>
        l := (l.push (.member address i) (V3.indcProjAddr address idx)
          (.indc ind src rootIdx (ctorIds[i]?.getD #[]))).1
        ctorRootStarts := ctorRootStarts.push (rootIdx + 1)
        rootIdx := rootIdx + 1 + ind.ctors.size.toUInt64
    for h : i in [0:members.size] do
      match members[i] with
      | .indc ind =>
        let cBase := ctorRootStarts[i]?.getD 0
        for h : j in [0:ind.ctors.size] do
          l := (l.push (.ctor address i j) (V3.ctorProjAddr address i.toUInt64 j.toUInt64)
            (.ctor ind.ctors[j] src (cBase + j.toUInt64) (base + i))).1
      | _ => pure ()
    let s : Source := { constant := c, members := memberIds, proofs, binderful }
    return { l with sources := l.sources.push s }
  | .defn d =>
    let (l, id) := l.push (.member address 0) address (.defn d src 0)
    let s : Source := { constant := c, members := #[id], proofs, binderful }
    return { l with sources := l.sources.push s }
  | .recr r =>
    let (l, id) := l.push (.member address 0) address (.recr r src 0)
    let s : Source := { constant := c, members := #[id], proofs, binderful }
    return { l with sources := l.sources.push s }
  | .axio a =>
    let (l, _) := l.push (.member address 0) address (.axio a src 0)
    let s : Source := { constant := c, members := #[], proofs, binderful }
    return { l with sources := l.sources.push s }
  | .quot q =>
    let (l, _) := l.push (.member address 0) address (.quot q src 0)
    let s : Source := { constant := c, members := #[], proofs, binderful }
    return { l with sources := l.sources.push s }
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => l

end Layout

/-! ## Binder-data helpers and N2 stored-datum cross-check -/

/-- Extract the stored zero-ness datum from a v5 binder node: `some pw` for a
decided binder node, `none` for `.undecided` or `.share`. -/
def binderNodeDatum : V3.BinderNode → Option PropWhen
  | .never _ => some .never
  | .zero _ => some .always
  | .ifAllZero params _ => some (.allZero (params.toList.map UInt64.toNat))
  | .undecided _ => none
  | .share _ => none

/-- Sorted, deduplicated universe parameter indices for semantic comparison of
`PropWhen` conditions. -/
def canonicalParams (ps : List Nat) : List Nat :=
  (ps.toArray.qsort (· < ·)).toList.eraseDups

/-- Whether two `PropWhen` conditions agree on every universe profile. -/
def samePropWhen : PropWhen → PropWhen → Bool
  | .never, .never => true
  | .allZero ps, .allZero qs => canonicalParams ps == canonicalParams qs
  | _, _ => false

/-- N2 fail-closed cross-check between a record's stored binder datum (`none`
for `.undecided`) and the annotator's computed `PropWhen`. Advisory when
undecided; fails closed on any disagreement. -/
def checkStoredDatum (pos : V3.BinderPos) (stored : Option PropWhen)
    (computed : PropWhen) : Except String Unit :=
  match stored with
  | none => .ok ()
  | some d =>
    if samePropWhen d computed then .ok ()
    else throw s!"src ingress: stored binder datum {repr d} disagrees with computed \
      {repr computed} at ({pos.shared}, {pos.index}, {pos.variant}, {pos.ordinal})"

/-- Strict N2 check that also refuses an `.undecided` stored datum. -/
def checkStoredDatumStrict (pos : V3.BinderPos) (stored : Option PropWhen)
    (computed : PropWhen) : Except String Unit :=
  match stored with
  | none =>
    throw s!"src ingress: undecided binder datum at \
      ({pos.shared}, {pos.index}, {pos.variant}, {pos.ordinal})"
  | some _ => checkStoredDatum pos stored computed

/-- Cross-check the stored datum at a single `BinderPos` of `c` against
`computed`, failing closed on missing node, share node, or disagreement. -/
def checkBinderDatumAt (c : V3.Constant) (pos : V3.BinderPos)
    (computed : PropWhen) (allowUndecided : Bool := true) : Except String Unit := do
  let some node := c.binderNodeAt? pos
    | throw s!"src ingress: missing binder node at \
        ({pos.shared}, {pos.index}, {pos.variant}, {pos.ordinal})"
  if node matches .share _ then
    throw s!"src ingress: share node at binder position \
      ({pos.shared}, {pos.index}, {pos.variant}, {pos.ordinal})"
  let datum := binderNodeDatum node
  if allowUndecided then checkStoredDatum pos datum computed
  else checkStoredDatumStrict pos datum computed

/-- Number of numbered nodes in `e` (`lam`, `all`, and binderful `share`
nodes, without entering shared entries), matching `Ixon.Expr.numberedNodes`. -/
def numberedNodeCount (full : Array Bool) : V3.Expr → Nat
  | .lam t b | .all t b => 1 + numberedNodeCount full t + numberedNodeCount full b
  | .app f a => numberedNodeCount full f + numberedNodeCount full a
  | .letE _ _ t v b =>
      numberedNodeCount full t + numberedNodeCount full v + numberedNodeCount full b
  | .prj _ _ v => numberedNodeCount full v
  | .share n => if full[n.toNat]?.getD false then 1 else 0
  | _ => 0

/-! ## Expression conversion -/

/-- Active binder-data block being walked while converting one expression or
sharing variant. -/
structure BlockCtx where
  shared : Bool
  index : UInt64
  variant : UInt64
  nodes : Array V3.BinderNode
  deriving Inhabited

structure Ctx where
  env : V3.Env
  source : Source
  byAddr : Std.HashMap Ixon.Address CId

/-- Per-constant share cache keyed by `(sharingIndex, variant)`. -/
abbrev ShareCache := Std.HashMap (UInt64 × UInt64) (Term × Nat)

abbrev ConvM := StateT ShareCache (Except String)

def univ (ctx : Ctx) (i : UInt64) : ConvM Univ :=
  match ctx.source.constant.univs[i.toNat]? with
  | some u => pure u
  | none => throw s!"src ingress: universe index {i} out of range"

def refAddr (ctx : Ctx) (i : UInt64) : ConvM Ixon.Address :=
  match ctx.source.constant.refs[i.toNat]? with
  | some a => pure a
  | none => throw s!"src ingress: reference index {i} out of range"

def resolveRef (ctx : Ctx) (i : UInt64) : ConvM CId := do
  let a ← refAddr ctx i
  match ctx.byAddr[a]? with
  | some c => pure c
  | none => throw s!"src ingress: unresolved reference {a}"

def blob (ctx : Ctx) (i : UInt64) : ConvM ByteArray := do
  let a ← refAddr ctx i
  match ctx.env.blobs[a]? with
  | some bytes => pure bytes
  | none => throw s!"src ingress: missing blob {a}"

private def blockNode (blk : BlockCtx) (ord : Nat) : Except String V3.BinderNode :=
  match blk.nodes[ord]? with
  | some n => .ok n
  | none =>
    throw s!"src ingress: missing binder node at \
      ({blk.shared}, {blk.index}, {blk.variant}, {ord})"

/-- Convert one expression inside binder-data block `blk` starting at ordinal
`ord`, returning the converted term, its height, and the next unread ordinal in
`blk`. `fuel` bounds nesting depth (share expansions included). Binderful
`.share` nodes consume their `.share variant` node at `BinderPos` and index the
share cache by `(index, variant)`; binder-free `.share` nodes consume no node
and cache at `(index, 0)`. -/
def convH (ctx : Ctx) (blk : BlockCtx) : Nat → Nat → V3.Expr → ConvM (Term × Nat × Nat)
  | 0, _, _ => throw "src ingress: expression depth budget exhausted"
  | fuel + 1, ord, e => match e with
    | .sort i => return (.sort (← univ ctx i), 1, ord)
    | .var i => return (.var i.toNat, 1, ord)
    | .ref i us => return (.const (← resolveRef ctx i) (← us.toList.mapM (univ ctx)), 1, ord)
    | .recur i us => do
      let some c := ctx.source.members[i.toNat]?
        | throw s!"src ingress: recursive member index {i} out of range"
      return (.const c (← us.toList.mapM (univ ctx)), 1, ord)
    | .prj i field v => do
      let s ← resolveRef ctx i
      let (t, h, ord1) ← convH ctx blk fuel ord v
      return (.proj s field.toNat t, h + 1, ord1)
    | .str i => do
      let bytes ← blob ctx i
      match String.fromUTF8? bytes with
      | some s => return (.strLit s, 1, ord)
      | none => throw "src ingress: string blob is not valid UTF-8"
    | .nat i => do
      let bytes ← blob ctx i
      match V3.decodeNatBlob bytes with
      | .ok n => return (.natLit n, 1, ord)
      | .error msg => throw s!"src ingress: {msg}"
    | .app f a => do
      let (f, hf, ord1) ← convH ctx blk fuel ord f
      let (a, ha, ord2) ← convH ctx blk fuel ord1 a
      return (.app f a .strict .rel, max hf ha + 1, ord2)
    | .lam d b => do
      let node ← blockNode blk ord
      let some mode := node.mode?
        | throw s!"src ingress: share node at lam binder position \
            ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
      let pw := (binderNodeDatum node).getD .never
      let (d, hd, ord1) ← convH ctx blk fuel (ord + 1) d
      let (b, hb, ord2) ← convH ctx blk fuel ord1 b
      return (.lam { mode, propWhen := pw } d b, max hd hb + 1, ord2)
    | .all d b => do
      let node ← blockNode blk ord
      let some mode := node.mode?
        | throw s!"src ingress: share node at all binder position \
            ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
      let pw := (binderNodeDatum node).getD .never
      let (d, hd, ord1) ← convH ctx blk fuel (ord + 1) d
      let (b, hb, ord2) ← convH ctx blk fuel ord1 b
      return (.pi { mode, propWhen := pw } d b, max hd hb + 1, ord2)
    | .letE nonDep mode t v b => do
      let (t, ht, ord1) ← convH ctx blk fuel ord t
      let (v, hv, ord2) ← convH ctx blk fuel ord1 v
      let (b, hb, ord3) ← convH ctx blk fuel ord2 b
      return (.letE nonDep mode .rel t v b, max ht (max hv hb) + 1, ord3)
    | .share i => do
      let isBinderful := ctx.source.binderful[i.toNat]?.getD false
      let (variant, nextOrd) ← if isBinderful then do
          let node ← blockNode blk ord
          match node with
          | .share v => pure (v, ord + 1)
          | _ =>
            throw s!"src ingress: expected share node at \
              ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
        else
          pure (0, ord)
      let key : UInt64 × UInt64 := (i, variant)
      if let some (t, h) := (← get)[key]? then
        if h > fuel then throw "src ingress: expression depth budget exhausted"
        return (t, h, nextOrd)
      let some expansion := ctx.source.constant.sharing[i.toNat]?
        | throw s!"src ingress: share index {i} out of range"
      let subNodes ← if isBinderful then
          match ctx.source.constant.blockNodes? true i variant with
          | some ns => pure ns
          | none =>
            throw s!"src ingress: missing binder block for share ({i}, {variant})"
        else
          pure #[]
      let subBlk : BlockCtx := { shared := true, index := i, variant, nodes := subNodes }
      let (t, h, subEnd) ← convH ctx subBlk fuel 0 expansion
      unless subEnd == subNodes.size do
        throw s!"src ingress: share block ({i}, {variant}) consumed {subEnd} of {subNodes.size} nodes"
      modify (·.insert key (t, h))
      return (t, h, nextOrd)

/-- Convert one root expression `e` at root index `rootIdx` in `V3.ConstantInfo.binderRoots`,
verifying that every node in the root's binder block is consumed. -/
def convRoot (ctx : Ctx) (rootIdx : UInt64) (fuel : Nat) (e : V3.Expr) : ConvM Term := do
  let nodes := (ctx.source.constant.blockNodes? false rootIdx 0).getD #[]
  let blk : BlockCtx := { shared := false, index := rootIdx, variant := 0, nodes }
  let (t, _, endOrd) ← convH ctx blk fuel 0 e
  unless endOrd == nodes.size do
    throw s!"src ingress: root block {rootIdx} consumed {endOrd} of {nodes.size} nodes"
  return t

/-- Depth budget for one expression, share expansions included
(`Src.maxTermDepth`). A share converted once is reused without its depth being
counted again, so the recheck path checks the program's depth again, as
trees, before its front end (`Recheck.checkSrc`). -/
def depthBudget : Nat := maxTermDepth

/-! ## Leading telescope readers (walking through `.share`) -/

private def leadingBindersLoop (wantLam : Bool) (c : V3.Constant) (full : Array Bool) :
    Nat → BlockCtx → Nat → V3.Expr →
      Array (V3.BinderPos × V3.BinderNode × V3.Expr) →
      Except String (Array (V3.BinderPos × V3.BinderNode × V3.Expr) × V3.Expr)
  | 0, _, _, _, _ => throw "src ingress: leading telescope depth budget exhausted"
  | fuel + 1, blk, ord, e, acc =>
    match e with
    | .share i =>
      if full[i.toNat]?.getD false then do
        let node ← blockNode blk ord
        let .share v := node
          | throw s!"src ingress: expected share node at \
              ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
        let some expansion := c.sharing[i.toNat]?
          | throw s!"src ingress: share index {i} out of range"
        let some subNodes := c.blockNodes? true i v
          | throw s!"src ingress: missing binder block for share ({i}, {v})"
        leadingBindersLoop wantLam c full fuel
          { shared := true, index := i, variant := v, nodes := subNodes } 0 expansion acc
      else
        -- A binder-free sharing entry has no leading binder; expand once to
        -- expose the body expression if present.
        match c.sharing[i.toNat]? with
        | some expansion => leadingBindersLoop wantLam c full fuel
            { shared := true, index := i, variant := 0, nodes := #[] } 0 expansion acc
        | none => throw s!"src ingress: share index {i} out of range"
    | .lam dom body =>
      if wantLam then do
        let node ← blockNode blk ord
        if node matches .share _ then
          throw s!"src ingress: share node at lam binder position \
            ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
        let pos : V3.BinderPos := ⟨blk.shared, blk.index, blk.variant, ord⟩
        let nextOrd := ord + 1 + numberedNodeCount full dom
        leadingBindersLoop wantLam c full fuel blk nextOrd body (acc.push (pos, node, dom))
      else
        .ok (acc, e)
    | .all dom body =>
      if !wantLam then do
        let node ← blockNode blk ord
        if node matches .share _ then
          throw s!"src ingress: share node at all binder position \
            ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
        let pos : V3.BinderPos := ⟨blk.shared, blk.index, blk.variant, ord⟩
        let nextOrd := ord + 1 + numberedNodeCount full dom
        leadingBindersLoop wantLam c full fuel blk nextOrd body (acc.push (pos, node, dom))
      else
        .ok (acc, e)
    | _ => .ok (acc, e)

/-- Read the leading `lam` telescope of root expression `e` (at `rootIdx` in
`c.info.binderRoots`), walking through `.share` nodes and resolving every
binder by `V3.BinderPos`. Returns the sequence of `(pos, node, domain)` and the
non-`lam` body expression. -/
def leadingLamBinders (c : V3.Constant) (rootIdx : UInt64) (e : V3.Expr)
    (fuel : Nat := depthBudget) :
    Except String (Array (V3.BinderPos × V3.BinderNode × V3.Expr) × V3.Expr) := do
  let full := c.binderfulEntries
  let nodes := (c.blockNodes? false rootIdx 0).getD #[]
  leadingBindersLoop true c full fuel
    { shared := false, index := rootIdx, variant := 0, nodes } 0 e #[]

/-- Read the leading `all` telescope of root expression `e` (at `rootIdx` in
`c.info.binderRoots`), walking through `.share` nodes and resolving every
binder by `V3.BinderPos`. Returns the sequence of `(pos, node, domain)` and the
non-`all` codomain expression. -/
def leadingAllBinders (c : V3.Constant) (rootIdx : UInt64) (e : V3.Expr)
    (fuel : Nat := depthBudget) :
    Except String (Array (V3.BinderPos × V3.BinderNode × V3.Expr) × V3.Expr) := do
  let full := c.binderfulEntries
  let nodes := (c.blockNodes? false rootIdx 0).getD #[]
  leadingBindersLoop false c full fuel
    { shared := false, index := rootIdx, variant := 0, nodes } 0 e #[]

/-! ## Whole-term N2 stored-datum cross-check -/

private def checkTermLoop (c : V3.Constant) (full : Array Bool) (skipIrr allowUndecided : Bool) :
    Nat → BlockCtx → Nat → V3.Expr → Term → Except String Nat
  | 0, _, _, _, _ => throw "src ingress: stored-datum check depth budget exhausted"
  | fuel + 1, blk, ord, e, t =>
    match e with
    | .share i =>
      if full[i.toNat]?.getD false then do
        let node ← blockNode blk ord
        let .share v := node
          | throw s!"src ingress: expected share node at \
              ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
        let some expansion := c.sharing[i.toNat]?
          | throw s!"src ingress: share index {i} out of range"
        let some subNodes := c.blockNodes? true i v
          | throw s!"src ingress: missing binder block for share ({i}, {v})"
        let subEnd ← checkTermLoop c full skipIrr allowUndecided fuel
          { shared := true, index := i, variant := v, nodes := subNodes } 0 expansion t
        unless subEnd == subNodes.size do
          throw s!"src ingress: share block ({i}, {v}) consumed {subEnd} of {subNodes.size} nodes"
        return ord + 1
      else
        return ord
    | .lam d b =>
      match t with
      | .lam bd dom body => do
        let pos : V3.BinderPos := ⟨blk.shared, blk.index, blk.variant, ord⟩
        let node ← blockNode blk ord
        if node matches .share _ then
          throw s!"src ingress: share node at lam binder position \
            ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
        let stored := binderNodeDatum node
        if allowUndecided then checkStoredDatum pos stored bd.propWhen
        else checkStoredDatumStrict pos stored bd.propWhen
        let ord1 ← if skipIrr then pure (ord + 1 + numberedNodeCount full d)
          else checkTermLoop c full skipIrr allowUndecided fuel blk (ord + 1) d dom
        checkTermLoop c full skipIrr allowUndecided fuel blk ord1 b body
      | _ => throw "src ingress: stored-datum check term mismatch at lam"
    | .all d b =>
      match t with
      | .pi bd dom cod => do
        let pos : V3.BinderPos := ⟨blk.shared, blk.index, blk.variant, ord⟩
        let node ← blockNode blk ord
        if node matches .share _ then
          throw s!"src ingress: share node at all binder position \
            ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
        if !skipIrr then
          let stored := binderNodeDatum node
          if allowUndecided then checkStoredDatum pos stored bd.propWhen
          else checkStoredDatumStrict pos stored bd.propWhen
        let ord1 ← if skipIrr then pure (ord + 1 + numberedNodeCount full d)
          else checkTermLoop c full skipIrr allowUndecided fuel blk (ord + 1) d dom
        if skipIrr then pure (ord1 + numberedNodeCount full b)
        else checkTermLoop c full skipIrr allowUndecided fuel blk ord1 b cod
      | _ => throw "src ingress: stored-datum check term mismatch at all"
    | .app f a =>
      match t with
      | .app tf ta _ r => do
        let ord1 ← checkTermLoop c full skipIrr allowUndecided fuel blk ord f tf
        if skipIrr && r.alwaysIrr then
          pure (ord1 + numberedNodeCount full a)
        else
          checkTermLoop c full skipIrr allowUndecided fuel blk ord1 a ta
      | _ => throw "src ingress: stored-datum check term mismatch at app"
    | .letE _ _ ty val body =>
      match t with
      | .letE _ _ r tty tv tb => do
        let ord1 ← if skipIrr then pure (ord + numberedNodeCount full ty)
          else checkTermLoop c full skipIrr allowUndecided fuel blk ord ty tty
        let ord2 ← if skipIrr && r.alwaysIrr then pure (ord1 + numberedNodeCount full val)
          else checkTermLoop c full skipIrr allowUndecided fuel blk ord1 val tv
        checkTermLoop c full skipIrr allowUndecided fuel blk ord2 body tb
      | _ => throw "src ingress: stored-datum check term mismatch at letE"
    | .prj _ _ v =>
      match t with
      | .proj _ _ tv => checkTermLoop c full skipIrr allowUndecided fuel blk ord v tv
      | _ => throw "src ingress: stored-datum check term mismatch at prj"
    | _ => pure ord

/-- Cross-check the stored binder zero-ness data in root `rootIdx` (`e`) of
record `c` against an annotated `Src.Term` (`annotated`), failing closed on any
disagreement (N2). When `skipIrr` is `true` (default, matching
`KernelFront.Annotate.walk`), always-irrelevant arguments, lets, types, and
domains are skipped; when `false`, every binder in the term is checked. -/
def checkTermBinderData (c : V3.Constant) (rootIdx : UInt64) (e : V3.Expr)
    (annotated : Term) (skipIrr : Bool := true) (allowUndecided : Bool := true)
    (fuel : Nat := depthBudget) : Except String Unit := do
  let full := c.binderfulEntries
  let nodes := (c.blockNodes? false rootIdx 0).getD #[]
  let endOrd ← checkTermLoop c full skipIrr allowUndecided fuel
    { shared := false, index := rootIdx, variant := 0, nodes } 0 e annotated
  unless endOrd == nodes.size do
    throw s!"src ingress: stored-datum check consumed {endOrd} of {nodes.size} nodes in root {rootIdx}"

/-! ## Recursor majors -/

/-- The major inductive of a recursor: the head of the domain of its
`params + motives + minors + indices`-th Π binder. -/
def majorInductive (isInductive : CId → Bool) (r : V3.Recursor) (type : Term) : Option CId :=
  let (binders, _) := type.pis
  let majorIdx := (r.params + r.motives + r.minors + r.indices).toNat
  match binders[majorIdx]? with
  | some (_, dom) =>
    match dom.spine.1 with
    | .const c _ => if isInductive c then some c else none
    | _ => none
  | none => none

/-! ## The records the seeds reach -/

/-- Where the walk starts. -/
structure Seeds where
  /-- Read by statement: the sidecar's roots, the pinned identities. -/
  statement : Array Ixon.Address := #[]
  /-- Read with proofs: explicit proof seeds. -/
  proofs : Array Ixon.Address := #[]
  /-- The sidecar's proposals that name a theorem, as (subject, theorem): the
  theorem is read with its proof once the subject is reached. -/
  eqns : Array (Ixon.Address × Ixon.Address) := #[]
  deriving Inhabited

/-- The addresses of the identities `pins` pins: `Src.Known`'s, the `Nat`
primitives and the standard axioms (not the D12 allowlist, which matters only
where it is reached). -/
def pinnedAddresses (pins : Pins) : Array Ixon.Address :=
  (([pins.nat, pins.natZero, pins.natSucc, pins.natRec, pins.bool, pins.boolTrue, pins.boolFalse,
      pins.eq, pins.decIsFalse, pins.decIsTrue].filterMap id) ++ pins.prims.map (·.2) ++
    pins.stdAxioms).toArray.map Pinned.addrOfNat

/-- **The seeds of a sidecar** under `pins` (ingress passes the pins of the
kernel's admitted role table): every root the sidecar names (not only the roots
a compile chooses, so that the program's numbering does not depend on the
choice); the pinned identities, so that `Src.Known` and the table's `prim`
entries resolve as they would on the whole artifact; and every proposal's
theorem (and optional `guess` checker and completeness theorem), read with its
proof once the proposal's subject is reached. -/
def Seeds.of (h : Hints) (pins : Pins) : Seeds :=
  { statement := h.roots.map (·.1) ++ pinnedAddresses pins
    proofs := #[]
    eqns := h.proposals.foldl (init := #[]) fun acc p =>
      let acc := match p.theorem? with | some t => acc.push (p.subject, t) | none => acc
      let acc := match p.checker? with | some c => acc.push (p.subject, c) | none => acc
      match p.comp? with | some cp => acc.push (p.subject, cp) | none => acc }

/-- Every record of an environment, read with proofs: the whole artifact, as
ingress read it before it read only what the seeds reach (for tools and
tests that compare the two readings). -/
def Seeds.everything (env : V3.Env) : Seeds :=
  { proofs := env.consts.keys.toArray.qsort (fun a b => a.cmpBytes b == .lt) }

/-- A record ingress reads: its address, its constant, and whether its
theorems' proofs are read. -/
structure Read where
  address : Ixon.Address
  constant : V3.Constant
  proofs : Bool
  deriving Inhabited

/-- Whether a constant holds a theorem, as itself or as a block member. -/
def hasTheorem (c : V3.Constant) : Bool :=
  match c.info with
  | .defn d => d.kind == .thm
  | .muts ms => ms.any fun | .defn d => d.kind == .thm | _ => false
  | _ => false

/-- The expressions ingress reads of a constant: all of them, or, without
proofs, all but its theorems' values. -/
def readExprs (proofs : Bool) (c : V3.Constant) : List V3.Expr :=
  if proofs then c.info.exprs
  else
    let defn := fun (d : V3.Definition) => if d.kind == .thm then [d.typ] else d.exprs
    match c.info with
    | .defn d => defn d
    | .muts ms => ms.toList.flatMap fun | .defn d => defn d | m => m.exprs
    | i => i.exprs

/-- The sharing entries and the reference indices that `es` use, through
`share` nodes transitively: an explicit worklist, each sharing entry expanded
once, so linear in the constant's size whatever its depth. -/
def uses (c : V3.Constant) (es : List V3.Expr) : Array V3.Expr × Array UInt64 := Id.run do
  let mut todo : Array V3.Expr := es.toArray
  let mut seen : Std.HashSet UInt64 := {}
  let mut shared : Array V3.Expr := #[]
  let mut refs : Array UInt64 := #[]
  while !todo.isEmpty do
    let some e := todo.back? | break
    todo := todo.pop
    match e with
    | .ref i _ | .str i | .nat i => refs := refs.push i
    | .prj i _ b =>
      refs := refs.push i
      todo := todo.push b
    | .app f a => todo := (todo.push f).push a
    | .lam t b | .all t b => todo := (todo.push t).push b
    | .letE _ _ t v b => todo := ((todo.push t).push v).push b
    | .share i =>
      unless seen.contains i do
        seen := seen.insert i
        if let some e' := c.sharing[i.toNat]? then
          shared := shared.push e'
          todo := todo.push e'
    | _ => pure ()
  return (shared, refs)

/-- IxCC's consumer budget on what it reads of a constant: with proofs, or for
a constant holding no theorem, the whole constant (`V3.Constant.withinBudget`);
otherwise its payload's counts and every expression read, with the sharing
entries they use (a theorem's unread proof may be of any size). -/
def withinReadBudget (proofs : Bool) (c : V3.Constant) : Bool :=
  if proofs || !hasTheorem c then c.withinBudget
  else
    let es := readExprs false c
    c.info.withinCounts && (es ++ (uses c es).1.toList).all V3.Expr.withinBudget

/-- Decode a reached record: the kernel's canonical decoder, complete
binder-data section and canonical mode checks (`bindersComplete`,
`modesCanonical`), IxCC's conversion, IxCC's consumer budget on what is read
(`withinReadBudget`), and, when the whole constant is read, the canonicity of
the converted value (`V3.constantBytes c = bytes`). -/
def decodeRead (bytes : ByteArray) (proofs : Bool) : Except String V3.Constant := do
  let decoded ← _root_.Ixon.Canonical.deConstant (1024 * 1024) V3.univNodeLimit bytes
  unless decoded.bindersComplete do
    throw "ixon-v5: binder-data section is not complete"
  unless decoded.modesCanonical do
    throw "ixon-v5: record modes are not canonical"
  let c ← V4.constantOfIx decoded
  unless withinReadBudget proofs c do throw "ixon-v5: constant exceeds the consumer budget"
  if proofs || !hasTheorem c then
    unless V3.constantBytes c = bytes do throw "ixon-v5: noncanonical constant"
  return c

/-- The addresses a record keys its definitions by: its own for a standalone
definition, the member projections' for a block. -/
def definitionKeys (address : Ixon.Address) (c : V3.Constant) : Array Ixon.Address :=
  match c.info with
  | .defn _ => #[address]
  | .muts ms => (ms.zipIdx.filterMap fun (m, i) => match m with
      | .defn _ => some (V3.defnProjAddr address i.toUInt64)
      | _ => none)
  | _ => #[]

/-- What a record read in a mode reaches: a projection record's block, and the
references of what is read (with proofs or without a theorem, every reference;
otherwise those of the expressions read). -/
def edges (c : V3.Constant) (proofs : Bool) : Array Ixon.Address :=
  match c.info with
  | .cPrj p => #[p.block]
  | .rPrj p => #[p.block]
  | .iPrj p => #[p.block]
  | .dPrj p => #[p.block]
  | _ =>
    if proofs || !hasTheorem c then c.refs
    else (uses c (readExprs false c)).2.filterMap fun i => c.refs[i.toNat]?

/-- At most eight addresses back from `a` along the walk, for diagnostics. -/
def trail (parent : Std.HashMap Ixon.Address Ixon.Address) (a : Ixon.Address) : String := Id.run do
  let mut out : Array String := #[]
  let mut cur := a
  for _ in [0:8] do
    match parent[cur]? with
    | some p =>
      if p == cur then break
      out := out.push ((toString p).take 12).toString
      cur := p
    | none => break
  return if out.isEmpty then "" else s!", reached from {" ← ".intercalate out.toList}"

/-- The theorems the proposals `eqns` name for each subject, in proposal order:
an index per subject (given on its first proposal) and the groups by index.
One pass; a theorem is pushed onto its group in place (`Array.modify` takes the
group out of the array first, so it is never shared and never copied), so the
grouping is linear in the proposals however many of them name one subject. -/
def eqnsBySubject (eqns : Array (Ixon.Address × Ixon.Address)) :
    Std.HashMap Ixon.Address Nat × Array (Array Ixon.Address) := Id.run do
  let mut index : Std.HashMap Ixon.Address Nat := {}
  let mut groups : Array (Array Ixon.Address) := #[]
  for (f, t) in eqns do
    match index[f]? with
    | some i => groups := groups.modify i (·.push t)
    | none =>
      index := index.insert f groups.size
      groups := groups.push #[t]
  return (index, groups)

/-- **The records the seeds reach**, decoded, in address order (module
note): the least set holding the seeds that are records of `env`, closed under
`edges`; a record is read with proofs exactly when a proof seed reaches it,
the proof seeds being `s.proofs` and the theorem of every proposal whose subject
a reached record keys. A worklist: each record is read at most twice (by
statement, then with proofs), each reference pushed once per reading, so the
walk is linear in the records reached. An address that is not a record (a blob,
or absent) is skipped; the conversion refuses a reference it cannot resolve.
Refused: a reached record that does not decode, lacks a complete binder-data
section, has non-canonical modes, or is over IxCC's consumer budget in what is
read of it. -/
def reach (env : V3.Env) (s : Seeds) : Except String (Array Read) := do
  let (eqnIndex, eqnGroups) := eqnsBySubject s.eqns
  let mut read : Std.HashMap Ixon.Address Read := {}
  let mut parent : Std.HashMap Ixon.Address Ixon.Address := {}
  let mut queue : Array (Ixon.Address × Bool × Ixon.Address) :=
    s.statement.map (fun a => (a, false, a)) ++ s.proofs.map (fun a => (a, true, a))
  let mut qi := 0
  while qi < queue.size do
    let some (a, proofs, from_) := queue[qi]? | break
    qi := qi + 1
    let prev := read[a]?
    if prev.any (fun r => r.proofs || !proofs) then continue
    let first := prev.isNone
    let some bytes := env.consts[a]? | continue
    unless parent.contains a do parent := parent.insert a from_
    let c ← (decodeRead bytes proofs).mapError fun m => s!"{m} (record {a}{trail parent a})"
    read := read.insert a { address := a, constant := c, proofs }
    for b in edges c proofs do queue := queue.push (b, proofs, a)
    if first then
      for k in definitionKeys a c do
        for t in ((eqnIndex[k]?).bind (eqnGroups[·]?)).getD #[] do queue := queue.push (t, true, a)
  return (read.toArray.map (·.2)).qsort fun x y => x.address.cmpBytes y.address == .lt

/-! ## Entry point -/

/-- **Read the records `records`** (the walk's output, `reach`) into a
program. Every record must have a complete binder-data section and canonical
modes. Every record other than a projection record is converted, in address
order; a theorem of a record read without proofs is converted by its statement
(its type; its value `Term.unreadProof`) and recorded in `byStatement`; a
projection record is an alias of the block member it names, which is keyed by
that record's address, so one that names no member of a block read is refused.
`roots` are resolved by address. The table is left empty (`Table.build` fills
it) and the pins are the default (`Pins.fixed`); ingress sets the kernel's
admitted role table's (`KernelFront.pinsOfTable`). -/
def readConsts (env : V3.Env) (records : Array Read) (roots : Array Ixon.Address) :
    Except String Program := do
  let sorted := records.qsort fun x y => x.address.cmpBytes y.address == .lt
  let mut layout : Layout := {}
  let mut projections : Array Ixon.Address := #[]
  for r in sorted do
    unless r.constant.bindersComplete do
      throw s!"src ingress: record {r.address} has incomplete binder-data section"
    unless r.constant.modesCanonical do
      throw s!"src ingress: record {r.address} has non-canonical modes"
    match r.constant.info with
    | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => projections := projections.push r.address
    | _ => pure ()
    layout := layout.add r.address r.constant r.proofs
  let byAddr := layout.byAddr
  for address in projections do
    unless byAddr.contains address do
      throw s!"src ingress: projection record {address} names no member of a block in the closure"
  let isInductive := fun (c : CId) => match layout.items[c]? with
    | some (.indc ..) => true
    | _ => false
  let ctorsOf := fun (c : CId) => match layout.items[c]? with
    | some (.indc _ _ _ ctors) => ctors
    | _ => #[]
  let mut consts : Array ConstEntry := Array.mkEmpty layout.items.size
  let mut byStatement : NatSet := .leaf
  let mut cache : ShareCache := {}
  let mut currentSrc : Option Nat := none
  for h : id in [0:layout.items.size] do
    let item := layout.items[id]
    if currentSrc != some item.src then
      cache := {}
      currentSrc := some item.src
    let source := layout.sources[item.src]?.getD default
    let ctx : Ctx := { env, source, byAddr }
    let run := fun (rootIdx : UInt64) (e : V3.Expr) (m : ShareCache) =>
      (convRoot ctx rootIdx depthBudget e).run m
    let ref := layout.refs[id]?.getD default
    let addr := layout.addrs[id]?.getD default
    let (decl, cache') ← match item with
      | .defn d _ rIdx => do
        let (ty, c0) ← run rIdx d.typ cache
        if d.kind == .thm && !source.proofs then
          pure (Decl.defn d.kind d.safety d.lvls.toNat ty Term.unreadProof, c0)
        else
          let (val, c1) ← run (rIdx + 1) d.value c0
          pure (Decl.defn d.kind d.safety d.lvls.toNat ty val, c1)
      | .recr r _ rIdx => do
        let (ty, c0) ← run rIdx r.typ cache
        let some ind := majorInductive isInductive r ty
          | throw s!"src ingress: recursor {addr} has no inductive major"
        let ctors := ctorsOf ind
        let mut c1 := c0
        let mut rules : Array Rule := #[]
        for h : j in [0:r.rules.size] do
          let rule := r.rules[j]
          let some ctor := ctors[j]?
            | throw s!"src ingress: recursor {addr} has more rules than constructors"
          let (rhs, c2) ← run (rIdx + 1 + j.toUInt64) rule.rhs c1
          c1 := c2
          rules := rules.push { ctor, fields := rule.fields.toNat, rhs }
        pure (Decl.recr (!r.isUnsafe) r.k r.lvls.toNat r.params.toNat r.motives.toNat
          r.minors.toNat r.indices.toNat ind rules.toList ty, c1)
      | .indc ind _ rIdx ctors => do
        let (ty, c0) ← run rIdx ind.typ cache
        pure (Decl.induct (!ind.isUnsafe) ind.lvls.toNat ind.params.toNat ind.indices.toNat
          ty ctors.toList, c0)
      | .ctor c _ rIdx ind => do
        let (ty, c0) ← run rIdx c.typ cache
        pure (Decl.ctor (!c.isUnsafe) c.lvls.toNat ind c.cidx.toNat c.params.toNat
          c.fields.toNat ty, c0)
      | .quot q _ rIdx => do
        let (ty, c0) ← run rIdx q.typ cache
        pure (Decl.quot q.kind q.lvls.toNat ty, c0)
      | .axio a _ rIdx => do
        let (ty, c0) ← run rIdx a.typ cache
        pure (Decl.axio (!a.isUnsafe) a.lvls.toNat ty, c0)
    cache := cache'
    if let .defn d _ _ := item then
      if d.kind == .thm && !source.proofs then byStatement := byStatement.insert id
    consts := consts.push { ref, addr, decl }
  let mut rootIds : Array (Ixon.Address × CId) := #[]
  for root in roots do
    match byAddr[root]? with
    | some c => rootIds := rootIds.push (root, c)
    | none =>
      if env.consts.contains root then throw s!"src ingress: root {root} is not in the closure"
      -- `reach` reads every stored root, so a root not read is not stored
      throw s!"src ingress: root {root} is not a record the artifact stores (a block member \
        named by its projection address is read through that projection record, which the \
        artifact must store; `ix compile` stores one for every member and constructor)"
  return { Program.ofConsts consts.toList with roots := rootIds.toList, byStatement }

/-- Every record of `env` read with proofs (`Seeds.everything`): the whole
artifact, as ingress read it before it read only what the seeds reach. For
tools and tests; no compile path reads this way. -/
def readAll (env : V3.Env) (roots : Array Ixon.Address) : Except String Program := do
  readConsts env (← reach env (Seeds.everything env)) roots

end IxCC.Src.Ingress
