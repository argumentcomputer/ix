module

public import Ix.Aiur.Protocol
public import Ix.Ixon
public import Ix.Claim
public import Ix.KernelCheck.Step

public section

/-!
# IxVM's binder data as witness hints (D2)

The certified kernel's rules read, at every λ and ∀ binder, its datum
`pw : PropWhen`: `never` (the binder's codomain sort is never zero) or
`ifAllZero S` (zero exactly when every level parameter in `S` is). IxVM
reads the datum of every `Lam` and `All` node it converts as a witness hint
(`plans/ixvmc/DECISIONS.md`, D2 revised; the interface is lane cx's
`plans/ixvmc/cx/REPORT.md`, "D2 hint interface"), and validates it where the
kernel's rules do (`Infer.forallE`, `Infer.lam`). So nothing here is
trusted: a wrong datum can only make a claim fail.

## What is computed

The data are the kernel's: IxC's annotation pass (`annotateBody`, its cached
twin `annotateBodyI`) writes `BinderMeta.pw` at every binder, by
`annotPwPiI`/`annotPwLamI` on the annotated opened body. The walk below is
that pass's traversal, node for node, over an Ixon record as IxVM converts
it: the same opening of binders by free variables of their annotated
domains, the same ζ-reduction of `let` (a `let`-bound variable reads as the
annotated value), the same datum functions on the same annotated bodies. It
calls the kernel's datum functions; it does not infer anything itself.

The kernel's environment is IxC's own: the witness's records, read by IxC's
reader and installed by phase A of its fold (`annotDeclStepWithUserAxioms`;
partial and unsafe records by the typing tier), in IxC's check order. The
environment check's phase B is not run: an ill-typed record is installed
anyway, and IxVM rejects it.

## The key

A key is `(rec, ekind, eidx, variant, ordinal)`:
* `rec`, the record whose tables the expression is converted against: the
  constant itself, or for a projection its block;
* the entry: `(0, r)` the `r`-th root expression of `rec`, `(1, n)` its
  sharing entry `n`;
* `variant`: roots are converted at 0; at a `Share n` node the datum is the
  variant entry `(1, n)` is converted with;
* `ordinal`: the node's position in the entry's pre-order over `Lam`, `All`
  and `Share` nodes (children left to right, `Share` not entered).

A sharing entry converted at several places gets one variant per distinct
datum vector: occurrences whose binders need the same data share one (0 in
the common case), and only an open entry under binders of different sorts
needs more. Occurrences under the same enclosing binders are memoized.

## The witness

The data travel in the claim's IO, never in the claim, its digest or the
`.ixe`: channel 7, one stream per record, keyed by the record's 32 address
bytes, its values the record's conversions:

```text
values = nblocks (ekind eidx variant nnodes node*)*
node   = 0            -- a binder, `never`
       | 1 v          -- a share site, entry converted at variant v
       | 2+k p1 … pk  -- a binder, `ifAllZero [p1 … pk]`
```

The Rust host (`crates/ixvm/src/pw.rs`) serves the three hint channels
`ixvm.pw`, `ixvm.pw.param` and `ixvm.pw.share` from it.
-/

namespace IxVM.PwHints

open Ix.Kernel.Reader (ECx Ctx)
open Benchmarks.Kernel.CheckIxeStep (Setup Hints)

abbrev KExpr := Ix.Kernel.Expr .anon

/-- The IO channel of the binder data. -/
def channel : Nat := 7

/-- The datum of one numbered node. -/
inductive Node where
  /-- a `Lam` or `All` node: `none` is `never`, `some ps` is `ifAllZero ps` -/
  | binder (params : Option (Array Nat))
  /-- a `Share` node: the variant its entry is converted with -/
  | share (variant : Nat)
  deriving BEq, Hashable, Repr, Inhabited

/-- One conversion of one entry: the entry, its variant, and the data of its
numbered nodes by ordinal. -/
structure Block where
  ekind : Nat
  eidx : Nat
  variant : Nat
  nodes : Array Node
  deriving BEq, Repr, Inhabited

/-- The datum of a binder from the kernel's `PropWhen`. -/
def Node.ofPw (pw : Ix.Kernel.PropWhen) : Node :=
  .binder (pw.toList?.map List.toArray)

/-- Counts for one annotation run. -/
structure Stats where
  /-- records annotated -/
  records : Nat := 0
  /-- entry conversions (roots, and sharing entries per variant) -/
  blocks : Nat := 0
  binders : Nat := 0
  params : Nat := 0
  shares : Nat := 0
  /-- sharing-entry conversions at a variant beyond 0 -/
  extraVariants : Nat := 0
  /-- binders whose datum the kernel's pass could not compute, given `never` -/
  fallbacks : Nat := 0
  /-- declarations the kernel installed, and records it refused -/
  installed : Nat := 0
  refused : Nat := 0
  /-- the stream values written -/
  values : Nat := 0
  deriving Repr, Inhabited

def Stats.add (a b : Stats) : Stats :=
  { records := a.records + b.records, blocks := a.blocks + b.blocks,
    binders := a.binders + b.binders, params := a.params + b.params,
    shares := a.shares + b.shares, extraVariants := a.extraVariants + b.extraVariants,
    fallbacks := a.fallbacks + b.fallbacks, installed := a.installed + b.installed,
    refused := a.refused + b.refused, values := a.values + b.values }

def Stats.render (s : Stats) : String :=
  s!"records={s.records} blocks={s.blocks} binders={s.binders} params={s.params} \
    shares={s.shares} variants>0={s.extraVariants} fallbacks={s.fallbacks} \
    installed={s.installed} refused={s.refused} values={s.values}"

/-! ## Records and their entries -/

/-- A record's root expressions, in the order IxVM numbers them: a
definition's type and value; an axiom's or quotient's type; a recursor's type
and its rules' right-hand sides; an inductive's type and its constructors'
types; a block's members in order, each contributing its roots, numbered
consecutively. Projection records have none (their block is the record). -/
def roots (c : Ixon.Constant) : Array Ixon.Expr :=
  let ofDefn (d : Ixon.Definition) : Array Ixon.Expr := #[d.typ, d.value]
  let ofRecr (r : Ixon.Recursor) : Array Ixon.Expr := #[r.typ] ++ r.rules.map (·.rhs)
  let ofIndc (i : Ixon.Inductive) : Array Ixon.Expr := #[i.typ] ++ i.ctors.map (·.typ)
  let ofMember : Ixon.MutConst → Array Ixon.Expr
    | .defn d => ofDefn d
    | .indc i => ofIndc i
    | .recr r => ofRecr r
  match c.info with
  | .defn d => ofDefn d
  | .axio a => #[a.typ]
  | .quot q => #[q.typ]
  | .recr r => ofRecr r
  | .muts ms => ms.foldl (init := #[]) fun acc m => acc ++ ofMember m
  | _ => #[]

/-- The number of members `Rec` may name. -/
def memberCount (c : Ixon.Constant) : Nat :=
  match c.info with
  | .muts ms => ms.size
  | _ => 1

/-- One more than the largest loose variable of `e`, under the bounds
`shared` of the sharing entries before it. -/
def looseBound (shared : Array Nat) : Ixon.Expr → Nat
  | .var i => i.toNat + 1
  | .app f a => max (looseBound shared f) (looseBound shared a)
  | .lam _ t b => max (looseBound shared t) (looseBound shared b - 1)
  | .all _ _ t b => max (looseBound shared t) (looseBound shared b - 1)
  | .letE _ t v b =>
    max (max (looseBound shared t) (looseBound shared v)) (looseBound shared b - 1)
  | .prj _ _ v => looseBound shared v
  | .share n => shared[n.toNat]?.getD 0
  | _ => 0

/-- Each sharing entry's loose bound, entry by entry. -/
def bounds (sharing : Array Ixon.Expr) : Array Nat :=
  sharing.foldl (fun out e => out.push (looseBound out e)) #[]

/-! ## The kernel's environment -/

/-- What the circuit reads from a witness: the records on channel 2, the
blobs on channel 4, the reducibility hints on channel 3 and the role table on
channel 6. -/
structure View where
  records : Array (Address × Ixon.Constant) := #[]
  blobs : Std.HashMap Address ByteArray := {}
  hints : Std.HashMap Address Lean.ReducibilityHints := {}
  table : Option ByteArray := none
  /-- channel-2 entries that do not decode -/
  undecoded : Nat := 0

private def addressOfKey (key : Array Aiur.G) : Option Address :=
  if key.size == 32 then some ⟨⟨key.map (·.val.toUInt8)⟩⟩ else none

private def bytesOf (io : Aiur.IOBuffer) (ch : Aiur.G) (info : Aiur.IOKeyInfo) : ByteArray :=
  ⟨((io.data.getD ch #[]).extract info.idx (info.idx + info.len)).map (·.val.toUInt8)⟩

/-- The inverse of the harness's channel-3 encoding (`opaque → 0`,
`abbrev → 0xFFFFFFFF`, `regular n → 1 + n`). -/
private def hintOfG (g : Aiur.G) : Lean.ReducibilityHints :=
  if g.n == 0 then .opaque
  else if g.n == 0xFFFFFFFF then .abbrev
  else .regular (g.n - 1).toUInt32

/-- The view of `io`, records sorted by address (so that a run does not
depend on the hash map's order). A record the environment `env` holds is
taken from it, any other decoded from its bytes. -/
def View.ofBuffer (io : Aiur.IOBuffer) (env : Ixon.Env := {}) : View := Id.run do
  let mut v : View := {}
  for ((ch, key), info) in io.map do
    -- channels 2, 3, 4 and 6 are keyed by 32-byte addresses
    let some a := addressOfKey key | continue
    match ch.n with
    | 2 =>
      match env.getConst? a with
      | some c => v := { v with records := v.records.push (a, c) }
      | none =>
        match Ixon.deConstantExact (bytesOf io ch info) with
        | .ok c => v := { v with records := v.records.push (a, c) }
        | .error _ => v := { v with undecoded := v.undecoded + 1 }
    | 3 =>
      if let some g := (io.data.getD ch #[])[info.idx]? then
        v := { v with hints := v.hints.insert a (hintOfG g) }
    | 4 => v := { v with blobs := v.blobs.insert a (bytesOf io ch info) }
    | 6 => v := { v with table := some (bytesOf io ch info) }
    | _ => pure ()
  return { v with records := v.records.qsort (fun x y => x.1.cmpBytes y.1 == .lt) }

/-- The kernel's environment over a view: IxC's reader context over the
records (and the prelude), and the environment its fold installs. -/
structure KernelEnv where
  setup : Setup
  fe : Ix.Kernel.FEnv .anon
  /-- the records with expressions, in the view's order -/
  owners : Array Address
  installed : Nat
  refused : Nat

/-- The index of `env`, as `Ix.Kernel.mkFEnv` builds it (the newest
constant of a key wins; counters from the oldest), by a loop rather than
`mkFEnv`'s recursion over the whole list. -/
def reindex (env : Ix.Kernel.Env .anon) : Ix.Kernel.FEnv .anon := Id.run do
  let n := env.consts.length
  let mut idx : Std.HashMap (Ix.Kernel.Key .anon) (Nat × Ix.Kernel.ConstantInfo .anon) :=
    Std.HashMap.emptyWithCapacity n
  let mut i := n
  for ci in env.consts do
    i := i - 1
    unless idx.contains ci.name do idx := idx.insert ci.name (i, ci)
  return ⟨env, idx, n⟩

/-- One declaration through phase A of IxC's fold; on failure, the
environment as it was. -/
def installDecl (ev : Ix.Kernel.Evidences .anon) (fe : Ix.Kernel.FEnv .anon) (pos : Nat)
    (d : Ix.Kernel.Declaration .anon) : Ix.Kernel.FEnv .anon × Nat × Bool :=
  let before := fe.env
  match Ix.Kernel.Cached.annotDeclStepWithUserAxioms .verified ev (pos, fe, #[]) d {} with
  | .ok ((pos', fe', _), _) => (fe', pos', true)
  | .error _ => (reindex before, pos + 1, false)

/-- A record's member types (an inductive's constructors included) as
axioms, with their keys and level counts: what the data need of a record the
kernel does not install (an inductive block whose recursors the witness
lacks, which IxC's reader declines; a declaration the kernel refuses), so
that the records that use it can still be typed. -/
def memberAxioms (cx : Ctx .anon) (a : Address) (c : Ixon.Constant) :
    Array (Ix.Kernel.Declaration .anon) := Id.run do
  let n := memberCount c
  let self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) := fun i =>
    if i < n then some (cx.memberKey (.member a i)) else none
  let mr := Ix.Kernel.Reader.MemberReader.mk' cx c id self
  let mut members : Array (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon) × UInt64 × Ixon.Expr) := #[]
  match c.info with
  | .defn d => members := members.push (cx.memberKey (.member a 0), d.lvls, d.typ)
  | .axio x => members := members.push (cx.memberKey (.member a 0), x.lvls, x.typ)
  | .quot q => members := members.push (cx.memberKey (.member a 0), q.lvls, q.typ)
  | .recr r => members := members.push (cx.memberKey (.member a 0), r.lvls, r.typ)
  | .muts ms =>
    for (m, i) in ms.zipIdx do
      match m with
      | .defn d => members := members.push (cx.memberKey (.member a i), d.lvls, d.typ)
      | .recr r => members := members.push (cx.memberKey (.member a i), r.lvls, r.typ)
      | .indc ind =>
        members := members.push (cx.memberKey (.member a i), ind.lvls, ind.typ)
        for (ctor, j) in ind.ctors.zipIdx do
          members := members.push (cx.memberKey (.ctor a i j), ctor.lvls, ctor.typ)
  | _ => pure ()
  let mut out := #[]
  for (key, lvls, typ) in members do
    match key, mr.read typ with
    | .ok k, .ok ty => out := out.push (.axiomDecl ⟨k, List.range lvls.toNat, ty⟩)
    | _, _ => pure ()
  return out

/-- Install `addresses` (owners, in check order) as phase A of IxC's fold
does, continuing past failures: a failed declaration leaves the environment
as it was. Partial and unsafe records go through the typing tier. A record
the kernel does not install gets its member types as axioms
(`memberAxioms`). Returns the environment, the declarations installed and the
records refused. -/
def install (s : Setup) (addresses : Array Address) : Ix.Kernel.FEnv .anon × Nat × Nat := Id.run do
  let mut fe : Ix.Kernel.FEnv .anon := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
  let mut st : Ix.Kernel.Reader.State .anon := {}
  let mut pos := 0
  let mut ok := 0
  let mut bad := 0
  for a in addresses do
    let mut failed := false
    let mut unread := false
    match s.tierRead a with
    | some (.ok d) =>
      let (fe', err) := Benchmarks.Kernel.CheckIxeStep.stepTier fe fe d
      fe := fe'
      if err.isSome then failed := true else ok := ok + 1
    | some (.error _) => failed := true
    | none =>
      match s.read st a with
      | .error _ => failed := true
      | .ok rd =>
        st := st.commit rd
        -- a recursor record reads with its block: if the block was not
        -- installed, its recursors are not either
        if rd.decls.isEmpty then unread := true
        for d in rd.decls do
          let (fe', pos', good) := installDecl s.evidence fe pos d
          fe := fe'
          pos := pos'
          if good then ok := ok + 1 else failed := true
    if failed then bad := bad + 1
    if failed || unread then
      if let some c := s.store[a]? then
        for d in memberAxioms s.cx a c do
          let fresh := match d with
            | .axiomDecl cv => (fe.find? cv.name).isNone
            | _ => false
          if fresh then
            let (fe', pos', _) := installDecl s.evidence fe pos d
            fe := fe'
            pos := pos'
  return (fe, ok, bad)

/-- The kernel's environment for a view. -/
def KernelEnv.ofView (v : View) : Except String KernelEnv := do
  -- the witness's role table and its prelude; a table that does not decode
  -- or whose prelude does not read (a malformed binding, which the circuit
  -- refuses) falls back to the default one, so that every key is answered
  let fallbackTable ← Ix.Kernel.Reader.defaultTable
  let given := (v.table.bind Ix.Kernel.RoleTable.ofBytes).getD fallbackTable
  let chosen : Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon ←
    match Ix.Kernel.Reader.preludeFor (md := .anon) given with
    | .ok pre => pure (given, pre)
    | .error _ => do
      let pre ← Ix.Kernel.Reader.preludeFor (md := .anon) fallbackTable
      pure (fallbackTable, pre)
  let (table, pre) := chosen
  let store : Ixon.CheckOrder.RecordStore :=
    v.records.foldl (fun m (a, c) => m.insert a c) {}
  let hints := Hints.ofStore store v.hints
  let s := Benchmarks.Kernel.CheckIxeStep.setup store (v.blobs[·]?) table pre hints.lookup
  let mut owners : Array Address := #[]
  let mut seen : Std.HashSet Address := {}
  for (a, c) in v.records do
    let o := Ixon.CheckOrder.owner a c
    if seen.contains o then continue
    seen := seen.insert o
    if let some oc := store[o]? then
      unless (roots oc).isEmpty do owners := owners.push o
  let first := pre.records.map (·.1)
  let addresses := Ixon.CheckOrder.closure s.store s.extra (first ++ owners)
  let (fe, installed, refused) := install s addresses
  return { setup := s, fe, owners, installed, refused }

/-! ## The walk

`walk` is `annotateBodyI` over an Ixon entry: it returns the entry's
annotated term, opened over the context's free variables, and records the
datum of each numbered node at its ordinal. -/

/-- A context entry: a binder's free variable or a `let`'s annotated value,
with an identity for the sharing memo. -/
structure CtxEntry where
  id : Nat
  val : KExpr

/-- What a record's walk reads. -/
structure RecCx where
  fe : Ix.Kernel.FEnv .anon
  core : Ix.Kernel.Cached.CoreFnsI .anon
  ecx : ECx .anon
  sharing : Array Ixon.Expr
  bounds : Array Nat

/-- A record's walk state: the sharing entries' variants (by datum vector)
and blocks, and the memo of share sites under the same context. -/
structure WState where
  nextId : Nat := 0
  variants : Std.HashMap Nat (Std.HashMap (Array Node) Nat) := {}
  blocks : Array Block := #[]
  memo : Std.HashMap (Nat × List Nat) (KExpr × Nat) := {}
  fallbacks : Nat := 0

abbrev CM := Ix.Kernel.Cached.CheckCM .anon
abbrev WM := StateT WState CM
/-- An entry's walk: its nodes' data, by ordinal. -/
abbrev EM := StateT (Array Node) WM

/-- Bounds the walk's depth (the recursion is structural on it). -/
def walkFuel : Nat := 1 <<< 24

private def fallback : WM Unit :=
  modify fun st => { st with fallbacks := st.fallbacks + 1 }

private def freshId : WM Nat :=
  modifyGet fun st => (st.nextId, { st with nextId := st.nextId + 1 })

/-- The kernel's datum of a binder whose annotated opened body is `body`,
at `depth` (the body's): `annotPwPiI` for a ∀, `annotPwLamI` for a λ.
Where the kernel's pass fails, `never`. -/
def datum (rc : RecCx) (pi : Bool) (depth : Nat) (body : KExpr) : WM Ix.Kernel.PropWhen := do
  let act : CM Ix.Kernel.PropWhen :=
    if pi then Ix.Kernel.Cached.annotPwPiI rc.core rc.fe depth body
    else Ix.Kernel.Cached.annotPwLamI rc.core rc.fe depth body
  let res : Option Ix.Kernel.PropWhen ←
    (tryCatch (some <$> act) (fun _ => pure none) : CM (Option Ix.Kernel.PropWhen))
  match res with
  | some pw => pure pw
  | none => do fallback; pure Ix.Kernel.PropWhen.never

private def reserve : EM Nat :=
  modifyGet fun nodes => (nodes.size, nodes.push (.binder none))

private def setNode (ord : Nat) (n : Node) : EM Unit :=
  modify fun nodes => nodes.set! ord n

/-- A leaf, by IxC's reader (`convExpr`). -/
private def leaf (rc : RecCx) (e : Ixon.Expr) : WM KExpr :=
  match Ix.Kernel.Reader.convExpr rc.ecx #[] e with
  | .ok k => pure k
  | .error _ => do fallback; pure (.sort .zero)

/-- The variant of entry `n` for the datum vector `nodes`. -/
private def variantOf (n : Nat) (nodes : Array Node) : WM Nat := do
  let st ← get
  let table := st.variants.getD n {}
  match table[nodes]? with
  | some v => pure v
  | none =>
    let v := table.size
    set { st with variants := st.variants.insert n (table.insert nodes v)
                  blocks := st.blocks.push ⟨1, n, v, nodes⟩ }
    pure v

/-- The walk of one entry's tree under `ctx` (innermost first) at binder
depth `depth`. -/
def walk : Nat → RecCx → List CtxEntry → Nat → Ixon.Expr → EM KExpr
  | 0, _, _, _, _ => do fallback; pure (.sort .zero)
  | fuel + 1, rc, ctx, depth, e =>
    match e with
    | .var i =>
      match ctx[i.toNat]? with
      | some c => pure c.val
      | none => do fallback; pure (Ix.Kernel.Expr.mkBvar i.toNat)
    | .app f a => do
      let f' ← walk fuel rc ctx depth f
      let a' ← walk fuel rc ctx depth a
      pure (.app f' a')
    | .lam c t b => do
      let ord ← reserve
      let t' ← walk fuel rc ctx depth t
      let id ← freshId
      let b' ← walk fuel rc (⟨id, .fvar depth t'⟩ :: ctx) (depth + 1) b
      let pw ← datum rc false (depth + 1) b'
      setNode ord (Node.ofPw pw)
      pure (.lam t' (b'.abstract1C depth) ((Ix.Kernel.BinderMeta.ofContracts c .shared).withPw pw))
    | .all c r t b => do
      let ord ← reserve
      let t' ← walk fuel rc ctx depth t
      let id ← freshId
      let b' ← walk fuel rc (⟨id, .fvar depth t'⟩ :: ctx) (depth + 1) b
      let pw ← datum rc true (depth + 1) b'
      setNode ord (Node.ofPw pw)
      pure (.forallE t' (b'.abstract1C depth) ((Ix.Kernel.BinderMeta.ofContracts c r).withPw pw))
    | .letE _ t v b => do
      -- the kernel annotates the type and the value, then the body with the
      -- value transparent (its ζ-reduct)
      let _ ← walk fuel rc ctx depth t
      let v' ← walk fuel rc ctx depth v
      let id ← freshId
      walk fuel rc (⟨id, v'⟩ :: ctx) depth b
    | .prj i f v => do
      let v' ← walk fuel rc ctx depth v
      match rc.ecx.keyAt i with
      | .ok k => pure (.proj k f.toNat v')
      | .error _ => do fallback; pure v'
    | .share n => do
      let ord ← reserve
      let n := n.toNat
      let key := (n, (ctx.take (rc.bounds[n]?.getD 0)).map (·.id))
      let (e', variant) ← match (← getThe WState).memo[key]? with
        | some hit => pure hit
        | none => do
          match rc.sharing[n]? with
          | none => do fallback; pure ((.sort .zero : KExpr), 0)
          | some entry => do
            let (e', nodes) ← ((walk fuel rc ctx depth entry).run #[] : WM (KExpr × Array Node))
            let variant ← variantOf n nodes
            modifyThe WState fun st => { st with memo := st.memo.insert key (e', variant) }
            pure (e', variant)
      setNode ord (.share variant)
      pure e'
    | _ => leaf rc e

/-- A record's blocks: its roots at variant 0, then its sharing entries'
conversions in the order they were first met; and its fallback count. -/
def annotateRecord (k : KernelEnv) (core : Ix.Kernel.Cached.CoreFnsI .anon) (addr : Address)
    (c : Ixon.Constant) : Array Block × Nat :=
  let n := memberCount c
  let cx := k.setup.cx
  let self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) := fun i =>
    if i < n then some (cx.memberKey (.member addr i)) else none
  let ecx : ECx .anon := ⟨cx, c, c.univs.map (Ix.Kernel.Reader.convUniv id), self⟩
  let rc : RecCx := { fe := k.fe, core, ecx, sharing := c.sharing, bounds := bounds c.sharing }
  let act : WM (Array Block) := do
    let mut out := #[]
    for (e, i) in (roots c).zipIdx do
      let (_, nodes) ← (walk walkFuel rc [] 0 e).run #[]
      out := out.push ⟨0, i, 0, nodes⟩
    return out
  match (act.run {}).run {} with
  | .ok ((rs, st), _) => (rs ++ st.blocks, st.fallbacks)
  | .error _ => (#[], 1)

/-- Every owner record's blocks. -/
def annotateKernel (k : KernelEnv) : Array (Address × Array Block) × Stats := Id.run do
  let core := Ix.Kernel.Cached.coreKnotI .verified k.fe Ix.Kernel.checkFuel
  let mut out := #[]
  let mut stats : Stats := { installed := k.installed, refused := k.refused }
  for a in k.owners do
    let some c := k.setup.store[a]? | continue
    let (blocks, fb) := annotateRecord k core a c
    out := out.push (a, blocks)
    stats := { stats with records := stats.records + 1, fallbacks := stats.fallbacks + fb }
    for b in blocks do
      stats := { stats with blocks := stats.blocks + 1
                            extraVariants := stats.extraVariants + (if b.variant > 0 then 1 else 0) }
      for node in b.nodes do
        match node with
        | .binder none => stats := { stats with binders := stats.binders + 1 }
        | .binder (some ps) =>
          stats := { stats with binders := stats.binders + 1, params := stats.params + ps.size }
        | .share _ => stats := { stats with shares := stats.shares + 1 }
  return (out, stats)

/-! ## The stream -/

/-- A record's stream values. -/
def encode (blocks : Array Block) : Array Aiur.G := Id.run do
  let mut out : Array Aiur.G := #[.ofNat blocks.size]
  for b in blocks do
    out := out ++ #[.ofNat b.ekind, .ofNat b.eidx, .ofNat b.variant, .ofNat b.nodes.size]
    for node in b.nodes do
      match node with
      | .binder none => out := out.push (.ofNat 0)
      | .share v => out := (out.push (.ofNat 1)).push (.ofNat v)
      | .binder (some ps) => out := (out.push (.ofNat (2 + ps.size))) ++ ps.map (.ofNat ·)
  return out

/-- A record's blocks from its stream values. -/
def decode (vs : Array Aiur.G) : Except String (Array Block) := do
  let nth (i : Nat) : Except String Nat := match vs[i]? with
    | some g => pure g.n
    | none => throw "binder-data stream ends early"
  let count ← nth 0
  let mut i := 1
  let mut out := #[]
  for _ in [0:count] do
    let ekind ← nth i
    let eidx ← nth (i + 1)
    let variant ← nth (i + 2)
    let size ← nth (i + 3)
    i := i + 4
    let mut nodes := #[]
    for _ in [0:size] do
      let t ← nth i
      i := i + 1
      if t == 0 then nodes := nodes.push (.binder none)
      else if t == 1 then
        nodes := nodes.push (.share (← nth i))
        i := i + 1
      else
        let mut ps := #[]
        for j in [0:t - 2] do ps := ps.push (← nth (i + j))
        i := i + (t - 2)
        nodes := nodes.push (.binder (some ps))
    out := out.push ⟨ekind, eidx, variant, nodes⟩
  unless i == vs.size do throw "binder-data stream has trailing values"
  return out

/-- `io` with every record's stream on `channel`. -/
def seed (io : Aiur.IOBuffer) (tables : Array (Address × Array Block)) : Aiur.IOBuffer × Nat :=
  tables.foldl (init := (io, 0)) fun (io, n) (a, blocks) =>
    if blocks.isEmpty then (io, n) else
    let vs := encode blocks
    (io.extend (.ofNat channel) (a.hash.data.map .ofUInt8) vs, n + vs.size)

/-- Whether `io` already carries binder data. -/
def hasHints (io : Aiur.IOBuffer) : Bool :=
  io.map.keys.any (·.1.n == channel)

/-- **The annotator**: `io` with the binder data of every record it carries on
channel 2, and the run's counts. `env` only saves decoding records it holds. -/
def annotate (io : Aiur.IOBuffer) (env : Ixon.Env := {}) : Except String (Aiur.IOBuffer × Stats) := do
  let v := View.ofBuffer io env
  if v.records.isEmpty then return (io, {})
  let k ← KernelEnv.ofView v
  let (tables, stats) := annotateKernel k
  let (io, values) := seed io tables
  return (io, { stats with values })

/-- The claim kinds whose checks convert expressions (`check`, `eval`,
`checkEnv`, `binding`); the others read records without converting them. -/
def converts : Ix.Claim → Bool
  | .check .. | .eval .. | .checkEnv .. | .binding .. => true
  | _ => false

/-- `io` with binder data when `claim` converts expressions and `io` has none
yet (the claim harness's builders call this last). -/
def withHints (claim : Ix.Claim) (io : Aiur.IOBuffer) (env : Ixon.Env := {}) :
    Except String Aiur.IOBuffer :=
  if converts claim && !hasHints io then (·.1) <$> annotate io env else pure io

/-- The claim a witness's IO carries under its public digest, if it decodes. -/
def claimOf (io : Aiur.IOBuffer) (digest : Array Aiur.G) : Option Ix.Claim := do
  let info ← io.map[((0 : Aiur.G), digest)]?
  (Ix.Claim.de (bytesOf io 0 info)).toOption

end IxVM.PwHints

end
