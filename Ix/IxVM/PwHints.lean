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
`.ixe`: channel 8 (channel 7 holds `IxVM.Model`'s payloads), one stream per
record, keyed by the record's 32 address bytes, its values the record's
conversions:

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
def channel : Nat := 8

/-- The datum of one numbered node. -/
inductive Node where
  /-- a `Lam` or `All` node: `none` is `never`, `some ps` is `ifAllZero ps` -/
  | binder (params : Option (Array Nat))
  /-- a `Share` node: the variant its entry is converted with -/
  | share (variant : Nat)
  /-- a `Lam` or `All` node whose datum is not decided: the kernel's datum
  function could not run there, or something under the binder is undecided.
  Written only in tainting mode (`RecCx.taint`, the compiler's). -/
  | undecided
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
  /-- share sites whose entry has no binder (through its shares): their variant is
  always 0 -/
  freeShares : Nat := 0
  /-- binders whose datum the kernel's pass could not compute, given `never` -/
  fallbacks : Nat := 0
  /-- binders of a definition value's top λ chain whose datum the kernel's pass
  could not compute, given the declared type's datum at the same place -/
  inherited : Nat := 0
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
    freeShares := a.freeShares + b.freeShares,
    fallbacks := a.fallbacks + b.fallbacks, inherited := a.inherited + b.inherited,
    installed := a.installed + b.installed,
    refused := a.refused + b.refused, values := a.values + b.values }

def Stats.render (s : Stats) : String :=
  s!"records={s.records} blocks={s.blocks} binders={s.binders} params={s.params} \
    shares={s.shares} free-shares={s.freeShares} variants>0={s.extraVariants} fallbacks={s.fallbacks} inherited={s.inherited} \
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

/-- For each root, the root that is its declared type when it is a definition's
value. -/
def valueTypes (c : Ixon.Constant) : Array (Option Nat) :=
  let none' (n : Nat) : Array (Option Nat) := (List.replicate n none).toArray
  let ofMember (base : Nat) : Ixon.MutConst → Array (Option Nat)
    | .defn _ => #[none, some base]
    | .indc i => none' (1 + i.ctors.size)
    | .recr r => none' (1 + r.rules.size)
  match c.info with
  | .defn _ => #[none, some 0]
  | .axio _ | .quot _ => #[none]
  | .recr r => none' (1 + r.rules.size)
  | .muts ms => ms.foldl (init := #[]) fun acc m => acc ++ ofMember acc.size m
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

/-- Whether `e` has a binder, through the sharing entries before it (`shared`). -/
def hasBinder (shared : Array Bool) : Ixon.Expr → Bool
  | .lam .. | .all .. => true
  | .app f a => hasBinder shared f || hasBinder shared a
  | .letE _ t v b => hasBinder shared t || hasBinder shared v || hasBinder shared b
  | .prj _ _ v => hasBinder shared v
  | .share n => shared[n.toNat]?.getD false
  | _ => false

/-- Whether each sharing entry has a binder. -/
def binderful (sharing : Array Ixon.Expr) : Array Bool :=
  sharing.foldl (fun out e => out.push (hasBinder out e)) #[]

/-- The share sites of a tree (its own numbered nodes) whose entry has no binder. -/
def freeSites (full : Array Bool) : Ixon.Expr → Nat
  | .lam _ t b => freeSites full t + freeSites full b
  | .all _ _ t b => freeSites full t + freeSites full b
  | .app f a => freeSites full f + freeSites full a
  | .letE _ t v b => freeSites full t + freeSites full v + freeSites full b
  | .prj _ _ v => freeSites full v
  | .share n => if full[n.toNat]?.getD false then 0 else 1
  | _ => 0

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
  /-- the records of the builder's environment the witness does not carry: read
  by the kernel only, to type the witness's records (an inductive block's
  recursor records, which IxC needs to install the block and its projection
  table, are often outside a claim's closure); never annotated -/
  support : Array (Address × Ixon.Constant) := #[]

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
  let carried : Std.HashSet Address := v.records.foldl (fun s (a, _) => s.insert a) {}
  let mut support := #[]
  for (a, lc) in env.consts do
    unless carried.contains a do
      if let some c := lc.get? then support := support.push (a, c)
  for (a, b) in env.blobs do
    unless v.blobs.contains a do v := { v with blobs := v.blobs.insert a b }
  for (a, h) in env.anonHints do
    unless v.hints.contains a do v := { v with hints := v.hints.insert a h }
  return { v with
    records := v.records.qsort (fun x y => x.1.cmpBytes y.1 == .lt)
    support := support.qsort (fun x y => x.1.cmpBytes y.1 == .lt) }

/-- The kernel's environment over a view: IxC's reader context over the
records (and the prelude), and the environment its fold installs. -/
structure KernelEnv where
  setup : Setup
  fe : Ix.Kernel.FEnv .anon
  /-- the records with expressions, in the view's order -/
  owners : Array Address
  installed : Nat
  refused : Nat
  /-- why each refused record was refused (the first reason) -/
  failures : Array (Address × String) := #[]

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
    (d : Ix.Kernel.Declaration .anon) :
    Ix.Kernel.FEnv .anon × Nat × Option (Ix.Kernel.CheckError .anon) :=
  let before := fe.env
  match Ix.Kernel.Cached.annotDeclStepWithUserAxioms .verified ev (pos, fe, #[]) d {} with
  | .ok ((pos', fe', _), _) => (fe', pos', none)
  | .error (e, _) => (reindex before, pos + 1, some e)

/-- The largest level-parameter count a record's members declare. -/
def levelCount (c : Ixon.Constant) : Nat :=
  let ofMember : Ixon.MutConst → Nat
    | .defn d => d.lvls.toNat
    | .indc i => i.ctors.foldl (fun n k => max n k.lvls.toNat) i.lvls.toNat
    | .recr r => r.lvls.toNat
  match c.info with
  | .defn d => d.lvls.toNat
  | .axio a => a.lvls.toNat
  | .quot q => q.lvls.toNat
  | .recr r => r.lvls.toNat
  | .muts ms => ms.foldl (fun n m => max n (ofMember m)) 0
  | _ => 0

/-- Records declaring more level parameters than this are not given to IxC:
its install lists the parameters and checks them pairwise distinct, so a record
with 2^32 of them (the TagN boundary cases; IxVM cannot prove such a claim either,
D15) would never finish. Their own data need no count: the walk reads the
universe table. -/
def maxLevels : Nat := 1 <<< 12

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
  /-- tainting mode (the compiler's): a binder whose datum the kernel's function
  cannot compute, or under which anything is undecided, is `Node.undecided`
  rather than `never` -/
  taint : Bool := false

/-- A record's walk state: the sharing entries' variants (by datum vector)
and blocks, and the memo of share sites under the same context. -/
structure WState where
  nextId : Nat := 0
  variants : Std.HashMap Nat (Std.HashMap (Array Node) Nat) := {}
  blocks : Array Block := #[]
  memo : Std.HashMap (Nat × List Nat) (KExpr × Nat × Bool) := {}
  fallbacks : Nat := 0
  /-- data taken from the declared type where the kernel's pass could not run -/
  inherited : Nat := 0

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
at `depth` (the body's): `annotPwPiI` for a ∀, `annotPwLamI` for a λ, and
whether it is decided. Where the kernel's pass fails, the declared type's datum
`typed` (decided), else `never` (undecided). -/
def datum (rc : RecCx) (pi : Bool) (depth : Nat) (body : KExpr)
    (typed : Option Ix.Kernel.PropWhen := none) : WM (Ix.Kernel.PropWhen × Bool) := do
  let act : CM Ix.Kernel.PropWhen :=
    if pi then Ix.Kernel.Cached.annotPwPiI rc.core rc.fe depth body
    else Ix.Kernel.Cached.annotPwLamI rc.core rc.fe depth body
  let res : Option Ix.Kernel.PropWhen ←
    (tryCatch (some <$> act) (fun _ => pure none) : CM (Option Ix.Kernel.PropWhen))
  match res, typed with
  | some pw, _ => pure (pw, true)
  | none, some pw => do
    modify fun st => { st with inherited := st.inherited + 1 }
    pure (pw, true)
  | none, none => do fallback; pure (Ix.Kernel.PropWhen.never, false)

private def reserve : EM Nat :=
  modifyGet fun nodes => (nodes.size, nodes.push (.binder none))

private def setNode (ord : Nat) (n : Node) : EM Unit :=
  modify fun nodes => nodes.set! ord n

/-- A leaf, by IxC's reader (`convExpr`), and whether it failed. -/
private def leaf (rc : RecCx) (e : Ixon.Expr) : WM (KExpr × Bool) :=
  match Ix.Kernel.Reader.convExpr rc.ecx #[] e with
  | .ok k => pure (k, false)
  | .error _ => do fallback; pure (.sort .zero, true)

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
depth `depth`: the annotated term, and whether anything in the tree is
undecided (a datum the kernel's function could not compute, or a node the walk
could not read). -/
def walk : Nat → RecCx → List CtxEntry → Nat → Option KExpr → Ixon.Expr → EM (KExpr × Bool)
  | 0, _, _, _, _, _ => do fallback; pure (.sort .zero, true)
  | fuel + 1, rc, ctx, depth, exp, e =>
    match e with
    | .var i =>
      match ctx[i.toNat]? with
      | some c => pure (c.val, false)
      | none => do fallback; pure (Ix.Kernel.Expr.mkBvar i.toNat, true)
    | .app f a => do
      let (f', bf) ← walk fuel rc ctx depth none f
      let (a', ba) ← walk fuel rc ctx depth none a
      pure (.app f' a', bf || ba)
    | .lam c t b => do
      let ord ← reserve
      let (t', bt) ← walk fuel rc ctx depth none t
      let id ← freshId
      -- a definition value's top λ chain: the declared type's ∀ at the same
      -- place, whose datum the kernel's binder congruence requires of the λ
      let (expBody, expPw) : Option KExpr × Option Ix.Kernel.PropWhen := match exp with
        | some (.forallE _ eb m) => (some eb, some m.pw)
        | _ => (none, none)
      let (b', bb) ← walk fuel rc (⟨id, .fvar depth t'⟩ :: ctx) (depth + 1) expBody b
      let (pw, decided) ← datum rc false (depth + 1) b' expPw
      let bad := !decided || bt || bb
      setNode ord (if rc.taint && bad then .undecided else Node.ofPw pw)
      pure (.lam t' (b'.abstract1C depth) ((Ix.Kernel.BinderMeta.ofContracts c .shared).withPw pw),
        bad)
    | .all c r t b => do
      let ord ← reserve
      let (t', bt) ← walk fuel rc ctx depth none t
      let id ← freshId
      let (b', bb) ← walk fuel rc (⟨id, .fvar depth t'⟩ :: ctx) (depth + 1) none b
      let (pw, decided) ← datum rc true (depth + 1) b'
      let bad := !decided || bt || bb
      setNode ord (if rc.taint && bad then .undecided else Node.ofPw pw)
      pure (.forallE t' (b'.abstract1C depth) ((Ix.Kernel.BinderMeta.ofContracts c r).withPw pw),
        bad)
    | .letE _ t v b => do
      -- the kernel annotates the type and the value, then the body with the
      -- value transparent (its ζ-reduct)
      let (_, bt) ← walk fuel rc ctx depth none t
      let (v', bv) ← walk fuel rc ctx depth none v
      let id ← freshId
      let (b', bb) ← walk fuel rc (⟨id, v'⟩ :: ctx) depth exp b
      pure (b', bt || bv || bb)
    | .prj i f v => do
      let (v', bv) ← walk fuel rc ctx depth none v
      match rc.ecx.keyAt i with
      | .ok k => pure (.proj k f.toNat v', bv)
      | .error _ => do fallback; pure (v', true)
    | .share n => do
      let ord ← reserve
      let n := n.toNat
      let key := (n, (ctx.take (rc.bounds[n]?.getD 0)).map (·.id))
      let (e', variant, bad) ← match (← getThe WState).memo[key]? with
        | some hit => pure hit
        | none => do
          match rc.sharing[n]? with
          | none => do fallback; pure ((.sort .zero : KExpr), 0, true)
          | some entry => do
            let ((e', bad), nodes) ← ((walk fuel rc ctx depth none entry).run #[] :
              WM ((KExpr × Bool) × Array Node))
            let variant ← variantOf n nodes
            modifyThe WState fun st => { st with memo := st.memo.insert key (e', variant, bad) }
            pure (e', variant, bad)
      setNode ord (.share variant)
      pure (e', bad)
    | _ => leaf rc e

/-- A record's blocks: its roots at variant 0, then its sharing entries'
conversions in the order they were first met; and its fallback count. -/
def annotateRecord (k : KernelEnv) (core : Ix.Kernel.Cached.CoreFnsI .anon) (addr : Address)
    (c : Ixon.Constant) (taint : Bool := false) : Array Block × Nat × Nat :=
  let n := memberCount c
  let cx := k.setup.cx
  let self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) := fun i =>
    if i < n then some (cx.memberKey (.member addr i)) else none
  let ecx : ECx .anon := ⟨cx, c, c.univs.map (Ix.Kernel.Reader.convUniv id), self⟩
  let rc : RecCx := { fe := k.fe, core, ecx, sharing := c.sharing, bounds := bounds c.sharing, taint }
  let act : WM (Array Block) := do
    let mut out := #[]
    let mut annotated : Array KExpr := #[]
    let tys := valueTypes c
    for (e, i) in (roots c).zipIdx do
      -- a definition's value is walked against its annotated type
      let exp := match tys[i]? with
        | some (some j) => annotated[j]?
        | _ => none
      let ((k, _), nodes) ← (walk walkFuel rc [] 0 exp e).run #[]
      annotated := annotated.push k
      out := out.push ⟨0, i, 0, nodes⟩
    return out
  match (act.run {}).run {} with
  | .ok ((rs, st), _) => (rs ++ st.blocks, st.fallbacks, st.inherited)
  | .error _ => (#[], 1, 0)

/-! ## A record the kernel does not install

IxC installs a record only if its fold accepts it, and refuses records of a
partial closure in cascades (a recursor whose block is not in the input, then
whatever uses that recursor, then the `Nat` operations whose evidence uses
those...). The data must not depend on that: a record the kernel does not
install is annotated by the walk (the kernel's datum functions over the
constants installed before it), and its constants enter the environment
directly, without the fold's checks: a definition with its annotated value
(so that it unfolds), a theorem with its value, everything else by its annotated
type. -/

/-- A record's roots, annotated by the walk against `fe`. -/
def annotatedRoots (cx : Ctx .anon) (fe : Ix.Kernel.FEnv .anon) (addr : Address)
    (c : Ixon.Constant) : Array KExpr :=
  let n := memberCount c
  let self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) := fun i =>
    if i < n then some (cx.memberKey (.member addr i)) else none
  let ecx : ECx .anon := ⟨cx, c, c.univs.map (Ix.Kernel.Reader.convUniv id), self⟩
  let core := Ix.Kernel.Cached.coreKnotI .verified fe Ix.Kernel.checkFuel
  let rc : RecCx := { fe, core, ecx, sharing := c.sharing, bounds := bounds c.sharing }
  let act : WM (Array KExpr) := do
    let mut out : Array KExpr := #[]
    let tys := valueTypes c
    for (e, i) in (roots c).zipIdx do
      let exp := match tys[i]? with
        | some (some j) => out[j]?
        | _ => none
      let ((kx, _), _) ← (walk walkFuel rc [] 0 exp e).run #[]
      out := out.push kx
    return out
  match (act.run {}).run {} with
  | .ok ((rs, _), _) => rs
  | .error _ => #[]

/-- The constants of a record the kernel does not install, with their annotated
types (and a definition's or theorem's annotated value). -/
def lenientInfos (cx : Ctx .anon) (fe : Ix.Kernel.FEnv .anon)
    (hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) (addr : Address)
    (c : Ixon.Constant) : Array (Ix.Kernel.ConstantInfo .anon) := Id.run do
  let rs := annotatedRoots cx fe addr c
  let key (r : Ix.Kernel.ConstRef Address) : Option (Ix.Kernel.Key .anon) := (cx.memberKey r).toOption
  let lps (n : UInt64) : List Nat := List.range n.toNat
  let mut out : Array (Ix.Kernel.ConstantInfo .anon) := #[]
  match c.info with
  | .axio x =>
    if let (some k, some ty) := (key (.member addr 0), rs[0]?) then
      out := out.push (.axiomInfo ⟨k, lps x.lvls, ty⟩)
  | .quot q =>
    if let (some k, some ty) := (key (.member addr 0), rs[0]?) then
      out := out.push (.axiomInfo ⟨k, lps q.lvls, ty⟩)
  | _ =>
    let members : Array Ixon.MutConst := match c.info with
      | .defn d => #[.defn d]
      | .recr r => #[.recr r]
      | .muts ms => ms
      | _ => #[]
    let mut j := 0
    for (m, i) in members.zipIdx do
      match m with
      | .defn d =>
        if let (some k, some ty, some v) := (key (.member addr i), rs[j]?, rs[j + 1]?) then
          let cv : Ix.Kernel.ConstantVal .anon := ⟨k, lps d.lvls, ty⟩
          out := out.push (match d.kind with
            | .defn => .defnInfo cv v ((hint (.member addr i)).getD (.regular 1))
            | .thm => .thmInfo cv v
            | .opaq => .axiomInfo cv)
        j := j + 2
      | .recr r =>
        if let (some k, some ty) := (key (.member addr i), rs[j]?) then
          out := out.push (.axiomInfo ⟨k, lps r.lvls, ty⟩)
        j := j + 1 + r.rules.size
      | .indc ind =>
        if let (some k, some ty) := (key (.member addr i), rs[j]?) then
          out := out.push (.axiomInfo ⟨k, lps ind.lvls, ty⟩)
        for (ctor, ci) in ind.ctors.zipIdx do
          if let (some k, some ty) := (key (.ctor addr i ci), rs[j + 1 + ci]?) then
            out := out.push (.axiomInfo ⟨k, lps ctor.lvls, ty⟩)
        j := j + 1 + ind.ctors.size
  return out

/-- Install `addresses` (owners, in check order) as phase A of IxC's fold
does, continuing past failures: a failed declaration leaves the environment
as it was. Partial and unsafe records go through the typing tier. A record
the kernel does not install enters directly, annotated by the walk
(`lenientInfos`). Returns the environment, the declarations installed and the
records refused. -/
def install (s : Setup) (addresses : Array Address) (lenient : Bool := true) :
    Ix.Kernel.FEnv .anon × Nat × Array (Address × String) := Id.run do
  let mut fe : Ix.Kernel.FEnv .anon := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
  let mut st : Ix.Kernel.Reader.State .anon := {}
  let mut pos := 0
  let mut ok := 0
  let mut failures : Array (Address × String) := #[]
  for a in addresses do
    let mut failure : Option String := none
    let mut unread := false
    if ((s.store[a]?).map levelCount).getD 0 > maxLevels then
      failures := failures.push (a, s!"more than {maxLevels} level parameters: not installed")
      continue
    match s.tierRead a with
    | some (.ok d) =>
      let (fe', err) := Benchmarks.Kernel.CheckIxeStep.stepTier fe fe d
      fe := fe'
      match err with
      | some e => failure := some (Benchmarks.Kernel.CheckIxeStep.tierOutcome d.safety e).2
      | none => ok := ok + 1
    | some (.error e) => failure := some (Benchmarks.Kernel.CheckIxeStep.readOutcome e).2
    | none =>
      match s.read st a with
      | .error e => failure := some (Benchmarks.Kernel.CheckIxeStep.readOutcome e).2
      | .ok rd =>
        st := st.commit rd
        -- a recursor record reads with its block: if the block was not
        -- installed, its recursors are not either
        if rd.decls.isEmpty then unread := true
        for d in rd.decls do
          let (fe', pos', err) := installDecl s.evidence fe pos d
          fe := fe'
          pos := pos'
          match err with
          | none => ok := ok + 1
          | some e =>
            if failure.isNone then
              failure := some (Benchmarks.Kernel.CheckIxeStep.checkOutcome e).2
    if let some why := failure then failures := failures.push (a, why)
    if lenient && (failure.isSome || unread) then
      if let some c := s.store[a]? then
        for ci in lenientInfos s.cx fe s.cx.hint a c do
          if (fe.find? ci.name).isNone then fe := fe.push ci
  return (fe, ok, failures)

/-- The kernel's environment for a view. `prelude?` gives the role table and
its prelude read from the environment's own records (the compiler's, whose
records are not yet the committed prelude's); without it, the witness's table
and the committed prelude. -/
def KernelEnv.ofView (v : View) (lenient : Bool := true)
    (prelude? : Option (Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon) := none) :
    Except String KernelEnv := do
  -- the witness's role table and its prelude; a table that does not decode
  -- or whose prelude does not read (a malformed binding, which the circuit
  -- refuses) falls back to the default one, so that every key is answered
  let chosen : Ix.Kernel.RoleTable × Ix.Kernel.Reader.Prelude .anon ← match prelude? with
    | some p => pure p
    | none => do
      let fallbackTable ← Ix.Kernel.Reader.defaultTable
      let given := (v.table.bind Ix.Kernel.RoleTable.ofBytes).getD fallbackTable
      match Ix.Kernel.Reader.preludeFor (md := .anon) given with
      | .ok pre => pure (given, pre)
      | .error _ => do
        let pre ← Ix.Kernel.Reader.preludeFor (md := .anon) fallbackTable
        pure (fallbackTable, pre)
  let (table, pre) := chosen
  let store : Ixon.CheckOrder.RecordStore :=
    (v.support ++ v.records).foldl (fun m (a, c) => m.insert a c) {}
  let hints := Hints.ofStore store v.hints
  let s := Benchmarks.Kernel.CheckIxeStep.setup store (v.blobs[·]?) table pre hints.lookup
  -- the witness's records with expressions (a projection's block counts only
  -- when the witness carries it: the circuit loads nothing else)
  let carried : Std.HashSet Address := v.records.foldl (fun s (a, _) => s.insert a) {}
  let mut owners : Array Address := #[]
  let mut seen : Std.HashSet Address := {}
  for (a, c) in v.records do
    let o := Ixon.CheckOrder.owner a c
    if seen.contains o || !carried.contains o then continue
    seen := seen.insert o
    if let some oc := store[o]? then
      unless (roots oc).isEmpty do owners := owners.push o
  let first := pre.records.map (·.1)
  let addresses := Ixon.CheckOrder.closure s.store s.extra (first ++ owners)
  let (fe, installed, failures) := install s addresses lenient
  return { setup := s, fe, owners, installed, refused := failures.size, failures }

/-- Every owner record's blocks. -/
def annotateKernel (k : KernelEnv) (taint : Bool := false) :
    Array (Address × Array Block) × Stats := Id.run do
  let core := Ix.Kernel.Cached.coreKnotI .verified k.fe Ix.Kernel.checkFuel
  let mut out := #[]
  let mut stats : Stats := { installed := k.installed, refused := k.refused }
  for a in k.owners do
    let some c := k.setup.store[a]? | continue
    let (blocks, fb, inh) := annotateRecord k core a c taint
    out := out.push (a, blocks)
    stats := { stats with records := stats.records + 1, fallbacks := stats.fallbacks + fb,
                          inherited := stats.inherited + inh }
    let full := binderful c.sharing
    let rs := roots c
    for b in blocks do
      let tree := if b.ekind == 0 then rs[b.eidx]? else c.sharing[b.eidx]?
      stats := { stats with freeShares := stats.freeShares + (tree.map (freeSites full)).getD 0 }
      stats := { stats with blocks := stats.blocks + 1
                            extraVariants := stats.extraVariants + (if b.variant > 0 then 1 else 0) }
      for node in b.nodes do
        match node with
        | .binder none => stats := { stats with binders := stats.binders + 1 }
        | .binder (some ps) =>
          stats := { stats with binders := stats.binders + 1, params := stats.params + ps.size }
        | .share _ => stats := { stats with shares := stats.shares + 1 }
        | .undecided => stats := { stats with binders := stats.binders + 1 }
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
      -- the channel has no undecided datum (the annotator writes none outside
      -- tainting mode): `never`, as an undecided datum was before
      | .undecided => out := out.push (.ofNat 0)
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

/-- The records whose binder data `io` already carries. -/
def annotated (io : Aiur.IOBuffer) : Std.HashSet Address :=
  io.map.fold (init := {}) fun s (ch, key) _ =>
    if ch.n == channel then
      match addressOfKey key with
      | some a => s.insert a
      | none => s
    else s

/-- **The annotator**: `io` with the binder data of every record it carries on
channel 2 that has none yet, and the run's counts. `env` only saves decoding
records it holds. The kernel's environment is built from every record on
channel 2; nothing is done when every record already has its data. -/
def annotate (io : Aiur.IOBuffer) (env : Ixon.Env := {}) : Except String (Aiur.IOBuffer × Stats) := do
  let v := View.ofBuffer io env
  let done := annotated io
  let byAddr : Std.HashMap Address Ixon.Constant := v.records.foldl (fun m (a, c) => m.insert a c) {}
  let pending := v.records.any fun (a, c) =>
    let o := Ixon.CheckOrder.owner a c
    !done.contains o && ((byAddr[o]?).map fun oc => !(roots oc).isEmpty).getD false
  if !pending then return (io, {})
  let k ← KernelEnv.ofView v
  let k := { k with owners := k.owners.filter (!done.contains ·) }
  let (tables, stats) := annotateKernel k
  let (io, values) := seed io tables
  return (io, { stats with values })

/-- The claim kinds whose checks convert expressions (`check`, `eval`,
`checkEnv`, `binding`); the others read records without converting them. -/
def converts : Ix.Claim → Bool
  | .check .. | .eval .. | .checkEnv .. | .binding .. => true
  | _ => false

/-- `io` with binder data for every record that lacks it, when `claim`
converts expressions (the claim harness's builders call this last; calling it
again after adding records annotates those). -/
def withHints (claim : Ix.Claim) (io : Aiur.IOBuffer) (env : Ixon.Env := {}) :
    Except String Aiur.IOBuffer :=
  if converts claim then (·.1) <$> annotate io env else pure io

/-- The claim a witness's IO carries under its public digest, if it decodes. -/
def claimOf (io : Aiur.IOBuffer) (digest : Array Aiur.G) : Option Ix.Claim := do
  let info ← io.map[((0 : Aiur.G), digest)]?
  (Ix.Claim.de (bytesOf io 0 info)).toOption

end IxVM.PwHints

end
