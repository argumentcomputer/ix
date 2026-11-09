import IxCC.Src.Syntax
import IxCC.Ixon.V3.Typed
import Std.Data.HashMap

/-! # Src ingress

Reads a decoded, Tc-typed Ixon closure into the table-free `Src.Program`
(design note 01 §2). Share nodes expand through a per-constant cache, so the
result is a DAG in memory. `ref` resolves through the constant's `refs` table
and the program's address map, `recur` through the block's members, `nat`
blobs decode little-endian and `str` blobs as UTF-8, and universe indices
through `univs`.

Every member of a mutual block gets a `CRef.member`, every constructor a
`CRef.ctor`; each is addressed by its projection constant (the Tc kernel's
identity), so projection constants are aliases. A standalone constant is a
singleton block. -/

namespace IxCC.Src.Ingress

open IxCC.Ixon

/-- One declaration to convert, with the index of the stored constant whose
tables it uses. -/
inductive Item where
  | defn (d : V3.Definition) (src : Nat)
  | recr (r : V3.Recursor) (src : Nat)
  | indc (ind : V3.Inductive) (src : Nat) (ctors : Array CId)
  | ctor (c : V3.Constructor) (src : Nat) (ind : CId)
  | quot (q : V3.Quotient) (src : Nat)
  | axio (a : V3.Axiom) (src : Nat)
  deriving Inhabited

def Item.src : Item → Nat
  | .defn _ s | .recr _ s | .indc _ s _ | .ctor _ s _ | .quot _ s | .axio _ s => s

/-- A stored constant with the member `CId`s that resolve its `recur`s. -/
structure Source where
  constant : V3.Constant
  members : Array CId
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

/-- Lay out one stored constant. Projections are aliases and add nothing. -/
def add (l : Layout) (address : Ixon.Address) (c : V3.Constant) : Layout := Id.run do
  let src := l.sources.size
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
    for h : i in [0:members.size] do
      let idx := i.toUInt64
      match members[i] with
      | .defn d =>
        l := (l.push (.member address i) (V3.Tc.defnProjAddr address idx) (.defn d src)).1
      | .recr r =>
        l := (l.push (.member address i) (V3.Tc.recrProjAddr address idx) (.recr r src)).1
      | .indc ind =>
        l := (l.push (.member address i) (V3.Tc.indcProjAddr address idx)
          (.indc ind src (ctorIds[i]?.getD #[]))).1
    for h : i in [0:members.size] do
      match members[i] with
      | .indc ind =>
        for h : j in [0:ind.ctors.size] do
          l := (l.push (.ctor address i j) (V3.Tc.ctorProjAddr address i.toUInt64 j.toUInt64)
            (.ctor ind.ctors[j] src (base + i))).1
      | _ => pure ()
    return { l with sources := l.sources.push { constant := c, members := memberIds } }
  | .defn d =>
    let (l, id) := l.push (.member address 0) address (.defn d src)
    return { l with sources := l.sources.push { constant := c, members := #[id] } }
  | .recr r =>
    let (l, id) := l.push (.member address 0) address (.recr r src)
    return { l with sources := l.sources.push { constant := c, members := #[id] } }
  | .axio a =>
    let (l, _) := l.push (.member address 0) address (.axio a src)
    return { l with sources := l.sources.push { constant := c, members := #[] } }
  | .quot q =>
    let (l, _) := l.push (.member address 0) address (.quot q src)
    return { l with sources := l.sources.push { constant := c, members := #[] } }
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => l

end Layout

/-! ## Expression conversion -/

structure Ctx where
  env : V3.Env
  source : Source
  byAddr : Std.HashMap Ixon.Address CId

abbrev ConvM := StateT (Std.HashMap UInt64 Term) (Except String)

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

/-- Convert one expression. `fuel` bounds the nesting depth, share
expansions included; the cache holds each expanded share index once. -/
def conv (ctx : Ctx) : Nat → V3.Expr → ConvM Term
  | 0, _ => throw "src ingress: expression depth budget exhausted"
  | fuel + 1, e => match e with
    | .sort i => return .sort (← univ ctx i)
    | .var i => return .var i.toNat
    | .ref i us => return .const (← resolveRef ctx i) (← us.toList.mapM (univ ctx))
    | .recur i us => do
      let some c := ctx.source.members[i.toNat]?
        | throw s!"src ingress: recursive member index {i} out of range"
      return .const c (← us.toList.mapM (univ ctx))
    | .prj i field v => return .proj (← resolveRef ctx i) field.toNat (← conv ctx fuel v)
    | .str i => do
      let bytes ← blob ctx i
      match String.fromUTF8? bytes with
      | some s => return .strLit s
      | none => throw "src ingress: string blob is not valid UTF-8"
    | .nat i => return .natLit (V3.Tc.natFromBytesLE (← blob ctx i).data)
    | .app f a => return .app (← conv ctx fuel f) (← conv ctx fuel a) .strict .rel
    | .lam c d b => return .lam { contract := c } (← conv ctx fuel d) (← conv ctx fuel b)
    | .all c r d b => return .pi { contract := c } r (← conv ctx fuel d) (← conv ctx fuel b)
    | .letE c t v b =>
      return .letE c .rel (← conv ctx fuel t) (← conv ctx fuel v) (← conv ctx fuel b)
    | .share i => do
      if let some t := (← get)[i]? then return t
      let some expansion := ctx.source.constant.sharing[i.toNat]?
        | throw s!"src ingress: share index {i} out of range"
      let t ← conv ctx fuel expansion
      modify (·.insert i t)
      return t

/-- Depth budget for one expression, share expansions included. -/
def depthBudget : Nat := 1 <<< 16

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

/-! ## Entry point -/

/-- Read a decoded v3 environment. Every constant is converted; `roots` are
resolved by address. The table is left empty (`Table.build` fills it).
Ingress works on arrays and hash maps (it is not on the recheck path) and
returns the kernel-evaluable `Program`. -/
def ofEnv (env : V3.Env) (roots : Array Ixon.Address) : Except String Program := do
  let addresses := env.consts.keys.toArray.qsort (fun a b => a.cmpBytes b == .lt)
  let mut layout : Layout := {}
  for address in addresses do
    let some bytes := env.consts[address]? | throw s!"src ingress: missing constant {address}"
    let decoded ← V3.decodeConstant bytes
    layout := layout.add address decoded.value
  let byAddr := layout.byAddr
  let isInductive := fun (c : CId) => match layout.items[c]? with
    | some (.indc ..) => true
    | _ => false
  let ctorsOf := fun (c : CId) => match layout.items[c]? with
    | some (.indc _ _ ctors) => ctors
    | _ => #[]
  let mut consts : Array ConstEntry := Array.mkEmpty layout.items.size
  let mut cache : Std.HashMap UInt64 Term := {}
  let mut currentSrc : Option Nat := none
  for h : id in [0:layout.items.size] do
    let item := layout.items[id]
    if currentSrc != some item.src then
      cache := {}
      currentSrc := some item.src
    let source := layout.sources[item.src]?.getD default
    let ctx : Ctx := { env, source, byAddr }
    let run := fun (e : V3.Expr) (m : Std.HashMap UInt64 Term) =>
      (conv ctx depthBudget e).run m
    let ref := layout.refs[id]?.getD default
    let addr := layout.addrs[id]?.getD default
    let (decl, cache') ← match item with
      | .defn d _ => do
        let (ty, c0) ← run d.typ cache
        let (val, c1) ← run d.value c0
        pure (Decl.defn d.kind d.safety d.lvls.toNat ty val, c1)
      | .recr r _ => do
        let (ty, c0) ← run r.typ cache
        let some ind := majorInductive isInductive r ty
          | throw s!"src ingress: recursor {addr} has no inductive major"
        let ctors := ctorsOf ind
        let mut c1 := c0
        let mut rules : Array Rule := #[]
        for h : j in [0:r.rules.size] do
          let rule := r.rules[j]
          let some ctor := ctors[j]?
            | throw s!"src ingress: recursor {addr} has more rules than constructors"
          let (rhs, c2) ← run rule.rhs c1
          c1 := c2
          rules := rules.push { ctor, fields := rule.fields.toNat, rhs }
        pure (Decl.recr (!r.isUnsafe) r.k r.lvls.toNat r.params.toNat r.motives.toNat
          r.minors.toNat r.indices.toNat ind rules.toList ty, c1)
      | .indc ind _ ctors => do
        let (ty, c0) ← run ind.typ cache
        pure (Decl.induct (!ind.isUnsafe) ind.lvls.toNat ind.params.toNat ind.indices.toNat
          ty ctors.toList, c0)
      | .ctor c _ ind => do
        let (ty, c0) ← run c.typ cache
        pure (Decl.ctor (!c.isUnsafe) c.lvls.toNat ind c.cidx.toNat c.params.toNat
          c.fields.toNat ty, c0)
      | .quot q _ => do
        let (ty, c0) ← run q.typ cache
        pure (Decl.quot q.kind q.lvls.toNat ty, c0)
      | .axio a _ => do
        let (ty, c0) ← run a.typ cache
        pure (Decl.axio (!a.isUnsafe) a.lvls.toNat ty, c0)
    cache := cache'
    consts := consts.push { ref, addr, decl }
  let mut rootIds : Array (Ixon.Address × CId) := #[]
  for root in roots do
    match byAddr[root]? with
    | some c => rootIds := rootIds.push (root, c)
    | none => throw s!"src ingress: root {root} is not in the closure"
  return { Program.ofConsts consts.toList with roots := rootIds.toList }

end IxCC.Src.Ingress

namespace IxCC.Src

private def pinAddr (hex : String) : Ixon.Address :=
  (Ixon.Address.fromString hex).getD default

private def resolveKnown (p : Program) : Known :=
  { nat := p.lookup (pinAddr "35e1cc809f6f076521a43f85068d5592220407c0532b6a08952f40d8523d04bc")
    natZero := p.lookup (pinAddr "eeb2e6268ff6d0e6b2e9764d9940b81bb64b9f8f4b1358d294ff9817e6941a46")
    natSucc := p.lookup (pinAddr "42d6ed31536f0958176f1dc973383808ac8583223746ebca78dbe389b65321a6")
    natRec := p.lookup (pinAddr "c8322e03d558f85a8edc7fe68524013880ad0bbcb7dc890136d247154b230992")
    bool := p.lookup (pinAddr "e6eba3c8b4d19f6a1076b39fa89aec61dccbb960f83d9a62e6acf35a69c9a0a4")
    boolTrue := p.lookup (pinAddr "a29a636176cf1135d077eb074798f9007c78e7801383e9cff363bae5edf05762")
    boolFalse := p.lookup (pinAddr "dda12bcb330727f6dfb816bc9752aabd0520e6515b79fc8a5a9e713866f4c63e")
    eq := p.lookup (pinAddr "c37d6290e00fb865fb5db7bce18fd69e6d1674ad573724b85466ea9f7578a207")
    decIsFalse := p.lookup (pinAddr "8cc0e1360c1b29108dab3d6172e7fce8a9aa9640daa4bbe99ba1305d9623624b")
    decIsTrue := p.lookup (pinAddr "363d071182be414e1a58599b83f5e19f9b873723054f4287ba69705aafef27da") }

/-- Ingress from a typed input (decoded and Tc-checked, no resource gate). -/
def ofTyped {bytes : ByteArray} (input : Ixon.V3.TypedInput bytes)
    (roots : Array Ixon.Address) : Except String Program := do
  let p ← Ingress.ofEnv input.env roots
  return { p with known := resolveKnown p }

end IxCC.Src
