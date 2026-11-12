import IxCC.Src.Syntax
import IxCC.Src.Pinned
import IxCC.Src.Hints
import IxCC.Src.Resource.Profile
import IxCC.Ixon.V3.Keys
import IxCC.Ixon.V3.Support
import Std.Data.HashMap
import Std.Data.HashSet

/-! # Src ingress

Reads the records of a decoded Ixon closure that its seeds reach into the
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
identities IxCC pins; every address the resource context names; and, read with
their proofs, the resource context's equation theorems and the equation theorem
of every sidecar proposal whose subject is reached), across every reference of
what is read, a projection record reaching its block. An address that is not a
record the artifact stores is not read: a block member named by its projection
address is read only if the artifact stores that projection record (`ix
compile` writes one for every member and constructor) or something else
reaches the block. A record is read *with proofs* when a proof seed reaches it
(the table checks walk their proofs, `Table.checkAxiomClosure`), and otherwise
*by statement*: whole, except that a
theorem's proof is not read and its references are not followed. A theorem so
read keeps its type and is recorded in `Program.byStatement`, its value
`Term.unreadProof`. Not followed: the recursors of a reached inductive (a
reached recursor is reached by reference), and the proof of a theorem read by
statement. The result is the least fixpoint of these rules, a function of the
records, the sidecar and the role table, whatever order the walk takes; IxCC's
consumer budget (`V3.Constant.withinBudget`) applies to what is read of each
record, and a reached record over it is refused.

**How it is read.** Share nodes expand through a per-constant cache, so the
result is a DAG in memory. `ref` resolves through the constant's `refs` table
and the program's address map, `recur` through the block's members, `nat`
blobs decode little-endian and `str` blobs as UTF-8, and universe indices
through `univs`.

Every member of a mutual block gets a `CRef.member`, every constructor a
`CRef.ctor`; each is addressed by its projection constant's address (the
block-member keys, `V3.defnProjAddr` and its siblings), so projection
constants are aliases. A standalone constant is a
singleton block. Constants are numbered in address order over the records
read, a block member by member, then constructor by constructor. -/

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

/-- A stored constant with the member `CId`s that resolve its `recur`s, and
whether its theorems' proofs are read. -/
structure Source where
  constant : V3.Constant
  members : Array CId
  proofs : Bool := true
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
def add (l : Layout) (address : Ixon.Address) (c : V3.Constant) (proofs : Bool := true) :
    Layout := Id.run do
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
        l := (l.push (.member address i) (V3.defnProjAddr address idx) (.defn d src)).1
      | .recr r =>
        l := (l.push (.member address i) (V3.recrProjAddr address idx) (.recr r src)).1
      | .indc ind =>
        l := (l.push (.member address i) (V3.indcProjAddr address idx)
          (.indc ind src (ctorIds[i]?.getD #[]))).1
    for h : i in [0:members.size] do
      match members[i] with
      | .indc ind =>
        for h : j in [0:ind.ctors.size] do
          l := (l.push (.ctor address i j) (V3.ctorProjAddr address i.toUInt64 j.toUInt64)
            (.ctor ind.ctors[j] src (base + i))).1
      | _ => pure ()
    return { l with sources := l.sources.push { constant := c, members := memberIds, proofs } }
  | .defn d =>
    let (l, id) := l.push (.member address 0) address (.defn d src)
    return { l with sources := l.sources.push { constant := c, members := #[id], proofs } }
  | .recr r =>
    let (l, id) := l.push (.member address 0) address (.recr r src)
    return { l with sources := l.sources.push { constant := c, members := #[id], proofs } }
  | .axio a =>
    let (l, _) := l.push (.member address 0) address (.axio a src)
    return { l with sources := l.sources.push { constant := c, members := #[], proofs } }
  | .quot q =>
    let (l, _) := l.push (.member address 0) address (.quot q src)
    return { l with sources := l.sources.push { constant := c, members := #[], proofs } }
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => l

end Layout

/-! ## Expression conversion -/

structure Ctx where
  env : V3.Env
  source : Source
  byAddr : Std.HashMap Ixon.Address CId

abbrev ConvM := StateT (Std.HashMap UInt64 (Term × Nat)) (Except String)

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

/-- Convert one expression, with the converted term's height. `fuel` bounds the
nesting depth, share expansions included; the cache holds each expanded share
index once, with its height, so a share reused deeper than its first use is
checked against the depth left there too. -/
def convH (ctx : Ctx) : Nat → V3.Expr → ConvM (Term × Nat)
  | 0, _ => throw "src ingress: expression depth budget exhausted"
  | fuel + 1, e => match e with
    | .sort i => return (.sort (← univ ctx i), 1)
    | .var i => return (.var i.toNat, 1)
    | .ref i us => return (.const (← resolveRef ctx i) (← us.toList.mapM (univ ctx)), 1)
    | .recur i us => do
      let some c := ctx.source.members[i.toNat]?
        | throw s!"src ingress: recursive member index {i} out of range"
      return (.const c (← us.toList.mapM (univ ctx)), 1)
    | .prj i field v => do
      let s ← resolveRef ctx i
      let (t, h) ← convH ctx fuel v
      return (.proj s field.toNat t, h + 1)
    | .str i => do
      let bytes ← blob ctx i
      match String.fromUTF8? bytes with
      | some s => return (.strLit s, 1)
      | none => throw "src ingress: string blob is not valid UTF-8"
    | .nat i => return (.natLit (V3.natFromBytesLE (← blob ctx i).data), 1)
    | .app f a => do
      let (f, hf) ← convH ctx fuel f
      let (a, ha) ← convH ctx fuel a
      return (.app f a .strict .rel, max hf ha + 1)
    | .lam c d b => do
      let (d, hd) ← convH ctx fuel d
      let (b, hb) ← convH ctx fuel b
      return (.lam { contract := c } d b, max hd hb + 1)
    | .all c r d b => do
      let (d, hd) ← convH ctx fuel d
      let (b, hb) ← convH ctx fuel b
      return (.pi { contract := c } r d b, max hd hb + 1)
    | .letE c t v b => do
      let (t, ht) ← convH ctx fuel t
      let (v, hv) ← convH ctx fuel v
      let (b, hb) ← convH ctx fuel b
      return (.letE c .rel t v b, max ht (max hv hb) + 1)
    | .share i => do
      if let some (t, h) := (← get)[i]? then
        if h > fuel then throw "src ingress: expression depth budget exhausted"
        return (t, h)
      let some expansion := ctx.source.constant.sharing[i.toNat]?
        | throw s!"src ingress: share index {i} out of range"
      let (t, h) ← convH ctx fuel expansion
      modify (·.insert i (t, h))
      return (t, h)

/-- Convert one expression (`convH` without the height). -/
def conv (ctx : Ctx) (fuel : Nat) (e : V3.Expr) : ConvM Term := (·.1) <$> convH ctx fuel e

/-- Depth budget for one expression, share expansions included
(`Src.maxTermDepth`). A share converted once is reused without its depth being
counted again, so the recheck path checks the program's depth again, as
trees, before its front end (`Recheck.checkSrc`). -/
def depthBudget : Nat := maxTermDepth

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
  /-- Read by statement: the sidecar's roots, the pinned identities, the
  resource context's addresses. -/
  statement : Array Ixon.Address := #[]
  /-- Read with proofs: the resource context's equation theorems. -/
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
entries resolve as they would on the whole artifact; every address the resource
context names (`Resource.validateContext` resolves them), its equation theorems
with their proofs; and every proposal's theorem, read with its proof once the
proposal's subject is reached. A profile that does not decode contributes
nothing (the resource binding then refuses). -/
def Seeds.of (h : Hints) (pins : Pins) : Seeds :=
  let (resStatement, resProofs) : Array Ixon.Address × Array Ixon.Address :=
    match h.resource with
    | none => (#[], #[])
    | some ctx =>
      let p := (Resource.Profile.ofBytes ctx.bytes).toOption.getD {}
      (p.assumptions ++ p.shareableTypes ++ p.choices ++ p.caseDefinitions ++ p.linearTypes ++
          #[p.natType, p.stringType, p.eqType].filterMap id ++ p.interfaces.map (·.1) ++
          p.equations.map (·.1) ++ (ctx.pairs.map (·.definition)).toArray,
        p.equations.map (·.2) ++ (ctx.pairs.map (·.equation)).toArray)
  { statement := h.roots.map (·.1) ++ pinnedAddresses pins ++ resStatement
    proofs := resProofs
    eqns := h.proposals.filterMap fun p => p.theorem?.map (p.subject, ·) }

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
    | .lam _ t b | .all _ _ t b => todo := (todo.push t).push b
    | .letE _ t v b => todo := ((todo.push t).push v).push b
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

/-- Decode a reached record: the kernel's canonical decoder, IxCC's
conversion, then IxCC's consumer budget on what is read
(`withinReadBudget`), and, when the whole constant is read, the canonicity of
the converted value (as `V3.decodeConstant` checks it). -/
def decodeRead (bytes : ByteArray) (proofs : Bool) : Except String V3.Constant := do
  let decoded ← _root_.Ixon.Canonical.deConstant (1024 * 1024) V3.univNodeLimit bytes
  let c ← V4.constantOfIx decoded
  unless withinReadBudget proofs c do throw "ixon-v4: constant exceeds the consumer budget"
  if proofs || !hasTheorem c then
    unless V3.constantBytes c = bytes do throw "ixon-v4: noncanonical constant"
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
Refused: a reached record that does not decode or is over IxCC's consumer
budget in what is read of it. -/
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
program. Every record other than a projection record is converted, in address
order; a theorem of a record read without proofs is converted by its statement
(its type; its value `Term.unreadProof`) and recorded in `byStatement`; a
projection record is an alias of the block member it names, which is keyed by
that record's address, so one that names no member of a block read is
refused. `roots` are resolved by address. The table is left empty
(`Table.build` fills it) and the pins are the default (`Pins.fixed`); ingress
sets the kernel's admitted role table's (`KernelFront.pinsOfTable`). -/
def readConsts (env : V3.Env) (records : Array Read) (roots : Array Ixon.Address) :
    Except String Program := do
  let sorted := records.qsort fun x y => x.address.cmpBytes y.address == .lt
  let mut layout : Layout := {}
  let mut projections : Array Ixon.Address := #[]
  for r in sorted do
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
    | some (.indc _ _ ctors) => ctors
    | _ => #[]
  let mut consts : Array ConstEntry := Array.mkEmpty layout.items.size
  let mut byStatement : NatSet := .leaf
  let mut cache : Std.HashMap UInt64 (Term × Nat) := {}
  let mut currentSrc : Option Nat := none
  for h : id in [0:layout.items.size] do
    let item := layout.items[id]
    if currentSrc != some item.src then
      cache := {}
      currentSrc := some item.src
    let source := layout.sources[item.src]?.getD default
    let ctx : Ctx := { env, source, byAddr }
    let run := fun (e : V3.Expr) (m : Std.HashMap UInt64 (Term × Nat)) =>
      (conv ctx depthBudget e).run m
    let ref := layout.refs[id]?.getD default
    let addr := layout.addrs[id]?.getD default
    let (decl, cache') ← match item with
      | .defn d _ => do
        let (ty, c0) ← run d.typ cache
        if d.kind == .thm && !source.proofs then
          pure (Decl.defn d.kind d.safety d.lvls.toNat ty Term.unreadProof, c0)
        else
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
    if let .defn d _ := item then
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
