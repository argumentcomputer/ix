import IxCC.Src.KernelFront.Accept
import IxCC.Src.Syntax
import IxCC.Src.Pinned
import IxCC.Ixon.V4.Convert

/-! # IxCC's program against the kernel's reading

The kernel front end keeps IxCC's own reading of the bytes into a
`Src.Program` (`Src.Ingress.readConsts` of the records its seeds reach,
`Src.Ingress.reach`: a subset of the records the kernel accepted, numbered
over what is read), and checks it against the reading the
kernel accepted (`Accepted.decls`, the declarations the verified fold ran
over), so that every relevance question is asked about the kernel's own terms
at the positions IxCC's terms occupy. This module holds the correspondence:

* **keys**: every Src constant's kernel key is the key the kernel's reader
  gives its identity (`Ix.Kernel.Reader.Ctx.memberKey` of the block member or
  constructor, under the accepted role table: a role key where the table binds
  it, the address otherwise), and the address the reader keys it by is the
  address IxCC keys it by (`Reading.build` refuses otherwise);
* **declarations**: every Src constant's kind, universe parameter count and
  counts (a constructor's parameters and fields, a recursor's arity and
  rules) are those of the kernel's declaration under its key (`headerCheck`);
* **terms**: a Src term corresponds to a kernel term (`corr`) when they have
  the same shape node for node, the same constants under the key map, the
  same literals and contracts, and corresponding universes. The universes of a
  large eliminator's own terms are renamed (the kernel's reader gives such a
  recursor the parameters `n :: [0, …, n-1]`, `Ix.Kernel.Reader.recLps`);
  every other constant's are the same.

The translation the other way (`toKernel`) gives the kernel term of a Src term
built by IxCC's table check rather than read (an equation's body). -/

namespace IxCC.Src.KernelFront

open IxCC.Src
open Ix.Kernel (ConstRef)

/-- Kernel terms, keys and levels, at the anonymous Ixon mode. -/
abbrev KTerm := Ix.Kernel.Expr .anon
abbrev KKey := Ix.Kernel.Key .anon
abbrev KLevel := Ix.Kernel.Level
abbrev KVal := Ix.Kernel.ConstantVal .anon

/-- The kernel's reference of a Src identity. -/
def kref : CRef → ConstRef KAddr
  | .member b i => .member (kaddr b) i
  | .ctor b i c => .ctor (kaddr b) i c

/-- A constant of the kernel's reading, by what IxCC needs of it. -/
inductive RInfo where
  /-- a definition, theorem or opaque, with its reading's value -/
  | defn (cv : KVal) (value : KTerm) (kind : Ixon.DefKind)
  | axio (cv : KVal)
  | quot (kind : Ix.Kernel.QuotKind) (cv : KVal)
  /-- an inductive type of a block with `numParams` parameters -/
  | induct (cv : KVal) (numParams : Nat)
  | ctor (cv : KVal) (numParams numFields : Nat)
  | recr (cv : KVal) (majorIdx rulePrefix : Nat) (rules : List (Ix.Kernel.RecRule .anon))
  /-- a constant of the typing tier: a `partial` or `unsafe` definition (with
  its reading's value), an unsafe opaque or an unsafe axiom; typed, opaque, and
  absent from the logical environment -/
  | tier (cv : KVal)
  /-- anything else a block holds (a projection table) -/
  | other (cv : KVal)
  deriving Inhabited

def RInfo.cv : RInfo → KVal
  | .defn cv .. | .axio cv | .quot _ cv | .induct cv _ | .ctor cv .. | .recr cv .. | .tier cv
  | .other cv => cv

def RInfo.ofInfo (numParams : Nat) : Ix.Kernel.ConstantInfo .anon → RInfo
  | .indInfo cv _ => .induct cv numParams
  | .ctorInfo cv np nf => .ctor cv np nf
  | .recInfo cv mI rP rules => .recr cv mI rP rules
  | ci => .other ci.toConstantVal

/-- The kernel's declarations by key. -/
def indexDecls (decls : Array (Ix.Kernel.Declaration .anon)) : Std.HashMap KKey RInfo := Id.run do
  let mut m : Std.HashMap KKey RInfo := {}
  for d in decls do
    match d with
    | .axiomDecl cv => m := m.insert cv.name (.axio cv)
    | .defnDecl cv v _ => m := m.insert cv.name (.defn cv v .defn)
    | .thmDecl cv v => m := m.insert cv.name (.defn cv v .thm)
    | .opaqueDecl cv v => m := m.insert cv.name (.defn cv v .opaq)
    | .quotDecl k cv => m := m.insert cv.name (.quot k cv)
    | .indDecl block nP =>
      for ci in block do m := m.insert ci.name (RInfo.ofInfo nP ci)
    | .basisDecl k =>
      for ci in k.decls (md := .anon) do m := m.insert ci.name (RInfo.ofInfo 0 ci)
  return m

/-- The tier reader's declarations, added to an index. -/
def indexTier (m : Std.HashMap KKey RInfo) (tds : Array (Nat × Ix.Kernel.Tier.TierDecl .anon)) :
    Std.HashMap KKey RInfo := Id.run do
  let mut m := m
  for (_, td) in tds do
    for cv in td.headers do m := m.insert cv.name (.tier cv)
  return m

/-- IxCC's program and the kernel's reading, keyed together. -/
structure Reading where
  /-- The kernel key of each Src constant, by `CId`. -/
  keys : Array KKey
  /-- The kernel's declarations by key. -/
  index : Std.HashMap KKey RInfo
  deriving Inhabited

def Reading.key? (rd : Reading) (c : CId) : Option KKey := rd.keys[c]?

def Reading.info? (rd : Reading) (c : CId) : Option RInfo := do
  rd.index[← rd.key? c]?

/-! ## Universes and terms -/

/-- A Src universe and a kernel level correspond: the same form, a Src
variable `i` at the kernel's parameter `lps[i]` (`i` itself past the list). -/
def levelCorr (lps : List Nat) : Ixon.Univ → KLevel → Bool
  | .zero, .zero => true
  | .succ u, .succ l => levelCorr lps u l
  | .max a b, .max c d => levelCorr lps a c && levelCorr lps b d
  | .imax a b, .imax c d => levelCorr lps a c && levelCorr lps b d
  | .var i, .param p => lps.getD i.toNat i.toNat == p
  | _, _ => false

/-- A Src universe as a kernel level, the variable `i` at `lps[i]`. -/
def levelOf (lps : List Nat) : Ixon.Univ → KLevel
  | .zero => .zero
  | .succ u => .succ (levelOf lps u)
  | .max a b => .max (levelOf lps a) (levelOf lps b)
  | .imax a b => .imax (levelOf lps a) (levelOf lps b)
  | .var i => .param (lps.getD i.toNat i.toNat)

/-- The Src index of a kernel level parameter of a constant whose kernel
parameters are `lps`: its position in `lps` (the inverse of `levelOf`'s
renaming), the parameter itself past it. -/
def backOf (lps : List Nat) (p : Nat) : Nat :=
  match lps.idxOf? p with
  | some i => i
  | none => p

/-- The nodes `corr` and `toKernel` visit per term, and their depth: the
annotator's budgets (`Src.maxTermDepth` bounds a term's depth at ingress). -/
def nodeBudget : Nat := 1 <<< 20
def depthBudget : Nat := 1 <<< 14

/-- A short description of a term's head, for diagnostics. -/
def srcHead : Term → String
  | .var _ => "var" | .sort _ => "sort" | .const .. => "const" | .app .. => "app"
  | .lam .. => "lam" | .pi .. => "pi" | .letE .. => "let" | .proj .. => "proj"
  | .natLit _ => "nat" | .strLit _ => "str"

def kHead : KTerm → String
  | .bvar _ => "bvar" | .fvar .. => "fvar" | .sort _ => "sort" | .const .. => "const"
  | .app .. => "app" | .lam .. => "lam" | .forallE .. => "forall" | .letE .. => "let"
  | .lit _ => "lit" | .proj .. => "proj"

/-- **A Src term corresponds to a kernel term** (closed, or with the same
loose bound variables): the same shape node for node, constants under the key
map, the same literals, binder, result and let contracts, and corresponding
universes (`levelCorr lps`). Walks the two as trees, within `fuel` levels and a
node budget; returns the budget left. Evaluation modes and relevance classes
are Src's own annotations and are not compared. -/
def corr (keys : Array KKey) (lps : List Nat) : Nat → Term → KTerm → Nat → Except String Nat
  | 0, _, _, _ => throw "the term is deeper than the comparison's depth budget"
  | fuel + 1, t, k, budget => do
    if budget == 0 then throw "the term exceeds the comparison's node budget"
    let budget := budget - 1
    let mismatch : Except String Nat :=
      throw s!"a Src {srcHead t} node meets a kernel {kHead k} node"
    match t, k with
    | .var i, .bvar j => if i == j then pure budget else mismatch
    | .sort u, .sort l => if levelCorr lps u l then pure budget else mismatch
    | .const c us, .const n ls =>
      if keys[c]? == some n && us.length == ls.length &&
          (us.zip ls).all (fun (u, l) => levelCorr lps u l) then pure budget
      else throw s!"constant {c} or its universes differ from the kernel's {n}"
    | .app f a _ _, .app f' a' => do
      let b ← corr keys lps fuel f f' budget
      corr keys lps fuel a a' b
    | .lam b d body, .lam d' body' mb => do
      unless Ixon.V4.binderToIx b.contract == mb.contract do throw "a λ binder's contract differs"
      let n ← corr keys lps fuel d d' budget
      corr keys lps fuel body body' n
    | .pi b r d c, .forallE d' c' mb => do
      unless Ixon.V4.binderToIx b.contract == mb.contract && Ixon.V4.valueToIx r == mb.result do
        throw "a Π binder's contracts differ"
      let n ← corr keys lps fuel d d' budget
      corr keys lps fuel c c' n
    | .letE lc _ ty v body, .letE ty' v' body' lm => do
      unless Ixon.V4.letToIx lc == lm.contract do throw "a let's contract differs"
      let n ← corr keys lps fuel ty ty' budget
      let n ← corr keys lps fuel v v' n
      corr keys lps fuel body body' n
    | .proj s i e, .proj n j e' =>
      if keys[s]? == some n && i == j then corr keys lps fuel e e' budget
      else throw s!"projection {s}.{i} differs from the kernel's {n}.{j}"
    | .natLit n, .lit (.natVal m) => if n == m then pure budget else mismatch
    | .strLit s, .lit (.strVal s') => if s == s' then pure budget else mismatch
    | _, _ => mismatch

/-- **The kernel term of a Src term** (closed, or with the same loose bound
variables), constants under the key map and universes at `levelOf lps`.
Within `fuel` levels and a node budget (each node once per occurrence). -/
def toKernel (keys : Array KKey) (lps : List Nat) : Nat → Term → StateT Nat (Except String) KTerm
  | 0, _ => throw "the term is deeper than the translation's depth budget"
  | fuel + 1, t => do
    let n ← get
    if n == 0 then throw "the term exceeds the translation's node budget"
    set (n - 1)
    let key (c : CId) : StateT Nat (Except String) KKey :=
      match keys[c]? with
      | some k => pure k
      | none => throw s!"constant {c} has no kernel key"
    match t with
    | .var i => pure (Ix.Kernel.Expr.mkBvar i)
    | .sort u => pure (.sort (levelOf lps u))
    | .const c us => return .const (← key c) (us.map (levelOf lps))
    | .app f a _ _ => return .app (← toKernel keys lps fuel f) (← toKernel keys lps fuel a)
    | .lam b d body =>
      return .lam (← toKernel keys lps fuel d) (← toKernel keys lps fuel body)
        (Ix.Kernel.BinderMeta.ofContracts (Ixon.V4.binderToIx b.contract) .shared)
    | .pi b r d c =>
      return .forallE (← toKernel keys lps fuel d) (← toKernel keys lps fuel c)
        (Ix.Kernel.BinderMeta.ofContracts (Ixon.V4.binderToIx b.contract) (Ixon.V4.valueToIx r))
    | .letE lc _ ty v body =>
      return .letE (← toKernel keys lps fuel ty) (← toKernel keys lps fuel v)
        (← toKernel keys lps fuel body) { contract := Ixon.V4.letToIx lc }
    | .proj s i e => return .proj (← key s) i (← toKernel keys lps fuel e)
    | .natLit n => pure (.lit (.natVal n))
    | .strLit s => pure (.lit (.strVal s))

/-! ## Declarations -/

/-- The kernel level parameters of a Src constant's declaration under the
reading (its universes' renaming). -/
def Reading.lps (rd : Reading) (c : CId) : List Nat :=
  ((rd.info? c).map (·.cv.levelParams)).getD []

/-- **A Src declaration's header corresponds to the kernel's**: the same kind,
universe parameter count, and counts. Terms are compared separately
(`corr`). -/
def headerCheck (rd : Reading) (d : Decl) (info : RInfo) : Except String Unit := do
  let n := info.cv.levelParams.length
  unless d.lvls == n do throw s!"{d.lvls} universe parameters; the kernel's declaration has {n}"
  match d, info with
  | .defn k _ _ _ _, .defn _ _ k' =>
    unless k == k' do throw s!"a {d.kindName}, the kernel reads another kind of definition"
  | .induct _ _ params _ _ _, .induct _ nP =>
    unless params == nP do throw s!"{params} parameters; the kernel's block has {nP}"
  | .ctor _ _ _ _ params fields _, .ctor _ nP nF =>
    unless params == nP && fields == nF do
      throw s!"{params} parameters and {fields} fields; the kernel's constructor has {nP} and {nF}"
  | .recr _ _ _ params motives minors indices _ rules _, .recr _ mI rP krules =>
    unless params + motives + minors + indices == mI && params + motives + minors == rP do
      throw "the recursor's counts differ from the kernel's"
    unless rules.length == krules.length do
      throw s!"{rules.length} recursor rules; the kernel's recursor has {krules.length}"
    for (r, kr) in rules.zip krules do
      unless rd.keys[r.ctor]? == some kr.ctor && r.fields == kr.nfields do
        throw "a recursor rule's constructor or field count differs from the kernel's"
  | .quot k _ _, .quot k' _ =>
    let same := match k, k' with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
    unless same do throw "the quotient constant's kind differs from the kernel's"
  | .axio .., .axio _ => pure ()
  -- a `partial` or `unsafe` definition, an unsafe opaque or an unsafe axiom: the typing tier
  | .defn _ s _ _ _, .tier _ =>
    unless s != .safe do throw "a safe definition; the kernel reads a constant of the typing tier"
  | .axio safe .., .tier _ =>
    unless !safe do throw "a safe axiom; the kernel reads a constant of the typing tier"
  -- `Quot.sound` is an axiom record; the prelude installs it in the quotient block
  | .axio .., .quot .sound _ => pure ()
  | _, _ => throw s!"a {d.kindName}; the kernel reads another kind of constant"

/-- **Read IxCC's program against the kernel's accepted reading**: every Src
constant has the key the kernel's reader gives its identity, keyed by the
address IxCC keys it by, and a kernel declaration under that key whose header
corresponds (`headerCheck`). -/
def Reading.build (a : Accepted) (p : Program) : Except String Reading := do
  let cx := a.ctx
  let index := indexTier (indexDecls a.decls) a.tierDecls
  let mut keys : Array KKey := Array.mkEmpty p.size
  for c in [0:p.size] do
    let ref := kref (p.cref c)
    let key ← match cx.memberKey ref with
      | .ok k => pure k
      | .error e => throw s!"constant {c} ({p.addr c}): the kernel's reader keys no constant there: {e}"
    let addr ← match cx.addressOf ref with
      | .ok x => pure x
      | .error e => throw s!"constant {c} ({p.addr c}): {e}"
    unless addr == kaddr (p.addr c) do
      throw s!"constant {c}: IxCC keys it by {p.addr c}, the kernel's reader by {addr}"
    keys := keys.push key
  let rd : Reading := { keys, index }
  for c in [0:p.size] do
    let some d := p.decl? c | throw s!"constant {c} is missing"
    let some k := keys[c]? | throw s!"constant {c} has no key"
    let some info := index[k]? | throw s!"constant {c} ({p.addr c}): no kernel declaration under {k}"
    (headerCheck rd d info).mapError fun e => s!"constant {c} ({p.addr c}): {e}"
  return rd

/-- The kernel's type of a Src constant corresponds to IxCC's. -/
def Reading.typeCheck (rd : Reading) (p : Program) (c : CId) : Except String Unit := do
  let some d := p.decl? c | throw s!"constant {c} is missing"
  let some info := rd.info? c | throw s!"constant {c} has no kernel declaration"
  let _ ← (corr rd.keys info.cv.levelParams depthBudget d.type info.cv.type nodeBudget).mapError
    fun e => s!"constant {c} ({p.addr c}), its type: {e}"

/-! ## Pins from the admitted role table -/

/-- An address as a 256-bit number, its bytes read big-endian
(`Src.Pinned.addrNat`). -/
def addrNatK (a : KAddr) : Nat := a.hash.data.toList.foldl (fun n b => n * 256 + b.toNat) 0

/-- The pins the kernel's admitted role table gives: the mapping of
`Src.Pinned` (`knownRoles`, `primRoles`, `stdAxiomRoles`) over the kernel's own
decoding of the binding section; the D12 allowlist, which no role names, at
its fixed address. -/
def pinsOfTable (t : Ix.Kernel.RoleTable) : Pins :=
  let pin := fun (r : Ix.Kernel.Role) => (t.addressOf? r).map addrNatK
  { nat := pin .nat, natZero := pin .natZero, natSucc := pin .natSucc, natRec := pin .natRec
    bool := pin .bool, boolTrue := pin .boolTrue, boolFalse := pin .boolFalse, eq := pin .eq
    decIsFalse := pin .decidableIsFalse, decIsTrue := pin .decidableIsTrue
    prims := Pinned.primRoles.filterMap fun (op, r) => (pin r).map (op, ·)
    stdAxioms := Pinned.stdAxiomRoles.filterMap fun (_, r) => pin r
    opaqueByValue := Pins.fixed.opaqueByValue }

end IxCC.Src.KernelFront
