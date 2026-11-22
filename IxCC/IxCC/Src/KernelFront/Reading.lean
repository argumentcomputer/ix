import IxCC.Src.KernelFront.Accept
import IxCC.Src.Syntax
import IxCC.Src.Pinned
import IxCC.Ixon.V4.Convert
import IxC.Ixon.ModeRead

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
* **terms**: after K3, kernel terms carry no resource modes (`BinderMeta =
  { pw, display }`, `LetMeta = { nonDep, display }`). `corrRec` checks a Src
  term node for node against both the kernel term (shape, constants under the
  key map, literals, `let` `nonDep`, corresponding universes) and the accepted
  v5 record's binder-data section and `let` headers (`Constant.blockNodes?` /
  `binderModeAt?`), refusing any Src mode mismatch against the bytes' reading.
  The universes of a large eliminator's own terms are renamed (the kernel's
  reader gives such a recursor the parameters `n :: [0, …, n-1]`,
  `Ix.Kernel.Reader.recLps`); every other constant's are the same.

The translation the other way (`toKernel`) gives the mode-blind kernel term of
a Src term built by IxCC's table check rather than read (an equation's body),
writing `BinderMeta.leanNever` and `{ nonDep }`. -/

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

/-- The v5 record and starting binder-root offset of a Src constant, read from
`Accepted.ctx.store` so `corrRec` and `Annotate` can validate modes and stored
zero-ness data directly against the accepted bytes' binder-data section. -/
structure RecSource where
  constant : KConstant
  binderful : Array Bool
  rootIdx : UInt64
  deriving Inhabited

/-- One root expression of a v5 record together with its binder-data section. -/
structure RecRoot where
  constant : KConstant
  binderful : Array Bool
  rootIdx : UInt64
  expr : _root_.Ixon.Expr
  deriving Inhabited

/-- Active binder-data block cursor while walking a v5 record expression. -/
structure RecBlock where
  shared : Bool
  index : UInt64
  variant : UInt64
  nodes : Array _root_.Ixon.BinderNode
  deriving Inhabited

/-- Sum the number of binder-root expressions contributed by members `[0..idx)`
of a mutual block `ms`, matching `_root_.Ixon.ConstantInfo.binderRoots` and
`Src.Ingress.Layout.add`. -/
def mutMemberRootStart (ms : Array _root_.Ixon.MutConst) (idx : Nat) : Option UInt64 := Id.run do
  if idx ≥ ms.size then return none
  let mut off : UInt64 := 0
  for i in [0:idx] do
    match ms[i]? with
    | some (.defn _) => off := off + 2
    | some (.recr r) => off := off + 1 + r.rules.size.toUInt64
    | some (.indc ind) => off := off + 1 + ind.ctors.size.toUInt64
    | none => return none
  return some off

/-- Resolve a Src `CRef` to its starting root index in
`constant.info.binderRoots`. -/
def rootStartOf (c : KConstant) : CRef → Option UInt64
  | .member _ i =>
    match c.info with
    | .defn _ | .recr _ | .axio _ | .quot _ => if i == 0 then some 0 else none
    | .muts ms => mutMemberRootStart ms i
    | _ => none
  | .ctor _ i j =>
    match c.info with
    | .muts ms => do
      let base ← mutMemberRootStart ms i
      match ms[i]? with
      | some (.indc ind) => if j < ind.ctors.size then some (base + 1 + j.toUInt64) else none
      | _ => none
    | _ => none

/-- IxCC's program and the kernel's reading, keyed together. -/
structure Reading where
  /-- The kernel key of each Src constant, by `CId`. -/
  keys : Array KKey
  /-- The kernel's declarations by key. -/
  index : Std.HashMap KKey RInfo
  /-- The v5 record and starting binder-root offset of each Src constant, by `CId`. -/
  sources : Array RecSource := #[]
  deriving Inhabited

def Reading.key? (rd : Reading) (c : CId) : Option KKey := rd.keys[c]?

def Reading.info? (rd : Reading) (c : CId) : Option RInfo := do
  rd.index[← rd.key? c]?

def Reading.recSource? (rd : Reading) (c : CId) : Option RecSource := rd.sources[c]?

def RecSource.rootAt? (s : RecSource) (delta : UInt64) : Option RecRoot :=
  let idx := s.rootIdx + delta
  s.constant.info.binderRoots[idx.toNat]?.map fun expr =>
    { constant := s.constant, binderful := s.binderful, rootIdx := idx, expr }

def Reading.typeRoot? (rd : Reading) (c : CId) : Option RecRoot :=
  (rd.recSource? c).bind (·.rootAt? 0)

def Reading.valueRoot? (rd : Reading) (c : CId) : Option RecRoot :=
  (rd.recSource? c).bind (·.rootAt? 1)

def Reading.ruleRoot? (rd : Reading) (r : CId) (j : Nat) : Option RecRoot :=
  (rd.recSource? r).bind (·.rootAt? (1 + j.toUInt64))

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

/-- Compare a Src binder's input mode against a v5 `AllMode` using unified R3
mode accessors (`usage`, `isUnique`, `isBorrowed`). -/
def binderInputMatches (b : Binder) (m : _root_.Ixon.AllMode) : Bool :=
  b.usage == m.usage &&
  b.isUnique == m.isUnique &&
  b.isBorrowed == m.isBorrowed

/-- Compare a Src λ binder's mode against a v5 record's `AllMode`. -/
def lamBinderMatches (b : Binder) (m : _root_.Ixon.AllMode) : Bool :=
  binderInputMatches b m &&
  b.resultMode.isUnique == m.result.isUnique &&
  b.resultMode.isBorrowed == m.result.isBorrowed

/-- Compare a Src Π binder's input and result modes against a v5 record's `AllMode`. -/
def piBinderMatches (b : Binder) (m : _root_.Ixon.AllMode) : Bool :=
  lamBinderMatches b m

/-- Compare a Src `let`'s `nonDep` flag and mode against a v5 record's `.letE`
header using unified R3 mode accessors (`isBorrow`, `binderMode`). -/
def letContractMatches (nonDep1 : Bool) (m1 : Ixon.V3.LetMode)
    (nonDep2 : Bool) (m2 : _root_.Ixon.LetMode) : Bool :=
  nonDep1 == nonDep2 &&
  m1.isBorrow == m2.isBorrow &&
  m1.binderMode == m2.binderMode

/-- **A Src term corresponds to a kernel term** (closed, or with the same
loose bound variables): the same shape node for node, constants under the key
map, the same literals and `let` `nonDep` flags, and corresponding universes
(`levelCorr lps`). After K3, kernel terms carry no resource modes; `corrRec`
below checks λ/Π binder modes and `let` modes against the accepted v5 record's
binder-data section and `let` headers. Walks the two as trees, within `fuel`
levels and a node budget; returns the budget left. Evaluation modes and
relevance classes are Src's own annotations and are not compared. -/
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
    | .lam _ d body, .lam d' body' _ => do
      let n ← corr keys lps fuel d d' budget
      corr keys lps fuel body body' n
    | .pi _ d c, .forallE d' c' _ => do
      let n ← corr keys lps fuel d d' budget
      corr keys lps fuel c c' n
    | .letE nonDep _ _ ty v body, .letE ty' v' body' lm => do
      unless nonDep == lm.nonDep do throw "a let's contract differs"
      let n ← corr keys lps fuel ty ty' budget
      let n ← corr keys lps fuel v v' n
      corr keys lps fuel body body' n
    | .proj s i e, .proj n j e' =>
      if keys[s]? == some n && i == j then corr keys lps fuel e e' budget
      else throw s!"projection {s}.{i} differs from the kernel's {n}.{j}"
    | .natLit n, .lit (.natVal m) => if n == m then pure budget else mismatch
    | .strLit s, .lit (.strVal s') => if s == s' then pure budget else mismatch
    | _, _ => mismatch

private def corrRecLoop (keys : Array KKey) (lps : List Nat) (rec : RecRoot) :
    Nat → RecBlock → Nat → _root_.Ixon.Expr → Term → KTerm → Nat → Except String (Nat × Nat)
  | 0, _, _, _, _, _, _ => throw "the term is deeper than the comparison's depth budget"
  | fuel + 1, blk, ord, e, t, k, budget => do
    match e with
    | .share i =>
      if rec.binderful[i.toNat]?.getD false then
        let some node := blk.nodes[ord]?
          | throw s!"missing binder share node at ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
        let .share variant := node
          | throw s!"expected share node at ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
        let some expansion := rec.constant.sharing[i.toNat]?
          | throw s!"share index {i} out of range"
        let some subNodes := rec.constant.blockNodes? true i variant
          | throw s!"missing binder block for share ({i}, {variant})"
        let (budget', subEnd) ← corrRecLoop keys lps rec fuel
          { shared := true, index := i, variant, nodes := subNodes } 0 expansion t k budget
        unless subEnd == subNodes.size do
          throw s!"share block ({i}, {variant}) consumed {subEnd} of {subNodes.size} nodes"
        pure (budget', ord + 1)
      else
        let some expansion := rec.constant.sharing[i.toNat]?
          | throw s!"share index {i} out of range"
        let (budget', _) ← corrRecLoop keys lps rec fuel
          { shared := true, index := i, variant := 0, nodes := #[] } 0 expansion t k budget
        pure (budget', ord)
    | _ =>
      if budget == 0 then throw "the term exceeds the comparison's node budget"
      let budget := budget - 1
      let mismatch : Except String (Nat × Nat) :=
        throw s!"a Src {srcHead t} node meets a kernel {kHead k} node"
      match t, k, e with
      | .var i, .bvar j, .var vi =>
        if i == j && vi.toNat == i then pure (budget, ord) else mismatch
      | .sort u, .sort l, .sort _ =>
        if levelCorr lps u l then pure (budget, ord) else mismatch
      | .const c us, .const n ls, .ref _ _ | .const c us, .const n ls, .recur _ _ =>
        if keys[c]? == some n && us.length == ls.length &&
            (us.zip ls).all (fun (u, l) => levelCorr lps u l) then pure (budget, ord)
        else throw s!"constant {c} or its universes differ from the kernel's {n}"
      | .app f a _ _, .app f' a', .app ef ea => do
        let (b, ord1) ← corrRecLoop keys lps rec fuel blk ord ef f f' budget
        corrRecLoop keys lps rec fuel blk ord1 ea a a' b
      | .lam b d body, .lam d' body' _, .lam ed eb => do
        -- O(1) lookup of `rec.constant.binderModeAt? ⟨blk.shared, blk.index, blk.variant, ord⟩`
        let some mode := (blk.nodes[ord]?).bind (·.mode?)
          | throw s!"missing λ binder mode at ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
        unless lamBinderMatches b mode do throw "a λ binder's contract differs"
        let (n, ord1) ← corrRecLoop keys lps rec fuel blk (ord + 1) ed d d' budget
        corrRecLoop keys lps rec fuel blk ord1 eb body body' n
      | .pi b d c, .forallE d' c' _, .all ed ec => do
        -- O(1) lookup of `rec.constant.binderModeAt? ⟨blk.shared, blk.index, blk.variant, ord⟩`
        let some mode := (blk.nodes[ord]?).bind (·.mode?)
          | throw s!"missing Π binder mode at ({blk.shared}, {blk.index}, {blk.variant}, {ord})"
        unless piBinderMatches b mode do throw "a Π binder's contracts differ"
        let (n, ord1) ← corrRecLoop keys lps rec fuel blk (ord + 1) ed d d' budget
        corrRecLoop keys lps rec fuel blk ord1 ec c c' n
      | .letE nonDep1 lm1 _ ty v body, .letE ty' v' body' lm, .letE nonDep2 lm2 ety ev eb => do
        unless nonDep1 == lm.nonDep && letContractMatches nonDep1 lm1 nonDep2 lm2 do
          throw "a let's contract differs"
        let (n, ord1) ← corrRecLoop keys lps rec fuel blk ord ety ty ty' budget
        let (n, ord2) ← corrRecLoop keys lps rec fuel blk ord1 ev v v' n
        corrRecLoop keys lps rec fuel blk ord2 eb body body' n
      | .proj s i e1, .proj n j e', .prj _ field ev =>
        if keys[s]? == some n && i == j && field.toNat == i then
          corrRecLoop keys lps rec fuel blk ord ev e1 e' budget
        else throw s!"projection {s}.{i} differs from the kernel's {n}.{j}"
      | .natLit n, .lit (.natVal m), .nat _ =>
        if n == m then pure (budget, ord) else mismatch
      | .strLit s, .lit (.strVal s'), .str _ =>
        if s == s' then pure (budget, ord) else mismatch
      | _, _, _ => mismatch

/-- **A Src term corresponds to both the kernel term and the accepted v5 record**
(post-K3): verifies node-for-node shape, constants, levels, literals, `let`
`nonDep` against `k`, AND λ/Π binder modes and `let` modes against `rec`'s
v5 binder-data section and `.letE` headers. -/
def corrRec (keys : Array KKey) (lps : List Nat) (rec : RecRoot)
    (fuel : Nat) (t : Term) (k : KTerm) (budget : Nat) : Except String Nat := do
  let nodes := (rec.constant.blockNodes? false rec.rootIdx 0).getD #[]
  let (budget', endOrd) ← corrRecLoop keys lps rec fuel
    { shared := false, index := rec.rootIdx, variant := 0, nodes } 0 rec.expr t k budget
  unless endOrd == nodes.size do
    throw s!"binder block {rec.rootIdx} consumed {endOrd} of {nodes.size} nodes"
  pure budget'

/-- **The kernel term of a Src term** (closed, or with the same loose bound
variables), constants under the key map and universes at `levelOf lps`.
Post-K3, kernel terms carry no modes: binders write `BinderMeta.leanNever` and
lets write `{ nonDep }`. Within `fuel` levels and a node budget
(each node once per occurrence). -/
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
    | .lam _ d body =>
      return .lam (← toKernel keys lps fuel d) (← toKernel keys lps fuel body)
        Ix.Kernel.BinderMeta.leanNever
    | .pi _ d c =>
      return .forallE (← toKernel keys lps fuel d) (← toKernel keys lps fuel c)
        Ix.Kernel.BinderMeta.leanNever
    | .letE nonDep _ _ ty v body =>
      return .letE (← toKernel keys lps fuel ty) (← toKernel keys lps fuel v)
        (← toKernel keys lps fuel body) { nonDep }
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
address IxCC keys it by, a backing v5 record in the kernel's store (`RecSource`),
and a kernel declaration under that key whose header corresponds (`headerCheck`). -/
def Reading.build (a : Accepted) (p : Program) : Except String Reading := do
  let cx := a.ctx
  let index := indexTier (indexDecls a.decls) a.tierDecls
  let mut keys : Array KKey := Array.mkEmpty p.size
  let mut sources : Array RecSource := Array.mkEmpty p.size
  let mut binderfulCache : Std.HashMap KAddr (Array Bool) := {}
  for c in [0:p.size] do
    let cref := p.cref c
    let ref := kref cref
    let key ← match cx.memberKey ref with
      | .ok k => pure k
      | .error e => throw s!"constant {c} ({p.addr c}): the kernel's reader keys no constant there: {e}"
    let addr ← match cx.addressOf ref with
      | .ok x => pure x
      | .error e => throw s!"constant {c} ({p.addr c}): {e}"
    unless addr == kaddr (p.addr c) do
      throw s!"constant {c}: IxCC keys it by {p.addr c}, the kernel's reader by {addr}"
    let blockAddr := ref.block
    let some kc := cx.store blockAddr
      | throw s!"constant {c} ({p.addr c}): no v5 record for block {blockAddr}"
    let some rootIdx := rootStartOf kc cref
      | throw s!"constant {c} ({p.addr c}): invalid binder root for {repr cref}"
    let binderful ← match binderfulCache[blockAddr]? with
      | some bf => pure bf
      | none =>
        let bf := _root_.Ixon.binderfulEntries kc.sharing
        binderfulCache := binderfulCache.insert blockAddr bf
        pure bf
    keys := keys.push key
    sources := sources.push { constant := kc, binderful, rootIdx }
  let rd : Reading := { keys, index, sources }
  for c in [0:p.size] do
    let some d := p.decl? c | throw s!"constant {c} is missing"
    let some k := keys[c]? | throw s!"constant {c} has no key"
    let some info := index[k]? | throw s!"constant {c} ({p.addr c}): no kernel declaration under {k}"
    (headerCheck rd d info).mapError fun e => s!"constant {c} ({p.addr c}): {e}"
  return rd

/-- The kernel's type and v5 record of a Src constant correspond to IxCC's. -/
def Reading.typeCheck (rd : Reading) (p : Program) (c : CId) : Except String Unit := do
  let some d := p.decl? c | throw s!"constant {c} is missing"
  let some info := rd.info? c | throw s!"constant {c} has no kernel declaration"
  let some rec := rd.typeRoot? c
    | throw s!"constant {c} ({p.addr c}): missing v5 record for its type"
  let _ ← (corrRec rd.keys info.cv.levelParams rec depthBudget d.type info.cv.type nodeBudget).mapError
    fun e => s!"constant {c} ({p.addr c}), its type: {e}"

/-! ## Pins from the admitted role table -/

/-- An address as a 256-bit number, its bytes read big-endian
(`Src.Pinned.addrNat`). -/
def addrNatK (a : KAddr) : Nat := a.hash.data.toList.foldl (fun n b => n * 256 + b.toNat) 0

/-- The pins the kernel's admitted role table gives: the mapping of
`Src.Pinned` (`knownRoles`, `primRoles`, `stdAxiomRoles`, and `Nat.le` for the
words' bridges) over the kernel's own decoding of the binding section; the D12
allowlist and the fixed-width words' constants, which no role names, at their
fixed addresses. -/
def pinsOfTable (t : Ix.Kernel.RoleTable) : Pins :=
  let pin := fun (r : Ix.Kernel.Role) => (t.addressOf? r).map addrNatK
  { nat := pin .nat, natZero := pin .natZero, natSucc := pin .natSucc, natRec := pin .natRec
    bool := pin .bool, boolTrue := pin .boolTrue, boolFalse := pin .boolFalse, eq := pin .eq
    decIsFalse := pin .decidableIsFalse, decIsTrue := pin .decidableIsTrue
    prims := Pinned.primRoles.filterMap fun (op, r) => (pin r).map (op, ·)
    stdAxioms := Pinned.stdAxiomRoles.filterMap fun (_, r) => pin r
    opaqueByValue := Pins.fixed.opaqueByValue
    natLe := pin .natLe
    wordTypes := Pins.fixed.wordTypes, wordCtors := Pins.fixed.wordCtors
    bitVecOfFin := Pins.fixed.bitVecOfFin, finMk := Pins.fixed.finMk
    wordOps := Pins.fixed.wordOps }

end IxCC.Src.KernelFront
