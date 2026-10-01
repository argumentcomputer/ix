/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Environment
import Ix.SemanticContract
import Ix.IxonUniv
import Ix.Tc.Validate
import Ix.CanonM
import Benchmarks.Kernel.CheckIxeStep

/-! # The Ixon reader against a direct translation of Lean's constants

The fidelity test of `Ix.Kernel.IxonReader`, in the style of Ix.Tc's
meta roundtrip (`Tests/Ix/Tc/Roundtrip.lean`, `Ix.Tc.metaRoundtripEnv`):
compile a Lean environment to Ixon with Ix's compiler, read every primary
record through the reader exactly as the census does (the Ixon prelude's
records first, then the census's dependency order, one record at a time with
the reader's state threaded by `State.commit`, the compiler's reducibility
hints), and compare every constant the reader emits against a **reference
translation** of the Lean `ConstantInfo` it was compiled from. The reference
is written here from Lean's own data and does not call the reader; the only
bridge between the two sides is the compiled environment's metadata (Lean
name ↦ record address), which the reader never reads.

The drivers are `Tests.Ix.Kernel.ReaderRoundtrip` (`lake test`, the
closure of `Tests.Ix.Kernel.ReaderFidelityDefs`) and `kernel-reader-fidelity`
(`Init` and `Std`: the census corpus or an in-process compile).

## The reference translation

* **Names.** A Lean constant's name is the reader's key of the reference its
  record resolves to: `ix.<hex b>.i` for member `i` of record `b`,
  `ix.<hex b>.i.c` for a constructor (`keyName`), or the pinned name where the
  committed table pins that reference. A recursor is named after what it
  eliminates, by Lean's own convention: `T.rec` ↦ `⟦T⟧.rec`, `T.rec_j` ↦
  `⟦T⟧.rec_j` with `T` the block's first member.
* **Level parameters.** Positional (`levelName i`), except at a reference
  the pin table gives level names to, where they are Lean's own names (the
  table must agree with Lean; a disagreement is reported). A recursor whose
  block has one level fewer is a large eliminator: its parameter `0` is the
  first positional name its block does not use, the rest are the block's.
* **Levels.** Lean's level, with its parameters by position, through
  `Ixon.canonUniv` (the compiler stores every universe level as the
  canonical representative of its semantic class, `Ix/IxonUniv.lean`), then
  with variable `i` named as above.
* **Expressions.** `mdata` is erased (Ixon keeps it as metadata), binder
  names and infos are dropped, every binder's `pw` is `.never` (the reader's
  placeholder; con-leche's annotation computes it), `let`'s `nonDep` flag is
  dropped, literals stay literals, a projection names its structure.
* **Constants.** Axioms, definitions (with Lean's own hint), theorems,
  opaques and quotient constants become the reader's declarations of the
  same kind; an inductive block becomes its members, constructors
  (`numParams`, `numFields`) and recursors (`majorIdx = nP + nM + nm + nI`,
  `rulePrefix = nP + nM + nm`, rules with Lean's constructor and right-hand
  side, the parse placeholders `ctorParams = 0`, `.inert`, `false`s) at the
  block's `numParams`. `partial` and `unsafe` definitions, unsafe opaques,
  axioms and inductives are expected to be declined.

## What is compared

1. **Per constant**, exact structural equality of the reader's entry and the
   reference (con-leche's executed `Expr`, `Level` and `Name` equalities, field
   by field), with the first difference located when there is one.
2. **Names**: the reader's `Ctx.nameOf` of each constant's reference against
   the reference name.
3. **Block order**: each inductive block's members, constructors and
   recursors in Lean's order (`all`, `ctors`, `T.rec`, `T₀.rec_j`).
4. **Shape data the reader computes** (Ixon lacks it): `isRec`,
   `isReflexive`, `numNested`, `nIdx`, `nP` and the recursor counts the reader
   hands the in-process modeller, against Lean's `InductiveVal`/`RecursorVal`.
5. **The pin table**: every pinned name is the Lean name of a constant
   compiled at the pinned reference, and every level-name list is that
   constant's Lean level parameters.
6. **Coverage**: every compiled Lean constant gets a verdict, and every
   constant the reader emits (but the modeller's) has a Lean constant.

## Classification of the differences

No reader defect was found (2026-10-01, `plans/review/cl-fidelity`). Every
difference on the fixture closure and on all of `Init` and `Std` is one of:

* **Intentional normalizations** of the reader:
  - *projection rewrite*: the projection functions of a structure-like
    member of a block that goes through the in-process modeller have their
    value `fun x => x.i` rewritten to recursor form (con-leche's `ProjRec`,
    `ExportC.projRewriteD`). The entry must equal the same rewrite of the
    reference value at the reader's state (`Node.val`, `Node.kids`);
  - *compiler hint (per address)*: the census supplies the compiler's hint
    at the record's address (`Env.anonHints`), which Ix min-merges over the
    alpha-equivalent definitions that share one address; Lean has one hint per
    name. Counted only when everything but the hint is equal, the hint is the
    per-address one, and the address is shared by several Lean constants (74
    on Init and Std: `GT.gt`, `GE.ge`, `id`, …);
  - the modeller's generated records (`Read.generated`) have no Lean
    counterpart; they are counted, not compared.
* **Ixon canonicalizations** of the compiler (`Ix.CompileM`, `Ix.AuxGen`):
  - *auxiliary regenerated*: `Named.original` is set: the compiler
    regenerated the constant in canonical form (the recursors, `recOn`,
    `below`, `brecOn` of a mutual block, whose members it orders
    canonically), so its record is not Lean's term;
  - *call-site surgery*: a call of such an auxiliary was permuted to the
    canonical order (`Ix.Tc.metaHasAlteringSurgery`).
  Both must still agree with the reference on kind, name, level parameters and
  counts (`weakAgree`); Ix.Tc's meta roundtrip skips the same two classes. A
  block whose recursors are regenerated may also be in the compiler's member
  order (counted, not a problem). Neither occurs in `Init` and `Std`.
* **Declines** the reader is expected to make (unsafe and partial constants).
* Anything else is **unexplained** and fails the drivers. -/

open Ix.Kernel (ConstRef)
open Ix.Kernel.IxonReader
open Benchmarks.Kernel.CheckIxeStep (RecordStore Hints setup Setup owner)

namespace Tests.Ix.Kernel.ReaderFidelity

/-! ## Entries -/

/-- A constant as the reader emits it (one of a declaration's constants),
and as the reference translates it. -/
inductive Entry where
  | axiom (cv : CVal)
  | defn (cv : CVal) (value : CExpr) (hint : Ix.Kernel.ReducibilityHint)
  | thm (cv : CVal) (value : CExpr)
  | opaque (cv : CVal) (value : CExpr)
  | quot (kind : Ix.Kernel.QuotKind) (cv : CVal)
  | induct (cv : CVal) (numParams : Nat)
  | ctor (cv : CVal) (numParams numFields : Nat)
  | recr (cv : CVal) (majorIdx rulePrefix : Nat) (rules : List Ix.Kernel.RecRule)
  deriving Inhabited

/-! Equality is decided field by field with con-leche's executed equalities
(`Expr.beq`, `Level.beq`, `Name.beq`: pointer test, cached hash, memoised
descent), not with the derived `DecidableEq`, whose structural descent does
not see sharing and is exponential on the DAGs that both sides build. -/

def CVal.beq (a b : CVal) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type

def RecRule.beq (a b : Ix.Kernel.RecRule) : Bool :=
  a.ctor == b.ctor && a.nfields == b.nfields && a.ctorParams == b.ctorParams &&
    decide (a.fire = b.fire) && a.rhs == b.rhs && a.k == b.k && a.eta == b.eta &&
    a.paramsBlind == b.paramsBlind

def RecRule.listBeq : List Ix.Kernel.RecRule → List Ix.Kernel.RecRule → Bool
  | [], [] => true
  | a :: as, b :: bs => RecRule.beq a b && RecRule.listBeq as bs
  | _, _ => false

def Entry.beq : Entry → Entry → Bool
  | .axiom a, .axiom b => CVal.beq a b
  | .defn a v h, .defn b w k => CVal.beq a b && v == w && decide (h = k)
  | .thm a v, .thm b w | .opaque a v, .opaque b w => CVal.beq a b && v == w
  | .quot k a, .quot l b => decide (k = l) && CVal.beq a b
  | .induct a p, .induct b q => CVal.beq a b && p == q
  | .ctor a p f, .ctor b q g => CVal.beq a b && p == q && f == g
  | .recr a m r rs, .recr b n s ts => CVal.beq a b && m == n && r == s && RecRule.listBeq rs ts
  | _, _ => false

instance : BEq Entry := ⟨Entry.beq⟩

def Entry.cv : Entry → CVal
  | .axiom cv | .defn cv .. | .thm cv _ | .opaque cv _ | .quot _ cv | .induct cv _
  | .ctor cv .. | .recr cv .. => cv

def Entry.name (e : Entry) : CName := e.cv.name

def Entry.kind : Entry → String
  | .axiom .. => "axiom" | .defn .. => "definition" | .thm .. => "theorem"
  | .opaque .. => "opaque" | .quot .. => "quotient" | .induct .. => "inductive"
  | .ctor .. => "constructor" | .recr .. => "recursor"

/-- The constants of a reader declaration. -/
def entriesOf : CDecl → Array Entry
  | .axiomDecl cv => #[.axiom cv]
  | .defnDecl cv v h => #[.defn cv v h]
  | .thmDecl cv v => #[.thm cv v]
  | .opaqueDecl cv v => #[.opaque cv v]
  | .quotDecl k cv => #[.quot k cv]
  | .indDecl block nP => block.toArray.filterMap fun
    | .indInfo cv _ => some (.induct cv nP)
    | .ctorInfo cv p f => some (.ctor cv p f)
    | .recInfo cv m r rules => some (.recr cv m r rules)
    | _ => none
  | .basisDecl _ => #[]

/-! ## The first difference -/

def levelStr (l : CLevel) : String := (reprStr l).take 120 |>.toString

/-- The first position where two expressions differ, with both sides. -/
partial def exprDiff (path : String) (a b : CExpr) : Option String :=
  if a == b then none else
  match a, b with
  | .app f x, .app g y => (exprDiff s!"{path}.fn" f g).orElse fun _ => exprDiff s!"{path}.arg" x y
  | .lam t x m, .lam s y n =>
    if m != n then some s!"{path}: binder annotation {reprStr m.pw} vs {reprStr n.pw}" else
    (exprDiff s!"{path}.lam.type" t s).orElse fun _ => exprDiff s!"{path}.lam.body" x y
  | .forallE t x m, .forallE s y n =>
    if m != n then some s!"{path}: binder annotation {reprStr m.pw} vs {reprStr n.pw}" else
    (exprDiff s!"{path}.pi.type" t s).orElse fun _ => exprDiff s!"{path}.pi.body" x y
  | .letE t v x, .letE s w y =>
    (exprDiff s!"{path}.let.type" t s).orElse fun _ =>
      (exprDiff s!"{path}.let.value" v w).orElse fun _ => exprDiff s!"{path}.let.body" x y
  | .proj n i x, .proj m j y =>
    if n == m && i == j then exprDiff s!"{path}.proj" x y
    else some s!"{path}: proj {n}.{i} vs proj {m}.{j}"
  | .const n us, .const m vs =>
    if n != m then some s!"{path}: const {n} vs const {m}"
    else some s!"{path}: const {n} levels {(reprStr us).take 200} vs {(reprStr vs).take 200}"
  | .sort u, .sort w => some s!"{path}: sort {levelStr u} vs sort {levelStr w}"
  | _, _ => some s!"{path}: {(reprStr a).take 160} vs {(reprStr b).take 160}"

def cvDiff (a b : CVal) : Option String :=
  if a.name != b.name then some s!"name {a.name} vs {b.name}"
  else if a.levelParams != b.levelParams then
    some s!"level parameters {a.levelParams} vs {b.levelParams}"
  else exprDiff "type" a.type b.type

def ruleDiff (i : Nat) (a b : Ix.Kernel.RecRule) : Option String :=
  if a.ctor != b.ctor then some s!"rule {i}: constructor {a.ctor} vs {b.ctor}"
  else if a.nfields != b.nfields then some s!"rule {i}: {a.nfields} fields vs {b.nfields}"
  else if a.rhs != b.rhs then exprDiff s!"rule {i} rhs" a.rhs b.rhs
  else if !RecRule.beq a b then some s!"rule {i}: install placeholders differ"
  else none

/-- The first difference between the reader's entry and the reference: `none`
exactly when the two are equal (a difference the walk does not locate is
still reported). -/
def entryDiff (actual expected : Entry) : Option String :=
  if actual == expected then none else
  Option.orElse (located actual expected) fun _ => some "the entries differ (unlocated)"
where
  located (actual expected : Entry) : Option String :=
  match actual, expected with
  | .axiom a, .axiom b => cvDiff a b
  | .defn a v h, .defn b w k =>
    (cvDiff a b).orElse fun _ => (exprDiff "value" v w).orElse fun _ =>
      if h != k then some s!"hint {reprStr h} vs {reprStr k}" else none
  | .thm a v, .thm b w | .opaque a v, .opaque b w =>
    (cvDiff a b).orElse fun _ => exprDiff "value" v w
  | .quot k a, .quot l b => if k != l then some "quotient kind" else cvDiff a b
  | .induct a p, .induct b q =>
    (cvDiff a b).orElse fun _ => if p != q then some s!"block numParams {p} vs {q}" else none
  | .ctor a p f, .ctor b q g =>
    (cvDiff a b).orElse fun _ =>
      if p != q || f != g then some s!"constructor counts ({p}, {f}) vs ({q}, {g})" else none
  | .recr a m r rs, .recr b n s ts =>
    (cvDiff a b).orElse fun _ =>
      if m != n || r != s then some s!"recursor majorIdx/rulePrefix ({m}, {r}) vs ({n}, {s})"
      else if rs.length != ts.length then some s!"{rs.length} rules vs {ts.length}"
      else ((rs.zip ts).zipIdx.findSome? fun ((x, y), i) => ruleDiff i x y)
  | a, b => some s!"kind {a.kind} vs {b.kind}"

/-! ## The reference translation -/

/-- A Lean name as a con-leche name, component by component. -/
def cname : Lean.Name → CName
  | .anonymous => .anonymous
  | .str p s => .str (cname p) s
  | .num p n => .num (cname p) n

/-- What the reference reads: Lean's constants, the compiled environment's
name ↦ reference map, and the pin table. -/
structure RefCx where
  find : Lean.Name → Option Lean.ConstantInfo
  refOf : Lean.Name → Option (ConstRef Address)
  pins : Pins

abbrev RefM := Except String

/-- A non-recursor constant's reference name. -/
def RefCx.memberName (cx : RefCx) (n : Lean.Name) : RefM CName := do
  let some r := cx.refOf n | throw s!"{n} was not compiled"
  pure (cx.pins.names.getD r (keyName r))

/-- A Lean constant's reference name (recursors by Lean's convention). -/
def RefCx.name (cx : RefCx) (n : Lean.Name) : RefM CName := do
  match cx.find n with
  | some (.recInfo rv) =>
    match n with
    | .str p "rec" =>
      unless rv.all.contains p do throw s!"recursor {n} of no member of its block"
      pure ((← cx.memberName p).str "rec")
    | .str p s =>
      unless s.startsWith "rec_" && rv.all.head? == some p do
        throw s!"recursor {n} has no recursor name"
      pure ((← cx.memberName p).str s)
    | _ => throw s!"recursor {n} has no recursor name"
  | _ => cx.memberName n

/-- Positional level names, or Lean's own where the pin table names the
reference's level parameters. -/
def RefCx.plainLps (cx : RefCx) (n : Lean.Name) (ci : Lean.ConstantInfo) : RefM (List CName) := do
  let some r := cx.refOf n | throw s!"{n} was not compiled"
  let k := ci.levelParams.length
  pure <| match cx.pins.levels[r]? with
    | some ns => if ns.length == k then ci.levelParams.map cname else levelNames k
    | none => levelNames k

/-- A constant's level-parameter names. -/
def RefCx.lps (cx : RefCx) (n : Lean.Name) (ci : Lean.ConstantInfo) : RefM (List CName) := do
  match ci with
  | .ctorInfo cv =>
    let some ind := cx.find cv.induct | throw s!"{n}: inductive {cv.induct} is missing"
    cx.plainLps cv.induct ind
  | .recInfo rv =>
    let some r := cx.refOf n | throw s!"{n} was not compiled"
    if let some ns := cx.pins.levels[r]? then
      if ns.length == ci.levelParams.length then return ci.levelParams.map cname
    let some first := rv.all.head? | throw s!"{n}: recursor of an empty block"
    let some ind := cx.find first | throw s!"{n}: inductive {first} is missing"
    let blockLps ← cx.plainLps first ind
    let k := ind.levelParams.length
    if ci.levelParams.length == k + 1 then
      let elim := (List.range (k + 2)).map levelName |>.find? (!blockLps.contains ·)
      pure (elim.getD (levelName (k + 1)) :: blockLps)
    else pure blockLps
  | _ => cx.plainLps n ci

/-- A Lean level with its parameters by position. -/
def toUniv (params : List Lean.Name) : Lean.Level → RefM Ixon.Univ
  | .zero => pure .zero
  | .succ l => do pure (.succ (← toUniv params l))
  | .max a b => do pure (.max (← toUniv params a) (← toUniv params b))
  | .imax a b => do pure (.imax (← toUniv params a) (← toUniv params b))
  | .param n => match params.idxOf? n with
    | some i => pure (.var i.toUInt64)
    | none => throw s!"unknown level parameter {n}"
  | .mvar _ => throw "level metavariable"

/-- An Ixon level as a con-leche level, variable `i` named `lps[i]`. -/
def ofUniv (lps : List CName) : Ixon.Univ → CLevel
  | .zero => .zero
  | .succ u => .succ (ofUniv lps u)
  | .max a b => .max (ofUniv lps a) (ofUniv lps b)
  | .imax a b => .imax (ofUniv lps a) (ofUniv lps b)
  | .var i => .param (lps.getD i.toNat (levelName i.toNat))

/-- The translation state: the name memo is shared by all constants, the
level and expression memos are per constant (they depend on its level
parameters).

The expression memo is keyed by object address (`Ix.CanonM.leanExprPtr`,
as Ix.Tc's reference `CanonM.canonConst` is), not by `Lean.Expr`'s `==`:
`Expr.eqv` caches only pairs of *shared* objects, and the terms of an imported
environment live in `.olean` compacted regions, where no object counts as
shared, so a lookup that meets an alpha-equal key at another address walks the
term as a tree. On `denote_blastDivSubtractShift_q` (6,716 objects, more than
10⁸ tree nodes) that took minutes per probe. The constant's objects outlive
its translation, so an address names one object for the memo's lifetime. -/
structure TrState where
  names : Std.HashMap Lean.Name CName := {}
  levels : Std.HashMap Lean.Level CLevel := {}
  exprs : Std.HashMap USize CExpr := {}

/-- Errors do not discard the state: the memo is threaded uniquely (a
`StateT` over `Except` would keep the state before a failing translation
alive, and every later insertion into the shared name memo would copy it). -/
abbrev TrM := ExceptT String (StateM TrState)

def liftRef (x : RefM α) : TrM α := match x with
  | .ok a => pure a
  | .error e => throw e

structure TrCx where
  ref : RefCx
  params : List Lean.Name
  lps : List CName

def trName (cx : TrCx) (n : Lean.Name) : TrM CName := do
  if let some c ← modifyGet (fun s => (s.names[n]?, s)) then return c
  let c ← liftRef (cx.ref.name n)
  modify fun s => { s with names := s.names.insert n c }
  return c

def trLevel (cx : TrCx) (l : Lean.Level) : TrM CLevel := do
  if let some c ← modifyGet (fun s => (s.levels[l]?, s)) then return c
  let u ← liftRef (toUniv cx.params l)
  let c := ofUniv cx.lps (Ixon.canonUniv u)
  modify fun s => { s with levels := s.levels.insert l c }
  return c

def never : Ix.Kernel.BinderMeta := ⟨.never⟩

partial def trExpr (cx : TrCx) (e : Lean.Expr) : TrM CExpr := do
  let p := _root_.Ix.CanonM.leanExprPtr e
  if let some c ← modifyGet (fun s => (s.exprs[p]?, s)) then return c
  let c ← match e with
    | .bvar i => pure (Ix.Kernel.Expr.mkBvar i)
    | .sort u => do pure (.sort (← trLevel cx u))
    | .const n us => do pure (.const (← trName cx n) (← us.mapM (trLevel cx)))
    | .app f a => do pure (.app (← trExpr cx f) (← trExpr cx a))
    | .lam _ t b _ => do pure (.lam (← trExpr cx t) (← trExpr cx b) never)
    | .forallE _ t b _ => do pure (.forallE (← trExpr cx t) (← trExpr cx b) never)
    | .letE _ t v b _ => do pure (.letE (← trExpr cx t) (← trExpr cx v) (← trExpr cx b))
    | .lit (.natVal n) => pure (.lit (.natVal n))
    | .lit (.strVal s) => pure (.lit (.strVal s))
    | .mdata _ x => trExpr cx x
    | .proj s i x => do pure (.proj (← trName cx s) i (← trExpr cx x))
    | .fvar _ => throw "free variable"
    | .mvar _ => throw "metavariable"
  modify fun s => { s with exprs := s.exprs.insert p c }
  return c

def hintOf : Lean.ReducibilityHints → Ix.Kernel.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

def quotKind : Lean.QuotKind → Ix.Kernel.QuotKind
  | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind

/-- Why the reader is expected to decline a constant, if it is. -/
def expectedDecline : Lean.ConstantInfo → Option String
  | .defnInfo v => match v.safety with
    | .unsafe => some "unsafe definition"
    | .partial => some "partial definition"
    | .safe => none
  | .opaqueInfo v => if v.isUnsafe then some "unsafe opaque" else none
  | .axiomInfo v => if v.isUnsafe then some "unsafe axiom" else none
  | .inductInfo v => if v.isUnsafe then some "unsafe inductive" else none
  | .ctorInfo v => if v.isUnsafe then some "unsafe inductive" else none
  | .recInfo v => if v.isUnsafe then some "unsafe inductive" else none
  | _ => none

/-- The reference entry of a Lean constant. -/
def reference (rcx : RefCx) (n : Lean.Name) (ci : Lean.ConstantInfo) : TrM Entry := do
  let lps ← liftRef (rcx.lps n ci)
  let cx : TrCx := ⟨rcx, ci.levelParams, lps⟩
  -- level and expression memos are per constant; the expression memo is keyed
  -- by object, so the constant is hash-consed first and each distinct subterm
  -- is translated once
  let ci := ShareCommon.shareCommon' ci
  modify fun s => { s with levels := {}, exprs := {} }
  let cv : CVal := ⟨← trName cx n, lps, ← trExpr cx ci.type⟩
  match ci with
  | .axiomInfo _ => pure (.axiom cv)
  | .defnInfo v => pure (.defn cv (← trExpr cx v.value) (hintOf v.hints))
  | .thmInfo v => pure (.thm cv (← trExpr cx v.value))
  | .opaqueInfo v => pure (.opaque cv (← trExpr cx v.value))
  | .quotInfo v => pure (.quot (quotKind v.kind) cv)
  | .inductInfo v => pure (.induct cv v.numParams)
  | .ctorInfo v => pure (.ctor cv v.numParams v.numFields)
  | .recInfo v =>
    let rules ← v.rules.mapM fun r => do
      pure (Ix.Kernel.RecRule.mk (← trName cx r.ctor) r.nfields 0 .inert (← trExpr cx r.rhs)
        false false false)
    pure (.recr cv (v.numParams + v.numMotives + v.numMinors + v.numIndices)
      (v.numParams + v.numMotives + v.numMinors) rules)

/-! ## The report -/

/-- How a constant compared. -/
inductive Verdict where
  | equal
  /-- an intentional normalization of the reader -/
  | normalized (kind : String)
  /-- one of the compiler's canonicalizations -/
  | canonicalized (kind : String)
  /-- an expected decline -/
  | declined (reason : String)
  | unexplained (detail : String)
  deriving Inhabited, BEq

def Verdict.label : Verdict → String
  | .equal => "equal"
  | .normalized k => s!"normalized: {k}"
  | .canonicalized k => s!"canonicalized: {k}"
  | .declined r => s!"declined: {r}"
  | .unexplained _ => "unexplained"

structure Report where
  /-- records read, records the reader failed -/
  records : Nat := 0
  readFailures : Nat := 0
  /-- Lean constants compared, and the count per verdict label -/
  constants : Nat := 0
  counts : Std.HashMap String Nat := {}
  /-- the modeller's generated declarations, and the projection rewrites the reader applied -/
  projRewrites : Nat := 0
  generated : Nat := 0
  /-- reader constants of records whose metadata names constants outside the
  Lean environment (the compiled source's own declarations: informational, as
  Ix.Tc's `notFound`) -/
  foreign : Nat := 0
  /-- regenerated auxiliaries whose reader name differs from the Lean convention -/
  renamedAux : Nat := 0
  /-- inductive blocks whose member order is the compiler's canonical one (their
  recursors regenerated), not Lean's -/
  reorderedBlocks : Array Lean.Name := #[]
  /-- reader constants no Lean constant translates to -/
  unmatched : Array CName := #[]
  /-- names, shape data and pin-table checks: problems found -/
  problems : Array String := #[]
  /-- unexplained differences, with the Lean name -/
  unexplained : Array (Lean.Name × String) := #[]
  /-- per Lean name: the verdict, for the tests that pin particular constants -/
  verdicts : Std.HashMap Lean.Name Verdict := {}
  /-- per kept Lean name: the reader's entry and the reference (for the tamper tests) -/
  pairs : Std.HashMap Lean.Name (Entry × Entry) := {}
  /-- up to ten Lean names per verdict label other than `equal` -/
  examples : Std.HashMap String (Array Lean.Name) := {}
  readMs : Nat := 0
  /-- records whose comparison took longer than 200 ms -/
  slow : Array (String × Nat) := #[]
  compareMs : Nat := 0

def Report.count (r : Report) (label : String) : Nat := r.counts.getD label 0

def Report.bump (r : Report) (n : Lean.Name) (v : Verdict) (keep : Bool) : Report :=
  let r := { r with constants := r.constants + 1,
                    counts := r.counts.insert v.label (r.count v.label + 1) }
  let r := if keep then { r with verdicts := r.verdicts.insert n v } else r
  let ex := r.examples.getD v.label #[]
  let r := if v != .equal && ex.size < 10 then { r with examples := r.examples.insert v.label (ex.push n) } else r
  match v with
  | .unexplained d => { r with unexplained := r.unexplained.push (n, d) }
  | _ => r

def Report.problem (r : Report) (p : String) : Report :=
  { r with problems := r.problems.push p }

/-- The report as text: counts, problems, the first unexplained. -/
def Report.summary (r : Report) (shown : Nat := 25) : String := Id.run do
  let mut lines : Array String := #[
    s!"records read: {r.records} ({r.readFailures} declined or malformed by the reader); \
      generated declarations: {r.generated}; projection rewrites: {r.projRewrites}; \
      read {r.readMs} ms, compared {r.compareMs} ms",
    s!"Lean constants compared: {r.constants}"]
  for (label, n) in r.counts.toArray.qsort (fun a b => a.1 < b.1) do
    lines := lines.push s!"  {n}\t{label}"
    for ex in (r.examples.getD label #[]) do lines := lines.push s!"      {ex}"
  lines := lines.push s!"reader constants of records outside the Lean environment: {r.foreign}"
  lines := lines.push s!"regenerated auxiliaries named off the Lean convention: {r.renamedAux}"
  lines := lines.push s!"inductive blocks in the compiler's canonical member order: {r.reorderedBlocks.size} {r.reorderedBlocks.extract 0 shown}"
  lines := lines.push s!"reader constants without a Lean constant: {r.unmatched.size}"
  for n in r.unmatched.extract 0 shown do lines := lines.push s!"  {n}"
  lines := lines.push s!"problems: {r.problems.size}"
  for p in r.problems.extract 0 shown do lines := lines.push s!"  {p}"
  lines := lines.push s!"slow comparisons: {r.slow.size}"
  for (a, ms) in (r.slow.qsort (fun x y => x.2 > y.2)).extract 0 shown do lines := lines.push s!"  {a} {ms} ms"
  lines := lines.push s!"unexplained: {r.unexplained.size}"
  for (n, d) in r.unexplained.extract 0 shown do lines := lines.push s!"  {n}: {d}"
  return "\n".intercalate lines.toList

/-! ## The run -/

/-- The compared environment: Lean's constants and the compiled records. -/
structure Input where
  lean : Lean.Name → Option Lean.ConstantInfo
  /-- the Lean names to compare (those with a compiled record) -/
  names : Array Lean.Name
  ixon : Ixon.Env
  store : RecordStore
  /-- records whose metadata names a constant outside the Lean environment -/
  foreign : Array Address := #[]

/-- The compiler's synthetic name of a `muts` block, `Ix.<hex address>.…`. -/
def isBlockName (n : Lean.Name) : Bool :=
  match n.components with
  | `Ix :: .str .anonymous h :: _ => h.length == 64 && h.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')
  | _ => false

/-- Decode every record of a compiled environment; the Lean names to compare
are the Lean constants the environment's metadata names. -/
def Input.ofEnv (lean : Lean.Environment) (ixon : Ixon.Env) : IO Input := do
  let mut store : RecordStore := {}
  for (address, lazy) in ixon.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let names := lean.constants.toList.toArray.filterMap fun (n, _) =>
    if ixon.named.contains (_root_.Ix.Name.fromLeanName n) then some n else none
  let foreign := ixon.named.toArray.filterMap fun (n, nd) =>
    let ln := _root_.Ix.SemanticContract.toLeanName n
    if lean.contains ln || isBlockName ln then none else some nd.addr
  return { lean := lean.find?, names, ixon, store, foreign }

/-! ## The closure of seeds -/

/-- The constants a declaration names, including an inductive's
constructors, block and recursors (every recursor of the block, the
auxiliary ones of a nested block included) and a recursor's block and rule
right-hand sides (as `kernel-entry-cases`: the reader declines a block whose
recursor is not in the input). -/
def references (env : Lean.Environment) (ci : Lean.ConstantInfo) : Array Lean.Name := Id.run do
  let mut out : Array Lean.Name := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => out := out ++ v.value.getUsedConstants
  | .thmInfo v => out := out ++ v.value.getUsedConstants
  | .opaqueInfo v => out := out ++ v.value.getUsedConstants
  | .inductInfo v =>
    out := out ++ v.ctors.toArray ++ v.all.toArray
    for t in v.all do out := out.push (t ++ `rec)
    if let some first := v.all.head? then
      for i in [1:v.numNested + 1] do
        out := out.push (first.str s!"rec_{i}")
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v =>
    out := out ++ v.all.toArray
    for rule in v.rules do out := out ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return out.filter (env.contains ·)

/-- The seeds and everything they reach. -/
def closure (env : Lean.Environment) (seeds : Array Lean.Name) :
    Except String (List (Lean.Name × Lean.ConstantInfo)) := do
  let mut seen : Lean.NameSet := {}
  let mut todo := seeds
  let mut out : Array (Lean.Name × Lean.ConstantInfo) := #[]
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throw s!"missing declaration {n}"
    out := out.push (n, ci)
    todo := todo ++ references env ci
  return out.toList

/-- The pin table's agreement with Lean: a pinned name is a Lean name
compiled at its reference, and a level list is that constant's levels. -/
def pinProblems (pins : Pins) (find : Lean.Name → Option Lean.ConstantInfo)
    (byRef : Std.HashMap (ConstRef Address) (Array Lean.Name)) : Array String := Id.run do
  let mut out := #[]
  for (r, n) in pins.names.toList do
    let leans := byRef.getD r #[]
    unless leans.isEmpty || leans.any (cname · == n) do
      out := out.push s!"pin {n} is not the Lean name of a constant at its reference \
        (there: {leans.toList.take 4})"
  for (r, ns) in pins.levels.toList do
    for ln in byRef.getD r #[] do
      if let some ci := find ln then
        unless ci.levelParams.map cname == ns do
          out := out.push s!"pinned level names of {ln}: {ns} vs Lean's {ci.levelParams}"
  return out

/-- What the comparison of one record reads besides the record. -/
structure Cx where
  input : Input
  rcx : RefCx
  named : Std.HashMap Lean.Name Ixon.Named
  byName : Std.HashMap CName (Array Lean.Name)
  /-- record owners whose metadata names constants outside the Lean
  environment (the compiled source's own declarations) -/
  foreign : Std.HashSet Address
  keep : Lean.Name → Bool
  /-- the host hint the census supplies at a Lean constant's reference -/
  advisory : Lean.Name → Option Ix.Kernel.ReducibilityHint
  /-- how many Lean constants share a Lean constant's reference -/
  aliases : Lean.Name → Nat

/-- What a canonicalized constant must still agree on: its kind, name and
level parameters, an inductive's parameter count, a constructor's counts,
and a recursor's argument counts and the set of its rules' constructors (the
compiler's canonical member order permutes motives, minors and rules). -/
def weakAgree (a e : Entry) : Bool :=
  a.kind == e.kind && a.name == e.name && a.cv.levelParams == e.cv.levelParams &&
  match a, e with
  | .induct _ p, .induct _ q => p == q
  | .ctor _ p f, .ctor _ q g => p == q && f == g
  | .recr _ m r rs, .recr _ n s ts =>
    m == n && r == s && rs.length == ts.length &&
      rs.all (fun x => ts.any (·.ctor == x.ctor)) && ts.all (fun y => rs.any (·.ctor == y.ctor))
  | _, _ => true

/-- The verdict on one Lean constant against the reader's entry, at the
reader's state before the record. -/
def judge (cx : Cx) (st : State) (n : Lean.Name) (actual : Entry) (expected : RefM Entry) : Verdict :=
  match expected with
  | .error e => .unexplained s!"reference: {e}"
  | .ok expected =>
    match entryDiff actual expected with
    | none => .equal
    | some diff =>
      -- the projection rewrite at the reader's state
      let rewritten : Option Entry := match expected with
        | .defn cv v h => (projRewrite st cv v).map (.defn cv · h)
        | .thm cv v => (projRewrite st cv v).map (.thm cv ·)
        | _ => none
      if rewritten.isSome && (rewritten.bind (entryDiff actual ·)).isNone then
        .normalized "projection rewrite"
      else
        let hintOnly := match actual, rewritten.getD expected with
          | .defn a v _, .defn b w _ => CVal.beq a b && v == w
          | _, _ => false
        let actualHint := match actual with | .defn _ _ h => some h | _ => none
        let nd := cx.named[n]?
        if hintOnly then
          -- the census supplies the compiler's per-address hint, which Ix
          -- min-merges over the alpha-equivalent definitions at one address
          if actualHint == cx.advisory n && cx.aliases n > 1 then .normalized "compiler hint (per address)"
          else .unexplained s!"{diff} (the reader's hint is not the per-address hint of an alias set)"
        else
          let canon? : Option String :=
            if (nd.map (·.original.isSome)).getD false then some "auxiliary regenerated"
            else if (nd.map (_root_.Ix.Tc.metaHasAlteringSurgery ·.constMeta)).getD false then
              some "call-site surgery"
            else none
          match canon? with
          | some k =>
            -- the record is not Lean's term, but it is the same constant
            if weakAgree actual expected then .canonicalized k
            else .unexplained s!"{diff} ({k}, and the kind, level parameters or counts differ)"
          | none => .unexplained diff

/-- Compare one record's reading: every constant it emits (not the
modeller's generated ones) against each Lean constant that translates to its
name, and the shape data it hands the modeller against Lean's. -/
def compareRecord (cx : Cx) (st : State) (address : Address) (rd : Read)
    (acc : Report × TrState × Std.HashSet CName) : Report × TrState × Std.HashSet CName := Id.run do
  let (report0, tr0, seen0) := acc
  let mut report := report0
  let mut tr := tr0
  let mut seen := seen0
  for (d, i) in rd.decls.zipIdx do
    if i < rd.generated then continue
    for actual in entriesOf d do
      let leans := cx.byName.getD actual.name #[]
      if leans.isEmpty then
        if cx.foreign.contains address then
          report := { report with foreign := report.foreign + 1 }
        else
          report := { report with unmatched := report.unmatched.push actual.name }
        continue
      seen := seen.insert actual.name
      for n in leans do
        let some ci := cx.input.lean n | continue
        let (expected, tr') := ((reference cx.rcx n ci).run).run tr
        tr := tr'
        report := report.bump n (judge cx st n actual expected) (cx.keep n)
        if cx.keep n then
          if let .ok e := expected then report := { report with pairs := report.pairs.insert n (actual, e) }
  -- the order of each inductive block's constants: members, then their
  -- constructors, then the recursors, all in Lean's order (`all`, `ctors`,
  -- `T.rec` per member and `T₀.rec_j` per nested auxiliary)
  for d in rd.decls do
    let .indDecl block _ := d | continue
    let actualNames := block.map (·.toConstantVal.name)
    let some first := block.head? | continue
    let some ln := (cx.byName.getD first.toConstantVal.name #[])[0]? | continue
    let some (.inductInfo iv) := cx.input.lean ln | continue
    let leanOrder : List Lean.Name := Id.run do
      let mut ctors : List Lean.Name := []
      for t in iv.all do
        if let some (.inductInfo tv) := cx.input.lean t then ctors := ctors ++ tv.ctors
      let recs := iv.all.map (· ++ `rec) ++
        ((List.range iv.numNested).filterMap fun j => iv.all.head?.map (·.str s!"rec_{j + 1}"))
      return iv.all ++ ctors ++ recs
    let expectedNames := leanOrder.filterMap fun n => (cx.rcx.name n).toOption
    unless actualNames == expectedNames do
      let regenerated := leanOrder.any fun n => ((cx.named[n]?).map (·.original.isSome)).getD false
      if regenerated && actualNames.length == expectedNames.length &&
          actualNames.all expectedNames.contains then
        report := { report with reorderedBlocks := report.reorderedBlocks.push ln }
      else
        report := report.problem s!"block order of {ln}: reader {actualNames.take 6}…, \
          Lean {expectedNames.take 6}…"
  -- the shape data the reader computed for the modeller (one block per record)
  if let some (_, b) := rd.blocks.head? then
    for t in b.types do
      let some ln := (cx.byName.getD t.cv.name #[])[0]? | continue
      let some (.inductInfo iv) := cx.input.lean ln | continue
      unless t.isRec == iv.isRec && t.isReflexive == iv.isReflexive &&
          t.numNested == iv.numNested && t.nIdx == iv.numIndices && t.nP == iv.numParams do
        report := report.problem s!"shape of {ln}: reader isRec {t.isRec}, isReflexive \
          {t.isReflexive}, numNested {t.numNested}, nIdx {t.nIdx}, nP {t.nP}; Lean {iv.isRec}, \
          {iv.isReflexive}, {iv.numNested}, {iv.numIndices}, {iv.numParams}"
    for rr in b.recs do
      let some ln := (cx.byName.getD rr.cv.name #[])[0]? | continue
      let some (.recInfo rv) := cx.input.lean ln | continue
      unless rr.nP == rv.numParams && rr.nM == rv.numMotives && rr.nm == rv.numMinors &&
          rr.nI == rv.numIndices do
        report := report.problem s!"recursor counts of {ln}: reader ({rr.nP}, {rr.nM}, {rr.nm}, \
          {rr.nI}), Lean ({rv.numParams}, {rv.numMotives}, {rv.numMinors}, {rv.numIndices})"
  return (report, tr, seen)

/-- Compare the reader's reading of the compiled records with the reference
translation of the Lean constants. `limit` bounds the records read (in the
census order); `keep` decides which verdicts are kept by name; `roots`
restricts the run to the prelude and the closure of those records. -/
def run (input : Input) (limit : Option Nat := none) (keep : Lean.Name → Bool := fun _ => false)
    (roots : Option (Array Address) := none) :
    IO Report := do
  let t0 ← IO.monoMsNow
  let pins ← IO.ofExcept defaultPins
  let pre ← IO.ofExcept builtinPrelude
  let hints := Hints.ofStore input.store input.ixon.anonHints
  let s : Setup := setup input.store (input.ixon.blobs[·]?) pins pre hints.lookup
  let store := s.store
  -- the bridge: Lean name ↦ reference, from the compiled metadata
  let mut refs : Std.HashMap Lean.Name (ConstRef Address) := {}
  let mut named : Std.HashMap Lean.Name Ixon.Named := {}
  for n in input.names do
    if let some nd := input.ixon.named[_root_.Ix.Name.fromLeanName n]? then
      named := named.insert n nd
      if let some r := resolve (store[·]?) nd.addr then refs := refs.insert n r
  let rcx : RefCx := { find := input.lean, refOf := (refs[·]?), pins }
  let mut report : Report := {}
  -- reference names, the inverse map, and the reader's own names
  let mut byName : Std.HashMap CName (Array Lean.Name) := {}
  let mut byRef : Std.HashMap (ConstRef Address) (Array Lean.Name) := {}
  for n in input.names do
    let some r := refs[n]? | continue
    byRef := byRef.insert r ((byRef.getD r #[]).push n)
    match rcx.name n with
    | .ok c =>
      byName := byName.insert c ((byName.getD c #[]).push n)
      let actual := s.cx.nameOf r
      if actual != c then
        if (named[n]?.map (·.original.isSome)).getD false then
          report := { report with renamedAux := report.renamedAux + 1 }
        else
          report := report.problem s!"name of {n}: reader {actual}, reference {c}"
    | .error e => report := report.problem s!"name of {n}: {e}"
  for p in pinProblems pins input.lean byRef do report := report.problem p
  let foreign : Std.HashSet Address := input.foreign.foldl (fun acc a =>
    match store[a]? with
    | some c => acc.insert (owner a c)
    | none => acc) {}
  let advisory (n : Lean.Name) : Option Ix.Kernel.ReducibilityHint := (refs[n]?).bind s.cx.hint
  let aliases (n : Lean.Name) : Nat := ((refs[n]?).map fun r => (byRef.getD r #[]).size).getD 0
  let cx : Cx := { input, rcx, named, byName, foreign, keep, advisory, aliases }
  -- read in the census order, comparing each record's constants at the
  -- reader's state before it
  let base := match roots with
    | some rs => Benchmarks.Kernel.CheckIxeStep.closure store s.extra (pre.records.map (fun (p : Address × Ixon.Constant) => p.1) ++ rs)
    | none => s.ordered
  let ordered := match limit with | some k => base.extract 0 k | none => base
  let mut st : State := {}
  let mut acc : Report × TrState × Std.HashSet CName := (report, {}, {})
  let mut readNs := 0
  let mut failed : Std.HashMap Address String := {}
  for address in ordered do
    let some source := store[address]? | continue
    let r0 ← IO.monoNanosNow
    let reading ← IO.lazyPure fun _ => readRecord s.cx st address source
    readNs := readNs + ((← IO.monoNanosNow) - r0)
    match reading with
    | .error e =>
      acc := ({ acc.1 with records := acc.1.records + 1, readFailures := acc.1.readFailures + 1 },
        acc.2)
      failed := failed.insert address (toString e)
    | .ok rd =>
      acc := ({ acc.1 with records := acc.1.records + 1, generated := acc.1.generated + rd.generated,
                           projRewrites := acc.1.projRewrites + rd.projRewrites }, acc.2)
      let c0 ← IO.monoNanosNow
      acc ← IO.lazyPure fun _ => compareRecord cx st address rd acc
      let dt := ((← IO.monoNanosNow) - c0) / 1000000
      if dt > 200 then
        let label := ((rd.decls.findSome? fun d => (entriesOf d)[0]?).bind fun e =>
          (byName.getD e.name #[])[0]?).map toString |>.getD (toString address)
        acc := ({ acc.1 with slow := acc.1.slow.push (label, dt) }, acc.2)
      st := st.commit rd
  let (report', _, seen) := acc
  report := report'
  -- Lean constants no reader entry matched: an expected decline, a failed
  -- record, or outside the limit
  let readOwners : Std.HashSet Address := ordered.foldl (·.insert ·) {}
  for n in input.names do
    let some r := refs[n]? | continue
    let some c := (rcx.name n).toOption | continue
    if seen.contains c then continue
    let some ci := input.lean n | continue
    let some rec := store[r.block]? | continue
    -- a recursor record is read with its block; a projection's owner is its block
    let ownerAddr := owner r.block rec
    let blockAddr : Address := match ci with
      | .recInfo rv => match rv.all.head?.bind (refs[·]?) with
        | some br => br.block
        | none => ownerAddr
      | _ => ownerAddr
    unless readOwners.contains blockAddr || readOwners.contains ownerAddr do continue
    let why := (failed[blockAddr]?).orElse fun _ => failed[ownerAddr]?
    let verdict : Verdict := match expectedDecline ci, why with
      | some reason, some _ => .declined reason
      | some reason, none => .unexplained s!"expected to decline ({reason}) but no reading of it"
      | none, some e => .unexplained s!"reader: {e}"
      | none, none => .unexplained "no reader entry"
    report := report.bump n verdict (keep n)
  let t1 ← IO.monoMsNow
  return { report with readMs := readNs / 1000000, compareMs := t1 - t0 - readNs / 1000000 }

end Tests.Ix.Kernel.ReaderFidelity
