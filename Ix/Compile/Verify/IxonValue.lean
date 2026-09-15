import Ix.Ixon
import Ix.Theory.Expr
import Ix.Theory.Model.Environment
import Ix.Compile.Verify.StdLemmas
import Ix.Compile.Verify.StringLiteral

open Ix.Theory (VLevel VExpr ConstRef)

/-!
# Ixon v2 expressions and set-model values

This is the first compiler-facing semantic boundary.  It interprets an Ixon
expression directly as a set-model `Ix.Theory.VExpr Address`; it does not run
Ix.Kernel and does not use checker acceptance as a specification.

The reading follows the conventions of the consistency reader
`Ix.Kernel.Consistency.readExpr?`: constants resolve by content address to a
block reference `ConstRef Address`, projections keep their structure reference
and field index, natural-number literals are native, a let is read by
substitution, and a string literal is the constructor expansion of
`StringRefs.stringLiteral`.  Constant occurrences additionally require an
entry in the set-model environment index with matching universe arity; this
is the only use of the environment, so the relation is monotone in it.

The relation is table-aware.  It resolves universe, reference, mutual-member,
sharing, and literal indices against an explicit immutable context.  A cyclic
sharing table has no finite derivation.  Lambda usage and forall
usage/ownership are intentionally absent from the semantic premises: ordinary
Lean compilation inhabits `.many`/`.shared`, while v2 annotations remain
available to later substructural passes without changing the Lean meaning.

The former named-specification relation carried a local context and a
declaration-supplied projection relation `trProj uvars locals name field val
out` because that syntax had no projection constructor.  The set-model syntax
has `VExpr.proj`, so the local context, universe count, and projection
parameter are gone: downstream theorems that only threaded them through can
drop those indices.
-/

namespace Ix.Compile.Verify

/-- Immutable semantic views needed to interpret an Ixon expression. -/
structure Catalog where
  /-- Resolve a content address to its set-model block reference. -/
  resolve : Address → Option (ConstRef Address)
  /-- Resolve literal content addresses to their committed bytes. -/
  blobs : Address → Option ByteArray
  /-- Resolve canonical constant payloads.  This stored view is deliberately
  separate from `resolve`: content integrity and semantic reference are
  distinct obligations. -/
  constants : Address → Option Ixon.Constant := fun _ => none
  /-- Resolve source-facing named registrations. -/
  named : Ix.Name → Option Ixon.Named := fun _ => none
  /-- Resolve content-addressed name components used by metadata. -/
  names : Address → Option Ix.Name := fun _ => none
  /-- Anonymous reducibility hints are operational input, not constant
  payload. -/
  anonHints : Address → Option Lean.ReducibilityHints := fun _ => none
  /-- Semantic addresses of members of a mutual block.  Projection constants
  remain ordinary entries in `constants`; this table supplies the positional
  context used by `.recur`. -/
  memberAddrs : Address → Option (Array Address) := fun _ => none

/-- The tables against which one constant's Ixon expressions are read. -/
structure DecodeCtx where
  refs : Array Address := #[]
  univs : Array Ixon.Univ := #[]
  sharing : Array Ixon.Expr := #[]
  /-- Semantic addresses of the current mutual block's members. -/
  mutAddrs : Array Address := #[]

/-- Structural interpretation of positional Ixon universes. -/
def univToVLevel : Ixon.Univ → VLevel
  | .zero => .zero
  | .succ u => .succ (univToVLevel u)
  | .max a b => .max (univToVLevel a) (univToVLevel b)
  | .imax a b => .imax (univToVLevel a) (univToVLevel b)
  | .var idx => .param idx.toNat

/-- Resolve one universe-table index. -/
def DecodeCtx.univ? (ctx : DecodeCtx) (idx : UInt64) : Option VLevel :=
  ctx.univs[idx.toNat]?.map univToVLevel

/-- Resolve an expression's universe argument vector in source order. -/
def DecodeCtx.univArgs? (ctx : DecodeCtx) (idxs : Array UInt64) :
    Option (List VLevel) :=
  idxs.toList.mapM ctx.univ?

/-- Direct semantic relation from table-indexed Ixon syntax to set-model
syntax.  This is a raw representation relation: typing and source-kernel
well-formedness are separate obligations. -/
inductive IxonExprRel (entries : Ix.Theory.Model.Environment Address)
    (catalog : Catalog) (dctx : DecodeCtx) (strings : StringRefs Address) :
    Ixon.Expr → VExpr Address → Prop where
  | var {idx : UInt64} :
    IxonExprRel entries catalog dctx strings (.var idx) (.bvar idx.toNat)
  | sort {idx : UInt64} {u : VLevel} :
    dctx.univ? idx = some u →
    IxonExprRel entries catalog dctx strings (.sort idx) (.sort u)
  | ref {refIdx : UInt64} {univIdxs : Array UInt64} {addr : Address}
      {ref : ConstRef Address} {entry : Ix.Theory.Model.ConstantEntry Address}
      {us : List VLevel} :
    dctx.refs[refIdx.toNat]? = some addr →
    catalog.resolve addr = some ref →
    entries ref = some entry →
    dctx.univArgs? univIdxs = some us →
    us.length = entry.universes →
    IxonExprRel entries catalog dctx strings (.ref refIdx univIdxs)
      (.const ref us)
  | recur {recIdx : UInt64} {univIdxs : Array UInt64} {addr : Address}
      {ref : ConstRef Address} {entry : Ix.Theory.Model.ConstantEntry Address}
      {us : List VLevel} :
    dctx.mutAddrs[recIdx.toNat]? = some addr →
    catalog.resolve addr = some ref →
    entries ref = some entry →
    dctx.univArgs? univIdxs = some us →
    us.length = entry.universes →
    IxonExprRel entries catalog dctx strings (.recur recIdx univIdxs)
      (.const ref us)
  | app {fn arg : Ixon.Expr} {fn' arg' : VExpr Address} :
    IxonExprRel entries catalog dctx strings fn fn' →
    IxonExprRel entries catalog dctx strings arg arg' →
    IxonExprRel entries catalog dctx strings (.app fn arg) (.app fn' arg')
  | lam {uses : Ixon.Uses} {ty body : Ixon.Expr} {ty' body' : VExpr Address} :
    IxonExprRel entries catalog dctx strings ty ty' →
    IxonExprRel entries catalog dctx strings body body' →
    IxonExprRel entries catalog dctx strings (.lam uses ty body)
      (.lam ty' body')
  | all {uses : Ixon.Uses} {owned : Ixon.Owned} {ty body : Ixon.Expr}
      {ty' body' : VExpr Address} :
    IxonExprRel entries catalog dctx strings ty ty' →
    IxonExprRel entries catalog dctx strings body body' →
    IxonExprRel entries catalog dctx strings (.all uses owned ty body)
      (.forallE ty' body')
  | letE {nonDep : Bool} {ty val body : Ixon.Expr}
      {ty' val' body' : VExpr Address} :
    IxonExprRel entries catalog dctx strings ty ty' →
    IxonExprRel entries catalog dctx strings val val' →
    IxonExprRel entries catalog dctx strings body body' →
    IxonExprRel entries catalog dctx strings (.letE nonDep ty val body)
      (body'.inst val')
  | prj {typeRefIdx field : UInt64} {val : Ixon.Expr} {addr : Address}
      {ref : ConstRef Address} {entry : Ix.Theory.Model.ConstantEntry Address}
      {val' : VExpr Address} :
    dctx.refs[typeRefIdx.toNat]? = some addr →
    catalog.resolve addr = some ref →
    entries ref = some entry →
    IxonExprRel entries catalog dctx strings val val' →
    IxonExprRel entries catalog dctx strings (.prj typeRefIdx field val)
      (.proj ref field.toNat val')
  | nat {refIdx : UInt64} {addr : Address} {bytes : ByteArray} :
    dctx.refs[refIdx.toNat]? = some addr →
    catalog.blobs addr = some bytes →
    IxonExprRel entries catalog dctx strings (.nat refIdx)
      (.natLit (Nat.fromBytesLE bytes.data))
  | str {refIdx : UInt64} {addr : Address} {bytes : ByteArray}
      {value : String} :
    dctx.refs[refIdx.toNat]? = some addr →
    catalog.blobs addr = some bytes →
    String.fromUTF8? bytes = some value →
    IxonExprRel entries catalog dctx strings (.str refIdx)
      (strings.stringLiteral value)
  | share {idx : UInt64} {expansion : Ixon.Expr} {value : VExpr Address} :
    dctx.sharing[idx.toNat]? = some expansion →
    IxonExprRel entries catalog dctx strings expansion value →
    IxonExprRel entries catalog dctx strings (.share idx) value

namespace IxonExprRel

/-- The representation relation is monotone in the set-model environment
index; only resolved entry witnesses are transported. -/
theorem mono {entries entries' : Ix.Theory.Model.Environment Address}
    (henv : ∀ r e, entries r = some e → entries' r = some e)
    {catalog : Catalog} {dctx : DecodeCtx} {strings : StringRefs Address}
    {expr : Ixon.Expr} {value : VExpr Address}
    (h : IxonExprRel entries catalog dctx strings expr value) :
    IxonExprRel entries' catalog dctx strings expr value := by
  induction h with
  | var => exact .var
  | sort hidx => exact .sort hidx
  | ref href hres hentry hunivs harity =>
    exact .ref href hres (henv _ _ hentry) hunivs harity
  | recur href hres hentry hunivs harity =>
    exact .recur href hres (henv _ _ hentry) hunivs harity
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | lam _ _ ihty ihbody => exact .lam ihty ihbody
  | all _ _ ihty ihbody => exact .all ihty ihbody
  | letE _ _ _ ihty ihval ihbody => exact .letE ihty ihval ihbody
  | prj href hres hentry _ ihval =>
    exact .prj href hres (henv _ _ hentry) ihval
  | nat href hblob => exact .nat href hblob
  | str href hblob hutf8 => exact .str href hblob hutf8
  | share href _ ih => exact .share href ih

end IxonExprRel

/-- Erase v2 substructural annotations into the conservative Lean fragment. -/
def eraseBinderModes : Ixon.Expr → Ixon.Expr
  | .sort idx => .sort idx
  | .var idx => .var idx
  | .ref idx us => .ref idx us
  | .recur idx us => .recur idx us
  | .prj typeIdx field val => .prj typeIdx field (eraseBinderModes val)
  | .str idx => .str idx
  | .nat idx => .nat idx
  | .app fn arg => .app (eraseBinderModes fn) (eraseBinderModes arg)
  | .lam _ ty body => .leanLam (eraseBinderModes ty) (eraseBinderModes body)
  | .all _ _ ty body => .leanAll (eraseBinderModes ty) (eraseBinderModes body)
  | .letE nonDep ty val body =>
    .letE nonDep (eraseBinderModes ty) (eraseBinderModes val)
      (eraseBinderModes body)
  | .share idx => .share idx

@[simp] theorem eraseModes_idem (expr : Ixon.Expr) :
    eraseBinderModes (eraseBinderModes expr) = eraseBinderModes expr := by
  induction expr <;>
    simp [eraseBinderModes, Ixon.Expr.leanLam, Ixon.Expr.leanAll, *]

@[simp] theorem leanFragment_eraseModes (expr : Ixon.Expr) :
    (eraseBinderModes expr).leanFragment = true := by
  induction expr <;>
    simp [eraseBinderModes, Ixon.Expr.leanLam, Ixon.Expr.leanAll,
      Ixon.Expr.leanFragment, *]

/-- A conservative-fragment expression is unchanged by mode erasure. -/
theorem eraseBinderModes_eq_self_of_leanFragment {expr : Ixon.Expr}
    (h : expr.leanFragment = true) : eraseBinderModes expr = expr := by
  induction expr with
  | sort | var | ref | recur | str | nat | share => rfl
  | prj typeIdx field val ih =>
    simp only [Ixon.Expr.leanFragment] at h
    simp [eraseBinderModes, ih h]
  | app fn arg ihfn iharg =>
    simp only [Ixon.Expr.leanFragment, Bool.and_eq_true] at h
    simp [eraseBinderModes, ihfn h.1, iharg h.2]
  | lam uses ty body ihty ihbody =>
    cases uses <;>
      simp_all [Ixon.Expr.leanFragment, eraseBinderModes, Ixon.Expr.leanLam]
  | all uses owned ty body ihty ihbody =>
    cases uses <;> cases owned <;>
      simp_all [Ixon.Expr.leanFragment, eraseBinderModes, Ixon.Expr.leanAll]
  | letE nonDep ty val body ihty ihval ihbody =>
    simp only [Ixon.Expr.leanFragment, Bool.and_eq_true] at h
    simp [eraseBinderModes, ihty h.1.1, ihval h.1.2, ihbody h.2]

namespace IxonExprRel

/-- Erasing v2 modes preserves every direct set-model value derivation. -/
theorem eraseModes {entries : Ix.Theory.Model.Environment Address}
    {catalog : Catalog} {dctx : DecodeCtx} {strings : StringRefs Address}
    {expr : Ixon.Expr} {value : VExpr Address}
    (h : IxonExprRel entries catalog dctx strings expr value) :
    IxonExprRel entries catalog dctx strings (eraseBinderModes expr) value := by
  induction h with
  | var => exact .var
  | sort hidx => exact .sort hidx
  | ref href hres hentry hunivs harity =>
    exact .ref href hres hentry hunivs harity
  | recur href hres hentry hunivs harity =>
    exact .recur href hres hentry hunivs harity
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | lam _ _ ihty ihbody => exact .lam ihty ihbody
  | all _ _ ihty ihbody => exact .all ihty ihbody
  | letE _ _ _ ihty ihval ihbody => exact .letE ihty ihval ihbody
  | prj href hres hentry _ ihval => exact .prj href hres hentry ihval
  | nat href hblob => exact .nat href hblob
  | str href hblob hutf8 => exact .str href hblob hutf8
  | share href hexp _ => exact .share href hexp

/-- A derivation for the conservative erasure can be decorated with the
original v2 modes.  No semantic evidence is invented or discarded. -/
theorem of_eraseModes {entries : Ix.Theory.Model.Environment Address}
    {catalog : Catalog} {dctx : DecodeCtx} {strings : StringRefs Address}
    {expr : Ixon.Expr} {value : VExpr Address}
    (h : IxonExprRel entries catalog dctx strings (eraseBinderModes expr)
      value) :
    IxonExprRel entries catalog dctx strings expr value := by
  induction expr generalizing value with
  | sort | var | ref | recur | str | nat | share =>
    simpa [eraseBinderModes] using h
  | prj typeIdx field val ih =>
    cases h with
    | prj href hres hentry hval => exact .prj href hres hentry (ih hval)
  | app fn arg ihfn iharg =>
    cases h with
    | app hfn harg => exact .app (ihfn hfn) (iharg harg)
  | lam uses ty body ihty ihbody =>
    cases h with
    | lam hty hbody => exact .lam (ihty hty) (ihbody hbody)
  | all uses owned ty body ihty ihbody =>
    cases h with
    | all hty hbody => exact .all (ihty hty) (ihbody hbody)
  | letE nonDep ty val body ihty ihval ihbody =>
    cases h with
    | letE hty hval hbody =>
      exact .letE (ihty hty) (ihval hval) (ihbody hbody)

/-- V2 annotations are semantically inert at the Lean compiler boundary. -/
theorem eraseModes_iff {entries : Ix.Theory.Model.Environment Address}
    {catalog : Catalog} {dctx : DecodeCtx} {strings : StringRefs Address}
    {expr : Ixon.Expr} {value : VExpr Address} :
    IxonExprRel entries catalog dctx strings (eraseBinderModes expr) value ↔
      IxonExprRel entries catalog dctx strings expr value :=
  ⟨of_eraseModes, eraseModes⟩

end IxonExprRel

/-- Honest boundary for source-kernel meaning: a set-model realization of the
environment index against which the compiler relations are read.  Compiler
theorems consume this explicit witness; no axiom is needed for the structural
Ixon conversion itself. -/
structure KernelSourceWitness (V : Type v) [Ix.Theory.Model.SetTheory V] where
  entries : Ix.Theory.Model.Environment Address
  constants : Ix.Theory.Model.Assignment Address V
  realizes : Ix.Theory.Model.Realizes constants entries

end Ix.Compile.Verify
