import Ix.Ixon
import Lean4Lean.Theory.Literals
import Lean4Lean.Theory.Typing.Env

/-!
# Ixon v2 expressions and Lean4Lean values

This is the first compiler-facing semantic boundary.  It interprets an Ixon
expression directly as a Lean4Lean `VExpr`; it does not run Ix.Tc and does not
use checker acceptance as a specification.

The relation is table-aware.  It resolves universe, reference, mutual-member,
sharing, and literal indices against an explicit immutable context.  A cyclic
sharing table has no finite derivation.  Lambda usage and forall
usage/ownership are intentionally absent from the semantic premises: ordinary
Lean compilation inhabits `.many`/`.shared`, while v2 annotations remain
available to later substructural passes without changing the Lean meaning.
-/

namespace Ix.Compile.Verify

open Lean4Lean (VConstant VEnv VExpr VLevel)

/-- Immutable semantic views needed to interpret an Ixon expression. -/
structure Catalog where
  /-- Resolve a content address to its Theory declaration name. -/
  nameOf : Address → Option Lean.Name
  /-- Resolve literal content addresses to their committed bytes. -/
  blobs : Address → Option ByteArray

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

/-- Projection interpretation is supplied by the surrounding declaration
model.  Its universe/local-context indices match the existing raw Theory
boundary, while this module remains independent of Ix.Tc. -/
abbrev ProjectionRel :=
  Nat → List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop

namespace ProjectionRel

/-- Projection-free fixtures use an uninhabited projection relation. -/
def none : ProjectionRel := fun _ _ _ _ _ _ => False

end ProjectionRel

/-- Direct semantic relation from table-indexed Ixon syntax to Lean4Lean
syntax.  This is a raw representation relation: typing and source-kernel
well-formedness are separate obligations. -/
inductive IxonExprRel (venv : VEnv) (catalog : Catalog) (dctx : DecodeCtx)
    (trProj : ProjectionRel) {uvars : Nat} :
    List VExpr → Ixon.Expr → VExpr → Prop where
  | var {locals : List VExpr} {idx : UInt64} :
    IxonExprRel venv catalog dctx trProj locals (.var idx) (.bvar idx.toNat)
  | sort {locals : List VExpr} {idx : UInt64} {u : VLevel} :
    dctx.univ? idx = some u →
    IxonExprRel venv catalog dctx trProj locals (.sort idx) (.sort u)
  | ref {locals : List VExpr} {refIdx : UInt64}
      {univIdxs : Array UInt64} {addr : Address} {name : Lean.Name}
      {ci : VConstant} {us : List VLevel} :
    dctx.refs[refIdx.toNat]? = some addr →
    catalog.nameOf addr = some name →
    venv.constants name = some ci →
    dctx.univArgs? univIdxs = some us →
    us.length = ci.uvars →
    IxonExprRel venv catalog dctx trProj locals (.ref refIdx univIdxs)
      (.const name us)
  | recur {locals : List VExpr} {recIdx : UInt64}
      {univIdxs : Array UInt64} {addr : Address} {name : Lean.Name}
      {ci : VConstant} {us : List VLevel} :
    dctx.mutAddrs[recIdx.toNat]? = some addr →
    catalog.nameOf addr = some name →
    venv.constants name = some ci →
    dctx.univArgs? univIdxs = some us →
    us.length = ci.uvars →
    IxonExprRel venv catalog dctx trProj locals (.recur recIdx univIdxs)
      (.const name us)
  | app {locals : List VExpr} {fn arg : Ixon.Expr} {fn' arg' : VExpr} :
    IxonExprRel venv catalog dctx trProj locals fn fn' →
    IxonExprRel venv catalog dctx trProj locals arg arg' →
    IxonExprRel venv catalog dctx trProj locals (.app fn arg) (.app fn' arg')
  | lam {locals : List VExpr} {uses : Ixon.Uses} {ty body : Ixon.Expr}
      {ty' body' : VExpr} :
    IxonExprRel venv catalog dctx trProj locals ty ty' →
    IxonExprRel venv catalog dctx trProj (ty' :: locals) body body' →
    IxonExprRel venv catalog dctx trProj locals (.lam uses ty body)
      (.lam ty' body')
  | all {locals : List VExpr} {uses : Ixon.Uses} {owned : Ixon.Owned}
      {ty body : Ixon.Expr} {ty' body' : VExpr} :
    IxonExprRel venv catalog dctx trProj locals ty ty' →
    IxonExprRel venv catalog dctx trProj (ty' :: locals) body body' →
    IxonExprRel venv catalog dctx trProj locals (.all uses owned ty body)
      (.forallE ty' body')
  | letE {locals : List VExpr} {nonDep : Bool} {ty val body : Ixon.Expr}
      {ty' val' body' : VExpr} :
    IxonExprRel venv catalog dctx trProj locals ty ty' →
    IxonExprRel venv catalog dctx trProj locals val val' →
    IxonExprRel venv catalog dctx trProj (ty' :: locals) body body' →
    IxonExprRel venv catalog dctx trProj locals (.letE nonDep ty val body)
      (body'.inst val')
  | prj {locals : List VExpr} {typeRefIdx field : UInt64}
      {val : Ixon.Expr} {addr : Address} {name : Lean.Name}
      {ci : VConstant} {val' out : VExpr} :
    dctx.refs[typeRefIdx.toNat]? = some addr →
    catalog.nameOf addr = some name →
    venv.constants name = some ci →
    IxonExprRel venv catalog dctx trProj locals val val' →
    trProj uvars locals name field.toNat val' out →
    IxonExprRel venv catalog dctx trProj locals
      (.prj typeRefIdx field val) out
  | nat {locals : List VExpr} {refIdx : UInt64} {addr : Address}
      {bytes : ByteArray} :
    dctx.refs[refIdx.toNat]? = some addr →
    catalog.blobs addr = some bytes →
    IxonExprRel venv catalog dctx trProj locals (.nat refIdx)
      (.natLit (Nat.fromBytesLE bytes.data))
  | str {locals : List VExpr} {refIdx : UInt64} {addr : Address}
      {bytes : ByteArray} {value : String} :
    dctx.refs[refIdx.toNat]? = some addr →
    catalog.blobs addr = some bytes →
    String.fromUTF8? bytes = some value →
    IxonExprRel venv catalog dctx trProj locals (.str refIdx)
      (.trLiteral (.strVal value))
  | share {locals : List VExpr} {idx : UInt64} {expansion : Ixon.Expr}
      {value : VExpr} :
    dctx.sharing[idx.toNat]? = some expansion →
    IxonExprRel venv catalog dctx trProj locals expansion value →
    IxonExprRel venv catalog dctx trProj locals (.share idx) value

namespace IxonExprRel

/-- The representation relation is monotone in the trusted Theory
environment; only resolved constant-table witnesses are transported. -/
theorem mono {venv venv' : VEnv} (henv : venv ≤ venv')
    {catalog : Catalog} {dctx : DecodeCtx} {trProj : ProjectionRel}
    {uvars : Nat} {locals : List VExpr} {expr : Ixon.Expr} {value : VExpr}
    (h : IxonExprRel (uvars := uvars) venv catalog dctx trProj locals expr value) :
    IxonExprRel (uvars := uvars) venv' catalog dctx trProj locals expr value := by
  induction h with
  | var => exact .var
  | sort hidx => exact .sort hidx
  | ref href hname hconst hunivs harity =>
    exact .ref href hname (henv.constants hconst) hunivs harity
  | recur href hname hconst hunivs harity =>
    exact .recur href hname (henv.constants hconst) hunivs harity
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | lam _ _ ihty ihbody => exact .lam ihty ihbody
  | all _ _ ihty ihbody => exact .all ihty ihbody
  | letE _ _ _ ihty ihval ihbody => exact .letE ihty ihval ihbody
  | prj href hname hconst _ hproj ihval =>
    exact .prj href hname (henv.constants hconst) ihval hproj
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

/-- Erasing v2 modes preserves every direct Theory value derivation. -/
theorem eraseModes {venv : VEnv} {catalog : Catalog} {dctx : DecodeCtx}
    {trProj : ProjectionRel} {uvars : Nat} {locals : List VExpr}
    {expr : Ixon.Expr} {value : VExpr}
    (h : IxonExprRel (uvars := uvars) venv catalog dctx trProj locals expr value) :
    IxonExprRel (uvars := uvars) venv catalog dctx trProj locals
      (eraseBinderModes expr) value := by
  induction h with
  | var => exact .var
  | sort hidx => exact .sort hidx
  | ref href hname hconst hunivs harity =>
    exact .ref href hname hconst hunivs harity
  | recur href hname hconst hunivs harity =>
    exact .recur href hname hconst hunivs harity
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | lam _ _ ihty ihbody => exact .lam ihty ihbody
  | all _ _ ihty ihbody => exact .all ihty ihbody
  | letE _ _ _ ihty ihval ihbody => exact .letE ihty ihval ihbody
  | prj href hname hconst _ hproj ihval =>
    exact .prj href hname hconst ihval hproj
  | nat href hblob => exact .nat href hblob
  | str href hblob hutf8 => exact .str href hblob hutf8
  | share href hexp _ => exact .share href hexp

/-- A derivation for the conservative erasure can be decorated with the
original v2 modes.  No semantic evidence is invented or discarded. -/
theorem of_eraseModes {venv : VEnv} {catalog : Catalog} {dctx : DecodeCtx}
    {trProj : ProjectionRel} {uvars : Nat} {locals : List VExpr}
    {expr : Ixon.Expr} {value : VExpr}
    (h : IxonExprRel (uvars := uvars) venv catalog dctx trProj locals
      (eraseBinderModes expr) value) :
    IxonExprRel (uvars := uvars) venv catalog dctx trProj locals expr value := by
  induction expr generalizing locals value with
  | sort | var | ref | recur | str | nat | share =>
    simpa [eraseBinderModes] using h
  | prj typeIdx field val ih =>
    cases h with
    | prj href hname hconst hval hproj =>
      exact .prj href hname hconst (ih hval) hproj
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
theorem eraseModes_iff {venv : VEnv} {catalog : Catalog} {dctx : DecodeCtx}
    {trProj : ProjectionRel} {uvars : Nat} {locals : List VExpr}
    {expr : Ixon.Expr} {value : VExpr} :
    IxonExprRel (uvars := uvars) venv catalog dctx trProj locals
        (eraseBinderModes expr) value ↔
      IxonExprRel (uvars := uvars) venv catalog dctx trProj locals expr value :=
  ⟨of_eraseModes, eraseModes⟩

end IxonExprRel

/-- Honest boundary for source-kernel meaning while upstream Lean4Lean
construction remains incomplete.  Compiler theorems consume this explicit
witness; no axiom is needed for the structural Ixon conversion itself. -/
structure KernelSourceWitness where
  venv : VEnv
  wf : venv.WF

end Ix.Compile.Verify
