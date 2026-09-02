import Ix.Compile.Verify.Reference

/-!
# Source-to-Ixon value preservation

This module closes the first expression-level compiler square.  `SourceExprRel`
gives a named `Ix.Expr` an independent Lean4Lean meaning.  `RefCompileCtxRel`
states that the finite indices chosen by `compileExprRef` point at the same
universes, names, and literal bytes in the target tables.  The preservation
theorem then constructs `IxonExprRel` for the exact compiler result.
-/

namespace Ix.Compile.Verify

open Lean4Lean (VConstant VEnv VExpr VLevel)

/-- Independent semantic interpretation choices for named source syntax. -/
structure SourceCtx where
  nameOf : Ix.Name → Lean.Name
  univ? : Ix.Level → Option VLevel

def SourceCtx.univArgs? (ctx : SourceCtx) (levels : Array Ix.Level) :
    Option (List VLevel) :=
  levels.toList.mapM ctx.univ?

/-- Raw semantic relation for the ordinary named-Ix compiler input.  Hash
well-formedness and typing are separate source-witness obligations. -/
inductive SourceExprRel (venv : VEnv) (sctx : SourceCtx)
    (trProj : ProjectionRel) {uvars : Nat} :
    List VExpr → Ix.Expr → VExpr → Prop where
  | bvar {locals : List VExpr} {idx : Nat} {hash : Address} :
    SourceExprRel venv sctx trProj locals (.bvar idx hash)
      (.bvar idx.toUInt64.toNat)
  | sort {locals : List VExpr} {level : Ix.Level} {hash : Address}
      {u : VLevel} :
    sctx.univ? level = some u →
    SourceExprRel venv sctx trProj locals (.sort level hash) (.sort u)
  | const {locals : List VExpr} {name : Ix.Name} {levels : Array Ix.Level}
      {hash : Address} {ci : VConstant} {us : List VLevel} :
    venv.constants (sctx.nameOf name) = some ci →
    sctx.univArgs? levels = some us →
    us.length = ci.uvars →
    SourceExprRel venv sctx trProj locals (.const name levels hash)
      (.const (sctx.nameOf name) us)
  | app {locals : List VExpr} {fn arg : Ix.Expr} {hash : Address}
      {fn' arg' : VExpr} :
    SourceExprRel venv sctx trProj locals fn fn' →
    SourceExprRel venv sctx trProj locals arg arg' →
    SourceExprRel venv sctx trProj locals (.app fn arg hash) (.app fn' arg')
  | lam {locals : List VExpr} {name : Ix.Name} {ty body : Ix.Expr}
      {bi : Lean.BinderInfo} {hash : Address} {ty' body' : VExpr} :
    SourceExprRel venv sctx trProj locals ty ty' →
    SourceExprRel venv sctx trProj (ty' :: locals) body body' →
    SourceExprRel venv sctx trProj locals (.lam name ty body bi hash)
      (.lam ty' body')
  | all {locals : List VExpr} {name : Ix.Name} {ty body : Ix.Expr}
      {bi : Lean.BinderInfo} {hash : Address} {ty' body' : VExpr} :
    SourceExprRel venv sctx trProj locals ty ty' →
    SourceExprRel venv sctx trProj (ty' :: locals) body body' →
    SourceExprRel venv sctx trProj locals (.forallE name ty body bi hash)
      (.forallE ty' body')
  | letE {locals : List VExpr} {name : Ix.Name} {ty val body : Ix.Expr}
      {nonDep : Bool} {hash : Address} {ty' val' body' : VExpr} :
    SourceExprRel venv sctx trProj locals ty ty' →
    SourceExprRel venv sctx trProj locals val val' →
    SourceExprRel venv sctx trProj (ty' :: locals) body body' →
    SourceExprRel venv sctx trProj locals
      (.letE name ty val body nonDep hash) (body'.inst val')
  | nat {locals : List VExpr} {value : Nat} {hash : Address} :
    SourceExprRel venv sctx trProj locals (.lit (.natVal value) hash)
      (.natLit value)
  | str {locals : List VExpr} {value : String} {hash : Address} :
    SourceExprRel venv sctx trProj locals (.lit (.strVal value) hash)
      (.trLiteral (.strVal value))
  | mdata {locals : List VExpr} {data : Array (Ix.Name × Ix.DataValue)}
      {inner : Ix.Expr} {hash : Address} {value : VExpr} :
    SourceExprRel venv sctx trProj locals inner value →
    SourceExprRel venv sctx trProj locals (.mdata data inner hash) value
  | prj {locals : List VExpr} {typeName : Ix.Name} {field : Nat}
      {val : Ix.Expr} {hash : Address} {ci : VConstant} {val' out : VExpr} :
    venv.constants (sctx.nameOf typeName) = some ci →
    SourceExprRel venv sctx trProj locals val val' →
    trProj uvars locals (sctx.nameOf typeName) field.toUInt64.toNat val' out →
    SourceExprRel venv sctx trProj locals
      (.proj typeName field val hash) out

/-- The reference compiler's index choices resolve to the source meaning in
one concrete target context. -/
structure RefCompileCtxRel (compile : RefCompileCtx) (source : SourceCtx)
    (catalog : Catalog) (dctx : DecodeCtx) : Prop where
  univ : ∀ {level idx u},
    compile.univIndex level = some idx →
    source.univ? level = some u →
    dctx.univ? idx = some u
  univArgs : ∀ {levels idxs us},
    levels.mapM compile.univIndex = some idxs →
    source.univArgs? levels = some us →
    dctx.univArgs? idxs = some us
  ref : ∀ {name idx}, compile.refIndex name = some idx →
    ∃ addr, dctx.refs[idx.toNat]? = some addr ∧
      catalog.nameOf addr = some (source.nameOf name)
  recur : ∀ {name idx}, compile.mutIndex name = some idx →
    ∃ addr, dctx.mutAddrs[idx.toNat]? = some addr ∧
      catalog.nameOf addr = some (source.nameOf name)
  nat : ∀ {value idx}, compile.literalRef (.natVal value) = some idx →
    ∃ addr bytes,
      dctx.refs[idx.toNat]? = some addr ∧
      catalog.blobs addr = some bytes ∧
      Nat.fromBytesLE bytes.data = value
  str : ∀ {value idx}, compile.literalRef (.strVal value) = some idx →
    ∃ addr bytes,
      dctx.refs[idx.toNat]? = some addr ∧
      catalog.blobs addr = some bytes ∧
      String.fromUTF8? bytes = some value

/-- Ordinary reference compilation preserves the independently stated
Lean4Lean value. -/
theorem compileExprRef_value {venv : VEnv} {sctx : SourceCtx}
    {catalog : Catalog} {dctx : DecodeCtx} {compile : RefCompileCtx}
    {trProj : ProjectionRel} {uvars : Nat} {locals : List VExpr}
    {source : Ix.Expr} {target : Ixon.Expr} {value : VExpr}
    (hctx : RefCompileCtxRel compile sctx catalog dctx)
    (hsource : SourceExprRel (uvars := uvars) venv sctx trProj locals source value)
    (hcompile : compileExprRef compile source = some target) :
    IxonExprRel (uvars := uvars) venv catalog dctx trProj locals target value := by
  induction hsource generalizing target with
  | bvar =>
    simp [compileExprRef] at hcompile
    subst target
    exact .var
  | sort hvalue =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨idx, hidx, rfl⟩
    exact .sort (hctx.univ hidx hvalue)
  | const hconst hvalues harity =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨idxs, hidxs, hcompile⟩
    split at hcompile
    · rename_i idx hmut
      simp at hcompile
      subst target
      rcases hctx.recur hmut with ⟨addr, href, hname⟩
      exact .recur href hname hconst (hctx.univArgs hidxs hvalues) harity
    · simp at hcompile
      rcases hcompile with ⟨idx, hidx, rfl⟩
      rcases hctx.ref hidx with ⟨addr, href, hname⟩
      exact .ref href hname hconst (hctx.univArgs hidxs hvalues) harity
  | app _ _ ihfn iharg =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨fn, hfn, arg, harg, rfl⟩
    exact .app (ihfn hfn) (iharg harg)
  | lam _ _ ihty ihbody =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨ty, hty, body, hbody, rfl⟩
    exact .lam (ihty hty) (ihbody hbody)
  | all _ _ ihty ihbody =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨ty, hty, body, hbody, rfl⟩
    exact .all (ihty hty) (ihbody hbody)
  | letE _ _ _ ihty ihval ihbody =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨ty, hty, val, hval, body, hbody, rfl⟩
    exact .letE (ihty hty) (ihval hval) (ihbody hbody)
  | nat =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨idx, hidx, rfl⟩
    rcases hctx.nat hidx with ⟨addr, bytes, href, hblob, hvalue⟩
    simpa [hvalue] using IxonExprRel.nat (venv := venv) (trProj := trProj)
      href hblob
  | str =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨idx, hidx, rfl⟩
    rcases hctx.str hidx with ⟨addr, bytes, href, hblob, hvalue⟩
    exact .str href hblob hvalue
  | mdata _ ih => exact ih hcompile
  | prj hconst _ hproj ihval =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨typeIdx, htype, val, hval, rfl⟩
    rcases hctx.ref htype with ⟨addr, href, hname⟩
    exact .prj href hname hconst (ihval hval) hproj

end Ix.Compile.Verify
