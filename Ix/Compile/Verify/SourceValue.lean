import Ix.Compile.Verify.Reference

open Ix.Theory (VLevel VExpr ConstRef)

/-!
# Source-to-Ixon value preservation

This module closes the first expression-level compiler square.  `SourceExprRel`
gives a named `Ix.Expr` an independent set-model meaning, read with the same
conventions as `IxonExprRel`.  `RefCompileCtxRel` states that the finite
indices chosen by `compileExprRef` point at the same universes, block
references, and literal bytes in the target tables.  The preservation theorem
then constructs `IxonExprRel` for the exact compiler result.
-/

namespace Ix.Compile.Verify

/-- Independent semantic interpretation choices for named source syntax. -/
structure SourceCtx where
  /-- The set-model block reference denoted by a source constant name. -/
  refOf : Ix.Name → ConstRef Address
  univ? : Ix.Level → Option VLevel

def SourceCtx.univArgs? (ctx : SourceCtx) (levels : Array Ix.Level) :
    Option (List VLevel) :=
  levels.toList.mapM ctx.univ?

/-- Raw semantic relation for the ordinary named-Ix compiler input.  Hash
well-formedness and typing are separate source-witness obligations. -/
inductive SourceExprRel (entries : Ix.Theory.Model.Environment Address)
    (sctx : SourceCtx) (strings : StringRefs Address) :
    Ix.Expr → VExpr Address → Prop where
  | bvar {idx : Nat} {hash : Address} :
    SourceExprRel entries sctx strings (.bvar idx hash)
      (.bvar idx.toUInt64.toNat)
  | sort {level : Ix.Level} {hash : Address} {u : VLevel} :
    sctx.univ? level = some u →
    SourceExprRel entries sctx strings (.sort level hash) (.sort u)
  | const {name : Ix.Name} {levels : Array Ix.Level} {hash : Address}
      {entry : Ix.Theory.Model.ConstantEntry Address} {us : List VLevel} :
    entries (sctx.refOf name) = some entry →
    sctx.univArgs? levels = some us →
    us.length = entry.universes →
    SourceExprRel entries sctx strings (.const name levels hash)
      (.const (sctx.refOf name) us)
  | app {fn arg : Ix.Expr} {hash : Address} {fn' arg' : VExpr Address} :
    SourceExprRel entries sctx strings fn fn' →
    SourceExprRel entries sctx strings arg arg' →
    SourceExprRel entries sctx strings (.app fn arg hash) (.app fn' arg')
  | lam {name : Ix.Name} {ty body : Ix.Expr} {bi : Lean.BinderInfo}
      {hash : Address} {ty' body' : VExpr Address} :
    SourceExprRel entries sctx strings ty ty' →
    SourceExprRel entries sctx strings body body' →
    SourceExprRel entries sctx strings (.lam name ty body bi hash)
      (.lam ty' body')
  | all {name : Ix.Name} {ty body : Ix.Expr} {bi : Lean.BinderInfo}
      {hash : Address} {ty' body' : VExpr Address} :
    SourceExprRel entries sctx strings ty ty' →
    SourceExprRel entries sctx strings body body' →
    SourceExprRel entries sctx strings (.forallE name ty body bi hash)
      (.forallE ty' body')
  | letE {name : Ix.Name} {ty val body : Ix.Expr} {nonDep : Bool}
      {hash : Address} {ty' val' body' : VExpr Address} :
    SourceExprRel entries sctx strings ty ty' →
    SourceExprRel entries sctx strings val val' →
    SourceExprRel entries sctx strings body body' →
    SourceExprRel entries sctx strings (.letE name ty val body nonDep hash)
      (body'.inst val')
  | nat {value : Nat} {hash : Address} :
    SourceExprRel entries sctx strings (.lit (.natVal value) hash)
      (.natLit value)
  | str {value : String} {hash : Address} :
    SourceExprRel entries sctx strings (.lit (.strVal value) hash)
      (strings.stringLiteral value)
  | mdata {data : Array (Ix.Name × Ix.DataValue)} {inner : Ix.Expr}
      {hash : Address} {value : VExpr Address} :
    SourceExprRel entries sctx strings inner value →
    SourceExprRel entries sctx strings (.mdata data inner hash) value
  | prj {typeName : Ix.Name} {field : Nat} {val : Ix.Expr} {hash : Address}
      {entry : Ix.Theory.Model.ConstantEntry Address} {val' : VExpr Address} :
    entries (sctx.refOf typeName) = some entry →
    SourceExprRel entries sctx strings val val' →
    SourceExprRel entries sctx strings (.proj typeName field val hash)
      (.proj (sctx.refOf typeName) field.toUInt64.toNat val')

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
      catalog.resolve addr = some (source.refOf name)
  recur : ∀ {name idx}, compile.mutIndex name = some idx →
    ∃ addr, dctx.mutAddrs[idx.toNat]? = some addr ∧
      catalog.resolve addr = some (source.refOf name)
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
set-model value. -/
theorem compileExprRef_value {entries : Ix.Theory.Model.Environment Address}
    {sctx : SourceCtx} {catalog : Catalog} {dctx : DecodeCtx}
    {compile : RefCompileCtx} {strings : StringRefs Address}
    {source : Ix.Expr} {target : Ixon.Expr} {value : VExpr Address}
    (hctx : RefCompileCtxRel compile sctx catalog dctx)
    (hsource : SourceExprRel entries sctx strings source value)
    (hcompile : compileExprRef compile source = some target) :
    IxonExprRel entries catalog dctx strings target value := by
  induction hsource generalizing target with
  | bvar =>
    simp [compileExprRef] at hcompile
    subst target
    exact .var
  | sort hvalue =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨idx, hidx, rfl⟩
    exact .sort (hctx.univ hidx hvalue)
  | const hentry hvalues harity =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨idxs, hidxs, hcompile⟩
    split at hcompile
    · rename_i idx hmut
      simp at hcompile
      subst target
      rcases hctx.recur hmut with ⟨addr, href, hres⟩
      exact .recur href hres hentry (hctx.univArgs hidxs hvalues) harity
    · simp at hcompile
      rcases hcompile with ⟨idx, hidx, rfl⟩
      rcases hctx.ref hidx with ⟨addr, href, hres⟩
      exact .ref href hres hentry (hctx.univArgs hidxs hvalues) harity
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
    simpa [hvalue] using
      IxonExprRel.nat (entries := entries) (strings := strings) href hblob
  | str =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨idx, hidx, rfl⟩
    rcases hctx.str hidx with ⟨addr, bytes, href, hblob, hvalue⟩
    exact .str href hblob hvalue
  | mdata _ ih => exact ih hcompile
  | prj hentry _ ihval =>
    simp [compileExprRef] at hcompile
    rcases hcompile with ⟨typeIdx, htype, val, hval, rfl⟩
    rcases hctx.ref htype with ⟨addr, href, hres⟩
    exact .prj href hres hentry (ihval hval)

end Ix.Compile.Verify
