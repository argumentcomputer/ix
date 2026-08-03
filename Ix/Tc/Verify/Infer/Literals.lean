import Ix.Tc.Verify.Infer.Constants

/-!
# Literal inference

The concrete checker represents literals directly, but inference returns the
`Nat` or `String` constant selected by the runtime primitive table.  The source
translation's `ContainsLits` premise proves the literal is meaningful; it does
not by itself identify the runtime table entry or prove that the selected type
constant accepts an empty universe array.  Those representation obligations
are therefore exposed explicitly below.
-/

namespace Ix.Tc

/-- Exact Theory interpretation of the two primitive-table entries read by
literal inference.  Trust and address-to-name agreement come from
`PrimitiveIdAgrees`; the arity fields prevent an empty universe array from
being accepted merely because a name happened to match. -/
structure LiteralPrimitiveTableAgrees (world : VerifyWorld)
    (prims : Primitives .anon) : Prop where
  nat : PrimitiveIdAgrees world prims.nat ``Nat
  string : PrimitiveIdAgrees world prims.string ``String
  natArity : forall {ci}, world.venv.constants ``Nat = some ci ->
    ci.uvars = 0
  stringArity : forall {ci}, world.venv.constants ``String = some ci ->
    ci.uvars = 0

namespace LiteralPrimitiveTableAgrees

/-- The runtime Nat result has the exact closed Theory translation. -/
theorem nat_tr
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {prims : Primitives .anon}
    (hcatalog : TrustedCatalogRel trProj world)
    (htable : LiteralPrimitiveTableAgrees world prims) :
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.mkConst prims.nat #[]) Lean4Lean.VExpr.nat := by
  rw [KExpr.mkConst_shape]
  obtain ⟨ci, hlookup⟩ := htable.nat.contains hcatalog
  simpa [Lean4Lean.VExpr.nat, htable.natArity hlookup] using
    (TrKExprS.const (Δ := Delta) (uvars := uvars)
      htable.nat.2 hlookup (by simp) (by simp [htable.natArity hlookup]))

/-- The runtime String result has the exact closed Theory translation. -/
theorem string_tr
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {prims : Primitives .anon}
    (hcatalog : TrustedCatalogRel trProj world)
    (htable : LiteralPrimitiveTableAgrees world prims) :
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.mkConst prims.string #[]) Lean4Lean.VExpr.string := by
  rw [KExpr.mkConst_shape]
  obtain ⟨ci, hlookup⟩ := htable.string.contains hcatalog
  simpa [Lean4Lean.VExpr.string, htable.stringArity hlookup] using
    (TrKExprS.const (Δ := Delta) (uvars := uvars)
      htable.string.2 hlookup (by simp)
        (by simp [htable.stringArity hlookup]))

end LiteralPrimitiveTableAgrees

/-- Run-scoped resources for the two literal branches.  Generated-support
fields are restricted to canonical production primitive tables, so they do
not make a finite run support artificially contain every possible KId. -/
structure LiteralInferContext (world : VerifyWorld)
    (support : RunSupport) : Prop where
  table : forall (prims : Primitives .anon), prims.CanonicalAnon ->
    LiteralPrimitiveTableAgrees world prims
  theoryPrimitives : world.venv.HasPrimitives
  collisionFree : support.CollisionFree
  natResult : forall (prims : Primitives .anon), prims.CanonicalAnon ->
    support (KExpr.mkConst prims.nat #[])
  stringResult : forall (prims : Primitives .anon), prims.CanonicalAnon ->
    support (KExpr.mkConst prims.string #[])

namespace RecM

/-- A concrete Nat literal infers the runtime Nat constant, preserving the
complete no-acceleration invariant. -/
theorem inferUncached_nat_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon -> RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {n : Nat} {blob : Address}
    {info : ExprInfo .anon} {sourceV : Lean4Lean.VExpr}
    (context : LiteralInferContext world support)
    (theory : WhnfTheory trProj world uvars)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.nat n blob info) sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.nat n blob info))
      (fun ty _ => support ty /\
        InferPost trProj world uvars Delta sourceV ty) := by
  cases hsource with
  | nat hcontains =>
      unfold inferUncached
      apply RecM.WF.bind (RecM.WF.withInv (prims_wf (s := s)))
      intro runtimePrims afterRead hread
      rcases hread with ⟨hI, hprims, hafterRead⟩
      subst afterRead
      have hcanonical : runtimePrims.CanonicalAnon := by
        rw [hprims]
        exact hI.noAccel_primitives
      have hsupport := context.natResult runtimePrims hcanonical
      have htable := context.table runtimePrims hcanonical
      have hcatalog := hI.1.core.trustedCatalog
      apply RecM.WF.mono
        (RecM.WF.withInv <| RecM.WF.liftTcM <|
          TcM.intern_whnf_wf context.collisionFree hsupport)
      · intro result final hresult
        rcases hresult with ⟨hIfinal, rfl, _⟩
        refine ⟨hsupport, Lean4Lean.VExpr.nat, ?_, ?_⟩
        · exact (htable.nat_tr hcatalog).trKExpr
            world.venvWF.ordered theory.literalWF theory.projections.wf
            hIfinal.2.1.wf
        · have htype0 : world.venv.HasType uvars []
              (.natLit n) Lean4Lean.VExpr.nat := by
            simpa using
              (Lean4Lean.TrExprS.natLit
                (Us := List.replicate uvars Lean.Name.anonymous) (Δ := [])
                context.theoryPrimitives hcontains n).2
          exact htype0.weak0 world.venvWF (Γ := Delta.toCtx)
      · intro _ _ _
        trivial

/-- A concrete String literal infers the runtime String constant.  The source
typing is the full Lean4Lean literal construction, including `Char.ofNat` and
`String.ofList`; the returned type is still the primitive `String` entry. -/
theorem inferUncached_str_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon -> RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {value : String} {blob : Address}
    {info : ExprInfo .anon} {sourceV : Lean4Lean.VExpr}
    (context : LiteralInferContext world support)
    (theory : WhnfTheory trProj world uvars)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.str value blob info) sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.str value blob info))
      (fun ty _ => support ty /\
        InferPost trProj world uvars Delta sourceV ty) := by
  cases hsource with
  | str hcontains =>
      unfold inferUncached
      apply RecM.WF.bind (RecM.WF.withInv (prims_wf (s := s)))
      intro runtimePrims afterRead hread
      rcases hread with ⟨hI, hprims, hafterRead⟩
      subst afterRead
      have hcanonical : runtimePrims.CanonicalAnon := by
        rw [hprims]
        exact hI.noAccel_primitives
      have hsupport := context.stringResult runtimePrims hcanonical
      have htable := context.table runtimePrims hcanonical
      have hcatalog := hI.1.core.trustedCatalog
      apply RecM.WF.mono
        (RecM.WF.withInv <| RecM.WF.liftTcM <|
          TcM.intern_whnf_wf context.collisionFree hsupport)
      · intro result final hresult
        rcases hresult with ⟨hIfinal, rfl, _⟩
        refine ⟨hsupport, Lean4Lean.VExpr.string, ?_, ?_⟩
        · exact (htable.string_tr hcatalog).trKExpr
            world.venvWF.ordered theory.literalWF theory.projections.wf
            hIfinal.2.1.wf
        · have htype0 : world.venv.HasType uvars []
              (.trLiteral (.strVal value)) Lean4Lean.VExpr.string := by
            simpa [Lean4Lean.VExpr.string] using
              (Lean4Lean.TrExprS.trLiteral world.venvWF.ordered
                (Us := List.replicate uvars Lean.Name.anonymous) (Δ := [])
                context.theoryPrimitives (.strVal value) hcontains).2
          exact htype0.weak0 world.venvWF (Γ := Delta.toCtx)
      · intro _ _ _
        trivial

end RecM

end Ix.Tc
