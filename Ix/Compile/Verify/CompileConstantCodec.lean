import Ix.Compile.Verify.CompileExprCodec
import Ix.Compile.Verify.MutualConstantCodec

/-!
# Production constant compiler/codec bridge

This module closes the unshared axiom and definition assembly core against the
production constant codec. The production declaration driver subsequently
runs `Sharing.applySharing`; preservation by that rewrite remains a separate,
explicit proof obligation.
-/

namespace Ix.Compile.Verify

/-- The primary reference and universe tables in a production block state are
representable by the constant wire format. -/
structure BlockWireTablesWF (state : Ix.CompileM.BlockState) : Prop where
  refsCount : state.refs.size < UInt64.size
  refs : ∀ ref ∈ state.refs, ref.hash.size = 32
  univsCount : state.univs.size < UInt64.size
  univs : ∀ univ ∈ state.univs, Codec.Ixon.Univ.WireWF univ

/-- A frozen expression-table view transports the primary wire-table
invariant from the preseed snapshot to the live production state. -/
theorem BlockWireTablesWF.of_exprTableView_eq
    {snapshot state : Ix.CompileM.BlockState}
    (h : BlockWireTablesWF snapshot)
    (hview : exprTableView state = exprTableView snapshot) :
    BlockWireTablesWF state := by
  have hrefs : state.refs = snapshot.refs :=
    congrArg ExprTableView.refs hview
  have hunivs : state.univs = snapshot.univs :=
    congrArg ExprTableView.univs hview
  constructor
  · simpa only [hrefs] using h.refsCount
  · simpa only [hrefs] using h.refs
  · simpa only [hunivs] using h.univsCount
  · simpa only [hunivs] using h.univs

/-- Assemble an unshared axiom constant from one compiled type and the primary
tables of its final production block state. -/
def unsharedAxiomConstant (isUnsafe : Bool) (lvls : UInt64)
    (typ : Ixon.Expr) (state : Ix.CompileM.BlockState) : Ixon.Constant :=
  { info := .axio { isUnsafe, lvls, typ }
    sharing := #[]
    refs := state.refs
    univs := state.univs }

/-- Assemble an unshared definition constant from its two compiled roots and
the primary tables of its final production block state. -/
def unsharedDefinitionConstant (kind : Ix.DefKind)
    (safety : Ix.DefinitionSafety) (lvls : UInt64)
    (typ value : Ixon.Expr) (state : Ix.CompileM.BlockState) : Ixon.Constant :=
  { info := .defn { kind, safety, lvls, typ, value }
    sharing := #[]
    refs := state.refs
    univs := state.univs }

theorem unsharedAxiomConstant_wireWF
    {isUnsafe : Bool} {lvls : UInt64} {typ : Ixon.Expr}
    {state : Ix.CompileM.BlockState}
    (htyp : typ.wireWF) (htables : BlockWireTablesWF state) :
    (unsharedAxiomConstant isUnsafe lvls typ state).wireWF := by
  refine ⟨htyp, ?_, ?_, htables.refsCount, htables.refs,
    htables.univsCount, htables.univs⟩
  · change 0 < UInt64.size
    exact UInt64.toNat_lt 0
  · intro expr hmem
    exact (Array.not_mem_empty expr hmem).elim

theorem unsharedDefinitionConstant_wireWF
    {kind : Ix.DefKind} {safety : Ix.DefinitionSafety} {lvls : UInt64}
    {typ value : Ixon.Expr} {state : Ix.CompileM.BlockState}
    (htyp : typ.wireWF) (hvalue : value.wireWF)
    (htables : BlockWireTablesWF state) :
    (unsharedDefinitionConstant kind safety lvls typ value state).wireWF := by
  refine ⟨⟨htyp, hvalue⟩, ?_, ?_, htables.refsCount, htables.refs,
    htables.univsCount, htables.univs⟩
  · change 0 < UInt64.size
    exact UInt64.toNat_lt 0
  · intro expr hmem
    exact (Array.not_mem_empty expr hmem).elim

/-- The unshared axiom assembly core lies in the exact production constant
codec domain. -/
theorem deConstant_serUnsharedAxiomConstant
    {isUnsafe : Bool} {lvls : UInt64} {typ : Ixon.Expr}
    {state : Ix.CompileM.BlockState}
    (htyp : typ.wireWF) (htables : BlockWireTablesWF state) :
    Ixon.deConstant
        (Ixon.serConstant (unsharedAxiomConstant isUnsafe lvls typ state)) =
      .ok (unsharedAxiomConstant isUnsafe lvls typ state) :=
  deConstant_serConstant _ (unsharedAxiomConstant_wireWF htyp htables)

/-- The unshared definition assembly core lies in the exact production
constant codec domain. -/
theorem deConstant_serUnsharedDefinitionConstant
    {kind : Ix.DefKind} {safety : Ix.DefinitionSafety} {lvls : UInt64}
    {typ value : Ixon.Expr} {state : Ix.CompileM.BlockState}
    (htyp : typ.wireWF) (hvalue : value.wireWF)
    (htables : BlockWireTablesWF state) :
    Ixon.deConstant (Ixon.serConstant
        (unsharedDefinitionConstant kind safety lvls typ value state)) =
      .ok (unsharedDefinitionConstant kind safety lvls typ value state) :=
  deConstant_serConstant _
    (unsharedDefinitionConstant_wireWF htyp hvalue htables)

/-- The ordinary production expression phase for an axiom produces an
unshared constant that round-trips through the production constant codec. -/
theorem compileExpr_run_ordinary_axiomConstant_roundtrip
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (isUnsafe : Bool) (lvls : UInt64)
    {state : Ix.CompileM.BlockState} {source : Ix.Expr}
    {target : Ixon.Expr}
    (hsource : SupportedOrdinaryExpr levelSupport source)
    (hbound : ExprWireBound source)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (href : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) source = some target) :
    ∃ root state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr source) =
        .ok ((target, root), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      (let constant := unsharedAxiomConstant isUnsafe lvls target state'
       constant.wireWF ∧
         Ixon.deConstant (Ixon.serConstant constant) = .ok constant) := by
  obtain ⟨root, state', hrun, hstate', hwire⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv blockEnv snapshot hfree hclosed
      hlevelFaithful hexprFaithful hsource hbound hstate href
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq hstate'.tables
  refine ⟨root, state', hrun, hstate', ?_⟩
  dsimp only
  have hconstant := unsharedAxiomConstant_wireWF
    (isUnsafe := isUnsafe) (lvls := lvls) hwire htables'
  exact ⟨hconstant, deConstant_serConstant _ hconstant⟩

/-- Sequential ordinary production compilation of a definition's type and
value produces an unshared constant that round-trips through the production
constant codec. The two returned roots remain available for declaration
metadata assembly. -/
theorem compileExpr_run_ordinary_definitionConstant_roundtrip
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (snapshot : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hfree : compileEnv.surgeryFree = true)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (htables : BlockWireTablesWF snapshot)
    (kind : Ix.DefKind) (safety : Ix.DefinitionSafety) (lvls : UInt64)
    {state : Ix.CompileM.BlockState}
    {sourceType sourceValue : Ix.Expr}
    {targetType targetValue : Ixon.Expr}
    (hsourceType : SupportedOrdinaryExpr levelSupport sourceType)
    (hsourceValue : SupportedOrdinaryExpr levelSupport sourceValue)
    (hboundType : ExprWireBound sourceType)
    (hboundValue : ExprWireBound sourceValue)
    (hstate : FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state)
    (hrefType : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sourceType =
        some targetType)
    (hrefValue : compileExprRef
      (frozenRefCompileCtx compileEnv blockEnv snapshot) sourceValue =
        some targetValue) :
    ∃ typeRoot middle valueRoot state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileExpr sourceType) =
        .ok ((targetType, typeRoot), middle) ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot middle ∧
      Ix.CompileM.CompileM.run compileEnv blockEnv middle
          (Ix.CompileM.compileExpr sourceValue) =
        .ok ((targetValue, valueRoot), state') ∧
      FrozenExprStateWF compileEnv blockEnv levelSupport snapshot state' ∧
      (let constant := unsharedDefinitionConstant kind safety lvls
          targetType targetValue state'
       constant.wireWF ∧
         Ixon.deConstant (Ixon.serConstant constant) = .ok constant) := by
  obtain ⟨typeRoot, middle, htypeRun, hmiddle, htypeWire⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv blockEnv snapshot hfree hclosed
      hlevelFaithful hexprFaithful hsourceType hboundType hstate hrefType
  obtain ⟨valueRoot, state', hvalueRun, hstate', hvalueWire⟩ :=
    compileExpr_run_ordinary_wireWF compileEnv blockEnv snapshot hfree hclosed
      hlevelFaithful hexprFaithful hsourceValue hboundValue hmiddle hrefValue
  have htables' : BlockWireTablesWF state' :=
    htables.of_exprTableView_eq hstate'.tables
  refine ⟨typeRoot, middle, valueRoot, state', htypeRun, hmiddle,
    hvalueRun, hstate', ?_⟩
  dsimp only
  have hconstant :=
    unsharedDefinitionConstant_wireWF (kind := kind) (safety := safety)
      (lvls := lvls) htypeWire hvalueWire htables'
  exact ⟨hconstant, deConstant_serConstant _ hconstant⟩

end Ix.Compile.Verify
