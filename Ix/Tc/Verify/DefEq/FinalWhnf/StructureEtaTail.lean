import Ix.Tc.Verify.DefEq.FinalWhnf.StructureEtaBase

/-!
# Structure-eta tail after type agreement

This module composes the common-base shortcut and explicit field loop after
the caller has established that the two operands have definitionally equal
types.  The only semantic input is an eta law indexed by the exact field
projection equations proved by those loops.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Exact semantic continuation needed after all structure fields agree.
The outer constructor/classifier proof supplies this from the trusted
constructor metadata and the explicit structure-eta Theory boundary. -/
def FinalWhnfStructEtaLaw (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) (Delta : KVLCtx) (inductId : KId .anon)
    (numFields : Nat) (fieldV : Nat → VExpr) (baseV resultV : VExpr) :
    Prop :=
  (∀ field, field < numFields →
    EtaExpansionFieldAgreement trProj world uvars Delta inductId field
      (fieldV field) baseV) →
    world.venv.IsDefEqU uvars Delta.toCtx baseV resultV

namespace RecM

/-- Both structure-eta implementations establish the same finite family of
field equations before invoking the semantic eta law. -/
theorem tryEtaStructAfterTypes_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {inductId : KId .anon} {numParams numFields : Nat}
    {base : KExpr .anon} {args : Array (KExpr .anon)}
    {baseV resultV : VExpr} {fieldV projectedV : Nat → VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hnoDelta : DefEqReduction.WFAt layer semantics trProj world support
      uvars whnfNoDelta)
    (hprojectionValue : ∀ {id : KId .anon} {idx : UInt64}
        {value : KExpr .anon} {info : ExprInfo .anon},
      support (.prj id idx value info) → support value)
    (hbaseSupport : support base)
    (hbase : TrKExprS world.venv uvars world.nameOf trProj Delta base baseV)
    (hfieldSupport : ∀ field, field < numFields →
      support args[numParams + field]!)
    (hfield : ∀ field, field < numFields →
      TrKExprS world.venv uvars world.nameOf trProj Delta
        args[numParams + field]! (fieldV field))
    (structName : Lean.Name)
    (hname : world.nameOf inductId.addr = some structName)
    (hgeneratedSupport : ∀ field, field < numFields →
      support (KExpr.mkPrj inductId field.toUInt64 base))
    (hgenerated : ∀ field, field < numFields →
      trProj Delta.toCtx structName field.toUInt64.toNat
        baseV (projectedV field))
    (hfieldIndex : ∀ field, field < numFields →
      field.toUInt64.toNat = field)
    (heta : FinalWhnfStructEtaLaw trProj world uvars Delta inductId
      numFields fieldV baseV resultV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryEtaStructAfterTypes inductId numParams numFields base args)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx baseV resultV) := by
  unfold tryEtaStructAfterTypes
  apply RecM.WF.bind <|
    etaExpansionBase_wf theory hcollision hnoDelta hprojectionValue
      hfieldSupport hfield
  intro commonBase afterBase hcommonBase
  have hexplicit : ∀ explicitState,
      RecM.WF layer semantics trProj world support uvars Delta explicitState
        (tryEtaStructFields inductId numParams base args numFields 0)
        (fun answer _ => answer = true →
          world.venv.IsDefEqU uvars Delta.toCtx baseV resultV) := by
    intro explicitState
    apply RecM.WF.mono <|
      tryEtaStructFields_wf hcollision hbase structName hname projectedV
        fieldV
        (fun offset hlt => by simpa using hgeneratedSupport offset hlt)
        (fun offset hlt => by simpa using hfieldSupport offset hlt)
        (fun offset hlt => by simpa using hgenerated offset hlt)
        (fun offset hlt => by simpa using hfield offset hlt)
    · intro answer final hagreement htrue
      apply heta
      intro field hlt
      have hprojection := hgenerated field hlt
      rw [hfieldIndex field hlt] at hprojection
      exact ⟨structName, projectedV field, hname, hprojection,
        (hagreement htrue field hlt).symm⟩
    · intro _ _ _
      trivial
  cases commonBase with
  | none =>
      simpa only using hexplicit afterBase
  | some commonBase =>
      rcases hcommonBase with
        ⟨hcommonSupport, commonBaseV, hcommonTr, hcommonAgreement⟩
      simp only
      apply RecM.WF.bind <| RecM.WF.withInv <|
        RecM.isDefEqCall_wf hbaseSupport hcommonSupport hbase hcommonTr
      intro equal afterEqual hequal
      rcases hequal with ⟨hIEqual, hequal⟩
      cases equal with
      | false =>
          simpa only [Bool.false_eq_true, if_false, pure_bind] using
            hexplicit afterEqual
      | true =>
          exact RecM.WF.pure fun _ _ => by
            apply heta
            intro field hlt
            obtain ⟨fieldStructName, commonProjectedV, hfieldName,
              hcommonProjection, hfieldCommon⟩ :=
                hcommonAgreement field hlt
            have hDelta : KVLCtx.WF world.venv uvars Delta :=
              hIEqual.2.1.wf
            have hctx :=
              (KVLCtx.IsDefEq.refl world.venvWF.ordered hDelta).defeqCtx
            obtain ⟨baseProjectedV, hbaseProjection⟩ :=
              theory.projections.defeqDFC hctx (hequal rfl).symm
                hcommonProjection
            have hprojectionEq := theory.projections.uniq hctx
              hcommonProjection hbaseProjection (hequal rfl).symm
            exact ⟨fieldStructName, baseProjectedV, hfieldName,
              hbaseProjection,
              hfieldCommon.trans world.venvWF hDelta hprojectionEq⟩

end RecM

end Ix.Tc
