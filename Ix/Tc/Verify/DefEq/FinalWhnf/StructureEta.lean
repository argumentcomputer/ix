import Ix.Tc.Verify.DefEq.FinalWhnf.StructureEtaTail
import Ix.Tc.Verify.Infer.Constants
import Ix.Tc.Verify.Infer.ProjectionTypes

/-!
# Final-WHNF structure eta

This module closes the outer structure-eta dispatcher around the verified
common-base scan and explicit projection loop.  Runtime classification and
constructor lookup remain distinct from the semantic eta rule: a positive
`isStructLike` answer yields an explicit eligibility token, and the narrow
Theory boundary consumes that token together with the exact constructor
metadata, typing derivations, and field equations selected by production.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Exact constructor fields retained from the declaration returned by the
production lookup. -/
def KConst.IsStructureConstructorFor (inductId : KId .anon)
    (params fields : UInt64) : KConst .anon → Prop
  | .ctor (induct := actualInduct) (params := actualParams)
      (fields := actualFields) .. =>
    actualInduct = inductId ∧ actualParams = params ∧ actualFields = fields
  | _ => False

namespace RecM

/-- Positive-result meaning of the concrete structure classifier.  The
eligibility predicate is supplied by the semantic structure-eta model; this
contract does not identify a state-only classifier result with a Theory law. -/
def FinalWhnfStructLike.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (eligible : KId .anon → Prop) : Prop :=
  ∀ {Delta state inductId},
    RecM.WF layer semantics trProj world support uvars Delta state
      (isStructLike inductId)
      (fun answer _ => answer = true → eligible inductId)

/-- Semantic boundary for structure eta.  Projection existence and the eta
law are indexed by the exact constructor application and immutable catalog
entry observed by production. -/
structure FinalWhnfStructEtaTheory (trProj : RawProjRel)
    (world : VerifyWorld) (eligible : KId .anon → Prop) : Prop where
  projections : ∀ {uvars : Nat} {Delta : KVLCtx}
      {source : KExpr .anon} {baseV : VExpr}
      {ctorId inductId : KId .anon} {levels : Array (KUniv .anon)}
      {info : ExprInfo .anon} {args : Array (KExpr .anon)}
      {entry : KConst .anon} {params fields : UInt64}
      {base : KExpr .anon},
    source.collectSpine = (.const ctorId levels info, args) →
    world.catalog ctorId = some entry →
    entry.IsStructureConstructorFor inductId params fields →
    eligible inductId →
    TrKExprS world.venv uvars world.nameOf trProj Delta base baseV →
    ∃ (structName : Lean.Name) (projectedV : Nat → VExpr),
      world.nameOf inductId.addr = some structName ∧
      ∀ field, field < fields.toNat →
        trProj Delta.toCtx structName field baseV (projectedV field)
  eta : ∀ {uvars : Nat} {Delta : KVLCtx}
      {source : KExpr .anon} {sourceV baseV : VExpr}
      {ctorId inductId : KId .anon} {levels : Array (KUniv .anon)}
      {info : ExprInfo .anon} {args : Array (KExpr .anon)}
      {entry : KConst .anon} {params fields : UInt64}
      {fieldV : Nat → VExpr}
      {baseTyV sourceTyV : VExpr},
    source.collectSpine = (.const ctorId levels info, args) →
    world.trusted ctorId →
    world.catalog ctorId = some entry →
    entry.IsStructureConstructorFor inductId params fields →
    eligible inductId →
    args.size = params.toNat + fields.toNat →
    TrAppSpine world.venv uvars world.nameOf trProj Delta
      (.const ctorId levels info) args.toList sourceV →
    (∀ field, field < fields.toNat →
      TrKExprS world.venv uvars world.nameOf trProj Delta
        args[params.toNat + field]! (fieldV field)) →
    world.venv.HasType uvars Delta.toCtx baseV baseTyV →
    world.venv.HasType uvars Delta.toCtx sourceV sourceTyV →
    world.venv.IsDefEqU uvars Delta.toCtx baseTyV sourceTyV →
    FinalWhnfStructEtaLaw trProj world uvars Delta inductId fields.toNat
      fieldV baseV sourceV

/-- Finite generated-projection footprint for the exact constructor source
selected by structure eta. -/
def FinalWhnfStructEtaGeneratedSupport (world : VerifyWorld)
    (support : RunSupport) (eligible : KId .anon → Prop) : Prop :=
  ∀ {source : KExpr .anon} {ctorId inductId : KId .anon}
      {levels : Array (KUniv .anon)} {info : ExprInfo .anon}
      {args : Array (KExpr .anon)} {entry : KConst .anon}
      {params fields : UInt64} {base : KExpr .anon},
    support source →
    source.collectSpine = (.const ctorId levels info, args) →
    world.catalog ctorId = some entry →
    entry.IsStructureConstructorFor inductId params fields →
    eligible inductId →
    support base →
    ∀ field, field < fields.toNat →
      support (KExpr.mkPrj inductId field.toUInt64 base)

/-- Complete run-scoped resources used by the outer structure-eta proof. -/
structure FinalWhnfStructEtaResources (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (eligible : KId .anon → Prop) : Prop where
  whnfTheory : WhnfTheory trProj world uvars
  etaTheory : FinalWhnfStructEtaTheory trProj world eligible
  collision : support.CollisionFree
  noDelta : DefEqReduction.WFAt layer semantics trProj world support uvars
    whnfNoDelta
  classifier : FinalWhnfStructLike.WFAt layer semantics trProj world support
    uvars eligible
  lazyFault : ∀ {Delta : KVLCtx},
    TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
  references : RecM.TrustedReferences world support
  projectionValues : ProjectionValueSupport support
  spines : ProjectionSpineSupport support
  generated : FinalWhnfStructEtaGeneratedSupport world support eligible

private theorem toNat_toUInt64_structureEta (n : Nat) :
    n.toUInt64.toNat = n % UInt64.size := by
  unfold Nat.toUInt64
  rfl

/-- Caught no-delta normalization either returns the verified reduct or the
original source with reflexive Theory equality. -/
theorem normalizeEtaStructSource_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {source : KExpr .anon} {sourceV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hnoDelta : DefEqReduction.WFAt layer semantics trProj world support
      uvars whnfNoDelta)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (normalizeEtaStructSource source)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result) := by
  unfold normalizeEtaStructSource
  apply RecM.WF.bind <| tryOptional_wf <| RecM.WF.withInv <|
    hnoDelta hsourceSupport hsource
  intro reduced afterWhnf hreduced
  cases reduced with
  | some reduced =>
      simp only
      rcases hreduced with ⟨_, hreduced⟩
      exact RecM.WF.pure fun _ => hreduced
  | none =>
      simp only
      exact RecM.WF.pure fun hI =>
        ⟨hsourceSupport, sourceV, hsource,
          Lean4Lean.VEnv.IsDefEqU.refl (theory.exprWF hI.2.1 hsource)⟩

/-- Exhaust the size check, structure classifier, both caught inference
calls, inferred-type comparison, and the verified structure-eta tail for one
exact constructor declaration. -/
theorem tryEtaStructAfterConstructor_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {eligible : KId .anon → Prop}
    {Delta : KVLCtx} {state : TcState .anon}
    {source base : KExpr .anon} {sourceV baseV : VExpr}
    {ctorId inductId : KId .anon} {levels : Array (KUniv .anon)}
    {info : ExprInfo .anon} {args : Array (KExpr .anon)}
    {entry : KConst .anon} {params fields : UInt64}
    (resources : FinalWhnfStructEtaResources layer semantics trProj world
      support uvars eligible)
    (hsourceSupport : support source) (hbaseSupport : support base)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hbase : TrKExprS world.venv uvars world.nameOf trProj Delta base baseV)
    (hspine : source.collectSpine = (.const ctorId levels info, args))
    (htrusted : world.trusted ctorId)
    (hcatalog : world.catalog ctorId = some entry)
    (hshape : entry.IsStructureConstructorFor inductId params fields) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryEtaStructAfterConstructor inductId params.toNat fields.toNat
        base source args)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx baseV sourceV) := by
  classical
  unfold tryEtaStructAfterConstructor
  cases hsize : (args.size != params.toNat + fields.toNat) with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ htrue => by contradiction
  | false =>
      have hsizeEq : args.size = params.toNat + fields.toNat := by
        exact eq_of_beq
          (show (args.size == params.toNat + fields.toNat) = true by
            simpa using hsize)
      simp only [Bool.false_eq_true, if_false]
      apply RecM.WF.bind resources.classifier
      intro structLike afterClassifier hstructLike
      cases structLike with
      | false =>
          simp only [Bool.not_false, if_true]
          exact RecM.WF.pure fun _ htrue => by contradiction
      | true =>
          have heligible : eligible inductId := hstructLike rfl
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          apply RecM.WF.bind
            (tryOptionalInferOnlyCall_wf hsourceSupport hsource)
          intro inferredSource afterSourceType hinferredSource
          cases inferredSource with
          | none =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction
          | some sourceTy =>
              rcases hinferredSource with
                ⟨hsourceTySupport, sourceTyV, hsourceTyTr, hsourceType⟩
              obtain ⟨sourceTyCoreV, hsourceTyCoreTr,
                hsourceTyCoreEq⟩ := hsourceTyTr
              simp only
              apply RecM.WF.bind
                (tryOptionalInferOnlyCall_wf hbaseSupport hbase)
              intro inferredBase afterBaseType hinferredBase
              cases inferredBase with
              | none =>
                  simp only
                  exact RecM.WF.pure fun _ htrue => by contradiction
              | some baseTy =>
                  rcases hinferredBase with
                    ⟨hbaseTySupport, baseTyV, hbaseTyTr, hbaseType⟩
                  obtain ⟨baseTyCoreV, hbaseTyCoreTr, hbaseTyCoreEq⟩ :=
                    hbaseTyTr
                  simp only
                  apply RecM.WF.bind <| RecM.WF.withInv <|
                    isDefEqCall_wf hbaseTySupport hsourceTySupport
                      hbaseTyCoreTr hsourceTyCoreTr
                  intro typesEqual afterTypeEquality htypesEqual
                  rcases htypesEqual with ⟨hITypeEquality, htypesEqual⟩
                  cases typesEqual with
                  | false =>
                      simp only [Bool.not_false, if_true]
                      exact RecM.WF.pure fun _ htrue => by contradiction
                  | true =>
                      simp only [Bool.not_true, Bool.false_eq_true,
                        if_false]
                      have hDelta : KVLCtx.WF world.venv uvars Delta :=
                        hITypeEquality.2.1.wf
                      have hbaseCoreType : world.venv.HasType uvars
                          Delta.toCtx baseV baseTyCoreV :=
                        hbaseType.defeqU_r world.venvWF hDelta
                          hbaseTyCoreEq.symm
                      have hsourceCoreType : world.venv.HasType uvars
                          Delta.toCtx sourceV sourceTyCoreV :=
                        hsourceType.defeqU_r world.venvWF hDelta
                          hsourceTyCoreEq.symm
                      have hspineSupport :=
                        resources.spines hsourceSupport hspine
                      have hspineTr :=
                        trAppSpine_of_collectSpine hsource hspine
                      have hfieldMem : ∀ field, field < fields.toNat →
                          args[params.toNat + field]! ∈ args.toList := by
                        intro field hlt
                        have hidx : params.toNat + field < args.size := by
                          rw [hsizeEq]
                          omega
                        have hget :
                            args[params.toNat + field]? =
                              some args[params.toNat + field]! := by
                          rw [getElem?_pos args (params.toNat + field) hidx,
                            getElem!_pos args (params.toNat + field) hidx]
                        exact Array.mem_toList_iff.mpr
                          (Array.mem_of_getElem? hget)
                      have hfieldSupport : ∀ field,
                          field < fields.toNat →
                          support args[params.toNat + field]! := by
                        intro field hlt
                        exact hspineSupport.2 _ (hfieldMem field hlt)
                      have hfieldWitness : ∀ field,
                          field < fields.toNat →
                          ∃ fieldV,
                            TrKExprS world.venv uvars world.nameOf trProj
                              Delta args[params.toNat + field]! fieldV := by
                        intro field hlt
                        obtain ⟨fieldV, _, _, hfieldTr⟩ :=
                          hspineTr.argument (hfieldMem field hlt)
                        exact ⟨fieldV, hfieldTr⟩
                      let fieldV : Nat → VExpr := fun field =>
                        if hlt : field < fields.toNat then
                          Classical.choose (hfieldWitness field hlt)
                        else baseV
                      have hfieldTr : ∀ field, field < fields.toNat →
                          TrKExprS world.venv uvars world.nameOf trProj Delta
                            args[params.toNat + field]! (fieldV field) := by
                        intro field hlt
                        simp only [fieldV, dif_pos hlt]
                        exact Classical.choose_spec
                          (hfieldWitness field hlt)
                      obtain ⟨structName, projectedV, hname, hprojection⟩ :=
                        resources.etaTheory.projections hspine hcatalog hshape
                          heligible hbase
                      have hgenerated : ∀ field, field < fields.toNat →
                          support
                            (KExpr.mkPrj inductId field.toUInt64 base) :=
                        resources.generated hsourceSupport hspine hcatalog
                          hshape heligible hbaseSupport
                      have hfieldIndex : ∀ field, field < fields.toNat →
                          field.toUInt64.toNat = field := by
                        intro field hlt
                        rw [toNat_toUInt64_structureEta]
                        exact Nat.mod_eq_of_lt
                          (Nat.lt_trans hlt fields.toNat_lt_size)
                      have heta : FinalWhnfStructEtaLaw trProj world uvars
                          Delta inductId fields.toNat fieldV baseV sourceV :=
                        resources.etaTheory.eta hspine htrusted hcatalog
                          hshape heligible hsizeEq hspineTr hfieldTr
                          hbaseCoreType hsourceCoreType (htypesEqual rfl)
                      exact tryEtaStructAfterTypes_wf resources.whnfTheory
                        resources.collision resources.noDelta
                        resources.projectionValues hbaseSupport hbase
                        hfieldSupport hfieldTr structName hname hgenerated
                        (fun field hlt => by
                          rw [hfieldIndex field hlt]
                          exact hprojection field hlt)
                        hfieldIndex heta

/-- Exhaust the actual constructor-head view and lazy declaration lookup.
Only the concrete `.ctor` result reaches the typed comparison theorem; every
other syntax or catalog shape is a conservative negative answer. -/
theorem tryEtaStructAfterNormalization_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {eligible : KId .anon → Prop}
    {Delta : KVLCtx} {state : TcState .anon}
    {source base : KExpr .anon} {sourceV baseV : VExpr}
    (resources : FinalWhnfStructEtaResources layer semantics trProj world
      support uvars eligible)
    (hsourceSupport : support source) (hbaseSupport : support base)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hbase : TrKExprS world.venv uvars world.nameOf trProj Delta base baseV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryEtaStructAfterNormalization base source)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx baseV sourceV) := by
  unfold tryEtaStructAfterNormalization
  rcases hspine : source.collectSpine with ⟨head, args⟩
  simp only
  cases head with
  | const ctorId levels info =>
      simp only
      have htrusted : world.trusted ctorId :=
        resources.references hsourceSupport
          (collectSpine_const_references hspine)
      apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
        TcM.tryGetConst_loaded_wf resources.lazyFault ctorId state
      intro found afterLookup hfound
      rcases hfound with ⟨hILookup, hloaded⟩
      cases found with
      | none =>
          simp only
          exact RecM.WF.pure fun _ htrue => by contradiction
      | some entry =>
          cases entry <;> simp only
          all_goals first
            | exact RecM.WF.pure fun _ htrue => by contradiction
            | skip
          case ctor name levelParams isUnsafe lvls inductId cidx params
              fields ty =>
            have hcatalog : world.catalog ctorId = some
                (.ctor name levelParams isUnsafe lvls inductId cidx params
                  fields ty) :=
              hILookup.1.core.loaded (hloaded _ rfl)
            have hshape :
                (KConst.ctor name levelParams isUnsafe lvls inductId cidx
                  params fields ty).IsStructureConstructorFor inductId
                    params fields :=
              ⟨rfl, rfl, rfl⟩
            exact tryEtaStructAfterConstructor_wf resources hsourceSupport
              hbaseSupport hsource hbase hspine htrusted hcatalog hshape
  | var _ _ _ =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | fvar _ _ _ =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | sort _ _ =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | app _ _ _ =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | lam _ _ _ _ _ =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | all _ _ _ _ _ =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | letE _ _ _ _ _ _ =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | prj _ _ _ _ =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | nat _ _ _ =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | str _ _ _ =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction

/-- Compose caught normalization with the constructor dispatcher and
transport the successful equality back to the original left operand. -/
theorem tryEtaStruct_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {eligible : KId .anon → Prop}
    {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (resources : FinalWhnfStructEtaResources layer semantics trProj world
      support uvars eligible)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryEtaStruct left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold tryEtaStruct
  apply RecM.WF.bind <|
    normalizeEtaStructSource_wf resources.whnfTheory resources.noDelta
      hleftSupport hleft
  intro normalized afterNormalization hnormalized
  rcases hnormalized with
    ⟨hnormalizedSupport, normalizedV, hnormalizedTr, hleftNormalized⟩
  apply RecM.WF.mono <| RecM.WF.withInv <|
    tryEtaStructAfterNormalization_wf resources hrightSupport
      hnormalizedSupport hright hnormalizedTr
  · intro answer final hanswer htrue
    exact hleftNormalized.trans world.venvWF hanswer.1.2.1.wf
      (hanswer.2 htrue)
  · intro _ _ _
    trivial

/-- The bidirectional production wrapper is sound in both eta orientations;
the reverse success is transported by Theory symmetry. -/
theorem tryDefEqWhnfStructEta_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {eligible : KId .anon → Prop}
    {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (resources : FinalWhnfStructEtaResources layer semantics trProj world
      support uvars eligible)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfStructEta left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold tryDefEqWhnfStructEta
  apply RecM.WF.bind <|
    tryEtaStruct_wf resources hleftSupport hrightSupport hleft hright
  intro forward afterForward hforward
  cases forward with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ _ => hforward rfl
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply RecM.WF.bind <|
        tryEtaStruct_wf resources hrightSupport hleftSupport hright hleft
      intro reverse afterReverse hreverse
      cases reverse with
      | true =>
          simp only [if_true]
          exact RecM.WF.pure fun _ _ => (hreverse rfl).symm
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact RecM.WF.pure fun _ => trivial

namespace TryDefEqWhnfStructEta

/-- Package the concrete outer proof at the final-WHNF phase contract. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {eligible : KId .anon → Prop}
    (resources : FinalWhnfStructEtaResources layer semantics trProj world
      support uvars eligible) :
    TryDefEqWhnfStructEta.WFAt layer semantics trProj world support
      uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport hleft
    hright
  exact tryDefEqWhnfStructEta_wf resources hleftSupport hrightSupport hleft
    hright

end TryDefEqWhnfStructEta

end RecM

end Ix.Tc
