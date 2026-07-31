import Ix.Tc.Verify.DefEq.FinalWhnf.ProofTail
import Ix.Tc.Verify.Infer.Constants
import Ix.Tc.Verify.Whnf.StructEta.RecursionClassifier

/-!
# Final-WHNF unit-like equality

The operational classifier is proved exhaustively against the immutable
catalog.  Its semantic conclusion uses one deliberately narrow inductive
law: inhabitants of a type headed by a trusted zero-index inductive with one
nullary constructor are definitionally equal.  Lean4Lean's current
`VEnv.addInduct` interface does not expose that law, so it remains an explicit
construction obligation for the inductive-theory bridge rather than being
inferred from concrete metadata alone.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Constructor metadata accepted by production's unit-like shortcut. -/
def KConst.IsNullaryConstructor : KConst .anon → Prop
  | .ctor (fields := fields) .. => fields = 0
  | _ => False

/-- Exact immutable-catalog shape accepted by the unit-like classifier. -/
def KConst.IsUnitLikeInductive (catalog : Catalog) : KConst .anon → Prop
  | .indc (indices := indices) (ctors := ctors) .. =>
      indices = 0 ∧ ctors.size = 1 ∧
        ∃ ctor, catalog ctors[0]! = some ctor ∧ ctor.IsNullaryConstructor
  | _ => False

/-- Semantic inductive law missing from Lean4Lean's current `addInduct`
specification.  It is indexed by the exact trusted catalog shape and by the
actual structurally translated type selected by production. -/
structure FinalWhnfUnitTheory (trProj : RawProjRel)
    (world : VerifyWorld) : Prop where
  unique : ∀ {uvars : Nat} {Delta : KVLCtx}
      {typeExpr : KExpr .anon} {typeV leftV rightV : VExpr}
      {indId : KId .anon} {levels : Array (KUniv .anon)}
      {info : ExprInfo .anon} {args : Array (KExpr .anon)} {entry : KConst .anon},
    typeExpr.collectSpine = (.const indId levels info, args) →
    TrKExprS world.venv uvars world.nameOf trProj Delta typeExpr typeV →
    world.trusted indId →
    world.catalog indId = some entry →
    entry.IsUnitLikeInductive world.catalog →
    world.venv.HasType uvars Delta.toCtx leftV typeV →
    world.venv.HasType uvars Delta.toCtx rightV typeV →
    world.venv.IsDefEqU uvars Delta.toCtx leftV rightV

/-- Run-scoped resources for the concrete unit-like shortcut. -/
structure FinalWhnfUnitResources (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop where
  theory : FinalWhnfUnitTheory trProj world
  references : RecM.TrustedReferences world support
  lazyFault : ∀ {Delta : KVLCtx},
    TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
  whnf : RecM.DefEqDirectWhnf.WFAt layer semantics trProj world support uvars

namespace RecM

/-- A positive classifier result is tied to the exact immutable-catalog
entries returned by both production lookups. -/
theorem isUnitLikeInductive_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {indId : KId .anon}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (isUnitLikeInductive indId)
      (fun answer _ => answer = true →
        ∃ entry, world.catalog indId = some entry ∧
          entry.IsUnitLikeInductive world.catalog) := by
  unfold isUnitLikeInductive
  apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
    TcM.tryGetConst_loaded_wf hfault indId state
  intro found afterInd hfound
  rcases hfound with ⟨hIInd, hloadedInd⟩
  cases found with
  | none =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | some entry =>
      cases entry <;> simp only
      all_goals first
        | exact RecM.WF.pure fun _ htrue => by contradiction
        | skip
      case indc name levelParams lvls params indices isUnsafe block memberIdx
          ty ctors leanAll =>
        cases hshape : (indices != 0 || ctors.size != 1) with
        | true =>
            simp only [if_true]
            exact RecM.WF.pure fun _ htrue => by contradiction
        | false =>
            have hshapeParts := Bool.or_eq_false_iff.mp hshape
            have hindices : indices = 0 := by
              exact eq_of_beq
                (show (indices == 0) = true by simpa using hshapeParts.1)
            have hctors : ctors.size = 1 := by
              exact eq_of_beq
                (show (ctors.size == 1) = true by simpa using hshapeParts.2)
            simp only [Bool.false_eq_true, if_false]
            let ctorId := ctors[0]!
            apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
              TcM.tryGetConst_loaded_wf hfault ctorId afterInd
            intro foundCtor afterCtor hfoundCtor
            rcases hfoundCtor with ⟨hICtor, hloadedCtor⟩
            cases foundCtor with
            | none =>
                simp only
                exact RecM.WF.pure fun _ htrue => by contradiction
            | some ctor =>
                cases ctor <;> simp only
                all_goals first
                  | exact RecM.WF.pure fun _ htrue => by contradiction
                  | skip
                case ctor name levelParams isUnsafe lvls induct cidx params
                    fields ty =>
                  exact RecM.WF.pure fun _ htrue => by
                    have hfields : fields = 0 := eq_of_beq htrue
                    have hindCatalog := hIInd.1.core.loaded
                      (hloadedInd _ rfl)
                    have hctorCatalog := hICtor.1.core.loaded
                      (hloadedCtor _ rfl)
                    exact ⟨_, hindCatalog, hindices, hctors, _,
                      hctorCatalog, hfields⟩

/-- The complete unit-like shortcut is sound against the explicit inductive
law.  All caught inference/WHNF errors and malformed catalog shapes are
conservative negative results. -/
theorem tryDefEqUnit_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (resources : FinalWhnfUnitResources layer semantics trProj world support
      uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqUnit left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold tryDefEqUnit
  apply RecM.WF.bind
    (tryOptionalInferOnlyCall_wf hleftSupport hleft)
  intro inferredLeft afterInferLeft hinferredLeft
  cases inferredLeft with
  | none =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | some leftTy =>
      rcases hinferredLeft with
        ⟨hleftTySupport, leftTyV, hleftTyTr, hleftType⟩
      obtain ⟨leftTyCoreV, hleftTyCoreTr, hleftTyCoreEq⟩ := hleftTyTr
      simp only
      apply RecM.WF.bind <| tryOptional_wf <| RecM.WF.withInv <|
        resources.whnf hleftTySupport hleftTyCoreTr
      intro reducedTy afterWhnf hreducedTy
      cases reducedTy with
      | none =>
          simp only
          exact RecM.WF.pure fun _ htrue => by contradiction
      | some leftTyWhnf =>
          rcases hreducedTy with
            ⟨hIWhnf, hleftTyWhnfSupport, leftTyWhnfV, hleftTyWhnfTr,
              hleftTyReduction⟩
          rcases hspine : leftTyWhnf.collectSpine with ⟨head, args⟩
          simp only [hspine]
          cases head with
          | const indId levels info =>
              simp only
              have htrusted : world.trusted indId :=
                resources.references hleftTyWhnfSupport
                  (collectSpine_const_references hspine)
              apply RecM.WF.bind <|
                isUnitLikeInductive_wf resources.lazyFault
              intro isUnit afterUnit hisUnit
              cases isUnit with
              | false =>
                  simp only [Bool.not_false]
                  exact RecM.WF.pure fun _ htrue => by contradiction
              | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, if_false]
                  obtain ⟨entry, hentry, hshape⟩ := hisUnit rfl
                  apply RecM.WF.bind
                    (tryOptionalInferOnlyCall_wf hrightSupport hright)
                  intro inferredRight afterInferRight hinferredRight
                  cases inferredRight with
                  | none =>
                      simp only
                      exact RecM.WF.pure fun _ htrue => by contradiction
                  | some rightTy =>
                      rcases hinferredRight with
                        ⟨hrightTySupport, rightTyV, hrightTyTr,
                          hrightType⟩
                      obtain ⟨rightTyCoreV, hrightTyCoreTr,
                        hrightTyCoreEq⟩ := hrightTyTr
                      simp only
                      apply RecM.WF.mono <|
                        isDefEqCall_wf hleftTyWhnfSupport hrightTySupport
                          hleftTyWhnfTr hrightTyCoreTr
                      · intro answer final hanswer htrue
                        have hDelta : KVLCtx.WF world.venv uvars Delta :=
                          hIWhnf.2.1.wf
                        have hleftCoreType : world.venv.HasType uvars
                            Delta.toCtx leftV leftTyCoreV :=
                          hleftType.defeqU_r world.venvWF hDelta
                            hleftTyCoreEq.symm
                        have hleftWhnfType : world.venv.HasType uvars
                            Delta.toCtx leftV leftTyWhnfV :=
                          hleftCoreType.defeqU_r world.venvWF hDelta
                            hleftTyReduction
                        have hrightCoreType : world.venv.HasType uvars
                            Delta.toCtx rightV rightTyCoreV :=
                          hrightType.defeqU_r world.venvWF hDelta
                            hrightTyCoreEq.symm
                        have hrightWhnfType : world.venv.HasType uvars
                            Delta.toCtx rightV leftTyWhnfV :=
                          hrightCoreType.defeqU_r world.venvWF hDelta
                            (hanswer htrue).symm
                        exact resources.theory.unique hspine
                          hleftTyWhnfTr htrusted hentry hshape
                          hleftWhnfType hrightWhnfType
                      · intro _ _ _
                        trivial
          | _ =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction

namespace TryDefEqUnit

/-- Package the concrete unit-like shortcut. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (resources : FinalWhnfUnitResources layer semantics trProj world support
      uvars) :
    TryDefEqUnit.WFAt layer semantics trProj world support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact tryDefEqUnit_wf resources hleftSupport hrightSupport hleft hright

end TryDefEqUnit

end RecM

end Ix.Tc
