import Ix.Tc.Verify.Check.DefEqPropositionPolicy

/-!
# Operational policy for DefEq eta phases

This module covers lambda eta construction and the complete structure-eta
pipeline, including caught normalization failures, declaration ingress,
infer-only type comparison, finite projection-field recursion, and the
common-base scan.
-/

namespace Ix.Tc

namespace RecM

theorem compareEtaExpansion_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (target source : KExpr .anon) (name : Mode.anon.F Name)
    (binderInfo : Mode.anon.F Lean.BinderInfo) (type : KExpr .anon) :
    ((compareEtaExpansion target source name binderInfo type).run
      methods).PreservesInferOnly := by
  unfold compareEtaExpansion
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.PreservesInferOnly.bind
    (TcM.PreservesInferOnly.runIntern (lift source 1 0))
  intro lifted
  apply TcM.PreservesInferOnly.bind
    (intern_preservesInferOnly (.mkVar 0 anonN))
  intro argument
  apply TcM.PreservesInferOnly.bind
    (intern_preservesInferOnly (.mkApp lifted argument))
  intro body
  apply TcM.PreservesInferOnly.bind
    (intern_preservesInferOnly (.mkLam name binderInfo type body))
  intro abstraction
  exact isDefEqCall_preservesInferOnly hmethods target abstraction

theorem tryEtaExpansionAfterGuard_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (target source : KExpr .anon) :
    ((tryEtaExpansionAfterGuard target source).run
      methods).PreservesInferOnly := by
  unfold tryEtaExpansionAfterGuard
  refine bind_preservesInferOnly
    (tryQuestion_preservesInferOnly
      (inferOnlyCall_preservesInferOnly hmethods source)) ?_
  intro typeResult
  cases typeResult with
  | none => exact TcM.PreservesInferOnly.pure false
  | some type =>
      simp only
      refine bind_preservesInferOnly
        (tryQuestion_preservesInferOnly (hwhnf type)) ?_
      intro normalizedResult
      cases normalizedResult with
      | none => exact TcM.PreservesInferOnly.pure false
      | some normalized =>
          cases normalized with
          | all name binderInfo domain body info =>
              exact compareEtaExpansion_preservesInferOnly hmethods target
                source name binderInfo domain
          | var | fvar | sort | const | app | lam | letE | prj | nat | str =>
              exact TcM.PreservesInferOnly.pure false

theorem tryEtaExpansion_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (target source : KExpr .anon) :
    ((tryEtaExpansion target source).run methods).PreservesInferOnly := by
  cases target <;> cases source <;> simp only [tryEtaExpansion, pure_bind]
  all_goals first
    | exact TcM.PreservesInferOnly.pure false
    | exact tryEtaExpansionAfterGuard_preservesInferOnly hmethods hwhnf _ _

theorem normalizeEtaStructSource_preservesInferOnly
    {methods : Methods .anon}
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (source : KExpr .anon) :
    ((normalizeEtaStructSource source).run
      methods).PreservesInferOnly := by
  unfold normalizeEtaStructSource
  refine bind_preservesInferOnly
    (tryQuestion_preservesInferOnly (hnoDelta source)) ?_
  intro result
  cases result <;> exact TcM.PreservesInferOnly.pure _

/-- The common-base scan is structurally recursive in its remaining field
count.  Its helper seams are unfolded here so that both caught-normalization
outcomes are covered by the same induction hypothesis. -/
theorem etaExpansionBaseLoop_preservesInferOnly
    {methods : Methods .anon}
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (inductiveId : KId .anon) (numParams : Nat)
    (arguments : Array (KExpr .anon)) : ∀ fuel field base,
    ((etaExpansionBaseLoop inductiveId numParams arguments fuel field base).run
      methods).PreservesInferOnly
  | 0, field, base => by
      rw [etaExpansionBaseLoop]
      exact TcM.PreservesInferOnly.pure base
  | fuel + 1, field, base => by
      rw [etaExpansionBaseLoop]
      refine bind_preservesInferOnly
        (hnoDelta arguments[numParams + field]!) ?_
      intro normalizedField
      cases normalizedField with
      | prj projectionId projectionIndex value info =>
          cases hshape :
              (projectionId.addr != inductiveId.addr ||
                projectionIndex.toNat != field) with
          | true =>
            simp only [hshape, if_true]
            exact TcM.PreservesInferOnly.pure none
          | false =>
            simp only [hshape, Bool.false_eq_true, if_false, pure_bind]
            unfold etaExpansionBaseAfterProjection
            refine bind_preservesInferOnly
              (tryQuestion_preservesInferOnly (hnoDelta value)) ?_
            intro normalizedValueResult
            unfold etaExpansionBaseAfterValue
            cases normalizedValueResult with
            | some normalizedValue =>
                cases base with
                | none =>
                    exact etaExpansionBaseLoop_preservesInferOnly hnoDelta
                      inductiveId numParams arguments fuel (field + 1)
                      (some normalizedValue)
                | some prior =>
                    cases hsame : (prior.addr != normalizedValue.addr) with
                    | true =>
                      simp only [hsame, if_true]
                      exact TcM.PreservesInferOnly.pure none
                    | false =>
                      simp only [hsame, Bool.false_eq_true, if_false,
                        pure_bind]
                      exact etaExpansionBaseLoop_preservesInferOnly hnoDelta
                        inductiveId numParams arguments fuel (field + 1)
                        (some prior)
            | none =>
                cases base with
                | none =>
                    exact etaExpansionBaseLoop_preservesInferOnly hnoDelta
                      inductiveId numParams arguments fuel (field + 1)
                      (some value)
                | some prior =>
                    cases hsame : (prior.addr != value.addr) with
                    | true =>
                      simp only [hsame, if_true]
                      exact TcM.PreservesInferOnly.pure none
                    | false =>
                      simp only [hsame, Bool.false_eq_true, if_false,
                        pure_bind]
                      exact etaExpansionBaseLoop_preservesInferOnly hnoDelta
                        inductiveId numParams arguments fuel (field + 1)
                        (some prior)
      | var | fvar | sort | const | app | lam | all | letE | nat | str =>
          exact TcM.PreservesInferOnly.pure none

theorem etaExpansionBaseAfterValue_preservesInferOnly
    {methods : Methods .anon}
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (inductiveId : KId .anon) (numParams : Nat)
    (arguments : Array (KExpr .anon)) (fuel field : Nat)
    (base : Option (KExpr .anon)) (value : KExpr .anon) :
    ((etaExpansionBaseAfterValue inductiveId numParams arguments fuel field
      base value).run methods).PreservesInferOnly := by
  unfold etaExpansionBaseAfterValue
  cases base with
  | none =>
      exact etaExpansionBaseLoop_preservesInferOnly hnoDelta inductiveId
        numParams arguments fuel (field + 1) (some value)
  | some prior =>
      cases hsame : (prior.addr != value.addr) with
      | true =>
        simp only [hsame, if_true]
        exact TcM.PreservesInferOnly.pure none
      | false =>
        simp only [hsame, Bool.false_eq_true, if_false, pure_bind]
        exact etaExpansionBaseLoop_preservesInferOnly hnoDelta inductiveId
          numParams arguments fuel (field + 1) (some prior)

theorem etaExpansionBaseAfterProjection_preservesInferOnly
    {methods : Methods .anon}
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (inductiveId : KId .anon) (numParams : Nat)
    (arguments : Array (KExpr .anon)) (fuel field : Nat)
    (base : Option (KExpr .anon)) (value : KExpr .anon) :
    ((etaExpansionBaseAfterProjection inductiveId numParams arguments fuel
      field base value).run methods).PreservesInferOnly := by
  unfold etaExpansionBaseAfterProjection
  refine bind_preservesInferOnly
    (tryQuestion_preservesInferOnly (hnoDelta value)) ?_
  intro result
  cases result with
  | some normalized =>
      exact etaExpansionBaseAfterValue_preservesInferOnly hnoDelta inductiveId
        numParams arguments fuel field base normalized
  | none =>
      exact etaExpansionBaseAfterValue_preservesInferOnly hnoDelta inductiveId
        numParams arguments fuel field base value

theorem etaExpansionBase_preservesInferOnly
    {methods : Methods .anon}
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (inductiveId : KId .anon) (numParams numFields : Nat)
    (arguments : Array (KExpr .anon)) :
    ((etaExpansionBase inductiveId numParams numFields arguments).run
      methods).PreservesInferOnly := by
  unfold etaExpansionBase
  exact etaExpansionBaseLoop_preservesInferOnly hnoDelta inductiveId numParams
    arguments numFields 0 none

theorem tryEtaStructFields_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (inductiveId : KId .anon) (numParams : Nat)
    (target : KExpr .anon) (arguments : Array (KExpr .anon)) : ∀ fuel field,
    ((tryEtaStructFields inductiveId numParams target arguments fuel field).run
      methods).PreservesInferOnly
  | 0, field => TcM.PreservesInferOnly.pure true
  | fuel + 1, field => by
      rw [tryEtaStructFields]
      refine bindIntern_preservesInferOnly
        (.mkPrj inductiveId field.toUInt64 target) ?_
      intro projection
      refine bind_preservesInferOnly
        (isDefEqCall_preservesInferOnly hmethods projection
          arguments[numParams + field]!) ?_
      intro equal
      cases equal with
      | false => exact TcM.PreservesInferOnly.pure false
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          exact tryEtaStructFields_preservesInferOnly hmethods inductiveId
            numParams target arguments fuel (field + 1)

theorem tryEtaStructAfterTypes_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (inductiveId : KId .anon) (numParams numFields : Nat)
    (target : KExpr .anon) (arguments : Array (KExpr .anon)) :
    ((tryEtaStructAfterTypes inductiveId numParams numFields target arguments).run
      methods).PreservesInferOnly := by
  unfold tryEtaStructAfterTypes
  refine bind_preservesInferOnly
    (etaExpansionBase_preservesInferOnly hnoDelta inductiveId numParams
      numFields arguments) ?_
  intro baseResult
  cases baseResult with
  | none =>
      exact tryEtaStructFields_preservesInferOnly hmethods inductiveId
        numParams target arguments numFields 0
  | some base =>
      simp only
      refine bind_preservesInferOnly
        (isDefEqCall_preservesInferOnly hmethods target base) ?_
      intro equal
      cases equal with
      | true => exact TcM.PreservesInferOnly.pure true
      | false =>
          simp only [Bool.false_eq_true, if_false, pure_bind]
          exact tryEtaStructFields_preservesInferOnly hmethods inductiveId
            numParams target arguments numFields 0

theorem tryEtaStructAfterConstructor_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (inductiveId : KId .anon) (numParams numFields : Nat)
    (target source : KExpr .anon) (arguments : Array (KExpr .anon)) :
    ((tryEtaStructAfterConstructor inductiveId numParams numFields target
      source arguments).run methods).PreservesInferOnly := by
  unfold tryEtaStructAfterConstructor
  split
  · exact TcM.PreservesInferOnly.pure false
  · refine bind_preservesInferOnly
      (isStructLike_preservesInferOnly hmethods inductiveId) ?_
    intro isStructure
    cases isStructure with
    | false => exact TcM.PreservesInferOnly.pure false
    | true =>
        simp only [Bool.not_true, Bool.false_eq_true, if_false]
        refine bind_preservesInferOnly
          (tryQuestion_preservesInferOnly
            (inferOnlyCall_preservesInferOnly hmethods source)) ?_
        intro sourceTypeResult
        cases sourceTypeResult with
        | none => exact TcM.PreservesInferOnly.pure false
        | some sourceType =>
            simp only
            refine bind_preservesInferOnly
              (tryQuestion_preservesInferOnly
                (inferOnlyCall_preservesInferOnly hmethods target)) ?_
            intro targetTypeResult
            cases targetTypeResult with
            | none => exact TcM.PreservesInferOnly.pure false
            | some targetType =>
                simp only
                refine bind_preservesInferOnly
                  (isDefEqCall_preservesInferOnly hmethods targetType
                    sourceType) ?_
                intro typesEqual
                cases typesEqual with
                | false => exact TcM.PreservesInferOnly.pure false
                | true =>
                    simp only [Bool.not_true, Bool.false_eq_true, if_false]
                    exact tryEtaStructAfterTypes_preservesInferOnly hmethods
                      hnoDelta inductiveId numParams numFields target arguments

theorem tryEtaStructAfterNormalization_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (target source : KExpr .anon) :
    ((tryEtaStructAfterNormalization target source).run
      methods).PreservesInferOnly := by
  rcases hspine : source.collectSpine with ⟨head, arguments⟩
  unfold tryEtaStructAfterNormalization
  simp only [hspine]
  cases head with
  | const constructorId universes info =>
      refine bindTcM_preservesInferOnly
        (TcM.PreservesInferOnly.tryGetConst constructorId) ?_
      intro declaration
      cases declaration with
      | none => exact TcM.PreservesInferOnly.pure false
      | some declaration =>
          cases declaration with
          | ctor name levelParams isUnsafe levels inductiveId constructorIndex
              params fields type =>
              exact tryEtaStructAfterConstructor_preservesInferOnly hmethods
                hnoDelta inductiveId params.toNat fields.toNat target source
                arguments
          | defn | recr | axio | quot | indc =>
              exact TcM.PreservesInferOnly.pure false
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      exact TcM.PreservesInferOnly.pure false

theorem tryEtaStruct_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (target source : KExpr .anon) :
    ((tryEtaStruct target source).run methods).PreservesInferOnly := by
  unfold tryEtaStruct
  refine bind_preservesInferOnly
    (normalizeEtaStructSource_preservesInferOnly hnoDelta target) ?_
  intro normalized
  exact tryEtaStructAfterNormalization_preservesInferOnly hmethods hnoDelta
    normalized source

end RecM

end Ix.Tc
