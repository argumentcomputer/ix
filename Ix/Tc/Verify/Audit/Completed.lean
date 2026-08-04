import Ix.Tc.Verify.Audit.Basic
import Ix.Tc.Verify.Check.Acceptance
import Ix.Tc.Verify.Check.BoundedPipelines
import Ix.Tc.Verify.Check.CheckerEvidence
import Ix.Tc.Verify.Check.FullInferenceApplications
import Ix.Tc.Verify.Check.FullInferenceBinders
import Ix.Tc.Verify.Check.FullInferenceCache
import Ix.Tc.Verify.Check.FullInferenceDispatcher
import Ix.Tc.Verify.Check.FullInferenceProjections
import Ix.Tc.Verify.Check.MemberEvidence
import Ix.Tc.Verify.Check.NatAcceptance
import Ix.Tc.Verify.Check.BlockNatFixture
import Ix.Tc.Verify.Check.PreTranslationScopes
import Ix.Tc.Verify.Check.PositiveFuelSort
import Ix.Tc.Verify.Check.ScopedPositiveFuelCertificate
import Ix.Tc.Verify.Check.SingletonInductive
import Ix.Tc.Verify.Inductive.EnumerationAcceptance
import Ix.Tc.Verify.Check.ProjectionInferencePolicy
import Ix.Tc.Verify.Check.ResetFrame
import Ix.Tc.Verify.Check.SafetyFrame
import Ix.Tc.Verify.Check.PublicStandalone
import Ix.Tc.Verify.Check.PublicBlocks
import Ix.Tc.Verify.Check.ValidatorFrame
import Ix.Tc.Verify.Ctx
import Ix.Tc.Verify.Decl
import Ix.Tc.Verify.DefEq
import Ix.Tc.Verify.DefEq.AcceleratorGates
import Ix.Tc.Verify.DefEq.ApplicationSpine
import Ix.Tc.Verify.DefEq.CacheShell
import Ix.Tc.Verify.DefEq.Closure
import Ix.Tc.Verify.DefEq.DeltaClassification
import Ix.Tc.Verify.DefEq.EqualRankCache
import Ix.Tc.Verify.DefEq.EqualRankPrefix
import Ix.Tc.Verify.DefEq.EqualRankReduction
import Ix.Tc.Verify.DefEq.FinalWhnf.Application
import Ix.Tc.Verify.DefEq.FinalWhnf.Closure
import Ix.Tc.Verify.DefEq.FinalWhnf.Contracts
import Ix.Tc.Verify.DefEq.FinalWhnf.EtaExpansion
import Ix.Tc.Verify.DefEq.FinalWhnf.LetDeclaration
import Ix.Tc.Verify.DefEq.FinalWhnf.NatBridge
import Ix.Tc.Verify.DefEq.FinalWhnf.ProofTail
import Ix.Tc.Verify.DefEq.FinalWhnf.StringExpansion
import Ix.Tc.Verify.DefEq.FinalWhnf.StructuralPrefix
import Ix.Tc.Verify.DefEq.FinalWhnf.StructureEta
import Ix.Tc.Verify.DefEq.FinalWhnf.UnitLike
import Ix.Tc.Verify.DefEq.LazyDelta
import Ix.Tc.Verify.DefEq.LazyDeltaClosure
import Ix.Tc.Verify.DefEq.LazyDeltaIteration
import Ix.Tc.Verify.DefEq.LoopFinish
import Ix.Tc.Verify.DefEq.NatOffset
import Ix.Tc.Verify.DefEq.NatOffsetDecomposition
import Ix.Tc.Verify.DefEq.NatReduction
import Ix.Tc.Verify.DefEq.OneSidedDelta
import Ix.Tc.Verify.DefEq.ProjectionDeltaActive
import Ix.Tc.Verify.DefEq.ProjectionDeltaClosure
import Ix.Tc.Verify.DefEq.ProjectionDeltaEqualRank
import Ix.Tc.Verify.DefEq.ProjectionDeltaFinish
import Ix.Tc.Verify.DefEq.ProjectionDeltaLoop
import Ix.Tc.Verify.DefEq.ProjectionDeltaRank
import Ix.Tc.Verify.DefEq.ProjectionDeltaStep
import Ix.Tc.Verify.DefEq.ProjectionDeltaUnfolding
import Ix.Tc.Verify.DefEq.ProjectionProbe
import Ix.Tc.Verify.DefEq.ProjectionReduction
import Ix.Tc.Verify.DefEq.PropositionClassifier
import Ix.Tc.Verify.DefEq.RankDispatch
import Ix.Tc.Verify.DefEq.SameHeadSpine
import Ix.Tc.Verify.DefEq.SpineArguments
import Ix.Tc.Verify.DefEq.StoppedContinuation
import Ix.Tc.Verify.DefEq.StoppedContinuationClosure
import Ix.Tc.Verify.DefEq.StructuralCongruence
import Ix.Tc.Verify.Driver.Fixtures
import Ix.Tc.Verify.Driver.BooleanAcceptance
import Ix.Tc.Verify.Driver.SupportedAcceptanceFixtures
import Ix.Tc.Verify.Execution
import Ix.Tc.Verify.Frame
import Ix.Tc.Verify.Infer.CacheSoundness
import Ix.Tc.Verify.InferDefEq.Closure
import Ix.Tc.Verify.Inductive.Certificate
import Ix.Tc.Verify.Inductive.AliasFormerAdmission
import Ix.Tc.Verify.Inductive.AliasRecAdmission
import Ix.Tc.Verify.Inductive.AnnotatedPiCertificate
import Ix.Tc.Verify.Inductive.AnnotatedPiAdmission
import Ix.Tc.Verify.Inductive.EliminationBreadthFixture
import Ix.Tc.Verify.Inductive.MutualBlockCertificate
import Ix.Tc.Verify.Inductive.MutualFamilyAdmission
import Ix.Tc.Verify.Inductive.IndexedRecursiveCertificate
import Ix.Tc.Verify.Inductive.RecursivePiCertificate
import Ix.Tc.Verify.Inductive.RecursivePiAdmission
import Ix.Tc.Verify.Inductive.IndexedRecursiveAcceptance
import Ix.Tc.Verify.Inductive.IndexedConstructorValidation
import Ix.Tc.Verify.Inductive.SpecializationIdentity
import Ix.Tc.Verify.Inductive.GeneratedRecursorMetadata
import Ix.Tc.Verify.Inductive.GeneratedRecursorAcceptance
import Ix.Tc.Verify.Inductive.GeneratedRecursorAcceptanceClosure
import Ix.Tc.Verify.Inductive.GeneratedRecursorAdmission
import Ix.Tc.Verify.Inductive.IndexedProducerClosure
import Ix.Tc.Verify.Inductive.GeneratedRecursorCheckerFixture
import Ix.Tc.Verify.Inductive.GeneratedRecursorCommitFixture
import Ix.Tc.Verify.Inductive.GeneratedRecursorComparison
import Ix.Tc.Verify.Inductive.GeneratedRecursorRuleFixture
import Ix.Tc.Verify.Inductive.GeneratedRecursorSelection
import Ix.Tc.Verify.Inductive.GeneratedRecursorSemantics
import Ix.Tc.Verify.Inductive.GeneratedRecursorTypeClosure
import Ix.Tc.Verify.Inductive.GeneratedRecursorTypeFixture
import Ix.Tc.Verify.Inductive.NestedAuxiliaryExpansion
import Ix.Tc.Verify.Inductive.NestedAdmission
import Ix.Tc.Verify.Inductive.NestedConstructorValidation
import Ix.Tc.Verify.Inductive.NestedRecursiveFixture
import Ix.Tc.Verify.Inductive.NestedRecursorAdmission
import Ix.Tc.Verify.Inductive.OccurrenceClosure
import Ix.Tc.Verify.Inductive.PositivityTraceAdapter
import Ix.Tc.Verify.Inductive.RecursivePositivityTraversal
import Ix.Tc.Verify.Ingress.LiteralBlobs
import Ix.Tc.Verify.Ingress.SerializedBoolean
import Ix.Tc.Verify.InstL
import Ix.Tc.Verify.Whnf.Closure
import Ix.Tc.Verify.Knot
import Ix.Tc.Verify.NatFixture
import Ix.Tc.Verify.Projection.ConcreteFixture
import Ix.Tc.Verify.Run
import Ix.Tc.Verify.RecursiveMethods.Closure
import Ix.Tc.Verify.RecursiveMethods.FiniteSupportBoundary
import Ix.Tc.Verify.RecursiveMethods.Public
import Ix.Tc.Verify.Support
import Ix.Tc.Verify.Totalization
import Ix.Tc.Verify.Whnf
import Ix.Tc.Verify.World

/-!
# Trust manifest for the completed `Ix.Tc.Verify` proof surface

These are the current completed foundations and reusable semantic interfaces
that later C1--C3 roots will consume.  A new headline theorem must be added here
when it becomes part of that exported proof surface.  The temporary C1/C2
statement skeletons are audited separately in `Audit/Statements.lean`
because their opaque relation names intentionally collide with the concrete
relations imported here.

The entries are deliberately repetitive at the root level: a change in the
transitive trust boundary of any one interface should produce a focused CI
failure.  Shared arrays below are only labels for exactly repeated sets.
-/

namespace Ix.Tc.Verify.Audit.Completed

open Ix.Tc.Verify.Audit

private def standard : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def standardWithoutChoice : Array Lean.Name :=
  #[``propext, ``Quot.sound]

private def standardWithoutQuot : Array Lean.Name :=
  #[``propext, ``Classical.choice]

private def propextOnly : Array Lean.Name := #[``propext]

/- The executable `AnnotatedPi` replay in the pinned Lean4Lean fork crosses
its verified wrappers for Lean's pointer-aware expression implementation.
Keep that nonlogical upstream footprint distinct from `standard`: these are
not ordinary logical axioms and must not become globally permitted. -/
private def annotatedPiUpstreamAxioms : Array Lean.Name := #[
  ``Lean4Lean.ptrEqConstantInfo_eq,
  ``Lean4Lean.ptrEqExpr_eq,
  ``Lean.Expr.abstractRange_eq,
  ``Lean.Expr.abstract_eq,
  ``Lean.Expr.eqv_eq,
  ``Lean.Expr.hasLooseBVar_eq,
  ``Lean.Expr.instantiate1_eq,
  ``Lean.Expr.instantiateRange_eq,
  ``Lean.Expr.instantiateRevRange_eq,
  ``Lean.Expr.instantiateRev_eq,
  ``Lean.Expr.instantiate_eq,
  ``Lean.Expr.looseBVarRange_eq,
  ``Lean.Expr.lowerLooseBVars_eq,
  ``Lean.Expr.mkAppData_eq,
  ``Lean.Expr.mkData_eq,
  ``Lean.Expr.replace_eq,
  ``Lean.Level.hasMVar_eq,
  ``Lean.Level.hasParam_eq,
  ``Lean.Level.isExplicitSubsumedAux_eq,
  ``Lean.Level.instLawfulBEqLevel,
  ``Lean.Level.normalize_eq,
  ``Lean.PersistentArray.toList'_push,
  ``Lean.PersistentHashMap.findAux_isSome,
  ``Lean.Syntax.structEq_eq,
  ``Lean.PersistentHashMap.WF.find?_eq,
  ``Lean.PersistentHashMap.WF.toList'_insert,
  ``Std.TreeMap.all_eq_all_toList
]

/- Exact direct `sorryAx` frontier inherited from Lean4Lean's executable
candidate-normalization proof.  Unlike the earlier closed-form fixtures,
`AnnotatedPi` exercises the verified implementation path far enough to reach
the currently declared projection/typechecker proof debt. -/
private def annotatedPiUpstreamDebt : Array Lean.Name := #[
  ``Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
  ``Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
  ``Lean4Lean.VEnv.IsDefEqU.sort_inv,
  ``Lean4Lean.VEnv.IsDefEqU.weakN_iff,
  ``Lean4Lean.VEnv.WF.registeredStructureHeadInversion,
  ``Lean4Lean.TypeChecker.Inner.reduceRecursor.WF
]

/- `AliasFormer` reaches the same executable normalization boundary as
`AnnotatedPi`: the former unfolds a reducible family-result alias, while the
latter unfolds a constructor-domain annotation.  Keep separate aliases so
the audit will expose either fixture if their upstream footprints diverge. -/
private def aliasFormerUpstreamAxioms : Array Lean.Name :=
  annotatedPiUpstreamAxioms

private def aliasFormerUpstreamDebt : Array Lean.Name :=
  annotatedPiUpstreamDebt.push
    ``Lean4Lean.InductiveReplayFixtures.aliasFormerAlignmentRun

/- `AliasRec` reaches the same executable normalization boundary while
unfolding a reducible wrapper around a recursive constructor field.  Keep its
allowances separately named so the exact-root audit detects any divergence. -/
private def aliasRecUpstreamAxioms : Array Lean.Name :=
  annotatedPiUpstreamAxioms

private def aliasRecUpstreamDebt : Array Lean.Name :=
  annotatedPiUpstreamDebt

private def blake3Native : Array Lean.Name := #[
  nativeAxiom `Blake3
    `Blake3.HasherOps.hash._native.native_decide.ax_1
]

private def expressionNative : Array Lean.Name := blake3Native.push
  (nativeAxiom `Ix.Tc.Expr
    `Ix.Tc.KExpr.mkVar._native.native_decide.ax_1)

private def levelNative : Array Lean.Name := expressionNative.push
  (nativeAxiom `Ix.Tc.Level
    `Ix.Tc.KUniv.mkSucc._native.native_decide.ax_1)

private def occurrenceValidationNative : Array Lean.Name := blake3Native.push
  (nativeAxiom `Ix.Tc.Level
    `Ix.Tc.KUniv.mkSucc._native.native_decide.ax_1)

private def specializationIdentityNative : Array Lean.Name :=
  occurrenceValidationNative.push
    (nativeAxiom `Ix.Tc.Verify.Inductive.SpecializationIdentity
      `Ix.Tc.SpecializationIdentityFixture.semanticUniverseEquality_does_not_collapse_specializationNative._native.native_decide.ax_1_1)

private def univOnlyNative : Array Lean.Name := #[
  nativeAxiom `Ix.Tc.Level
    `Ix.Tc.KUniv.mkSucc._native.native_decide.ax_1
]

private def nameDecideNative : Lean.Name :=
  nativeAxiom `Ix.Environment
    `Ix.Name.mkStr._native.native_decide.ax_1

private def nameNative : Array Lean.Name := levelNative.push nameDecideNative

private def expressionNameNative : Array Lean.Name :=
  expressionNative.push nameDecideNative

private def canonicalPrimitivesNative : Array Lean.Name :=
  blake3Native.push nameDecideNative

private def ctxAddrNative : Lean.Name :=
  nativeAxiom `Ix.Tc.Monad
    `Ix.Tc.TcM.ctxAddrForLbrUncached._native.native_decide.ax_3

private def blake3ContextNative : Array Lean.Name :=
  blake3Native.push ctxAddrNative

private def contextNative : Array Lean.Name :=
  expressionNative.push ctxAddrNative

private def inferNative : Array Lean.Name :=
  levelNative.push ctxAddrNative

private def nameContextNative : Array Lean.Name :=
  nameNative.push ctxAddrNative

private def canonicalPrimitivesContextNative : Array Lean.Name :=
  canonicalPrimitivesNative.push ctxAddrNative

private def natAddNeSuccNative : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.NatFixture
    `Ix.Tc.AmbientNat.natAdd_ne_natSucc._native.native_decide.ax_1_1

private def natAddNeBeqNative : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.NatFixture
    `Ix.Tc.AmbientNat.natAdd_ne_natBeq._native.native_decide.ax_1_1

private def natAddNeBleNative : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.NatFixture
    `Ix.Tc.AmbientNat.natAdd_ne_natBle._native.native_decide.ax_1_1

private def natReductionNative : Array Lean.Name :=
  (((contextNative.push nameDecideNative).push natAddNeSuccNative).push
    natAddNeBeqNative).push natAddNeBleNative

private def natSuffixReductionNative : Array Lean.Name :=
  ((contextNative.push nameDecideNative).push natAddNeBeqNative).push
    natAddNeBleNative

private def natSuffixCertificateNative : Array Lean.Name :=
  ((expressionNative.push nameDecideNative).push natAddNeBeqNative).push
    natAddNeBleNative

private def natBranchOrderNative : Array Lean.Name :=
  (((inferNative.push nameDecideNative).push natAddNeSuccNative).push
    natAddNeBeqNative).push natAddNeBleNative

private def inductiveNative : Array Lean.Name := (inferNative.push
  (nativeAxiom `Ix.Environment
    `Ix.Name.mkStr._native.native_decide.ax_1)).push
  (nativeAxiom `Ix.Tc.Inductive
    `Ix.Tc.RecM.canonicalAuxOrder._native.native_decide.ax_9)

/- Mutual-block fixtures use many small closed `native_decide` facts.  Build
their exact private names structurally so the audit stays reviewable while
still enumerating every generated axiom. -/
private def mutualNativeUserName (decl : String) (index : Nat) : Lean.Name :=
  Lean.Name.str
    (Lean.Name.str
      (Lean.Name.str
        (Lean.Name.str `Ix.Tc.MutualTreeFixture decl)
        "_native")
      "native_decide")
    s!"ax_1_{index + 1}"

private def mutualNativeSeries (moduleName : Lean.Name) (decl : String)
    (count : Nat) : Array Lean.Name :=
  (Array.range count).map fun index =>
    nativeAxiom moduleName (mutualNativeUserName decl index)

private def mutualPublicNativeSeries (decl : String)
    (count : Nat) : Array Lean.Name :=
  (Array.range count).map fun index => mutualNativeUserName decl index

private def mutualNativeSingletons (moduleName : Lean.Name)
    (decls : Array String) : Array Lean.Name :=
  decls.map fun decl => nativeAxiom moduleName (mutualNativeUserName decl 0)

private def mutualFamilyAdmissionNativeSeries (decl : String)
    (count : Nat) : Array Lean.Name :=
  mutualNativeSeries `Ix.Tc.Verify.Inductive.MutualFamilyAdmission decl count

private def mutualBlockFixtureNativeSeries (decl : String)
    (count : Nat) : Array Lean.Name :=
  mutualNativeSeries `Ix.Tc.Verify.Inductive.MutualBlockFixture decl count

private def mutualRecursorAdmissionNativeSeries (decl : String)
    (count : Nat) : Array Lean.Name :=
  mutualNativeSeries `Ix.Tc.Verify.Inductive.MutualRecursorAdmission decl count

private def mutualInternDataValueNative : Lean.Name :=
  nativeAxiom `Ix.CanonM
    `Ix.CanonM.internDataValue._native.native_decide.ax_1

/-- Exact native footprint of the unconditional seven-member mutual-family
admission.  This is public only so the conditional audit can reuse the exact
completed prefix instead of maintaining a second copy. -/
def mutualFamilyNative : Array Lean.Name :=
  inductiveNative.push mutualInternDataValueNative ++
  mutualPublicNativeSeries "catalog_branch" 5 ++
  mutualPublicNativeSeries "catalog_cons" 7 ++
  mutualPublicNativeSeries "catalog_leaf" 3 ++
  mutualPublicNativeSeries "catalog_nil" 6 ++
  mutualPublicNativeSeries "catalog_node" 4 ++
  mutualPublicNativeSeries "catalog_tree" 1 ++
  mutualPublicNativeSeries "catalog_treeList" 2 ++
  mutualPublicNativeSeries "catalog_treeListRec" 9 ++
  mutualPublicNativeSeries "catalog_treeRec" 8 ++
  mutualPublicNativeSeries "nameOf_branch" 5 ++
  mutualPublicNativeSeries "nameOf_cons" 7 ++
  mutualPublicNativeSeries "nameOf_leaf" 3 ++
  mutualPublicNativeSeries "nameOf_nil" 6 ++
  mutualPublicNativeSeries "nameOf_node" 4 ++
  mutualPublicNativeSeries "nameOf_tree" 1 ++
  mutualPublicNativeSeries "nameOf_treeList" 2 ++
  mutualPublicNativeSeries "familyMembers_eq" 1 ++
  mutualPublicNativeSeries "recursorMembers_eq" 1 ++
  mutualNativeSingletons `Ix.Tc.Verify.Inductive.MutualBlockFixture #[
    "familyAuxCompileSucceededNative",
    "familyBlockLoadedNative",
    "familyIngressSucceededNative",
    "recursorBlockLoadedNative",
    "recursorIngressSucceededNative"
  ] ++
  mutualNativeSingletons `Ix.Tc.Verify.Inductive.MutualBlockValidation #[
    "familyKernelSucceededNative",
    "recursorKernelSucceededNative"
  ] ++
  mutualFamilyAdmissionNativeSeries "familyMemberShapeFactsNative" 19 ++
  mutualFamilyAdmissionNativeSeries "ownershipShapeFactsNative" 9 ++
  mutualNativeSingletons `Ix.Tc.Verify.Inductive.MutualFamilyAdmission #[
    "treeBranchTypeRawNative",
    "treeLeafTypeRawNative",
    "treeListConsTypeRawNative",
    "treeListNilTypeRawNative",
    "treeListTypeRawNative",
    "treeNodeTypeRawNative",
    "treeTypeRawNative"
  ]

/-- Native footprint added by the physical-order two-recursor link.  The two
pending semantic assumptions are intentionally not part of this array; the
conditional audit accounts for them in `RootAllowance.pendingAxioms`. -/
def mutualRecursorConditionalNative : Array Lean.Name :=
  mutualFamilyNative ++
  mutualPublicNativeSeries "nameOf_treeListRec" 9 ++
  mutualPublicNativeSeries "nameOf_treeRec" 8 ++
  mutualRecursorAdmissionNativeSeries
    "physicalSourceMembershipFactsNative" 5 ++
  mutualRecursorAdmissionNativeSeries "recursorRepresentationFactsNative" 55 ++
  mutualNativeSingletons `Ix.Tc.Verify.Inductive.MutualRecursorAdmission #[
    "branchRuleRawNative",
    "consRuleRawNative",
    "flatCtorFour",
    "flatCtorOne",
    "flatCtorThree",
    "flatCtorTwo",
    "flatCtorZero",
    "leafRuleRawNative",
    "nilRuleRawNative",
    "nodeRuleRawNative",
    "physicalBranchTypeRawNative",
    "physicalConsTypeRawNative",
    "physicalLeafTypeRawNative",
    "physicalNilTypeRawNative",
    "physicalNodeTypeRawNative",
    "physicalTreeListTypeRawNative",
    "physicalTreeTypeRawNative",
    "recursorOne",
    "recursorZero",
    "treeListRecNotFamily",
    "treeListRecTypeRawNative",
    "treeListRuleOne",
    "treeListRuleZero",
    "treeRecNotFamily",
    "treeRecTypeRawNative",
    "treeRuleOne",
    "treeRuleTwo",
    "treeRuleZero"
  ]

private def recursivePiFixtureNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.RecursivePiFixture name

private def recursivePiRecursorFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.RecursivePiRecursorFixture name

private def recursivePiAdmissionNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.RecursivePiAdmission name

private def annotatedPiCertificateNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AnnotatedPiCertificate name

private def annotatedPiCertificateBreadthNative : Array Lean.Name := #[
  annotatedPiCertificateNativeAxiom
    `Ix.Tc.AnnotatedPiCertificateFixture.breadthNative._native.native_decide.ax_1_1
]

private def annotatedPiFixtureNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AnnotatedPiFixture name

private def annotatedPiRecursorFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AnnotatedPiRecursorFixture name

private def annotatedPiAdmissionNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AnnotatedPiAdmission name

private def aliasFormerCertificateNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AliasFormerCertificate name

private def aliasFormerCertificateBreadthNative : Array Lean.Name := #[
  aliasFormerCertificateNativeAxiom
    `Ix.Tc.AliasFormerCertificateFixture.breadthNative._native.native_decide.ax_1_1
]

private def aliasFormerFixtureNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AliasFormerFixture name

private def aliasFormerPatternNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AliasFormerPattern name

private def aliasFormerRecursorFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AliasFormerRecursorFixture name

private def aliasFormerAdmissionNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AliasFormerAdmission name

private def aliasRecCertificateNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AliasRecCertificate name

private def aliasRecCertificateBreadthNative : Array Lean.Name := #[
  aliasRecCertificateNativeAxiom
    `Ix.Tc.AliasRecCertificateFixture.breadthNative._native.native_decide.ax_1_1
]

private def aliasRecFixtureNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AliasRecFixture name

private def aliasRecRecursorFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AliasRecRecursorFixture name

private def aliasRecAdmissionNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.AliasRecAdmission name

/- Exact executable footprint of the family-result-normalizing
AliasFormer family/recursor transaction. -/
private def aliasFormerAtomicClosureNative : Array Lean.Name :=
  inductiveNative ++ aliasFormerCertificateBreadthNative ++ #[
  aliasFormerAdmissionNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  aliasFormerAdmissionNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorOwnerNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.entriesSizeNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.entriesUniqueNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.entryAtOneNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.entryAtZeroNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.entryIdsNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.familyEntryNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.familyShapeNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.memberKidsNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.mkEntryNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.mkShapeNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Tc.AliasFormerFixture.typeFamilyAliasIngressSucceededNative._native.native_decide.ax_1_1,
  aliasFormerPatternNativeAxiom
    `Ix.Tc.AliasFormerPattern.generationCtorPairsNonempty._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_2,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.catalogMkNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.catalogMkNative._native.native_decide.ax_1_2,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.catalogMkNative._native.native_decide.ax_1_3,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.catalogTypeFamilyAliasNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.constructorCountNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.mkRuleBinderCoreNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.mkRuleFieldsNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.mkRuleRawNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.mkRuleScopedNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.mkRuleSizeBoundNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.mkSourceNameNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.mkTypeRawNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.nameOfMkNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.nameOfTypeFamilyAliasNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorEntryNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorEntrySizeNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorUniverseCountNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorShapeNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Tc.AliasFormerRecursorFixture.typeFamilyAliasTranslationsNative._native.native_decide.ax_1_1
]

/- Exact executable footprint of the recursive-field-normalizing `AliasRec`
family/recursor transaction. -/
private def aliasRecAtomicClosureNative : Array Lean.Name :=
  inductiveNative ++ aliasRecCertificateBreadthNative ++ #[
  aliasRecAdmissionNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  aliasRecAdmissionNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorOwnerNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.entriesSizeNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.entriesUniqueNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.entryAtOneNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.entryAtZeroNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.entryIdsNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.familyEntryNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.familyShapeNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.memberKidsNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.mkEntryNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.mkShapeNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.recAliasIngressSucceededNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Tc.AliasRecFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_2,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.catalogMkNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.catalogMkNative._native.native_decide.ax_1_2,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.catalogMkNative._native.native_decide.ax_1_3,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.catalogRecAliasNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.constructorCountNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.mkRuleBinderCoreNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.mkRuleFieldsNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.mkRuleRawNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.mkRuleScopedNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.mkRuleSizeBoundNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.mkSourceNameNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.mkTypeRawNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.nameOfMkNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.nameOfRecAliasNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recAliasTranslationsNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorEntryNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorEntrySizeNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorUniverseCountNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorShapeNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Tc.AliasRecRecursorFixture.recursorTypeRawNative._native.native_decide.ax_1_1
]

/- Exact executable footprint of the annotation-normalizing family/recursor
transaction, including its Theory breadth witness and physical outParam,
family, constructor, and recursor entries. -/
private def annotatedPiAtomicClosureNative : Array Lean.Name :=
  inductiveNative ++ annotatedPiCertificateBreadthNative ++ #[
  annotatedPiAdmissionNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  annotatedPiAdmissionNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorOwnerNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.entriesSizeNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.entriesUniqueNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.entryAtOneNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.entryAtZeroNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.entryIdsNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.familyEntryNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.familyShapeNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.memberKidsNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.mkEntryNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.mkShapeNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.outParamIngressSucceededNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_2,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.catalogMkNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.catalogMkNative._native.native_decide.ax_1_2,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.catalogMkNative._native.native_decide.ax_1_3,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.catalogOutParamNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.constructorCountNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.mkRuleBinderCoreNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.mkRuleFieldsNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.mkRuleRawNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.mkRuleScopedNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.mkRuleSizeBoundNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.mkSourceNameNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.mkTypeRawNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.nameOfMkNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.nameOfOutParamNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.outParamTranslationsNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorEntryNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorEntrySizeNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorUniverseCountNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorShapeNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Tc.AnnotatedPiRecursorFixture.recursorTypeRawNative._native.native_decide.ax_1_1
]

/- Exact executable footprint of the recursive-Pi family/recursor transaction.
The list is deliberately independent from the broader IndexedVec fixture so
the `Acc` closure cannot silently acquire unrelated native assumptions. -/
private def recursivePiAtomicClosureNative : Array Lean.Name :=
  inductiveNative ++ #[
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.entriesSizeNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.entriesUniqueNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.entryAtOneNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.entryAtZeroNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.entryIdsNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.familyEntryNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.familyShapeNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.ingressSucceededNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.introEntryNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.introShapeNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.memberKidsNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Tc.RecursivePiFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.catalogIntroNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.catalogIntroNative._native.native_decide.ax_1_2,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.constructorCountNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.introRuleBinderCoreNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.introRuleFieldsNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.introRuleRawNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.introRuleScopedNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.introRuleSizeBoundNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.introSourceNameNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.introTypeRawNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.nameOfIntroNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorEntryNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorEntrySizeNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorShapeNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
  recursivePiAdmissionNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  recursivePiAdmissionNativeAxiom
    `Ix.Tc.RecursivePiRecursorFixture.recursorOwnerNative._native.native_decide.ax_1_1
]

private def enumerationFixtureNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.EnumerationFixture name

private def enumerationAcceptanceNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.EnumerationAcceptance name

private def indexedRecursiveFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedRecursiveFixture name

private def indexedRecursiveAcceptanceNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedRecursiveAcceptance name

private def eliminationBreadthNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.EliminationBreadthFixture name

private def smallEliminationAcceptanceNative : Array Lean.Name :=
  inductiveNative.push mutualInternDataValueNative ++ #[
    `Lean4Lean.InductiveReplayFixtures.smallSourceAlignment06._native.native_decide.ax_1,
    `Lean4Lean.InductiveReplayFixtures.smallSourceEliminationResult06_isOk._native.native_decide.ax_1_1,
    `Ix.Tc.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_1,
    `Ix.Tc.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_2,
    `Ix.Tc.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_3,
    `Ix.Tc.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_4,
    `Ix.Tc.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_5,
    `Ix.Tc.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_6,
    `Ix.Tc.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_7,
    `Ix.Tc.EliminationBreadthFixture.smallComputeKMatches_eq._native.native_decide.ax_1_1,
    `Ix.Tc.EliminationBreadthFixture.smallPreparationMatches_eq._native.native_decide.ax_1_1,
    `Ix.Tc.EliminationBreadthFixture.smallRecursorShape._native.native_decide.ax_1_1,
    `Ix.Tc.EliminationBreadthFixture.smallTheoryRecUvars._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.smallCompilerSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.smallExecutionKNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.smallExecutionModeNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.smallFamilyIngressSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.smallFamilyKernelSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.smallRecursorIngressSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.smallRecursorKernelSucceededNative._native.native_decide.ax_1_1
  ]

private def kTargetAcceptanceNative : Array Lean.Name :=
  inductiveNative.push mutualInternDataValueNative ++ #[
    `Lean4Lean.InductiveReplayFixtures.eqAlignment06._native.native_decide.ax_1,
    `Lean4Lean.InductiveReplayFixtures.eqEliminationResult06_isOk._native.native_decide.ax_1_1,
    `Ix.Tc.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_1,
    `Ix.Tc.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_2,
    `Ix.Tc.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_3,
    `Ix.Tc.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_4,
    `Ix.Tc.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_5,
    `Ix.Tc.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_6,
    `Ix.Tc.EliminationBreadthFixture.eqComputeKMatches_eq._native.native_decide.ax_1_1,
    `Ix.Tc.EliminationBreadthFixture.eqPreparationMatches_eq._native.native_decide.ax_1_1,
    `Ix.Tc.EliminationBreadthFixture.eqRecursorShape._native.native_decide.ax_1_1,
    `Ix.Tc.EliminationBreadthFixture.eqTheoryRecUvars._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.eqCompilerSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.eqExecutionKNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.eqExecutionModeNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.eqFamilyIngressSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.eqFamilyKernelSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.eqRecursorIngressSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Tc.EliminationBreadthFixture.eqRecursorKernelSucceededNative._native.native_decide.ax_1_1
  ]

private def indexedRecursiveFixtureNativeNames : Array Lean.Name := #[
  `Ix.Tc.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_2,
  `Ix.Tc.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_3,
  `Ix.Tc.IndexedRecursiveFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_2,
  `Ix.Tc.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_3,
  `Ix.Tc.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_4,
  `Ix.Tc.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_5,
  `Ix.Tc.IndexedRecursiveFixture.catalogNilNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.catalogNilNative._native.native_decide.ax_1_2,
  `Ix.Tc.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  `Ix.Tc.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  `Ix.Tc.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_2,
  `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_3,
  `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_4,
  `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_5,
  `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_6,
  `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_7,
  `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_2,
  `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_3,
  `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_4,
  `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_5,
  `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_6,
  `Ix.Tc.IndexedRecursiveFixture.consEntryNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.consSourceNameNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.consRuleBinderCoreNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.consRuleFieldsNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.consRuleRawNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.consRuleScopedNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.consRuleSizeBoundNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.consShapeNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.consTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.constructorCountNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyEntriesSizeNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyEntriesUniqueNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyEntryAtOneNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyEntryAtTwoNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyEntryAtZeroNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyEntryIdsNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyEntryNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyMemberKidsNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyShapeNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.generationCtorPairOne._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nameOfConsNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nameOfNatNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nameOfNilNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nameOfSuccNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nameOfZeroNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natConstructorCountNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natEntriesSizeNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natEntriesUniqueNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natEntryAtOneNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natEntryAtTwoNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natEntryAtZeroNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natEntryIdsNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natEntryNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natFamilyShapeNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natIngressSucceededNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natMemberKidsNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natSourceConstructorOne._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natSourceConstructorZero._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nilEntryNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nilSourceNameNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nilRuleBinderCoreNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nilRuleFieldsNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nilRuleRawNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nilRuleScopedNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nilRuleSizeBoundNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nilShapeNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.nilTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorEntryNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorShapeNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorUniverseCountNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.sourceConstructorOne._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.succEntryNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.succSourceNameNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.succShapeNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.succTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.zeroEntryNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.zeroSourceNameNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.zeroShapeNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.zeroTypeRawNative._native.native_decide.ax_1_1
]

private def indexedRecursiveAcceptanceNativeNames : Array Lean.Name := #[
  `Ix.Tc.IndexedRecursiveFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.malformedRecursorRejectedNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natKernelSucceededNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.natNotFamilyDirectOwnerNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  `Ix.Tc.IndexedRecursiveFixture.recursorOwnerNative._native.native_decide.ax_1_1
]

private def indexedRecursiveNative : Array Lean.Name :=
  inductiveNative ++
    indexedRecursiveFixtureNativeNames.map indexedRecursiveFixtureNativeAxiom ++
    indexedRecursiveAcceptanceNativeNames.map
      indexedRecursiveAcceptanceNativeAxiom

/-- Exact native footprint of the concrete production `buildRecType` run.
The broad indexed-recursive fixture manifest is intentionally not reused: a
new observation in an unrelated acceptance theorem must not silently widen
this builder root. -/
private def generatedRecursorTypeFixtureNative : Array Lean.Name :=
  inductiveNative ++ #[
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeSizeBoundNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Tc.Verify.Inductive.GeneratedRecursorTypeFixture
      `Ix.Tc.IndexedRecursiveFixture.familyBuildTypeResultNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Tc.Verify.Inductive.GeneratedRecursorTypeFixture
      `Ix.Tc.IndexedRecursiveFixture.familyBuildTypeSucceededNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Tc.Verify.Inductive.GeneratedRecursorTypeFixture
      `Ix.Tc.IndexedRecursiveFixture.familyPreparationSucceededNative._native.native_decide.ax_1_1
  ]

private def generatedRecursorRuleFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.GeneratedRecursorRuleFixture name

/-- Exact native footprint of the complete IndexedVec peer-alignment and
`buildRuleRhs` run. -/
private def generatedRecursorRuleFixtureNative : Array Lean.Name :=
  inductiveNative ++ #[
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeSizeBoundNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.generationCtorPairZero._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.generationCtorPairOne._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.nilRuleBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.nilRuleFieldsNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.nilRuleRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.nilRuleScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.nilRuleSizeBoundNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.consRuleBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.consRuleFieldsNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.consRuleRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.consRuleScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.consRuleSizeBoundNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.familyBuiltRulesNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.familyCompletedRecursorTypeNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.familyRulePopulationSucceededNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.generationRuleCountNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorRulesLiteralNative._native.native_decide.ax_1_1
  ]

/- Exact native footprint of the transactional rule commit.  This is kept
separate from `generatedRecursorRuleFixtureNative`: the commit proof observes
the two intermediate array sizes, but no longer depends on the standalone
completed-type observation used by the builder fixture. -/
private def generatedRecursorCommitFixtureNative : Array Lean.Name :=
  inductiveNative ++ #[
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorTypeSizeBoundNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.generationCtorPairZero._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.generationCtorPairOne._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.nilRuleBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.nilRuleFieldsNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.nilRuleRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.nilRuleScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.nilRuleSizeBoundNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.consRuleBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.consRuleFieldsNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.consRuleRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.consRuleScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.consRuleSizeBoundNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.familyBuiltRulesNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.familyGeneratedSnapshotSizeNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.familyGeneratedWithRulesSizeNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.familyRulePopulationSucceededNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.generationRuleCountNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorRulesLiteralNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Tc.Verify.Inductive.GeneratedRecursorCommitFixture
      `Ix.Tc.IndexedRecursiveFixture.familyRuleCommitSucceededNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Tc.Verify.Inductive.GeneratedRecursorCommitFixture
      `Ix.Tc.IndexedRecursiveFixture.familyGeneratedSnapshotTypeNative._native.native_decide.ax_1_1
  ]

private def generatedRecursorCheckerFixtureNative : Array Lean.Name :=
  generatedRecursorCommitFixtureNative ++ #[
    indexedRecursiveFixtureNativeAxiom
      `Ix.Tc.IndexedRecursiveFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Tc.Verify.Inductive.GeneratedRecursorCheckerFixture
      `Ix.Tc.IndexedRecursiveFixture.familyCacheCheckSucceededNative._native.native_decide.ax_1_1
  ]

/- The additional native facts used to construct the concrete IndexedVec
semantic world.  They are disjoint from the checker execution footprint
above, so the concatenated canonical fixture manifest remains exact. -/
private def generatedRecursorCanonicalWorldNative : Array Lean.Name := #[
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natNotFamilyDirectOwnerNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_3,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_3,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_4,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_5,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogNilNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogNilNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_3,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_4,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_5,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_6,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_7,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_3,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_4,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_5,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_6,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.consEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.consShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.consSourceNameNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.consTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.constructorCountNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyEntriesSizeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyEntriesUniqueNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyEntryAtOneNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyEntryAtTwoNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyEntryAtZeroNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyEntryIdsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberKidsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.nameOfConsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.nameOfNatNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.nameOfNilNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.nameOfSuccNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.nameOfZeroNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natConstructorCountNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natEntriesSizeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natEntriesUniqueNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natEntryAtOneNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natEntryAtTwoNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natEntryAtZeroNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natEntryIdsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natFamilyShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natIngressSucceededNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natMemberKidsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natSourceConstructorOne._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natSourceConstructorZero._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.natTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.nilEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.nilShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.nilSourceNameNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.nilTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.sourceConstructorOne._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.succEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.succShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.succSourceNameNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.succTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.zeroEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.zeroShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.zeroSourceNameNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.zeroTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.recursorShapeNative._native.native_decide.ax_1_1
]

private def generatedRecursorCanonicalFixtureNative : Array Lean.Name :=
  generatedRecursorCheckerFixtureNative ++
    generatedRecursorCanonicalWorldNative

private def generatedRecursorCommitFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.GeneratedRecursorCommitFixture name

private def generatedRecursorMemberFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.GeneratedRecursorMemberFixture name

private def generatedRecursorInitialInvariantNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom
    `Ix.Tc.Verify.Inductive.GeneratedRecursorInitialInvariant name

/- Exact executable footprint of the complete concrete recursor-member
transaction.  The earlier commit and semantic-world manifests are reused
only where they are exact subsets.  The remaining entries pin the outer
member prelude, the finite initial cache invariant, and the semantic recursor
entry used by the oracle-free second admission. -/
private def generatedRecursorAtomicClosureNative : Array Lean.Name :=
  generatedRecursorCommitFixtureNative ++
    generatedRecursorCanonicalWorldNative ++ #[
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.recursorUniverseCountNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.recursorEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.recursorOwnerNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.consConcreteHeaderNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.familyConcreteHeaderNative._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyInstalledRecursorAtZeroMemberNative._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyInstalledRecursorTypeEqNative._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyInstalledConsRuleInternSupported._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyInstalledNilRuleInternSupported._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyInstalledRecursorInductiveAddress._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyInstalledRecursorRules._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyInstalledRecursorTypeInternSupported._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberArityBoundNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberSingletonSizeNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInitialPrimitivesNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyCharOfNatAbsent._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberCheckSucceededNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberDirectMajorShapeNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInitialBlocksCoveredNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInitialClosedFieldsNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInitialConstsCoveredNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInitialEquivEntriesEmpty._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInitialEquivLabelsEmpty._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInitialEquivParentEmpty._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInitialExprKeysNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInitialRecursorLoaded._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInitialReferencesCovered._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInitialUnivKeysNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberMajorSkipRunNeutral._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberOwnerCacheMatchesNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberPopulationReferencesCovered._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberPreparationMatchesNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRecursorConcreteHeader._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberReferenceId_authorized._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberReferenceId_authorized._native.native_decide.ax_1_2,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberReferenceId_authorized._native.native_decide.ax_1_3,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberResolutionPrefixMatchesNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberResultLevelNonzero._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberResultSortShape._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRulePopulationCacheChecksNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRulePopulationExprKeysNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRulePopulationExtendsNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRulePopulationMatchesNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRulePopulationNoLazyNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRulePopulationSemanticChecksNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRulePopulationUnivKeysNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberSnapshotFamilyLoaded._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberSnapshotGeneratedCache._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyNatSuccLookup._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyNatZeroLookup._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyNilConcreteHeader._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberBlockPeersClassifiedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberBlockResultKeysClassifiedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberConsInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberConsInnerResultLevel_raw._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberConsResultLevel_raw._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberConsTypeTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberDefEqCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberDefEqCheapCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberDefEqFailureCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberFamilyInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberFamilyReferenceTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberFamilyResultLevel_raw._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberFamilyTypeTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInferCensusNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberInferOnlyCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberIsPropCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberIsRecCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberNatBlockAccepted._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberNatBlockAccepted._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberNatInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberNatReferenceTranslation._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberNatReferenceWhnf._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberNatSuccStuckCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberNatTrusted._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberNatTypeTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberNilInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberNilTypeTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRecMajorsClassifiedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRecursorBlocksClassifiedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRecursorOwnersClassifiedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberRecursorPayloadsInternedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberSuccInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberSuccReferenceTranslation._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberSuccTrusted._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberSuccTypeTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberTypedConstantSyntaxNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberUnfoldCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberWhnfCensusNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberWhnfCoreCensusNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberWhnfCoreCheapCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberWhnfNoDeltaCensusNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberWhnfNoDeltaCheapCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberZeroInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberZeroReferenceTranslation._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberZeroTrusted._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyMemberZeroTypeTranslation._native.native_decide.ax_1_2
]

/-- Exact executable delta between the existing semantic recursor closure
and the stronger closure that also retains the analyzer's candidate producer
equation.  The latter adds only the two outer production block checks. -/
private def indexedProducerClosureNative : Array Lean.Name :=
  generatedRecursorAtomicClosureNative ++ #[
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Tc.IndexedRecursiveFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1
]

/-- Exact executable footprint of the production-linked IndexedVec
constructor-validation replay.  Keep this separate from the broader
end-to-end acceptance fixture so a new observation changes this root's audit. -/
private def indexedConstructorValidationNative : Array Lean.Name := #[
  nativeAxiom `Blake3
    `Blake3.HasherOps.hash._native.native_decide.ax_1,
  nativeAxiom `Ix.Environment
    `Ix.Name.mkStr._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Expr
    `Ix.Tc.KExpr.mkVar._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Inductive
    `Ix.Tc.RecM.canonicalAuxOrder._native.native_decide.ax_9,
  nativeAxiom `Ix.Tc.Level
    `Ix.Tc.KUniv.mkSucc._native.native_decide.ax_1,
  nativeAxiom `Ix.Tc.Monad
    `Ix.Tc.TcM.ctxAddrForLbrUncached._native.native_decide.ax_3,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.consConcreteHeaderNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.familyAritySucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.familyClassificationMatchesNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.familyConcreteHeaderNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.familyDiscoveryMatchesNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.familyMemberLoadedNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.familyNilAfterConsLoadedNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.familyNilValidationSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.familyPeerAgreementSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedBlockValidation
    `Ix.Tc.IndexedRecursiveFixture.familyResultLevelSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Tc.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_2,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Tc.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_3,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Tc.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_4,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Tc.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_5,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Tc.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_6,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Tc.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_7,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorAfterParamShapeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorAlphaEnsureTypeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorConsumeAlphaNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorConsumeNatNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorConsumeTailNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorGetTypeAlphaNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorInstantiateHeadNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorInstantiateNNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorInstantiateTailNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorNatEnsureTypeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorNatUniverse._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorParamIsDefEqNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorParamUniverse._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorResultIsValidNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorTailEnsureTypeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedConstructorValidation
    `Ix.Tc.IndexedRecursiveFixture.indexedVecConstructorTypeShapeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedPositivityTransport
    `Ix.Tc.IndexedRecursiveFixture.familyConsHeadDomainCandidateCheckNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedPositivityTransport
    `Ix.Tc.IndexedRecursiveFixture.familyConsNatDomainCandidateCheckNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedPositivityTransport
    `Ix.Tc.IndexedRecursiveFixture.familyConsTailDomainCandidateCheckNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedPositivityTransport
    `Ix.Tc.IndexedRecursiveFixture.familyConsTailWhnfCandidateCheckNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedPositivityTransport
    `Ix.Tc.IndexedRecursiveFixture.indexedVecAlphaCandidateWhnfNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedPositivityTransport
    `Ix.Tc.IndexedRecursiveFixture.indexedVecAlphaHasNoIndOccTrusted._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedPositivityTransport
    `Ix.Tc.IndexedRecursiveFixture.indexedVecNatCandidateWhnfNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedPositivityTransport
    `Ix.Tc.IndexedRecursiveFixture.indexedVecNatHasNoIndOccTrusted._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedPositivityTransport
    `Ix.Tc.IndexedRecursiveFixture.indexedVecTailAppIsValidTrusted._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedPositivityTransport
    `Ix.Tc.IndexedRecursiveFixture.indexedVecTailCandidateWhnfNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedPositivityTransport
    `Ix.Tc.IndexedRecursiveFixture.indexedVecTailHasIndOccTrusted._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsHeadDomainRootFreeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsHeadOpenSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsHeadTelescopeWhnfIsForallNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsNatDomainRootFreeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsNatOpenSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsNatTelescopeWhnfIsForallNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsPositivityParametersSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsResultWhnfSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsResultWhnfTerminalNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsTailDomainMentionsRootNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsTailDomainSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsTailDomainWhnfNotForallNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsTailDomainWhnfSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsTailOpenSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsTailTelescopeWhnfIsForallNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsTailWhnfSpineActiveNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedProductionPositivity
    `Ix.Tc.IndexedRecursiveFixture.familyConsTailWhnfSpineIsConstNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedRecursiveAcceptance
    `Ix.Tc.IndexedRecursiveFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Tc.Verify.Inductive.IndexedRecursiveFixture
    `Ix.Tc.IndexedRecursiveFixture.familyEntriesSizeNative._native.native_decide.ax_1_1
]

private def nestedRecursiveFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.NestedRecursiveFixture name

private def nestedRecursiveActionNative : Array Lean.Name :=
  nameContextNative ++ #[
    nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.boxInactiveNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.nestedMentionsRootNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.nestedSpineNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.nestedWhnfSucceededNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.positivitySucceededNative._native.native_decide.ax_1_1
  ]

private def nestedRecursiveProducedNative : Array Lean.Name :=
  nestedRecursiveActionNative ++ #[
    nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.boxConcreteHeaderMatchesNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.boxLookupConcreteNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.boxLookupSucceededNative._native.native_decide.ax_1_1
  ]

private def nestedRecursiveFreshNative : Array Lean.Name :=
  nestedRecursiveProducedNative.push
    (nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.positivityRequestAbsentNative._native.native_decide.ax_1_1)

private def nestedRecursiveReachabilityNative : Array Lean.Name :=
  nestedRecursiveFreshNative ++ #[
    nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.builtFlatShapeNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.flatBuildSucceededNative._native.native_decide.ax_1_1
  ]

private def nestedCandidateSyntaxNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.NestedCandidateSyntax name

private def nestedPositivityTransportNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.NestedPositivityTransport name

private def nestedAuxiliaryPositivityNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.NestedAuxiliaryPositivity name

private def nestedConstructorValidationNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.NestedConstructorValidation name

private def nestedCandidateRelationNative : Array Lean.Name := #[
  nestedCandidateSyntaxNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.leanAuxiliaryOccursNative._native.native_decide.ax_1_1,
  nestedCandidateSyntaxNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.leanAuxiliarySourceNative._native.native_decide.ax_1_1,
  nestedCandidateSyntaxNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.leanAuxiliaryTargetNative._native.native_decide.ax_1_1,
  nestedCandidateSyntaxNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.leanFlatNodeTypeNative._native.native_decide.ax_1_1,
  nestedCandidateSyntaxNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.nestedDomainCandidateCheckNative._native.native_decide.ax_1_1
]

private def nestedRecursiveReachabilityWithResultNative : Array Lean.Name :=
  nestedRecursiveReachabilityNative.push
    (nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.nestedWhnfResultNative._native.native_decide.ax_1_1)

private def nestedOuterTransportNative : Array Lean.Name :=
  nestedRecursiveReachabilityWithResultNative ++ nestedCandidateRelationNative ++ #[
    nestedPositivityTransportNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanAuxiliaryCandidateWhnfNative._native.native_decide.ax_1_1,
    nestedPositivityTransportNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.nestedDomainMentionsRootNative._native.native_decide.ax_1_1,
    nestedPositivityTransportNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.nestedExternalInactiveNative._native.native_decide.ax_1_1
  ]

private def nestedAuxiliaryCandidateTargetNative : Array Lean.Name :=
  nestedRecursiveReachabilityNative ++ nestedCandidateRelationNative

private def nestedAuxiliaryExecutionNative : Array Lean.Name := #[
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliaryDiscoverySucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliaryDomainWhnfNotForallNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliaryDomainWhnfResultNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliaryDomainWhnfSucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliaryFieldWhnfShapeNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliaryFieldWhnfSucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliaryInstantiationSucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliaryParameterArgsNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliaryStrippingSucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliarySubstitutionSucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliaryTreeMentionsRootNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.auxiliaryWrapLookupSucceededNative._native.native_decide.ax_1_1
]

private def nestedAuxiliaryProductionNative : Array Lean.Name :=
  nestedRecursiveFreshNative ++ nestedAuxiliaryExecutionNative

private def nestedAuxiliaryTransportNative : Array Lean.Name :=
  nameContextNative ++ #[
    nestedAuxiliaryPositivityNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.auxiliaryDomainWhnfResultNative._native.native_decide.ax_1_1,
    nestedAuxiliaryPositivityNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.auxiliaryDomainWhnfSucceededNative._native.native_decide.ax_1_1,
    nestedAuxiliaryPositivityNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.auxiliaryTreeMentionsRootNative._native.native_decide.ax_1_1,
    nestedAuxiliaryPositivityNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanTreeCandidateWhnfNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanTreeOccursNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanTreeTargetNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.treeCandidateCheckNative._native.native_decide.ax_1_1
  ]

private def nestedAuxiliaryConstructorNative : Array Lean.Name :=
  nestedAuxiliaryProductionNative ++ #[
    nestedAuxiliaryPositivityNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanTreeCandidateWhnfNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanTreeOccursNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanTreeTargetNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.treeCandidateCheckNative._native.native_decide.ax_1_1
  ]

private def nestedNodeConstructorValidationNative : Array Lean.Name :=
  nestedOuterTransportNative ++ #[
    nestedConstructorValidationNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.consumeLeanAuxiliaryNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.instantiateLeanTreeNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanAuxiliaryEnsureTypeNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanFlatFieldUniverse._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanTreeTerminalNative._native.native_decide.ax_1_1
  ]

private def nestedWrapConstructorValidationNative : Array Lean.Name :=
  nestedAuxiliaryConstructorNative ++ #[
    nestedCandidateSyntaxNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanFlatWrapTypeNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.consumeLeanTreeNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.instantiateLeanAuxiliaryNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanAuxiliaryTerminalNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanFlatFieldUniverse._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.leanTreeEnsureTypeNative._native.native_decide.ax_1_1
  ]

private def nestedTreeCandidateSyntaxNative : Array Lean.Name :=
  expressionNative.push
    (nestedCandidateSyntaxNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.treeCandidateCheckNative._native.native_decide.ax_1_1)

/- The nested semantic transaction has two independently executable halves:
the Lean4Lean source/restoration proof and Ix's physical catalog/checker
join.  Keep their native footprints explicit so the headline audit cannot
silently acquire oracle materialization or pending assumptions. -/
private def nativeUnion (left right : Array Lean.Name) : Array Lean.Name :=
  right.foldl (fun names name =>
    if names.contains name then names else names.push name) left

private def nestedSemanticBoxNative : Array Lean.Name := #[
  `Ix.Tc.NestedRecursiveFixture.semanticBoxAfter_isSome._native.native_decide.ax_1_1,
  `Ix.Tc.NestedRecursiveFixture.semanticBoxChecked._native.native_decide.ax_1,
  `Ix.Tc.NestedRecursiveFixture.semanticBoxGeneration._native.native_decide.ax_1,
  `Ix.Tc.NestedRecursiveFixture.semanticBoxShape._native.native_decide.ax_1_1,
  `Ix.Tc.NestedRecursiveFixture.semanticBoxShape._native.native_decide.ax_1_2,
  `Ix.Tc.NestedRecursiveFixture.semanticBoxShape._native.native_decide.ax_1_3,
  `Ix.Tc.NestedRecursiveFixture.semanticBoxShape._native.native_decide.ax_1_4,
  `Ix.Tc.NestedRecursiveFixture.semanticBoxShape._native.native_decide.ax_1_5
]

private def nestedSemanticWFNative : Array Lean.Name :=
  nestedSemanticBoxNative ++ #[
    `Ix.Tc.NestedRecursiveFixture.semanticTreeNested_isSome._native.native_decide.ax_1_1,
    `Ix.Tc.NestedRecursiveFixture.semanticTreeRecursors_eq._native.native_decide.ax_1_1,
    `Ix.Tc.NestedRecursiveFixture.semanticTreeRules_eq._native.native_decide.ax_1_1
  ]

private def nestedSemanticCertificateNative : Array Lean.Name :=
  nestedSemanticWFNative.push
    `Ix.Tc.NestedRecursiveFixture.semanticTreeAfter_isSome._native.native_decide.ax_1_1

private def nestedSemanticFactsNative : Array Lean.Name :=
  nestedSemanticCertificateNative ++ #[
    `Ix.Tc.NestedRecursiveFixture.semanticTreeNodeName._native.native_decide.ax_1_1,
    `Ix.Tc.NestedRecursiveFixture.semanticTreeRestoredClean._native.native_decide.ax_1_1
  ]

private def nestedSemanticAdmissionNative : Array Lean.Name :=
  nestedSemanticCertificateNative ++ #[
    `Ix.Tc.NestedRecursiveFixture.semanticTreeNodeName._native.native_decide.ax_1_1,
    `Ix.Tc.NestedRecursiveFixture.semanticTreeSourceInventory._native.native_decide.ax_1_1,
    `Ix.Tc.NestedRecursiveFixture.semanticTreeSourceInventory._native.native_decide.ax_1_2
  ]

private def nestedAdmissionNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Inductive.NestedAdmission name

private def nestedAdmissionPublicNative : Array Lean.Name := #[
  `Ix.Tc.NestedRecursiveFixture.nestedCatalog_node._native.native_decide.ax_1_1,
  `Ix.Tc.NestedRecursiveFixture.nestedCatalog_node._native.native_decide.ax_1_2,
  `Ix.Tc.NestedRecursiveFixture.nestedCatalog_tree._native.native_decide.ax_1_1,
  `Ix.Tc.NestedRecursiveFixture.nestedNameOf_node._native.native_decide.ax_1_1,
  `Ix.Tc.NestedRecursiveFixture.nestedNameOf_node._native.native_decide.ax_1_2,
  `Ix.Tc.NestedRecursiveFixture.nestedNameOf_node._native.native_decide.ax_1_3,
  `Ix.Tc.NestedRecursiveFixture.nestedNameOf_node._native.native_decide.ax_1_4,
  `Ix.Tc.NestedRecursiveFixture.nestedNameOf_tree._native.native_decide.ax_1_1,
  `Ix.Tc.NestedRecursiveFixture.nestedNameOf_tree._native.native_decide.ax_1_2,
  `Ix.Tc.NestedRecursiveFixture.nestedNameOf_tree._native.native_decide.ax_1_3
]

private def nestedAdmissionPrivateNative : Array Lean.Name := #[
  nestedAdmissionNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.nestedFamilyBlockLoadedNative._native.native_decide.ax_1_1,
  nestedAdmissionNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.nestedMemberShapeFactsNative._native.native_decide.ax_1_1,
  nestedAdmissionNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.nestedMemberShapeFactsNative._native.native_decide.ax_1_2,
  nestedAdmissionNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.nestedMemberShapeFactsNative._native.native_decide.ax_1_3,
  nestedAdmissionNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.nestedMemberShapeFactsNative._native.native_decide.ax_1_4,
  nestedAdmissionNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.nestedNodeDirectConstructor._native.native_decide.ax_1_1,
  nestedAdmissionNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.nestedNodeTypeRawNative._native.native_decide.ax_1_1,
  nestedAdmissionNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.nestedTreeDirectOwner._native.native_decide.ax_1_1,
  nestedAdmissionNativeAxiom
    `Ix.Tc.NestedRecursiveFixture.nestedTreeTypeRawNative._native.native_decide.ax_1_1
]

private def nestedFamilyCertificateNative : Array Lean.Name :=
  nativeUnion
    (nativeUnion nameNative nestedSemanticAdmissionNative)
    (nestedAdmissionPublicNative ++ nestedAdmissionPrivateNative)

private def nestedFamilyKernelNative : Array Lean.Name :=
  inductiveNative.push
    (nestedAdmissionNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.nestedFamilyKernelSucceededNative._native.native_decide.ax_1_1)

private def nestedSemanticTransactionClosureNative : Array Lean.Name :=
  let withSemantics := nativeUnion nestedFamilyCertificateNative
    nestedSemanticFactsNative
  let withKernel := nativeUnion withSemantics nestedFamilyKernelNative
  let withNode := nativeUnion withKernel nestedNodeConstructorValidationNative
  let withWrap := nativeUnion withNode nestedWrapConstructorValidationNative
  let withBoxIngress := withWrap.push
    (nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.boxIngressSucceededNative._native.native_decide.ax_1_1)
  withBoxIngress.push
    (nestedRecursiveFixtureNativeAxiom
      `Ix.Tc.NestedRecursiveFixture.treeIngressSucceededNative._native.native_decide.ax_1_1)

/- The physical nested-recursor slice is deliberately separate from the
source transaction above.  It compiles the retained kernel declarations,
ingresses the generated two-member recursor block, proves both restored iota
patterns, and admits family plus recursors in one semantic closure.  Generate
the repetitive exact native names structurally, but keep every declaration
and cardinality visible in the manifest. -/
private def nestedRecursorNativeUserName (decl : String)
    (index : Nat) : Lean.Name :=
  Lean.Name.str
    (Lean.Name.str
      (Lean.Name.str
        (Lean.Name.str `Ix.Tc.NestedRecursiveFixture decl)
        "_native")
      "native_decide")
    s!"ax_1_{index + 1}"

private def nestedRecursorNativeSeries (moduleName : Lean.Name)
    (decl : String) (count : Nat) : Array Lean.Name :=
  (Array.range count).map fun index =>
    nativeAxiom moduleName (nestedRecursorNativeUserName decl index)

private def nestedRecursorPublicNativeSeries (decl : String)
    (count : Nat) : Array Lean.Name :=
  (Array.range count).map fun index =>
    nestedRecursorNativeUserName decl index

private def nestedRecursorFixtureNativeSeries (decl : String)
    (count : Nat := 1) : Array Lean.Name :=
  nestedRecursorNativeSeries
    `Ix.Tc.Verify.Inductive.NestedRecursorFixture decl count

private def nestedRecursorPatternNativeSeries (decl : String)
    (count : Nat := 1) : Array Lean.Name :=
  nestedRecursorNativeSeries
    `Ix.Tc.Verify.Inductive.NestedRecursorPattern decl count

private def nestedRecursorSoundnessNativeSeries (decl : String)
    (count : Nat := 1) : Array Lean.Name :=
  nestedRecursorNativeSeries
    `Ix.Tc.Verify.Inductive.NestedRecursorSoundness decl count

private def nestedRecursorAdmissionNativeSeries (decl : String)
    (count : Nat := 1) : Array Lean.Name :=
  nestedRecursorNativeSeries
    `Ix.Tc.Verify.Inductive.NestedRecursorAdmission decl count

private def nestedRecursorCompilerBaseNative : Array Lean.Name :=
  nameContextNative.push mutualInternDataValueNative

private def nestedRecursorCompilerRunNative : Array Lean.Name :=
  nestedRecursorCompilerBaseNative ++
    nestedRecursorFixtureNativeSeries "nestedCompilerSucceededNative"

private def nestedRecursorCompilerIdentityNative : Array Lean.Name :=
  nestedRecursorCompilerBaseNative ++
    nestedRecursorFixtureNativeSeries "nestedCompiledIdentityFactsNative" 7

private def nestedRecursorIngressNative : Array Lean.Name :=
  nestedRecursorCompilerBaseNative ++
    nestedRecursorFixtureNativeSeries "recursorIngressSucceededNative"

private def nestedRecursorRepresentationNative : Array Lean.Name :=
  nestedRecursorCompilerBaseNative ++
    nestedRecursorPatternNativeSeries
      "nestedRecursorRepresentationFactsNative" 20 ++
    nestedRecursorPatternNativeSeries "treeRecOneRuleZero" ++
    nestedRecursorPatternNativeSeries "treeRecRuleZero"

private def nestedRecursorSemanticNative : Array Lean.Name :=
  nativeUnion nestedSemanticFactsNative nestedSemanticAdmissionNative

private def nestedRecursorNodePublicNative : Array Lean.Name :=
  nestedRecursorPublicNativeSeries "nestedRecursorCatalog_node" 4 ++
    nestedRecursorPublicNativeSeries "nestedRecursorNameOf_node" 4 ++
    nestedRecursorPublicNativeSeries "nestedRecursorNameOf_treeRec" 5

private def nestedRecursorWrapPublicNative : Array Lean.Name :=
  nestedRecursorPublicNativeSeries "nestedRecursorCatalog_wrap" 2 ++
    nestedRecursorPublicNativeSeries "nestedRecursorNameOf_treeRecOne" 6 ++
    nestedRecursorPublicNativeSeries "nestedRecursorNameOf_wrap" 2

private def nestedRecursorNodeSoundnessNative : Array Lean.Name :=
  nestedRecursorSoundnessNativeSeries "commonBindersLength" ++
    nestedRecursorSoundnessNativeSeries "nodeConstructorTypeInstLNil" ++
    nestedRecursorSoundnessNativeSeries "nodeRuleBindersLength" ++
    nestedRecursorSoundnessNativeSeries "nodeRuleLhsShape"

private def nestedRecursorWrapSoundnessNative : Array Lean.Name :=
  nestedRecursorSoundnessNativeSeries "commonBindersLength" ++
    nestedRecursorSoundnessNativeSeries "treeFamilyTypeInstLNil" ++
    nestedRecursorSoundnessNativeSeries "treeFamilyTypeShape" ++
    nestedRecursorSoundnessNativeSeries "wrapConstructorTypeInstLNil" ++
    nestedRecursorSoundnessNativeSeries "wrapRuleBindersLength" ++
    nestedRecursorSoundnessNativeSeries "wrapRuleLhsShape"

private def nestedRecursorNodePatternNative : Array Lean.Name :=
  nativeUnion
    (nativeUnion
      (nativeUnion nestedRecursorRepresentationNative
        nestedSemanticFactsNative)
      nestedRecursorNodePublicNative)
    nestedRecursorNodeSoundnessNative

private def nestedRecursorWrapPatternNative : Array Lean.Name :=
  nativeUnion
    (nativeUnion
      (nativeUnion nestedRecursorRepresentationNative
        nestedSemanticFactsNative)
      nestedRecursorWrapPublicNative)
    nestedRecursorWrapSoundnessNative

private def nestedRecursorPublicNative : Array Lean.Name :=
  nestedRecursorPublicNativeSeries "nestedRecursorCatalog_box" 1 ++
    nestedRecursorPublicNativeSeries "nestedRecursorCatalog_node" 4 ++
    nestedRecursorPublicNativeSeries "nestedRecursorCatalog_tree" 3 ++
    nestedRecursorPublicNativeSeries "nestedRecursorCatalog_treeRec" 5 ++
    nestedRecursorPublicNativeSeries "nestedRecursorCatalog_treeRecOne" 6 ++
    nestedRecursorPublicNativeSeries "nestedRecursorCatalog_wrap" 2 ++
    nestedRecursorPublicNativeSeries "nestedRecursorNameOf_node" 4 ++
    nestedRecursorPublicNativeSeries "nestedRecursorNameOf_tree" 3 ++
    nestedRecursorPublicNativeSeries "nestedRecursorNameOf_treeRec" 5 ++
    nestedRecursorPublicNativeSeries "nestedRecursorNameOf_treeRecOne" 6 ++
    nestedRecursorPublicNativeSeries "nestedRecursorNameOf_wrap" 2

private def nestedRecursorMemberShapeNative : Array Lean.Name :=
  nestedRecursorNativeSeries `Ix.Tc.Verify.Inductive.NestedAdmission
    "nestedMemberShapeFactsNative" 4

private def nestedRecursorAdmissionFactsNative : Array Lean.Name :=
  nestedRecursorAdmissionNativeSeries "nestedBlocksDistinct" ++
    nestedRecursorAdmissionNativeSeries "nestedBoxDirectOwner" ++
    nestedRecursorAdmissionNativeSeries
      "nestedNodeDirectConstructorComplete" ++
    nestedRecursorAdmissionNativeSeries "nestedRecursorNodeTypeRawNative" ++
    nestedRecursorAdmissionNativeSeries "nestedRecursorTreeTypeRawNative" ++
    nestedRecursorAdmissionNativeSeries "nestedTreeDirectOwnerComplete" ++
    nestedRecursorAdmissionNativeSeries "nestedWrapDirectConstructor" ++
    nestedRecursorAdmissionNativeSeries "treeRecDirectOwner" ++
    nestedRecursorAdmissionNativeSeries "treeRecNotFamily" ++
    nestedRecursorAdmissionNativeSeries "treeRecOneDirectOwner" ++
    nestedRecursorAdmissionNativeSeries "treeRecOneNotFamily"

private def nestedRecursorRegisteredRuleNative : Array Lean.Name :=
  nestedRecursorPatternNativeSeries "treeNodeRuleHeadNative" ++
    nestedRecursorPatternNativeSeries "treeNodeRuleRawNative" ++
    nestedRecursorPatternNativeSeries "treeRecOneTypeRawNative" ++
    nestedRecursorPatternNativeSeries "treeRecTypeRawNative" ++
    nestedRecursorPatternNativeSeries "treeWrapRuleHeadNative" ++
    nestedRecursorPatternNativeSeries "treeWrapRuleRawNative"

private def nestedRecursorBlockLookupNative : Array Lean.Name :=
  nestedRecursorFixtureNativeSeries "nestedRecursorBlockLoadedNative" ++
    nestedRecursorFixtureNativeSeries
      "nestedRecursorFamilyBlockLoadedNative"

private def nestedRecursorAtomicAdmissionNative : Array Lean.Name :=
  let withSemantics := nativeUnion nestedRecursorRepresentationNative
    nestedRecursorSemanticNative
  let withPublic := nativeUnion withSemantics nestedRecursorPublicNative
  let withShapes := nativeUnion withPublic nestedRecursorMemberShapeNative
  let withAdmission := nativeUnion withShapes nestedRecursorAdmissionFactsNative
  let withRules := nativeUnion withAdmission nestedRecursorRegisteredRuleNative
  let withNode := nativeUnion withRules nestedRecursorNodeSoundnessNative
  let withWrap := nativeUnion withNode nestedRecursorWrapSoundnessNative
  nativeUnion withWrap nestedRecursorBlockLookupNative

private def nestedRecursorOperationalNative : Array Lean.Name :=
  nestedRecursorFixtureNativeSeries "nestedCompiledIdentityFactsNative" 7 ++
    nestedRecursorFixtureNativeSeries "nestedCompilerGroundedNative" ++
    nestedRecursorFixtureNativeSeries "nestedCompilerSucceededNative" ++
    nestedRecursorFixtureNativeSeries "nestedRecursorFamilySucceededNative" ++
    nestedRecursorFixtureNativeSeries "nestedRecursorKernelSucceededNative" ++
    nestedRecursorFixtureNativeSeries "recursorEntriesUniqueNative" ++
    nestedRecursorFixtureNativeSeries "recursorEntryIdsNative" ++
    nestedRecursorFixtureNativeSeries "recursorIngressSucceededNative" ++
    #[nativeAxiom `Ix.Tc.Inductive
      `Ix.Tc.RecM.canonicalAuxOrder._native.native_decide.ax_9]

private def nestedRecursorAtomicClosureNative : Array Lean.Name :=
  nativeUnion nestedRecursorAtomicAdmissionNative
    nestedRecursorOperationalNative

private def nestedRestoredPatternUpstreamDebt : Array Lean.Name := #[
  ``Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
  ``Lean4Lean.VEnv.IsDefEqU.sort_inv
]

private def booleanAcceptanceNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Driver.BooleanAcceptance name

private def serializedBooleanNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Ingress.SerializedBoolean name

private def literalBlobsNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Tc.Verify.Ingress.LiteralBlobs name

/- The explicit Boolean one-family admission consumes the finite catalog,
ingress, generation, rule, and pattern facts below.  Checker executions are
kept out of this shared semantic slice so the one-family root cannot inherit
them merely because the larger end-to-end witness also records those runs. -/
private def booleanSemanticFixtureNative : Array Lean.Name := #[
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_3,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.enumerationShapeNative._native.native_decide.ax_1_6,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.enumerationShapeNative._native.native_decide.ax_1_7,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseRuleBinderCoreNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseRuleFieldsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseRuleRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseRuleScopedNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseRuleSizeBoundNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyConstructorCountNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntriesUniqueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryAtOneNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryAtTwoNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryAtZeroNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryIdsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyMemberKidsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.generationCtorPairOne._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.nameOfFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.nameOfTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.sourceConstructorOne._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueRuleBinderCoreNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueRuleFieldsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueRuleRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueRuleScopedNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueRuleSizeBoundNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_2
]

private def booleanSemanticAdmissionNative : Array Lean.Name :=
    nameNative ++ #[
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorOwnerNative._native.native_decide.ax_1_1
] ++ booleanSemanticFixtureNative

/- The concrete Boolean end-to-end witness additionally evaluates the real
block loads, checker branches, content-address context, and canonical
auxiliary ordering.  Keep every fixture-local native proof explicit rather
than treating the witness as one opaque executable assumption. -/
private def booleanEnumerationNative : Array Lean.Name :=
    inductiveNative ++ #[
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyBodySucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyClassificationSucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorBlockLoadedAfterFamilyNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorBodySucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorClassificationSucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorOwnerNative._native.native_decide.ax_1_1
] ++ booleanSemanticFixtureNative

/- The E3-S family-body bridge consumes only the family-side slice of the
full end-to-end Boolean witness.  Keep this narrower than
`booleanEnumerationNative`: in particular it must not inherit the executable
recursor run, kernel-run, generated-rule, or recursor-ingress facts merely
because the larger E2b witness uses them. -/
private def booleanFamilyBodyNative : Array Lean.Name := inductiveNative ++ #[
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyBodySucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyClassificationSucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_3,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyConstructorCountNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntriesUniqueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryAtOneNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryAtTwoNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryAtZeroNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryIdsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyMemberKidsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.nameOfFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.nameOfTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.sourceConstructorOne._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_2
]

/-- Exact evaluator boundary of the final E3-S Boolean whole-driver witness.
This is intentionally narrower than `booleanEnumerationNative`: the release
root consumes the generated Theory certificate and exact physical links, but
does not inherit the earlier standalone body/kernel executions as semantic
authority for the serial run. -/
def booleanDriverNative : Array Lean.Name := inductiveNative ++ #[
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.buildAnonWorkNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.checkEnvAnonNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseProjectionEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseProjectionEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseProjectionEntry._native.native_decide.ax_1_3,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyBlockEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyBlockEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyBlockEntry._native.native_decide.ax_1_3,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyProjectionEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyProjectionEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyProjectionEntry._native.native_decide.ax_1_3,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyTargetsNonemptyNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorBlockEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorBlockEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorBlockEntry._native.native_decide.ax_1_3,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorProjectionEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorProjectionEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorProjectionEntry._native.native_decide.ax_1_3,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorTargetsNonemptyNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.sourceAddressesNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.sourceAddressesNodupNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.sourceKeysNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueProjectionEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueProjectionEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueProjectionEntry._native.native_decide.ax_1_3,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorOwnerNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_3,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.enumerationShapeNative._native.native_decide.ax_1_6,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.enumerationShapeNative._native.native_decide.ax_1_7,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseRuleBinderCoreNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseRuleFieldsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseRuleRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseRuleScopedNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseRuleSizeBoundNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyConstructorCountNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntriesUniqueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryAtOneNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryAtTwoNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryAtZeroNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryIdsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyMemberKidsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.familyTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.generationCtorPairOne._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.nameOfFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.nameOfTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.sourceConstructorOne._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueRuleBinderCoreNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueRuleFieldsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueRuleRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueRuleScopedNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueRuleSizeBoundNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Tc.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_2
]

/-- Exact evaluator boundary of the serialized T0 Boolean certificate.  Each
closed computation is named so changes in the byte, eager, lazy, dependency,
or driver slices are visible independently in the trust manifest. -/
def serializedBooleanNative : Array Lean.Name := booleanDriverNative ++ #[
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.blobKeysNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.buildAnonWorkNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.checkEnvAnonNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.decodeSucceededNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.eagerBlockKeysClassifiedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.eagerFalseNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.eagerFamilyBlockNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.eagerFamilyNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.eagerKeysClassifiedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.eagerRecursorBlockNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.eagerRecursorNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.eagerSucceededNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.eagerTrueNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.eagerWorkNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.encodeSucceededNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.falseProjectionEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.falseProjectionEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.falseProjectionHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.falseProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.familyBlockEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.familyBlockEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.familyBlockHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.familyBlockLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.familyProjectionEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.familyProjectionEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.familyProjectionHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.familyProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.familyTargetsNonemptyNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFalseLoadedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFamilyBlockKeysNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFamilyBlockNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFamilyKeysClassifiedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFamilyLoadedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFamilySucceededNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFinalBlockKeysClassifiedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFinalFalseNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFinalFamilyBlockNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFinalFamilyNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFinalRecursorBlockNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFinalRecursorNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyFinalTrueNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyRecursorKeysClassifiedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyRecursorSucceededNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.lazyTrueLoadedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.originalFalseProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.originalFamilyBlockLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.originalFamilyProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.originalRecursorBlockLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.originalRecursorProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.originalTrueProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.recursorBlockEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.recursorBlockEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.recursorBlockHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.recursorBlockLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.recursorProjectionEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.recursorProjectionEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.recursorProjectionHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.recursorProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.recursorTargetsNonemptyNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.sourceAddressesNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.sourceAddressesNodupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.sourceKeysNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.trueProjectionEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.trueProjectionEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.trueProjectionHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Tc.BooleanSerialized.trueProjectionLookupNative._native.native_decide.ax_1_1
]

/- Exact evaluator boundary of the non-vacuous literal/blob T0 fixture. -/
private def literalRoundTripNative : Array Lean.Name := nameNative ++ #[
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.blobKeysClassifiedNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.decodeSucceededNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.encodeSucceededNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.natBlobHashNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.natBlobLookupNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.natEntry._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.natEntry._native.native_decide.ax_1_2,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.natHashNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.natLoadedNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.natLookupNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.natSucceededNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.sourceAddressesClassifiedNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.sourceAddressesNodupNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.sourceKeysClassifiedNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.stringBlobHashNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.stringBlobLookupNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.stringEntry._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.stringEntry._native.native_decide.ax_1_2,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.stringHashNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.stringLoadedNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.stringLookupNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.stringSucceededNative._native.native_decide.ax_1_1
]

private def malformedConstantNative : Array Lean.Name :=
  canonicalPrimitivesNative.push <| literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.malformedConstantRejectedNative._native.native_decide.ax_1_1

private def malformedBlobNative : Array Lean.Name :=
  canonicalPrimitivesNative.push <| literalBlobsNativeAxiom
    `Ix.Tc.SerializedLiteralBlobs.malformedBlobRejectedNative._native.native_decide.ax_1_1

/- Direct upstream `sorryAx` origins.  Listing the declarations, rather than
merely allowing `sorryAx`, makes upstream debt movement visible in review.
The certificate-bearing Lean4Lean pin discharges the former `VInductDecl.WF`,
`VEnv.addInduct`, `VEnv.addInduct_WF`, and `TrProj` origins. -/
private def forallEInv : Lean.Name :=
  ``Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified
private def sortInv : Lean.Name := ``Lean4Lean.VEnv.IsDefEqU.sort_inv

private def typingDebt : Array Lean.Name :=
  #[forallEInv, sortInv]

/- P0's concrete projection adapter consumes Lean4Lean's structural laws.
Its uniqueness law reaches the named registered-structure inversion theorem;
the context-defeq law also crosses Lean4Lean's current unique-typing boundary
and therefore inherits the two L2 inversion origins.  Keep this exact rather
than allowing the remainder of the executable inductive-fixture debt. -/
private def projectionDebt : Array Lean.Name :=
  typingDebt.push ``Lean4Lean.VEnv.WF.registeredStructureHeadInversion

/- The empty legacy whole-`KEnv` inductive path is forbidden from every G2b
consumer root.  Keeping this list in the executable audit prevents an
innocent-looking helper from reintroducing the old `nomatch` dependency. -/
private def legacyWholeEnv : Array Lean.Name := #[
  ``Ix.Tc.AddKInduct,
  ``Ix.Tc.AddKInduct.to_addInduct,
  ``Ix.Tc.TrKEnv',
  ``Ix.Tc.TrKEnv
]

/- E2a is intentionally a Theory-only certificate consumer. These
checker/catalog/pattern declarations must not enter its dependency graph. -/
private def certificateAdapterForbidden : Array Lean.Name := #[
  ``Ix.Tc.Catalog,
  ``Ix.Tc.RawInductiveConstRel,
  ``Ix.Tc.RawRecursorRuleRel,
  ``Ix.Tc.RawRecursorRulePatternRel,
  ``Ix.Tc.InductiveOracle,
  ``Lean4Lean.TrProj
]

/- `AnnotatedPi`'s upstream certificate is produced by Lean4Lean's executable
normalization pipeline, so it cannot satisfy the earlier closed-form
certificate quarantine against `TrProj`.  It must still remain independent of
all Ix catalog, checker-pattern, and oracle authority. -/
private def annotatedPiCertificateForbidden : Array Lean.Name := #[
  ``Ix.Tc.Catalog,
  ``Ix.Tc.RawInductiveConstRel,
  ``Ix.Tc.RawRecursorRuleRel,
  ``Ix.Tc.RawRecursorRulePatternRel,
  ``Ix.Tc.InductiveOracle
]

/- The pre-TrustedBody delta route admitted successful unfolding through a broad
reflection oracle and arbitrary cache-write authority.  The final K1 closure
must use exact trusted declaration certificates instead. -/
private def legacyDeltaAuthority : Array Lean.Name := #[
  ``Ix.Tc.UnfoldCacheWriteOracle,
  ``Ix.Tc.DeltaUnfoldReflection,
  ``Ix.Tc.RecM.DeltaUnfoldContext,
  ``Ix.Tc.RecM.FullWhnfStepContext.ofDelta
]

private def k1ForbiddenDependencies : Array Lean.Name :=
  legacyWholeEnv ++ legacyDeltaAuthority

/- Bounded recursive-method and checker roots must not silently regain the
all-depth, single-support closure interface whose finite-sort obstruction is
proved below.  The legacy declarations remain audited as compatibility
artifacts while consumers migrate. -/
private def legacyAllDepthKnot : Array Lean.Name := #[
  ``Ix.Tc.RecursiveMethodClosureContext,
  ``Ix.Tc.RecursiveMethodClosureContext.closedAt,
  ``Ix.Tc.RecursiveMethodClosureContext.methodsN,
  ``Ix.Tc.RecursiveMethodClosureContext.fullInferenceContext,
  ``Ix.Tc.RecursiveMethodClosureContext.next_fullInferenceWFAt,
  ``Ix.Tc.RecursiveMethodClosureContext.methodsN_fullInferenceWFAt,
  ``Ix.Tc.RecursiveMethodClosureContext.publicInfer_full_wf
]

private def boundedKnotForbiddenDependencies : Array Lean.Name :=
  k1ForbiddenDependencies ++ legacyAllDepthKnot

/- E2c occurrence-validation roots must be derived from the production run,
not from the ambient semantic inductive oracle retained by E2b. -/
private def occurrenceValidationForbiddenDependencies : Array Lean.Name :=
  boundedKnotForbiddenDependencies.push ``Ix.Tc.InductiveOracle

/- Existing semantic admission returns the shared `TrustedCatalogLog`, whose
inductive declaration necessarily mentions its legacy ambient constructor.
Constructor-insensitive dependency traversal therefore cannot forbid the
`InductiveOracle` type itself here.  Instead, quarantine every operation that
materializes or admits an oracle-selected future world. -/
private def oracleWorldMaterialization : Array Lean.Name := #[
    ``Ix.Tc.VerifyWorld.admitOracle,
    ``Ix.Tc.VerifyWorld.le_admitOracle,
    ``Ix.Tc.OracleBlockCertificate.admit,
    ``Ix.Tc.OracleBlockCertificate.admitState,
    ``Ix.Tc.RecM.certifyOracleBackedBlock,
    ``Ix.Tc.RecM.certifyOracleBackedAdmittedBlock,
    ``Ix.Tc.SingletonFamilyCatalogLink.oracle,
    ``Ix.Tc.SingletonRecursorCatalogLink.oracle,
    ``Ix.Tc.InductiveOracle.reindex,
    ``Ix.Tc.InductiveOracle.restageMissing,
    ``Ix.Tc.IndexedRecursivePattern.oracle,
    ``Ix.Tc.IndexedRecursiveFixture.recursorBlockOracle,
    ``Ix.Tc.IndexedRecursiveFixture.recursorAtomicAdmission
]

private def existingSemanticBlockForbiddenDependencies : Array Lean.Name :=
  boundedKnotForbiddenDependencies ++ oracleWorldMaterialization

/- K2S keeps the global suffix model as a compatibility surface only.  The
finite positive-fuel construction must neither manufacture that model nor
reach the older public adapters that consume it. -/
private def legacyGlobalSuffix : Array Lean.Name := #[
  ``Ix.Tc.KernelSuffixModel,
  ``Ix.Tc.ScopedKernelSuffixModel.toKernelSuffixModel,
  ``Ix.Tc.PropositionClassifierContext,
  ``Ix.Tc.RecursiveMethodRunContext,
  ``Ix.Tc.TcM.whnf.wf_legacy,
  ``Ix.Tc.TcM.infer.wf_legacy,
  ``Ix.Tc.TcM.isDefEq.wf_legacy,
  ``Ix.Tc.TcM.checkConst.wf_legacy
]

private def scopedK2SForbiddenDependencies : Array Lean.Name :=
  boundedKnotForbiddenDependencies ++ legacyGlobalSuffix

private def canonicalRecursorForbiddenDependencies : Array Lean.Name :=
  scopedK2SForbiddenDependencies ++ oracleWorldMaterialization

private def certificateBackedDriverForbiddenDependencies : Array Lean.Name :=
  scopedK2SForbiddenDependencies ++ oracleWorldMaterialization

-- The generated code for this deliberately exhaustive manifest contains more
-- than nineteen hundred nested array pushes.  Keep the compiler's structural
-- recursion budget above the manifest size so adding audited roots cannot make
-- the audit definition itself fail to compile.
set_option maxRecDepth 100000

private def roots : Array RootAllowance := #[
  -- Level decision procedures.
  { root := ``Ix.Tc.univEq_sound, standardAxioms := standard },
  { root := ``Ix.Tc.univGeq_sound, standardAxioms := standard },

  -- Memoized expression walkers against their pure specifications.
  { root := ``Ix.Tc.lift_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.subst_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.simulSubst_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.instantiateRev_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  -- There is not yet an API-level `abstractFVars_spec`; protect the current
  -- walker master until that final wrapper replaces it.
  { root := ``Ix.Tc.abstractFVarsCached_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.TcM.instantiateUnivParams_wf,
    standardAxioms := standard, nativeAxioms := levelNative },

  -- G3a finite run support and generated-term resource bounds.
  { root := ``Ix.Tc.KExpr.LiftReach.finite,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative },
  { root := ``Ix.Tc.KExpr.SubstReach.finite,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative },
  { root := ``Ix.Tc.KExpr.InstUnivReach.finite,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := levelNative },
  { root := ``Ix.Tc.WalkerRequest.reach_finite,
    standardAxioms := standard,
    nativeAxioms := levelNative },
  { root := ``Ix.Tc.InternTable.exprSupport_finite,
    standardAxioms := standard },
  { root := ``Ix.Tc.RunSupport.collisionFree_of_le,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.RunSupport.singleton_collisionFree,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.WalkerRequest.Bounds.lift_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.WalkerRequest.Bounds.subst_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.CheckConstSupport.initial_support,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.CheckConstSupport.lift,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.CheckConstSupport.subst,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.CheckConstSupport.instUniv,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.CheckConstSupport.mono,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.CheckConstSupport.scope,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.ResourceBounds.mono,
    standardAxioms := standard,
    nativeAxioms := expressionNative },
  { root := ``Ix.Tc.AmbientNat.checkSupport,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.resourceBounds,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.supportAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- G3b closes the remaining formalized walker/direct-intern families and
  -- ties the exact finite request list to an actual TcM computation.
  { root := ``Ix.Tc.KExpr.SimulSubstReach.finite,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative },
  { root := ``Ix.Tc.KExpr.InstRevReach.finite,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative },
  { root := ``Ix.Tc.KExpr.AbstractReach.finite,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.WalkerRequest.univReach_finite,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.InternTable.univSupport_finite,
    standardAxioms := standard },
  { root := ``Ix.Tc.RunSupport.pair_collisionFree,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.WalkerRequest.Bounds.simulSubst_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.WalkerRequest.Bounds.instRev_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.WalkerRequest.Bounds.abstractFVars_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.abstractFVars_eq,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.InternPreservesUnivs.pure,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.InternPreservesUnivs.runWalk,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.WalkPreservesUnivs.pure,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.WalkPreservesUnivs.bind,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.WalkPreservesUnivs.scratchGet,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.WalkPreservesUnivs.scratchInsert,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.WalkPreservesUnivs.liftIntern,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.WalkPreservesUnivs.internExpr,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.lift_preservesUnivs,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.subst_preservesUnivs,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.simulSubst_preservesUnivs,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.instantiateRev_preservesUnivs,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.abstractFVars_preservesUnivs,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.WalkerRequest.Bounds.abstractFVarsCached_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.CheckConstSupport.initial_univ_support,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.CheckConstSupport.internExpr,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.CheckConstSupport.internUniv,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.CheckConstSupport.simulSubst,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.CheckConstSupport.instRev,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.CheckConstSupport.abstractFVars,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.ExecutionRequests.bind,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.ExecutionRequests.tryCatch,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.ExecutionRequests.runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.ExecutionRequests.isolateCheckErrors,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.ExecutionRequests.modify,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.ExecutionRequests.weaken,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.ExecutionRequests.of_eq,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.ExecutionRequests.intern_eq_of_nil,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RunAssumptions.initial,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.requestBounds,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RunAssumptions.internExpr_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.internUniv_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunSupport.CoversIntern.of_expr_univs,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RunAssumptions.lift_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.subst_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.simulSubst_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.instRev_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.abstractFVarsCached_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.abstractFVars_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.instantiateUnivParams_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.runIntern_supported_wf,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RunAssumptions.lift_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.subst_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.simulSubst_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.instRev_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.abstractFVars_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.instUniv_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.AmbientNat.supportExecution,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.runAssumptions,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Expression translation, typing, uniqueness, and defeq bridges.
  { root := ``Ix.Tc.TrKExprS.instL,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.TrKExprS.inst,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.TrKExprS.inst_let,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.TrKExprS.inst_let_lbr,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.TrKExprS.wf, standardAxioms := standard },
  { root := ``Ix.Tc.TrKExpr.wf, standardAxioms := standard },
  { root := ``Ix.Tc.TrKExprS.uniq,
    standardAxioms := standard, sorryOrigins := typingDebt },
  { root := ``Ix.Tc.TrKExprS.defeqDFC,
    standardAxioms := standard, sorryOrigins := typingDebt },
  { root := ``Ix.Tc.TrKExpr.defeq,
    standardAxioms := standard, sorryOrigins := typingDebt },

  -- Legacy whole-environment compatibility interfaces.  G2b consumer roots
  -- below are forbidden from depending on these declarations.
  { root := ``Ix.Tc.TrKEnv.wf,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrKEnv.find?,
    standardAxioms := standard },
  { root := ``Ix.Tc.TcM.tick.tcInv,
    standardAxioms := standard },
  { root := ``Ix.Tc.TcM.instantiateUnivParams.tcInv,
    standardAxioms := standard, nativeAxioms := levelNative },

  -- The narrow upstream-context dependency behind translation uniqueness.
  { root := ``Ix.Tc.KVLCtx.IsDefEq.find?_uniq,
    standardAxioms := standard },

  -- Dual-context reconciliation entry points used by the checker proofs.
  { root := ``Ix.Tc.CtxRecon.wf, standardAxioms := standard },
  { root := ``Ix.Tc.CtxRecon.lookupVar,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.CtxRecon.fvar_resolves,
    standardAxioms := standard },

  -- G1a's non-circular world and one-way lazy-load boundary.
  { root := ``Ix.Tc.VerifyWorld.ofCatalog_catalogued_not_trusted,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.VerifyWorld.LE.trans,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.VerifyWorld.LE.catalogued_iff,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.LoadedAgrees.world_iff,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.LoadedAgrees.insert,
    standardAxioms := standard },
  { root := ``Ix.Tc.LoadedAgrees.of_extension,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.VerifyWorld.ofCatalog_loaded,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.VerifyWorld.ofCatalog_loaded_not_trusted,
    standardAxioms := standard },

  -- G1b's raw/pending boundary.  Raw correspondence has no declaration-WF
  -- premise; the fixture roots pin the concrete non-WF pending case.
  { root := ``Ix.Tc.RawExprRel.mono,
    standardAxioms := standard },
  { root := ``Ix.Tc.RawExprRel.reference_resolved,
    standardAxioms := standard },
  { root := ``Ix.Tc.RawDeclRel.mono,
    standardAxioms := standard },
  { root := ``Ix.Tc.PendingDecl.no_target_lookup,
    standardAxioms := standard },
  { root := ``Ix.Tc.PendingDecl.no_self_expr_reference,
    standardAxioms := standard },
  { root := ``Ix.Tc.PendingDecl.not_trustedDecl,
    standardAxioms := standard },
  { root := ``Ix.Tc.IllTypedPending.pending_but_not_wf,
    standardAxioms := standard },
  { root := ``Ix.Tc.IllTypedPending.loaded_pending_but_not_wf,
    standardAxioms := standard },

  -- G1c's trusted-only catalog log and explicit-WF promotion boundary.
  { root := ``Ix.Tc.RawDeclRel.wf_le,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrustedCatalogLog.wf,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrustedCatalogLog.catalogued,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrustedCatalogLog.find,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrustedCatalogRel.ofCatalog,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrustedCatalogRel.find,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrustedCatalogEntry.recursorRule,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrustedCatalogRel.recursorRule,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrustedCatalogEntry.recursorPattern,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrustedCatalogRel.recursorPattern,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrustedDecl.lookup,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrustedCatalogRel.lookup,
    standardAxioms := standard },
  { root := ``Ix.Tc.Promotes.trans,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.TrustedCatalogRel.promote,
    standardAxioms := standard },
  { root := ``Ix.Tc.IllTypedPending.trustedCatalogRel,
    standardAxioms := standard },
  { root := ``Ix.Tc.WellTypedPromotion.promotes,
    standardAxioms := standard },

  -- G1d's world-based concrete-state invariant.  Loading stays
  -- representation-only, promotion requires a fresh WF witness, and the
  -- fixed-world Hoare roots pin no-promotion behavior on both outcomes.
  { root := ``Ix.Tc.TcStateWF.of_consts_eq,
    standardAxioms := standard },
  { root := ``Ix.Tc.TcStateWF.load,
    standardAxioms := standard },
  { root := ``Ix.Tc.TcStateWF.promote,
    standardAxioms := standard },
  { root := ``Ix.Tc.TcStateWF.find?,
    standardAxioms := standard },
  { root := ``Ix.Tc.TcInv.find?,
    standardAxioms := standard },
  { root := ``Ix.Tc.IllTypedPending.tcInv_pending_but_not_wf,
    standardAxioms := standard },
  { root := ``Ix.Tc.TcM.tick.tcStateWF,
    standardAxioms := standard },
  { root := ``Ix.Tc.TcM.instantiateUnivParams.tcStateWF,
    standardAxioms := standard, nativeAxioms := levelNative },

  -- Pin A / E2a: the certified-generation adapter may use only Lean4Lean
  -- Theory transaction facts, never Ix checker/catalog/pattern authority.
  { root := ``Ix.Tc.CertifiedGenerationTransaction.trace,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Tc.CertifiedGenerationTransaction.afterWF,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Tc.CertifiedGenerationTransaction.facts,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },

  -- L4L-08's Theory-only block adapter preserves the same quarantine while
  -- exposing one atomic all-families/all-constructors/all-recursors/all-rules
  -- transaction rather than a sequence of singleton admissions.
  { root := ``Ix.Tc.CertifiedBlockGenerationTransaction.trace,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Tc.CertifiedBlockGenerationTransaction.afterWF,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Tc.CertifiedBlockGenerationTransaction.facts,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },

  -- E2c retains the exact Lean4Lean candidate-producer equation alongside
  -- the certified Theory transaction.  Unlike the Theory-only adapter above,
  -- this Verify-backed bridge deliberately inherits the pinned analyzer debt.
  { root := ``Ix.Tc.ProducedGenerationTransaction.facts,
    standardAxioms := standard,
    upstreamAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Tc.ExactProducedGenerationTransaction.facts,
    standardAxioms := standard,
    upstreamAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },

  -- First genuine multi-family semantic witness: Tree/TreeList has two
  -- motives and recursors, five flattened constructors/rules, sibling
  -- recursion in both directions, and one recursive occurrence below a Pi.
  { root := ``Ix.Tc.MutualTreeCertificateFixture.breadth,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Tc.MutualTreeCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Tc.MutualTreeCertificateFixture.finalEnvWF,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },

  -- The production compiler emits this SCC in physical order
  -- `TreeList, Tree`.  All seven family/constructor entries are linked to the
  -- complete catalog and admitted atomically without the pending recursor
  -- pattern/WF witnesses used by the later conditional closure.
  { root := ``Ix.Tc.MutualTreeFixture.mutualFamilyAtomicClosure,
    standardAxioms := standard,
    nativeAxioms := mutualFamilyNative },

  -- E2c's first concrete breadth witness is the exact staged `IndexedVec`
  -- certificate: one parameter, one changing index, a recursive field, large
  -- elimination, and both generated rules.  It remains Theory-only here;
  -- production Ix catalog correspondence is audited in the later linkage.
  { root :=
      ``Ix.Tc.IndexedRecursiveCertificateFixture.transaction_generation,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Tc.IndexedRecursiveCertificateFixture.breadth,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Tc.IndexedRecursiveCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Tc.IndexedRecursiveCertificateFixture.producedCertificate_eq,
    standardAxioms := standard,
    upstreamAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Tc.IndexedRecursiveCertificateFixture.producedToCertified_eq,
    standardAxioms := standard,
    upstreamAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Tc.IndexedRecursiveCertificateFixture.producerLinkedFacts,
    standardAxioms := standard,
    upstreamAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },

  -- The next honest one-family breadth witness is `Acc`: its sole recursive
  -- occurrence is reached beneath a two-binder Pi telescope, and the
  -- generated induction hypothesis is therefore itself a function. Like the
  -- IndexedVec certificate, these roots remain entirely on the Theory side
  -- of the catalog/checker boundary.
  { root :=
      ``Ix.Tc.RecursivePiCertificateFixture.transaction_generation,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Tc.RecursivePiCertificateFixture.breadth,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Tc.RecursivePiCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },

  -- `AnnotatedPi` is the first certified singleton whose recursive-Pi
  -- candidate is genuinely normalized: the stored constructor retains
  -- `outParam Prop`, while the analyzer-owned candidate exposes `Prop`.
  -- These certificate roots remain entirely on the Theory side.
  { root :=
      ``Ix.Tc.AnnotatedPiCertificateFixture.transaction_generation,
    standardAxioms := standard,
    upstreamAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Tc.AnnotatedPiCertificateFixture.breadth,
    standardAxioms := standardWithoutChoice,
    nativeAxioms := annotatedPiCertificateBreadthNative,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Tc.AnnotatedPiCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    upstreamAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Tc.AnnotatedPiCertificateFixture.producerLinkedFacts,
    standardAxioms := standard,
    upstreamAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },

  -- `AliasFormer` keeps the stored family result at `TypeFamilyAlias`, while
  -- the analyzer-owned candidate unfolds that reducible dependency to
  -- `Type`.  These roots certify the non-identity family-result view without
  -- Ix catalog, checker-pattern, or oracle authority.
  { root :=
      ``Ix.Tc.AliasFormerCertificateFixture.transaction_generation,
    standardAxioms := standard,
    upstreamAxioms := aliasFormerUpstreamAxioms,
    sorryOrigins := aliasFormerUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Tc.AliasFormerCertificateFixture.breadth,
    standardAxioms := standardWithoutChoice,
    nativeAxioms := aliasFormerCertificateBreadthNative,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Tc.AliasFormerCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    upstreamAxioms := aliasFormerUpstreamAxioms,
    sorryOrigins := aliasFormerUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Tc.AliasFormerCertificateFixture.producerLinkedFacts,
    standardAxioms := standard,
    upstreamAxioms := aliasFormerUpstreamAxioms,
    sorryOrigins := aliasFormerUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },

  -- `AliasRec` retains `RecAlias AliasRec` in the stored constructor while
  -- certifying the direct-recursive checked field.  The adapter packages the
  -- pinned upstream generation/WF replay without Ix-side semantic authority.
  { root :=
      ``Ix.Tc.AliasRecCertificateFixture.transaction_generation,
    standardAxioms := standard,
    upstreamAxioms := aliasRecUpstreamAxioms,
    sorryOrigins := aliasRecUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Tc.AliasRecCertificateFixture.breadth,
    standardAxioms := standard,
    upstreamAxioms := aliasRecUpstreamAxioms,
    nativeAxioms := aliasRecCertificateBreadthNative,
    sorryOrigins := aliasRecUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Tc.AliasRecCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    upstreamAxioms := aliasRecUpstreamAxioms,
    sorryOrigins := aliasRecUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },

  -- E2c occurrence-validation seam.  These roots expose the selected loaded
  -- family and strengthen every production guard into the elementwise
  -- valid-inductive-application invariant, without oracle authority.
  { root :=
      ``Ix.Tc.RecM.checkPositiveRecursiveApplicationPreconditions_success_iff,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.positiveUniverseArgumentsAgree_eq_true_iff,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.positiveIndicesIndependent_eq_true_iff,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositiveParametersFrom_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositiveParameters_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.PositiveParameterComparisonTrace.sound,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.PositiveParameterComparisonTrace.theoryDefEq,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.ValidPositiveRecursiveApplicationHeader.theoryParameters,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.PositiveParameterComparisonTrace.theoryDefEqScoped,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    -- This is the K2S instantiation bridge, not the oracle-free occurrence
    -- theorem above. `ScopedWhnfStateInv` contains `TrustedCatalogLog`, whose
    -- ambient constructor names `InductiveOracle`; semantic use remains
    -- confined to the projected `ScopedWFAtOn.isDefEq` field.
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.ValidPositiveRecursiveApplicationHeader.theoryParametersScoped,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.positivityGroupMatches_eq_true_iff,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.SpecializationIdentityFixture.semanticUniverseEquality_does_not_collapse_specialization,
    standardAxioms := standard,
    nativeAxioms := specializationIdentityNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.checkPositiveRecursiveApplicationHeader_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.PositiveRecursiveApplicationHeaderTrace.valid,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositiveRecursiveApplicationHeader_valid,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositiveRecursiveApplication_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.PositiveRecursiveApplicationTrace.valid,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositiveRecursiveApplication_valid,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- E2c production-traversal seam.  Root-free domains are state-preserving;
  -- direct recursive-family applications inherit the oracle-free occurrence
  -- invariant; and forall success exposes the decremented recursive run plus
  -- exact local-context restoration.
  { root := ``Ix.Tc.RecM.withLctxRestoration_success,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositivityDomainFuel_rootFree,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositivityDomainFuel_direct,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositivityDomainFuel_direct_valid,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositivityDomainFuel_nested,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositivityDomainFuel_forall_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositivityDomainFuel_forall_negative,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Exhaustive nested positivity.  These roots expose exact header and
  -- constructor lookup, specialization selection, source-ordered constructor
  -- traversal, universe instantiation, parameter stripping/substitution,
  -- recursive field-domain checks, and context restoration.  The final root
  -- classifies every successful production domain without a branch oracle.
  { root := ``Ix.Tc.RecM.findNestedPositivityGroup?_some,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.checkNestedPositivityApplicationPreconditions_success_iff,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.checkNestedPositivityApplicationResolvedFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.checkNestedPositivityApplicationCheckedFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkNestedConstructorFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkNestedConstructorsFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.checkFreshNestedPositivityApplicationFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.stripNestedCtorParameters_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkNestedCtorFieldsLoopFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkNestedCtorFieldsFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.completeNestedConstructor_of_trace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.completeNestedConstructorList_of_trace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.completeFreshNestedPositivity_of_trace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.completeNestedPositivityChecked_of_trace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.completeNestedPositivityResolved_of_trace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.checkNestedPositivityApplicationFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.checkNestedPositivityApplicationFuel_complete,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkPositivityDomainFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- E2c nested auxiliary expansion.  The complete positivity trace emits an
  -- exact existing-or-fresh request; the flat scanner classifies every
  -- successful detector call as an unchanged pair or one fresh exact append.
  -- The source-ordered constructor and bounded-queue histories prove that the
  -- real public builder returns an aligned, duplicate-free physical/key list.
  -- The next fixture must identify its positivity request with one detector
  -- call; it cannot replace that reachability evidence with DefEq.
  { root := ``Ix.Tc.lawfulBEqNestedSpecializationKey,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedAuxiliaryHeaderRel.key_eq,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedAuxiliaryHeaderRel.positivityFlatIdentity,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedAuxiliaryAppendTrace.member_mem,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedAuxiliaryAppendTrace.key_mem,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.appendNestedAuxiliary_fresh,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.appendNestedAuxiliary_existing,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxSeenSound.empty,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxSeenSound.push,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxTransition.seenSound,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxTransition.flat_mem,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxTransition.key_mem,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxHistory.single,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxHistory.trans,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxHistory.seenSound,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxHistory.flat_mem,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxHistory.key_mem,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxQueueExact.empty,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxQueueExact.pushOriginal,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxQueueExact.transition,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.FlatAuxQueueExact.history,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.appendNestedAuxiliary_transition,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.appendNestedAuxiliary_seenSound,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.tryDetectNestedCore_transition,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.tryDetectNested_transition,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.tryDetectNested_seenSound,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.scanFlatConstructorFields_history,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.scanFlatConstructor_history,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.scanFlatConstructors_history,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.buildFlatBlockQueueStep_history,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.runBounded_flatAuxHistory,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.seedFlatBlockMembers_exact,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.buildFlatBlockWithAuxSeen_exact,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.buildFlatBlock_auxiliaryOrder,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.CompleteNestedPositivityApplicationTrace.auxiliaryRequest,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.CompleteNestedPositivityApplicationTrace.producedRequest,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Concrete E2c nested reachability.  The compiler-shaped Box/Tree fixture
  -- runs production ingress, positivity, and flat-block construction on the
  -- same `Box Tree` occurrence.  Its headline root proves that the exact
  -- fresh positivity request is retained under the audited queue invariant.
  { root := ``Ix.Tc.NestedRecursiveFixture.boxIngressRun,
    standardAxioms := standard,
    nativeAxioms := levelNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.boxIngressSucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.treeIngressRun,
    standardAxioms := standard,
    nativeAxioms := levelNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.treeIngressSucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.boxConcreteHeader,
    standardAxioms := standard,
    nativeAxioms := levelNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.boxConcreteHeaderMatchesNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nodeConcreteType,
    standardAxioms := standard,
    nativeAxioms := levelNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.nodeConcreteTypeNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.positivityRun,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.positivitySucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedWhnfRun,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.nestedWhnfSucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedWhnfResult_eq,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.nestedWhnfResultNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedActionRun,
    standardAxioms := standard,
    nativeAxioms := nestedRecursiveActionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.requestHeaderRelation,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.positivityCompleteTrace,
    standardAxioms := standard,
    nativeAxioms := nestedRecursiveActionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.boxLookupRun,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.boxLookupSucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.boxLookupConcrete_eq,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.boxLookupConcreteNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.positivityRequestProduced,
    standardAxioms := standard,
    nativeAxioms := nestedRecursiveProducedNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.positivityRequestFreshExpansion,
    standardAxioms := standard,
    nativeAxioms := nestedRecursiveFreshNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.flatBuildRun,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.flatBuildSucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.builtFlatShape,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.builtFlatShapeNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.requestedAuxiliaryPresent,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Tc.NestedRecursiveFixture.builtFlatShapeNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedAuxiliaryReachability,
    standardAxioms := standard,
    nativeAxioms := nestedRecursiveReachabilityNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Exact Lean4Lean syntax and semantic transport for the retained nested
  -- member.  The outer field reaches the fresh auxiliary; the auxiliary's
  -- own field recursively reaches the original Tree member at lower fuel.
  { root := ``Ix.Tc.NestedRecursiveFixture.treeCandidateSyntax,
    standardAxioms := standard,
    nativeAxioms := nestedTreeCandidateSyntaxNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedAuxiliaryCandidateTarget,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryCandidateTargetNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedOuterPositivityTransport,
    standardAxioms := standard,
    nativeAxioms := nestedOuterTransportNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.nestedOuterConstructorPositivityTrace,
    standardAxioms := standard,
    nativeAxioms := nestedOuterTransportNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.nestedAuxiliaryFieldProductionTrace,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryProductionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.nestedAuxiliaryPositivityTransport,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryTransportNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.nestedAuxiliaryFieldProductionTraceAt,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryProductionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.nestedAuxiliaryConstructorPositivityTraceAt,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryConstructorNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.nestedAuxiliaryConstructorPositivityTrace,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryConstructorNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.leanFlatNodeConstructorTypeValidationTrace,
    standardAxioms := standard,
    nativeAxioms := nestedNodeConstructorValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.leanFlatNodeConstructorValidationRun,
    standardAxioms := standard,
    nativeAxioms := nestedNodeConstructorValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.leanFlatWrapConstructorTypeValidationTrace,
    standardAxioms := standard,
    nativeAxioms := nestedWrapConstructorValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.leanFlatWrapConstructorValidationRun,
    standardAxioms := standard,
    nativeAxioms := nestedWrapConstructorValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Completed nested semantic transaction.  The generic adapter consumes a
  -- pinned Lean4Lean `NestedBlockCertificate`; the concrete roots then prove
  -- restored source/recursor/rule well-formedness, run Ix's real nested
  -- family checker, and admit the exact two-member source block atomically.
  -- No auxiliary flattening name, legacy inductive oracle, or pending axiom
  -- may enter this completed boundary.
  { root := ``Ix.Tc.NestedFamilyCatalogLink.translateMember,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedFamilyCatalogLink.semanticEntry,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedFamilyCatalogLink.transition,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.semanticTreeCertificate,
    standardAxioms := standard,
    nativeAxioms := nestedSemanticCertificateNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.semanticTreeTransactionFacts,
    standardAxioms := standard,
    nativeAxioms := nestedSemanticFactsNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedFamilyKernelRun,
    standardAxioms := standard,
    nativeAxioms := nestedFamilyKernelNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedFamilyBlockCertificate,
    standardAxioms := standard,
    nativeAxioms := nestedFamilyCertificateNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedFamilyAtomicAdmission,
    standardAxioms := standard,
    nativeAxioms := nestedFamilyCertificateNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.nestedSemanticTransactionClosure,
    standardAxioms := standard,
    nativeAxioms := nestedSemanticTransactionClosureNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },

  -- Completed physical nested-recursor transaction.  The compiler and
  -- ingress roots pin the actual generated block; the two pattern roots pin
  -- the restored node/wrap equations independently; the final roots require
  -- all-or-nothing family-plus-recursor admission.  The only `sorryAx`
  -- origins are two exact inversion lemmas inherited from Lean4Lean.
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedCompilerRun,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorCompilerRunNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedCompiledIdentityFacts,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorCompilerIdentityNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.recursorIngressRun,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorIngressNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root :=
      ``Ix.Tc.NestedRecursiveFixture.nestedRecursorRepresentationFacts,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorRepresentationNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.treeNodePatternRel,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorNodePatternNative,
    sorryOrigins := nestedRestoredPatternUpstreamDebt,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.treeWrapPatternRel,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorWrapPatternNative,
    sorryOrigins := nestedRestoredPatternUpstreamDebt,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedRecursorAtomicAdmission,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorAtomicAdmissionNative,
    sorryOrigins := nestedRestoredPatternUpstreamDebt,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.NestedRecursiveFixture.nestedRecursorAtomicClosure,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorAtomicClosureNative,
    sorryOrigins := nestedRestoredPatternUpstreamDebt,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },

  -- E2c generated-recursor metadata.  The seven cached header fields are
  -- derived positionally from the certified flat block and are invariant
  -- under both best-effort and complete rule population.  The final root
  -- covers the actual anonymous-mode cache insertion phase; none of these
  -- roots may recover the legacy inductive oracle.
  { root := ``Ix.Tc.GeneratedRecursorMetadata.at_of_expectedFlat,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.initialGeneratedRecursor_metadata,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursor.metadata_setRules,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursor.metadata_withRules,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursor.ty_withRules,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursor.map_metadata_modify_withRules,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursor.map_metadata_zipWithRules,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursor.map_ty_zipWithRules,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.commitGeneratedRecursorRulesAt_artifacts,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.populateOptionalGeneratedRecursorRules_metadata,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecM.populateCompleteGeneratedRecursorRules_metadata,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.populateRecursorRulesFromBlock_artifacts,
    standardAxioms := standard,
    nativeAxioms := inductiveNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.populateRecursorRulesFromBlock_metadata,
    standardAxioms := standard,
    nativeAxioms := inductiveNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.GeneratedRecursorSemantics.CanonicalRulesS.generatedRuleAt,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.GeneratedRecursorSemantics.CanonicalArtifactsS.withRules,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.GeneratedRecursorSemantics.CanonicalTypeS.canonical,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.GeneratedRecursorSemantics.CanonicalRulesS.canonical,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.GeneratedRecursorSemantics.CanonicalArtifactsS.canonical,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.GeneratedRecursorSemantics.RecM.commitGeneratedRecursorRulesAt_canonicalAt,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.buildGeneratedRecursorTypes_metadata,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.buildAndCacheGeneratedRecursors_metadata,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- E2c generated-recursor type closure. Production closes the accumulated
  -- domains through explicit right-to-left intern requests. These roots prove
  -- exact finite-support execution, operation-shaped structural translation,
  -- and equality with Lean4Lean's public canonical mixed recursor type.
  { root := ``Ix.Tc.CertifiedGenerationTransaction.generationEnv,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursorTypeClosure.opened_toCtx,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursorTypeClosure.isType_forallN_inv,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursorTypeClosure.onTel_isType_getElem,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.GeneratedRecursorTypeClosure.canonical_onTel_and_bodyType,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursorTypeClosure.canonical_domainType,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursorTypeClosure.canonical_bodyType,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.GeneratedRecursorTypeClosure.TelescopeS.of_canonical,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.GeneratedRecursorTypeClosure.closeV_eq_forallN_take,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursorTypeClosure.closeV_canonical,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursorTypeClosure.TelescopeS.close,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursorTypeClosure.run_exact,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursorTypeClosure.run_translation,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursorTypeClosure.run_canonicalType,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.GeneratedRecursorTypeClosure.buildRecType_decompose,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.GeneratedRecursorTypeClosure.buildRecType_canonical_of_body,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.IndexedRecursiveFixture.familyBuildTypeExecution,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorTypeFixtureNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.IndexedRecursiveFixture.familyBuildArtifactsExecution,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorRuleFixtureNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- E2c generated-recursor commit, selection, and exhaustive comparison.
  -- Production selection compares complete closed types through an explicit
  -- finite fold; one K2S successor layer preserves the scoped state across
  -- selection and gives semantic meaning to the repeated type and positional
  -- rule comparisons.
  { root := ``Ix.Tc.RecM.checkGeneratedRecursorFromCache_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkGeneratedRecursorFromCache_canonical,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkGeneratedRecursorFromCache_canonicalScoped,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.RecM.selectGeneratedRecursorIndex_preservesScoped,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.IndexedRecursiveFixture.familyRuleCommitExecution,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorCommitFixtureNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.IndexedRecursiveFixture.familyCacheCheckExecution,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorCheckerFixtureNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.IndexedRecursiveFixture.familyCacheCheckCanonicalScoped,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorCanonicalFixtureNative,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },

  -- E2c outer member closure and exact semantic admission.  The explicit
  -- transition bridge fixes both Theory environments and requires complete
  -- trusted provenance for every exact physical member; the existing-block
  -- specialization keeps that environment unchanged for the recursor block.
  -- Their shared log type mentions the legacy ambient constructor, so the
  -- audit forbids every oracle constructor/world-materialization operation
  -- rather than the `InductiveOracle` type name itself.
  { root :=
      ``Ix.Tc.SemanticBlockTransitionCertificate.le_admittedWorld,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.SemanticBlockTransitionCertificate.admit,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.SemanticBlockTransitionCertificate.admitState,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root :=
      ``Ix.Tc.ExistingSemanticBlockCertificate.le_admittedWorld,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.ExistingSemanticBlockCertificate.admit,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.ExistingSemanticBlockCertificate.admitState,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.OneFamilyRecursorCertificate.atomicClosure,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Tc.IndexedRecursiveFixture.familyRecursorAtomicClosure,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorAtomicClosureNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  { root := ``Ix.Tc.IndexedRecursiveFixture.producerLinkedOneFamilyClosure,
    standardAxioms := standard,
    upstreamAxioms := annotatedPiUpstreamAxioms,
    nativeAxioms := indexedProducerClosureNative,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  { root :=
      ``Ix.Tc.RecursivePiRecursorFixture.recursivePiAtomicClosure,
    standardAxioms := standard,
    nativeAxioms := recursivePiAtomicClosureNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  { root :=
      ``Ix.Tc.AnnotatedPiRecursorFixture.annotatedPiAtomicClosure,
    standardAxioms := standard,
    upstreamAxioms := annotatedPiUpstreamAxioms,
    nativeAxioms := annotatedPiAtomicClosureNative,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  { root :=
      ``Ix.Tc.AliasFormerRecursorFixture.aliasFormerAtomicClosure,
    standardAxioms := standard,
    upstreamAxioms := aliasFormerUpstreamAxioms,
    nativeAxioms := aliasFormerAtomicClosureNative,
    sorryOrigins := aliasFormerUpstreamDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  { root :=
      ``Ix.Tc.AliasRecRecursorFixture.aliasRecAtomicClosure,
    standardAxioms := standard,
    upstreamAxioms := aliasRecUpstreamAxioms,
    nativeAxioms := aliasRecAtomicClosureNative,
    sorryOrigins := aliasRecUpstreamDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },

  -- E2c flat semantic transport.  The refined flat production trace erases
  -- to the exhaustive classifier, and the operation-shaped cross-kernel
  -- contract recursively constructs Lean4Lean's retained positivity trace.
  -- Nested auxiliary expansion remains a separate explicit bridge.
  { root := ``Ix.Tc.FlatPositivityDomainTrace.toPositivityDomainTrace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Tc.FlatPositivityTraceTransport.constructorPositivityTrace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- E2c's concrete cross-kernel trace bridge.  These roots start at the
  -- exact positivity calls selected by the production IndexedVec family
  -- checker, transport those operations to Lean4Lean, and replay the complete
  -- retained constructor validator.  The direct recursive fixture has no
  -- nested auxiliary expansion; that remains the next generic E2c bridge.
  { root :=
      ``Ix.Tc.IndexedRecursiveFixture.indexedVecConsConstructorValidationRun,
    standardAxioms := standard,
    nativeAxioms := indexedConstructorValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- E2c's first production-linked indexed/recursive vertical slice.  The
  -- generated cons equation includes its predecessor recursive call; the
  -- oracle is then instantiated by exact anonymous ingress, production
  -- family/recursor checking, exact ownership, and atomic admission.  The
  -- same executable witness rejects a recursor whose stored index arity was
  -- changed while its canonical type and rules were retained.
  { root := ``Lean4Lean.VEnv.HasType.lamN_appN_beta,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.IndexedRecursivePattern.nilPatternRel,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.IndexedRecursivePattern.consPatternRel,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.IndexedRecursivePattern.oracle,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.IndexedRecursiveFixture.endToEndAcceptance,
    standardAxioms := standard,
    nativeAxioms := indexedRecursiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },

  -- Elimination-breadth regression over exact kernel declarations.  These
  -- roots compile, ingress, and run the production family/recursor checkers
  -- for both a source-universe-bearing small eliminator and `Eq`'s positive
  -- K branch, then relate the stored physical metadata to Lean4Lean's exact
  -- generation trace.
  { root := ``Ix.Tc.EliminationBreadthFixture.smallEliminationAcceptance,
    standardAxioms := standard,
    nativeAxioms := smallEliminationAcceptanceNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Tc.EliminationBreadthFixture.kTargetAcceptance,
    standardAxioms := standard,
    nativeAxioms := kTargetAcceptanceNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- E2b's singleton link and legacy oracle constructors remain audited as
  -- compatibility surfaces.  The concrete Boolean closure below no longer
  -- consumes those oracle constructors: its family block advances the exact
  -- generated Theory environment, and its recursor block consumes entries
  -- already installed there.
  { root := ``Lean4Lean.VEnv.HasType.transfer_appN_telescope,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.SingletonFamilyCatalogLink.oracle,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.SingletonRecursorCatalogLink.enumerationPatternRel,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.SingletonRecursorCatalogLink.oracle,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.certifySingletonFamilyBlock,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.certifySingletonRecursorBlock,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  -- Oracle-free semantic composition is audited independently of production
  -- execution so its native boundary contains only the finite representation,
  -- generation, equation, and pattern checks.
  { root := ``Ix.Tc.BooleanEnumerationFixture.oneFamilyAtomicClosure,
    standardAxioms := standard,
    nativeAxioms := booleanSemanticAdmissionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  -- The headline additionally joins anonymous ingress, both production
  -- block-body and branch checkers, exact physical/catalog ownership, and the
  -- composed two-stage semantic transaction in one final world.
  { root := ``Ix.Tc.BooleanEnumerationFixture.endToEndAcceptance,
    standardAxioms := standard, nativeAxioms := booleanEnumerationNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },

  -- G2a's explicit ambient-inductive assumption boundary.  Audit every
  -- oracle projection so adding a field changes this manifest, then pin the
  -- constructive Nat model and its adversarial loaded-state witness.
  { root := ``Ix.Tc.RawInductiveConstRel.mono,
    standardAxioms := standard },
  { root := ``Ix.Tc.TrKExprS.mono,
    standardAxioms := standard },
  { root := ``Ix.Tc.RegisteredRecursorRuleRhsRel.mono,
    standardAxioms := standard },
  { root := ``Ix.Tc.RegisteredRecursorRuleRhsRel.rhsTyped,
    standardAxioms := standard },
  { root := ``Ix.Tc.RawRecursorRuleRel.registeredRhs,
    standardAxioms := standard },
  { root := ``Ix.Tc.RawRecursorRuleRel.mono,
    standardAxioms := standard },
  { root := ``Ix.Tc.HeadConstN.of_varN_matches },
  { root := ``Ix.Tc.RecursorIotaPattern.matches_shape },
  { root := ``Ix.Tc.KConst.RecursorRuleAt.hasRecursorRule,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.RawRecursorRulePatternRel.mono,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.InductiveOracle.members,
    standardAxioms := standard },
  { root := ``Ix.Tc.InductiveOracle.nonempty,
    standardAxioms := standard },
  { root := ``Ix.Tc.InductiveOracle.fresh,
    standardAxioms := standard },
  { root := ``Ix.Tc.InductiveOracle.after,
    standardAxioms := standard },
  { root := ``Ix.Tc.InductiveOracle.envLE,
    standardAxioms := standard },
  { root := ``Ix.Tc.InductiveOracle.blockWF,
    standardAxioms := standard },
  { root := ``Ix.Tc.InductiveOracle.translateBlock,
    standardAxioms := standard },
  { root := ``Ix.Tc.InductiveOracle.recursorFacts,
    standardAxioms := standard },
  { root := ``Ix.Tc.InductiveOracle.recursorPatterns,
    standardAxioms := standard },
  { root := ``Ix.Tc.InductiveOracle.catalogued,
    standardAxioms := standard },
  { root := ``Ix.Tc.AmbientNat.oracle,
    standardAxioms := standard },
  { root := ``Ix.Tc.AmbientNat.nat_lookup_good,
    standardAxioms := standard },
  { root := ``Ix.Tc.AmbientNat.badDecl_not_wf,
    standardAxioms := standard },
  { root := ``Ix.Tc.AmbientNat.acceptance,
    standardAxioms := standard },

  -- G2b's C1--C3 consumer path.  These roots resolve exact concrete
  -- constants through trusted-world provenance and are mechanically barred
  -- from depending on the legacy whole-environment translation.
  { root := ``Ix.Tc.TrustedConstRel.mono,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TrustedConstRel.trKExprS_const,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TrustedCatalogRel.resolve,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcStateWF.resolve,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcInv.resolve,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.natResolved,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.natReferenceTranslates,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.bad_not_resolved,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.natResolvedInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },

  -- G4's lookup isolation, exhaustive semantic-cache provenance, monotone
  -- warm-world transport, and transactional public-check error boundary.
  { root := ``Ix.Tc.PendingDecl.lookup_isolation,
    standardAxioms := standard },
  { root := ``Ix.Tc.CacheEntry.SupportedBy.mono },
  { root := ``Ix.Tc.CacheAuthority.stable_mono,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.CacheProvenance.mono,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.CacheProvenance.pending_isolation_stable,
    standardAxioms := standard },
  { root := ``Ix.Tc.KEnv.restoreBlockCheckResultsOnError_origin,
    standardAxioms := standard },
  { root := ``Ix.Tc.CacheInvariant.mono,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.CacheInvariant.insertWhnf,
    standardAxioms := standard },
  { root := ``Ix.Tc.CacheInvariant.insertWhnfNoDelta,
    standardAxioms := standard },
  { root := ``Ix.Tc.CacheInvariant.insertWhnfNoDeltaCheap,
    standardAxioms := standard },
  { root := ``Ix.Tc.CacheInvariant.insertWhnfCore,
    standardAxioms := standard },
  { root := ``Ix.Tc.CacheInvariant.insertWhnfCoreCheap,
    standardAxioms := standard },
  { root := ``Ix.Tc.CacheInvariant.of_intern_update,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.CacheInvariant.clearReductionCaches,
    standardAxioms := standard },
  { root := ``Ix.Tc.CacheInvariant.restoreCheckCachesOnError,
    standardAxioms := standard },
  { root := ``Ix.Tc.TcM.isolateCheckErrors_error,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.TcM.reset_cache_frame,
    standardAxioms := standard,
    nativeAxioms := #[nativeAxiom `Blake3
      `Blake3.HasherOps.hash._native.native_decide.ax_1] },
  { root := ``Ix.Tc.KernelStateWF.pendingCacheIsolation,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.KernelStateWF.restoreCheckCachesOnError,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.AmbientNat.warmCache_worldTransport,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.warmCache_cannotResolvePending,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.cacheAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- K1's concrete Theory reduction meaning, exact five-way cache overlay,
  -- and real ambient-Nat warm-hit witness.  The only sorries are the already
  -- named upstream inductive-environment boundary.
  { root := ``Ix.Tc.WhnfMeaning.refl,
    standardAxioms := standard },
  { root := ``Ix.Tc.WhnfMeaning.symm,
    standardAxioms := standard },
  { root := ``Ix.Tc.WhnfMeaning.mono,
    standardAxioms := standard },
  { root := ``Ix.Tc.ExprCacheKind.isWhnf_iff },
  { root := ``Ix.Tc.WhnfCacheValid.mono,
    standardAxioms := standard },
  { root := ``Ix.Tc.WhnfCacheValid.expr,
    standardAxioms := standard },
  { root := ``Ix.Tc.CacheProvenance.isRec_of_trusted,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.IsRecCacheValid.mono,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.IsRecCacheValid.trusted,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.kernelCacheSemantics_isRec_valid,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheProvenance.whnfMeaning,
    standardAxioms := standard },
  { root := ``Ix.Tc.CacheInvariant.whnfHit,
    standardAxioms := standard },
  { root := ``Ix.Tc.AmbientNat.supportExpr_whnfMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.warmHit_whnfMeaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNative_noAccel,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RecM.tryReduceBitvec_noAccel,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.tryReduceDecidable_noAccel,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RecM.tryReduceFinValDecidableRec_noAccel,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.WhnfTheory.exprWF,
    standardAxioms := standard },
  { root := ``Ix.Tc.WhnfTheory.transMeaning,
    standardAxioms := standard,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RawProjRel.none_ok,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.RawProjRel.lean4Lean_ok,
    standardAxioms := standard,
    sorryOrigins := projectionDebt },
  { root := ``Ix.Tc.ConcreteProjectionFixture.acceptance,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    sorryOrigins := projectionDebt },
  { root := ``Ix.Tc.TcM.ctxAddrForLbr_zero,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Tc.TcM.whnfKey_closed,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Tc.ContextKeyFrame.whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.TcM.ctxAddrForLbr_wf,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Tc.TcM.whnfKey_wf,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Tc.TcM.whnfKey_matches_wf,
    standardAxioms := standard, nativeAxioms := contextNative },
  -- interning frame: exact intern-only framing, execution-indexed simultaneous
  -- substitution, and the production one-argument beta path.
  { root := ``Ix.Tc.InternUpdateFrame.whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.TcM.runIntern_whnf_wf,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.TcM.runIntern_whnf_eval,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RunAssumptions.simulSubst_whnf_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.simulSubst_whnf_eval,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.WhnfMeaning.beta,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.WhnfMeaning.letE,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.WhnfMeaning.betaSimul,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.WhnfCoreLeaf.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_betaOne,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_leaf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsUncached_betaOne,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsUncached_betaOne_wf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlags_leaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.AmbientNat.warmStateInvAccelerated,
    standardAxioms := standard,
    nativeAxioms := inferNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.warmKey_matches_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.whnfCoreConst_noAccel_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.betaIdentityMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.betaSimulSpec,
    standardAxioms := standardWithoutQuot, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.AmbientNat.betaSimulMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.betaWalker_eval,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.AmbientNat.betaResultMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.betaCoreUncached_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.AmbientNat.betaCoreUncached_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- zeta reduction: both production zeta branches, including the legacy lifting walk,
  -- mixed-context semantic lookup, bounded driver, and inhabited fixtures.
  { root := ``Ix.Tc.CtxRecon.lctxFindLetVal,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.TcM.lookupLetVal_eval,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RunAssumptions.lift_whnf_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RunAssumptions.lift_whnf_eval,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.WhnfMeaning.zetaVar,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.WhnfMeaning.zetaFVar,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_varZeta,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_fvarZeta,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsUncached_nextLeaf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsUncached_varZeta,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsUncached_fvarZeta,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsUncached_varZeta_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsUncached_fvarZeta_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.AmbientNat.bvarZetaLiftSpec,
    standardAxioms := standardWithoutQuot, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.AmbientNat.bvarZetaLookupEval,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.AmbientNat.bvarZetaMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.bvarZetaCoreUncachedEval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.AmbientNat.bvarZetaAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fvarZetaMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fvarZetaCoreUncachedEval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.AmbientNat.fvarZetaAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- projection/iota branch: exact projection/iota branches and bounded-driver composition.
  -- Semantic success is conditional on an explicit translated-source oracle;
  -- the two hostile fixtures prove that raw helper success cannot replace it.
  { root := ``Ix.Tc.WhnfMeaning.projection,
    standardAxioms := standard },
  { root := ``Ix.Tc.WhnfMeaning.registeredDefEq,
    standardAxioms := standard },
  { root := ``Ix.Tc.InductiveReductionOracle.projection,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.InductiveReductionOracle.iota,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_projection,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_iota,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsUncached_projection,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsUncached_iota,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsUncached_projection_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsUncached_iota_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.AmbientNat.projectionReduceEval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.projectionCoreEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.projectionSource_not_translated,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.projectionAdversarialWitness,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaStateInv,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaTryEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaCoreEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaSource_not_translated,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaAdversarialWitness,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- structural trace: arbitrary-length structural traces compose exact production
  -- execution, fixed-world/context invariants, and local Theory meanings.
  -- The inhabited fixture takes two `.next` steps before its leaf; the
  -- hostile zero-fuel witness cannot be certified as a successful trace.
  { root := ``Ix.Tc.RecM.WhnfCoreTrace.no_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfCoreTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfCoreTrace.initialInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfCoreTrace.finalInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfCoreTrace.meaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.WhnfCoreTrace.uncached_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfCoreTrace.uncached_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.AmbientNat.structuralNatLit_type,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structuralWhnfTheory,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structuralLoopStateInv,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structuralLoopSourceMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structuralLoopBetaMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structuralLoopFVarStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structuralLoopBetaStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structuralLoopTrace,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structuralLoopAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structuralLoopZeroFuel,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- structural cache: the public structural entry point's keyed body has exact full,
  -- cheap, miss, hit, and transient equations.  Misses require both an
  -- execution-indexed trace and universal provenance before insertion;
  -- hits require the physical entry, semantic invariant, and executed key
  -- match.  The Nat fixture runs cold-to-warm in both isolated partitions.
  { root := ``Ix.Tc.RecM.WhnfCoreNonLeaf.enter,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlags_varNotLet,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlags_varEnter,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfCoreKeyedEntry.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsNonLeaf_fullHit,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsNonLeaf_cheapHit,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsNonLeaf_fullMiss,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsNonLeaf_cheapMiss,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsNonLeaf_transient,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfCoreCacheUpdate.full_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.WhnfCoreCacheUpdate.cheap_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlags_fullHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlags_cheapHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlags_fullMiss_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlags_cheapMiss_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlags_transient_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.AmbientNat.betaArgMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullCoreProvenance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.cheapCoreProvenance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.coreCacheFreshStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullCoreWarmStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.bothCoreWarmStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.coreCacheKey_eval,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.coreCacheKey_matches,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.betaTransientFalse,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.betaWalker_eval_state,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.betaStep_state,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.coreCacheTrace,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullCoreColdAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullCoreWarmAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.cheapCorePolicyMissAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.cheapCoreWarmAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.coreCachePolicyIsolation,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  -- outer WHNF driver: no-delta and full-WHNF now have execution-indexed bounded traces,
  -- exact public-prefix/cache/fuel equations, provenance-checked insertion,
  -- and semantic hit/miss acceptance.  The Nat fixture executes all nested
  -- cache layers, proves the cold call consumes exactly one fuel unit, and
  -- proves the warm public call preserves the entire state.
  { root := ``Ix.Tc.WhnfStateInv.of_semantic_fields_eq,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.TcM.stepTrace_disabled,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.TcM.bumpStats_disabled,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.TcM.tick_success,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.WhnfNoDeltaTrace.no_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfNoDeltaTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfNoDeltaTrace.initialInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfNoDeltaTrace.finalInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfNoDeltaTrace.meaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.WhnfNoDeltaTrace.uncached_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfNoDeltaTrace.uncached_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.WhnfFullTrace.no_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfFullTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfFullTrace.initialInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfFullTrace.finalInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfFullTrace.meaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.WhnfFullTrace.uncached_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfFullTrace.uncached_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.WhnfDriverNonLeaf.noDelta_enter,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfDriverNonLeaf.full_enter,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfDriverEntry.noDelta_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfDriverEntry.full_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccModePrefix_disabled,
    standardAxioms := standard },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccModeMissCharge_disabled,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplNonLeaf_fullHit,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplNonLeaf_cheapHit,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplNonLeaf_fullMiss,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplNonLeaf_cheapMiss,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplNonLeaf_stuck,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplNonLeaf_transient,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplNonLeaf_nativeNoInsert,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfDriverCacheUpdate.noDelta_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.WhnfDriverCacheUpdate.noDeltaCheap_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.WhnfDriverCacheUpdate.full_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImpl_fullHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImpl_cheapHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImpl_fullMiss_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImpl_cheapMiss_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImpl_stuck_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImpl_transient_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccModeNonLeaf_hit,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccModeNonLeaf_miss,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccModeNonLeaf_stuck,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccModeNonLeaf_transient,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccModeNonLeaf_nativeNoInsert,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccMode_hit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccMode_miss_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccMode_stuck_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccMode_transient_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.whnf_public_eq_whnfWithNatSuccMode,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.AmbientNat.betaNoDeltaStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullNoDeltaProvenance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfProvenance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullNoDeltaWarmStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.noDeltaTrace,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullNoDeltaColdAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullNoDeltaWarmAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.noDeltaCachePolicyIsolation,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfChargedStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfPrefixCold,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfMissCharge,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfCharged_noDeltaHit,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.betaFullWhnfStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfTrace,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfWarmStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfColdAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfWarmAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfFuelDiscipline,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfCacheLayering,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  -- total-outcome boundary: local step contracts now construct success traces and classify
  -- bounded exhaustion versus step errors.  The public no-delta/full-WHNF
  -- dispatchers close conditionally over suffix reconciliation, transient
  -- lookup safety, collision-robust insertion provenance, and the local
  -- semantic step contracts.  Instrumentation and miss charging are proved.
  { root := ``Ix.Tc.WhnfPost.transMeaning,
    standardAxioms := standard, sorryOrigins := typingDebt },
  { root := ``Ix.Tc.WhnfPost.meaning,
    standardAxioms := standard },
  { root := ``Ix.Tc.TcM.isLetVar_wf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.TcM.stepTrace_whnf_wf,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.TcM.bumpStats_whnf_wf,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.WF.liftTcM,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.WF.get,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.WF.modifyGet,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.WF.modify,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.WhnfCoreTrace.complete,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfCoreTrace.uncached_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.WhnfNoDeltaTrace.complete,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfNoDeltaTrace.uncached_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.WhnfFullTrace.complete,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.WhnfFullTrace.uncached_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplNonLeaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImpl_nonLeaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccModeNonLeaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccMode_nonLeaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccModePrefix_wf,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccModeMissCharge_wf,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccMode_nonLeaf_semantic_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImpl_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfWithNatSuccMode_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNoDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.noDeltaZeroFuel,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fullWhnfZeroFuel,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.whnfLoopErrorSeparation,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfPost.refl,
    standardAxioms := standard },
  { root := ``Ix.Tc.RecM.WF.bind,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.runBounded_wf,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.RecM.WhnfLeaf.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnf_leaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnf_leaf_wf_of_theory,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.AmbientNat.noAccelStateInv,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.whnfLeaf_noAccel_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.whnfLeaf_noAccel_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.whnfKey_fst,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Tc.WhnfContextKeys.Matches.sourceAddr,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Tc.CacheProvenance.whnfMeaningOfMatches,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Tc.CacheInvariant.whnfHitOfMatches,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Tc.AmbientNat.warmKey_matches,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.methodsN_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.methodsN_succ_whnf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.methodsN_succ_whnfCore,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.methodsN_succ_whnfMode,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.methodsN_succ_whnfCoreFlags,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.methodsN_succ_infer,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.methodsN_succ_isDefEq,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.methodsOut_whnf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.methodsOut_whnfCore,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.methodsOut_whnfMode,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.methodsOut_whnfCoreFlags,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.methodsOut_infer,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.methodsOut_isDefEq,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.TcM.runRec_apply,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.TcM.runRec_directInfer_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.TcM.whnf_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.TcM.whnfCore_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.TcM.whnfNoDelta_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.TcM.infer_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.TcM.isDefEq_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.TcM.ensureSort_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.TcM.ensureForall_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.unfoldConstValue_equation,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RecM.tryDeltaUnfold_equation,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RecM.deltaUnfoldOne_equation,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RecM.applyIotaArg_false,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.applyIotaArg_true_lam,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.isNatLiteralRecursorApp_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.isTransientNatLiteralWork_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.cleanupNatOffsetMajor_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.projectDecidableFinValMinor_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.tryReduceFinValDecidableRec_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.tryReduceProjectionDefinition_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.natRecLiteralParts_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.isNatStuckRecursorAddr_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.isStuckNatPredicateProbe_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.bitvecOfNatArgs_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.charOfNatExpr_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.tryReduceString_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.discoverBlockInductives_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.runBounded_zero,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.runBounded_succ,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.consumeBetaLams_equation,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.consumeBetaLamsFuel_zero,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.consumeBetaLamsFuel_succ,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.compareRank_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.RecM.isNatLike_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.isNatZero_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.natSuccOf_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.isBoolTrue_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.isDelta_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.isRegular_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.defRankId_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.infer_eq_inferWith,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.inferCall_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.inferOnlyCall_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.isDefEqCall_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.whnfRec_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.whnfModeRec_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.whnfCoreFlagsRec_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.whnf_eq_whnfWithNatSuccMode,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCore_eq_whnfCoreWithFlags,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDelta_eq_whnfNoDeltaImpl,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.ensureSortDirect_equation,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.ensureForallDirect_equation,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.peelProjForall_equation,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.checkNoUnsafeRefs_equation,
    standardAxioms := standard },
  { root := ``Ix.Tc.RecM.checkNoUnsafeRefs_go_nil,
    standardAxioms := standard },
  { root := ``Ix.Tc.RecM.checkNoUnsafeRefs_go_app,
    standardAxioms := standard },
  { root := ``Ix.Tc.RecM.validateUnivParamsSeen_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.validateUnivParamsSeen_go_nil,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.validateUnivParamsSeen_go_max,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.validateExprWellScoped_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.validateExprWellScoped_go_nil,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.validateExprWellScoped_go_app,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.peelRuleIhForalls_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.checkPositivityDomain_equation,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.checkPositivityDomainFuel_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.checkNestedCtorFieldsFuel_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.checkNestedCtorFieldsLoopFuel_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.countForalls_equation,
    standardAxioms := standard, nativeAxioms := inferNative },
  -- The complete checker dispatch is transparent now; these roots pin its
  -- exact production trust boundary in addition to the local equations.
  { root := ``Ix.Tc.RecM.checkInductive,
    standardAxioms := standard, nativeAxioms := inductiveNative },
  { root := ``Ix.Tc.RecM.checkRecursorMemberImpl,
    standardAxioms := standard, nativeAxioms := inductiveNative },
  { root := ``Ix.Tc.RecM.checkConst,
    standardAxioms := standard, nativeAxioms := inductiveNative },
  { root := ``Ix.Tc.TcM.checkConst,
    standardAxioms := standard, nativeAxioms := inductiveNative },
  { root := ``Ix.Tc.extractNatValue_app_const_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.extractNatValue_nat_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.projectionDefinitionInfo_go_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.EquivManager.find_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.EquivManager.find_go_zero },
  { root := ``Ix.Tc.EquivManager.find_go_succ },
  { root := ``Ix.Tc.LocalContext.truncate_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.LocalContext.truncate_go_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.LocalContext.truncate_go_succ,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.TcM.restoreDepth_apply,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.TcM.restoreDepth_go_zero,
    standardAxioms := standard, nativeAxioms := blake3Native },
  { root := ``Ix.Tc.TcM.ctxSuffixNeed_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.TcM.ctxSuffixNeed_succ,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.TcM.ctxSuffixNeed_of_fixed,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.KExpr.render_equation,
    standardAxioms := standard },
  { root := ``Ix.Tc.KExpr.renderFuel_zero,
    standardAxioms := standard },
  { root := ``Ix.Tc.RecM.natOffset_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.natOffsetOrZero_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.evalNatOffsetLiteral_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.natOffsetFuel_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.evalNatOffsetLiteralFuel_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.tryEvalNatValueForPred_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.tryEvalNatValueForPredFuel_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.compareKUniv_succ_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.compareKUniv_max_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.mergeSorted_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.mergeSorted_go_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.sortByCompare_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.sortByCompareFuel_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.sortKConstsRefineFuel_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.KExpr.treeSize_pos,
    standardAxioms := propextOnly },
  { root := ``Ix.Tc.exprMentionsAddr_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.exprMentionsAddr_go_nil,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.exprMentionsAddr_go_app,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.exprMentionsAddr_go_const,
    standardAxioms := standardWithoutChoice },

  -- RuntimeContracts: the repaired step source includes finite support plus an actual
  -- translation; closed contexts derive both key representation and
  -- collision-robust write validity.  The transient Nat probe is proved
  -- state-pure for eager states.  General lazy execution is reduced to the
  -- exact invariant contract of the driver-installed environment hook.
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_leaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_betaOne_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_projection_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_iota_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RunAssumptions.subst_whnf_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RunAssumptions.subst_whnf_eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_letE,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_letE_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- regular-binder fallback: both translated regular-binder forms take the state-pure `.done`
  -- fallback and cannot be confused with their let-bound zeta siblings.
  { root := ``Ix.Tc.TcM.lookupLetVal_none_state,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_varDone,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_fvarDone,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_varDone_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_fvarDone_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.bvarStuckAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.fvarStuckAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- stuck-reduction fallback: projection misses and unchanged non-lambda application heads keep
  -- their original syntax, distinguish helper errors from `none`, and are
  -- inhabited by translated projection and constructor-application fixtures.
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_projectionDone,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_projectionWhnfError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_projectionReduceError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appUnchangedDone,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appHeadError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appUnchangedIotaError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_projectionDone_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appUnchangedDone_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.appStuckAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.ProjectionFallback.acceptance,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },

  -- application rebuilding: both application rebuilding loops share one audited helper.  A
  -- finite certificate fixes suffix order, support, collision freedom, and
  -- intern-only framing; general multi-beta and changed-head hit/miss/error
  -- equations consume that helper boundary.  The Nat fixtures make argument
  -- reversal, a trailing argument, and physically changed heads observable.
  { root := ``Ix.Tc.InternUpdateFrame.refl,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.InternUpdateFrame.trans,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RunAssumptions.internExpr_whnf_eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishAppResult_eq_foldlM,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.finishAppResult_one,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.FinishAppRequests.result_eq_foldl,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.FinishAppRequests.support,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Tc.RecM.FinishAppRequests.foldlM_eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.FinishAppRequests.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.FinishAppRequests.final_eq_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_betaMany,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appChangedIota,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appChangedDone,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appChangedIotaError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_betaMany_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appChangedDone_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appChangedIota_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appChangedIotaError_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiBetaStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.changedHeadInternSpec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.AmbientNat.changedHeadStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.WhnfKey.closed_represents,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.WhnfCacheWriteOracle.closed,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.tryGetConst_noLazy,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.TcM.lazyIngressAddr_wf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.TcM.tryGetConst_wf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.KId.anon_eq_of_addr_eq },
  { root := ``Ix.Tc.TcM.tryGetConst_success_loaded,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.NatRecLiteralPartsSuccessTrace.eval,
    standardAxioms := standard },
  { root := ``Ix.Tc.RecM.NatRecLiteralPartsSuccessTrace.complete,
    standardAxioms := standard },
  { root := ``Ix.Tc.RecM.NatRecLiteralPartsSuccessTrace.trusted,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrustedNatRecLiteralParts.patternAt,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.HeadConstN.matches_varN },
  { root := ``Ix.Tc.HeadConstN.natLit_zero },
  { root := ``Ix.Tc.HeadConstN.natLit_succ },
  { root := ``Ix.Tc.RecursorIotaPattern.matches_of_shapes },
  { root := ``Ix.Tc.RecursorIotaPattern.exists_matches_iff_shapes },
  { root := ``Ix.Tc.RecursorIotaPattern.matches_natZero },
  { root := ``Ix.Tc.RecursorIotaPattern.matches_natSucc },
  { root := ``Ix.Tc.NatRecIotaCase.major_shape },
  { root := ``Ix.Tc.RecursorRulePattern.matches_natLiteral },
  { root := ``Ix.Tc.RecM.TrAppSpine.headConstN,
    standardAxioms := standard },
  { root := ``Ix.Tc.RecM.TrAppSpine.matches_natRecRulePrefix,
    standardAxioms := standard },
  { root := ``Ix.Tc.RawRecursorRulePatternRel.matches_natLiteralPrefix,
    standardAxioms := standard },
  { root := ``Ix.Tc.AmbientNat.linearRecTheoryPrefix_shape },
  { root := ``Ix.Tc.AmbientNat.linearRecZeroPatternMatch },
  { root := ``Ix.Tc.AmbientNat.linearRecSuccPatternMatch },
  { root := ``Ix.Tc.TrustedNatRecursorLayout.caseForMajor,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSuffix.tr,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSpine.splitAt,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatRecLiteralPartsDescriptor.patternMajor,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatRecLiteralPartsDescriptor.translatedSplit,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrustedNatRecLiteralParts.translatedCase,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSuffix.startHasType,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSuffix.rebase,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RawRecursorRulePatternRel.checkedReduction,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatRecLiteralTranslationSplit.checkedRhsSuffix,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RegisteredRecursorRuleRhsRel.rhsRaw,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RegisteredRecursorRuleRhsRel.rhsStructural,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RegisteredRecursorRuleRhsRel.instUnivSpec,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RegisteredRecursorRuleRhsRel.instantiateUnivParams_nonempty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RawRecursorRuleRel.registeredRhsTyped,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSuffix.rebaseQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.NatRecLiteralTranslationSplit.checkedRhsSuffixQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KExpr.Constructed.liftNoIntern_eq_liftSpec,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KExpr.Constructed.substNoIntern_eq_substSpec,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applyIotaArg_true_lam_spec,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applyIotaArg_true_lam_run,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfMeaning.betaNoIntern,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.betaIotaArgRun,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.betaNoInternMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.IotaArgNonLambda.applyIotaArg_true,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.IotaArgNonLambda.applyIotaArg_true_run,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfMeaning.appRebuild,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applyIotaArg_true_nonlam_semantic,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applyIotaArg_false_eval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applyIotaArg_false_semantic,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.appStuckIotaTransient,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.appStuckIotaInterned,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfMeaning.resultQuot,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfMeaning.ofStructuralQuot,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KExpr.substNoIntern_of_lbr_le,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KExpr.liftNoIntern_of_lbr_le,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applyIotaArgs_eq_foldlM,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.singleton,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.append,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.three,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.ApplyIotaArgsTrace.transientNonLambdaSingleton,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.ApplyIotaArgsTrace.transientNonLambdaSingletonQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.internedSingleton,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.transientLambdaSingleton,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.transientLambdaSingletonQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.evalList,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.evalArray,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.sourceTr,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.finalQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.finalInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.frame,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.finalSupport,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.acceptance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.evalThreeArrays,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.threeArrayAcceptance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfMeaning.ofQuot,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.sourceQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.acceptanceQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaArgsTrace.threeArrayAcceptanceQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.instantiateUnivParams_whnf_of_run,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaRuleTrace.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaRuleTrace.emptyInstantiation,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaRuleTrace.instantiatePost,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaRuleTrace.acceptance,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaRuleTrace.acceptance_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.ApplyIotaRuleTrace.registeredStartQuot_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.ApplyIotaRuleTrace.registeredAcceptance_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.ApplyIotaRuleTrace.registeredStartQuot_nonempty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.ApplyIotaRuleTrace.registeredAcceptance_nonempty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaRuleTrace.checkedMeaning,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.ApplyIotaRuleTrace.checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.ApplyIotaRuleTrace.checkedAcceptance_nonempty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KConst.recursorMajorIdx_of_iotaInfo,
    standardAxioms := propextOnly,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KConst.recursorRuleAt_of_iotaInfo,
    standardAxioms := propextOnly,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryApplyIotaCtorSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaCtorTrace.operational,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaCtorTrace.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaCtorTrace.recursorRuleAt,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaCtorTrace.acceptance_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaCtorTrace.checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ApplyIotaCtorTrace.checkedAcceptance_nonempty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaCtorOrStructEta_regular,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaAfterMajorWhnf_regular,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaWithFlags_nonKPrefix,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaWithFlags_regularCtor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryIotaWithFlags_regularCtor_checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natToConstructor_zero,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natToConstructor_succ,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaAfterMajorWhnf_nat,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaWithFlags_natCtor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryIotaWithFlags_natCtor_checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.intern_success_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.strLitListToConstructor_empty,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.strLitListToConstructor_success_frame,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.strLitToConstructor_success_frame,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.evalNatOffsetLiteral_str,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natOffset_str,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.cleanupNatOffsetMajor_str,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaAfterMajorWhnf_str,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaWithFlags_strCtor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryIotaWithFlags_strCtor_checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaStringEmptyFold,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaStringExpand,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaStringCallback,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaStringCleanup,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaStringGetZeroOfFrame,
    standardAxioms := standard,
    nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaStringApplyRule,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaStringApplyCtor,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaStringAfterEval,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },

  -- ConstructorSynthesis: the positive K-like recursor branch.  Optional probes retain
  -- error-side state, candidate synthesis records the DefEq gate and counter
  -- order, and the inhabited fixture reaches the real bounded WHNF driver.
  { root := ``Ix.Tc.RecM.tryOptional_success,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryOptional_error,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.VerifyKSynthCandidateSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.VerifyKSynthCandidateRejectTrace.eval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.SynthCtorWhenKSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaWithFlags_kPrefix,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaWithFlags_kFallback,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaWithFlags_kCtor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryIotaWithFlags_kCtor_checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaIntern,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaMajorInfer,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaMajorWhnf,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaGetRec,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaGetNat,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaMajorInductive,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaCtorInfer,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaAttemptStats,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaTypeDefEq,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaCandidate,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaSynth,
    standardAxioms := standard,
    nativeAxioms := inferNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaInternFrame,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaSynthCleanup,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaSynthWhnf,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaGetZeroAfter,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaApplyRule,
    standardAxioms := standard, nativeAxioms := nameNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaApplyCtor,
    standardAxioms := standard, nativeAxioms := nameNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaTryEval,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaStepEval,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kIotaCoreEval,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },

  -- ConstructorSynthesisFallback: exhaustive K-synthesis fallback and error branches.
  { root := ``Ix.Tc.RecM.verifyKSynthCandidate_inferMiss,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.verifyKSynthCandidate_inferError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.verifyKSynthCandidate_defEqError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.selectKSynthCandidate_mismatch,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.selectKSynthCandidate_missing,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.selectKSynthCandidate_nonInductive,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.selectKSynthCandidate_empty,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.selectKSynthCandidate_selected,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.selectKSynthCandidate_selectedError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.synthCtorWhenK_majorInferMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.synthCtorWhenK_majorInferError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.synthCtorWhenK_majorWhnfMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.synthCtorWhenK_majorWhnfError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.synthCtorWhenK_nonConstHead,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.synthCtorWhenK_recursorMissing,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.synthCtorWhenK_majorInductiveMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.synthCtorWhenK_majorInductiveError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.SynthCtorWhenKSelectionTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.SynthCtorWhenKSelectionTrace.mismatch,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.SynthCtorWhenKSelectionTrace.missing,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.SynthCtorWhenKSelectionTrace.nonInductive,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.SynthCtorWhenKSelectionTrace.empty,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.SynthCtorWhenKSelectionTrace.selected,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.SynthCtorWhenKSelectionTrace.selectedError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kMajorInferRawError,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kMajorInferCaughtMiss,
    standardAxioms := standard,
    nativeAxioms := inferNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kCandidateInferRawError,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kCandidateInferCaughtMiss,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kDefEqRawError,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kDefEqCandidateError,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kDefEqSynthError,
    standardAxioms := standard,
    nativeAxioms := inferNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kEmptyGetRec,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kEmptyGetNat,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kEmptyMajorInductive,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.kEmptyInductiveMiss,
    standardAxioms := standard,
    nativeAxioms := inferNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },

  -- StructEtaControl: exhaustive struct-eta classification, caught probes, rebuild,
  -- single-rule selection, and final constructor fallthrough.  Rebuilding is
  -- proved total; only universe instantiation can produce a post-guard error.
  { root := ``Ix.Tc.RecM.isStructLike_missing,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isStructLike_nonInductive,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isStructLike_lookupError,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isStructLike_badShape,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isStructLike_shapeQualified,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isStructLike_recError,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishStructEtaResult_empty,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.structEtaIntern_total,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishStructEtaFields_total,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishStructEtaResult_of_segments,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishStructEtaResult_total,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishStructEtaResult_ne_error,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishStructEtaAfterSort_prop,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishStructEtaAfterSort_success,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishStructEtaAfterSort_instantiateError,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishStructEtaAfterSort_finishError,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaAfterInductive_notStruct,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaAfterInductive_structError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaAfterInductive_majorInferMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaAfterInductive_majorInferError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaAfterInductive_sortInferMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaAfterInductive_sortInferError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaAfterInductive_sortWhnfMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaAfterInductive_sortWhnfError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaProbeTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaProbeTrace.prop,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaProbeTrace.success,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaProbeTrace.finishError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaIota_ruleCount,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaIota_recursorMissing,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaIota_recursorError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaIota_majorInductiveMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaIota_majorInductiveError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaSelectionTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaIotaSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaIotaSuccessTrace.acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Rebuild: the successful struct-eta rebuild derives its invariant, frame,
  -- and finite support from the exact projection/application request list.
  -- The registered Theory equation remains an explicit premise.
  { root := ``Ix.Tc.RecM.StructEtaFieldRequests.support,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaFieldRequests.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaBuildRequests.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaIotaSuccessTrace.acceptance_of_requests,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- CallbackPrefix: the exact infer-only and optional-catch wrappers preserve the
  -- complete fixed-world invariant while retaining callback mutations.
  { root := ``Ix.Tc.TcM.withInferOnly_eq,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.withInferOnly_whnf_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.inferOnlyRec_run,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryOptional_run,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryOptional_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.inferOnlyRec_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryOptionalInferOnlyRec_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryOptionalWhnfRec_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },

  -- RecursionClassifier: recursion classification now owns its complete concrete state
  -- transaction.  Both physical writes require explicit provenance; the
  -- final write is indexed by the exact classifier execution, and only
  -- errors inside that classifier enter the erase-and-rethrow handler.
  { root := ``Ix.Tc.CacheInvariant.insertIsRec,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheInvariant.eraseIsRec,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsRecCacheUpdate.insert_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsRecCacheUpdate.erase_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsRecCacheWriteOracle.of_trusted,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.getConst_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.tryGetBlock_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.WhnfCallbackSupports.preserves,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.getMajorInductiveId_wf,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.collectSpine_const_references,
    standardAxioms := propextOnly,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.getMajorInductiveId_trusted_wf,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.discoverBlockInductives_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.computeIsRec_wf,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.cacheIsRec_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.eraseCachedIsRec_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.computedIsRecClassify_wf,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.computedIsRecMiss_wf,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.computedIsRec_wf,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Classifier: compose the recursion classifier through `isStructLike`, then
  -- exhaust the single-rule recursor lookup and all three caught struct-eta
  -- probes.  Only the explicitly parameterized cache-write, callback, and
  -- successful universe/rebuild authorities remain outside these proofs.
  { root := ``Ix.Tc.RecM.isStructLike_wf,
    standardAxioms := standard, nativeAxioms := blake3ContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryOptional_state_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryOptional_fixed_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaAfterInductive_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaIota_prefix_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaIota_trusted_prefix_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructEtaIota_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- RebuildTail: the universe-instantiation/rebuild tail now preserves the complete
  -- invariant from the finite execution request census, including retained
  -- intern-table updates on a non-backtracking walker error.
  { root := ``Ix.Tc.TcM.instantiateUnivParams_whnf_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaBuildRequests.wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishStructEtaAfterSort_wf_of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },

  -- CacheShell: both structural-core cache partitions now have explicit
  -- collision-robust write authority, and the actual public dispatcher is
  -- closed conditionally on the remaining exhaustive structural step.
  { root := ``Ix.Tc.RecM.WhnfCoreCacheWriteOracle.closed,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfSuffixModel.coreCacheWriteOracle,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsNonLeaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlags_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- BasicStep: immediate leaves, the complete fvar split, and explicit-let
  -- substitution now share one local structural-step contract.  The fvar
  -- theorem exposes the real unchanged-value safety invariant rather than
  -- inferring closedness or arithmetic bounds from translation alone.
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_fvar_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_letE_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_basic_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- VariableStep: legacy zeta now derives its semantic weakening from the exact
  -- lift-walker bounds.  The only additional safety fact is the real
  -- UInt64 `idx + 1` no-wrap condition on an actual let-value hit.
  { root := ``Ix.Tc.CtxRecon.lookupLetVal_liftBounds,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.lookupLetVal_noLet,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfMeaning.zetaVar_liftBounds,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_var_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_basicVar_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  
  -- RecursiveCallbacks: projection values and application-spine children now have an
  -- explicit finite-support boundary, and both recursive head callbacks are
  -- instantiated directly from the predecessor method-table contract.
  { root := ``Ix.Tc.RecM.whnfCoreFlagsRec_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSpine.headTr,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.projectionValueCallback_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applicationHeadCallback_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applicationArgument_support,
    standardAxioms := propextOnly,
    forbiddenDependencies := legacyWholeEnv },

  -- ProjectionStep: all projection-step outcomes now satisfy the local structural
  -- contract once the exact helper effect/result boundary is instantiated;
  -- callback and helper errors retain their partial post-state.
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_projection_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_basicVarProjection_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- ApplicationCongruence: the application-head callback is tied to the exact typed suffix,
  -- and Theory application congruence transports head reduction across every
  -- argument rebuilt by the finite production certificate.
  { root := ``Ix.Tc.RecM.TrAppSpine.toSuffix,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applicationHeadCallbackWithSuffix_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.WhnfMeaning.appHeadRebuild,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- ApplicationRebuild: a finite census now executes each dynamic changed-head rebuild and
  -- returns its exact intern frame, support, and transported Theory meaning.
  { root := ``Ix.Tc.RecM.changedHeadFinish_acceptance,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- ApplicationTails: both non-beta application tails are exhaustive over iota hit,
  -- miss, and error.  Changed-head hits compose rebuild congruence with the
  -- helper result; unchanged misses remain reflexive at the original source.
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appUnchangedIota,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appUnchanged_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfCoreWithFlagsStep_appChanged_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- NoAccelTail: the actual no-acceleration projection tail now forces the
  -- Fin/Decidable probe to miss, preserves lazy constructor lookup state,
  -- and derives selected-field support from the concrete collected spine.
  -- Only String preprocessing and the installed lazy-ingress hook remain at
  -- the public helper constructor.
  { root := ``Ix.Tc.RecM.WhnfCoreInputSupport.spineArg,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryProjReduceTail_noAccel_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ProjectionPrelude.nonString,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ProjectionPrelude.ofString,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryProjReduce_noAccel_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ProjectionHelper.noAccel,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ProjectionStringPrelude.ofExpansion,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ProjectionHelper.noAccelOfExpansion,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  -- StringExpansion: the remaining String-expansion premise is reduced to a pure,
  -- finite plan.  The actual primitive read, seven prefix interns, recursive
  -- character fold, and final intern preserve the complete K1 invariant and
  -- return the exact structurally translated generated expression.
  { root := ``Ix.Tc.RecM.strLitListToConstructor_plan_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.strLitToConstructorWithPrimitives_plan_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.strLitToConstructor_plan_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ProjectionStringExpansion.ofPlans,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ProjectionHelper.noAccelOfStringPlans,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  -- LazyIngress: instantiate the generic lazy-fault plumbing with production's
  -- anonymous shallow-ingress callback.  The outcome refinement explicitly
  -- covers a successful load, an absent address, and an error-carried partial
  -- environment; hook identity remains visible because `TcState.lazyFault`
  -- otherwise stores an arbitrary function.
  { root := ``Ix.Tc.LazyIngressEnvFrame.refl,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.LazyIngressEnvFrame.kernelStateWF,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.LazyIngressEnvFrame.ctxRecon,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.LazyIngressEnvFrame.whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ingressAnonAddrShallow_absent,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AnonIngressRefinement.absentOfVerifiedMiss,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AnonIngressRefinement.error,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AnonIngressRefinement.lazyFaultPreserves,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AnonLazyIngressContext,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AnonLazyIngressContext.preserves,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.ProjectionHelper.noAccelOfAnonIngress,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  -- NatOffset: the actual post-major iota preprocessing path.  Bounded Nat-offset
  -- parsing, Nat constructor expansion, cleanup, lazy constructor lookup,
  -- finite String expansion, the policy-selected recursive callback, and the
  -- constructor/struct-eta dispatch all preserve the complete K1 invariant.
  -- Only the ordinary-constructor and struct-eta tails remain named inputs.
  { root := ``Ix.Tc.RecM.prims_state_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isNatBinArithAddr_state_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natOffsetReaders_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natOffset_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.evalNatOffsetLiteral_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natToConstructor_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.mkNatSucc_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.mkNatAdd_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.WF.with_run_eq,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.OptionalGeneratedInput,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatOffsetCleanupInputOracle,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.cleanupNatOffsetMajor_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.cleanupNatOffsetMajor_input_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryApplyIotaCtorPreserves,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaIotaPreserves,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.SelectedStructEtaIotaPreserves,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaCtorOrStructEta_state_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.strLitToConstructor_context_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaAfterCleanup_state_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaAfterMajorWhnf_state_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- ApplicationRequests--Ingress: finite ordinary-iota, struct-eta, and K-synthesis request
  -- censuses close every generated-expression effect.  Their composition
  -- exhausts the actual tryIotaWithFlags state path through lazy lookup,
  -- caught probes, both cleanup stages, policy-selected major callbacks,
  -- statistics updates, and the final uncaught DefEq callback.
  { root := ``Ix.Tc.RecM.IotaArgsInternRequests,
    standardAxioms := standardWithoutQuot, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IotaArgsInternRequests.wfList,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IotaArgsInternRequests.wfArray,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applyIotaArg_true_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applyIotaArgs_true_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IotaRuleRequests,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IotaRuleRequestCensus,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.applyIotaRule_state_wf_of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryApplyIotaCtor_state_wf_of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryApplyIotaCtorPreserves.of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaFinishRequests,
    standardAxioms := standardWithoutQuot, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaFinishRequestCensus,
    standardAxioms := standardWithoutQuot, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaFinishPreserves.of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructEtaIotaPreserves.of_components,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaAfterMajorWhnf_state_wf_of_contexts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsDefEqCallbackPreserves,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.WF.tryFinally_const,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.enterDispatch_whnf_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.exitDispatch_whnf_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.callIsDefEq_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.KSynthCandidateRequests,
    standardAxioms := standardWithoutQuot, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.KSynthCandidateRequestCensus,
    standardAxioms := standardWithoutQuot, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.KSynthCandidateInputs,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.KSynthCandidateInputOracle,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.FinishAppRequests.state_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.verifyKSynthCandidate_state_wf_of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.selectKSynthCandidate_state_wf_of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.synthCtorWhenK_state_wf_of_requests,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.verifyKSynthCandidate_state_wf_of_inputs,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.selectKSynthCandidate_state_wf_of_inputs,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.synthCtorWhenK_state_wf_of_inputs,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaWithFlags_state_wf_of_contexts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- OptionalReduction: the exhaustive state proof and the direct admission-owned success
  -- boundary assemble the ordinary optional-reduction contract.  The success
  -- boundary contributes support and Theory meaning only; it cannot hide an
  -- error-side or miss-side state assumption.
  { root := ``Ix.Tc.IotaCallbackFrameOracle,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.IotaSuccessOracle,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaWithFlags_optional_wf_of_contexts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- Reducer: the structural contract is indexed by the actual universe/context
  -- represented by the cache model.  The assembled theorem feeds OptionalReduction into
  -- the exhaustive syntax step and then through the bounded/cache driver.
  { root := ``Ix.Tc.StructuralReduction.WF,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructuralCoreContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.StructuralCoreContext.wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- ProjectionApplication: projection-application reduction is exhaustive over empty and
  -- non-projection misses, both callback/helper error seams, helper misses,
  -- and successful projection followed by a certified complete-spine
  -- rebuild.  Head meaning is transported through the typed suffix rather
  -- than inferred from expression-address equality.
  { root := ``Ix.Tc.RecM.tryProjAppReduce_empty,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryProjAppReduce_notProjection,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryProjAppReduce_projectionWhnfError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryProjAppReduce_projectionReduceError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryProjAppReduce_projectionNone,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryProjAppReduce_projectionSome,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryProjAppReduceFinished_empty_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryProjAppReduceFinished_app_optional_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryProjAppReduceFinished_optional_wf_of_contexts,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- StringPrimitive: the production String primitive helper is exhaustive over every
  -- classifier miss and all three hits.  Its state proof derives finite
  -- generated-node support at each intern; the reflection boundary owns
  -- only Theory meaning for an observed successful run.
  { root := ``Ix.Tc.StringReductionSupport,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.StringReductionReflection,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceString_inv_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceString_optional_wf_of_reflection,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  -- ProjectionDefinition: projection-wrapper reduction covers the real lazy constant lookup,
  -- the generated projection, and every suffix intern.  The request plan
  -- exposes all intermediate support obligations instead of assuming that
  -- support for the final node retroactively makes those interns safe.
  { root := ``Ix.Tc.ProjectionDefinitionRequestCensus,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ProjectionDefinitionReflection,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.projectionDefinitionFinish_eq,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.FinishAppRequests.finishAppResult_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceProjectionDefinition_inv_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryReduceProjectionDefinition_optional_wf_of_contexts,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  -- Quotient: quotient reduction derives the selected major's support and
  -- translation from its real application-spine position, executes the
  -- predecessor WHNF callback, and covers the initial representative
  -- application plus every trailing suffix intern.  The former successful-
  -- run reflection input is now constructed from two Theory-only contraction
  -- laws.  Ix owns the complete dynamic trace, exact lift/ind layouts,
  -- normalized `Quot.mk` transport, collision-free base intern, and suffix
  -- reconstruction.
  { root := ``Ix.Tc.QuotientReductionRequestCensus,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.QuotientReductionReflection,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.QuotientReductionLaws,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSpine.three,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSpine.four,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSpine.five,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrKExprS.const_name,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.quotientLiftMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.quotientIndMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.QuotientSelectedSuccessTrace.complete,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.QuotientSelectedSuccessTrace.semanticInputs,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.QuotientSelectedSuccessTrace.liftMeaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.QuotientSelectedSuccessTrace.indMeaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.QuotientReductionReflection.of_laws,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryQuotReduceSelected,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryQuotReduceSelected_inv_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryQuotReduce_inv_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryQuotReduce_optional_wf_of_contexts,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  -- BaseReductions: the five active no-acceleration reducers are assembled into the
  -- exact production base oracle for either successor policy.  Native and
  -- BitVec remain independently discharged by the no-acceleration gate.
  { root := ``Ix.Tc.RecM.NoDeltaBaseContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NoDeltaBaseContext.oracle,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- Reducer: Reducer's structural reducer and BaseReductions's active base oracle now feed
  -- the real bounded, keyed, transient-aware, cache-writing public
  -- `whnfNoDeltaImpl` shell for every flag and successor policy.
  { root := ``Ix.Tc.RecM.NoDeltaDriverContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NoDeltaDriverContext.wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- FullStep--Closure: the exhaustive full-WHNF step is connected to exact
  -- definition/theorem certificates.  Stable unfold-cache provenance covers
  -- warm and cold paths, typed suffix rebuilding covers applied heads, and
  -- the bare fallback closes `deltaUnfoldOne`.  The final cache composition
  -- and method knot are indexed by the active universe count; concrete lazy
  -- ingress is carried by `AnonLazyIngressContext`, not a free callback.
  { root := ``Ix.Tc.OptionalReduction.WFAt,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TrustedDeltaBody.meaning,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.StableWhnfTheory,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TrustedDeltaBody.unfoldCacheProvenance,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.unfoldConstValue_trusted_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TrustedDeltaCensus,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryDeltaUnfold_trusted_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.deltaUnfoldOne_trusted_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrustedDeltaContext,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrustedDeltaContext.wfAt,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.FullWhnfStepContext.ofTrustedDelta,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.WhnfClosedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.Methods.methodsN_wfAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.K1ClosureContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.K1ClosureContext.closedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.AmbientNat.structEtaInferOnlyRun,
    standardAxioms := standard, nativeAxioms := expressionNameNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structEtaOptionalInferOnlyRun,
    standardAxioms := standard, nativeAxioms := expressionNameNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaCtorOrStructEta_nonConst,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaCtorOrStructEta_missing,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaCtorOrStructEta_notConstructor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaCtorOrStructEta_lookupError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryIotaCtorOrStructEta_constructor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structEtaIotaSuccess,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structEtaBuildRequests,
    standardAxioms := standardWithoutQuot, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structEtaDispatchSuccess,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structEtaIotaAbsent,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structEtaIotaCaughtInferError,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },

  { root := ``Ix.Tc.AmbientNat.iotaCleanupOfNatValue,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaNatCleanup,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaNatCtorCleanup,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaNatMajorWhnf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaNatZeroExpand,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaNatSuccExpand,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaNatApplyRule,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaNatApplyCtor,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaNatTryEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaNatStepEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaNatCoreEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaApplyRule,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaApplyCtor,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.support_le_iotaArgsSupport,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaArgsStateInv,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaArgsSupport_head,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.iotaArgsSupport_source,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.appStuckIotaTransientThreeSegments,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaFirstResult,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaSecondResult,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.appStuckHead_constructed,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiBetaInner_constructed,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaIntermediate_constructed,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.appStuckHead_tr_ctx,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.appStuckHead_type_ctx,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaIntermediate_tr,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.support_le_multiIotaSupport,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaStateInv,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaSupport_start,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaSupport_intermediate,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaSupport_head,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaSupport_result,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaFirstTrace,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaSecondTrace,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaThirdTrace,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaTransientThreeSegments,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaPrefixSlice,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaFieldSlice,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaTrailingSlice,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaRuleEval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaRuleAcceptance,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaCtorEval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiIotaCtorAcceptance,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.missingRuleDescriptor,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.AmbientNat.missingRuleDescriptor_noZeroRule,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.AmbientNat.multiBetaMiddleSplit,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.multiBetaMiddleRebase,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.linearRecPartsRun,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.AmbientNat.linearRecPartsTrace,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.TcM.LazyFaultPreserves.of_none,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.natRecLiteralParts_wf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.NatRecLiteralPartsPreserves.of_lazy,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatRecLiteralPartsPreserves.eager,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isNatLiteralRecursorApp_wf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.isTransientNatLiteralWork_wf,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.TransientNatWork.preserving,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isTransientNatLiteralWork_noLazy,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.TransientNatWork.eager,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },

  -- ordered no-delta reduction: the production no-delta tail has an explicit seam.  Exact equations
  -- pin projection-app completion, every ordered success/fallback branch, and
  -- every partial error state.  The semantic package composes structural and
  -- reducer meanings, while the closed Nat.add fixture makes precedence
  -- executable and records its three canonical-address decisions explicitly.
  { root := ``Ix.Tc.RecM.tryProjAppReduceFinished_some,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.tryProjAppReduceFinished_none,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.tryProjAppReduceFinished_projError,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.tryProjAppReduceFinished_finishError,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_projApp,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_bitvec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_nat,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_native,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_string,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_projectionDef,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_quotFull,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_quotCheap,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_doneFull,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_doneCheap,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_projError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_bitvecError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_natError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_nativeError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_stringError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_projectionDefError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_quotFullError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_quotCheapError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplStep_ofCore,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplStep_coreError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplStep_reducerError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplStep_next_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplStep_done_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplStep_error_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.noDeltaNatAddReduction,
    standardAxioms := standard, nativeAxioms := natReductionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.noDeltaNatBranchOrder,
    standardAxioms := standard, nativeAxioms := natBranchOrderNative,
    forbiddenDependencies := legacyWholeEnv },

  -- primitive reduction: `.noAccel` concretely discharges the native and BitVec optional
  -- reducers.  The five active helpers remain an explicit base oracle, which
  -- now feeds the exhaustive tail, outer step, and public no-delta shell.
  { root := ``Ix.Tc.RecM.tryReduceNative_noAccel_optional_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceBitvec_noAccel_optional_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.NoDeltaBaseOracle.toNoAccel,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNoDeltaReducersStep_noAccel_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplStep_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImplStep_noAccel_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNoDeltaImpl_noAccel_wf_of_base,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- WHNF layer policy: production WHNF layers bind every observable primitive-table
  -- address to `PrimAddrs.canonical`; the separate structural layer retains
  -- table-parametric syntax tests without being eligible for production
  -- reducer closure.  The world/context interface then binds the active Nat,
  -- String, projection, and quotient IDs to trusted Theory names and scopes
  -- generated results to actual successful helper executions.
  { root := ``Ix.Tc.Primitives.ofAnonAddrs_canonical,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfStateInv.noAccel_primitives,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfStateInv.accelerated_primitives,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.PrimitiveIdAgrees.contains,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.PrimitiveIdAgrees.mono,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.NoDeltaPrimitiveTableAgrees.mono,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.NoDeltaPrimitiveContext.stateTable,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  -- Nat reducer callback: the Nat reducer's shared callback/fuel boundary and exact binary
  -- arithmetic hit.  The primitive computation is derived from the bound
  -- canonical table and Lean4Lean reflection laws; no raw address equality
  -- is treated as semantic authority.
  { root := ``Ix.Tc.WhnfStateInv.set_recFuel,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.WF.tryCatch,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfRec_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNatReducerArg_post_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNatReducerArg_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.NoDeltaPrimitiveContext.computeNatBin_defeq,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TrKExprS.of_extractNatLit,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TrKExprS.natExprFromValue,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TrKExprS.natBinExact_inv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfPost.of_extractNatLit,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfMeaning.natBinExact,
    standardAxioms := standard, sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binArithExact,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binArithExact_acceptance,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- Nat primitive classification: canonical classifier derivation and exact Bool-predicate hits.  The
  -- generic proof uses trusted-name separation instead of native hash
  -- inequalities, and the finite Bool intern is checked against explicit run
  -- collision freedom and generated-node support.
  { root := ``Ix.Tc.TcM.intern_whnf_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.intern_whnf_eval,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.PrimitiveIdAgrees.addr_ne,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.NoDeltaPrimitiveContext.computeNatBin_classifiers,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.NoDeltaPrimitiveContext.natPredicate_classifiers,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.NoDeltaPrimitiveContext.natPredicate_defeq,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TrKExprS.boolExprFromDecision,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatPredicate_exact,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binPredExact,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binPredExact_acceptance,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- binary Nat early-out: exhaustive early-out traces and state closure for exact binary Nat
  -- reduction.  Callback errors retain their partial state, arithmetic and
  -- predicate extraction order is pinned, and the complete two-argument
  -- dispatcher preserves the invariant on every outcome.
  { root := ``Ix.Tc.RecM.WF.withInv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.prims_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isNatBinArithAddr_inv_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isNatBinPredAddr_inv_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNatReducerArg_ok_inv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.whnfNatReducerArg_error_inv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatPredicate_bin_inv_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_bin_inv_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatPredicate_argAMiss,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatPredicate_argAError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatPredicate_extractAMiss,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatPredicate_argBMiss,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatPredicate_argBError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatPredicate_extractBMiss,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binPredMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binPredError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binArithArgAMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binArithArgAError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binArithArgBMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binArithArgBError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binArithExtractAMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binArithExtractBMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binArithComputeMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  -- binary Nat success: every successful exact-binary Nat run is inverted into its actual
  -- callback/extraction/computation-or-intern trace, then folded into a
  -- semantic optional-reduction Hoare slice.  Predicate precedence remains
  -- operationally exhaustive even before canonical classifier separation.
  { root := ``Ix.Tc.RecM.isNatBinArithAddr_eval,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isNatBinPredAddr_eval,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isNatBinPredAddr_true,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binPredAnyExact,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatPredicateSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatPredicateSuccessTrace.complete,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatBinSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatBinSuccessTrace.complete,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatBinSuccessTrace.acceptance,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_bin_optional_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.structuralInvariant_does_not_bind_primitives,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.productionNoAccelStateInv,
    standardAxioms := standard, nativeAxioms := nameNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.noAccelInvariant_rejects_mismatched_primitives,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Nat suffix reduction: production `collectSpine` is reconciled with a typed structural
  -- spine, exact Nat equations are transported over arbitrary unchanged
  -- argument suffixes, and finite rebuild certificates preserve state and
  -- support.  Successful general-spine executions are inverted exhaustively.
  { root := ``Ix.Tc.RecM.appSpineView_go,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.appSpineView_collectSpine,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Tc.RecM.trAppSpine_of_tr,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSpine.argument,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSpine.tr,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.trAppSpine_of_collectSpine,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TrKExprS.foldlMkApp_initial,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfMeaning.appSameArg,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfMeaning.foldlMkApp,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfMeaning.mkAppN,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfMeaning.ofSharedSourceTranslation,
    standardAxioms := standard, sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatPredicate_suffixExact,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binPredSuffixExact,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binArithSuffixExact,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binArithSuffix_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryReduceNatWithSuccMode_binPredSuffix_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatPredicateSuffixSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatPredicateSuffixSuccessTrace.complete,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatSpineSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatSpineSuccessTrace.complete,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.noDeltaNatAddSuffixSpine,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.noDeltaNatAddSuffixFinishRequests,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.noDeltaNatAddSuffixReduction,
    standardAxioms := standard, nativeAxioms := natSuffixReductionNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Nat suffix closure: all general-spine misses and callback errors preserve the full
  -- invariant without suffix assumptions.  A successful trace is enriched
  -- with only its observed finite rebuild requests, then interpreted as the
  -- fixed-state optional-reduction Hoare contract.  The over-applied Nat.add
  -- fixture inhabits that execution-indexed coverage boundary.
  { root := ``Ix.Tc.RecM.finishAppResult_total,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natBinSpine_inputs,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatPredicate_spine_nonhit_inv,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_spine_nonhit_inv,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatSpineCertifiedSuccess.trace,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatSpineCertifiedSuccess.acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_spine_optional_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.noDeltaNatAddSuffixCertifiedSuccess,
    standardAxioms := standard, nativeAxioms := natSuffixCertificateNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.noDeltaNatAddSuffixFinishCoverage,
    standardAxioms := standard, nativeAxioms := natSuffixReductionNative,
    forbiddenDependencies := legacyWholeEnv },

  -- successor-collapse loop: the production successor-collapse loop is split into named seams
  -- whose entry, callback, literal, peel, memo-hit, memo-miss, and partial-
  -- error equations are exhaustive.  Stuck-marker writes preserve the full
  -- cache/state invariant only under explicit per-key provenance.  The
  -- closed Nat.succ fixture runs through the actual dispatcher and bounded
  -- driver without mutating the state.
  { root := ``Ix.Tc.CacheInvariant.insertNatSuccStuck,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheInvariant.insertNatSuccStuckList,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheInvariant.insertNatSuccStuckArray,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatSuccStuckCacheUpdate.fold_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccIter_entryHit,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccIter_entryKeyError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccIter_entryMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccIterStep_linearHit,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccIterStep_linearError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccIterStep_whnfError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccIterStep_afterWhnf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccAfterWhnf_literal,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccAfterWhnf_stuck,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.recordNatSuccStuck_eval,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.recordNatSuccStuck_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccPeel_keyError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccPeel_afterKey,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccPeelAfterKey_hit,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccPeelAfterKey_miss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccPeelMiss_keyError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccPeelMiss_next,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccAfterWhnf_succ,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_succ_stuck,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_succ_collapse,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.succCollapseSpine,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.succCollapseLinearMiss,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.succCollapseWhnf,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.succCollapseExtract,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.succCollapseStep,
    standardAxioms := standard,
    nativeAxioms := contextNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.succCollapseKey,
    standardAxioms := standard,
    nativeAxioms := contextNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.succCollapseMemoMiss,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.succCollapseIter,
    standardAxioms := standard,
    nativeAxioms := contextNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.succCollapseReduction,
    standardAxioms := standard,
    nativeAxioms := contextNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },

  -- successor-collapse semantics: semantic closure of the actual successor-collapse loop.  Negative
  -- memo markers are semantically inert but retain exact source/reference
  -- provenance; the ghost loop state tracks Nat typing, arbitrary successor
  -- offsets, and every pending marker.  Linear Nat.rec recognition remains
  -- behind its explicit oracle until inductive iota semantics instantiate it.
  { root := ``Ix.Tc.WhnfCacheValid.natSuccStuck,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheProvenance.whnfNatSuccStuck,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatSuccStuckWriteOracle.forWhnfCache,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natSucc_hasType,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natSuccSpine_tr,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccPeel_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccAfterWhnf_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccIterStep_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccIter_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Outer Nat integration: attach the semantic successor loop to the actual
  -- outer Nat
  -- dispatcher, recover successful generated support from that execution,
  -- and exhaustively assemble short, successor, and general-spine branches
  -- in both successor policies.  The general branch consumes only a finite
  -- request census; descriptor safety is derived from the lazy-hook contract,
  -- while successful callback meaning reduces the former exact-arity
  -- assumption to canonical Nat/Bool result-shape separation.  Nat.rec
  -- reflection and that Theory shape fact remain explicit.
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_succ_optional_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.NatCollapseRequestCensus.suffix_eq_empty_of_result_shape,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatCollapseRequestCensus.of_no_suffix,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatCollapseRequestCensus.of_result_shape,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatCollapseRequestCensus.certify,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isNatSuccIhStep_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatSuccLinearRec_effect_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatSuccLinearOracle.of_reflection,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_collapse_optional_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryReduceNatWithSuccMode_collapse_optional_wf_of_boundaries,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_stuck_short,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryReduceNatWithSuccMode_stuck_optional_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryReduceNatWithSuccMode_stuck_optional_wf_of_boundary,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryReduceNatWithSuccMode_optional_wf_of_boundaries,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.tryReduceNatWithSuccMode_optional_wf_of_lazy_boundaries,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.AmbientNat.succStuckReduction,
    standardAxioms := standard,
    nativeAxioms := contextNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },

  -- K2a: suffix semantics reduce open-context cache validity to one explicit
  -- operational model.  The recursive method table closes by induction from
  -- an exact one-layer contract split between WHNF and Infer/DefEq ownership.
  { root := ``Ix.Tc.WhnfSuffixModel.keyRepresents,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfSuffixModel.cacheWriteOracle,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.Methods.LayerWF.of_parts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.Methods.Closed.of_parts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.Methods.methodsOut_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.Methods.methodsN_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.runRec_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- K2a also assigns exact meanings to the remaining cache families.  A
  -- positive DefEq result carries Theory equality; negative results are
  -- intentionally vacuous for the one-way soundness claim.
  { root := ``Ix.Tc.InferMeaning.mono,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.InferMeaning.post,
    standardAxioms := standard, sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.InferCacheValid.mono,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheInvariant.inferHitOfMatches,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.DefEqMeaning.mono,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.DefEqMeaning.of_translations,
    standardAxioms := standard, sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.DefEqCacheValid.mono,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheProvenance.kernelWhnfMeaningOfMatches,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheProvenance.kernelInferMeaningOfMatches,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheProvenance.kernelDefEqMeaning,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },

  -- K2b: production key executions now generate the canonical operational
  -- context witnesses.  Physical inference/DefEq writes preserve every
  -- cache partition, including the rejection-only same-head failure set.
  { root := ``Ix.Tc.CacheInvariant.insertInfer,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheInvariant.insertInferOnly,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheInvariant.insertDefEq,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheInvariant.insertDefEqCheap,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheInvariant.insertDefEqFailure,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.ctxAddrForLbr_empty,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.whnfKey_ctx,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.operationalWhnfContextKeys.represents,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.operationalWhnfContextKeys.representsCtx,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ContextDigestSpec.execution,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ContextDigestSpec.StateValid,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ContextDigestSpec.memoValid,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ContextDigestSpec.preserves,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.ctxAddrForLbr_trivial,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.ctxAddrForLbr_cacheHit,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.ctxAddrForLbr_cacheMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.ctxAddrForLbr_replay,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.ContextAddrMemoValid,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.ctxAddrForLbr_memoValid,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.scopedOperationalWhnfContextKeys.represents,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.scopedOperationalWhnfContextKeys.representsCtx,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.scopedOperationalWhnfContextKeys.digest_eq,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.scopedOperationalWhnfContextKeys.mem,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.WhnfSuffixModel.operational,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.inferKey_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.inferKey_operational_matches_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.inferWith_fullHit,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.inferWith_inferOnlyHit,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.InferCacheUpdate.full_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.InferCacheUpdate.inferOnly_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },

  -- The union-find frame and joint suffix model keep composite context-hash
  -- transport explicit for WHNF, inference, and DefEq.  Collision-robust
  -- provenance constructors quantify over every supported address peer.
  { root := ``Ix.Tc.TcM.withEquiv_eq,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.withEquiv_whnf_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.defEqCtxKey_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.defEqCtxKey_operational_matches_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.DefEqMeaning.of_addr_beq,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.DefEqMeaning.symm,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KernelSuffixModel.toWhnfSuffixModel,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KernelSuffixModel.operational,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ContextSuffixSemantics.whnf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ContextSuffixSemantics.infer,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ContextSuffixSemantics.defEq,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ScopedKernelSuffixModel.represents,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ScopedKernelSuffixModel.StateInScope,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ScopedKernelSuffixModel.whnfTransport,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ScopedKernelSuffixModel.inferTransport,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ScopedKernelSuffixModel.defEqTransport,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ScopedKernelSuffixModel.finiteOperational,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.ScopedKernelSuffixModel.toKernelSuffixModel,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KernelSuffixModel.finiteOperational,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheProvenance.kernelDefEqMeaningCanonical,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KernelSuffixModel.inferProvenance,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KernelSuffixModel.defEqProvenance,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.KernelSuffixModel.defEqFailureProvenance,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqCacheUpdate.full_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqCacheUpdate.cheap_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqCacheUpdate.failure_whnfStateInv,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },

  -- First production K2 branches: both inference hit partitions, collision-
  -- safe DefEq address reflexivity, and a positive full DefEq hit including
  -- canonical ordering and its final union-find mutation.
  { root := ``Ix.Tc.RecM.isDefEq_fullHit_true,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isDefEq_fullHit_true_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isDefEq_addrEq_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.inferWith_fullHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.inferWith_inferOnlyHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The memoized proposition classifier closes proof irrelevance's sole
  -- auxiliary cache family.  Positive hits and writes are tied to `Sort 0`
  -- through expression collision freedom and the explicit suffix model.
  { root := ``Ix.Tc.RecM.isPropType_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryProofIrrel_classifier_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Lazy delta is a bounded semantic state machine.  These roots expose the
  -- pair invariant, the fuel-bounded closure, and the exact remaining
  -- obligations for one iteration and the stopped continuation.
  { root := ``Ix.Tc.RecM.DefEqPairInvariant.refl,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqPairInvariant.conclude,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.runDefEqLazyDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isDefEqInnerAfterProofIrrelevance_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqAfterProofIrrelevance.ofLazyDelta,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- The front of each lazy-delta iteration now closes the actual Nat-offset
  -- literal/zero guards and both ordinary Nat-reduction attempts.  Structural
  -- offset decomposition and the post-Nat reducer tiers remain explicit
  -- continuation contracts; negative recognizer results carry no semantics.
  { root := ``Ix.Tc.RecM.isNatZero_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsNatZero.ofContext,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryDefEqOffset_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryDefEqOffset.ofContext,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.defEqLazyDeltaStepAfterOffsetMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqLazyDeltaAfterOffsetMiss.ofNat,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.defEqLazyDeltaStepAfterNatMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqLazyDeltaAfterNatMiss.ofNoAccel,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.classifyDeltaHead_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.defEqLazyDeltaStepAfterAcceleratorMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.DefEqLazyDeltaAfterAcceleratorMiss.ofClassification,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryUnfoldProjApp_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.defEqLazyDeltaStepAfterDeltaClassification_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.DefEqLazyDeltaAfterDeltaClassification.ofProjection,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.finishDefEqLazyDeltaStep_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.defEqLazyDeltaStepWithLeftDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.defEqLazyDeltaStepWithRightDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.rankDeltaHead_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.defEqLazyDeltaStepAfterProjectionMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqLazyDeltaAfterProjectionMiss.ofRankDispatch,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.defEqLazyDeltaStepAfterSameHeadMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqLazyDeltaAfterSameHeadMiss.ofReduction,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Equal-rank closure: recursive spine arguments, constant-universe
  -- congruence, and the rejection-only failure-cache shell.  A cache hit can
  -- only skip the comparison; every positive result still comes from the
  -- semantic same-head proof.
  { root := ``Ix.Tc.RecM.allDefEqSpineArgs_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrAppSpine.defEq_of_zip,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.sameDefEqUniverses_sound,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.constantHeadsDefEq,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.trySameHeadSpine_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrySameHeadSpine.ofResources,
    standardAxioms := standard, nativeAxioms := blake3Native,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.CacheEntry.defEqFailureReferencesAuthorized,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.DefEqFailureCacheResources.ofKernelSuffixModel,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isRegular_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.trySameHeadSpineCached_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TrySameHeadSpineCached.ofResources,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.defEqLazyDeltaStepWithEqualRank_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqLazyDeltaEqualRank.ofPrefix,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqLazyDeltaEqualRank.ofKernelResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The Nat-offset candidate branch is state-safe on every parser and rebuild
  -- path.  Its only semantic input is an exact successful-run reflection;
  -- recursive equality is transported forward through the common successor
  -- suffix, without assuming offset injectivity or completeness.
  { root := ``Ix.Tc.TcM.WF.withInvRunEq,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natOffsetDecompose_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natOffsetRebuild_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryDefEqOffsetAfterCandidates_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryDefEqOffsetAfterCandidates.ofContext,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The stopped continuation now closes its exact outer control flow.  The
  -- general app probe reconstructs equality through both typed spines;
  -- structural congruence proves constants and variables directly and
  -- delegates matching projections to one execution-indexed helper contract.
  { root := ``Ix.Tc.RecM.tryDefEqApp_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryDefEqApp.ofResources,
    standardAxioms := standard, nativeAxioms := blake3Native,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryStructuralCongruence_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryStructuralCongruence.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isDefEqAfterLazyDeltaStopped_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqAfterLazyDeltaStopped.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqLazyDeltaContext.ofKernelResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.DefEqAfterProofIrrelevance.ofKernelResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The structural projection callback's bounded lazy-delta driver preserves
  -- the original projected semantics across delta steps, direct projection
  -- reduction, recursive comparison, and normal depth exhaustion.
  { root := ``Ix.Tc.RecM.lazyDeltaProjReduction_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.LazyDeltaProjReduction.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Direct projection reduction gets state/support closure from the proved
  -- no-acceleration helper and consults semantic reflection only for the
  -- exact successful execution that occurred.
  { root := ``Ix.Tc.RecM.tryProjReduce_direct_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryProjReduce.ofDirectResources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },

  -- The compact projection-loop delta step exposes its two lazy declaration
  -- classifications as a proved prefix; the exact branch continuation sees
  -- only their concrete results.
  { root := ``Ix.Tc.RecM.lazyDeltaReductionStep_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.LazyDeltaReductionStep.ofClassification,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.lazyDeltaReductionStepAfterClassification_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.LazyDeltaReductionAfterClassification.ofActive,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.LazyDeltaReductionStep.ofActive,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Once classification reports an active delta head, the compact step is
  -- exhaustive: projection hits enter the productive finish, misses select
  -- one- or two-sided unfolding, and equal ranks try same-head congruence
  -- before normalizing both sides.  The final two roots assemble that branch
  -- proof with the already-audited classifier prefix.
  { root := ``Ix.Tc.RecM.finishLazyDeltaReductionStep_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.lazyDeltaReductionStepWithLeftDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.lazyDeltaReductionStepWithRightDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.lazyDeltaReductionStepAfterSameHeadMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.lazyDeltaReductionStepWithEqualRank_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.defRankId_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.lazyDeltaReductionStepWithBothDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.lazyDeltaReductionStepAfterActive_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.LazyDeltaReductionAfterActive.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.LazyDeltaReductionStep.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Concrete projection-loop assembly derives the compact step, bounded
  -- projection comparison, and structural-congruence projection branch from
  -- named lower reducers.  The exact-run direct projection reflection is the
  -- remaining semantic boundary; the outer loop itself is no longer one.
  { root := ``Ix.Tc.RecM.ProjectionDeltaClosureResources.loop,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.LazyDeltaProjReduction.ofClosureResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.TryStructuralCongruence.ofProjectionDeltaResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The stopped continuation now derives its structural field from the
  -- concrete projection loop and reuses that record's core/quick resources;
  -- only application-spine and final-WHNF contracts remain as sibling inputs.
  { root :=
      ``Ix.Tc.RecM.StoppedContinuationClosureResources.stopped,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Tc.RecM.DefEqAfterLazyDeltaStopped.ofClosureResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The final-WHNF comparator is split at a production seam: an optional
  -- constructor-directed prefix followed by the fallback chain.  Application
  -- comparison and every constructor in the prefix are now exhaustive
  -- concrete proofs.  The let roots include exact allocation, common-fvar
  -- body opening, context transport, and local-scope restoration.
  { root := ``Ix.Tc.RecM.isDefEqWhnf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsDefEqWhnf.ofPhases,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryDefEqWhnfApp_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryDefEqWhnfApp.ofResources,
    standardAxioms := standard, nativeAxioms := blake3Native,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.TcM.openLetWithFV_scope,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.withLctxScope_openLetWithFV_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryDefEqWhnfLet_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryDefEqWhnfLet.ofResources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isNatLike_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.natSuccOf_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.NatSuccOf.ofResources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isDefEqNatAfterLiteral_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isDefEqNat_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryDefEqWhnfNat_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryDefEqWhnfNat.ofResources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isDefEqWhnfAfterStructural_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsDefEqWhnfAfterStructural.ofNat,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryDefEqWhnfStructural_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryDefEqWhnfStructural.ofResources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Lambda eta is split into a syntactic guard, caught infer/WHNF probes, and
  -- an explicit term builder.  The builder's lifted source and generated #0
  -- application are translated structurally before the recursive comparison
  -- is composed with Theory eta; the ordered reverse attempt uses symmetry.
  { root := ``Ix.Tc.TcM.lift_whnf_wf_of_resources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.compareEtaExpansion_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryEtaExpansionAfterGuard_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryEtaExpansion_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryDefEqWhnfEtaAfterGuard_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryDefEqWhnfEta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryDefEqWhnfEta.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isDefEqWhnfAfterNat_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsDefEqWhnfAfterNat.ofEta,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The final-WHNF String phase reuses the exact expansion plans proved for
  -- the earlier DefEq tier.  Its optional result preserves the original
  -- two-way short-circuit order; reverse success is justified by symmetry.
  { root := ``Ix.Tc.RecM.tryDefEqWhnfStringAfterGuard_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryDefEqWhnfString_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryDefEqWhnfString.ofContext,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isDefEqWhnfAfterEta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsDefEqWhnfAfterEta.ofString,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- The terminal final-WHNF chain is split at the two inductive boundaries.
  -- Proof irrelevance is concrete through the memoized proposition
  -- classifier; unit-like and structure-eta soundness remain separately
  -- named contracts until their exact inductive laws are supplied.
  { root := ``Ix.Tc.RecM.isDefEqWhnfAfterUnit_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsDefEqWhnfAfterUnit.ofClassifier,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isDefEqWhnfAfterStructEta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsDefEqWhnfAfterStructEta.ofUnitAndProof,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.isDefEqWhnfAfterString_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.IsDefEqWhnfAfterString.ofStructEta,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- The unit-like classifier is tied to the exact immutable-catalog entries
  -- returned by both lazy lookups.  The shortcut then consumes only the
  -- narrow unique-inhabitant law for that trusted zero-index, one-nullary-
  -- constructor shape; it does not recover the legacy whole-environment
  -- inductive oracle.
  { root := ``Ix.Tc.RecM.isUnitLikeInductive_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.tryDefEqUnit_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Tc.RecM.TryDefEqUnit.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  { root := ``Ix.Tc.RecM.DefEqLazyDeltaStep.ofKernelResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Structure eta is proved from the exact normalized source, immutable
  -- constructor lookup, typed field spine, and generated projection law.
  -- The positive structure classifier cannot manufacture semantic eta on
  -- its own, and every exported root remains quarantined from both legacy
  -- whole-environment and broad delta-authority paths.
  { root := ``Ix.Tc.TrKExprS.prj_components,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.tryEtaStructFields_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.etaExpansionBaseLoop_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.etaExpansionBase_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.tryEtaStructAfterTypes_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.normalizeEtaStructSource_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.tryEtaStructAfterConstructor_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.tryEtaStructAfterNormalization_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.tryEtaStruct_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.tryDefEqWhnfStructEta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.TryDefEqWhnfStructEta.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- The final-WHNF phases are now assembled in exact production order.
  { root := ``Ix.Tc.RecM.FinalWhnfClosureResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.FinalWhnfClosureResources.afterStructural,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.FinalWhnfClosureResources.finalWhnf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- Recursive DefEq closure: trusted finite expression references authorize
  -- only the two direct roots of an ordinary result entry.  The complete
  -- inner tier then feeds the guarded public cache shell.
  { root := ``Ix.Tc.CacheEntry.defEqReferencesAuthorized,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.DefEqInner.WF,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.isDefEq_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.DefEqClosureResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.DefEqClosureResources.stopped,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.DefEqClosureResources.lazyDelta,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.DefEqClosureResources.inner,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.DefEqClosureResources.entryPoint,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.DefEqClosureResources.nextDefEq_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- Inference and DefEq consume the same predecessor table and suffix model;
  -- their fixed-universe pair closes before it is joined to the four WHNF
  -- fields.
  { root := ``Ix.Tc.UncachedInference.Context.nextInfer_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.InferDefEqClosedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.InferDefEqClosureContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.InferDefEqClosureContext.layer,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.InferDefEqClosureContext.closedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- Legacy all-depth six-field knot assembly under the canonical production
  -- cache stack.  These roots remain audited as migration adapters, but the
  -- bounded public interfaces below are forbidden from depending on them.
  { root := ``Ix.Tc.kernelCacheFallback,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.kernelCacheSemantics_eq_k1,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.ClosedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.ClosedAt.of_parts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.runRec_wfAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecursiveMethodClosureContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecursiveMethodClosureContext.closedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecursiveMethodClosureContext.methodsN,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- The all-depth closure interface is provably unusable for a
  -- finite support containing a sort: its syntax resources would generate
  -- an unbounded successor-sort chain.  The replacement below separates the
  -- finite result footprint from fuel-indexed method-call domains.
  { root :=
      ``Ix.Tc.FiniteSupportBoundary.SyntaxInferenceResources.no_sort_source,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- C1A's usable production boundary: a finite schedule closes only the
  -- method-table depths selected by this run's recursion fuel.  The public
  -- adapters consume the terminal successor-layer domain and have no
  -- `sorryAx` dependency.
  { root := ``Ix.Tc.Methods.CallDomain.empty_within,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.Methods.CallDomain.singletonInfer_within,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.Methods.methodsOut_wfAtOn,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.Methods.CallScheduleAt.methodsN,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.Methods.CallScheduleAt.nextSelected,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecursiveMethodRunContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.TcM.whnf.wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.TcM.infer.wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.TcM.isDefEq.wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.Methods.SortSchedule.two,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.TcM.infer.sort_wf_bounded,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.TcM.infer.sort_wf_fuel_one,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },

  -- K3 reconstructs the typed source translation from untyped/scoped
  -- checker ingress.  These roots are usable before the final checkConst
  -- assembly and do not depend on its statement placeholder.
  { root := ``Ix.Tc.KUniv.scoped_iff_toVLevel_wf,
    standardAxioms := propextOnly,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.PreTrKExprS.upgradeOfTyped,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TrKExprS.openFVarZero,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Lean4Lean.VExpr.inst_subst_cons,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RawCtxInterp.find?_inl,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RawCtxInterp.bvars_eq,
    standardAxioms := propextOnly,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RawProjRel.none_substCompatible,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RawExprRel.toPre_of_scoped_aux,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RawExprRel.toPre_of_scoped,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RawDeclRel.toPre_of_scope,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.PendingDecl.toPre_of_scope,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TypeCheckEvidence.isType,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.ValueCheckEvidence.hasType,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.StandaloneCheckEvidence.accepted,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.StandaloneCheckResult.accepted,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RawDeclRel.wfOfAccepted,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.PendingDecl.promoteOfAccepted,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.PendingDecl.checkResultAndPromote,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateUnivParamsSeen_go_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateUnivParamsSeen_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateUnivRootsList_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateUnivRootsArray_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateExprWellScoped_go_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateExprWellScoped_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateConstWellScoped_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.PendingDecl.toPre_of_validation,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.PendingDecl.checkValidatedResultAndPromote,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateUnivParamsSeen_go_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateUnivParamsSeen_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateUnivRootsList_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateUnivRootsArray_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.getConst_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.hasConst_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateExprWellScoped_go_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateExprWellScoped_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.validateConstWellScoped_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.LazyFaultPreserves.withInferOnly,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkTypePipeline_sound,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkValuePipeline_sound,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.FullInferenceWFAtOn.ofTypedIngress,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.Methods.FullInferenceWFAtOn.ofSingletonSort,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.StandalonePipelineResources.singletonSortAxiom,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkTypePipeline_bounded_sound,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkValuePipeline_bounded_sound,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkConstMember_axiom_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkConstMember_defn_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkConstMember_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkConstMember_validation_success,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkConstMember_pending_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkConstMemberFresh_pending_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.StandaloneRoute.axiomRoute,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkConst_standalone_pending_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkNoUnsafeRefs_go_frame,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkNoUnsafeRefs_frame,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.KernelStateWF.rebaseWorld,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.WhnfStateInv.rebaseWorld,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.reset_whnf_entry,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.FullInferPost.of_typed,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.WF.withInv,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferWith_fullHit_pre_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_sort_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_var_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_fvar_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_const_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_nat_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_str_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.FullInferenceStepContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_app_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.PreservesInferOnly.strengthenWFValue,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.PreservesInferOnly.withInferOnly,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.PreservesInferOnly.openBinder,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.PreservesInferOnly.inferKey,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.cacheInferResult_preservesInferOnly,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.withLctxScope_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.ensureForallDirect_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.ensureSortDirect_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.methodsOut_preservesInferOnly,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.methodsN_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.PreservesInferOnly.isDefEq_full_wf,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.openBinder_scope_base,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.openBinder_pre_scope,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.KExpr.abstractFVarsSpec_instantiateRevSpec_singleton,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TrKExprS.closeOpenedFVarZero,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.withLctxScope_openBinder_pre_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_lam_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_all_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.openLet_scope_base,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.openLet_pre_scope,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.withLctxScope_openLet_pre_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_let_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.ProjectionInference.FullWFAt.of_semantic_and_policy,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_prj_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferWith_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.infer_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.PreservesInferOnly.instantiateUnivParams,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.inferUncached_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.ProjectionInference.preservesInferOnlyAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecM.infer_preservesInferOnly_of_whnf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- K3 closes the concrete operational policy and retains the old strong
  -- all-support inference roots below as compatibility artifacts.  The
  -- public checker now consumes the bounded successor-layer resources above.
  { root := ``Ix.Tc.Methods.next_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.inferOnlyClosed,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.methodsN_concrete_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.FullInferenceWFAt,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecursiveMethodClosureContext.fullInferenceContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecursiveMethodClosureContext.next_fullInferenceWFAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.Methods.methodsOut_fullInferenceWFAt,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecursiveMethodClosureContext.methodsN_fullInferenceWFAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.RecursiveMethodClosureContext.publicInfer_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.checkConst.rollback_on_error,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.checkConst.rollback_preserves_kernel,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.TcM.checkConst.wf,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.TcM.checkConst.rejected_of_no_decl_wf,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.TcM.checkConst.axiom_pending_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkConstMemberFresh_scoped_pending_evidence,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },

  -- E0 closes the atomic coordinated-block transaction around the real
  -- production router, classifier, body, and block-result cache.  The
  -- singleton-definition adapter consumes K3; inductive/recursor bodies keep
  -- their E2 oracle premise explicit.  Quotients are audited as excluded from
  -- this authority rather than being silently admitted by the block theorem.
  { root := ``Ix.Tc.ExactCheckBlock.rebaseWorld,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.coordinatedBlockIfKind_success_trace,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.classifyBlock_wf,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.coordinatedBlockFor_some_preserves,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.CacheInvariant.replayCoordinatedMember,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.CacheInvariant.rejectsSuccessWithUntrustedMember,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkCoordinatedBlock_accepted,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkCoordinatedBlock_rejected,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkConst_success_disposition,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.TcM.checkConst.blockDisposition,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.certifySingletonDefinition,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.certifySingletonDefinitionScoped,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.RecM.certifyOracleBackedBlock,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.coordinatedBlockFor_quotient,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.Catalog.quotient_not_coordinated,
    standardAxioms := propextOnly,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  -- Quotients remain physically standalone, but semantic admission is one
  -- exact four-member Theory transaction followed by the registered quotient
  -- equation. The production bridge inverts all four real checkQuot runs,
  -- converts digest equality through a finite collision scope, and publishes
  -- the completed transaction as one exact trusted-log event. Its temporary
  -- Lean4Lean semantic input is an explicit theorem parameter, not an axiom.
  { root := ``Ix.Tc.QuotientAdmissionStep.bind,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientAdmissionStep.le,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientBundleAdmission.catalogEntries,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientBundleAdmission.nameAssignments,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientBundleAdmission.toAddQuot,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientBundleAdmission.le,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientBundleAdmission.quotType,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientBundleAdmission.quotCtor,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientBundleAdmission.quotLift,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientBundleAdmission.quotInd,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientBundleAdmission.quotientDefEq,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientAdmission.wf,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientAdmission.le,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkQuot_success_typeAddress,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkQuot_success_levels,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.RecM.checkQuot_success_type,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.CheckedQuotientBundle.toAdmission,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientAdmission.entry,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientAdmission.admit,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.QuotientAdmission.newlyTrustedMember,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.CheckedQuotientBundle.admitAtomically,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AmbientNat.E0.atomicAdmission,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AmbientNat.E0.rejectsPrematureSuccess,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },

  -- E1 models semantic declaration dependencies in the production Address
  -- domain, proves buildAnonWork is an exact duplicate-free partition, and
  -- composes successful items in a constructive collapsed-block order.  The
  -- serial roots recover real successful checkConst calls from the public
  -- result array before applying the named C2 success adapter.
  { root := ``Ix.Tc.WorkCovers.covered,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.WorkCovers.subjectOfCovered,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.VerifyWorld.AcceptsAddress.mono,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.WorkItemAccepted.mono,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.WorkItemAccepted.acceptsAddress,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.WellFoundedBlocks.noTwoCycle,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.acceptedWorkset_subjectWF,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.IxonEnv.dependencyCatalog_blockOf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.IxonEnv.dependencyCatalog_dependsOn_iff,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.IxonExpr.DeclReference.target_mem_refs,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.IxonConstant.SemanticDependency.target_mem_refs,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.ExactAnonEntry.getConst,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.ExactAnonEntry.constant_unique,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.ExactAnonEntry.buildAnonWorkItem_eq,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.buildAnonWork_eq_expected,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.mem_expectedAnonWork_iff,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkItem.ofConstantInfo_root,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkItem.covers_root,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkItem.ofConstantInfo_primary_mem_targets,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.source_covered,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.covered_is_source,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.expected_primary_mem_targets,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.ExactAnonEntry.blockOfAddr_eq_owner,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.ExactAnonEntry.blockOfAddr_eq_self,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.matches_blockOfAddr,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.expectedAnonWork_covers,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.expectedAnonWork_matchesCatalog,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.buildAnonWork_exact,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.finishAnonCheckItem_results,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.runAnonCheckItem_preserves_result,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.runAnonCheckList_preserves_result,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.runAnonCheckItem_error_result,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.serialChecksSucceeded_of_results,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.SerialChecksSucceeded.successfulStep,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.SerialChecksSucceeded.allAccepted,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.checkEnvAnon_eq_serial,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.checkEnvAnon_subjectWF,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.E1Fixture.exactSubjectsAndAssumptions,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.E1Fixture.droppingWorkItem_breaks_coverage,
    standardAxioms := propextOnly,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.E1Fixture.unresolvedDependency_breaks_closure,
    standardAxioms := propextOnly,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.E1Fixture.cyclicStandalones_not_wellFounded,
    standardAxioms := propextOnly,
    forbiddenDependencies := boundedKnotForbiddenDependencies },

  -- E3-S assembles the scoped K3 standalone theorem and E0's exact atomic
  -- disposition into E1's concrete-call adapter.  The operational body sum
  -- remains transparent: singleton definitions use the scoped K3 certificate
  -- and fresh inductive/recursor bodies retain an explicit E2 oracle resource.
  -- Separately, the certificate-backed replay adapter consumes already-
  -- installed member provenance, admits exact arrays idempotently, and gives
  -- all-block consumers a path which cannot reach oracle materialization.
  { root := ``Ix.Tc.SupportedStandaloneResources.promotes,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.SupportedBlockBodyResources.certify,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.SupportedCheckRun.accepts,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.SupportedCheckFragment.checkSuccessSound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.AnonWorkEnvWF.checkEnvAnon_supported_subjectWF,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.CertificateBackedBlockResources.newlyTrustedMember,
    standardAxioms := standard,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root := ``Ix.Tc.CertificateBackedBlockResources.accepts,
    standardAxioms := standard, nativeAxioms := blake3Native,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root := ``Ix.Tc.CertificateBackedCheckFragment.checkSuccessSound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root :=
      ``Ix.Tc.AnonWorkEnvWF.checkEnvAnon_certificateBacked_subjectWF,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root := ``Ix.Tc.BooleanEnumerationFixture.subjectWF,
    standardAxioms := standard, nativeAxioms := booleanDriverNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root := ``Ix.Tc.BooleanSerialized.subjectWF,
    standardAxioms := standard, nativeAxioms := serializedBooleanNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root := ``Ix.Tc.SerializedLiteralBlobs.literalRoundTrip,
    standardAxioms := standard, nativeAxioms := literalRoundTripNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.SerializedLiteralBlobs.malformedConstantRejected,
    standardAxioms := standard, nativeAxioms := malformedConstantNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.SerializedLiteralBlobs.malformedBlobRejected,
    standardAxioms := standard, nativeAxioms := malformedBlobNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root :=
      ``Ix.Tc.SupportedAcceptanceFixture.block_rejects_standalone_route,
    standardAxioms := propextOnly,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.SupportedAcceptanceFixture.block_rejects_wrong_route,
    standardAxioms := propextOnly,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root :=
      ``Ix.Tc.SupportedAcceptanceFixture.certificate_backed_definition_excluded,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root :=
      ``Ix.Tc.SupportedAcceptanceFixture.booleanFamilyBody_certified,
    standardAxioms := standard, nativeAxioms := booleanFamilyBodyNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },

  -- Positive-fuel acceptance witness.  The original resource theorem leaves
  -- the joint suffix model explicit; the scoped checker roots below construct
  -- the finite model from their exact public execution certificate.  Two
  -- exact Blake3 address inequalities remain explicit fixture inputs.
  { root := ``Ix.Tc.PositiveFuelSort.methodContractAtFuelOne,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.PositiveFuelSort.fullInferenceAtFuelOne,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Tc.PositiveFuelSort.pipelines_cover_concreteAxiom,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },

  -- K2S closed-context vertical slice.  These roots certify the exact
  -- fuel-one public trace, package its finite requests and bounded recursive
  -- schedule, instantiate `ScopedKernelSuffixModel.finiteOperational`, and
  -- retain `StateInScope` through successful semantic promotion.  None may
  -- pass through the global suffix-model compatibility path.
  { root := ``Ix.Tc.PositiveFuelSort.Checker.model,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.PositiveFuelSort.Checker.initialState_inv,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.PositiveFuelSort.Checker.inference_run,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.PositiveFuelSort.Checker.public_requests,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.PositiveFuelSort.Checker.runAssumptions,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.PositiveFuelSort.Checker.publicContext,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Tc.PositiveFuelSort.Checker.checked_and_promoted,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },

  -- The joined ambient-Nat fixture uses the exact semantic pending objects
  -- and exact public checker executions for both verdicts.  Its valid path
  -- carries a concrete acceptance result and promotion; its invalid path
  -- returns the malformed-universe error with exact rollback.
  { root := ``Ix.Tc.AmbientNat.goodCheckResult,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.AmbientNat.initial_good_public,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.AmbientNat.reset_bad_public,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Tc.AmbientNat.publicCheckLifecycle,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies }
]

run_cmd Ix.Tc.Verify.Audit.check roots

end Ix.Tc.Verify.Audit.Completed
