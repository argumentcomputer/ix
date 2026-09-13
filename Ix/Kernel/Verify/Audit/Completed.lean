import Ix.Kernel.Verify.Audit.Basic
import Ix.Kernel.Verify.Check.Acceptance
import Ix.Kernel.Verify.Check.BoundedPipelines
import Ix.Kernel.Verify.Check.CheckerEvidence
import Ix.Kernel.Verify.Check.FullInferenceApplications
import Ix.Kernel.Verify.Check.FullInferenceBinders
import Ix.Kernel.Verify.Check.FullInferenceCache
import Ix.Kernel.Verify.Check.FullInferenceDispatcher
import Ix.Kernel.Verify.Check.FullInferenceProjections
import Ix.Kernel.Verify.Check.MemberEvidence
import Ix.Kernel.Verify.Check.NatAcceptance
import Ix.Kernel.Verify.Check.BlockNatFixture
import Ix.Kernel.Verify.Check.PreTranslationScopes
import Ix.Kernel.Verify.Check.PositiveFuelSort
import Ix.Kernel.Verify.Check.ScopedPositiveFuelCertificate
import Ix.Kernel.Verify.Check.SingletonInductive
import Ix.Kernel.Verify.Inductive.EnumerationAcceptance
import Ix.Kernel.Verify.Check.ProjectionInferencePolicy
import Ix.Kernel.Verify.Check.ResetFrame
import Ix.Kernel.Verify.Check.SafetyFrame
import Ix.Kernel.Verify.Check.PublicStandalone
import Ix.Kernel.Verify.Check.PublicBlocks
import Ix.Kernel.Verify.Check.ValidatorFrame
import Ix.Kernel.Verify.Ctx
import Ix.Kernel.Verify.Decl
import Ix.Kernel.Verify.DefEq
import Ix.Kernel.Verify.DefEq.AcceleratorGates
import Ix.Kernel.Verify.DefEq.ApplicationSpine
import Ix.Kernel.Verify.DefEq.CacheShell
import Ix.Kernel.Verify.DefEq.Closure
import Ix.Kernel.Verify.DefEq.DeltaClassification
import Ix.Kernel.Verify.DefEq.EqualRankCache
import Ix.Kernel.Verify.DefEq.EqualRankPrefix
import Ix.Kernel.Verify.DefEq.EqualRankReduction
import Ix.Kernel.Verify.DefEq.FinalWhnf.Application
import Ix.Kernel.Verify.DefEq.FinalWhnf.Closure
import Ix.Kernel.Verify.DefEq.FinalWhnf.Contracts
import Ix.Kernel.Verify.DefEq.FinalWhnf.EtaExpansion
import Ix.Kernel.Verify.DefEq.FinalWhnf.LetDeclaration
import Ix.Kernel.Verify.DefEq.FinalWhnf.NatBridge
import Ix.Kernel.Verify.DefEq.FinalWhnf.ProofTail
import Ix.Kernel.Verify.DefEq.FinalWhnf.StringExpansion
import Ix.Kernel.Verify.DefEq.FinalWhnf.StructuralPrefix
import Ix.Kernel.Verify.DefEq.FinalWhnf.StructureEta
import Ix.Kernel.Verify.DefEq.FinalWhnf.UnitLike
import Ix.Kernel.Verify.DefEq.LazyDelta
import Ix.Kernel.Verify.DefEq.LazyDeltaClosure
import Ix.Kernel.Verify.DefEq.LazyDeltaIteration
import Ix.Kernel.Verify.DefEq.LoopFinish
import Ix.Kernel.Verify.DefEq.NatOffset
import Ix.Kernel.Verify.DefEq.NatOffsetDecomposition
import Ix.Kernel.Verify.DefEq.NatReduction
import Ix.Kernel.Verify.DefEq.OneSidedDelta
import Ix.Kernel.Verify.DefEq.ProjectionDeltaActive
import Ix.Kernel.Verify.DefEq.ProjectionDeltaClosure
import Ix.Kernel.Verify.DefEq.ProjectionDeltaEqualRank
import Ix.Kernel.Verify.DefEq.ProjectionDeltaFinish
import Ix.Kernel.Verify.DefEq.ProjectionDeltaLoop
import Ix.Kernel.Verify.DefEq.ProjectionDeltaRank
import Ix.Kernel.Verify.DefEq.ProjectionDeltaStep
import Ix.Kernel.Verify.DefEq.ProjectionDeltaUnfolding
import Ix.Kernel.Verify.DefEq.ProjectionProbe
import Ix.Kernel.Verify.DefEq.ProjectionReduction
import Ix.Kernel.Verify.DefEq.PropositionClassifier
import Ix.Kernel.Verify.DefEq.RankDispatch
import Ix.Kernel.Verify.DefEq.SameHeadSpine
import Ix.Kernel.Verify.DefEq.SpineArguments
import Ix.Kernel.Verify.DefEq.StoppedContinuation
import Ix.Kernel.Verify.DefEq.StoppedContinuationClosure
import Ix.Kernel.Verify.DefEq.StructuralCongruence
import Ix.Kernel.Verify.Driver.Fixtures
import Ix.Kernel.Verify.Driver.BooleanAcceptance
import Ix.Kernel.Verify.Driver.SupportedAcceptanceFixtures
import Ix.Kernel.Verify.Execution
import Ix.Kernel.Verify.Frame
import Ix.Kernel.Verify.Infer.CacheSoundness
import Ix.Kernel.Verify.InferDefEq.Closure
import Ix.Kernel.Verify.Inductive.Certificate
import Ix.Kernel.Verify.Inductive.AliasFormerAdmission
import Ix.Kernel.Verify.Inductive.AliasRecAdmission
import Ix.Kernel.Verify.Inductive.AnnotatedPiCertificate
import Ix.Kernel.Verify.Inductive.AnnotatedPiAdmission
import Ix.Kernel.Verify.Inductive.EliminationBreadthFixture
import Ix.Kernel.Verify.Inductive.MutualBlockCertificate
import Ix.Kernel.Verify.Inductive.MutualFamilyAdmission
import Ix.Kernel.Verify.Inductive.IndexedRecursiveCertificate
import Ix.Kernel.Verify.Inductive.RecursivePiCertificate
import Ix.Kernel.Verify.Inductive.RecursivePiAdmission
import Ix.Kernel.Verify.Inductive.IndexedRecursiveAcceptance
import Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
import Ix.Kernel.Verify.Inductive.SpecializationIdentity
import Ix.Kernel.Verify.Inductive.GeneratedRecursorMetadata
import Ix.Kernel.Verify.Inductive.GeneratedRecursorAcceptance
import Ix.Kernel.Verify.Inductive.GeneratedRecursorAcceptanceClosure
import Ix.Kernel.Verify.Inductive.GeneratedRecursorAdmission
import Ix.Kernel.Verify.Inductive.IndexedProducerClosure
import Ix.Kernel.Verify.Inductive.GeneratedRecursorCheckerFixture
import Ix.Kernel.Verify.Inductive.GeneratedRecursorCommitFixture
import Ix.Kernel.Verify.Inductive.GeneratedRecursorComparison
import Ix.Kernel.Verify.Inductive.GeneratedRecursorRuleFixture
import Ix.Kernel.Verify.Inductive.GeneratedRecursorSelection
import Ix.Kernel.Verify.Inductive.GeneratedRecursorSemantics
import Ix.Kernel.Verify.Inductive.GeneratedRecursorTypeClosure
import Ix.Kernel.Verify.Inductive.GeneratedRecursorTypeFixture
import Ix.Kernel.Verify.Inductive.NestedAuxiliaryExpansion
import Ix.Kernel.Verify.Inductive.NestedAdmission
import Ix.Kernel.Verify.Inductive.NestedConstructorValidation
import Ix.Kernel.Verify.Inductive.NestedRecursiveFixture
import Ix.Kernel.Verify.Inductive.NestedRecursorAdmission
import Ix.Kernel.Verify.Inductive.OccurrenceClosure
import Ix.Kernel.Verify.Inductive.PositivityTraceAdapter
import Ix.Kernel.Verify.Inductive.RecursivePositivityTraversal
import Ix.Kernel.Verify.Ingress.LiteralBlobs
import Ix.Kernel.Verify.Ingress.SerializedBoolean
import Ix.Kernel.Verify.InstL
import Ix.Kernel.Verify.Whnf.Closure
import Ix.Kernel.Verify.Knot
import Ix.Kernel.Verify.NatFixture
import Ix.Kernel.Verify.Projection.ConcreteFixture
import Ix.Kernel.Verify.Run
import Ix.Kernel.Verify.RecursiveMethods.Closure
import Ix.Kernel.Verify.RecursiveMethods.FiniteSupportBoundary
import Ix.Kernel.Verify.RecursiveMethods.Public
import Ix.Kernel.Verify.Support
import Ix.Kernel.Verify.Totalization
import Ix.Kernel.Verify.Whnf
import Ix.Kernel.Verify.World

open Ix.Theory (VLevel)

/-!
# Trust manifest for the completed `Ix.Kernel.Verify` proof surface

These are the current completed foundations and reusable semantic interfaces
used by lookup, admission, and driver composition. A new headline theorem
must be added here when it becomes part of that exported proof surface. The
temporary statement skeletons are audited separately in `Audit/Statements.lean`
because their opaque relation names intentionally collide with the concrete
relations imported here.

The entries are deliberately repetitive at the root level: a change in the
transitive trust boundary of any one interface should produce a focused CI
failure.  Shared arrays below are only labels for exactly repeated sets.
-/

namespace Ix.Kernel.Verify.Audit.Completed

open Ix.Kernel.Verify.Audit

private def standard : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def standardWithoutChoice : Array Lean.Name :=
  #[``propext, ``Quot.sound]

private def standardWithoutQuot : Array Lean.Name :=
  #[``propext, ``Classical.choice]

private def propextOnly : Array Lean.Name := #[``propext]

/- The executable `AnnotatedPi` replay in the local named specification crosses
its verified wrappers for Lean's pointer-aware expression implementation.
Keep that nonlogical upstream footprint distinct from `standard`: these are
not ordinary logical axioms and must not become globally permitted. -/
private def annotatedPiUpstreamAxioms : Array Lean.Name := #[
  ``Ix.Theory.Named.ptrEqConstantInfo_eq,
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

/- Exact direct `sorryAx` frontier inherited from Ix.Theory.Named's executable
candidate-normalization proof.  Unlike the earlier closed-form fixtures,
`AnnotatedPi` exercises the verified implementation path far enough to reach
the currently declared projection/typechecker proof debt. -/
private def annotatedPiUpstreamDebt : Array Lean.Name := #[
  ``Ix.Theory.Named.VEnv.IsDefEqU.forallE_inv_stratified,
  ``Ix.Theory.Named.VEnv.IsDefEqU.sort_forallE_inv,
  ``Ix.Theory.Named.VEnv.IsDefEqU.sort_inv,
  ``Ix.Theory.Named.VEnv.IsDefEqU.weakN_iff,
  ``Ix.Theory.Named.VEnv.WF.registeredStructureHeadInversion,
  ``Ix.Theory.Named.TypeChecker.Inner.reduceRecursor.WF
]

/- `AliasFormer` reaches the same executable normalization boundary as
`AnnotatedPi`: the former unfolds a reducible family-result alias, while the
latter unfolds a constructor-domain annotation.  Keep separate aliases so
the audit will expose either fixture if their upstream footprints diverge. -/
private def aliasFormerUpstreamAxioms : Array Lean.Name :=
  annotatedPiUpstreamAxioms

private def aliasFormerUpstreamDebt : Array Lean.Name :=
  annotatedPiUpstreamDebt.push
    ``Ix.Theory.Named.InductiveReplayFixtures.aliasFormerAlignmentRun

/- `AliasRec` reaches the same executable normalization boundary while
unfolding a reducible wrapper around a recursive constructor field.  Keep its
allowances separately named so the exact-root audit detects any divergence. -/
private def aliasRecUpstreamAxioms : Array Lean.Name :=
  annotatedPiUpstreamAxioms

private def aliasRecUpstreamDebt : Array Lean.Name :=
  annotatedPiUpstreamDebt

private def expressionNative : Array Lean.Name := #[].push
  (nativeAxiom `Ix.Kernel.Expr
    `Ix.Kernel.KExpr.mkVar._native.native_decide.ax_1)

private def levelNative : Array Lean.Name := expressionNative.push
  (nativeAxiom `Ix.Kernel.Level
    `Ix.Kernel.KUniv.mkSucc._native.native_decide.ax_1)

private def occurrenceValidationNative : Array Lean.Name := #[].push
  (nativeAxiom `Ix.Kernel.Level
    `Ix.Kernel.KUniv.mkSucc._native.native_decide.ax_1)

private def specializationIdentityNative : Array Lean.Name :=
  occurrenceValidationNative.push
    (nativeAxiom `Ix.Kernel.Verify.Inductive.SpecializationIdentity
      `Ix.Kernel.SpecializationIdentityFixture.semanticUniverseEquality_does_not_collapse_specializationNative._native.native_decide.ax_1_1)

private def univOnlyNative : Array Lean.Name := #[
  nativeAxiom `Ix.Kernel.Level
    `Ix.Kernel.KUniv.mkSucc._native.native_decide.ax_1
]

private def nameDecideNative : Lean.Name :=
  nativeAxiom `Ix.Environment
    `Ix.Name.mkStr._native.native_decide.ax_1

private def nameNative : Array Lean.Name := levelNative.push nameDecideNative

private def expressionNameNative : Array Lean.Name :=
  expressionNative.push nameDecideNative

private def canonicalPrimitivesNative : Array Lean.Name :=
  #[].push nameDecideNative

private def contextNative : Array Lean.Name :=
  expressionNative

private def inferNative : Array Lean.Name :=
  levelNative

private def nameContextNative : Array Lean.Name :=
  nameNative

private def canonicalPrimitivesContextNative : Array Lean.Name :=
  canonicalPrimitivesNative

private def natAddNeSuccNative : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.NatFixture
    `Ix.Kernel.AmbientNat.natAdd_ne_natSucc._native.native_decide.ax_1_1

private def natAddNeBeqNative : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.NatFixture
    `Ix.Kernel.AmbientNat.natAdd_ne_natBeq._native.native_decide.ax_1_1

private def natAddNeBleNative : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.NatFixture
    `Ix.Kernel.AmbientNat.natAdd_ne_natBle._native.native_decide.ax_1_1

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
  (nativeAxiom `Ix.Kernel.Inductive
    `Ix.Kernel.RecM.canonicalAuxOrder._native.native_decide.ax_9)

/- Mutual-block fixtures use many small closed `native_decide` facts.  Build
their exact private names structurally so the audit stays reviewable while
still enumerating every generated axiom. -/
private def mutualNativeUserName (decl : String) (index : Nat) : Lean.Name :=
  Lean.Name.str
    (Lean.Name.str
      (Lean.Name.str
        (Lean.Name.str `Ix.Kernel.MutualTreeFixture decl)
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
  mutualNativeSeries `Ix.Kernel.Verify.Inductive.MutualFamilyAdmission decl count

private def mutualBlockFixtureNativeSeries (decl : String)
    (count : Nat) : Array Lean.Name :=
  mutualNativeSeries `Ix.Kernel.Verify.Inductive.MutualBlockFixture decl count

private def mutualRecursorAdmissionNativeSeries (decl : String)
    (count : Nat) : Array Lean.Name :=
  mutualNativeSeries `Ix.Kernel.Verify.Inductive.MutualRecursorAdmission decl count

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
  mutualNativeSingletons `Ix.Kernel.Verify.Inductive.MutualBlockFixture #[
    "familyAuxCompileSucceededNative",
    "familyBlockLoadedNative",
    "familyIngressSucceededNative",
    "recursorBlockLoadedNative",
    "recursorIngressSucceededNative"
  ] ++
  mutualNativeSingletons `Ix.Kernel.Verify.Inductive.MutualBlockValidation #[
    "familyKernelSucceededNative",
    "recursorKernelSucceededNative"
  ] ++
  mutualFamilyAdmissionNativeSeries "familyMemberShapeFactsNative" 19 ++
  mutualFamilyAdmissionNativeSeries "ownershipShapeFactsNative" 9 ++
  mutualNativeSingletons `Ix.Kernel.Verify.Inductive.MutualFamilyAdmission #[
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
  mutualNativeSingletons `Ix.Kernel.Verify.Inductive.MutualRecursorAdmission #[
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
  nativeAxiom `Ix.Kernel.Verify.Inductive.RecursivePiFixture name

private def recursivePiRecursorFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.RecursivePiRecursorFixture name

private def recursivePiAdmissionNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.RecursivePiAdmission name

private def annotatedPiCertificateNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AnnotatedPiCertificate name

private def annotatedPiCertificateBreadthNative : Array Lean.Name := #[
  annotatedPiCertificateNativeAxiom
    `Ix.Kernel.AnnotatedPiCertificateFixture.breadthNative._native.native_decide.ax_1_1
]

private def annotatedPiFixtureNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AnnotatedPiFixture name

private def annotatedPiRecursorFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AnnotatedPiRecursorFixture name

private def annotatedPiAdmissionNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AnnotatedPiAdmission name

private def aliasFormerCertificateNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AliasFormerCertificate name

private def aliasFormerCertificateBreadthNative : Array Lean.Name := #[
  aliasFormerCertificateNativeAxiom
    `Ix.Kernel.AliasFormerCertificateFixture.breadthNative._native.native_decide.ax_1_1
]

private def aliasFormerFixtureNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AliasFormerFixture name

private def aliasFormerPatternNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AliasFormerPattern name

private def aliasFormerRecursorFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AliasFormerRecursorFixture name

private def aliasFormerAdmissionNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AliasFormerAdmission name

private def aliasRecCertificateNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AliasRecCertificate name

private def aliasRecCertificateBreadthNative : Array Lean.Name := #[
  aliasRecCertificateNativeAxiom
    `Ix.Kernel.AliasRecCertificateFixture.breadthNative._native.native_decide.ax_1_1
]

private def aliasRecFixtureNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AliasRecFixture name

private def aliasRecRecursorFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AliasRecRecursorFixture name

private def aliasRecAdmissionNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.AliasRecAdmission name

/- Exact executable footprint of the family-result-normalizing
AliasFormer family/recursor transaction. -/
private def aliasFormerAtomicClosureNative : Array Lean.Name :=
  inductiveNative ++ aliasFormerCertificateBreadthNative ++ #[
  aliasFormerAdmissionNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  aliasFormerAdmissionNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorOwnerNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.entriesSizeNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.entriesUniqueNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.entryAtOneNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.entryAtZeroNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.entryIdsNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.familyEntryNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.familyShapeNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.memberKidsNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.mkEntryNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.mkShapeNative._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  aliasFormerFixtureNativeAxiom
    `Ix.Kernel.AliasFormerFixture.typeFamilyAliasIngressSucceededNative._native.native_decide.ax_1_1,
  aliasFormerPatternNativeAxiom
    `Ix.Kernel.AliasFormerPattern.generationCtorPairsNonempty._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_2,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.catalogMkNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.catalogMkNative._native.native_decide.ax_1_2,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.catalogMkNative._native.native_decide.ax_1_3,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.catalogTypeFamilyAliasNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.constructorCountNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.mkRuleBinderCoreNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.mkRuleFieldsNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.mkRuleRawNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.mkRuleScopedNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.mkRuleSizeBoundNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.mkSourceNameNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.mkTypeRawNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.nameOfMkNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.nameOfTypeFamilyAliasNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorEntryNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorEntrySizeNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorUniverseCountNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorShapeNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
  aliasFormerRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasFormerRecursorFixture.typeFamilyAliasTranslationsNative._native.native_decide.ax_1_1
]

/- Exact executable footprint of the recursive-field-normalizing `AliasRec`
family/recursor transaction. -/
private def aliasRecAtomicClosureNative : Array Lean.Name :=
  inductiveNative ++ aliasRecCertificateBreadthNative ++ #[
  aliasRecAdmissionNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  aliasRecAdmissionNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorOwnerNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.entriesSizeNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.entriesUniqueNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.entryAtOneNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.entryAtZeroNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.entryIdsNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.familyEntryNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.familyShapeNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.memberKidsNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.mkEntryNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.mkShapeNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.recAliasIngressSucceededNative._native.native_decide.ax_1_1,
  aliasRecFixtureNativeAxiom
    `Ix.Kernel.AliasRecFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_2,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.catalogMkNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.catalogMkNative._native.native_decide.ax_1_2,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.catalogMkNative._native.native_decide.ax_1_3,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.catalogRecAliasNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.constructorCountNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.mkRuleBinderCoreNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.mkRuleFieldsNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.mkRuleRawNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.mkRuleScopedNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.mkRuleSizeBoundNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.mkSourceNameNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.mkTypeRawNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.nameOfMkNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.nameOfRecAliasNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recAliasTranslationsNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorEntryNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorEntrySizeNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorUniverseCountNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorShapeNative._native.native_decide.ax_1_1,
  aliasRecRecursorFixtureNativeAxiom
    `Ix.Kernel.AliasRecRecursorFixture.recursorTypeRawNative._native.native_decide.ax_1_1
]

/- Exact executable footprint of the annotation-normalizing family/recursor
transaction, including its Theory breadth witness and physical outParam,
family, constructor, and recursor entries. -/
private def annotatedPiAtomicClosureNative : Array Lean.Name :=
  inductiveNative ++ annotatedPiCertificateBreadthNative ++ #[
  annotatedPiAdmissionNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  annotatedPiAdmissionNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorOwnerNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.entriesSizeNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.entriesUniqueNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.entryAtOneNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.entryAtZeroNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.entryIdsNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.familyEntryNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.familyShapeNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.memberKidsNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.mkEntryNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.mkShapeNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.outParamIngressSucceededNative._native.native_decide.ax_1_1,
  annotatedPiFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_2,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.catalogMkNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.catalogMkNative._native.native_decide.ax_1_2,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.catalogMkNative._native.native_decide.ax_1_3,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.catalogOutParamNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.constructorCountNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.mkRuleBinderCoreNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.mkRuleFieldsNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.mkRuleRawNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.mkRuleScopedNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.mkRuleSizeBoundNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.mkSourceNameNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.mkTypeRawNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.nameOfMkNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.nameOfOutParamNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.outParamTranslationsNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorEntryNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorEntrySizeNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorUniverseCountNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorShapeNative._native.native_decide.ax_1_1,
  annotatedPiRecursorFixtureNativeAxiom
    `Ix.Kernel.AnnotatedPiRecursorFixture.recursorTypeRawNative._native.native_decide.ax_1_1
]

/- Exact executable footprint of the recursive-Pi family/recursor transaction.
The list is deliberately independent from the broader IndexedVec fixture so
the `Acc` closure cannot silently acquire unrelated native assumptions. -/
private def recursivePiAtomicClosureNative : Array Lean.Name :=
  inductiveNative ++ #[
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.entriesSizeNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.entriesUniqueNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.entryAtOneNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.entryAtZeroNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.entryIdsNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.familyEntryNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.familyShapeNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.ingressSucceededNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.introEntryNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.introShapeNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.memberKidsNative._native.native_decide.ax_1_1,
  recursivePiFixtureNativeAxiom
    `Ix.Kernel.RecursivePiFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.catalogIntroNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.catalogIntroNative._native.native_decide.ax_1_2,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.constructorCountNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.introRuleBinderCoreNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.introRuleFieldsNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.introRuleRawNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.introRuleScopedNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.introRuleSizeBoundNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.introSourceNameNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.introTypeRawNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.nameOfIntroNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorEntryNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorEntrySizeNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorShapeNative._native.native_decide.ax_1_1,
  recursivePiRecursorFixtureNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
  recursivePiAdmissionNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  recursivePiAdmissionNativeAxiom
    `Ix.Kernel.RecursivePiRecursorFixture.recursorOwnerNative._native.native_decide.ax_1_1
]

private def enumerationFixtureNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.EnumerationFixture name

private def enumerationAcceptanceNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.EnumerationAcceptance name

private def indexedRecursiveFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedRecursiveFixture name

private def indexedRecursiveAcceptanceNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedRecursiveAcceptance name

private def eliminationBreadthNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.EliminationBreadthFixture name

private def smallEliminationAcceptanceNative : Array Lean.Name :=
  inductiveNative.push mutualInternDataValueNative ++ #[
    `Ix.Theory.Named.InductiveReplayFixtures.smallSourceAlignment06._native.native_decide.ax_1,
    `Ix.Theory.Named.InductiveReplayFixtures.smallSourceEliminationResult06_isOk._native.native_decide.ax_1_1,
    `Ix.Kernel.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_1,
    `Ix.Kernel.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_2,
    `Ix.Kernel.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_3,
    `Ix.Kernel.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_4,
    `Ix.Kernel.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_5,
    `Ix.Kernel.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_6,
    `Ix.Kernel.EliminationBreadthFixture.smallCompiledIdentity._native.native_decide.ax_1_7,
    `Ix.Kernel.EliminationBreadthFixture.smallComputeKMatches_eq._native.native_decide.ax_1_1,
    `Ix.Kernel.EliminationBreadthFixture.smallPreparationMatches_eq._native.native_decide.ax_1_1,
    `Ix.Kernel.EliminationBreadthFixture.smallRecursorShape._native.native_decide.ax_1_1,
    `Ix.Kernel.EliminationBreadthFixture.smallTheoryRecUvars._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.smallCompilerSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.smallExecutionKNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.smallExecutionModeNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.smallFamilyIngressSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.smallFamilyKernelSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.smallRecursorIngressSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.smallRecursorKernelSucceededNative._native.native_decide.ax_1_1
  ]

private def kTargetAcceptanceNative : Array Lean.Name :=
  inductiveNative.push mutualInternDataValueNative ++ #[
    `Ix.Theory.Named.InductiveReplayFixtures.eqAlignment06._native.native_decide.ax_1,
    `Ix.Theory.Named.InductiveReplayFixtures.eqEliminationResult06_isOk._native.native_decide.ax_1_1,
    `Ix.Kernel.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_1,
    `Ix.Kernel.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_2,
    `Ix.Kernel.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_3,
    `Ix.Kernel.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_4,
    `Ix.Kernel.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_5,
    `Ix.Kernel.EliminationBreadthFixture.eqCompiledIdentity._native.native_decide.ax_1_6,
    `Ix.Kernel.EliminationBreadthFixture.eqComputeKMatches_eq._native.native_decide.ax_1_1,
    `Ix.Kernel.EliminationBreadthFixture.eqPreparationMatches_eq._native.native_decide.ax_1_1,
    `Ix.Kernel.EliminationBreadthFixture.eqRecursorShape._native.native_decide.ax_1_1,
    `Ix.Kernel.EliminationBreadthFixture.eqTheoryRecUvars._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.eqCompilerSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.eqExecutionKNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.eqExecutionModeNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.eqFamilyIngressSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.eqFamilyKernelSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.eqRecursorIngressSucceededNative._native.native_decide.ax_1_1,
    eliminationBreadthNativeAxiom
      `Ix.Kernel.EliminationBreadthFixture.eqRecursorKernelSucceededNative._native.native_decide.ax_1_1
  ]

private def indexedRecursiveFixtureNativeNames : Array Lean.Name := #[
  `Ix.Kernel.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_2,
  `Ix.Kernel.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_3,
  `Ix.Kernel.IndexedRecursiveFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_2,
  `Ix.Kernel.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_3,
  `Ix.Kernel.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_4,
  `Ix.Kernel.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_5,
  `Ix.Kernel.IndexedRecursiveFixture.catalogNilNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.catalogNilNative._native.native_decide.ax_1_2,
  `Ix.Kernel.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  `Ix.Kernel.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  `Ix.Kernel.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_2,
  `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_3,
  `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_4,
  `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_5,
  `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_6,
  `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_7,
  `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_2,
  `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_3,
  `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_4,
  `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_5,
  `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_6,
  `Ix.Kernel.IndexedRecursiveFixture.consEntryNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.consSourceNameNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.consRuleBinderCoreNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.consRuleFieldsNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.consRuleRawNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.consRuleScopedNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.consRuleSizeBoundNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.consShapeNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.consTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.constructorCountNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyEntriesSizeNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyEntriesUniqueNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyEntryAtOneNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyEntryAtTwoNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyEntryAtZeroNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyEntryIdsNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyEntryNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyMemberKidsNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyShapeNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.generationCtorPairOne._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nameOfConsNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nameOfNatNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nameOfNilNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nameOfSuccNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nameOfZeroNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natConstructorCountNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natEntriesSizeNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natEntriesUniqueNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natEntryAtOneNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natEntryAtTwoNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natEntryAtZeroNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natEntryIdsNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natEntryNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natFamilyShapeNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natIngressSucceededNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natMemberKidsNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natSourceConstructorOne._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natSourceConstructorZero._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nilEntryNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nilSourceNameNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nilRuleBinderCoreNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nilRuleFieldsNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nilRuleRawNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nilRuleScopedNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nilRuleSizeBoundNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nilShapeNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.nilTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorEntryNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorShapeNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorUniverseCountNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.sourceConstructorOne._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.succEntryNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.succSourceNameNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.succShapeNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.succTypeRawNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.zeroEntryNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.zeroSourceNameNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.zeroShapeNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.zeroTypeRawNative._native.native_decide.ax_1_1
]

private def indexedRecursiveAcceptanceNativeNames : Array Lean.Name := #[
  `Ix.Kernel.IndexedRecursiveFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.malformedRecursorRejectedNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natKernelSucceededNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.natNotFamilyDirectOwnerNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  `Ix.Kernel.IndexedRecursiveFixture.recursorOwnerNative._native.native_decide.ax_1_1
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
      `Ix.Kernel.IndexedRecursiveFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeSizeBoundNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Kernel.Verify.Inductive.GeneratedRecursorTypeFixture
      `Ix.Kernel.IndexedRecursiveFixture.familyBuildTypeResultNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Kernel.Verify.Inductive.GeneratedRecursorTypeFixture
      `Ix.Kernel.IndexedRecursiveFixture.familyBuildTypeSucceededNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Kernel.Verify.Inductive.GeneratedRecursorTypeFixture
      `Ix.Kernel.IndexedRecursiveFixture.familyPreparationSucceededNative._native.native_decide.ax_1_1
  ]

private def generatedRecursorRuleFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.GeneratedRecursorRuleFixture name

/-- Exact native footprint of the complete IndexedVec peer-alignment and
`buildRuleRhs` run. -/
private def generatedRecursorRuleFixtureNative : Array Lean.Name :=
  inductiveNative ++ #[
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeSizeBoundNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.generationCtorPairZero._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.generationCtorPairOne._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.nilRuleBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.nilRuleFieldsNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.nilRuleRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.nilRuleScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.nilRuleSizeBoundNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.consRuleBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.consRuleFieldsNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.consRuleRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.consRuleScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.consRuleSizeBoundNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.familyBuiltRulesNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.familyCompletedRecursorTypeNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.familyRulePopulationSucceededNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.generationRuleCountNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorRulesLiteralNative._native.native_decide.ax_1_1
  ]

/- Exact native footprint of the transactional rule commit.  This is kept
separate from `generatedRecursorRuleFixtureNative`: the commit proof observes
the two intermediate array sizes, but no longer depends on the standalone
completed-type observation used by the builder fixture. -/
private def generatedRecursorCommitFixtureNative : Array Lean.Name :=
  inductiveNative ++ #[
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorTypeSizeBoundNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.generationCtorPairZero._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.generationCtorPairOne._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.nilRuleBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.nilRuleFieldsNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.nilRuleRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.nilRuleScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.nilRuleSizeBoundNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.consRuleBinderCoreNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.consRuleFieldsNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.consRuleRawNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.consRuleScopedNative._native.native_decide.ax_1_1,
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.consRuleSizeBoundNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.familyBuiltRulesNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.familyGeneratedSnapshotSizeNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.familyGeneratedWithRulesSizeNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.familyRulePopulationSucceededNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.generationRuleCountNative._native.native_decide.ax_1_1,
    generatedRecursorRuleFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorRulesLiteralNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Kernel.Verify.Inductive.GeneratedRecursorCommitFixture
      `Ix.Kernel.IndexedRecursiveFixture.familyRuleCommitSucceededNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Kernel.Verify.Inductive.GeneratedRecursorCommitFixture
      `Ix.Kernel.IndexedRecursiveFixture.familyGeneratedSnapshotTypeNative._native.native_decide.ax_1_1
  ]

private def generatedRecursorCheckerFixtureNative : Array Lean.Name :=
  generatedRecursorCommitFixtureNative ++ #[
    indexedRecursiveFixtureNativeAxiom
      `Ix.Kernel.IndexedRecursiveFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
    nativeAxiom `Ix.Kernel.Verify.Inductive.GeneratedRecursorCheckerFixture
      `Ix.Kernel.IndexedRecursiveFixture.familyCacheCheckSucceededNative._native.native_decide.ax_1_1
  ]

/- The additional native facts used to construct the concrete IndexedVec
semantic world.  They are disjoint from the checker execution footprint
above, so the concatenated canonical fixture manifest remains exact. -/
private def generatedRecursorCanonicalWorldNative : Array Lean.Name := #[
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natNotFamilyDirectOwnerNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogConsNative._native.native_decide.ax_1_3,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_3,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_4,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogNatNative._native.native_decide.ax_1_5,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogNilNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogNilNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_3,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_4,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_5,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_6,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogSuccNative._native.native_decide.ax_1_7,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_3,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_4,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_5,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogZeroNative._native.native_decide.ax_1_6,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.consEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.consShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.consSourceNameNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.consTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.constructorCountNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyEntriesSizeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyEntriesUniqueNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyEntryAtOneNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyEntryAtTwoNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyEntryAtZeroNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyEntryIdsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberKidsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.nameOfConsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.nameOfNatNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.nameOfNilNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.nameOfSuccNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.nameOfZeroNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natConstructorCountNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natEntriesSizeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natEntriesUniqueNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natEntryAtOneNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natEntryAtTwoNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natEntryAtZeroNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natEntryIdsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natFamilyShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natIngressSucceededNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natMemberKidsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natSourceConstructorOne._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natSourceConstructorZero._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.natTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.nilEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.nilShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.nilSourceNameNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.nilTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.sourceConstructorOne._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.succEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.succShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.succSourceNameNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.succTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.zeroEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.zeroShapeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.zeroSourceNameNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.zeroTypeRawNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.recursorShapeNative._native.native_decide.ax_1_1
]

private def generatedRecursorCanonicalFixtureNative : Array Lean.Name :=
  generatedRecursorCheckerFixtureNative ++
    generatedRecursorCanonicalWorldNative

private def generatedRecursorCommitFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.GeneratedRecursorCommitFixture name

private def generatedRecursorMemberFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.GeneratedRecursorMemberFixture name

private def generatedRecursorInitialInvariantNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom
    `Ix.Kernel.Verify.Inductive.GeneratedRecursorInitialInvariant name

/- Exact executable footprint of the complete concrete recursor-member
transaction.  The earlier commit and semantic-world manifests are reused
only where they are exact subsets.  The remaining entries pin the outer
member prelude, the finite initial cache invariant, and the semantic recursor
entry used by the oracle-free second admission. -/
private def generatedRecursorAtomicClosureNative : Array Lean.Name :=
  generatedRecursorCommitFixtureNative ++
    generatedRecursorCanonicalWorldNative ++ #[
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.recursorUniverseCountNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.recursorEntryNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  indexedRecursiveFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.recursorOwnerNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.consConcreteHeaderNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.familyConcreteHeaderNative._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyInstalledRecursorAtZeroMemberNative._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyInstalledRecursorTypeEqNative._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyInstalledConsRuleInternSupported._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyInstalledNilRuleInternSupported._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyInstalledRecursorInductiveAddress._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyInstalledRecursorRules._native.native_decide.ax_1_1,
  generatedRecursorCommitFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyInstalledRecursorTypeInternSupported._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberArityBoundNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberSingletonSizeNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInitialPrimitivesNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyCharOfNatAbsent._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberCheckSucceededNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberDirectMajorShapeNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInitialBlocksCoveredNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInitialClosedFieldsNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInitialConstsCoveredNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInitialEquivEntriesEmpty._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInitialEquivLabelsEmpty._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInitialEquivParentEmpty._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInitialExprKeysNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInitialRecursorLoaded._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInitialReferencesCovered._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInitialUnivKeysNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberMajorSkipRunNeutral._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberOwnerCacheMatchesNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberPopulationReferencesCovered._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberPreparationMatchesNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRecursorConcreteHeader._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberReferenceId_authorized._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberReferenceId_authorized._native.native_decide.ax_1_2,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberReferenceId_authorized._native.native_decide.ax_1_3,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberResolutionPrefixMatchesNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberResultLevelNonzero._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberResultSortShape._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRulePopulationCacheChecksNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRulePopulationExprKeysNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRulePopulationExtendsNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRulePopulationMatchesNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRulePopulationNoLazyNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRulePopulationSemanticChecksNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRulePopulationUnivKeysNative._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberSnapshotFamilyLoaded._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberSnapshotGeneratedCache._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyNatSuccLookup._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyNatZeroLookup._native.native_decide.ax_1_1,
  generatedRecursorMemberFixtureNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyNilConcreteHeader._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberBlockPeersClassifiedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberBlockResultKeysClassifiedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberConsInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberConsInnerResultLevel_raw._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberConsResultLevel_raw._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberConsTypeTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberDefEqCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberDefEqCheapCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberDefEqFailureCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberFamilyInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberFamilyReferenceTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberFamilyResultLevel_raw._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberFamilyTypeTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInferCensusNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberInferOnlyCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberIsPropCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberIsRecCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberNatBlockAccepted._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberNatBlockAccepted._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberNatInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberNatReferenceTranslation._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberNatReferenceWhnf._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberNatSuccStuckCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberNatTrusted._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberNatTypeTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberNilInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberNilTypeTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRecMajorsClassifiedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRecursorBlocksClassifiedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRecursorOwnersClassifiedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberRecursorPayloadsInternedNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberSuccInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberSuccReferenceTranslation._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberSuccTrusted._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberSuccTypeTranslation._native.native_decide.ax_1_2,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberTypedConstantSyntaxNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberUnfoldCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberWhnfCensusNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberWhnfCoreCensusNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberWhnfCoreCheapCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberWhnfNoDeltaCensusNative._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberWhnfNoDeltaCheapCacheEmpty._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberZeroInfoLookup._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberZeroReferenceTranslation._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberZeroTrusted._native.native_decide.ax_1_1,
  generatedRecursorInitialInvariantNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberZeroTypeTranslation._native.native_decide.ax_1_2
]

/-- Exact executable delta between the existing semantic recursor closure
and the stronger closure that also retains the analyzer's candidate producer
equation.  The latter adds only the two outer production block checks. -/
private def indexedProducerClosureNative : Array Lean.Name :=
  generatedRecursorAtomicClosureNative ++ #[
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  indexedRecursiveAcceptanceNativeAxiom
    `Ix.Kernel.IndexedRecursiveFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1
]

/-- Exact executable footprint of the production-linked IndexedVec
constructor-validation replay.  Keep this separate from the broader
end-to-end acceptance fixture so a new observation changes this root's audit. -/
private def indexedConstructorValidationNative : Array Lean.Name := #[
  nativeAxiom `Ix.Environment
    `Ix.Name.mkStr._native.native_decide.ax_1,
  nativeAxiom `Ix.Kernel.Expr
    `Ix.Kernel.KExpr.mkVar._native.native_decide.ax_1,
  nativeAxiom `Ix.Kernel.Inductive
    `Ix.Kernel.RecM.canonicalAuxOrder._native.native_decide.ax_9,
  nativeAxiom `Ix.Kernel.Level
    `Ix.Kernel.KUniv.mkSucc._native.native_decide.ax_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.consConcreteHeaderNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.familyAritySucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.familyClassificationMatchesNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.familyConcreteHeaderNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.familyDiscoveryMatchesNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.familyMemberLoadedNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.familyNilAfterConsLoadedNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.familyNilValidationSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.familyPeerAgreementSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedBlockValidation
    `Ix.Kernel.IndexedRecursiveFixture.familyResultLevelSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Kernel.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_2,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Kernel.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_3,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Kernel.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_4,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Kernel.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_5,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Kernel.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_6,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedCandidateSyntax
    `Ix.Kernel.IndexedRecursiveFixture.candidateBlockSyntaxNative._native.native_decide.ax_1_7,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorAfterParamShapeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorAlphaEnsureTypeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorConsumeAlphaNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorConsumeNatNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorConsumeTailNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorGetTypeAlphaNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorInstantiateHeadNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorInstantiateNNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorInstantiateTailNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorNatEnsureTypeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorNatUniverse._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorParamIsDefEqNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorParamUniverse._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorResultIsValidNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorTailEnsureTypeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedConstructorValidation
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecConstructorTypeShapeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedPositivityTransport
    `Ix.Kernel.IndexedRecursiveFixture.familyConsHeadDomainCandidateCheckNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedPositivityTransport
    `Ix.Kernel.IndexedRecursiveFixture.familyConsNatDomainCandidateCheckNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedPositivityTransport
    `Ix.Kernel.IndexedRecursiveFixture.familyConsTailDomainCandidateCheckNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedPositivityTransport
    `Ix.Kernel.IndexedRecursiveFixture.familyConsTailWhnfCandidateCheckNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedPositivityTransport
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecAlphaCandidateWhnfNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedPositivityTransport
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecAlphaHasNoIndOccTrusted._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedPositivityTransport
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecNatCandidateWhnfNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedPositivityTransport
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecNatHasNoIndOccTrusted._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedPositivityTransport
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecTailAppIsValidTrusted._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedPositivityTransport
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecTailCandidateWhnfNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedPositivityTransport
    `Ix.Kernel.IndexedRecursiveFixture.indexedVecTailHasIndOccTrusted._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsHeadDomainRootFreeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsHeadOpenSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsHeadTelescopeWhnfIsForallNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsNatDomainRootFreeNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsNatOpenSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsNatTelescopeWhnfIsForallNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsPositivityParametersSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsResultWhnfSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsResultWhnfTerminalNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsTailDomainMentionsRootNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsTailDomainSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsTailDomainWhnfNotForallNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsTailDomainWhnfSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsTailOpenSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsTailTelescopeWhnfIsForallNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsTailWhnfSpineActiveNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedProductionPositivity
    `Ix.Kernel.IndexedRecursiveFixture.familyConsTailWhnfSpineIsConstNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedRecursiveAcceptance
    `Ix.Kernel.IndexedRecursiveFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  nativeAxiom `Ix.Kernel.Verify.Inductive.IndexedRecursiveFixture
    `Ix.Kernel.IndexedRecursiveFixture.familyEntriesSizeNative._native.native_decide.ax_1_1
]

private def nestedRecursiveFixtureNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.NestedRecursiveFixture name

private def nestedRecursiveActionNative : Array Lean.Name :=
  nameContextNative ++ #[
    nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.boxInactiveNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.nestedMentionsRootNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.nestedSpineNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.nestedWhnfSucceededNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.positivitySucceededNative._native.native_decide.ax_1_1
  ]

private def nestedRecursiveProducedNative : Array Lean.Name :=
  nestedRecursiveActionNative ++ #[
    nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.boxConcreteHeaderMatchesNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.boxLookupConcreteNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.boxLookupSucceededNative._native.native_decide.ax_1_1
  ]

private def nestedRecursiveFreshNative : Array Lean.Name :=
  nestedRecursiveProducedNative.push
    (nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.positivityRequestAbsentNative._native.native_decide.ax_1_1)

private def nestedRecursiveReachabilityNative : Array Lean.Name :=
  nestedRecursiveFreshNative ++ #[
    nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.builtFlatShapeNative._native.native_decide.ax_1_1,
    nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.flatBuildSucceededNative._native.native_decide.ax_1_1
  ]

private def nestedCandidateSyntaxNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.NestedCandidateSyntax name

private def nestedPositivityTransportNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.NestedPositivityTransport name

private def nestedAuxiliaryPositivityNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.NestedAuxiliaryPositivity name

private def nestedConstructorValidationNativeAxiom
    (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.NestedConstructorValidation name

private def nestedCandidateRelationNative : Array Lean.Name := #[
  nestedCandidateSyntaxNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.leanAuxiliaryOccursNative._native.native_decide.ax_1_1,
  nestedCandidateSyntaxNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.leanAuxiliarySourceNative._native.native_decide.ax_1_1,
  nestedCandidateSyntaxNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.leanAuxiliaryTargetNative._native.native_decide.ax_1_1,
  nestedCandidateSyntaxNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.leanFlatNodeTypeNative._native.native_decide.ax_1_1,
  nestedCandidateSyntaxNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.nestedDomainCandidateCheckNative._native.native_decide.ax_1_1
]

private def nestedRecursiveReachabilityWithResultNative : Array Lean.Name :=
  nestedRecursiveReachabilityNative.push
    (nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.nestedWhnfResultNative._native.native_decide.ax_1_1)

private def nestedOuterTransportNative : Array Lean.Name :=
  nestedRecursiveReachabilityWithResultNative ++ nestedCandidateRelationNative ++ #[
    nestedPositivityTransportNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanAuxiliaryCandidateWhnfNative._native.native_decide.ax_1_1,
    nestedPositivityTransportNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.nestedDomainMentionsRootNative._native.native_decide.ax_1_1,
    nestedPositivityTransportNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.nestedExternalInactiveNative._native.native_decide.ax_1_1
  ]

private def nestedAuxiliaryCandidateTargetNative : Array Lean.Name :=
  nestedRecursiveReachabilityNative ++ nestedCandidateRelationNative

private def nestedAuxiliaryExecutionNative : Array Lean.Name := #[
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliaryDiscoverySucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliaryDomainWhnfNotForallNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliaryDomainWhnfResultNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliaryDomainWhnfSucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliaryFieldWhnfShapeNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliaryFieldWhnfSucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliaryInstantiationSucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliaryParameterArgsNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliaryStrippingSucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliarySubstitutionSucceededNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliaryTreeMentionsRootNative._native.native_decide.ax_1_1,
  nestedAuxiliaryPositivityNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.auxiliaryWrapLookupSucceededNative._native.native_decide.ax_1_1
]

private def nestedAuxiliaryProductionNative : Array Lean.Name :=
  nestedRecursiveFreshNative ++ nestedAuxiliaryExecutionNative

private def nestedAuxiliaryTransportNative : Array Lean.Name :=
  nameContextNative ++ #[
    nestedAuxiliaryPositivityNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.auxiliaryDomainWhnfResultNative._native.native_decide.ax_1_1,
    nestedAuxiliaryPositivityNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.auxiliaryDomainWhnfSucceededNative._native.native_decide.ax_1_1,
    nestedAuxiliaryPositivityNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.auxiliaryTreeMentionsRootNative._native.native_decide.ax_1_1,
    nestedAuxiliaryPositivityNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanTreeCandidateWhnfNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanTreeOccursNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanTreeTargetNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.treeCandidateCheckNative._native.native_decide.ax_1_1
  ]

private def nestedAuxiliaryConstructorNative : Array Lean.Name :=
  nestedAuxiliaryProductionNative ++ #[
    nestedAuxiliaryPositivityNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanTreeCandidateWhnfNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanTreeOccursNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanTreeTargetNative._native.native_decide.ax_1_1,
    nestedCandidateSyntaxNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.treeCandidateCheckNative._native.native_decide.ax_1_1
  ]

private def nestedNodeConstructorValidationNative : Array Lean.Name :=
  nestedOuterTransportNative ++ #[
    nestedConstructorValidationNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.consumeLeanAuxiliaryNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.instantiateLeanTreeNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanAuxiliaryEnsureTypeNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanFlatFieldUniverse._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanTreeTerminalNative._native.native_decide.ax_1_1
  ]

private def nestedWrapConstructorValidationNative : Array Lean.Name :=
  nestedAuxiliaryConstructorNative ++ #[
    nestedCandidateSyntaxNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanFlatWrapTypeNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.consumeLeanTreeNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.instantiateLeanAuxiliaryNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanAuxiliaryTerminalNative._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanFlatFieldUniverse._native.native_decide.ax_1_1,
    nestedConstructorValidationNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.leanTreeEnsureTypeNative._native.native_decide.ax_1_1
  ]

private def nestedTreeCandidateSyntaxNative : Array Lean.Name :=
  expressionNative.push
    (nestedCandidateSyntaxNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.treeCandidateCheckNative._native.native_decide.ax_1_1)

/- The nested semantic transaction has two independently executable halves:
the Ix.Theory.Named source/restoration proof and Ix's physical catalog/checker
join.  Keep their native footprints explicit so the headline audit cannot
silently acquire oracle materialization or pending assumptions. -/
private def nativeUnion (left right : Array Lean.Name) : Array Lean.Name :=
  right.foldl (fun names name =>
    if names.contains name then names else names.push name) left

private def nestedSemanticBoxNative : Array Lean.Name := #[
  `Ix.Kernel.NestedRecursiveFixture.semanticBoxAfter_isSome._native.native_decide.ax_1_1,
  `Ix.Kernel.NestedRecursiveFixture.semanticBoxChecked._native.native_decide.ax_1,
  `Ix.Kernel.NestedRecursiveFixture.semanticBoxGeneration._native.native_decide.ax_1,
  `Ix.Kernel.NestedRecursiveFixture.semanticBoxShape._native.native_decide.ax_1_1,
  `Ix.Kernel.NestedRecursiveFixture.semanticBoxShape._native.native_decide.ax_1_2,
  `Ix.Kernel.NestedRecursiveFixture.semanticBoxShape._native.native_decide.ax_1_3,
  `Ix.Kernel.NestedRecursiveFixture.semanticBoxShape._native.native_decide.ax_1_4,
  `Ix.Kernel.NestedRecursiveFixture.semanticBoxShape._native.native_decide.ax_1_5
]

private def nestedSemanticWFNative : Array Lean.Name :=
  nestedSemanticBoxNative ++ #[
    `Ix.Kernel.NestedRecursiveFixture.semanticTreeNested_isSome._native.native_decide.ax_1_1,
    `Ix.Kernel.NestedRecursiveFixture.semanticTreeRecursors_eq._native.native_decide.ax_1_1,
    `Ix.Kernel.NestedRecursiveFixture.semanticTreeRules_eq._native.native_decide.ax_1_1
  ]

private def nestedSemanticCertificateNative : Array Lean.Name :=
  nestedSemanticWFNative.push
    `Ix.Kernel.NestedRecursiveFixture.semanticTreeAfter_isSome._native.native_decide.ax_1_1

private def nestedSemanticFactsNative : Array Lean.Name :=
  nestedSemanticCertificateNative ++ #[
    `Ix.Kernel.NestedRecursiveFixture.semanticTreeNodeName._native.native_decide.ax_1_1,
    `Ix.Kernel.NestedRecursiveFixture.semanticTreeRestoredClean._native.native_decide.ax_1_1
  ]

private def nestedSemanticAdmissionNative : Array Lean.Name :=
  nestedSemanticCertificateNative ++ #[
    `Ix.Kernel.NestedRecursiveFixture.semanticTreeNodeName._native.native_decide.ax_1_1,
    `Ix.Kernel.NestedRecursiveFixture.semanticTreeSourceInventory._native.native_decide.ax_1_1,
    `Ix.Kernel.NestedRecursiveFixture.semanticTreeSourceInventory._native.native_decide.ax_1_2
  ]

private def nestedAdmissionNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Inductive.NestedAdmission name

private def nestedAdmissionPublicNative : Array Lean.Name := #[
  `Ix.Kernel.NestedRecursiveFixture.nestedCatalog_node._native.native_decide.ax_1_1,
  `Ix.Kernel.NestedRecursiveFixture.nestedCatalog_node._native.native_decide.ax_1_2,
  `Ix.Kernel.NestedRecursiveFixture.nestedCatalog_tree._native.native_decide.ax_1_1,
  `Ix.Kernel.NestedRecursiveFixture.nestedNameOf_node._native.native_decide.ax_1_1,
  `Ix.Kernel.NestedRecursiveFixture.nestedNameOf_node._native.native_decide.ax_1_2,
  `Ix.Kernel.NestedRecursiveFixture.nestedNameOf_node._native.native_decide.ax_1_3,
  `Ix.Kernel.NestedRecursiveFixture.nestedNameOf_node._native.native_decide.ax_1_4,
  `Ix.Kernel.NestedRecursiveFixture.nestedNameOf_tree._native.native_decide.ax_1_1,
  `Ix.Kernel.NestedRecursiveFixture.nestedNameOf_tree._native.native_decide.ax_1_2,
  `Ix.Kernel.NestedRecursiveFixture.nestedNameOf_tree._native.native_decide.ax_1_3
]

private def nestedAdmissionPrivateNative : Array Lean.Name := #[
  nestedAdmissionNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.nestedFamilyBlockLoadedNative._native.native_decide.ax_1_1,
  nestedAdmissionNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.nestedMemberShapeFactsNative._native.native_decide.ax_1_1,
  nestedAdmissionNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.nestedMemberShapeFactsNative._native.native_decide.ax_1_2,
  nestedAdmissionNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.nestedMemberShapeFactsNative._native.native_decide.ax_1_3,
  nestedAdmissionNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.nestedMemberShapeFactsNative._native.native_decide.ax_1_4,
  nestedAdmissionNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.nestedNodeDirectConstructor._native.native_decide.ax_1_1,
  nestedAdmissionNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.nestedNodeTypeRawNative._native.native_decide.ax_1_1,
  nestedAdmissionNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.nestedTreeDirectOwner._native.native_decide.ax_1_1,
  nestedAdmissionNativeAxiom
    `Ix.Kernel.NestedRecursiveFixture.nestedTreeTypeRawNative._native.native_decide.ax_1_1
]

private def nestedFamilyCertificateNative : Array Lean.Name :=
  nativeUnion
    (nativeUnion nameNative nestedSemanticAdmissionNative)
    (nestedAdmissionPublicNative ++ nestedAdmissionPrivateNative)

private def nestedFamilyKernelNative : Array Lean.Name :=
  inductiveNative.push
    (nestedAdmissionNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.nestedFamilyKernelSucceededNative._native.native_decide.ax_1_1)

private def nestedSemanticTransactionClosureNative : Array Lean.Name :=
  let withSemantics := nativeUnion nestedFamilyCertificateNative
    nestedSemanticFactsNative
  let withKernel := nativeUnion withSemantics nestedFamilyKernelNative
  let withNode := nativeUnion withKernel nestedNodeConstructorValidationNative
  let withWrap := nativeUnion withNode nestedWrapConstructorValidationNative
  let withBoxIngress := withWrap.push
    (nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.boxIngressSucceededNative._native.native_decide.ax_1_1)
  withBoxIngress.push
    (nestedRecursiveFixtureNativeAxiom
      `Ix.Kernel.NestedRecursiveFixture.treeIngressSucceededNative._native.native_decide.ax_1_1)

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
        (Lean.Name.str `Ix.Kernel.NestedRecursiveFixture decl)
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
    `Ix.Kernel.Verify.Inductive.NestedRecursorFixture decl count

private def nestedRecursorPatternNativeSeries (decl : String)
    (count : Nat := 1) : Array Lean.Name :=
  nestedRecursorNativeSeries
    `Ix.Kernel.Verify.Inductive.NestedRecursorPattern decl count

private def nestedRecursorSoundnessNativeSeries (decl : String)
    (count : Nat := 1) : Array Lean.Name :=
  nestedRecursorNativeSeries
    `Ix.Kernel.Verify.Inductive.NestedRecursorSoundness decl count

private def nestedRecursorAdmissionNativeSeries (decl : String)
    (count : Nat := 1) : Array Lean.Name :=
  nestedRecursorNativeSeries
    `Ix.Kernel.Verify.Inductive.NestedRecursorAdmission decl count

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
  nestedRecursorNativeSeries `Ix.Kernel.Verify.Inductive.NestedAdmission
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
    #[nativeAxiom `Ix.Kernel.Inductive
      `Ix.Kernel.RecM.canonicalAuxOrder._native.native_decide.ax_9]

private def nestedRecursorAtomicClosureNative : Array Lean.Name :=
  nativeUnion nestedRecursorAtomicAdmissionNative
    nestedRecursorOperationalNative

private def nestedRestoredPatternUpstreamDebt : Array Lean.Name := #[
  ``Ix.Theory.Named.VEnv.IsDefEqU.forallE_inv_stratified,
  ``Ix.Theory.Named.VEnv.IsDefEqU.sort_inv
]

private def booleanAcceptanceNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Driver.BooleanAcceptance name

private def serializedBooleanNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Ingress.SerializedBoolean name

private def literalBlobsNativeAxiom (name : Lean.Name) : Lean.Name :=
  nativeAxiom `Ix.Kernel.Verify.Ingress.LiteralBlobs name

/- The explicit Boolean one-family admission consumes the finite catalog,
ingress, generation, rule, and pattern facts below.  Checker executions are
kept out of this shared semantic slice so the one-family root cannot inherit
them merely because the larger end-to-end witness also records those runs. -/
private def booleanSemanticFixtureNative : Array Lean.Name := #[
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_3,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.enumerationShapeNative._native.native_decide.ax_1_6,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.enumerationShapeNative._native.native_decide.ax_1_7,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseRuleBinderCoreNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseRuleFieldsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseRuleRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseRuleScopedNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseRuleSizeBoundNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyConstructorCountNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntriesUniqueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryAtOneNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryAtTwoNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryAtZeroNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryIdsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyMemberKidsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.generationCtorPairOne._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.nameOfFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.nameOfTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.sourceConstructorOne._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueRuleBinderCoreNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueRuleFieldsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueRuleRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueRuleScopedNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueRuleSizeBoundNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_2
]

private def booleanSemanticAdmissionNative : Array Lean.Name :=
    nameNative ++ #[
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorOwnerNative._native.native_decide.ax_1_1
] ++ booleanSemanticFixtureNative

/- The concrete Boolean end-to-end witness additionally evaluates the real
block loads, checker branches, content-address context, and canonical
auxiliary ordering.  Keep every fixture-local native proof explicit rather
than treating the witness as one opaque executable assumption. -/
private def booleanEnumerationNative : Array Lean.Name :=
    inductiveNative ++ #[
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyBodySucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyClassificationSucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyKernelSucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorBlockLoadedAfterFamilyNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorBodySucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorClassificationSucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorKernelSucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorOwnerNative._native.native_decide.ax_1_1
] ++ booleanSemanticFixtureNative

/- The supported fragment family-body bridge consumes only the family-side slice of the
full end-to-end Boolean witness.  Keep this narrower than
`booleanEnumerationNative`: in particular it must not inherit the executable
recursor run, kernel-run, generated-rule, or recursor-ingress facts merely
because the larger singleton certification witness uses them. -/
private def booleanFamilyBodyNative : Array Lean.Name := inductiveNative ++ #[
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyBodySucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyClassificationSucceededNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_3,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyConstructorCountNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntriesUniqueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryAtOneNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryAtTwoNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryAtZeroNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryIdsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyMemberKidsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.nameOfFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.nameOfTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.sourceConstructorOne._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_2
]

/-- Exact evaluator boundary of the Boolean whole-driver witness.
This is intentionally narrower than `booleanEnumerationNative`: the release
root consumes the generated Theory certificate and exact physical links, but
does not inherit the earlier standalone body/kernel executions as semantic
authority for the serial run. -/
def booleanDriverNative : Array Lean.Name := inductiveNative ++ #[
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.buildAnonWorkNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.checkEnvAnonNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseProjectionEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseProjectionEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseProjectionEntry._native.native_decide.ax_1_3,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyBlockEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyBlockEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyBlockEntry._native.native_decide.ax_1_3,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyProjectionEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyProjectionEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyProjectionEntry._native.native_decide.ax_1_3,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyTargetsNonemptyNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorBlockEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorBlockEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorBlockEntry._native.native_decide.ax_1_3,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorProjectionEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorProjectionEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorProjectionEntry._native.native_decide.ax_1_3,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorTargetsNonemptyNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.sourceAddressesNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.sourceAddressesNodupNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.sourceKeysNative._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueProjectionEntry._native.native_decide.ax_1_1,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueProjectionEntry._native.native_decide.ax_1_2,
  booleanAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueProjectionEntry._native.native_decide.ax_1_3,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyDirectOwnerNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorBlockLoadedNative._native.native_decide.ax_1_1,
  enumerationAcceptanceNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorOwnerNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogFalseNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_3,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogRecursorNative._native.native_decide.ax_1_4,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.catalogTrueNative._native.native_decide.ax_1_3,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.enumerationShapeNative._native.native_decide.ax_1_6,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.enumerationShapeNative._native.native_decide.ax_1_7,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseRuleBinderCoreNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseRuleFieldsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseRuleRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseRuleScopedNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseRuleSizeBoundNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.falseTypeNative._native.native_decide.ax_1_2,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyConstructorCountNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntriesUniqueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryAtOneNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryAtTwoNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryAtZeroNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryIdsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyIngressSucceededNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyMemberKidsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.familyTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.generationCtorPairOne._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.generationCtorPairZero._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.nameOfFalseNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.nameOfFamilyNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.nameOfRecursorNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.nameOfTrueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorEntriesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorEntriesUniqueNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorEntryIdsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorIngressSucceededNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorMemberKidsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorRulesSizeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.recursorTypeRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.sourceConstructorOne._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.sourceConstructorZero._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueEntryNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueRuleBinderCoreNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueRuleFieldsNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueRuleRawNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueRuleScopedNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueRuleSizeBoundNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueShapeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueSourceTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_1,
  enumerationFixtureNativeAxiom
    `Ix.Kernel.BooleanEnumerationFixture.trueTypeNative._native.native_decide.ax_1_2
]

/-- Exact evaluator boundary of the serialized Boolean certificate. Each
closed computation is named so changes in the byte, eager, lazy, dependency,
or driver slices are visible independently in the trust manifest. -/
def serializedBooleanNative : Array Lean.Name := booleanDriverNative ++ #[
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.blobKeysNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.buildAnonWorkNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.checkEnvAnonNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.decodeSucceededNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.eagerBlockKeysClassifiedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.eagerFalseNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.eagerFamilyBlockNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.eagerFamilyNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.eagerKeysClassifiedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.eagerRecursorBlockNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.eagerRecursorNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.eagerSucceededNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.eagerTrueNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.eagerWorkNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.encodeSucceededNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.falseProjectionEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.falseProjectionEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.falseProjectionHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.falseProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.familyBlockEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.familyBlockEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.familyBlockHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.familyBlockLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.familyProjectionEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.familyProjectionEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.familyProjectionHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.familyProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.familyTargetsNonemptyNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFalseLoadedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFamilyBlockKeysNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFamilyBlockNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFamilyKeysClassifiedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFamilyLoadedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFamilySucceededNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFinalBlockKeysClassifiedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFinalFalseNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFinalFamilyBlockNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFinalFamilyNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFinalRecursorBlockNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFinalRecursorNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyFinalTrueNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyRecursorKeysClassifiedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyRecursorSucceededNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.lazyTrueLoadedNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.originalFalseProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.originalFamilyBlockLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.originalFamilyProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.originalRecursorBlockLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.originalRecursorProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.originalTrueProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.recursorBlockEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.recursorBlockEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.recursorBlockHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.recursorBlockLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.recursorProjectionEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.recursorProjectionEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.recursorProjectionHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.recursorProjectionLookupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.recursorTargetsNonemptyNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.sourceAddressesNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.sourceAddressesNodupNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.sourceKeysNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.trueProjectionEntry._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.trueProjectionEntry._native.native_decide.ax_1_2,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.trueProjectionHashNative._native.native_decide.ax_1_1,
  serializedBooleanNativeAxiom
    `Ix.Kernel.BooleanSerialized.trueProjectionLookupNative._native.native_decide.ax_1_1
]

/- Exact evaluator boundary of the non-vacuous literal/blob serialization fixture. -/
private def literalRoundTripNative : Array Lean.Name := nameNative ++ #[
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.blobKeysClassifiedNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.decodeSucceededNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.encodeSucceededNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.natBlobHashNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.natBlobLookupNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.natEntry._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.natEntry._native.native_decide.ax_1_2,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.natHashNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.natLoadedNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.natLookupNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.natSucceededNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.sourceAddressesClassifiedNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.sourceAddressesNodupNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.sourceKeysClassifiedNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.stringBlobHashNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.stringBlobLookupNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.stringEntry._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.stringEntry._native.native_decide.ax_1_2,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.stringHashNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.stringLoadedNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.stringLookupNative._native.native_decide.ax_1_1,
  literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.stringSucceededNative._native.native_decide.ax_1_1
]

private def malformedConstantNative : Array Lean.Name :=
  canonicalPrimitivesNative.push <| literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.malformedConstantRejectedNative._native.native_decide.ax_1_1

private def malformedBlobNative : Array Lean.Name :=
  canonicalPrimitivesNative.push <| literalBlobsNativeAxiom
    `Ix.Kernel.SerializedLiteralBlobs.malformedBlobRejectedNative._native.native_decide.ax_1_1

/- Direct upstream `sorryAx` origins.  Listing the declarations, rather than
merely allowing `sorryAx`, makes upstream debt movement visible in review.
The certificate-bearing Ix.Theory.Named pin discharges the former `VInductDecl.WF`,
`VEnv.addInduct`, `VEnv.addInduct_WF`, and `TrProj` origins. -/
private def forallEInv : Lean.Name :=
  ``Ix.Theory.Named.VEnv.IsDefEqU.forallE_inv_stratified
private def sortInv : Lean.Name := ``Ix.Theory.Named.VEnv.IsDefEqU.sort_inv

private def typingDebt : Array Lean.Name :=
  #[forallEInv, sortInv]

/- P0's concrete projection adapter consumes Ix.Theory.Named's structural laws.
Its uniqueness law reaches the named registered-structure inversion theorem;
the context-defeq law also crosses Ix.Theory.Named's current unique-typing boundary
and therefore inherits the two L2 inversion origins.  Keep this exact rather
than allowing the remainder of the executable inductive-fixture debt. -/
private def projectionDebt : Array Lean.Name :=
  typingDebt.push ``Ix.Theory.Named.VEnv.WF.registeredStructureHeadInversion

/- The empty legacy whole-`KEnv` inductive path is forbidden from every catalog lookup
consumer root.  Keeping this list in the executable audit prevents an
innocent-looking helper from reintroducing the old `nomatch` dependency. -/
private def legacyWholeEnv : Array Lean.Name := #[
  ``Ix.Kernel.AddKInduct,
  ``Ix.Kernel.AddKInduct.to_addInduct,
  ``Ix.Kernel.TrKEnv',
  ``Ix.Kernel.TrKEnv
]

/- The generation adapter is a Theory-only certificate consumer. These
checker/catalog/pattern declarations must not enter its dependency graph. -/
private def certificateAdapterForbidden : Array Lean.Name := #[
  ``Ix.Kernel.Catalog,
  ``Ix.Kernel.RawInductiveConstRel,
  ``Ix.Kernel.RawRecursorRuleRel,
  ``Ix.Kernel.RawRecursorRulePatternRel,
  ``Ix.Kernel.InductiveOracle,
  ``Ix.Theory.Named.TrProj
]

/- `AnnotatedPi`'s upstream certificate is produced by Ix.Theory.Named's executable
normalization pipeline, so it cannot satisfy the earlier closed-form
certificate quarantine against `TrProj`.  It must still remain independent of
all Ix catalog, checker-pattern, and oracle authority. -/
private def annotatedPiCertificateForbidden : Array Lean.Name := #[
  ``Ix.Kernel.Catalog,
  ``Ix.Kernel.RawInductiveConstRel,
  ``Ix.Kernel.RawRecursorRuleRel,
  ``Ix.Kernel.RawRecursorRulePatternRel,
  ``Ix.Kernel.InductiveOracle
]

/- The pre-TrustedBody delta route admitted successful unfolding through a broad
reflection oracle and arbitrary cache-write authority.  The final WHNF closure
must use exact trusted declaration certificates instead. -/
private def legacyDeltaAuthority : Array Lean.Name := #[
  ``Ix.Kernel.UnfoldCacheWriteOracle,
  ``Ix.Kernel.DeltaUnfoldReflection,
  ``Ix.Kernel.RecM.DeltaUnfoldContext,
  ``Ix.Kernel.RecM.FullWhnfStepContext.ofDelta
]

private def k1ForbiddenDependencies : Array Lean.Name :=
  legacyWholeEnv ++ legacyDeltaAuthority

/- Bounded recursive-method and checker roots must not silently regain the
all-depth, single-support closure interface whose finite-sort obstruction is
proved below.  The legacy declarations remain audited as compatibility
artifacts while consumers migrate. -/
private def legacyAllDepthKnot : Array Lean.Name := #[
  ``Ix.Kernel.RecursiveMethodClosureContext,
  ``Ix.Kernel.RecursiveMethodClosureContext.closedAt,
  ``Ix.Kernel.RecursiveMethodClosureContext.methodsN,
  ``Ix.Kernel.RecursiveMethodClosureContext.fullInferenceContext,
  ``Ix.Kernel.RecursiveMethodClosureContext.next_fullInferenceWFAt,
  ``Ix.Kernel.RecursiveMethodClosureContext.methodsN_fullInferenceWFAt,
  ``Ix.Kernel.RecursiveMethodClosureContext.publicInfer_full_wf
]

private def boundedKnotForbiddenDependencies : Array Lean.Name :=
  k1ForbiddenDependencies ++ legacyAllDepthKnot

/- Occurrence-validation roots must be derived from the production run,
not from the ambient semantic inductive oracle retained by singleton certification. -/
private def occurrenceValidationForbiddenDependencies : Array Lean.Name :=
  boundedKnotForbiddenDependencies.push ``Ix.Kernel.InductiveOracle

/- Existing semantic admission returns the shared `TrustedCatalogLog`, whose
inductive declaration necessarily mentions its legacy ambient constructor.
Constructor-insensitive dependency traversal therefore cannot forbid the
`InductiveOracle` type itself here.  Instead, quarantine every operation that
materializes or admits an oracle-selected future world. -/
private def oracleWorldMaterialization : Array Lean.Name := #[
    ``Ix.Kernel.VerifyWorld.admitOracle,
    ``Ix.Kernel.VerifyWorld.le_admitOracle,
    ``Ix.Kernel.OracleBlockCertificate.admit,
    ``Ix.Kernel.OracleBlockCertificate.admitState,
    ``Ix.Kernel.RecM.certifyOracleBackedBlock,
    ``Ix.Kernel.RecM.certifyOracleBackedAdmittedBlock,
    ``Ix.Kernel.SingletonFamilyCatalogLink.oracle,
    ``Ix.Kernel.SingletonRecursorCatalogLink.oracle,
    ``Ix.Kernel.InductiveOracle.reindex,
    ``Ix.Kernel.InductiveOracle.restageMissing,
    ``Ix.Kernel.IndexedRecursivePattern.oracle,
    ``Ix.Kernel.IndexedRecursiveFixture.recursorBlockOracle,
    ``Ix.Kernel.IndexedRecursiveFixture.recursorAtomicAdmission
]

private def existingSemanticBlockForbiddenDependencies : Array Lean.Name :=
  boundedKnotForbiddenDependencies ++ oracleWorldMaterialization

/- Scoped method proofs keep the global suffix model as a compatibility surface only. The
finite positive-fuel construction must neither manufacture that model nor
reach the older public adapters that consume it. -/
private def legacyGlobalSuffix : Array Lean.Name := #[
  ``Ix.Kernel.KernelSuffixModel,
  ``Ix.Kernel.ScopedKernelSuffixModel.toKernelSuffixModel,
  ``Ix.Kernel.PropositionClassifierContext,
  ``Ix.Kernel.RecursiveMethodRunContext,
  ``Ix.Kernel.TcM.whnf.wf_legacy,
  ``Ix.Kernel.TcM.infer.wf_legacy,
  ``Ix.Kernel.TcM.isDefEq.wf_legacy,
  ``Ix.Kernel.TcM.checkConst.wf_legacy
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
  { root := ``Ix.Kernel.univEq_sound, standardAxioms := standard },
  { root := ``Ix.Kernel.univGeq_sound, standardAxioms := standard },

  -- Memoized expression walkers against their pure specifications.
  { root := ``Ix.Kernel.lift_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.subst_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.simulSubst_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.instantiateRev_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  -- There is not yet an API-level `abstractFVars_spec`; protect the current
  -- walker master until that final wrapper replaces it.
  { root := ``Ix.Kernel.abstractFVarsCached_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.TcM.instantiateUnivParams_wf,
    standardAxioms := standard, nativeAxioms := levelNative },

  -- Finite run support and generated-term resource bounds. Universe
  -- instantiation can rebuild sorts/constants and therefore reaches the now
  -- total expression serializer's standard `UInt8` quotient implementation.
  { root := ``Ix.Kernel.KExpr.LiftReach.finite,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.KExpr.SubstReach.finite,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.KExpr.InstUnivReach.finite,
    standardAxioms := standard,
    nativeAxioms := levelNative },
  { root := ``Ix.Kernel.WalkerRequest.reach_finite,
    standardAxioms := standard,
    nativeAxioms := levelNative },
  { root := ``Ix.Kernel.InternTable.exprSupport_finite,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RunSupport.collisionFree_of_le,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.RunSupport.singleton_collisionFree,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.WalkerRequest.Bounds.lift_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.WalkerRequest.Bounds.subst_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.CheckConstSupport.initial_support,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.CheckConstSupport.lift,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.CheckConstSupport.subst,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.CheckConstSupport.instUniv,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.CheckConstSupport.mono,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.CheckConstSupport.scope,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.ResourceBounds.mono,
    standardAxioms := standard,
    nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.AmbientNat.checkSupport,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.resourceBounds,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.supportAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Execution-indexed support covers the formalized walker/direct-intern families and
  -- ties the exact finite request list to an actual TcM computation. The
  -- simultaneous/reverse instantiation specs can likewise rebuild serialized
  -- expressions and inherit the same standard quotient footprint.
  { root := ``Ix.Kernel.KExpr.SimulSubstReach.finite,
    standardAxioms := standard,
    nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.KExpr.InstRevReach.finite,
    standardAxioms := standard,
    nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.KExpr.AbstractReach.finite,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.WalkerRequest.univReach_finite,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.InternTable.univSupport_finite,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RunSupport.pair_collisionFree,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.WalkerRequest.Bounds.simulSubst_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.WalkerRequest.Bounds.instRev_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.WalkerRequest.Bounds.abstractFVars_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.abstractFVars_eq,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.InternPreservesUnivs.pure,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.InternPreservesUnivs.runWalk,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.WalkPreservesUnivs.pure,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.WalkPreservesUnivs.bind,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.WalkPreservesUnivs.scratchGet,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.WalkPreservesUnivs.scratchInsert,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.WalkPreservesUnivs.liftIntern,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.WalkPreservesUnivs.internExpr,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.lift_preservesUnivs,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.subst_preservesUnivs,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.simulSubst_preservesUnivs,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.instantiateRev_preservesUnivs,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.abstractFVars_preservesUnivs,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.WalkerRequest.Bounds.abstractFVarsCached_result,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.CheckConstSupport.initial_univ_support,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.CheckConstSupport.internExpr,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.CheckConstSupport.internUniv,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.CheckConstSupport.simulSubst,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.CheckConstSupport.instRev,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.CheckConstSupport.abstractFVars,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.ExecutionRequests.bind,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.ExecutionRequests.tryCatch,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.ExecutionRequests.runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.ExecutionRequests.isolateCheckErrors,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.ExecutionRequests.modify,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.ExecutionRequests.weaken,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.ExecutionRequests.of_eq,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.ExecutionRequests.intern_eq_of_nil,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RunAssumptions.initial,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.requestBounds,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RunAssumptions.internExpr_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.internUniv_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunSupport.CoversIntern.of_expr_univs,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RunAssumptions.lift_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.subst_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.simulSubst_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.instRev_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.abstractFVarsCached_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.abstractFVars_spec,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.instantiateUnivParams_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.runIntern_supported_wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RunAssumptions.lift_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.subst_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.simulSubst_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.instRev_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.abstractFVars_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.instUniv_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.AmbientNat.supportExecution,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.runAssumptions,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Expression translation, typing, uniqueness, and defeq bridges.
  { root := ``Ix.Kernel.TrKExprS.instL,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.TrKExprS.inst,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.TrKExprS.inst_let,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.TrKExprS.inst_let_lbr,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.TrKExprS.wf, standardAxioms := standard },
  { root := ``Ix.Kernel.TrKExpr.wf, standardAxioms := standard },
  { root := ``Ix.Kernel.TrKExprS.uniq,
    standardAxioms := standard, sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.TrKExprS.defeqDFC,
    standardAxioms := standard, sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.TrKExpr.defeq,
    standardAxioms := standard, sorryOrigins := typingDebt },

  -- Legacy whole-environment compatibility interfaces. Catalog lookup consumer roots
  -- below are forbidden from depending on these declarations.
  { root := ``Ix.Kernel.TrKEnv.wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrKEnv.find?,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.tick.tcInv,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.instantiateUnivParams.tcInv,
    standardAxioms := standard, nativeAxioms := levelNative },

  -- The narrow upstream-context dependency behind translation uniqueness.
  { root := ``Ix.Kernel.KVLCtx.IsDefEq.find?_uniq,
    standardAxioms := standard },

  -- Dual-context reconciliation entry points used by the checker proofs.
  { root := ``Ix.Kernel.CtxRecon.wf, standardAxioms := standard },
  { root := ``Ix.Kernel.CtxRecon.lookupVar,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.CtxRecon.fvar_resolves,
    standardAxioms := standard },

  -- Non-circular world model and one-way lazy-load boundary.
  { root := ``Ix.Kernel.VerifyWorld.ofCatalog_catalogued_not_trusted,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.VerifyWorld.LE.trans,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.VerifyWorld.LE.catalogued_iff,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.LoadedAgrees.world_iff,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.LoadedAgrees.insert,
    standardAxioms := standard },
  { root := ``Ix.Kernel.LoadedAgrees.of_extension,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.VerifyWorld.ofCatalog_loaded,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.VerifyWorld.ofCatalog_loaded_not_trusted,
    standardAxioms := standard },

  -- Pending-declaration isolation. Raw correspondence has no declaration-WF
  -- premise; the fixture roots pin the concrete non-WF pending case.
  { root := ``Ix.Kernel.RawExprRel.mono,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RawExprRel.reference_resolved,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RawDeclRel.mono,
    standardAxioms := standard },
  { root := ``Ix.Kernel.PendingDecl.no_target_lookup,
    standardAxioms := standard },
  { root := ``Ix.Kernel.PendingDecl.no_self_expr_reference,
    standardAxioms := standard },
  { root := ``Ix.Kernel.PendingDecl.not_trustedDecl,
    standardAxioms := standard },
  { root := ``Ix.Kernel.IllTypedPending.pending_but_not_wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.IllTypedPending.loaded_pending_but_not_wf,
    standardAxioms := standard },

  -- Trusted-only catalog log and explicit-WF promotion boundary.
  { root := ``Ix.Kernel.RawDeclRel.wf_le,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrustedCatalogLog.wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrustedCatalogLog.catalogued,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrustedCatalogLog.find,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrustedCatalogRel.ofCatalog,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrustedCatalogRel.find,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrustedCatalogEntry.recursorRule,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrustedCatalogRel.recursorRule,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrustedCatalogEntry.recursorPattern,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrustedCatalogRel.recursorPattern,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrustedDecl.lookup,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrustedCatalogRel.lookup,
    standardAxioms := standard },
  { root := ``Ix.Kernel.Promotes.trans,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.TrustedCatalogRel.promote,
    standardAxioms := standard },
  { root := ``Ix.Kernel.IllTypedPending.trustedCatalogRel,
    standardAxioms := standard },
  { root := ``Ix.Kernel.WellTypedPromotion.promotes,
    standardAxioms := standard },

  -- World-based concrete-state invariant. Loading stays
  -- representation-only, promotion requires a fresh WF witness, and the
  -- fixed-world Hoare roots pin no-promotion behavior on both outcomes.
  { root := ``Ix.Kernel.TcStateWF.of_consts_eq,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcStateWF.load,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcStateWF.promote,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcStateWF.find?,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcInv.find?,
    standardAxioms := standard },
  { root := ``Ix.Kernel.IllTypedPending.tcInv_pending_but_not_wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.tick.tcStateWF,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.instantiateUnivParams.tcStateWF,
    standardAxioms := standard, nativeAxioms := levelNative },

  -- The certified-generation adapter may use only Ix.Theory.Named
  -- Theory transaction facts, never Ix checker/catalog/pattern authority.
  { root := ``Ix.Kernel.CertifiedGenerationTransaction.trace,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Kernel.CertifiedGenerationTransaction.afterWF,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Kernel.CertifiedGenerationTransaction.facts,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },

  -- The Theory-only block adapter preserves the same quarantine while
  -- exposing one atomic all-families/all-constructors/all-recursors/all-rules
  -- transaction rather than a sequence of singleton admissions.
  { root := ``Ix.Kernel.CertifiedBlockGenerationTransaction.trace,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Kernel.CertifiedBlockGenerationTransaction.afterWF,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Kernel.CertifiedBlockGenerationTransaction.facts,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := certificateAdapterForbidden },

  -- Inductive verification retains the exact Ix.Theory.Named candidate-producer equation alongside
  -- the certified Theory transaction.  Unlike the Theory-only adapter above,
  -- this Verify-backed bridge deliberately inherits the pinned analyzer debt.
  { root := ``Ix.Kernel.ProducedGenerationTransaction.facts,
    standardAxioms := standard,
    implementationAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Kernel.ExactProducedGenerationTransaction.facts,
    standardAxioms := standard,
    implementationAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },

  -- First genuine multi-family semantic witness: Tree/TreeList has two
  -- motives and recursors, five flattened constructors/rules, sibling
  -- recursion in both directions, and one recursive occurrence below a Pi.
  { root := ``Ix.Kernel.MutualTreeCertificateFixture.breadth,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Kernel.MutualTreeCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Kernel.MutualTreeCertificateFixture.finalEnvWF,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },

  -- The production compiler emits this SCC in physical order
  -- `TreeList, Tree`.  All seven family/constructor entries are linked to the
  -- complete catalog and admitted atomically without the pending recursor
  -- pattern/WF witnesses used by the later conditional closure.
  { root := ``Ix.Kernel.MutualTreeFixture.mutualFamilyAtomicClosure,
    standardAxioms := standard,
    nativeAxioms := mutualFamilyNative },

  -- The concrete breadth witness is the exact staged `IndexedVec`
  -- certificate: one parameter, one changing index, a recursive field, large
  -- elimination, and both generated rules.  It remains Theory-only here;
  -- production Ix catalog correspondence is audited in the later linkage.
  { root :=
      ``Ix.Kernel.IndexedRecursiveCertificateFixture.transaction_generation,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Kernel.IndexedRecursiveCertificateFixture.breadth,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Kernel.IndexedRecursiveCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Kernel.IndexedRecursiveCertificateFixture.producedCertificate_eq,
    standardAxioms := standard,
    implementationAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Kernel.IndexedRecursiveCertificateFixture.producedToCertified_eq,
    standardAxioms := standard,
    implementationAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Kernel.IndexedRecursiveCertificateFixture.producerLinkedFacts,
    standardAxioms := standard,
    implementationAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },

  -- The next honest one-family breadth witness is `Acc`: its sole recursive
  -- occurrence is reached beneath a two-binder Pi telescope, and the
  -- generated induction hypothesis is therefore itself a function. Like the
  -- IndexedVec certificate, these roots remain entirely on the Theory side
  -- of the catalog/checker boundary.
  { root :=
      ``Ix.Kernel.RecursivePiCertificateFixture.transaction_generation,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Kernel.RecursivePiCertificateFixture.breadth,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },
  { root := ``Ix.Kernel.RecursivePiCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    forbiddenDependencies := certificateAdapterForbidden },

  -- `AnnotatedPi` is the first certified singleton whose recursive-Pi
  -- candidate is genuinely normalized: the stored constructor retains
  -- `outParam Prop`, while the analyzer-owned candidate exposes `Prop`.
  -- These certificate roots remain entirely on the Theory side.
  { root :=
      ``Ix.Kernel.AnnotatedPiCertificateFixture.transaction_generation,
    standardAxioms := standard,
    implementationAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Kernel.AnnotatedPiCertificateFixture.breadth,
    standardAxioms := standardWithoutChoice,
    nativeAxioms := annotatedPiCertificateBreadthNative,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Kernel.AnnotatedPiCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    implementationAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Kernel.AnnotatedPiCertificateFixture.producerLinkedFacts,
    standardAxioms := standard,
    implementationAxioms := annotatedPiUpstreamAxioms,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },

  -- `AliasFormer` keeps the stored family result at `TypeFamilyAlias`, while
  -- the analyzer-owned candidate unfolds that reducible dependency to
  -- `Type`.  These roots certify the non-identity family-result view without
  -- Ix catalog, checker-pattern, or oracle authority.
  { root :=
      ``Ix.Kernel.AliasFormerCertificateFixture.transaction_generation,
    standardAxioms := standard,
    implementationAxioms := aliasFormerUpstreamAxioms,
    sorryOrigins := aliasFormerUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Kernel.AliasFormerCertificateFixture.breadth,
    standardAxioms := standardWithoutChoice,
    nativeAxioms := aliasFormerCertificateBreadthNative,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Kernel.AliasFormerCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    implementationAxioms := aliasFormerUpstreamAxioms,
    sorryOrigins := aliasFormerUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Kernel.AliasFormerCertificateFixture.producerLinkedFacts,
    standardAxioms := standard,
    implementationAxioms := aliasFormerUpstreamAxioms,
    sorryOrigins := aliasFormerUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },

  -- `AliasRec` retains `RecAlias AliasRec` in the stored constructor while
  -- certifying the direct-recursive checked field.  The adapter packages the
  -- pinned upstream generation/WF replay without Ix-side semantic authority.
  { root :=
      ``Ix.Kernel.AliasRecCertificateFixture.transaction_generation,
    standardAxioms := standard,
    implementationAxioms := aliasRecUpstreamAxioms,
    sorryOrigins := aliasRecUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Kernel.AliasRecCertificateFixture.breadth,
    standardAxioms := standard,
    implementationAxioms := aliasRecUpstreamAxioms,
    nativeAxioms := aliasRecCertificateBreadthNative,
    sorryOrigins := aliasRecUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },
  { root := ``Ix.Kernel.AliasRecCertificateFixture.certifiedFacts,
    standardAxioms := standard,
    implementationAxioms := aliasRecUpstreamAxioms,
    sorryOrigins := aliasRecUpstreamDebt,
    forbiddenDependencies := annotatedPiCertificateForbidden },

  -- Occurrence-validation boundary. These roots expose the selected loaded
  -- family and strengthen every production guard into the elementwise
  -- valid-inductive-application invariant, without oracle authority.
  { root :=
      ``Ix.Kernel.RecM.checkPositiveRecursiveApplicationPreconditions_success_iff,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.positiveUniverseArgumentsAgree_eq_true_iff,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.positiveIndicesIndependent_eq_true_iff,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositiveParametersFrom_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositiveParameters_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.PositiveParameterComparisonTrace.sound,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.PositiveParameterComparisonTrace.theoryDefEq,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.ValidPositiveRecursiveApplicationHeader.theoryParameters,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.PositiveParameterComparisonTrace.theoryDefEqScoped,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    -- This is the scoped method instantiation bridge, not the oracle-free occurrence
    -- theorem above. `ScopedWhnfStateInv` contains `TrustedCatalogLog`, whose
    -- ambient constructor names `InductiveOracle`; semantic use remains
    -- confined to the projected `ScopedWFAtOn.isDefEq` field.
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.ValidPositiveRecursiveApplicationHeader.theoryParametersScoped,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.positivityGroupMatches_eq_true_iff,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.SpecializationIdentityFixture.semanticUniverseEquality_does_not_collapse_specialization,
    standardAxioms := standard,
    nativeAxioms := specializationIdentityNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.checkPositiveRecursiveApplicationHeader_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.PositiveRecursiveApplicationHeaderTrace.valid,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositiveRecursiveApplicationHeader_valid,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositiveRecursiveApplication_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.PositiveRecursiveApplicationTrace.valid,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositiveRecursiveApplication_valid,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Production-traversal boundary. Root-free domains are state-preserving;
  -- direct recursive-family applications inherit the oracle-free occurrence
  -- invariant; and forall success exposes the decremented recursive run plus
  -- exact local-context restoration.
  { root := ``Ix.Kernel.RecM.withLctxRestoration_success,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositivityDomainFuel_rootFree,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositivityDomainFuel_direct,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositivityDomainFuel_direct_valid,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositivityDomainFuel_nested,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositivityDomainFuel_forall_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositivityDomainFuel_forall_negative,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Exhaustive nested positivity.  These roots expose exact header and
  -- constructor lookup, specialization selection, source-ordered constructor
  -- traversal, universe instantiation, parameter stripping/substitution,
  -- recursive field-domain checks, and context restoration.  The final root
  -- classifies every successful production domain without a branch oracle.
  { root := ``Ix.Kernel.RecM.findNestedPositivityGroup?_some,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.checkNestedPositivityApplicationPreconditions_success_iff,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.checkNestedPositivityApplicationResolvedFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.checkNestedPositivityApplicationCheckedFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkNestedConstructorFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkNestedConstructorsFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.checkFreshNestedPositivityApplicationFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.stripNestedCtorParameters_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkNestedCtorFieldsLoopFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkNestedCtorFieldsFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.completeNestedConstructor_of_trace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.completeNestedConstructorList_of_trace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.completeFreshNestedPositivity_of_trace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.completeNestedPositivityChecked_of_trace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.completeNestedPositivityResolved_of_trace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.checkNestedPositivityApplicationFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.checkNestedPositivityApplicationFuel_complete,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkPositivityDomainFuel_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Nested auxiliary expansion. The complete positivity trace emits an
  -- exact existing-or-fresh request; the flat scanner classifies every
  -- successful detector call as an unchanged pair or one fresh exact append.
  -- The source-ordered constructor and bounded-queue histories prove that the
  -- real public builder returns an aligned, duplicate-free physical/key list.
  -- The next fixture must identify its positivity request with one detector
  -- call; it cannot replace that reachability evidence with DefEq.
  { root := ``Ix.Kernel.lawfulBEqNestedSpecializationKey,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedAuxiliaryHeaderRel.key_eq,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedAuxiliaryHeaderRel.positivityFlatIdentity,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedAuxiliaryAppendTrace.member_mem,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedAuxiliaryAppendTrace.key_mem,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.appendNestedAuxiliary_fresh,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.appendNestedAuxiliary_existing,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxSeenSound.empty,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxSeenSound.push,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxTransition.seenSound,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxTransition.flat_mem,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxTransition.key_mem,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxHistory.single,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxHistory.trans,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxHistory.seenSound,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxHistory.flat_mem,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxHistory.key_mem,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxQueueExact.empty,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxQueueExact.pushOriginal,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxQueueExact.transition,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.FlatAuxQueueExact.history,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.appendNestedAuxiliary_transition,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.appendNestedAuxiliary_seenSound,
    standardAxioms := standard,
    nativeAxioms := occurrenceValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.tryDetectNestedCore_transition,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.tryDetectNested_transition,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.tryDetectNested_seenSound,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.scanFlatConstructorFields_history,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.scanFlatConstructor_history,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.scanFlatConstructors_history,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.buildFlatBlockQueueStep_history,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.runBounded_flatAuxHistory,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.seedFlatBlockMembers_exact,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.buildFlatBlockWithAuxSeen_exact,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.buildFlatBlock_auxiliaryOrder,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.CompleteNestedPositivityApplicationTrace.auxiliaryRequest,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.CompleteNestedPositivityApplicationTrace.producedRequest,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Concrete nested reachability. The compiler-shaped Box/Tree fixture
  -- runs production ingress, positivity, and flat-block construction on the
  -- same `Box Tree` occurrence.  Its headline root proves that the exact
  -- fresh positivity request is retained under the audited queue invariant.
  { root := ``Ix.Kernel.NestedRecursiveFixture.boxIngressRun,
    standardAxioms := standard,
    nativeAxioms := levelNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.boxIngressSucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.treeIngressRun,
    standardAxioms := standard,
    nativeAxioms := levelNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.treeIngressSucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.boxConcreteHeader,
    standardAxioms := standard,
    nativeAxioms := levelNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.boxConcreteHeaderMatchesNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nodeConcreteType,
    standardAxioms := standard,
    nativeAxioms := levelNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.nodeConcreteTypeNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.positivityRun,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.positivitySucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedWhnfRun,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.nestedWhnfSucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedWhnfResult_eq,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.nestedWhnfResultNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedActionRun,
    standardAxioms := standard,
    nativeAxioms := nestedRecursiveActionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.requestHeaderRelation,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.positivityCompleteTrace,
    standardAxioms := standard,
    nativeAxioms := nestedRecursiveActionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.boxLookupRun,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.boxLookupSucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.boxLookupConcrete_eq,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.boxLookupConcreteNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.positivityRequestProduced,
    standardAxioms := standard,
    nativeAxioms := nestedRecursiveProducedNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.positivityRequestFreshExpansion,
    standardAxioms := standard,
    nativeAxioms := nestedRecursiveFreshNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.flatBuildRun,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.flatBuildSucceededNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.builtFlatShape,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.builtFlatShapeNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.requestedAuxiliaryPresent,
    standardAxioms := standard,
    nativeAxioms := nameContextNative.push
      (nestedRecursiveFixtureNativeAxiom
        `Ix.Kernel.NestedRecursiveFixture.builtFlatShapeNative._native.native_decide.ax_1_1),
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedAuxiliaryReachability,
    standardAxioms := standard,
    nativeAxioms := nestedRecursiveReachabilityNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Exact Ix.Theory.Named syntax and semantic transport for the retained nested
  -- member.  The outer field reaches the fresh auxiliary; the auxiliary's
  -- own field recursively reaches the original Tree member at lower fuel.
  { root := ``Ix.Kernel.NestedRecursiveFixture.treeCandidateSyntax,
    standardAxioms := standard,
    nativeAxioms := nestedTreeCandidateSyntaxNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedAuxiliaryCandidateTarget,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryCandidateTargetNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedOuterPositivityTransport,
    standardAxioms := standard,
    nativeAxioms := nestedOuterTransportNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.nestedOuterConstructorPositivityTrace,
    standardAxioms := standard,
    nativeAxioms := nestedOuterTransportNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.nestedAuxiliaryFieldProductionTrace,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryProductionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.nestedAuxiliaryPositivityTransport,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryTransportNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.nestedAuxiliaryFieldProductionTraceAt,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryProductionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.nestedAuxiliaryConstructorPositivityTraceAt,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryConstructorNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.nestedAuxiliaryConstructorPositivityTrace,
    standardAxioms := standard,
    nativeAxioms := nestedAuxiliaryConstructorNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.leanFlatNodeConstructorTypeValidationTrace,
    standardAxioms := standard,
    nativeAxioms := nestedNodeConstructorValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.leanFlatNodeConstructorValidationRun,
    standardAxioms := standard,
    nativeAxioms := nestedNodeConstructorValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.leanFlatWrapConstructorTypeValidationTrace,
    standardAxioms := standard,
    nativeAxioms := nestedWrapConstructorValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.leanFlatWrapConstructorValidationRun,
    standardAxioms := standard,
    nativeAxioms := nestedWrapConstructorValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Completed nested semantic transaction.  The generic adapter consumes a
  -- local named-specification `NestedBlockCertificate`; the concrete roots then prove
  -- restored source/recursor/rule well-formedness, run Ix's real nested
  -- family checker, and admit the exact two-member source block atomically.
  -- No auxiliary flattening name, legacy inductive oracle, or pending axiom
  -- may enter this completed boundary.
  { root := ``Ix.Kernel.NestedFamilyCatalogLink.translateMember,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedFamilyCatalogLink.semanticEntry,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedFamilyCatalogLink.transition,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.semanticTreeCertificate,
    standardAxioms := standard,
    nativeAxioms := nestedSemanticCertificateNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.semanticTreeTransactionFacts,
    standardAxioms := standard,
    nativeAxioms := nestedSemanticFactsNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedFamilyKernelRun,
    standardAxioms := standard,
    nativeAxioms := nestedFamilyKernelNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedFamilyBlockCertificate,
    standardAxioms := standard,
    nativeAxioms := nestedFamilyCertificateNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedFamilyAtomicAdmission,
    standardAxioms := standard,
    nativeAxioms := nestedFamilyCertificateNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.nestedSemanticTransactionClosure,
    standardAxioms := standard,
    nativeAxioms := nestedSemanticTransactionClosureNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },

  -- Completed physical nested-recursor transaction.  The compiler and
  -- ingress roots pin the actual generated block; the two pattern roots pin
  -- the restored node/wrap equations independently; the final roots require
  -- all-or-nothing family-plus-recursor admission.  The only `sorryAx`
  -- origins are two exact inversion lemmas inherited from Ix.Theory.Named.
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedCompilerRun,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorCompilerRunNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedCompiledIdentityFacts,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorCompilerIdentityNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.recursorIngressRun,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorIngressNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root :=
      ``Ix.Kernel.NestedRecursiveFixture.nestedRecursorRepresentationFacts,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorRepresentationNative,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.treeNodePatternRel,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorNodePatternNative,
    sorryOrigins := nestedRestoredPatternUpstreamDebt,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.treeWrapPatternRel,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorWrapPatternNative,
    sorryOrigins := nestedRestoredPatternUpstreamDebt,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedRecursorAtomicAdmission,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorAtomicAdmissionNative,
    sorryOrigins := nestedRestoredPatternUpstreamDebt,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.NestedRecursiveFixture.nestedRecursorAtomicClosure,
    standardAxioms := standard,
    nativeAxioms := nestedRecursorAtomicClosureNative,
    sorryOrigins := nestedRestoredPatternUpstreamDebt,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },

  -- Generated-recursor metadata. The seven cached header fields are
  -- derived positionally from the certified flat block and are invariant
  -- under both best-effort and complete rule population.  The final root
  -- covers the actual anonymous-mode cache insertion phase; none of these
  -- roots may recover the legacy inductive oracle.
  { root := ``Ix.Kernel.GeneratedRecursorMetadata.at_of_expectedFlat,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.initialGeneratedRecursor_metadata,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursor.metadata_setRules,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursor.metadata_withRules,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursor.ty_withRules,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursor.map_metadata_modify_withRules,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursor.map_metadata_zipWithRules,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursor.map_ty_zipWithRules,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.commitGeneratedRecursorRulesAt_artifacts,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.populateOptionalGeneratedRecursorRules_metadata,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecM.populateCompleteGeneratedRecursorRules_metadata,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.populateRecursorRulesFromBlock_artifacts,
    standardAxioms := standard,
    nativeAxioms := inductiveNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.populateRecursorRulesFromBlock_metadata,
    standardAxioms := standard,
    nativeAxioms := inductiveNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.GeneratedRecursorSemantics.CanonicalRulesS.generatedRuleAt,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.GeneratedRecursorSemantics.CanonicalArtifactsS.withRules,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.GeneratedRecursorSemantics.CanonicalTypeS.canonical,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.GeneratedRecursorSemantics.CanonicalRulesS.canonical,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.GeneratedRecursorSemantics.CanonicalArtifactsS.canonical,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.GeneratedRecursorSemantics.RecM.commitGeneratedRecursorRulesAt_canonicalAt,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.buildGeneratedRecursorTypes_metadata,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.buildAndCacheGeneratedRecursors_metadata,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Generated-recursor type closure. Production closes the accumulated
  -- domains through explicit right-to-left intern requests. These roots prove
  -- exact finite-support execution, operation-shaped structural translation,
  -- and equality with Ix.Theory.Named's public canonical mixed recursor type.
  { root := ``Ix.Kernel.CertifiedGenerationTransaction.generationEnv,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursorTypeClosure.opened_toCtx,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursorTypeClosure.isType_forallN_inv,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursorTypeClosure.onTel_isType_getElem,
    standardAxioms := propextOnly,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.GeneratedRecursorTypeClosure.canonical_onTel_and_bodyType,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursorTypeClosure.canonical_domainType,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursorTypeClosure.canonical_bodyType,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.GeneratedRecursorTypeClosure.TelescopeS.of_canonical,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.GeneratedRecursorTypeClosure.closeV_eq_forallN_take,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursorTypeClosure.closeV_canonical,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursorTypeClosure.TelescopeS.close,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursorTypeClosure.run_exact,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursorTypeClosure.run_translation,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursorTypeClosure.run_canonicalType,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.GeneratedRecursorTypeClosure.buildRecType_decompose,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.GeneratedRecursorTypeClosure.buildRecType_canonical_of_body,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.IndexedRecursiveFixture.familyBuildTypeExecution,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorTypeFixtureNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.IndexedRecursiveFixture.familyBuildArtifactsExecution,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorRuleFixtureNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Generated-recursor commit, selection, and exhaustive comparison.
  -- Production selection compares complete closed types through an explicit
  -- finite fold; one scoped method successor layer preserves the scoped state across
  -- selection and gives semantic meaning to the repeated type and positional
  -- rule comparisons.
  { root := ``Ix.Kernel.RecM.checkGeneratedRecursorFromCache_success,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkGeneratedRecursorFromCache_canonical,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkGeneratedRecursorFromCache_canonicalScoped,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.selectGeneratedRecursorIndex_preservesScoped,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.IndexedRecursiveFixture.familyRuleCommitExecution,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorCommitFixtureNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.IndexedRecursiveFixture.familyCacheCheckExecution,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorCheckerFixtureNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.IndexedRecursiveFixture.familyCacheCheckCanonicalScoped,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorCanonicalFixtureNative,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },

  -- Outer member closure and exact semantic admission. The explicit
  -- transition bridge fixes both Theory environments and requires complete
  -- trusted provenance for every exact physical member; the existing-block
  -- specialization keeps that environment unchanged for the recursor block.
  -- Their shared log type mentions the legacy ambient constructor, so the
  -- audit forbids every oracle constructor/world-materialization operation
  -- rather than the `InductiveOracle` type name itself.
  { root :=
      ``Ix.Kernel.SemanticBlockTransitionCertificate.le_admittedWorld,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.SemanticBlockTransitionCertificate.admit,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.SemanticBlockTransitionCertificate.admitState,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root :=
      ``Ix.Kernel.ExistingSemanticBlockCertificate.le_admittedWorld,
    standardAxioms := standard,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.ExistingSemanticBlockCertificate.admit,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.ExistingSemanticBlockCertificate.admitState,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.OneFamilyRecursorCertificate.atomicClosure,
    standardAxioms := standard,
    forbiddenDependencies := existingSemanticBlockForbiddenDependencies },
  { root := ``Ix.Kernel.IndexedRecursiveFixture.familyRecursorAtomicClosure,
    standardAxioms := standard,
    nativeAxioms := generatedRecursorAtomicClosureNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  { root := ``Ix.Kernel.IndexedRecursiveFixture.producerLinkedOneFamilyClosure,
    standardAxioms := standard,
    implementationAxioms := annotatedPiUpstreamAxioms,
    nativeAxioms := indexedProducerClosureNative,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  { root :=
      ``Ix.Kernel.RecursivePiRecursorFixture.recursivePiAtomicClosure,
    standardAxioms := standard,
    nativeAxioms := recursivePiAtomicClosureNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  { root :=
      ``Ix.Kernel.AnnotatedPiRecursorFixture.annotatedPiAtomicClosure,
    standardAxioms := standard,
    implementationAxioms := annotatedPiUpstreamAxioms,
    nativeAxioms := annotatedPiAtomicClosureNative,
    sorryOrigins := annotatedPiUpstreamDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  { root :=
      ``Ix.Kernel.AliasFormerRecursorFixture.aliasFormerAtomicClosure,
    standardAxioms := standard,
    implementationAxioms := aliasFormerUpstreamAxioms,
    nativeAxioms := aliasFormerAtomicClosureNative,
    sorryOrigins := aliasFormerUpstreamDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  { root :=
      ``Ix.Kernel.AliasRecRecursorFixture.aliasRecAtomicClosure,
    standardAxioms := standard,
    implementationAxioms := aliasRecUpstreamAxioms,
    nativeAxioms := aliasRecAtomicClosureNative,
    sorryOrigins := aliasRecUpstreamDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },

  -- Flat semantic transport. The refined flat production trace erases
  -- to the exhaustive classifier, and the operation-shaped cross-kernel
  -- contract recursively constructs Ix.Theory.Named's retained positivity trace.
  -- Nested auxiliary expansion remains a separate explicit bridge.
  { root := ``Ix.Kernel.FlatPositivityDomainTrace.toPositivityDomainTrace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root :=
      ``Ix.Kernel.FlatPositivityTraceTransport.constructorPositivityTrace,
    standardAxioms := standard,
    nativeAxioms := inferNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Concrete cross-kernel trace bridge. These roots start at the
  -- exact positivity calls selected by the production IndexedVec family
  -- checker, transport those operations to Ix.Theory.Named, and replay the complete
  -- retained constructor validator.  The direct recursive fixture has no
  -- nested auxiliary expansion; that remains a separate generic proof obligation.
  { root :=
      ``Ix.Kernel.IndexedRecursiveFixture.indexedVecConsConstructorValidationRun,
    standardAxioms := standard,
    nativeAxioms := indexedConstructorValidationNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- Production-linked indexed/recursive fixture. The
  -- generated cons equation includes its predecessor recursive call; the
  -- oracle is then instantiated by exact anonymous ingress, production
  -- family/recursor checking, exact ownership, and atomic admission.  The
  -- same executable witness rejects a recursor whose stored index arity was
  -- changed while its canonical type and rules were retained.
  { root := ``Ix.Theory.Named.VEnv.HasType.lamN_appN_beta,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.IndexedRecursivePattern.nilPatternRel,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.IndexedRecursivePattern.consPatternRel,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.IndexedRecursivePattern.oracle,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.IndexedRecursiveFixture.endToEndAcceptance,
    standardAxioms := standard,
    nativeAxioms := indexedRecursiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },

  -- Elimination-breadth regression over exact kernel declarations.  These
  -- roots compile, ingress, and run the production family/recursor checkers
  -- for both a source-universe-bearing small eliminator and `Eq`'s positive
  -- K branch, then relate the stored physical metadata to Ix.Theory.Named's exact
  -- generation trace.
  { root := ``Ix.Kernel.EliminationBreadthFixture.smallEliminationAcceptance,
    standardAxioms := standard,
    nativeAxioms := smallEliminationAcceptanceNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },
  { root := ``Ix.Kernel.EliminationBreadthFixture.kTargetAcceptance,
    standardAxioms := standard,
    nativeAxioms := kTargetAcceptanceNative,
    forbiddenDependencies := occurrenceValidationForbiddenDependencies },

  -- The singleton link and legacy oracle constructors remain audited as
  -- compatibility surfaces.  The concrete Boolean closure below no longer
  -- consumes those oracle constructors: its family block advances the exact
  -- generated Theory environment, and its recursor block consumes entries
  -- already installed there.
  { root := ``Ix.Theory.Named.VEnv.HasType.transfer_appN_telescope,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.SingletonFamilyCatalogLink.oracle,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.SingletonRecursorCatalogLink.enumerationPatternRel,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.SingletonRecursorCatalogLink.oracle,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.certifySingletonFamilyBlock,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.certifySingletonRecursorBlock,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  -- Oracle-free semantic composition is audited independently of production
  -- execution so its native boundary contains only the finite representation,
  -- generation, equation, and pattern checks.
  { root := ``Ix.Kernel.BooleanEnumerationFixture.oneFamilyAtomicClosure,
    standardAxioms := standard,
    nativeAxioms := booleanSemanticAdmissionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },
  -- The headline additionally joins anonymous ingress, both production
  -- block-body and branch checkers, exact physical/catalog ownership, and the
  -- composed two-stage semantic transaction in one final world.
  { root := ``Ix.Kernel.BooleanEnumerationFixture.endToEndAcceptance,
    standardAxioms := standard, nativeAxioms := booleanEnumerationNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := canonicalRecursorForbiddenDependencies },

  -- Explicit ambient-inductive assumption boundary. Audit every
  -- oracle projection so adding a field changes this manifest, then pin the
  -- constructive Nat model and its adversarial loaded-state witness.
  { root := ``Ix.Kernel.RawInductiveConstRel.mono,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TrKExprS.mono,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RegisteredRecursorRuleRhsRel.mono,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RegisteredRecursorRuleRhsRel.rhsTyped,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RawRecursorRuleRel.registeredRhs,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RawRecursorRuleRel.mono,
    standardAxioms := standard },
  { root := ``Ix.Kernel.HeadConstN.of_varN_matches },
  { root := ``Ix.Kernel.RecursorIotaPattern.matches_shape },
  { root := ``Ix.Kernel.KConst.RecursorRuleAt.hasRecursorRule,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.RawRecursorRulePatternRel.mono,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.InductiveOracle.members,
    standardAxioms := standard },
  { root := ``Ix.Kernel.InductiveOracle.nonempty,
    standardAxioms := standard },
  { root := ``Ix.Kernel.InductiveOracle.fresh,
    standardAxioms := standard },
  { root := ``Ix.Kernel.InductiveOracle.after,
    standardAxioms := standard },
  { root := ``Ix.Kernel.InductiveOracle.envLE,
    standardAxioms := standard },
  { root := ``Ix.Kernel.InductiveOracle.blockWF,
    standardAxioms := standard },
  { root := ``Ix.Kernel.InductiveOracle.translateBlock,
    standardAxioms := standard },
  { root := ``Ix.Kernel.InductiveOracle.recursorFacts,
    standardAxioms := standard },
  { root := ``Ix.Kernel.InductiveOracle.recursorPatterns,
    standardAxioms := standard },
  { root := ``Ix.Kernel.InductiveOracle.catalogued,
    standardAxioms := standard },
  { root := ``Ix.Kernel.AmbientNat.oracle,
    standardAxioms := standard },
  { root := ``Ix.Kernel.AmbientNat.nat_lookup_good,
    standardAxioms := standard },
  { root := ``Ix.Kernel.AmbientNat.badDecl_not_wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.AmbientNat.acceptance,
    standardAxioms := standard },

  -- Lookup and admission roots resolve exact concrete
  -- constants through trusted-world provenance and are mechanically barred
  -- from depending on the legacy whole-environment translation.
  { root := ``Ix.Kernel.TrustedConstRel.mono,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TrustedConstRel.trKExprS_const,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TrustedCatalogRel.resolve,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcStateWF.resolve,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcInv.resolve,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.natResolved,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.natReferenceTranslates,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.bad_not_resolved,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.natResolvedInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },

  -- Lookup isolation, exhaustive semantic-cache provenance, monotone
  -- warm-world transport, and transactional public-check error boundary.
  { root := ``Ix.Kernel.PendingDecl.lookup_isolation,
    standardAxioms := standard },
  { root := ``Ix.Kernel.CacheEntry.SupportedBy.mono },
  { root := ``Ix.Kernel.CacheAuthority.stable_mono,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.CacheProvenance.mono,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.CacheProvenance.pending_isolation_stable,
    standardAxioms := standard },
  { root := ``Ix.Kernel.KEnv.restoreBlockCheckResultsOnError_origin,
    standardAxioms := standard },
  { root := ``Ix.Kernel.CacheInvariant.mono,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.CacheInvariant.insertWhnf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.CacheInvariant.insertWhnfNoDelta,
    standardAxioms := standard },
  { root := ``Ix.Kernel.CacheInvariant.insertWhnfNoDeltaCheap,
    standardAxioms := standard },
  { root := ``Ix.Kernel.CacheInvariant.insertWhnfCore,
    standardAxioms := standard },
  { root := ``Ix.Kernel.CacheInvariant.insertWhnfCoreCheap,
    standardAxioms := standard },
  { root := ``Ix.Kernel.CacheInvariant.of_intern_update,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.CacheInvariant.clearReductionCaches,
    standardAxioms := standard },
  { root := ``Ix.Kernel.CacheInvariant.restoreCheckCachesOnError,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.isolateCheckErrors_error,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.TcM.reset_cache_frame,
    standardAxioms := standard },
  { root := ``Ix.Kernel.KernelStateWF.pendingCacheIsolation,
    standardAxioms := standard },
  { root := ``Ix.Kernel.KernelStateWF.restoreCheckCachesOnError,
    standardAxioms := standard },
  { root := ``Ix.Kernel.AmbientNat.warmCache_worldTransport,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.warmCache_cannotResolvePending,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.cacheAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- WHNF's concrete Theory reduction meaning, exact five-way cache overlay,
  -- and real ambient-Nat warm-hit witness.  The only sorries are the already
  -- named upstream inductive-environment boundary.
  { root := ``Ix.Kernel.WhnfMeaning.refl,
    standardAxioms := standard },
  { root := ``Ix.Kernel.WhnfMeaning.symm,
    standardAxioms := standard },
  { root := ``Ix.Kernel.WhnfMeaning.mono,
    standardAxioms := standard },
  { root := ``Ix.Kernel.ExprCacheKind.isWhnf_iff },
  { root := ``Ix.Kernel.WhnfCacheValid.mono,
    standardAxioms := standard },
  { root := ``Ix.Kernel.WhnfCacheValid.expr,
    standardAxioms := standard },
  { root := ``Ix.Kernel.CacheProvenance.isRec_of_trusted,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.IsRecCacheValid.mono,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.IsRecCacheValid.trusted,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.kernelCacheSemantics_isRec_valid,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheProvenance.whnfMeaning,
    standardAxioms := standard },
  { root := ``Ix.Kernel.CacheInvariant.whnfHit,
    standardAxioms := standard },
  { root := ``Ix.Kernel.AmbientNat.supportExpr_whnfMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.warmHit_whnfMeaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNative_noAccel,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RecM.tryReduceBitvec_noAccel,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.tryReduceDecidable_noAccel,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RecM.tryReduceFinValDecidableRec_noAccel,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.WhnfTheory.exprWF,
    standardAxioms := standard },
  { root := ``Ix.Kernel.WhnfTheory.transMeaning,
    standardAxioms := standard,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RawProjRel.none_ok,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.RawProjRel.named_ok,
    standardAxioms := standard,
    sorryOrigins := projectionDebt },
  { root := ``Ix.Kernel.ConcreteProjectionFixture.acceptance,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    sorryOrigins := projectionDebt },
  { root := ``Ix.Kernel.TcM.ctxAddrForLbr_zero,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Kernel.TcM.whnfKey_closed,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Kernel.ContextKeyFrame.whnfStateInv,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.ctxAddrForLbr_wf,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Kernel.TcM.whnfKey_wf,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Kernel.TcM.whnfKey_matches_wf,
    standardAxioms := standard, nativeAxioms := contextNative },
  -- interning frame: exact intern-only framing, execution-indexed simultaneous
  -- substitution, and the production one-argument beta path.
  { root := ``Ix.Kernel.InternUpdateFrame.whnfStateInv,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.runIntern_whnf_wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.runIntern_whnf_eval,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RunAssumptions.simulSubst_whnf_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.simulSubst_whnf_eval,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.WhnfMeaning.beta,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.WhnfMeaning.letE,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.WhnfMeaning.betaSimul,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.WhnfCoreLeaf.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_betaOne,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_leaf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsUncached_betaOne,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsUncached_betaOne_wf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlags_leaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.AmbientNat.warmStateInvAccelerated,
    standardAxioms := standard,
    nativeAxioms := inferNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.warmKey_matches_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.whnfCoreConst_noAccel_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.betaIdentityMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.betaSimulSpec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.AmbientNat.betaSimulMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.betaWalker_eval,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.AmbientNat.betaResultMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.betaCoreUncached_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.AmbientNat.betaCoreUncached_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- zeta reduction: both production zeta branches, including the legacy lifting walk,
  -- mixed-context semantic lookup, bounded driver, and inhabited fixtures.
  { root := ``Ix.Kernel.CtxRecon.lctxFindLetVal,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.TcM.lookupLetVal_eval,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RunAssumptions.lift_whnf_wf,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RunAssumptions.lift_whnf_eval,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.WhnfMeaning.zetaVar,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.WhnfMeaning.zetaFVar,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_varZeta,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_fvarZeta,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsUncached_nextLeaf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsUncached_varZeta,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsUncached_fvarZeta,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsUncached_varZeta_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsUncached_fvarZeta_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.AmbientNat.bvarZetaLiftSpec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.AmbientNat.bvarZetaLookupEval,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.AmbientNat.bvarZetaMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.bvarZetaCoreUncachedEval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.AmbientNat.bvarZetaAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fvarZetaMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fvarZetaCoreUncachedEval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.AmbientNat.fvarZetaAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- projection/iota branch: exact projection/iota branches and bounded-driver composition.
  -- Semantic success is conditional on an explicit translated-source oracle;
  -- the two hostile fixtures prove that raw helper success cannot replace it.
  { root := ``Ix.Kernel.WhnfMeaning.projection,
    standardAxioms := standard },
  { root := ``Ix.Kernel.WhnfMeaning.registeredDefEq,
    standardAxioms := standard },
  { root := ``Ix.Kernel.InductiveReductionOracle.projection,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.InductiveReductionOracle.iota,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_projection,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_iota,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsUncached_projection,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsUncached_iota,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsUncached_projection_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsUncached_iota_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.AmbientNat.projectionReduceEval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.projectionCoreEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.projectionSource_not_translated,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.projectionAdversarialWitness,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaStateInv,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaTryEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaCoreEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaSource_not_translated,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaAdversarialWitness,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- structural trace: arbitrary-length structural traces compose exact production
  -- execution, fixed-world/context invariants, and local Theory meanings.
  -- The inhabited fixture takes two `.next` steps before its leaf; the
  -- hostile zero-fuel witness cannot be certified as a successful trace.
  { root := ``Ix.Kernel.RecM.WhnfCoreTrace.no_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfCoreTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfCoreTrace.initialInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfCoreTrace.finalInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfCoreTrace.meaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.WhnfCoreTrace.uncached_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfCoreTrace.uncached_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.AmbientNat.structuralNatLit_type,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structuralWhnfTheory,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structuralLoopStateInv,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structuralLoopSourceMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structuralLoopBetaMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structuralLoopFVarStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structuralLoopBetaStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structuralLoopTrace,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structuralLoopAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structuralLoopZeroFuel,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- structural cache: the public structural entry point's keyed body has exact full,
  -- cheap, miss, hit, and transient equations.  Misses require both an
  -- execution-indexed trace and universal provenance before insertion;
  -- hits require the physical entry, semantic invariant, and executed key
  -- match.  The Nat fixture runs cold-to-warm in both isolated partitions.
  { root := ``Ix.Kernel.RecM.WhnfCoreNonLeaf.enter,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlags_varNotLet,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlags_varEnter,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfCoreKeyedEntry.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsNonLeaf_fullHit,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsNonLeaf_cheapHit,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsNonLeaf_fullMiss,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsNonLeaf_cheapMiss,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsNonLeaf_transient,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfCoreCacheUpdate.full_whnfStateInv,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.WhnfCoreCacheUpdate.cheap_whnfStateInv,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlags_fullHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlags_cheapHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlags_fullMiss_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlags_cheapMiss_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlags_transient_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.AmbientNat.betaArgMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullCoreProvenance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.cheapCoreProvenance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.coreCacheFreshStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullCoreWarmStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.bothCoreWarmStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.coreCacheKey_eval,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.coreCacheKey_matches,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.betaTransientFalse,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.betaWalker_eval_state,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.betaStep_state,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.coreCacheTrace,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullCoreColdAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullCoreWarmAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.cheapCorePolicyMissAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.cheapCoreWarmAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.coreCachePolicyIsolation,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  -- outer WHNF driver: no-delta and full-WHNF now have execution-indexed bounded traces,
  -- exact public-prefix/cache/fuel equations, provenance-checked insertion,
  -- and semantic hit/miss acceptance.  The Nat fixture executes all nested
  -- cache layers, proves the cold call consumes exactly one fuel unit, and
  -- proves the warm public call preserves the entire state.
  { root := ``Ix.Kernel.WhnfStateInv.of_semantic_fields_eq,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.stepTrace_disabled,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.TcM.bumpStats_disabled,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.TcM.tick_success,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.WhnfNoDeltaTrace.no_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfNoDeltaTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfNoDeltaTrace.initialInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfNoDeltaTrace.finalInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfNoDeltaTrace.meaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.WhnfNoDeltaTrace.uncached_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfNoDeltaTrace.uncached_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.WhnfFullTrace.no_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfFullTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfFullTrace.initialInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfFullTrace.finalInv,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfFullTrace.meaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.WhnfFullTrace.uncached_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfFullTrace.uncached_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.WhnfDriverNonLeaf.noDelta_enter,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfDriverNonLeaf.full_enter,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfDriverEntry.noDelta_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfDriverEntry.full_eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccModePrefix_disabled,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccModeMissCharge_disabled,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplNonLeaf_fullHit,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplNonLeaf_cheapHit,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplNonLeaf_fullMiss,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplNonLeaf_cheapMiss,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplNonLeaf_stuck,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplNonLeaf_transient,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplNonLeaf_nativeNoInsert,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfDriverCacheUpdate.noDelta_whnfStateInv,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.WhnfDriverCacheUpdate.noDeltaCheap_whnfStateInv,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.WhnfDriverCacheUpdate.full_whnfStateInv,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImpl_fullHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImpl_cheapHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImpl_fullMiss_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImpl_cheapMiss_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImpl_stuck_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImpl_transient_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccModeNonLeaf_hit,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccModeNonLeaf_miss,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccModeNonLeaf_stuck,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccModeNonLeaf_transient,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccModeNonLeaf_nativeNoInsert,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccMode_hit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccMode_miss_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccMode_stuck_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccMode_transient_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.whnf_public_eq_whnfWithNatSuccMode,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.AmbientNat.betaNoDeltaStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullNoDeltaProvenance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfProvenance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullNoDeltaWarmStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.noDeltaTrace,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullNoDeltaColdAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullNoDeltaWarmAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.noDeltaCachePolicyIsolation,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfChargedStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfPrefixCold,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfMissCharge,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfCharged_noDeltaHit,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.betaFullWhnfStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfTrace,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfWarmStateInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfColdAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfWarmAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfFuelDiscipline,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfCacheLayering,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  -- total-outcome boundary: local step contracts now construct success traces and classify
  -- bounded exhaustion versus step errors.  The public no-delta/full-WHNF
  -- dispatchers close conditionally over suffix reconciliation, transient
  -- lookup safety, collision-robust insertion provenance, and the local
  -- semantic step contracts.  Instrumentation and miss charging are proved.
  { root := ``Ix.Kernel.WhnfPost.transMeaning,
    standardAxioms := standard, sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.WhnfPost.meaning,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.isLetVar_wf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.TcM.stepTrace_whnf_wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.bumpStats_whnf_wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.WF.liftTcM,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.WF.get,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.WF.modifyGet,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.WF.modify,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.WhnfCoreTrace.complete,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfCoreTrace.uncached_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.WhnfNoDeltaTrace.complete,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfNoDeltaTrace.uncached_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.WhnfFullTrace.complete,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.WhnfFullTrace.uncached_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplNonLeaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImpl_nonLeaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccModeNonLeaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccMode_nonLeaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccModePrefix_wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccModeMissCharge_wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccMode_nonLeaf_semantic_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImpl_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfWithNatSuccMode_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNoDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.noDeltaZeroFuel,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fullWhnfZeroFuel,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.whnfLoopErrorSeparation,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfPost.refl,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.WF.bind,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.runBounded_wf,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.WhnfLeaf.eval,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnf_leaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnf_leaf_wf_of_theory,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.AmbientNat.noAccelStateInv,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.whnfLeaf_noAccel_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.whnfLeaf_noAccel_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.whnfKey_fst,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Kernel.WhnfContextKeys.Matches.sourceAddr,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Kernel.CacheProvenance.whnfMeaningOfMatches,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Kernel.CacheInvariant.whnfHitOfMatches,
    standardAxioms := standard, nativeAxioms := contextNative },
  { root := ``Ix.Kernel.AmbientNat.warmKey_matches,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.methodsN_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.methodsN_succ_whnf,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.methodsN_succ_whnfCore,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.methodsN_succ_whnfMode,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.methodsN_succ_whnfCoreFlags,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.methodsN_succ_infer,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.methodsN_succ_isDefEq,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.methodsOut_whnf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.methodsOut_whnfCore,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.methodsOut_whnfMode,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.methodsOut_whnfCoreFlags,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.methodsOut_infer,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.methodsOut_isDefEq,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.TcM.runRec_apply,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.TcM.runRec_directInfer_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.TcM.whnf_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.TcM.whnfCore_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.TcM.whnfNoDelta_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.TcM.infer_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.TcM.isDefEq_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.TcM.ensureSort_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.TcM.ensureForall_eq_runRec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.unfoldConstValue_equation,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RecM.tryDeltaUnfold_equation,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RecM.deltaUnfoldOne_equation,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RecM.applyIotaArg_false,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.applyIotaArg_true_lam,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.isNatLiteralRecursorApp_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.isTransientNatLiteralWork_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.cleanupNatOffsetMajor_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.projectDecidableFinValMinor_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.tryReduceFinValDecidableRec_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.tryReduceProjectionDefinition_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.natRecLiteralParts_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.isNatStuckRecursorAddr_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.isStuckNatPredicateProbe_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.bitvecOfNatArgs_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.charOfNatExpr_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.tryReduceString_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.discoverBlockInductives_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.runBounded_zero,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.runBounded_succ,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.consumeBetaLams_equation,
    standardAxioms := standard,
    nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.consumeBetaLamsFuel_zero,
    standardAxioms := standard,
    nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.consumeBetaLamsFuel_succ,
    standardAxioms := standard,
    nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.compareRank_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.RecM.isNatLike_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.isNatZero_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.natSuccOf_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.isBoolTrue_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.isDelta_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.isRegular_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.defRankId_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.infer_eq_inferWith,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.inferCall_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.inferOnlyCall_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.isDefEqCall_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.whnfRec_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.whnfModeRec_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.whnfCoreFlagsRec_run,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.whnf_eq_whnfWithNatSuccMode,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCore_eq_whnfCoreWithFlags,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDelta_eq_whnfNoDeltaImpl,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.ensureSortDirect_equation,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.ensureForallDirect_equation,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.peelProjForall_equation,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.checkNoUnsafeRefs_equation,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.checkNoUnsafeRefs_go_nil,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.checkNoUnsafeRefs_go_app,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.validateUnivParamsSeen_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.validateUnivParamsSeen_go_nil,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.validateUnivParamsSeen_go_max,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.validateExprWellScoped_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.validateExprWellScoped_go_nil,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.validateExprWellScoped_go_app,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.peelRuleIhForalls_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.checkPositivityDomain_equation,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.checkPositivityDomainFuel_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.checkNestedCtorFieldsFuel_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.checkNestedCtorFieldsLoopFuel_zero,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.countForalls_equation,
    standardAxioms := standard, nativeAxioms := inferNative },
  -- The complete checker dispatch is transparent now; these roots pin its
  -- exact production trust boundary in addition to the local equations.
  { root := ``Ix.Kernel.RecM.checkInductive,
    standardAxioms := standard, nativeAxioms := inductiveNative },
  { root := ``Ix.Kernel.RecM.checkRecursorMemberImpl,
    standardAxioms := standard, nativeAxioms := inductiveNative },
  { root := ``Ix.Kernel.RecM.checkConst,
    standardAxioms := standard, nativeAxioms := inductiveNative },
  { root := ``Ix.Kernel.TcM.checkConst,
    standardAxioms := standard, nativeAxioms := inductiveNative },
  { root := ``Ix.Kernel.extractNatValue_app_const_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.extractNatValue_nat_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.projectionDefinitionInfo_go_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.EquivManager.find_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.EquivManager.find_go_zero },
  { root := ``Ix.Kernel.EquivManager.find_go_succ },
  { root := ``Ix.Kernel.LocalContext.truncate_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.LocalContext.truncate_go_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.LocalContext.truncate_go_succ,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.TcM.restoreDepth_apply,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.restoreDepth_go_zero,
    standardAxioms := standard },
  { root := ``Ix.Kernel.TcM.ctxSuffixNeed_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.TcM.ctxSuffixNeed_succ,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.TcM.ctxSuffixNeed_of_fixed,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.KExpr.render_equation,
    standardAxioms := standard },
  { root := ``Ix.Kernel.KExpr.renderFuel_zero,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.natOffset_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.natOffsetOrZero_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.evalNatOffsetLiteral_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.natOffsetFuel_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.evalNatOffsetLiteralFuel_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.tryEvalNatValueForPred_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.tryEvalNatValueForPredFuel_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.compareKUniv_succ_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.compareKUniv_max_equation,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.mergeSorted_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.mergeSorted_go_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.sortByCompare_equation,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.sortByCompareFuel_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.sortKConstsRefineFuel_zero,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.KExpr.treeSize_pos,
    standardAxioms := propextOnly },
  { root := ``Ix.Kernel.exprMentionsAddr_equation,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.exprMentionsAddr_go_nil,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.exprMentionsAddr_go_app,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.exprMentionsAddr_go_const,
    standardAxioms := standardWithoutChoice },

  -- RuntimeContracts: the repaired step source includes finite support plus an actual
  -- translation; closed contexts derive both key representation and
  -- collision-robust write validity.  The transient Nat probe is proved
  -- state-pure for eager states.  General lazy execution is reduced to the
  -- exact invariant contract of the driver-installed environment hook.
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_leaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_betaOne_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_projection_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_iota_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RunAssumptions.subst_whnf_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RunAssumptions.subst_whnf_eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_letE,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_letE_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- regular-binder fallback: both translated regular-binder forms take the state-pure `.done`
  -- fallback and cannot be confused with their let-bound zeta siblings.
  { root := ``Ix.Kernel.TcM.lookupLetVal_none_state,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_varDone,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_fvarDone,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_varDone_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_fvarDone_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.bvarStuckAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.fvarStuckAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- stuck-reduction fallback: projection misses and unchanged non-lambda application heads keep
  -- their original syntax, distinguish helper errors from `none`, and are
  -- inhabited by translated projection and constructor-application fixtures.
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_projectionDone,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_projectionWhnfError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_projectionReduceError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appUnchangedDone,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appHeadError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appUnchangedIotaError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_projectionDone_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appUnchangedDone_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.appStuckAcceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.ProjectionFallback.acceptance,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },

  -- application rebuilding: both application rebuilding loops share one audited helper.  A
  -- finite certificate fixes suffix order, support, collision freedom, and
  -- intern-only framing; general multi-beta and changed-head hit/miss/error
  -- equations consume that helper boundary.  The Nat fixtures make argument
  -- reversal, a trailing argument, and physically changed heads observable.
  { root := ``Ix.Kernel.InternUpdateFrame.refl,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.InternUpdateFrame.trans,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RunAssumptions.internExpr_whnf_eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishAppResult_eq_foldlM,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.finishAppResult_one,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.FinishAppRequests.result_eq_foldl,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.FinishAppRequests.support,
    standardAxioms := standard, nativeAxioms := levelNative },
  { root := ``Ix.Kernel.RecM.FinishAppRequests.foldlM_eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.FinishAppRequests.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.FinishAppRequests.final_eq_spec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_betaMany,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appChangedIota,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appChangedDone,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appChangedIotaError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_betaMany_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appChangedDone_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appChangedIota_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appChangedIotaError_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiBetaStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.changedHeadInternSpec,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.AmbientNat.changedHeadStep,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.WhnfKey.closed_represents,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.WhnfCacheWriteOracle.closed,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.tryGetConst_noLazy,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.TcM.lazyIngressAddr_wf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.TcM.tryGetConst_wf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.KId.anon_eq_of_addr_eq },
  { root := ``Ix.Kernel.TcM.tryGetConst_success_loaded,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.NatRecLiteralPartsSuccessTrace.eval,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.NatRecLiteralPartsSuccessTrace.complete,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.NatRecLiteralPartsSuccessTrace.trusted,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrustedNatRecLiteralParts.patternAt,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.HeadConstN.matches_varN },
  { root := ``Ix.Kernel.HeadConstN.natLit_zero },
  { root := ``Ix.Kernel.HeadConstN.natLit_succ },
  { root := ``Ix.Kernel.RecursorIotaPattern.matches_of_shapes },
  { root := ``Ix.Kernel.RecursorIotaPattern.exists_matches_iff_shapes },
  { root := ``Ix.Kernel.RecursorIotaPattern.matches_natZero },
  { root := ``Ix.Kernel.RecursorIotaPattern.matches_natSucc },
  { root := ``Ix.Kernel.NatRecIotaCase.major_shape },
  { root := ``Ix.Kernel.RecursorRulePattern.matches_natLiteral },
  { root := ``Ix.Kernel.RecM.TrAppSpine.headConstN,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RecM.TrAppSpine.matches_natRecRulePrefix,
    standardAxioms := standard },
  { root := ``Ix.Kernel.RawRecursorRulePatternRel.matches_natLiteralPrefix,
    standardAxioms := standard },
  { root := ``Ix.Kernel.AmbientNat.linearRecTheoryPrefix_shape },
  { root := ``Ix.Kernel.AmbientNat.linearRecZeroPatternMatch },
  { root := ``Ix.Kernel.AmbientNat.linearRecSuccPatternMatch },
  { root := ``Ix.Kernel.TrustedNatRecursorLayout.caseForMajor,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSuffix.tr,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSpine.splitAt,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatRecLiteralPartsDescriptor.patternMajor,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatRecLiteralPartsDescriptor.translatedSplit,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrustedNatRecLiteralParts.translatedCase,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSuffix.startHasType,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSuffix.rebase,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RawRecursorRulePatternRel.checkedReduction,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatRecLiteralTranslationSplit.checkedRhsSuffix,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RegisteredRecursorRuleRhsRel.rhsRaw,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RegisteredRecursorRuleRhsRel.rhsStructural,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RegisteredRecursorRuleRhsRel.instUnivSpec,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RegisteredRecursorRuleRhsRel.instantiateUnivParams_nonempty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RawRecursorRuleRel.registeredRhsTyped,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSuffix.rebaseQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.NatRecLiteralTranslationSplit.checkedRhsSuffixQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KExpr.Constructed.liftNoIntern_eq_liftSpec,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KExpr.Constructed.substNoIntern_eq_substSpec,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applyIotaArg_true_lam_spec,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applyIotaArg_true_lam_run,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfMeaning.betaNoIntern,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.betaIotaArgRun,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.betaNoInternMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.IotaArgNonLambda.applyIotaArg_true,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.IotaArgNonLambda.applyIotaArg_true_run,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfMeaning.appRebuild,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applyIotaArg_true_nonlam_semantic,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applyIotaArg_false_eval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applyIotaArg_false_semantic,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.appStuckIotaTransient,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.appStuckIotaInterned,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfMeaning.resultQuot,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfMeaning.ofStructuralQuot,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KExpr.substNoIntern_of_lbr_le,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KExpr.liftNoIntern_of_lbr_le,
    standardAxioms := standardWithoutQuot,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applyIotaArgs_eq_foldlM,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.singleton,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.append,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.three,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.ApplyIotaArgsTrace.transientNonLambdaSingleton,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.ApplyIotaArgsTrace.transientNonLambdaSingletonQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.internedSingleton,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.transientLambdaSingleton,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.transientLambdaSingletonQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.evalList,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.evalArray,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.sourceTr,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.finalQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.finalInv,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.frame,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.finalSupport,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.acceptance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.evalThreeArrays,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.threeArrayAcceptance,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfMeaning.ofQuot,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.sourceQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.acceptanceQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaArgsTrace.threeArrayAcceptanceQuot,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.instantiateUnivParams_whnf_of_run,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaRuleTrace.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaRuleTrace.emptyInstantiation,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaRuleTrace.instantiatePost,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaRuleTrace.acceptance,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaRuleTrace.acceptance_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.ApplyIotaRuleTrace.registeredStartQuot_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.ApplyIotaRuleTrace.registeredAcceptance_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.ApplyIotaRuleTrace.registeredStartQuot_nonempty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.ApplyIotaRuleTrace.registeredAcceptance_nonempty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaRuleTrace.checkedMeaning,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.ApplyIotaRuleTrace.checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.ApplyIotaRuleTrace.checkedAcceptance_nonempty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KConst.recursorMajorIdx_of_iotaInfo,
    standardAxioms := propextOnly,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KConst.recursorRuleAt_of_iotaInfo,
    standardAxioms := propextOnly,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryApplyIotaCtorSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaCtorTrace.operational,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaCtorTrace.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaCtorTrace.recursorRuleAt,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaCtorTrace.acceptance_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaCtorTrace.checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ApplyIotaCtorTrace.checkedAcceptance_nonempty,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaCtorOrStructEta_regular,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaAfterMajorWhnf_regular,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaWithFlags_nonKPrefix,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaWithFlags_regularCtor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryIotaWithFlags_regularCtor_checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natToConstructor_zero,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natToConstructor_succ,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaAfterMajorWhnf_nat,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaWithFlags_natCtor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryIotaWithFlags_natCtor_checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.intern_success_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.strLitListToConstructor_empty,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.strLitListToConstructor_success_frame,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.strLitToConstructor_success_frame,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.evalNatOffsetLiteral_str,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natOffset_str,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.cleanupNatOffsetMajor_str,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaAfterMajorWhnf_str,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaWithFlags_strCtor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryIotaWithFlags_strCtor_checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaStringEmptyFold,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaStringExpand,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaStringCallback,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaStringCleanup,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaStringGetZeroOfFrame,
    standardAxioms := standard,
    nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaStringApplyRule,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaStringApplyCtor,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaStringAfterEval,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },

  -- ConstructorSynthesis: the positive K-like recursor branch.  Optional probes retain
  -- error-side state, candidate synthesis records the DefEq gate and counter
  -- order, and the inhabited fixture reaches the real bounded WHNF driver.
  { root := ``Ix.Kernel.RecM.tryOptional_success,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryOptional_error,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.VerifyKSynthCandidateSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.VerifyKSynthCandidateRejectTrace.eval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.SynthCtorWhenKSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaWithFlags_kPrefix,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaWithFlags_kFallback,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaWithFlags_kCtor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryIotaWithFlags_kCtor_checkedAcceptance_empty,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaIntern,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaMajorInfer,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaMajorWhnf,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaGetRec,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaGetNat,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaMajorInductive,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaCtorInfer,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaAttemptStats,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaTypeDefEq,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaCandidate,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaSynth,
    standardAxioms := standard,
    nativeAxioms := inferNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaInternFrame,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaSynthCleanup,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaSynthWhnf,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaGetZeroAfter,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaApplyRule,
    standardAxioms := standard, nativeAxioms := nameNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaApplyCtor,
    standardAxioms := standard, nativeAxioms := nameNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaTryEval,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaStepEval,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kIotaCoreEval,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },

  -- ConstructorSynthesisFallback: exhaustive K-synthesis fallback and error branches.
  { root := ``Ix.Kernel.RecM.verifyKSynthCandidate_inferMiss,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.verifyKSynthCandidate_inferError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.verifyKSynthCandidate_defEqError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.selectKSynthCandidate_mismatch,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.selectKSynthCandidate_missing,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.selectKSynthCandidate_nonInductive,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.selectKSynthCandidate_empty,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.selectKSynthCandidate_selected,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.selectKSynthCandidate_selectedError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.synthCtorWhenK_majorInferMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.synthCtorWhenK_majorInferError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.synthCtorWhenK_majorWhnfMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.synthCtorWhenK_majorWhnfError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.synthCtorWhenK_nonConstHead,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.synthCtorWhenK_recursorMissing,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.synthCtorWhenK_majorInductiveMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.synthCtorWhenK_majorInductiveError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.SynthCtorWhenKSelectionTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.SynthCtorWhenKSelectionTrace.mismatch,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.SynthCtorWhenKSelectionTrace.missing,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.SynthCtorWhenKSelectionTrace.nonInductive,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.SynthCtorWhenKSelectionTrace.empty,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.SynthCtorWhenKSelectionTrace.selected,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.SynthCtorWhenKSelectionTrace.selectedError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kMajorInferRawError,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kMajorInferCaughtMiss,
    standardAxioms := standard,
    nativeAxioms := inferNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kCandidateInferRawError,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kCandidateInferCaughtMiss,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kDefEqRawError,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kDefEqCandidateError,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kDefEqSynthError,
    standardAxioms := standard,
    nativeAxioms := inferNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kEmptyGetRec,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kEmptyGetNat,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kEmptyMajorInductive,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.kEmptyInductiveMiss,
    standardAxioms := standard,
    nativeAxioms := inferNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },

  -- StructEtaControl: exhaustive struct-eta classification, caught probes, rebuild,
  -- single-rule selection, and final constructor fallthrough.  Rebuilding is
  -- proved total; only universe instantiation can produce a post-guard error.
  { root := ``Ix.Kernel.RecM.isStructLike_missing,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isStructLike_nonInductive,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isStructLike_lookupError,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isStructLike_badShape,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isStructLike_shapeQualified,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isStructLike_recError,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishStructEtaResult_empty,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.structEtaIntern_total,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishStructEtaFields_total,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishStructEtaResult_of_segments,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishStructEtaResult_total,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishStructEtaResult_ne_error,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishStructEtaAfterSort_prop,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishStructEtaAfterSort_success,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishStructEtaAfterSort_instantiateError,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishStructEtaAfterSort_finishError,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaAfterInductive_notStruct,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaAfterInductive_structError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaAfterInductive_majorInferMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaAfterInductive_majorInferError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaAfterInductive_sortInferMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaAfterInductive_sortInferError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaAfterInductive_sortWhnfMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaAfterInductive_sortWhnfError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaProbeTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaProbeTrace.prop,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaProbeTrace.success,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaProbeTrace.finishError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaIota_ruleCount,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaIota_recursorMissing,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaIota_recursorError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaIota_majorInductiveMiss,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaIota_majorInductiveError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaSelectionTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaIotaSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaIotaSuccessTrace.acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Rebuild: the successful struct-eta rebuild derives its invariant, frame,
  -- and finite support from the exact projection/application request list.
  -- The registered Theory equation remains an explicit premise.
  { root := ``Ix.Kernel.RecM.StructEtaFieldRequests.support,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaFieldRequests.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaBuildRequests.eval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaIotaSuccessTrace.acceptance_of_requests,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- CallbackPrefix: the exact infer-only and optional-catch wrappers preserve the
  -- complete fixed-world invariant while retaining callback mutations.
  { root := ``Ix.Kernel.TcM.withInferOnly_eq,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.withInferOnly_whnf_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.inferOnlyRec_run,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryOptional_run,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryOptional_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.inferOnlyRec_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryOptionalInferOnlyRec_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryOptionalWhnfRec_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },

  -- RecursionClassifier: recursion classification now owns its complete concrete state
  -- transaction.  Both physical writes require explicit provenance; the
  -- final write is indexed by the exact classifier execution, and only
  -- errors inside that classifier enter the erase-and-rethrow handler.
  { root := ``Ix.Kernel.CacheInvariant.insertIsRec,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheInvariant.eraseIsRec,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsRecCacheUpdate.insert_whnfStateInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsRecCacheUpdate.erase_whnfStateInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsRecCacheWriteOracle.of_trusted,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.getConst_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.tryGetBlock_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.WhnfCallbackSupports.preserves,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.getMajorInductiveId_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.collectSpine_const_references,
    standardAxioms := propextOnly,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.getMajorInductiveId_trusted_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.discoverBlockInductives_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.computeIsRec_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.cacheIsRec_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.eraseCachedIsRec_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.computedIsRecClassify_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.computedIsRecMiss_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.computedIsRec_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },

  -- Classifier: compose the recursion classifier through `isStructLike`, then
  -- exhaust the single-rule recursor lookup and all three caught struct-eta
  -- probes.  Only the explicitly parameterized cache-write, callback, and
  -- successful universe/rebuild authorities remain outside these proofs.
  { root := ``Ix.Kernel.RecM.isStructLike_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryOptional_state_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryOptional_fixed_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaAfterInductive_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaIota_prefix_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaIota_trusted_prefix_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructEtaIota_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- RebuildTail: the universe-instantiation/rebuild tail now preserves the complete
  -- invariant from the finite execution request census, including retained
  -- intern-table updates on a non-backtracking walker error.
  { root := ``Ix.Kernel.TcM.instantiateUnivParams_whnf_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaBuildRequests.wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishStructEtaAfterSort_wf_of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },

  -- CacheShell: both structural-core cache partitions now have explicit
  -- collision-robust write authority, and the actual public dispatcher is
  -- closed conditionally on the remaining exhaustive structural step.
  { root := ``Ix.Kernel.RecM.WhnfCoreCacheWriteOracle.closed,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfSuffixModel.coreCacheWriteOracle,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsNonLeaf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlags_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- BasicStep: immediate leaves, the complete fvar split, and explicit-let
  -- substitution now share one local structural-step contract.  The fvar
  -- theorem exposes the real unchanged-value safety invariant rather than
  -- inferring closedness or arithmetic bounds from translation alone.
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_fvar_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_letE_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_basic_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- VariableStep: legacy zeta now derives its semantic weakening from the exact
  -- lift-walker bounds.  The only additional safety fact is the real
  -- UInt64 `idx + 1` no-wrap condition on an actual let-value hit.
  { root := ``Ix.Kernel.CtxRecon.lookupLetVal_liftBounds,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.lookupLetVal_noLet,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfMeaning.zetaVar_liftBounds,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_var_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_basicVar_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  
  -- RecursiveCallbacks: projection values and application-spine children now have an
  -- explicit finite-support boundary, and both recursive head callbacks are
  -- instantiated directly from the predecessor method-table contract.
  { root := ``Ix.Kernel.RecM.whnfCoreFlagsRec_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSpine.headTr,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.projectionValueCallback_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applicationHeadCallback_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applicationArgument_support,
    standardAxioms := propextOnly,
    forbiddenDependencies := legacyWholeEnv },

  -- ProjectionStep: all projection-step outcomes now satisfy the local structural
  -- contract once the exact helper effect/result boundary is instantiated;
  -- callback and helper errors retain their partial post-state.
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_projection_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_basicVarProjection_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- ApplicationCongruence: the application-head callback is tied to the exact typed suffix,
  -- and Theory application congruence transports head reduction across every
  -- argument rebuilt by the finite production certificate.
  { root := ``Ix.Kernel.RecM.TrAppSpine.toSuffix,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applicationHeadCallbackWithSuffix_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.WhnfMeaning.appHeadRebuild,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- ApplicationRebuild: a finite census now executes each dynamic changed-head rebuild and
  -- returns its exact intern frame, support, and transported Theory meaning.
  { root := ``Ix.Kernel.RecM.changedHeadFinish_acceptance,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- ApplicationTails: both non-beta application tails are exhaustive over iota hit,
  -- miss, and error.  Changed-head hits compose rebuild congruence with the
  -- helper result; unchanged misses remain reflexive at the original source.
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appUnchangedIota,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appUnchanged_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfCoreWithFlagsStep_appChanged_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- NoAccelTail: the actual no-acceleration projection tail now forces the
  -- Fin/Decidable probe to miss, preserves lazy constructor lookup state,
  -- and derives selected-field support from the concrete collected spine.
  -- Only String preprocessing and the installed lazy-ingress hook remain at
  -- the public helper constructor.
  { root := ``Ix.Kernel.RecM.WhnfCoreInputSupport.spineArg,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryProjReduceTail_noAccel_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ProjectionPrelude.nonString,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ProjectionPrelude.ofString,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryProjReduce_noAccel_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ProjectionHelper.noAccel,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ProjectionStringPrelude.ofExpansion,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ProjectionHelper.noAccelOfExpansion,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  -- StringExpansion: the remaining String-expansion premise is reduced to a pure,
  -- finite plan.  The actual primitive read, seven prefix interns, recursive
  -- character fold, and final intern preserve the complete WHNF invariant and
  -- return the exact structurally translated generated expression.
  { root := ``Ix.Kernel.RecM.strLitListToConstructor_plan_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.strLitToConstructorWithPrimitives_plan_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.strLitToConstructor_plan_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ProjectionStringExpansion.ofPlans,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ProjectionHelper.noAccelOfStringPlans,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  -- LazyIngress: instantiate the generic lazy-fault plumbing with production's
  -- anonymous shallow-ingress callback.  The outcome refinement explicitly
  -- covers a successful load, an absent address, and an error-carried partial
  -- environment; hook identity remains visible because `TcState.lazyFault`
  -- otherwise stores an arbitrary function.
  { root := ``Ix.Kernel.LazyIngressEnvFrame.refl,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.LazyIngressEnvFrame.kernelStateWF,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.LazyIngressEnvFrame.ctxRecon,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.LazyIngressEnvFrame.whnfStateInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ingressAnonAddrShallow_absent,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AnonIngressRefinement.absentOfVerifiedMiss,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AnonIngressRefinement.error,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AnonIngressRefinement.lazyFaultPreserves,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AnonLazyIngressContext,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AnonLazyIngressContext.preserves,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.ProjectionHelper.noAccelOfAnonIngress,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  -- NatOffset: the actual post-major iota preprocessing path.  Bounded Nat-offset
  -- parsing, Nat constructor expansion, cleanup, lazy constructor lookup,
  -- finite String expansion, the policy-selected recursive callback, and the
  -- constructor/struct-eta dispatch all preserve the complete WHNF invariant.
  -- Only the ordinary-constructor and struct-eta tails remain named inputs.
  { root := ``Ix.Kernel.RecM.prims_state_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isNatBinArithAddr_state_wf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natOffsetReaders_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natOffset_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.evalNatOffsetLiteral_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natToConstructor_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.mkNatSucc_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.mkNatAdd_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.WF.with_run_eq,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.OptionalGeneratedInput,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatOffsetCleanupInputOracle,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.cleanupNatOffsetMajor_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.cleanupNatOffsetMajor_input_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryApplyIotaCtorPreserves,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaIotaPreserves,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.SelectedStructEtaIotaPreserves,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaCtorOrStructEta_state_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.strLitToConstructor_context_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaAfterCleanup_state_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaAfterMajorWhnf_state_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- ApplicationRequests--Ingress: finite ordinary-iota, struct-eta, and K-synthesis request
  -- censuses close every generated-expression effect.  Their composition
  -- exhausts the actual tryIotaWithFlags state path through lazy lookup,
  -- caught probes, both cleanup stages, policy-selected major callbacks,
  -- statistics updates, and the final uncaught DefEq callback.
  { root := ``Ix.Kernel.RecM.IotaArgsInternRequests,
    standardAxioms := standardWithoutQuot, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IotaArgsInternRequests.wfList,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IotaArgsInternRequests.wfArray,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applyIotaArg_true_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applyIotaArgs_true_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IotaRuleRequests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IotaRuleRequestCensus,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.applyIotaRule_state_wf_of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryApplyIotaCtor_state_wf_of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryApplyIotaCtorPreserves.of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaFinishRequests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaFinishRequestCensus,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaFinishPreserves.of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructEtaIotaPreserves.of_components,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaAfterMajorWhnf_state_wf_of_contexts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsDefEqCallbackPreserves,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.WF.tryFinally_const,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.enterDispatch_whnf_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.exitDispatch_whnf_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.callIsDefEq_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.KSynthCandidateRequests,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.KSynthCandidateRequestCensus,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.KSynthCandidateInputs,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.KSynthCandidateInputOracle,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.FinishAppRequests.state_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.verifyKSynthCandidate_state_wf_of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.selectKSynthCandidate_state_wf_of_requests,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.synthCtorWhenK_state_wf_of_requests,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.verifyKSynthCandidate_state_wf_of_inputs,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.selectKSynthCandidate_state_wf_of_inputs,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.synthCtorWhenK_state_wf_of_inputs,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaWithFlags_state_wf_of_contexts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- OptionalReduction: the exhaustive state proof and the direct admission-owned success
  -- boundary assemble the ordinary optional-reduction contract.  The success
  -- boundary contributes support and Theory meaning only; it cannot hide an
  -- error-side or miss-side state assumption.
  { root := ``Ix.Kernel.IotaCallbackFrameOracle,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.IotaSuccessOracle,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaWithFlags_optional_wf_of_contexts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  -- Reducer: the structural contract is indexed by the actual universe/context
  -- represented by the cache model.  The assembled theorem feeds OptionalReduction into
  -- the exhaustive syntax step and then through the bounded/cache driver.
  { root := ``Ix.Kernel.StructuralReduction.WF,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructuralCoreContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.StructuralCoreContext.wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- ProjectionApplication: projection-application reduction is exhaustive over empty and
  -- non-projection misses, both callback/helper error seams, helper misses,
  -- and successful projection followed by a certified complete-spine
  -- rebuild.  Head meaning is transported through the typed suffix rather
  -- than inferred from expression-address equality.
  { root := ``Ix.Kernel.RecM.tryProjAppReduce_empty,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryProjAppReduce_notProjection,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryProjAppReduce_projectionWhnfError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryProjAppReduce_projectionReduceError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryProjAppReduce_projectionNone,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryProjAppReduce_projectionSome,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryProjAppReduceFinished_empty_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryProjAppReduceFinished_app_optional_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryProjAppReduceFinished_optional_wf_of_contexts,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- StringPrimitive: the production String primitive helper is exhaustive over every
  -- classifier miss and all three hits.  Its state proof derives finite
  -- generated-node support at each intern; the reflection boundary owns
  -- only Theory meaning for an observed successful run.
  { root := ``Ix.Kernel.StringReductionSupport,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.StringReductionReflection,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceString_inv_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceString_optional_wf_of_reflection,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  -- ProjectionDefinition: projection-wrapper reduction covers the real lazy constant lookup,
  -- the generated projection, and every suffix intern.  The request plan
  -- exposes all intermediate support obligations instead of assuming that
  -- support for the final node retroactively makes those interns safe.
  { root := ``Ix.Kernel.ProjectionDefinitionRequestCensus,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ProjectionDefinitionReflection,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.projectionDefinitionFinish_eq,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.FinishAppRequests.finishAppResult_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceProjectionDefinition_inv_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryReduceProjectionDefinition_optional_wf_of_contexts,
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
  { root := ``Ix.Kernel.QuotientReductionRequestCensus,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.QuotientReductionReflection,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.QuotientReductionLaws,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSpine.three,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSpine.four,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSpine.five,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrKExprS.const_name,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.quotientLiftMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.quotientIndMeaning,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.QuotientSelectedSuccessTrace.complete,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.QuotientSelectedSuccessTrace.semanticInputs,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.QuotientSelectedSuccessTrace.liftMeaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.QuotientSelectedSuccessTrace.indMeaning,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.QuotientReductionReflection.of_laws,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryQuotReduceSelected,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryQuotReduceSelected_inv_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryQuotReduce_inv_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryQuotReduce_optional_wf_of_contexts,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  -- BaseReductions: the five active no-acceleration reducers are assembled into the
  -- exact production base oracle for either successor policy.  Native and
  -- BitVec remain independently discharged by the no-acceleration gate.
  { root := ``Ix.Kernel.RecM.NoDeltaBaseContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NoDeltaBaseContext.oracle,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- Reducer: Reducer's structural reducer and BaseReductions's active base oracle now feed
  -- the real bounded, keyed, transient-aware, cache-writing public
  -- `whnfNoDeltaImpl` shell for every flag and successor policy.
  { root := ``Ix.Kernel.RecM.NoDeltaDriverContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NoDeltaDriverContext.wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- FullStep--Closure: the exhaustive full-WHNF step is connected to exact
  -- definition/theorem certificates.  Stable unfold-cache provenance covers
  -- warm and cold paths, typed suffix rebuilding covers applied heads, and
  -- the bare fallback closes `deltaUnfoldOne`.  The final cache composition
  -- and method knot are indexed by the active universe count; concrete lazy
  -- ingress is carried by `AnonLazyIngressContext`, not a free callback.
  { root := ``Ix.Kernel.OptionalReduction.WFAt,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TrustedDeltaBody.meaning,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.StableWhnfTheory,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TrustedDeltaBody.unfoldCacheProvenance,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.unfoldConstValue_trusted_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TrustedDeltaCensus,
    standardAxioms := standard, nativeAxioms := univOnlyNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryDeltaUnfold_trusted_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.deltaUnfoldOne_trusted_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrustedDeltaContext,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrustedDeltaContext.wfAt,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.FullWhnfStepContext.ofTrustedDelta,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.WhnfClosedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.Methods.methodsN_wfAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.K1ClosureContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.K1ClosureContext.closedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.AmbientNat.structEtaInferOnlyRun,
    standardAxioms := standard, nativeAxioms := expressionNameNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structEtaOptionalInferOnlyRun,
    standardAxioms := standard, nativeAxioms := expressionNameNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaCtorOrStructEta_nonConst,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaCtorOrStructEta_missing,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaCtorOrStructEta_notConstructor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaCtorOrStructEta_lookupError,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryIotaCtorOrStructEta_constructor,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structEtaIotaSuccess,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structEtaBuildRequests,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structEtaDispatchSuccess,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structEtaIotaAbsent,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structEtaIotaCaughtInferError,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := legacyWholeEnv },

  { root := ``Ix.Kernel.AmbientNat.iotaCleanupOfNatValue,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaNatCleanup,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaNatCtorCleanup,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaNatMajorWhnf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaNatZeroExpand,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaNatSuccExpand,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaNatApplyRule,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaNatApplyCtor,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaNatTryEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaNatStepEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaNatCoreEval,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaApplyRule,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaApplyCtor,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.support_le_iotaArgsSupport,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaArgsStateInv,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaArgsSupport_head,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.iotaArgsSupport_source,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.appStuckIotaTransientThreeSegments,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaFirstResult,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaSecondResult,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.appStuckHead_constructed,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiBetaInner_constructed,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaIntermediate_constructed,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.appStuckHead_tr_ctx,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.appStuckHead_type_ctx,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaIntermediate_tr,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.support_le_multiIotaSupport,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaStateInv,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaSupport_start,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaSupport_intermediate,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaSupport_head,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaSupport_result,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaFirstTrace,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaSecondTrace,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaThirdTrace,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaTransientThreeSegments,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaPrefixSlice,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaFieldSlice,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaTrailingSlice,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaRuleEval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaRuleAcceptance,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaCtorEval,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiIotaCtorAcceptance,
    standardAxioms := standard, nativeAxioms := levelNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.missingRuleDescriptor,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.AmbientNat.missingRuleDescriptor_noZeroRule,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.AmbientNat.multiBetaMiddleSplit,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.multiBetaMiddleRebase,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.linearRecPartsRun,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.AmbientNat.linearRecPartsTrace,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.TcM.LazyFaultPreserves.of_none,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.natRecLiteralParts_wf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.NatRecLiteralPartsPreserves.of_lazy,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatRecLiteralPartsPreserves.eager,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isNatLiteralRecursorApp_wf,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.isTransientNatLiteralWork_wf,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.TransientNatWork.preserving,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isTransientNatLiteralWork_noLazy,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.TransientNatWork.eager,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },

  -- ordered no-delta reduction: the production no-delta tail has an explicit seam.  Exact equations
  -- pin projection-app completion, every ordered success/fallback branch, and
  -- every partial error state.  The semantic package composes structural and
  -- reducer meanings, while the closed Nat.add fixture makes precedence
  -- executable and records its three canonical-address decisions explicitly.
  { root := ``Ix.Kernel.RecM.tryProjAppReduceFinished_some,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.tryProjAppReduceFinished_none,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.tryProjAppReduceFinished_projError,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.tryProjAppReduceFinished_finishError,
    standardAxioms := standard, nativeAxioms := expressionNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_projApp,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_bitvec,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_nat,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_native,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_string,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_projectionDef,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_quotFull,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_quotCheap,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_doneFull,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_doneCheap,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_projError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_bitvecError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_natError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_nativeError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_stringError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_projectionDefError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_quotFullError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_quotCheapError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplStep_ofCore,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplStep_coreError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplStep_reducerError,
    standardAxioms := standard, nativeAxioms := inferNative },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplStep_next_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplStep_done_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplStep_error_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.noDeltaNatAddReduction,
    standardAxioms := standard, nativeAxioms := natReductionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.noDeltaNatBranchOrder,
    standardAxioms := standard, nativeAxioms := natBranchOrderNative,
    forbiddenDependencies := legacyWholeEnv },

  -- primitive reduction: `.noAccel` concretely discharges the native and BitVec optional
  -- reducers.  The five active helpers remain an explicit base oracle, which
  -- now feeds the exhaustive tail, outer step, and public no-delta shell.
  { root := ``Ix.Kernel.RecM.tryReduceNative_noAccel_optional_wf,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceBitvec_noAccel_optional_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.NoDeltaBaseOracle.toNoAccel,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaReducersStep_noAccel_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplStep_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImplStep_noAccel_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNoDeltaImpl_noAccel_wf_of_base,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- WHNF layer policy: production WHNF layers bind every observable primitive-table
  -- address to `PrimAddrs.canonical`; the separate structural layer retains
  -- table-parametric syntax tests without being eligible for production
  -- reducer closure.  The world/context interface then binds the active Nat,
  -- String, projection, and quotient IDs to trusted Theory names and scopes
  -- generated results to actual successful helper executions.
  { root := ``Ix.Kernel.Primitives.ofAnonAddrs_canonical,
    standardAxioms := standard, nativeAxioms := canonicalPrimitivesNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfStateInv.noAccel_primitives,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfStateInv.accelerated_primitives,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.PrimitiveIdAgrees.contains,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.PrimitiveIdAgrees.mono,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.NoDeltaPrimitiveTableAgrees.mono,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.NoDeltaPrimitiveContext.stateTable,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  -- Nat reducer callback: the Nat reducer's shared callback/fuel boundary and exact binary
  -- arithmetic hit.  The primitive computation is derived from the bound
  -- canonical table and Ix.Theory.Named reflection laws; no raw address equality
  -- is treated as semantic authority.
  { root := ``Ix.Kernel.WhnfStateInv.set_recFuel,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.WF.tryCatch,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfRec_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNatReducerArg_post_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNatReducerArg_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.NoDeltaPrimitiveContext.computeNatBin_defeq,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TrKExprS.of_extractNatLit,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TrKExprS.natExprFromValue,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TrKExprS.natBinExact_inv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfPost.of_extractNatLit,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfMeaning.natBinExact,
    standardAxioms := standard, sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binArithExact,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binArithExact_acceptance,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- Nat primitive classification: canonical classifier derivation and exact Bool-predicate hits.  The
  -- generic proof uses trusted-name separation instead of native hash
  -- inequalities, and the finite Bool intern is checked against explicit run
  -- collision freedom and generated-node support.
  { root := ``Ix.Kernel.TcM.intern_whnf_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.intern_whnf_eval,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.PrimitiveIdAgrees.addr_ne,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.NoDeltaPrimitiveContext.computeNatBin_classifiers,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.NoDeltaPrimitiveContext.natPredicate_classifiers,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.NoDeltaPrimitiveContext.natPredicate_defeq,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TrKExprS.boolExprFromDecision,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatPredicate_exact,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binPredExact,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binPredExact_acceptance,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  -- binary Nat early-out: exhaustive early-out traces and state closure for exact binary Nat
  -- reduction.  Callback errors retain their partial state, arithmetic and
  -- predicate extraction order is pinned, and the complete two-argument
  -- dispatcher preserves the invariant on every outcome.
  { root := ``Ix.Kernel.RecM.WF.withInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.prims_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isNatBinArithAddr_inv_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isNatBinPredAddr_inv_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNatReducerArg_ok_inv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.whnfNatReducerArg_error_inv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatPredicate_bin_inv_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_bin_inv_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatPredicate_argAMiss,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatPredicate_argAError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatPredicate_extractAMiss,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatPredicate_argBMiss,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatPredicate_argBError,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatPredicate_extractBMiss,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binPredMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binPredError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binArithArgAMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binArithArgAError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binArithArgBMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binArithArgBError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binArithExtractAMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binArithExtractBMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binArithComputeMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  -- binary Nat success: every successful exact-binary Nat run is inverted into its actual
  -- callback/extraction/computation-or-intern trace, then folded into a
  -- semantic optional-reduction Hoare slice.  Predicate precedence remains
  -- operationally exhaustive even before canonical classifier separation.
  { root := ``Ix.Kernel.RecM.isNatBinArithAddr_eval,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isNatBinPredAddr_eval,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isNatBinPredAddr_true,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binPredAnyExact,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatPredicateSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatPredicateSuccessTrace.complete,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatBinSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatBinSuccessTrace.complete,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatBinSuccessTrace.acceptance,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_bin_optional_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.structuralInvariant_does_not_bind_primitives,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.productionNoAccelStateInv,
    standardAxioms := standard, nativeAxioms := nameNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.noAccelInvariant_rejects_mismatched_primitives,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Nat suffix reduction: production `collectSpine` is reconciled with a typed structural
  -- spine, exact Nat equations are transported over arbitrary unchanged
  -- argument suffixes, and finite rebuild certificates preserve state and
  -- support.  Successful general-spine executions are inverted exhaustively.
  { root := ``Ix.Kernel.RecM.appSpineView_go,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.appSpineView_collectSpine,
    standardAxioms := standardWithoutChoice },
  { root := ``Ix.Kernel.RecM.trAppSpine_of_tr,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSpine.argument,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSpine.tr,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.trAppSpine_of_collectSpine,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TrKExprS.foldlMkApp_initial,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfMeaning.appSameArg,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfMeaning.foldlMkApp,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfMeaning.mkAppN,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfMeaning.ofSharedSourceTranslation,
    standardAxioms := standard, sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatPredicate_suffixExact,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binPredSuffixExact,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binArithSuffixExact,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binArithSuffix_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_binPredSuffix_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatPredicateSuffixSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatPredicateSuffixSuccessTrace.complete,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatSpineSuccessTrace.eval,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatSpineSuccessTrace.complete,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.noDeltaNatAddSuffixSpine,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.noDeltaNatAddSuffixFinishRequests,
    standardAxioms := standard,
    nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.noDeltaNatAddSuffixReduction,
    standardAxioms := standard, nativeAxioms := natSuffixReductionNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Nat suffix closure: all general-spine misses and callback errors preserve the full
  -- invariant without suffix assumptions.  A successful trace is enriched
  -- with only its observed finite rebuild requests, then interpreted as the
  -- fixed-state optional-reduction Hoare contract.  The over-applied Nat.add
  -- fixture inhabits that execution-indexed coverage boundary.
  { root := ``Ix.Kernel.RecM.finishAppResult_total,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natBinSpine_inputs,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatPredicate_spine_nonhit_inv,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_spine_nonhit_inv,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatSpineCertifiedSuccess.trace,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatSpineCertifiedSuccess.acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_spine_optional_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.noDeltaNatAddSuffixCertifiedSuccess,
    standardAxioms := standard, nativeAxioms := natSuffixCertificateNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.noDeltaNatAddSuffixFinishCoverage,
    standardAxioms := standard, nativeAxioms := natSuffixReductionNative,
    forbiddenDependencies := legacyWholeEnv },

  -- successor-collapse loop: the production successor-collapse loop is split into named seams
  -- whose entry, callback, literal, peel, memo-hit, memo-miss, and partial-
  -- error equations are exhaustive.  Stuck-marker writes preserve the full
  -- cache/state invariant only under explicit per-key provenance.  The
  -- closed Nat.succ fixture runs through the actual dispatcher and bounded
  -- driver without mutating the state.
  { root := ``Ix.Kernel.CacheInvariant.insertNatSuccStuck,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheInvariant.insertNatSuccStuckList,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheInvariant.insertNatSuccStuckArray,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatSuccStuckCacheUpdate.fold_whnfStateInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccIter_entryHit,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccIter_entryKeyError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccIter_entryMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccIterStep_linearHit,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccIterStep_linearError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccIterStep_whnfError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccIterStep_afterWhnf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccAfterWhnf_literal,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccAfterWhnf_stuck,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.recordNatSuccStuck_eval,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.recordNatSuccStuck_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccPeel_keyError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccPeel_afterKey,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccPeelAfterKey_hit,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccPeelAfterKey_miss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccPeelMiss_keyError,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccPeelMiss_next,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccAfterWhnf_succ,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_succ_stuck,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_succ_collapse,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.succCollapseSpine,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.succCollapseLinearMiss,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.succCollapseWhnf,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.succCollapseExtract,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.succCollapseStep,
    standardAxioms := standard,
    nativeAxioms := contextNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.succCollapseKey,
    standardAxioms := standard,
    nativeAxioms := contextNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.succCollapseMemoMiss,
    standardAxioms := standard,
    nativeAxioms := expressionNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.succCollapseIter,
    standardAxioms := standard,
    nativeAxioms := contextNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.succCollapseReduction,
    standardAxioms := standard,
    nativeAxioms := contextNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },

  -- successor-collapse semantics: semantic closure of the actual successor-collapse loop.  Negative
  -- memo markers are semantically inert but retain exact source/reference
  -- provenance; the ghost loop state tracks Nat typing, arbitrary successor
  -- offsets, and every pending marker.  Linear Nat.rec recognition remains
  -- behind its explicit oracle until inductive iota semantics instantiate it.
  { root := ``Ix.Kernel.WhnfCacheValid.natSuccStuck,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheProvenance.whnfNatSuccStuck,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatSuccStuckWriteOracle.forWhnfCache,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natSucc_hasType,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natSuccSpine_tr,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccPeel_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccAfterWhnf_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccIterStep_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccIter_wf,
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
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_succ_optional_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.NatCollapseRequestCensus.suffix_eq_empty_of_result_shape,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatCollapseRequestCensus.of_no_suffix,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatCollapseRequestCensus.of_result_shape,
    standardAxioms := standard, nativeAxioms := contextNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatCollapseRequestCensus.certify,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isNatSuccIhStep_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatSuccLinearRec_effect_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatSuccLinearOracle.of_reflection,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_collapse_optional_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_collapse_optional_wf_of_boundaries,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_stuck_short,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_stuck_optional_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_stuck_optional_wf_of_boundary,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_optional_wf_of_boundaries,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.tryReduceNatWithSuccMode_optional_wf_of_lazy_boundaries,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.AmbientNat.succStuckReduction,
    standardAxioms := standard,
    nativeAxioms := contextNative.push nameDecideNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Suffix semantics reduce open-context cache validity to one explicit
  -- operational model.  The recursive method table closes by induction from
  -- an exact one-layer contract split between WHNF and Infer/DefEq ownership.
  { root := ``Ix.Kernel.WhnfSuffixModel.keyRepresents,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfSuffixModel.cacheWriteOracle,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.Methods.LayerWF.of_parts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.Methods.Closed.of_parts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.Methods.methodsOut_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.Methods.methodsN_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.runRec_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Exact meanings for the remaining cache families. A
  -- positive DefEq result carries Theory equality; negative results are
  -- intentionally vacuous for the one-way soundness claim.
  { root := ``Ix.Kernel.InferMeaning.mono,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.InferMeaning.post,
    standardAxioms := standard, sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.InferCacheValid.mono,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheInvariant.inferHitOfMatches,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.DefEqMeaning.mono,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.DefEqMeaning.of_translations,
    standardAxioms := standard, sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.DefEqCacheValid.mono,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheProvenance.kernelWhnfMeaningOfMatches,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheProvenance.kernelInferMeaningOfMatches,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheProvenance.kernelDefEqMeaning,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },

  -- Production key executions generate the canonical operational
  -- context witnesses.  Physical inference/DefEq writes preserve every
  -- cache partition, including the rejection-only same-head failure set.
  { root := ``Ix.Kernel.CacheInvariant.insertInfer,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheInvariant.insertInferOnly,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheInvariant.insertDefEq,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheInvariant.insertDefEqCheap,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheInvariant.insertDefEqFailure,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.ctxAddrForLbr_empty,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.whnfKey_ctx,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.operationalWhnfContextKeys.represents,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.operationalWhnfContextKeys.representsCtx,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ContextDigestSpec.execution,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ContextDigestSpec.StateValid,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ContextDigestSpec.memoValid,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ContextDigestSpec.preserves,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.ctxAddrForLbr_trivial,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.ctxAddrForLbr_cacheHit,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.ctxAddrForLbr_cacheMiss,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.ctxAddrForLbr_replay,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.ContextAddrMemoValid,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.ctxAddrForLbr_memoValid,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.scopedOperationalWhnfContextKeys.represents,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.scopedOperationalWhnfContextKeys.representsCtx,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.scopedOperationalWhnfContextKeys.digest_eq,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.scopedOperationalWhnfContextKeys.mem,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.WhnfSuffixModel.operational,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.inferKey_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.inferKey_operational_matches_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.inferWith_fullHit,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.inferWith_inferOnlyHit,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.InferCacheUpdate.full_whnfStateInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.InferCacheUpdate.inferOnly_whnfStateInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },

  -- The union-find frame and joint suffix model keep composite context-hash
  -- transport explicit for WHNF, inference, and DefEq.  Collision-robust
  -- provenance constructors quantify over every supported address peer.
  { root := ``Ix.Kernel.TcM.withEquiv_eq,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.withEquiv_whnf_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.defEqCtxKey_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.defEqCtxKey_operational_matches_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.DefEqMeaning.of_addr_beq,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.DefEqMeaning.symm,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KernelSuffixModel.toWhnfSuffixModel,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KernelSuffixModel.operational,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ContextSuffixSemantics.whnf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ContextSuffixSemantics.infer,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ContextSuffixSemantics.defEq,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ScopedKernelSuffixModel.represents,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ScopedKernelSuffixModel.StateInScope,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ScopedKernelSuffixModel.whnfTransport,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ScopedKernelSuffixModel.inferTransport,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ScopedKernelSuffixModel.defEqTransport,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ScopedKernelSuffixModel.finiteOperational,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.ScopedKernelSuffixModel.toKernelSuffixModel,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KernelSuffixModel.finiteOperational,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheProvenance.kernelDefEqMeaningCanonical,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KernelSuffixModel.inferProvenance,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KernelSuffixModel.defEqProvenance,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.KernelSuffixModel.defEqFailureProvenance,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqCacheUpdate.full_whnfStateInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqCacheUpdate.cheap_whnfStateInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqCacheUpdate.failure_whnfStateInv,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },

  -- Production inference/conversion branches: both inference hit partitions, collision-
  -- safe DefEq address reflexivity, and a positive full DefEq hit including
  -- canonical ordering and its final union-find mutation.
  { root := ``Ix.Kernel.RecM.isDefEq_fullHit_true,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isDefEq_fullHit_true_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isDefEq_addrEq_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.inferWith_fullHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.inferWith_inferOnlyHit_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The memoized proposition classifier closes proof irrelevance's sole
  -- auxiliary cache family.  Positive hits and writes are tied to `Sort 0`
  -- through expression collision freedom and the explicit suffix model.
  { root := ``Ix.Kernel.RecM.isPropType_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryProofIrrel_classifier_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Lazy delta is a bounded semantic state machine.  These roots expose the
  -- pair invariant, the fuel-bounded closure, and the exact remaining
  -- obligations for one iteration and the stopped continuation.
  { root := ``Ix.Kernel.RecM.DefEqPairInvariant.refl,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqPairInvariant.conclude,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.runDefEqLazyDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isDefEqInnerAfterProofIrrelevance_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqAfterProofIrrelevance.ofLazyDelta,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- The front of each lazy-delta iteration now closes the actual Nat-offset
  -- literal/zero guards and both ordinary Nat-reduction attempts.  Structural
  -- offset decomposition and the post-Nat reducer tiers remain explicit
  -- continuation contracts; negative recognizer results carry no semantics.
  { root := ``Ix.Kernel.RecM.isNatZero_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsNatZero.ofContext,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryDefEqOffset_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryDefEqOffset.ofContext,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.defEqLazyDeltaStepAfterOffsetMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqLazyDeltaAfterOffsetMiss.ofNat,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.defEqLazyDeltaStepAfterNatMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqLazyDeltaAfterNatMiss.ofNoAccel,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.classifyDeltaHead_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.defEqLazyDeltaStepAfterAcceleratorMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.DefEqLazyDeltaAfterAcceleratorMiss.ofClassification,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryUnfoldProjApp_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.defEqLazyDeltaStepAfterDeltaClassification_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.DefEqLazyDeltaAfterDeltaClassification.ofProjection,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.finishDefEqLazyDeltaStep_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.defEqLazyDeltaStepWithLeftDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.defEqLazyDeltaStepWithRightDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.rankDeltaHead_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.defEqLazyDeltaStepAfterProjectionMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqLazyDeltaAfterProjectionMiss.ofRankDispatch,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.defEqLazyDeltaStepAfterSameHeadMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqLazyDeltaAfterSameHeadMiss.ofReduction,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Equal-rank closure: recursive spine arguments, constant-universe
  -- congruence, and the rejection-only failure-cache shell.  A cache hit can
  -- only skip the comparison; every positive result still comes from the
  -- semantic same-head proof.
  { root := ``Ix.Kernel.RecM.allDefEqSpineArgs_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrAppSpine.defEq_of_zip,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.sameDefEqUniverses_sound,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.constantHeadsDefEq,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.trySameHeadSpine_wf,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrySameHeadSpine.ofResources,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.CacheEntry.defEqFailureReferencesAuthorized,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.DefEqFailureCacheResources.ofKernelSuffixModel,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isRegular_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.trySameHeadSpineSpeculative_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.trySameHeadSpineCached_wf,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TrySameHeadSpineCached.ofResources,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.defEqLazyDeltaStepWithEqualRank_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqLazyDeltaEqualRank.ofPrefix,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqLazyDeltaEqualRank.ofKernelResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The Nat-offset candidate branch is state-safe on every parser and rebuild
  -- path.  Its only semantic input is an exact successful-run reflection;
  -- recursive equality is transported forward through the common successor
  -- suffix, without assuming offset injectivity or completeness.
  { root := ``Ix.Kernel.TcM.WF.withInvRunEq,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natOffsetDecompose_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natOffsetRebuild_state_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryDefEqOffsetAfterCandidates_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryDefEqOffsetAfterCandidates.ofContext,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The stopped continuation now closes its exact outer control flow.  The
  -- general app probe reconstructs equality through both typed spines;
  -- structural congruence proves constants and variables directly and
  -- delegates matching projections to one execution-indexed helper contract.
  { root := ``Ix.Kernel.RecM.tryDefEqApp_wf,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryDefEqApp.ofResources,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryStructuralCongruence_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryStructuralCongruence.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isDefEqAfterLazyDeltaStopped_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqAfterLazyDeltaStopped.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqLazyDeltaContext.ofKernelResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.DefEqAfterProofIrrelevance.ofKernelResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The structural projection callback's bounded lazy-delta driver preserves
  -- the original projected semantics across delta steps, direct projection
  -- reduction, recursive comparison, and normal depth exhaustion.
  { root := ``Ix.Kernel.RecM.lazyDeltaProjReduction_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.LazyDeltaProjReduction.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Direct projection reduction gets state/support closure from the proved
  -- no-acceleration helper and consults semantic reflection only for the
  -- exact successful execution that occurred.
  { root := ``Ix.Kernel.RecM.tryProjReduce_direct_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryProjReduce.ofDirectResources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },

  -- The compact projection-loop delta step exposes its two lazy declaration
  -- classifications as a proved prefix; the exact branch continuation sees
  -- only their concrete results.
  { root := ``Ix.Kernel.RecM.lazyDeltaReductionStep_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.LazyDeltaReductionStep.ofClassification,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.lazyDeltaReductionStepAfterClassification_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.LazyDeltaReductionAfterClassification.ofActive,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.LazyDeltaReductionStep.ofActive,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- Once classification reports an active delta head, the compact step is
  -- exhaustive: projection hits enter the productive finish, misses select
  -- one- or two-sided unfolding, and equal ranks try same-head congruence
  -- before normalizing both sides.  The final two roots assemble that branch
  -- proof with the already-audited classifier prefix.
  { root := ``Ix.Kernel.RecM.finishLazyDeltaReductionStep_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.lazyDeltaReductionStepWithLeftDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.lazyDeltaReductionStepWithRightDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.lazyDeltaReductionStepAfterSameHeadMiss_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.lazyDeltaReductionStepWithEqualRank_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.defRankId_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.lazyDeltaReductionStepWithBothDelta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.lazyDeltaReductionStepAfterActive_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.LazyDeltaReductionAfterActive.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.LazyDeltaReductionStep.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Concrete projection-loop assembly derives the compact step, bounded
  -- projection comparison, and structural-congruence projection branch from
  -- named lower reducers.  The exact-run direct projection reflection is the
  -- remaining semantic boundary; the outer loop itself is no longer one.
  { root := ``Ix.Kernel.RecM.ProjectionDeltaClosureResources.loop,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.LazyDeltaProjReduction.ofClosureResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.TryStructuralCongruence.ofProjectionDeltaResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The stopped continuation now derives its structural field from the
  -- concrete projection loop and reuses that record's core/quick resources;
  -- only application-spine and final-WHNF contracts remain as sibling inputs.
  { root :=
      ``Ix.Kernel.RecM.StoppedContinuationClosureResources.stopped,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root :=
      ``Ix.Kernel.RecM.DefEqAfterLazyDeltaStopped.ofClosureResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The final-WHNF comparator is split at a production seam: an optional
  -- constructor-directed prefix followed by the fallback chain.  Application
  -- comparison and every constructor in the prefix are now exhaustive
  -- concrete proofs.  The let roots include exact allocation, common-fvar
  -- body opening, context transport, and local-scope restoration.
  { root := ``Ix.Kernel.RecM.isDefEqWhnf_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsDefEqWhnf.ofPhases,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryDefEqWhnfApp_wf,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryDefEqWhnfApp.ofResources,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.TcM.openLetWithFV_scope,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.withLctxScope_openLetWithFV_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryDefEqWhnfLet_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryDefEqWhnfLet.ofResources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isNatLike_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.natSuccOf_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.NatSuccOf.ofResources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isDefEqNatAfterLiteral_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isDefEqNat_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryDefEqWhnfNat_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryDefEqWhnfNat.ofResources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isDefEqWhnfAfterStructural_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsDefEqWhnfAfterStructural.ofNat,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryDefEqWhnfStructural_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryDefEqWhnfStructural.ofResources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Lambda eta is split into a syntactic guard, caught infer/WHNF probes, and
  -- an explicit term builder.  The builder's lifted source and generated #0
  -- application are translated structurally before the recursive comparison
  -- is composed with Theory eta; the ordered reverse attempt uses symmetry.
  { root := ``Ix.Kernel.TcM.lift_whnf_wf_of_resources,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.compareEtaExpansion_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryEtaExpansionAfterGuard_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryEtaExpansion_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryDefEqWhnfEtaAfterGuard_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryDefEqWhnfEta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryDefEqWhnfEta.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isDefEqWhnfAfterNat_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsDefEqWhnfAfterNat.ofEta,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- The final-WHNF String phase reuses the exact expansion plans proved for
  -- the earlier DefEq tier.  Its optional result preserves the original
  -- two-way short-circuit order; reverse success is justified by symmetry.
  { root := ``Ix.Kernel.RecM.tryDefEqWhnfStringAfterGuard_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryDefEqWhnfString_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryDefEqWhnfString.ofContext,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isDefEqWhnfAfterEta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsDefEqWhnfAfterEta.ofString,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- The terminal final-WHNF chain is split at the two inductive boundaries.
  -- Proof irrelevance is concrete through the memoized proposition
  -- classifier; unit-like and structure-eta soundness remain separately
  -- named contracts until their exact inductive laws are supplied.
  { root := ``Ix.Kernel.RecM.isDefEqWhnfAfterUnit_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsDefEqWhnfAfterUnit.ofClassifier,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isDefEqWhnfAfterStructEta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsDefEqWhnfAfterStructEta.ofUnitAndProof,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.isDefEqWhnfAfterString_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.IsDefEqWhnfAfterString.ofStructEta,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := legacyWholeEnv },

  -- The unit-like classifier is tied to the exact immutable-catalog entries
  -- returned by both lazy lookups.  The shortcut then consumes only the
  -- narrow unique-inhabitant law for that trusted zero-index, one-nullary-
  -- constructor shape; it does not recover the legacy whole-environment
  -- inductive oracle.
  { root := ``Ix.Kernel.RecM.isUnitLikeInductive_wf,
    standardAxioms := standard,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.tryDefEqUnit_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },
  { root := ``Ix.Kernel.RecM.TryDefEqUnit.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  { root := ``Ix.Kernel.RecM.DefEqLazyDeltaStep.ofKernelResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := legacyWholeEnv },

  -- Structure eta is proved from the exact normalized source, immutable
  -- constructor lookup, typed field spine, and generated projection law.
  -- The positive structure classifier cannot manufacture semantic eta on
  -- its own, and every exported root remains quarantined from both legacy
  -- whole-environment and broad delta-authority paths.
  { root := ``Ix.Kernel.TrKExprS.prj_components,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.tryEtaStructFields_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.etaExpansionBaseLoop_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.etaExpansionBase_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.tryEtaStructAfterTypes_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.normalizeEtaStructSource_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.tryEtaStructAfterConstructor_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.tryEtaStructAfterNormalization_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.tryEtaStruct_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.tryDefEqWhnfStructEta_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.TryDefEqWhnfStructEta.ofResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- The final-WHNF phases are now assembled in exact production order.
  { root := ``Ix.Kernel.RecM.FinalWhnfClosureResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.FinalWhnfClosureResources.afterStructural,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.FinalWhnfClosureResources.finalWhnf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- Recursive DefEq closure: trusted finite expression references authorize
  -- only the two direct roots of an ordinary result entry.  The complete
  -- inner tier then feeds the guarded public cache shell.
  { root := ``Ix.Kernel.CacheEntry.defEqReferencesAuthorized,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.DefEqInner.WF,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.isDefEq_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.DefEqClosureResources,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.DefEqClosureResources.stopped,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.DefEqClosureResources.lazyDelta,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.DefEqClosureResources.inner,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.DefEqClosureResources.entryPoint,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.DefEqClosureResources.nextDefEq_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- Inference and DefEq consume the same predecessor table and suffix model;
  -- their fixed-universe pair closes before it is joined to the four WHNF
  -- fields.
  { root := ``Ix.Kernel.UncachedInference.Context.nextInfer_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.InferDefEqClosedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.InferDefEqClosureContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.InferDefEqClosureContext.layer,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.InferDefEqClosureContext.closedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- Legacy all-depth six-field knot assembly under the canonical production
  -- cache stack.  These roots remain audited as migration adapters, but the
  -- bounded public interfaces below are forbidden from depending on them.
  { root := ``Ix.Kernel.kernelCacheFallback,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.kernelCacheSemantics_eq_k1,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.ClosedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.ClosedAt.of_parts,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.runRec_wfAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecursiveMethodClosureContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecursiveMethodClosureContext.closedAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecursiveMethodClosureContext.methodsN,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- The all-depth closure interface is provably unusable for a
  -- finite support containing a sort: its syntax resources would generate
  -- an unbounded successor-sort chain.  The replacement below separates the
  -- finite result footprint from fuel-indexed method-call domains.
  { root :=
      ``Ix.Kernel.FiniteSupportBoundary.SyntaxInferenceResources.no_sort_source,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- Bounded production methods: a finite schedule closes only the
  -- method-table depths selected by this run's recursion fuel.  The public
  -- adapters consume the terminal successor-layer domain and have no
  -- `sorryAx` dependency.
  { root := ``Ix.Kernel.Methods.CallDomain.empty_within,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.CallDomain.singletonInfer_within,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.methodsOut_wfAtOn,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.CallScheduleAt.methodsN,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.CallScheduleAt.nextSelected,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecursiveMethodRunContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.whnf.wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.infer.wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.isDefEq.wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.SortSchedule.two,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.infer.sort_wf_bounded,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.infer.sort_wf_fuel_one,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },

  -- Declaration checking reconstructs the typed source translation from untyped/scoped
  -- checker ingress.  These roots are usable before the final checkConst
  -- assembly and do not depend on its statement placeholder.
  { root := ``Ix.Kernel.KUniv.scoped_iff_toVLevel_wf,
    standardAxioms := propextOnly,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.PreTrKExprS.upgradeOfTyped,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TrKExprS.openFVarZero,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Theory.Named.VExpr.inst_subst_cons,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RawCtxInterp.find?_inl,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RawCtxInterp.bvars_eq,
    standardAxioms := propextOnly,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RawProjRel.none_substCompatible,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RawExprRel.toPre_of_scoped_aux,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RawExprRel.toPre_of_scoped,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RawDeclRel.toPre_of_scope,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.PendingDecl.toPre_of_scope,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TypeCheckEvidence.isType,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.ValueCheckEvidence.hasType,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.StandaloneCheckEvidence.accepted,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.StandaloneCheckResult.accepted,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RawDeclRel.wfOfAccepted,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.PendingDecl.promoteOfAccepted,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.PendingDecl.checkResultAndPromote,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateUnivParamsSeen_go_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateUnivParamsSeen_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateUnivRootsList_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateUnivRootsArray_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateExprWellScoped_go_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateExprWellScoped_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateConstWellScoped_sound,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.PendingDecl.toPre_of_validation,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.PendingDecl.checkValidatedResultAndPromote,
    standardAxioms := standard,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateUnivParamsSeen_go_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateUnivParamsSeen_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateUnivRootsList_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateUnivRootsArray_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.getConst_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.hasConst_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateExprWellScoped_go_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateExprWellScoped_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.validateConstWellScoped_frame,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.LazyFaultPreserves.withInferOnly,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkTypePipeline_sound,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkValuePipeline_sound,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.FullInferenceWFAtOn.ofTypedIngress,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.FullInferenceWFAtOn.ofSingletonSort,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.StandalonePipelineResources.singletonSortAxiom,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkTypePipeline_bounded_sound,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkValuePipeline_bounded_sound,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkConstMember_axiom_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkConstMember_defn_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkConstMember_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkConstMember_validation_success,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkConstMember_pending_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkConstMemberFresh_pending_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.StandaloneRoute.axiomRoute,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkConst_standalone_pending_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkNoUnsafeRefs_go_frame,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkNoUnsafeRefs_frame,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.KernelStateWF.rebaseWorld,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.WhnfStateInv.rebaseWorld,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.reset_whnf_entry,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.FullInferPost.of_typed,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.WF.withInv,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferWith_fullHit_pre_acceptance,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_sort_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_var_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_fvar_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_const_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_nat_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_str_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.FullInferenceStepContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_app_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.PreservesInferOnly.strengthenWFValue,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.PreservesInferOnly.withInferOnly,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.PreservesInferOnly.openBinder,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.PreservesInferOnly.inferKey,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.cacheInferResult_preservesInferOnly,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.withLctxScope_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.ensureForallDirect_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.ensureSortDirect_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.methodsOut_preservesInferOnly,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.methodsN_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.PreservesInferOnly.isDefEq_full_wf,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.openBinder_scope_base,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.openBinder_pre_scope,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.KExpr.abstractFVarsSpec_instantiateRevSpec_singleton,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TrKExprS.closeOpenedFVarZero,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.withLctxScope_openBinder_pre_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_lam_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_all_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.openLet_scope_base,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.openLet_pre_scope,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.withLctxScope_openLet_pre_wf,
    standardAxioms := standard, nativeAxioms := expressionNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_let_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.ProjectionInference.FullWFAt.of_semantic_and_policy,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_prj_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferWith_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.infer_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.PreservesInferOnly.instantiateUnivParams,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.inferUncached_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.ProjectionInference.preservesInferOnlyAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.infer_preservesInferOnly_of_whnf,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },

  -- Declaration checking closes the concrete operational policy and retains the old strong
  -- all-support inference roots below as compatibility artifacts.  The
  -- public checker now consumes the bounded successor-layer resources above.
  { root := ``Ix.Kernel.Methods.next_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.inferOnlyClosed,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.methodsN_concrete_preservesInferOnly,
    standardAxioms := standard, nativeAxioms := inferNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.FullInferenceWFAt,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecursiveMethodClosureContext.fullInferenceContext,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecursiveMethodClosureContext.next_fullInferenceWFAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.Methods.methodsOut_fullInferenceWFAt,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecursiveMethodClosureContext.methodsN_fullInferenceWFAt,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.RecursiveMethodClosureContext.publicInfer_full_wf,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.checkConst.rollback_on_error,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.checkConst.rollback_preserves_kernel,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.checkConst.wf,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.checkConst.rejected_of_no_decl_wf,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.checkConst.axiom_pending_sound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkConstMemberFresh_scoped_pending_evidence,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },

  -- Block admission closes the atomic coordinated-block transaction around the real
  -- production router, classifier, body, and block-result cache.  The
  -- singleton-definition adapter consumes the declaration-checking theorem; inductive/recursor bodies keep
  -- their inductive certification oracle premise explicit.  Quotients are audited as excluded from
  -- this authority rather than being silently admitted by the block theorem.
  { root := ``Ix.Kernel.ExactCheckBlock.rebaseWorld,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.coordinatedBlockIfKind_success_trace,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.classifyBlock_wf,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.coordinatedBlockFor_some_preserves,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.CacheInvariant.replayCoordinatedMember,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.CacheInvariant.rejectsSuccessWithUntrustedMember,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkCoordinatedBlock_accepted,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkCoordinatedBlock_rejected,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkConst_success_disposition,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.TcM.checkConst.blockDisposition,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.certifySingletonDefinition,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.certifySingletonDefinitionScoped,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.certifyOracleBackedBlock,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.coordinatedBlockFor_quotient,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.Catalog.quotient_not_coordinated,
    standardAxioms := propextOnly,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  -- Quotients remain physically standalone, but semantic admission is one
  -- exact four-member Theory transaction followed by the registered quotient
  -- equation. The production bridge inverts all four real checkQuot runs,
  -- converts digest equality through a finite collision scope, and publishes
  -- the completed transaction as one exact trusted-log event. Its temporary
  -- Ix.Theory.Named semantic input is an explicit theorem parameter, not an axiom.
  { root := ``Ix.Kernel.QuotientAdmissionStep.bind,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientAdmissionStep.le,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientBundleAdmission.catalogEntries,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientBundleAdmission.nameAssignments,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientBundleAdmission.toAddQuot,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientBundleAdmission.le,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientBundleAdmission.quotType,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientBundleAdmission.quotCtor,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientBundleAdmission.quotLift,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientBundleAdmission.quotInd,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientBundleAdmission.quotientDefEq,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientAdmission.wf,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientAdmission.le,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkQuot_success_typeAddress,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkQuot_success_levels,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.RecM.checkQuot_success_type,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.CheckedQuotientBundle.toAdmission,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientAdmission.entry,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientAdmission.admit,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.QuotientAdmission.newlyTrustedMember,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.CheckedQuotientBundle.admitAtomically,
    standardAxioms := standard, nativeAxioms := levelNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AmbientNat.E0.atomicAdmission,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AmbientNat.E0.rejectsPrematureSuccess,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },

  -- Serial composition models semantic declaration dependencies in the production Address
  -- domain, proves buildAnonWork is an exact duplicate-free partition, and
  -- composes successful items in a constructive collapsed-block order.  The
  -- serial roots recover real successful checkConst calls from the public
  -- result array before applying the named per-item success adapter.
  { root := ``Ix.Kernel.WorkCovers.covered,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.WorkCovers.subjectOfCovered,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.VerifyWorld.AcceptsAddress.mono,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.WorkItemAccepted.mono,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.WorkItemAccepted.acceptsAddress,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.WellFoundedBlocks.noTwoCycle,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.acceptedWorkset_subjectWF,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.IxonEnv.dependencyCatalog_blockOf,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.IxonEnv.dependencyCatalog_dependsOn_iff,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.IxonExpr.DeclReference.target_mem_refs,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.IxonConstant.SemanticDependency.target_mem_refs,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.ExactAnonEntry.getConst,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.ExactAnonEntry.constant_unique,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.ExactAnonEntry.buildAnonWorkItem_eq,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.buildAnonWork_eq_expected,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.mem_expectedAnonWork_iff,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkItem.ofConstantInfo_root,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkItem.covers_root,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkItem.ofConstantInfo_primary_mem_targets,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.source_covered,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.covered_is_source,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.expected_primary_mem_targets,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.ExactAnonEntry.blockOfAddr_eq_owner,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.ExactAnonEntry.blockOfAddr_eq_self,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.matches_blockOfAddr,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.expectedAnonWork_covers,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.expectedAnonWork_matchesCatalog,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.buildAnonWork_exact,
    standardAxioms := standard,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.finishAnonCheckItem_results,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.runAnonCheckItem_preserves_result,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.runAnonCheckList_preserves_result,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.runAnonCheckItem_error_result,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.serialChecksSucceeded_of_results,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.SerialChecksSucceeded.successfulStep,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.SerialChecksSucceeded.allAccepted,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.checkEnvAnon_eq_serial,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.checkEnvAnon_subjectWF,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.E1Fixture.exactSubjectsAndAssumptions,
    standardAxioms := standardWithoutChoice,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.E1Fixture.droppingWorkItem_breaks_coverage,
    standardAxioms := propextOnly,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.E1Fixture.unresolvedDependency_breaks_closure,
    standardAxioms := propextOnly,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.E1Fixture.cyclicStandalones_not_wellFounded,
    standardAxioms := propextOnly,
    forbiddenDependencies := boundedKnotForbiddenDependencies },

  -- The supported fragment combines the scoped standalone theorem and atomic
  -- block disposition in the serial driver's concrete-call adapter. Singleton
  -- definitions use the scoped checking certificate; fresh inductive/recursor
  -- bodies retain an explicit inductive-certification oracle resource.
  -- Separately, the certificate-backed replay adapter consumes already-
  -- installed member provenance, admits exact arrays idempotently, and gives
  -- all-block consumers a path which cannot reach oracle materialization.
  { root := ``Ix.Kernel.SupportedStandaloneResources.promotes,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.SupportedBlockBodyResources.certify,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.SupportedCheckRun.accepts,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.SupportedCheckFragment.checkSuccessSound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.AnonWorkEnvWF.checkEnvAnon_supported_subjectWF,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.CertificateBackedBlockResources.newlyTrustedMember,
    standardAxioms := standard,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root := ``Ix.Kernel.CertificateBackedBlockResources.accepts,
    standardAxioms := standard,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root := ``Ix.Kernel.CertificateBackedCheckFragment.checkSuccessSound,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root :=
      ``Ix.Kernel.AnonWorkEnvWF.checkEnvAnon_certificateBacked_subjectWF,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root := ``Ix.Kernel.BooleanEnumerationFixture.subjectWF,
    standardAxioms := standard, nativeAxioms := booleanDriverNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root := ``Ix.Kernel.BooleanSerialized.subjectWF,
    standardAxioms := standard, nativeAxioms := serializedBooleanNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root := ``Ix.Kernel.SerializedLiteralBlobs.literalRoundTrip,
    standardAxioms := standard, nativeAxioms := literalRoundTripNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.SerializedLiteralBlobs.malformedConstantRejected,
    standardAxioms := standard, nativeAxioms := malformedConstantNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.SerializedLiteralBlobs.malformedBlobRejected,
    standardAxioms := standard, nativeAxioms := malformedBlobNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root :=
      ``Ix.Kernel.SupportedAcceptanceFixture.block_rejects_standalone_route,
    standardAxioms := propextOnly,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.SupportedAcceptanceFixture.block_rejects_wrong_route,
    standardAxioms := propextOnly,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root :=
      ``Ix.Kernel.SupportedAcceptanceFixture.certificate_backed_definition_excluded,
    forbiddenDependencies := certificateBackedDriverForbiddenDependencies },
  { root :=
      ``Ix.Kernel.SupportedAcceptanceFixture.booleanFamilyBody_certified,
    standardAxioms := standard, nativeAxioms := booleanFamilyBodyNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },

  -- Positive-fuel acceptance witness.  The original resource theorem leaves
  -- the joint suffix model explicit; the scoped checker roots below construct
  -- the finite model from their exact public execution certificate.  Two
  -- exact Blake3 address inequalities remain explicit fixture inputs.
  { root := ``Ix.Kernel.PositiveFuelSort.methodContractAtFuelOne,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.PositiveFuelSort.fullInferenceAtFuelOne,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },
  { root := ``Ix.Kernel.PositiveFuelSort.pipelines_cover_concreteAxiom,
    standardAxioms := standard, nativeAxioms := inferNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := boundedKnotForbiddenDependencies },

  -- Scoped methods in a closed context. These roots certify the exact
  -- fuel-one public trace, package its finite requests and bounded recursive
  -- schedule, instantiate `ScopedKernelSuffixModel.finiteOperational`, and
  -- retain `StateInScope` through successful semantic promotion.  None may
  -- pass through the global suffix-model compatibility path.
  { root := ``Ix.Kernel.PositiveFuelSort.Checker.model,
    standardAxioms := standard, nativeAxioms := contextNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.PositiveFuelSort.Checker.initialState_inv,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.PositiveFuelSort.Checker.inference_run,
    standardAxioms := standard, nativeAxioms := nameContextNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.PositiveFuelSort.Checker.public_requests,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.PositiveFuelSort.Checker.runAssumptions,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.PositiveFuelSort.Checker.publicContext,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },
  { root := ``Ix.Kernel.PositiveFuelSort.Checker.checked_and_promoted,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    sorryOrigins := typingDebt,
    forbiddenDependencies := scopedK2SForbiddenDependencies },

  -- The joined ambient-Nat fixture uses the exact semantic pending objects
  -- and exact public checker executions for both verdicts.  Its valid path
  -- carries a concrete acceptance result and promotion; its invalid path
  -- returns the malformed-universe error with exact rollback.
  { root := ``Ix.Kernel.AmbientNat.goodCheckResult,
    standardAxioms := standard,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.AmbientNat.initial_good_public,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.AmbientNat.reset_bad_public,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies },
  { root := ``Ix.Kernel.AmbientNat.publicCheckLifecycle,
    standardAxioms := standard, nativeAxioms := inductiveNative,
    forbiddenDependencies := k1ForbiddenDependencies }
]

run_cmd Ix.Kernel.Verify.Audit.check roots

end Ix.Kernel.Verify.Audit.Completed
