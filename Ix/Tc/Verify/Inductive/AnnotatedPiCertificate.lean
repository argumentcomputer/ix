import Ix.Tc.Verify.Inductive.ProducedGenerationTransaction
import Lean4Lean.Verify.Environment.InductiveFixtures

/-!
# Certified annotation-normalizing recursive-Pi fixture

`AnnotatedPi.mk` retains the raw binder domain `outParam Prop`, while the
Lean4Lean analyzer classifies recursion through the normalized domain `Prop`.
This is the first Ix transaction whose certified generation is deliberately
non-identity: the stored family and generated artifacts preserve raw syntax,
but recursive classification is owned by the checked view produced by the
ordinary Lean4Lean candidate pipeline.

The module is still Theory-facing.  Physical anonymous ingress, production
checking, and catalog admission are separate layers built on this exact
certificate.
-/

namespace Ix.Tc.AnnotatedPiCertificateFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures

noncomputable section

/-- The transparent annotation definition preceding `AnnotatedPi`.  Naming
this value publicly lets the Ix ingress layer relate one physical definition
to the exact Theory history required by the generation certificate. -/
def outParamValue : VDefVal where
  name := ``outParam
  uvars := (vconst(type_of% @outParam) : VConstant).uvars
  type := (vconst(type_of% @outParam) : VConstant).type
  value := outParamDefEq.rhs

theorem outParamValue_wf : outParamValue.WF VEnv.empty := by
  exact VEnv.HasType.lam
    (VEnv.HasType.sort (by decide))
    (VEnv.HasType.bvar .zero)

@[simp] theorem outParamValue_toVConstant :
    outParamValue.toVConstant =
      (vconst(type_of% @outParam) : VConstant) := rfl

@[simp] theorem outParamValue_toDefEq :
    outParamValue.toDefEq = outParamDefEq := rfl

theorem outParamDeclWF :
    VDecl.WF VEnv.empty (.def outParamValue) outParamEnv := by
  apply VDecl.WF.def outParamValue_wf
  rfl

/-- Explicit well-formed history for the annotation environment.  The public
Lean4Lean certificate needs this environment as input, rather than silently
treating the reducible annotation as a primitive. -/
theorem beforeWF : outParamEnv.WF :=
  ⟨[.def outParamValue], .decl outParamDeclWF .empty⟩

/-- Exact post-environment selected by that certificate. -/
def finalEnv : VEnv := annotatedPiFinalEnv

/-- The exact L4L-01E package.  Its producer-shape index is deliberately
inferred here because Lean4Lean keeps the fixture's concrete shape witness
private while exposing this public dependent existence theorem. -/
def exactPackage :=
  Classical.choice annotatedPiExactProducedGenerationCandidatePackage_exists

/-- The exact successful outer metadata producer, dependent semantic package,
and certified Theory insertion retained as one E2c transaction.  Construction
keeps the producer-selected source and generation indices intact. -/
def exactProducedTransaction :=
  ExactProducedGenerationTransaction.mk
    (before := outParamEnv) (after := finalEnv) (Us := [])
    exactPackage
    (by
      have certificate_eq :
          exactPackage.package.package.certificate =
            annotatedPiGenerationCertificate := by
        congr
      rw [certificate_eq]
      exact annotatedPi_addInductCertified)
    beforeWF

/-- Intentional operational erasure of the exact L4L-01E indices. -/
def producedTransaction :
    ProducedGenerationTransaction outParamEnv finalEnv [] :=
  exactProducedTransaction.toProduced

/-- The named, computable Theory certificate.  The producer-linked path is
kept separately above so executable consumers do not inherit the
`Classical.choice` used to unpack the exact dependent producer package. -/
def certificate : annotatedPiRawDecl.GenerationCertificate outParamEnv :=
  annotatedPiGenerationCertificate

theorem success :
    outParamEnv.addInductCertified certificate = some finalEnv :=
  annotatedPi_addInductCertified

/-- One exact non-identity generation transaction. -/
def transaction : CertifiedGenerationTransaction annotatedPiRawDecl
    outParamEnv finalEnv where
  certificate := certificate
  success := success
  beforeWF := beforeWF

/-- Erasing producer provenance yields the same Theory certificate used by
the executable transaction.  Only proof fields differ. -/
theorem producedCertificate_eq :
    producedTransaction.certificate = certificate := by
  congr

/-- The exact producer-linked path and the named Theory path coincide after
the intentional provenance erasure. -/
theorem producedToCertified_eq :
    producedTransaction.toCertified = transaction := by
  congr

/-- The ordinary producer equation and its semantic transaction remain
coupled at the Ix boundary before the Theory-only erasure. -/
theorem producerLinkedFacts : producedTransaction.Facts :=
  producedTransaction.facts

@[simp] theorem transaction_generation :
    transaction.certificate.generation = annotatedPiGenerationChecked := rfl

/-- Computable representative of the exact generation selected by
`transaction`; `transaction_generation` identifies the two. -/
private abbrev generation := annotatedPiGenerationChecked

/-- Computed facts that distinguish this fixture from identity-normalized
recursive-Pi generation.  In particular, raw artifacts retain
`outParam Prop`, while the analyzer-owned view exposes `Prop` before marking
the function result as recursive. -/
structure BreadthFacts : Prop where
  zeroUniverses : annotatedPiRawDecl.uvars = 0
  zeroParameters : annotatedPiRawDecl.nparams = 0
  singletonFamily : annotatedPiRawDecl.types.length = 1
  zeroIndices : generation.block.checked.indices.length = 0
  largeElimination : generation.block.checked.elimination = .large
  oneConstructor : generation.block.checked.constructors.length = 1
  oneConstructorField : generation.block.checked.constructors[0].fields.length = 1
  oneRecursiveArgument :
    generation.block.checked.constructors[0].recursive.length = 1
  recursiveFieldIndex :
    generation.block.checked.constructors[0].recursive[0].fieldIndex = 0
  recursiveBinderCount :
    generation.block.checked.constructors[0].recursive[0].binders.length = 1
  rawDomainRetained :
    generation.block.sourceType.ctors[0].type =
      .forallE
        (.forallE
          (.app (.const ``outParam [.succ .zero]) (.sort .zero))
          (.const ``AnnotatedPi []))
        (.const ``AnnotatedPi [])
  checkedDomainNormalized :
    generation.block.checked.constructors[0].value.type =
      .forallE
        (.forallE (.sort .zero) (.const ``AnnotatedPi []))
        (.const ``AnnotatedPi [])
  nonIdentityConstructor :
    generation.block.sourceType.ctors[0].type ≠
      generation.block.checked.constructors[0].value.type
  oneGeneratedRule : generation.generatedRules.length = 1

private theorem breadthNative :
    generation.block.checked.indices.length = 0 ∧
    generation.block.checked.elimination = .large ∧
    generation.block.checked.constructors.length = 1 ∧
    generation.block.checked.constructors[0].fields.length = 1 ∧
    generation.block.checked.constructors[0].recursive.length = 1 ∧
    generation.block.checked.constructors[0].recursive[0].fieldIndex = 0 ∧
    generation.block.checked.constructors[0].recursive[0].binders.length = 1 ∧
    generation.block.sourceType.ctors[0].type =
      .forallE
        (.forallE
          (.app (.const ``outParam [.succ .zero]) (.sort .zero))
          (.const ``AnnotatedPi []))
        (.const ``AnnotatedPi []) ∧
    generation.block.checked.constructors[0].value.type =
      .forallE
        (.forallE (.sort .zero) (.const ``AnnotatedPi []))
        (.const ``AnnotatedPi []) ∧
    generation.block.sourceType.ctors[0].type ≠
      generation.block.checked.constructors[0].value.type ∧
    generation.generatedRules.length = 1 := by
  native_decide

theorem breadth : BreadthFacts := by
  rcases breadthNative with
    ⟨hindices, helim, hctors, hfields, hrecursive, hfieldIndex,
      hbinders, hraw, hchecked, hnonidentity, hrules⟩
  exact {
    zeroUniverses := rfl
    zeroParameters := rfl
    singletonFamily := rfl
    zeroIndices := hindices
    largeElimination := helim
    oneConstructor := hctors
    oneConstructorField := hfields
    oneRecursiveArgument := hrecursive
    recursiveFieldIndex := hfieldIndex
    recursiveBinderCount := hbinders
    rawDomainRetained := hraw
    checkedDomainNormalized := hchecked
    nonIdentityConstructor := hnonidentity
    oneGeneratedRule := hrules }

theorem certifiedFacts :
    CertifiedGenerationFacts outParamEnv finalEnv transaction.certificate :=
  transaction.facts

end

end Ix.Tc.AnnotatedPiCertificateFixture
