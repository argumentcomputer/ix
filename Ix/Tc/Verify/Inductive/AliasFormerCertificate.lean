import Ix.Tc.Verify.Inductive.ProducedGenerationTransaction
import Lean4Lean.Verify.Environment.InductiveFixtures

/-!
# Certified family-result-normalizing fixture

`AliasFormer` is declared with the raw result sort `TypeFamilyAlias`, a
transparent alias for `Type`.  Lean4Lean's ordinary candidate pipeline
normalizes that result to `Sort 1` before dependent inductive analysis while
retaining the raw family and constructor declarations in the generated
environment.

This module exposes the exact checker-produced Theory transaction.  Physical
anonymous ingress, production checking, and catalog admission are separate
layers built on this certificate.
-/

namespace Ix.Tc.AliasFormerCertificateFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures

noncomputable section

/-- The transparent alias definition preceding `AliasFormer`. -/
def typeFamilyAliasValue : VDefVal where
  name := ``TypeFamilyAlias
  uvars := (vconst(type_of% @TypeFamilyAlias) : VConstant).uvars
  type := (vconst(type_of% @TypeFamilyAlias) : VConstant).type
  value := typeFamilyAliasDefEq.rhs

theorem typeFamilyAliasValue_wf :
    typeFamilyAliasValue.WF VEnv.empty := by
  exact VEnv.HasType.sort (by decide)

@[simp] theorem typeFamilyAliasValue_toVConstant :
    typeFamilyAliasValue.toVConstant =
      (vconst(type_of% @TypeFamilyAlias) : VConstant) := rfl

@[simp] theorem typeFamilyAliasValue_toDefEq :
    typeFamilyAliasValue.toDefEq = typeFamilyAliasDefEq := rfl

theorem typeFamilyAliasDeclWF :
    VDecl.WF VEnv.empty (.def typeFamilyAliasValue) typeFamilyAliasEnv := by
  apply VDecl.WF.def typeFamilyAliasValue_wf
  rfl

/-- Explicit well-formed history for the alias environment. -/
theorem beforeWF : typeFamilyAliasEnv.WF :=
  ⟨[.def typeFamilyAliasValue], .decl typeFamilyAliasDeclWF .empty⟩

/-- Exact post-environment selected by that certificate. -/
def finalEnv : VEnv := aliasFormerFinalEnv

/-- The exact L4L-01E package.  Its producer-shape index is deliberately
inferred here because Lean4Lean keeps the fixture's concrete shape witness
private while exposing this public dependent existence theorem. -/
def exactPackage :=
  Classical.choice aliasFormerExactProducedGenerationCandidatePackage_exists

/-- The exact successful outer metadata producer, dependent semantic package,
and certified Theory insertion retained as one E2c transaction.  Construction
keeps the producer-selected source and generation indices intact. -/
def exactProducedTransaction :=
  ExactProducedGenerationTransaction.mk
    (before := typeFamilyAliasEnv) (after := finalEnv) (Us := [])
    exactPackage
    (by
      have certificate_eq :
          exactPackage.package.package.certificate =
            aliasFormerGenerationCertificate := by
        congr
      rw [certificate_eq]
      exact aliasFormer_addInductCertified_checked)
    beforeWF

/-- Intentional operational erasure of the exact L4L-01E indices. -/
def producedTransaction :
    ProducedGenerationTransaction typeFamilyAliasEnv finalEnv [] :=
  exactProducedTransaction.toProduced

/-- The named, computable Theory certificate.  The producer-linked path is
kept separately above so executable consumers do not inherit the
`Classical.choice` used to unpack the exact dependent producer package. -/
def certificate : aliasFormerRawDecl.GenerationCertificate
    typeFamilyAliasEnv :=
  aliasFormerGenerationCertificate

theorem success :
    typeFamilyAliasEnv.addInductCertified certificate = some finalEnv :=
  aliasFormer_addInductCertified_checked

/-- One exact non-identity family-result generation transaction. -/
def transaction : CertifiedGenerationTransaction aliasFormerRawDecl
    typeFamilyAliasEnv finalEnv where
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
    transaction.certificate.generation = aliasFormerGenerationChecked := rfl

/-- Computable representative of the exact generation selected by
`transaction`; `transaction_generation` identifies the two. -/
private abbrev generation := aliasFormerGenerationChecked

/-- Computed facts that distinguish this fixture from identity-normalized
singleton enumeration: the stored family result is the alias, while the
analyzer-owned checked view is `Type`. -/
structure BreadthFacts : Prop where
  zeroUniverses : aliasFormerRawDecl.uvars = 0
  zeroParameters : aliasFormerRawDecl.nparams = 0
  singletonFamily : aliasFormerRawDecl.types.length = 1
  zeroIndices : generation.block.checked.indices.length = 0
  largeElimination : generation.block.checked.elimination = .large
  oneConstructor : generation.block.checked.constructors.length = 1
  zeroConstructorFields :
    generation.block.checked.constructors[0].fields.length = 0
  zeroRecursiveArguments :
    generation.block.checked.constructors[0].recursive.length = 0
  rawFamilyResult :
    generation.block.sourceType.type = .const ``TypeFamilyAlias []
  checkedFamilyResult :
    generation.block.checked.type.type = .sort (.succ .zero)
  nonIdentityFamilyResult :
    generation.block.sourceType.type ≠ generation.block.checked.type.type
  rawConstructorRetained :
    generation.block.sourceType.ctors[0].type = .const ``AliasFormer []
  checkedConstructorRetained :
    generation.block.checked.constructors[0].value.type =
      .const ``AliasFormer []
  oneGeneratedRule : generation.generatedRules.length = 1

private theorem breadthNative :
    generation.block.checked.indices.length = 0 ∧
    generation.block.checked.elimination = .large ∧
    generation.block.checked.constructors.length = 1 ∧
    generation.block.checked.constructors[0].fields.length = 0 ∧
    generation.block.checked.constructors[0].recursive.length = 0 ∧
    generation.block.sourceType.type = .const ``TypeFamilyAlias [] ∧
    generation.block.checked.type.type = .sort (.succ .zero) ∧
    generation.block.sourceType.type ≠ generation.block.checked.type.type ∧
    generation.block.sourceType.ctors[0].type = .const ``AliasFormer [] ∧
    generation.block.checked.constructors[0].value.type =
      .const ``AliasFormer [] ∧
    generation.generatedRules.length = 1 := by
  native_decide

theorem breadth : BreadthFacts := by
  rcases breadthNative with
    ⟨hindices, helim, hctors, hfields, hrecursive, hrawFamily,
      hcheckedFamily, hnonidentity, hrawCtor, hcheckedCtor, hrules⟩
  exact {
    zeroUniverses := rfl
    zeroParameters := rfl
    singletonFamily := rfl
    zeroIndices := hindices
    largeElimination := helim
    oneConstructor := hctors
    zeroConstructorFields := hfields
    zeroRecursiveArguments := hrecursive
    rawFamilyResult := hrawFamily
    checkedFamilyResult := hcheckedFamily
    nonIdentityFamilyResult := hnonidentity
    rawConstructorRetained := hrawCtor
    checkedConstructorRetained := hcheckedCtor
    oneGeneratedRule := hrules }

theorem certifiedFacts :
    CertifiedGenerationFacts typeFamilyAliasEnv finalEnv
      transaction.certificate :=
  transaction.facts

end

end Ix.Tc.AliasFormerCertificateFixture
