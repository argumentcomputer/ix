import Ix.Tc.Verify.Inductive.Certificate
import Lean4Lean.Verify.Environment.InductiveFixtures

/-!
# Certified recursive-field-normalizing fixture

`AliasRec.mk` retains the raw field `RecAlias AliasRec`, where `RecAlias` is
a transparent identity definition.  Lean4Lean's checked normalization path
unfolds that field to the direct recursive occurrence `AliasRec` before
dependent inductive analysis, while the generated environment continues to
store the raw constructor declaration.

Lean4Lean exposes the exact checked generation and its semantic WF theorem,
but deliberately does not add another fixture-specific public certificate
wrapper.  This module performs that narrow consumer-side packaging.  Physical
anonymous ingress, production checking, and catalog admission remain
separate layers.
-/

namespace Ix.Tc.AliasRecCertificateFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures

/-- The transparent identity definition preceding `AliasRec`. -/
def recAliasValue : VDefVal := recAliasVal

theorem recAliasValue_wf : recAliasValue.WF VEnv.empty :=
  recAliasVal_wf

@[simp] theorem recAliasValue_toVConstant :
    recAliasValue.toVConstant =
      (vconst(type_of% @RecAlias) : VConstant) := rfl

@[simp] theorem recAliasValue_toDefEq :
    recAliasValue.toDefEq = recAliasDefEq := rfl

theorem recAliasDeclWF :
    VDecl.WF VEnv.empty (.def recAliasValue) recAliasEnv := by
  apply VDecl.WF.def recAliasValue_wf
  rfl

/-- Explicit well-formed history for the alias environment. -/
theorem beforeWF : recAliasEnv.WF :=
  ⟨[.def recAliasValue], .decl recAliasDeclWF .empty⟩

/-- Consumer-facing packaging of Lean4Lean's exact checker-produced
`AliasRec` generation.  The proof field is erased by `addInductCertified`;
the executable generation is definitionally the upstream checked artifact. -/
def certificate : aliasRecRawDecl.GenerationCertificate recAliasEnv where
  generation := aliasRecGenerationChecked
  wf := aliasRecGenerationChecked_wf_checked

/-- Exact post-environment selected by that generation. -/
def finalEnv : VEnv := aliasRecFinalEnv

theorem success :
    recAliasEnv.addInductCertified certificate = some finalEnv :=
  aliasRec_addInductGeneration

/-- One exact non-identity recursive-field generation transaction. -/
def transaction : CertifiedGenerationTransaction aliasRecRawDecl
    recAliasEnv finalEnv where
  certificate := certificate
  success := success
  beforeWF := beforeWF

@[simp] theorem transaction_generation :
    transaction.certificate.generation = aliasRecGenerationChecked := rfl

private abbrev generation := transaction.certificate.generation

/-- Computed facts distinguishing this fixture from identity-normalized
direct recursion.  The raw constructor stores `RecAlias AliasRec`; the
analyzer-owned view exposes one direct recursive field with no intervening
binders. -/
structure BreadthFacts : Prop where
  zeroUniverses : aliasRecRawDecl.uvars = 0
  zeroParameters : aliasRecRawDecl.nparams = 0
  singletonFamily : aliasRecRawDecl.types.length = 1
  zeroIndices : generation.block.checked.indices.length = 0
  largeElimination : generation.block.checked.elimination = .large
  oneConstructor : generation.block.checked.constructors.length = 1
  oneConstructorField :
    generation.block.checked.constructors[0].fields.length = 1
  oneRecursiveArgument :
    generation.block.checked.constructors[0].recursive.length = 1
  recursiveFieldIndex :
    generation.block.checked.constructors[0].recursive[0].fieldIndex = 0
  recursiveBinderCount :
    generation.block.checked.constructors[0].recursive[0].binders.length = 0
  recursiveTargetFamily :
    generation.block.checked.constructors[0].recursive[0].targetType = 0
  recursiveTargetIndices :
    generation.block.checked.constructors[0].recursive[0].indices = []
  rawFieldRetained :
    generation.block.sourceType.ctors[0].type =
      .forallE
        (.app (.const ``RecAlias [.succ .zero]) (.const ``AliasRec []))
        (.const ``AliasRec [])
  checkedFieldNormalized :
    generation.block.checked.constructors[0].value.type =
      .forallE (.const ``AliasRec []) (.const ``AliasRec [])
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
    generation.block.checked.constructors[0].recursive[0].binders.length = 0 ∧
    generation.block.checked.constructors[0].recursive[0].targetType = 0 ∧
    generation.block.checked.constructors[0].recursive[0].indices = [] ∧
    generation.block.sourceType.ctors[0].type =
      .forallE
        (.app (.const ``RecAlias [.succ .zero]) (.const ``AliasRec []))
        (.const ``AliasRec []) ∧
    generation.block.checked.constructors[0].value.type =
      .forallE (.const ``AliasRec []) (.const ``AliasRec []) ∧
    generation.block.sourceType.ctors[0].type ≠
      generation.block.checked.constructors[0].value.type ∧
    generation.generatedRules.length = 1 := by
  native_decide

theorem breadth : BreadthFacts := by
  rcases breadthNative with
    ⟨hindices, helim, hctors, hfields, hrecursive, hfieldIndex,
      hbinders, htarget, htargetIndices, hraw, hchecked, hnonidentity,
      hrules⟩
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
    recursiveTargetFamily := htarget
    recursiveTargetIndices := htargetIndices
    rawFieldRetained := hraw
    checkedFieldNormalized := hchecked
    nonIdentityConstructor := hnonidentity
    oneGeneratedRule := hrules }

theorem certifiedFacts :
    CertifiedGenerationFacts recAliasEnv finalEnv transaction.certificate :=
  transaction.facts

end Ix.Tc.AliasRecCertificateFixture
