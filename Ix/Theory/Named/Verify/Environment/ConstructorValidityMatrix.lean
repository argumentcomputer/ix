/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.ConstructorValidityFixtures
import Ix.Theory.Named.Verify.Environment.InductiveFixtures

/-!
# Constructor-validity differential matrix

The positive half quotes real Lean metadata, runs the ordinary normalization
candidate producer, then runs both strengthened constructor gates at their
actual pre-family and post-family environments.  The negative half pairs each failed
source declaration in `Theory.ConstructorValidityFixtures` with hand-built
metadata at the nearest ordinary-producer phase.
-/

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta Elab Term
open Ix.Theory.Named.InductiveFixtures

/-! ## Actual positive metadata -/

def constructorValidityMatrixInfo : ConstantInfo :=
  kernelInductInfo% ConstructorValidityMatrix

def constructorValidityMatrixMkInfo : ConstantInfo :=
  kernelCtorInfo% ConstructorValidityMatrix.mk

def constructorValidityMatrixRecInfo : ConstantInfo :=
  kernelRecInfo% ConstructorValidityMatrix.rec

def constructorValidityMatrixKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% ConstructorValidityMatrix.rec 0

def constructorValidityMatrixKernelCtor : Constructor where
  name := constructorValidityMatrixMkInfo.name
  type := constructorValidityMatrixMkInfo.type

def constructorValidityMatrixKernelType : InductiveType where
  name := constructorValidityMatrixInfo.name
  type := constructorValidityMatrixInfo.type
  ctors := [constructorValidityMatrixKernelCtor]

def propRecursiveBoundaryInfo : ConstantInfo :=
  kernelInductInfo% PropRecursiveBoundary

def propRecursiveBoundaryMkInfo : ConstantInfo :=
  kernelCtorInfo% PropRecursiveBoundary.mk

def propRecursiveBoundaryRecInfo : ConstantInfo :=
  kernelRecInfo% PropRecursiveBoundary.rec

def propRecursiveBoundaryKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% PropRecursiveBoundary.rec 0

def propRecursiveBoundaryKernelCtor : Constructor where
  name := propRecursiveBoundaryMkInfo.name
  type := propRecursiveBoundaryMkInfo.type

def propRecursiveBoundaryKernelType : InductiveType where
  name := propRecursiveBoundaryInfo.name
  type := propRecursiveBoundaryInfo.type
  ctors := [propRecursiveBoundaryKernelCtor]

theorem constructorValidityMatrix_kernel_shape :
    (match constructorValidityMatrixInfo with
    | .inductInfo info => (info.numParams, info.numIndices)
    | _ => (0, 0)) = (2, 0) ∧
      (match constructorValidityMatrixMkInfo with
      | .ctorInfo info => info.numFields
      | _ => 0) = 6 ∧
      (match constructorValidityMatrixRecInfo with
      | .recInfo info =>
        (info.numParams, info.numIndices, info.numMotives,
          info.numMinors, info.rules.length)
      | _ => (0, 0, 0, 0, 0)) = (2, 0, 1, 1, 1) := by
  exact ⟨rfl, rfl, rfl⟩

theorem constructorValidityMatrix_recursive_positions_exact :
    constructorValidityMatrixChecked.constructors[0].recursive.map
      (fun position => (position.fieldIndex, position.binders.length)) =
        [(2, 0), (3, 1)] := rfl

theorem constructorValidityMatrix_kernel_rule_exact :
    constructorValidityMatrixKernelRuleRhs =
      constructorValidityMatrixGenerationChecked.generatedRules[0].rhs := rfl

theorem propRecursiveBoundary_kernel_shape :
    (match propRecursiveBoundaryInfo with
    | .inductInfo info => (info.numParams, info.numIndices)
    | _ => (0, 0)) = (1, 1) ∧
      (match propRecursiveBoundaryMkInfo with
      | .ctorInfo info => info.numFields
      | _ => 0) = 2 ∧
      (match propRecursiveBoundaryRecInfo with
      | .recInfo info =>
        (info.numParams, info.numIndices, info.numMotives,
          info.numMinors, info.rules.length)
      | _ => (0, 0, 0, 0, 0)) = (1, 1, 1, 1, 1) := by
  exact ⟨rfl, rfl, rfl⟩

theorem propRecursiveBoundary_recursive_positions_exact :
    propRecursiveBoundaryChecked.constructors[0].recursive.map
      (fun position => (position.fieldIndex, position.binders.length)) =
        [(1, 1)] := rfl

theorem propRecursiveBoundary_kernel_rule_exact :
    propRecursiveBoundaryKernelRuleRhs =
      propRecursiveBoundaryGenerationChecked.generatedRules[0].rhs := rfl

/-! ## Positive ordinary and strengthened gates -/

def constructorValidityMatrixContext : AddInductive.Context where
  env := Kernel.Environment.ofConstants `_constructorValidityMatrix
    ({} : ConstMap)
  lparams := [`u]
  safety := .safe
  allowPrimitive := false

def propRecursiveBoundaryContext : AddInductive.Context where
  env := Kernel.Environment.ofConstants `_propRecursiveBoundary
    ({} : ConstMap)
  lparams := [`u]
  safety := .safe
  allowPrimitive := false

def singletonCandidateExact (nparams : Nat) (source : InductiveType)
    (context : AddInductive.Context) : Bool :=
  match AddInductive.buildNormalizationCandidate nparams [source] 0 false
      context with
  | .error _ => false
  | .ok candidate =>
      candidate.families.singleton.familyType.type.view.equal source.type &&
        candidate.families.singleton.constructors.toList
          (fun _ constructor => constructor.type.view) ==
            source.ctors.map (fun constructor => constructor.type)

def singletonPreFamilyAccepted (nparams : Nat) (source : InductiveType)
    (context : AddInductive.Context) : Bool :=
  match AddInductive.buildNormalizationCandidate nparams [source] 0 false
      context with
  | .error _ => false
  | .ok candidate =>
      match AddInductive.checkInductiveTypes nparams #[source]
          (fun stats =>
            AddInductive.checkConstructorPreFamilySafety stats
              candidate.families.singleton.familyType.type.view
              candidate.families.singleton.constructors) context with
      | .ok _ => true
      | .error _ => false

def singletonUniverseAccepted (nparams : Nat) (source : InductiveType)
    (context : AddInductive.Context) : Bool :=
  match AddInductive.checkInductiveTypes nparams #[source]
      (fun stats => do
        let familyEnv ← AddInductive.declareInductiveTypes stats nparams
          #[source] 0 false
        AddInductive.withEnv familyEnv do
          AddInductive.checkConstructorUniverseListSemantics stats
            source.ctors) context with
  | .ok _ => true
  | .error _ => false

#guard singletonCandidateExact 2 constructorValidityMatrixKernelType
  constructorValidityMatrixContext

#guard singletonPreFamilyAccepted 2 constructorValidityMatrixKernelType
  constructorValidityMatrixContext

#guard singletonUniverseAccepted 2 constructorValidityMatrixKernelType
  constructorValidityMatrixContext

#guard singletonCandidateExact 1 propRecursiveBoundaryKernelType
  propRecursiveBoundaryContext

#guard singletonPreFamilyAccepted 1 propRecursiveBoundaryKernelType
  propRecursiveBoundaryContext

#guard singletonUniverseAccepted 1 propRecursiveBoundaryKernelType
  propRecursiveBoundaryContext

/-! ## Matching ordinary-producer rejections -/

def spec05TypeBoxName : Name :=
  `Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05TypeBox

def spec05ProofBoxName : Name :=
  `Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05ProofBox

def spec05DepProofBoxName : Name :=
  `Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05DepProofBox

def spec05TypeBoxInfo : ConstantInfo := .axiomInfo {
  name := spec05TypeBoxName
  levelParams := []
  type := .forallE `α (.sort (.succ .zero))
    (.sort (.succ .zero)) .default
  isUnsafe := false }

def spec05ProofBoxInfo : ConstantInfo := .axiomInfo {
  name := spec05ProofBoxName
  levelParams := []
  type := .forallE `α (.sort (.succ .zero)) (.sort .zero) .default
  isUnsafe := false }

def spec05DepProofBoxInfo : ConstantInfo := .axiomInfo {
  name := spec05DepProofBoxName
  levelParams := []
  type := .forallE `α (.sort (.succ .zero))
    (.forallE `value (.bvar 0) (.sort .zero) .default) .implicit
  isUnsafe := false }

def spec05NegativeMap : ConstMap :=
  ((({} : ConstMap).insert spec05TypeBoxName spec05TypeBoxInfo).insert
    spec05ProofBoxName spec05ProofBoxInfo).insert
      spec05DepProofBoxName spec05DepProofBoxInfo

def spec05NegativeContext : AddInductive.Context where
  env := Kernel.Environment.ofConstants `_spec05Negative spec05NegativeMap
  lparams := []
  safety := .safe
  allowPrimitive := false

def spec05UnsafeNegativeContext : AddInductive.Context :=
  { spec05NegativeContext with safety := .unsafe }

def spec05NegativeType (name ctorName : Name) (ctorType : Expr) :
    InductiveType where
  name := name
  type := .sort (.succ .zero)
  ctors := [{ name := ctorName, type := ctorType }]

def spec05NestedNegativeName : Name :=
  `Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05NestedNegative

def spec05NestedNegativeMkName : Name :=
  .str spec05NestedNegativeName "mk"

def spec05NestedNegativeConst : Expr :=
  .const spec05NestedNegativeName []

def spec05NestedNegativeField : Expr :=
  .forallE `_
    (.forallE `_ spec05NestedNegativeConst (.sort .zero) .default)
    spec05NestedNegativeConst .default

def spec05NestedNegativeType : InductiveType :=
  spec05NegativeType spec05NestedNegativeName spec05NestedNegativeMkName
    (.forallE `field spec05NestedNegativeField
      spec05NestedNegativeConst .default)

def spec05FamilyNonrecursiveName : Name :=
  `Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05FamilyNonrecursive

def spec05FamilyNonrecursiveMkName : Name :=
  .str spec05FamilyNonrecursiveName "mk"

def spec05FamilyNonrecursiveConst : Expr :=
  .const spec05FamilyNonrecursiveName []

def spec05FamilyNonrecursiveType : InductiveType :=
  spec05NegativeType spec05FamilyNonrecursiveName
    spec05FamilyNonrecursiveMkName
    (.forallE `field
      (.app (.const spec05TypeBoxName []) spec05FamilyNonrecursiveConst)
      spec05FamilyNonrecursiveConst .default)

def spec05FamilyProofName : Name :=
  `Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05FamilyProof

def spec05FamilyProofMkName : Name :=
  .str spec05FamilyProofName "mk"

def spec05FamilyProofConst : Expr :=
  .const spec05FamilyProofName []

def spec05FamilyProofType : InductiveType :=
  spec05NegativeType spec05FamilyProofName spec05FamilyProofMkName
    (.forallE `proof
      (.app (.const spec05ProofBoxName []) spec05FamilyProofConst)
      spec05FamilyProofConst .default)

def spec05RecursiveDependencyName : Name :=
  `Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05RecursiveDependency

def spec05RecursiveDependencyMkName : Name :=
  .str spec05RecursiveDependencyName "mk"

def spec05RecursiveDependencyConst : Expr :=
  .const spec05RecursiveDependencyName []

def spec05RecursiveDependencyProof : Expr :=
  .app (.app (.const spec05DepProofBoxName [])
    spec05RecursiveDependencyConst) (.bvar 0)

def spec05RecursiveDependencyType : InductiveType :=
  spec05NegativeType spec05RecursiveDependencyName
    spec05RecursiveDependencyMkName
    (.forallE `recursive spec05RecursiveDependencyConst
      (.forallE `proof spec05RecursiveDependencyProof
        spec05RecursiveDependencyConst .default) .default)

def spec05UniverseRejectName : Name :=
  `Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05UniverseReject

def spec05UniverseRejectMkName : Name :=
  .str spec05UniverseRejectName "mk"

def spec05UniverseRejectConst : Expr :=
  .const spec05UniverseRejectName []

def spec05UniverseRejectType : InductiveType :=
  spec05NegativeType spec05UniverseRejectName spec05UniverseRejectMkName
    (.forallE `α (.sort (.succ .zero)) spec05UniverseRejectConst .default)

def spec05CandidateError (source : InductiveType) : Option String :=
  match AddInductive.buildNormalizationCandidate 0 [source] 0 false
      spec05NegativeContext with
  | .error (.other message) => some message
  | _ => none

#guard spec05CandidateError spec05NestedNegativeType = some
  "arg #1 of 'Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05NestedNegative.mk' has a non positive occurrence of the datatypes being declared"

#guard spec05CandidateError spec05FamilyNonrecursiveType = some
  "arg #1 of 'Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05FamilyNonrecursive.mk' has a non valid occurrence of the datatypes being declared"

#guard spec05CandidateError spec05FamilyProofType = some
  "arg #1 of 'Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05FamilyProof.mk' has a non valid occurrence of the datatypes being declared"

#guard spec05CandidateError spec05RecursiveDependencyType = some
  "arg #2 of 'Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05RecursiveDependency.mk' has a non valid occurrence of the datatypes being declared"

#guard spec05CandidateError spec05UniverseRejectType = some
  "universe level of type_of(arg #1) of 'Ix.Theory.Named.InductiveFixtures.KernelDifferential.Spec05UniverseReject.mk' is too big for the corresponding inductive datatype"

def spec05RecursiveDependencyPreFamilyError : Option String :=
  match AddInductive.buildNormalizationCandidate 0
      [spec05RecursiveDependencyType] 0 true spec05UnsafeNegativeContext with
  | .error _ => none
  | .ok candidate =>
      match AddInductive.checkInductiveTypes 0
          #[spec05RecursiveDependencyType]
          (fun stats =>
            AddInductive.checkConstructorPreFamilySafety stats
              candidate.families.singleton.familyType.type.view
              candidate.families.singleton.constructors)
          spec05UnsafeNegativeContext with
      | .error (.other message) => some message
      | _ => none

#guard spec05RecursiveDependencyPreFamilyError =
  some "constructor depends on an omitted recursive local"

end Ix.Theory.Named.InductiveReplayFixtures
