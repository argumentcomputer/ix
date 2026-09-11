/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.InductiveFixtures

open Ix.Theory (VLevel)

/-!
# Complete singleton-family parity inputs

This module is the Theory-side inventory for Spec-07.  Each row owns the exact
raw declaration together with the one checked generation artifact consumed by
the kernel differential and environment-replay matrix.  `Unit` is represented
honestly by the kernel's polymorphic `PUnit` family; the reducible `Unit`
definition itself is pinned on the Verify side.
-/

namespace Ix.Theory.Named.InductiveFixtures

open VInductDecl

private def permC07 (constant : VConstant) (levels : List VLevel) :
    VConstant :=
  ⟨constant.uvars, constant.type.instL levels⟩

/-! ## Checked artifacts for the pre-existing fixed rows -/

def boolChecked : boolDecl.Checked := boolDecl.checked?.get (by decide)

def boolGenerationChecked : GenerationChecked boolDecl :=
  (identityGeneration? boolDecl).get (by decide)

def listChecked : listDecl.Checked := listDecl.checked?.get (by decide)

def listGenerationChecked : GenerationChecked listDecl :=
  (identityGeneration? listDecl).get (by decide)

def optionChecked : optionDecl.Checked := optionDecl.checked?.get (by decide)

def optionGenerationChecked : GenerationChecked optionDecl :=
  (identityGeneration? optionDecl).get (by decide)

def prodChecked : prodDecl.Checked := prodDecl.checked?.get (by decide)

def prodGenerationChecked : GenerationChecked prodDecl :=
  (identityGeneration? prodDecl).get (by decide)

def heqChecked : heqDecl.Checked := heqDecl.checked?.get (by decide)

def heqGenerationChecked : GenerationChecked heqDecl :=
  (identityGeneration? heqDecl).get (by decide)

def orGenerationChecked : GenerationChecked orDecl :=
  (identityGeneration? orDecl).get (by decide)

def andGenerationChecked : GenerationChecked andDecl :=
  (identityGeneration? andDecl).get (by decide)

/-! ## Fin -/

def finType : VInductiveType where
  name := ``Fin
  uvars := 0
  type := vconst(type_of% @Fin).type
  ctors := [⟨vconst(type_of% @Fin.mk), ``Fin.mk⟩]

def finDecl : VInductDecl := ⟨0, 1, [finType]⟩

def finChecked : finDecl.Checked := finDecl.checked?.get (by decide)

def finGenerationChecked : GenerationChecked finDecl :=
  (identityGeneration? finDecl).get (by decide)

example : finDecl.stage3 = true := rfl
example : finChecked.params = [.const ``Nat []] := rfl
example : finChecked.indices = [] := rfl
example : finChecked.resultLevel = .succ .zero := rfl
example : finChecked.elimination = .large := rfl
example : finChecked.kTarget = false := rfl
example : finChecked.constructors.length = 1 := rfl
example : finChecked.constructors[0].fields.length = 2 := rfl
example : finChecked.constructors[0].recursive = [] := rfl
example : finGenerationChecked.recursor =
    vconst(type_of% @Fin.rec) := rfl

/-! ## Vector -/

def vectorType : VInductiveType where
  name := ``Vector
  uvars := 1
  type := vconst(type_of% @Vector).type
  ctors := [⟨vconst(type_of% @Vector.mk), ``Vector.mk⟩]

def vectorDecl : VInductDecl := ⟨1, 2, [vectorType]⟩

def vectorChecked : vectorDecl.Checked := vectorDecl.checked?.get (by decide)

def vectorGenerationChecked : GenerationChecked vectorDecl :=
  (identityGeneration? vectorDecl).get (by decide)

example : vectorDecl.stage3 = true := rfl
example : vectorChecked.params =
    [.sort (.succ (.param 0)), .const ``Nat []] := rfl
example : vectorChecked.indices = [] := rfl
example : vectorChecked.resultLevel = .succ (.param 0) := rfl
example : vectorChecked.elimination = .large := rfl
example : vectorChecked.kTarget = false := rfl
example : vectorChecked.constructors.length = 1 := rfl
example : vectorChecked.constructors[0].fields.length = 2 := rfl
example : vectorChecked.constructors[0].recursive = [] := rfl
example : vectorGenerationChecked.recursor =
    permC07 (vconst(type_of% @Vector.rec)) [.param 1, .param 0] := rfl

/-! ## One authoritative singleton artifact inventory -/

/-- A source-indexed singleton artifact.  Merely constructing a row proves
that the public checked analyzer accepted that exact raw declaration and that
all downstream generation data came from the same checked path. -/
structure SingletonParityArtifact where
  label : Name
  source : VInductDecl
  generation : source.GenerationChecked

namespace SingletonParityArtifact

def typeName (artifact : SingletonParityArtifact) : Name :=
  artifact.generation.block.sourceType.name

def constructorNames (artifact : SingletonParityArtifact) : List Name :=
  artifact.generation.block.sourceType.ctors.map (·.name)

end SingletonParityArtifact

/-- The fixed Spec-07 positive matrix, in roadmap order.  The `Unit` row points
to `PUnit`, matching the actual v4.31 kernel representation rather than
inventing alias-level inductive metadata. -/
def singletonPositiveArtifacts : List SingletonParityArtifact :=
  [⟨``Nat, natDecl, natGenerationChecked⟩,
    ⟨``Bool, boolDecl, boolGenerationChecked⟩,
    ⟨``List, listDecl, listGenerationChecked⟩,
    ⟨``Option, optionDecl, optionGenerationChecked⟩,
    ⟨``Prod, prodDecl, prodGenerationChecked⟩,
    ⟨``Unit, punitDecl, punitGenerationChecked⟩,
    ⟨``Empty, emptyDecl, emptyGenerationChecked⟩,
    ⟨``Or, orDecl, orGenerationChecked⟩,
    ⟨``And, andDecl, andGenerationChecked⟩,
    ⟨``Eq, eqDecl, eqGenerationChecked⟩,
    ⟨``HEq, heqDecl, heqGenerationChecked⟩,
    ⟨``Fin, finDecl, finGenerationChecked⟩,
    ⟨``Vector, vectorDecl, vectorGenerationChecked⟩,
    ⟨``Acc, accDecl, accGenerationChecked⟩]

/-- The focused non-identity normalization rows retained alongside the fixed
standard-library matrix. -/
def singletonNormalizationArtifacts : List SingletonParityArtifact :=
  [⟨``AliasFormer, aliasFormerRawDecl, aliasFormerGenerationChecked⟩,
    ⟨``AliasRec, aliasRecRawDecl, aliasRecGenerationChecked⟩,
    ⟨``NormalizationMatrix, normalizationMatrixRawDecl,
      normalizationMatrixGenerationChecked⟩,
    ⟨``AnnotatedPi, annotatedPiRawDecl, annotatedPiGenerationChecked⟩,
    ⟨``AnnotatedParam, annotatedParamRawDecl,
      annotatedParamGenerationChecked⟩]

example : singletonPositiveArtifacts.length = 14 := rfl
example : singletonPositiveArtifacts.map (·.label) =
    [``Nat, ``Bool, ``List, ``Option, ``Prod, ``Unit, ``Empty, ``Or, ``And,
      ``Eq, ``HEq, ``Fin, ``Vector, ``Acc] := rfl
example : singletonPositiveArtifacts.map (·.typeName) =
    [``Nat, ``Bool, ``List, ``Option, ``Prod, ``PUnit, ``Empty, ``Or, ``And,
      ``Eq, ``HEq, ``Fin, ``Vector, ``Acc] := rfl
example : singletonNormalizationArtifacts.length = 5 := rfl

/-!
The inventory roots are trust-sensitive: pin their exact logical closure so
later fixture refactors cannot silently import a broader proof surface.
-/

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.singletonPositiveArtifacts [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveFixtures.singletonNormalizationArtifacts [propext, Quot.sound]

end Ix.Theory.Named.InductiveFixtures
