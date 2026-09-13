/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Accept
import Tests.Theory.Checker
import Tests.Theory.Certified

open Ix.Theory

namespace Tests.Theory.Acceptance

open Ix.Theory.Certified Ix.Theory.Model
open Tests.Theory.Checker (identity identityType identityWitness)
open Tests.Theory.Certified (primitives primitiveStore)

def prelude : Store Nat :=
  primitiveStore PrimitiveSignature.falseDeclaration primitives.falseElimDeclaration

def identityAnnotations (l : VLevel) : AnnotationTree :=
  .lam (zeroCondition l).toRaw .leaf (.lam (zeroCondition l).toRaw .leaf .leaf)

def identityTypeAnnotations (l : VLevel) : AnnotationTree :=
  .forallE (zeroCondition l).toRaw .leaf (.forallE (zeroCondition l).toRaw .leaf .leaf)

def identityTypeLevel (l : VLevel) : VLevel := .imax (.succ l) (.imax l l)

def identityTypeWitness (l : VLevel) : TypingWitness Nat :=
  .forallE (.succ l) (.imax l l) .sort (.forallE l l .bvar .bvar)

def identityPropositionWitness : TypingWitness Nat :=
  .conv (.sort (identityTypeLevel .zero)) (.succ .zero) (identityTypeWitness .zero) .sort .sort

def identityInput : ProofInput Nat :=
  ⟨prelude, 0, (identity .zero).erase, (identityType .zero).erase⟩

def identityProofWitness : ProofWitness Nat :=
  ⟨[], identityAnnotations .zero, identityTypeAnnotations .zero,
    identityWitness .zero, identityPropositionWitness⟩

#guard acceptsCertified.{0,0} 50 primitives identityInput identityProofWitness

def withDefinition (declaration : Const Nat) : Store Nat where
  dom := [10, 11, 12]
  nodup := by decide
  blocks b :=
    if b = 10 then some ⟨[PrimitiveSignature.falseDeclaration]⟩
    else if b = 11 then some ⟨[primitives.falseElimDeclaration]⟩
    else if b = 12 then some ⟨[declaration]⟩ else none
  mem_dom b := by
    by_cases h : b = 10 <;> by_cases h' : b = 11 <;> by_cases h'' : b = 12 <;> simp_all

def idRef : ConstRef Nat := .member 12 0

def idDeclaration (kind : DefKind := .definition) : Const Nat :=
  .defn 1 kind (identityType (.param 0)).erase (identity (.param 0)).erase .safe

def idDefinitionWitness : DefinitionWitness Nat :=
  ⟨idRef, identityTypeAnnotations (.param 0), identityAnnotations (.param 0),
    identityTypeLevel (.param 0), identityTypeWitness (.param 0), identityWitness (.param 0)⟩

def idDefinitionInput (kind : DefKind := .definition) : ProofInput Nat :=
  ⟨withDefinition (idDeclaration kind), 0, .const idRef [.zero], (identityType .zero).erase⟩

def idDefinitionProofWitness : ProofWitness Nat :=
  { identityProofWitness with
    declarations := [.definition idDefinitionWitness]
    proofAnnotations := .leaf
    proofWitness := .const }

#guard acceptsCertified.{0,0} 50 primitives (idDefinitionInput .definition) idDefinitionProofWitness
#guard acceptsCertified.{0,0} 50 primitives (idDefinitionInput .theorem) idDefinitionProofWitness
#guard acceptsCertified.{0,0} 50 primitives (idDefinitionInput .opaque) idDefinitionProofWitness

-- Positive-universe instantiation of the same admitted definition occurs as
-- an argument to a proposition-valued function.
def largeIdentityUse : AExpr Nat :=
  .app (.lam .always (identityType (.succ .zero)) (identity .zero))
    (.const idRef [.succ .zero])

def largeIdentityUseAnnotations : AnnotationTree :=
  .app (.lam (some []) (identityTypeAnnotations (.succ .zero)) (identityAnnotations .zero)) .leaf

def largeIdentityUseWitness : TypingWitness Nat :=
  .app .always (identityType (.succ .zero)) (identityType .zero)
    (.lam (identityTypeLevel (.succ .zero)) .zero (identityType .zero)
      (identityTypeWitness (.succ .zero)) identityPropositionWitness (identityWitness .zero))
    .const

#guard acceptsCertified.{0,0} 70 primitives
  { idDefinitionInput with proof := largeIdentityUse.erase }
  { idDefinitionProofWitness with
    proofAnnotations := largeIdentityUseAnnotations
    proofWitness := largeIdentityUseWitness }

-- Every declaration kind still checks its supplied body.
def forgedBodyInput (kind : DefKind) : ProofInput Nat :=
  { idDefinitionInput kind with
    store := withDefinition (.defn 1 kind (identityType (.param 0)).erase (.sort .zero) .safe) }
#guard !acceptsCertified.{0,0} 50 primitives (forgedBodyInput .definition) idDefinitionProofWitness
#guard !acceptsCertified.{0,0} 50 primitives (forgedBodyInput .theorem) idDefinitionProofWitness
#guard !acceptsCertified.{0,0} 50 primitives (forgedBodyInput .opaque) idDefinitionProofWitness

-- Object axioms cannot enter through the declaration fold.
#guard !acceptsCertified.{0,0} 50 primitives
  { idDefinitionInput with
    store := withDefinition (.axiom 1 (identityType (.param 0)).erase .safe) }
  idDefinitionProofWitness

-- Missing, repeated, forward, and self dependencies fail at admission.
#guard !acceptsCertified.{0,0} 50 primitives (idDefinitionInput)
  { idDefinitionProofWitness with declarations := [] }
#guard !acceptsCertified.{0,0} 50 primitives (idDefinitionInput)
  { idDefinitionProofWitness with declarations := [.definition idDefinitionWitness, .definition idDefinitionWitness] }
#guard !acceptsCertified.{0,0} 50 primitives
  { idDefinitionInput with
    store := withDefinition
      (.defn 1 .definition (identityType (.param 0)).erase (.const idRef [.param 0]) .safe) }
  { idDefinitionProofWitness with
    declarations := [.definition { idDefinitionWitness with bodyAnnotations := .leaf, bodyWitness := .const }] }

-- A changed original statement is checked, even with an otherwise valid proof.
#guard !acceptsCertified.{0,0} 50 primitives
  { identityInput with proposition := primitives.falseExpr }
  { identityProofWitness with propositionAnnotations := .leaf, propositionWitness := .const }

-- Complete primitive metadata is checked before even a constant-free proof.
#guard !acceptsCertified.{0,0} 50 primitives
  { identityInput with
    store := primitiveStore (.axiom 0 (.sort .zero) .safe) primitives.falseElimDeclaration }
  identityProofWitness

def falseA : AExpr Nat := .const primitives.falseType []
def eliminatorProposition : AExpr Nat := primitives.falseElimReading.instL [.zero]
def eliminatorAnnotations : AnnotationTree :=
  .forallE (some []) (.forallE none .leaf .leaf)
    (.forallE (some []) .leaf (.app .leaf .leaf))

def eliminatorTypeLevel : VLevel :=
  .imax (.imax .zero (.succ .zero)) (.imax .zero .zero)

def eliminatorPropositionWitness : TypingWitness Nat :=
  .conv (.sort eliminatorTypeLevel) (.succ .zero)
    (.forallE (.imax .zero (.succ .zero)) (.imax .zero .zero)
      (.forallE .zero (.succ .zero) .const .sort)
      (.forallE .zero .zero .const (.app .never falseA (.sort .zero) .bvar .bvar)))
    .sort .sort

def eliminatorInput : ProofInput Nat :=
  ⟨prelude, 0, .const primitives.falseElim [.zero], eliminatorProposition.erase⟩
def eliminatorProofWitness : ProofWitness Nat :=
  ⟨[], .leaf, eliminatorAnnotations, .const, eliminatorPropositionWitness⟩

#guard acceptsCertified.{0,0} 50 primitives eliminatorInput eliminatorProofWitness
#guard !acceptsCertified.{0,0} 50 primitives
  { eliminatorInput with proof := .const primitives.falseElim [] } eliminatorProofWitness
#guard !acceptsCertified.{0,0} 50 primitives
  { eliminatorInput with proof := .const primitives.falseElim [.param 0] } eliminatorProofWitness

end Tests.Theory.Acceptance
