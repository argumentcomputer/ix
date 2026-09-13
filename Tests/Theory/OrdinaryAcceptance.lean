/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Theory.Ordinary
import Tests.Theory.Acceptance
import Ix.Theory.Certificate.Build

open Ix.Theory

/-! Closed acceptance through atomic ordinary admission and generated equation
certificates. These are abstract-source tests; serialized VM coverage has its
own adapter and corpus. -/

namespace Tests.Theory.OrdinaryAcceptance

open Ix.Theory.Model Ix.Theory.Certified Ix.Theory.Certified.Ordinary Ix.Theory.Certificate
open Tests.Theory.Certified (primitives)
open Tests.Theory.Ordinary (natShape listShape indexedShape emptyProp singletonProp manyProp dataProp)

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

def storeFor (shape : Shape Nat) (mode : Inductive.ElimMode)
    (recursorOverride : Option (Const Nat) := none) : Store Nat where
  dom := [10, 11, 100, 101]
  nodup := by decide
  blocks b :=
    if b = 10 then some ⟨[PrimitiveSignature.falseDeclaration]⟩
    else if b = 11 then some ⟨[primitives.falseElimDeclaration]⟩
    else if b = 100 then some ⟨[shape.source 100]⟩
    else if b = 101 then some ⟨[recursorOverride.getD (shape.recursorSource 100 101 mode)]⟩ else none
  mem_dom b := by
    by_cases h0 : b = 10 <;> by_cases h1 : b = 11 <;>
      by_cases hs : b = 100 <;> by_cases hr : b = 101 <;> simp_all

def admitted (shape : Shape Nat) (mode : Inductive.ElimMode) : Bool :=
  match initialize?.{0,0} primitives (storeFor shape mode),
      Certificate.Ordinary.block? 1000 primitives.environment shape 100 101 mode with
  | some state, some witness => (admitOrdinary?.{0,0} 1000 state witness).isSome
  | _, _ => false

#guard admitted natShape .large
#guard admitted listShape .large
#guard admitted indexedShape .large
#guard admitted emptyProp .large
#guard admitted singletonProp .large
#guard admitted manyProp .small
#guard !admitted manyProp .large
#guard !admitted dataProp .large

def identity : AExpr Nat := .lam .always (.sort .zero) (.lam .always (.bvar 0) (.bvar 0))
def identityType : AExpr Nat := .forallE .always (.sort .zero) (.forallE .always (.bvar 0) (.bvar 1))
def proposition (computed : AExpr Nat) : AExpr Nat :=
  .forallE .always (.sort .zero) (.forallE .always (.bvar 0) computed)

def proofWitness? (shape : Shape Nat) (mode : Inductive.ElimMode) (proof proposition : AExpr Nat) :
    Option (ProofWitness Nat) := do
  let block ← Certificate.Ordinary.block? 1000 primitives.environment shape 100 101 mode
  let entries := shape.publishedEnvironment primitives.environment 100 101 mode
  let P ← inferAnnotated? 1000 0 entries [] proposition
  let Pw ← castWith? 1000 0 entries [] P (.sort .zero)
  let e ← inferAnnotated? 1000 0 entries [] proof
  let ew ← castWith? 1000 0 entries [] e proposition
  return ⟨[.ordinary block], annotations proof, annotations proposition, ew, Pw⟩

def accepted (shape : Shape Nat) (mode : Inductive.ElimMode) (proof proposition : AExpr Nat)
    (recursorOverride : Option (Const Nat) := none) : Bool :=
  match proofWitness? shape mode proof proposition with
  | none => false
  | some witness => acceptsCertified.{0,0} 2000 primitives
      ⟨storeFor shape mode recursorOverride, 0, proof.erase, proposition.erase⟩ witness

def family : AExpr Nat := .const (.member 100 0) []
def zero : AExpr Nat := .const (.ctor 100 0 0) []
def succ (n : AExpr Nat) : AExpr Nat := .app (.const (.ctor 100 0 1) []) n

def natComputed : AExpr Nat := .appN (.const (.member 101 0) [.succ .zero])
  [.lam .never family (.sort .zero), .bvar 1,
    .lam .never family (.lam .never (.sort .zero) (.bvar 0)), succ zero]

#guard (proofWitness? natShape .large identity (proposition natComputed)).isSome
#guard accepted natShape .large identity (proposition natComputed)

def listType : AExpr Nat := .app (.const (.member 100 0) [.zero]) (.sort .zero)
def nil : AExpr Nat := .app (.const (.ctor 100 0 0) [.zero]) (.sort .zero)
def cons : AExpr Nat := .appN (.const (.ctor 100 0 1) [.zero]) [.sort .zero, .bvar 1, nil]
def listComputed : AExpr Nat := .appN (.const (.member 101 0) [.succ .zero, .zero])
  [.sort .zero, .lam .never listType (.sort .zero), .bvar 1,
    .lam .never (.sort .zero) (.lam .never listType (.lam .never (.sort .zero) (.bvar 0))), cons]

#guard (proofWitness? listShape .large identity (proposition listComputed)).isSome
#guard accepted listShape .large identity (proposition listComputed)

def indexedComputed : AExpr Nat := .appN (.const (.member 101 0) [.succ .zero])
  [.lam .never (.sort (.succ .zero)) (.lam .never (.app family (.bvar 0)) (.sort .zero)),
    .bvar 1, .sort .zero, zero]

#guard accepted indexedShape .large identity (proposition indexedComputed)

def functionalShape : Shape Nat :=
  ⟨0, [], [], .succ .zero, [⟨[], [], []⟩, ⟨[], [⟨[.sort .zero], []⟩], []⟩]⟩
def functionalComputed : AExpr Nat := .appN (.const (.member 101 0) [.succ .zero])
  [.lam .never family (.sort .zero), .bvar 1,
    .lam .never (.forallE .never (.sort .zero) family)
      (.lam .never (.forallE .never (.sort .zero) (.sort .zero)) (.app (.bvar 0) (.bvar 3))),
    succ (.lam .never (.sort .zero) zero)]

#guard admitted functionalShape .large
#guard (proofWitness? functionalShape .large identity (proposition functionalComputed)).isSome
#guard accepted functionalShape .large identity (proposition functionalComputed)

def smallProof : AExpr Nat := .lam .always (.sort .zero) (.lam .always (.bvar 0)
  (.appN (.const (.member 101 0) []) [.lam .never family (.bvar 2), .bvar 0, .bvar 0, zero]))
#guard accepted manyProp .small smallProof identityType

-- Source rule tampering cannot be repaired by a valid shape/type certificate.
def forgedNatRecursor : Const Nat :=
  match natShape.recursorSource 100 101 .large with
  | .recursor u p i m n type (_ :: rules) k safety =>
    .recursor u p i m n type (⟨0, .sort .zero⟩ :: rules) k safety
  | other => other
#guard !accepted natShape .large identity (proposition natComputed) (some forgedNatRecursor)

-- A staged signature has no equation; the public environment gets the law
-- only after the entire block checker succeeds.
def natEquationLicensed (entries : Environment Nat) : Bool := Id.run do
  let some law := (natShape.recursorLaws 100 101 .large)[0]? | return false
  return (verifyConversion.{0,0} 1000 0 entries []
    (law.lhs.instL [.succ .zero]) (law.rhs.instL [.succ .zero])
    (.equation (.member 101 0) 0 [.succ .zero])).isSome

#guard natEquationLicensed (natShape.publishedEnvironment primitives.environment 100 101 .large)
#guard !natEquationLicensed (natShape.recursorEnvironment primitives.environment 100 101 .large)

/-- The generic driver recovers its shape and declaration order from the raw
store. No description is provided to witness construction. -/
def sourceAccepted (shape : Shape Nat) (mode : Inductive.ElimMode)
    (proof proposition : AExpr Nat) : Bool :=
  let input : ProofInput Nat := ⟨storeFor shape mode, 0, proof.erase, proposition.erase⟩
  (Certificate.proofWitness? 2000 primitives input).any
    (acceptsCertified.{0,0} 2000 primitives input)

#guard sourceAccepted natShape .large identity (proposition natComputed)
#guard sourceAccepted listShape .large identity (proposition listComputed)
#guard sourceAccepted indexedShape .large identity (proposition indexedComputed)
#guard sourceAccepted functionalShape .large identity (proposition functionalComputed)
#guard sourceAccepted manyProp .small smallProof identityType

-- The source parser also reconstructs dependent telescopes and more than one
-- recursive field. It never silently removes a recursive dependency.
#guard [Tests.Theory.Ordinary.wShape, Tests.Theory.Ordinary.dependentIndices].all fun shape =>
  (Certificate.Ordinary.description? 1000 primitives.environment 100 (shape.source 100)).isSome

def multipleFields : Shape Nat :=
  ⟨0, [], [], .succ .zero, [⟨[], [], []⟩, ⟨[], [⟨[], []⟩, ⟨[], []⟩], []⟩]⟩
#guard (Certificate.Ordinary.description? 1000 primitives.environment 100
  (multipleFields.source 100)).isSome
#guard (Certificate.Ordinary.removeVariables? 1 (.bvar 0 : VExpr Nat)).isNone

end Tests.Theory.OrdinaryAcceptance
