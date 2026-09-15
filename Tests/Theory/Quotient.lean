/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Build
import Tests.Theory.Certified

open Ix.Theory

namespace Tests.Theory.Quotient

open Ix.Theory.Model Ix.Theory.Certified Ix.Theory.Certified.Basis
open Tests.Theory.Certified (primitives)

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

def refs : Certified.Quotient.Refs Nat where
  eq := .member 100 0
  eqRefl := .ctor 100 0 0
  eqRec := .member 101 0
  type := .member 200 0
  ctor := .member 201 0
  lift := .member 202 0
  ind := .member 203 0
  sound := .member 204 0

def declaration : Nat → Const Nat
  | 10 => PrimitiveSignature.falseDeclaration
  | 11 => primitives.falseElimDeclaration
  | 100 => Equality.shape.source 100
  | 101 => Equality.shape.recursorSource 100 101 .large true
  | 200 => refs.source .type
  | 201 => refs.source .ctor
  | 202 => refs.source .lift
  | 203 => refs.source .ind
  | 204 => refs.source .sound
  | _ => .axiom 0 (.sort .zero) .safe

def addresses : List Nat := [10, 11, 100, 101, 200, 201, 202, 203, 204]

def store (alter : Nat → Const Nat → Const Nat := fun _ c => c) : Store Nat where
  dom := addresses
  nodup := by decide
  blocks b := if b ∈ addresses then some ⟨[alter b (declaration b)]⟩ else none
  mem_dom b := by split <;> simp_all

def input (n : Nat) (proof proposition : AExpr Nat) : ProofInput Nat :=
  ⟨store, n, proof.erase, proposition.erase⟩

def accepted (n : Nat) (proof proposition : AExpr Nat) : Bool :=
  let input := input n proof proposition
  (Certificate.proofWitness? 3000 primitives input).any (acceptsCertified.{0,0} 3000 primitives input)

#guard (Certificate.Quotient.refs? store refs.type).isSome
#guard (Certificate.Quotient.refs? store refs.sound).isSome

-- Exact soundness and dependent Prop induction are themselves closed logical
-- propositions, admitted through source discovery and executable validation.
#guard accepted 1 (.const refs.sound [.param 0]) (Certified.Quotient.soundType refs)
#guard accepted 1 (.const refs.ind [.param 0]) (Certified.Quotient.indType refs)

def relation (u : VLevel) (A : AExpr Nat) : AExpr Nat :=
  .lam .never A (.lam .never (A.liftN 1)
    (Equality.applied refs.eq u (A.liftN 2) (.bvar 1) (.bvar 0)))

def constantInvariant (u v : VLevel) (A B b : AExpr Nat) : AExpr Nat :=
  .lamN .always [A, A.liftN 1, .appN ((relation u A).liftN 2) [.bvar 1, .bvar 0]]
    (Equality.reflexivity refs.eqRefl v (B.liftN 3) (b.liftN 3))

def computed (u v : VLevel) (A B b a : AExpr Nat) : AExpr Nat :=
  .appN (.const refs.lift [u, v]) [A, relation u A, B,
    .lam (zeroCondition v) A (b.liftN 1), constantInvariant u v A B b,
    Certified.Quotient.constructed refs u A (relation u A) a]

def binders (u : VLevel) : List (AExpr Nat) := [.sort u, .bvar 0, .sort .zero, .bvar 0]
def betaProof (u : VLevel) : AExpr Nat := .lamN .always (binders u) (.bvar 0)
def betaProposition (u : VLevel) : AExpr Nat :=
  .forallN .always (binders u) (computed u (.succ .zero) (.bvar 3) (.sort .zero) (.bvar 1) (.bvar 2))

-- The original statement contains a quotient lift returning a proposition.
-- Conversion to that statement requires the newly admitted computation law.
#guard accepted 1 (betaProof (.param 0)) (betaProposition (.param 0))
#guard accepted 0 (betaProof .zero) (betaProposition .zero)
#guard accepted 0 (betaProof (.succ .zero)) (betaProposition (.succ .zero))

def propLiftProof (u : VLevel) : AExpr Nat :=
  .lamN .always (binders u) (computed u .zero (.bvar 3) (.bvar 1) (.bvar 0) (.bvar 2))
def propLiftProposition (u : VLevel) : AExpr Nat := .forallN .always (binders u) (.bvar 1)

#guard accepted 1 (propLiftProof (.param 0)) (propLiftProposition (.param 0))
#guard accepted 0 (propLiftProof .zero) (propLiftProposition .zero)

def betaInput := input 1 (betaProof (.param 0)) (betaProposition (.param 0))
def betaWitness := Certificate.proofWitness? 3000 primitives betaInput

#guard betaWitness.isSome

def wrongKind (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 200 then .quot .ctor 1 Certified.Quotient.typeType.erase else c
def wrongArity (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 201 then .quot .ctor 2 (Certified.Quotient.ctorType refs).erase else c
def falseSound (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 204 then .axiom 1 primitives.falseExpr .safe else c
def unsafeSound (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 204 then .axiom 1 (Certified.Quotient.soundType refs).erase .unsafe else c
def wrongLift (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 202 then .quot .lift 2 (Certified.Quotient.indType refs).erase else c

-- A valid certificate for the original declarations must fail against each
-- altered source store; this tests the validator, not just producer decline.
#guard [wrongKind, wrongArity, falseSound, unsafeSound, wrongLift].all fun alter =>
  betaWitness.any fun witness =>
    !acceptsCertified.{0,0} 3000 primitives { betaInput with store := store alter } witness

#guard betaWitness.any fun witness =>
  let declarations := witness.declarations.map fun declaration => match declaration with
    | .quotient q => DeclarationWitness.quotient { q with types := q.types.drop 1 }
    | other => other
  !acceptsCertified.{0,0} 3000 primitives betaInput { witness with declarations }

#guard betaWitness.any fun witness =>
  let declarations := witness.declarations.map fun declaration => match declaration with
    | .quotient q => DeclarationWitness.quotient { q with liftRule := q.indRule }
    | other => other
  !acceptsCertified.{0,0} 3000 primitives betaInput { witness with declarations }

#guard betaWitness.any fun witness =>
  let declarations := witness.declarations.map fun declaration => match declaration with
    | .quotient q => DeclarationWitness.quotient { q with refs := { q.refs with ctor := q.refs.type } }
    | other => other
  !acceptsCertified.{0,0} 3000 primitives betaInput { witness with declarations }

#guard betaWitness.any fun witness =>
  let quotient := witness.declarations.filter fun declaration => match declaration with
    | .quotient _ => true
    | _ => false
  let rest := witness.declarations.filter fun declaration => match declaration with
    | .quotient _ => false
    | _ => true
  !acceptsCertified.{0,0} 3000 primitives betaInput { witness with declarations := quotient ++ rest }

end Tests.Theory.Quotient
