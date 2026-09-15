/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Build
import Tests.Theory.Certified

open Ix.Theory

namespace Tests.Theory.Standard

open Ix.Theory.Model Ix.Theory.Certified Ix.Theory.Certified.Basis Ix.Theory.Certificate
open Tests.Theory.Certified (primitives)

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def eq : ConstRef Nat := .member 100 0
def refl : ConstRef Nat := .ctor 100 0 0
def iff : ConstRef Nat := .member 102 0
def ne : ConstRef Nat := .member 104 0
def neIntro : ConstRef Nat := .ctor 104 0 0
def propextRef : ConstRef Nat := .member 106 0
def choiceRef : ConstRef Nat := .member 107 0

def propextSpec : Certified.Standard.Spec Nat :=
  .propext eq refl (.member 101 0) iff (.ctor 102 0 0) (.member 103 0)
def choiceSpec : Certified.Standard.Spec Nat := .choice ne neIntro (.member 105 0)

def declaration : Nat → Const Nat
  | 10 => PrimitiveSignature.falseDeclaration
  | 11 => primitives.falseElimDeclaration
  | 100 => Equality.shape.source 100
  | 101 => Equality.shape.recursorSource 100 101 .large true
  | 102 => Iff.shape.source 102
  | 103 => Iff.shape.recursorSource 102 103 .large
  | 104 => Nonempty.shape.source 104
  | 105 => Nonempty.shape.recursorSource 104 105 .small
  | 106 => propextSpec.source
  | 107 => choiceSpec.source
  | _ => .axiom 0 (.sort .zero) .safe

def store (alter : Nat → Const Nat → Const Nat := fun _ c => c) : Store Nat where
  dom := [10, 11, 100, 101, 102, 103, 104, 105, 106, 107]
  nodup := by decide
  blocks b := if b ∈ [10, 11, 100, 101, 102, 103, 104, 105, 106, 107] then
    some ⟨[alter b (declaration b)]⟩ else none
  mem_dom b := by split <;> simp_all

def input (n : Nat) (proof proposition : AExpr Nat) : ProofInput Nat :=
  ⟨store, n, proof.erase, proposition.erase⟩

def accepted (n : Nat) (proof proposition : AExpr Nat) : Bool :=
  let input := input n proof proposition
  (Certificate.proofWitness? 2000 primitives input).any (acceptsCertified.{0,0} 2000 primitives input)

#guard accepted 0 (.const propextRef []) propextSpec.type
#guard accepted 0 (.const choiceRef [.zero]) (choiceSpec.type.instL [.zero])

def chosen (u : VLevel) (A a : AExpr Nat) : AExpr Nat :=
  .appN (.const choiceRef [u]) [A, Nonempty.introduction neIntro u A a]

-- The choice result is used at its actual positive source universe as an
-- argument to reflexivity, under arbitrary A and a : A.
def choiceRefl (u : VLevel) : AExpr Nat :=
  .lam .always (.sort u) (.lam .always (.bvar 0)
    (Equality.reflexivity refl u (.bvar 1) (chosen u (.bvar 1) (.bvar 0))))
def choiceReflType (u : VLevel) : AExpr Nat :=
  .forallE .always (.sort u) (.forallE .always (.bvar 0)
    (Equality.applied eq u (.bvar 1) (chosen u (.bvar 1) (.bvar 0)) (chosen u (.bvar 1) (.bvar 0))))

#guard accepted 1 (choiceRefl (.param 0)) (choiceReflType (.param 0))
#guard accepted 0 (choiceRefl (.succ .zero)) (choiceReflType (.succ .zero))
#guard accepted 0 (choiceRefl (.succ (.succ .zero))) (choiceReflType (.succ (.succ .zero)))

def kDomain (P : AExpr Nat) : AExpr Nat :=
  Equality.applied eq (.succ .zero) (.sort .zero) P P
def kMotive (P : AExpr Nat) : AExpr Nat :=
  .lam .never (.sort .zero)
    (.lam .never (Equality.applied eq (.succ .zero) (.sort .zero) (P.liftN 1) (.bvar 0)) (.sort .zero))
def kComputed (P proof : AExpr Nat) : AExpr Nat :=
  .appN (.const (.member 101 0) [.succ .zero, .succ .zero])
    [.sort .zero, P, kMotive P, P, P, proof]
def kProof : AExpr Nat :=
  .lam .always (.sort .zero) (.lam .always (.bvar 0)
    (.lam .always (kDomain (.bvar 1)) (.bvar 1)))
def kProposition : AExpr Nat :=
  .forallE .always (.sort .zero) (.forallE .always (.bvar 0)
    (.forallE .always (kDomain (.bvar 1)) (kComputed (.bvar 2) (.bvar 0))))

-- The major premise is an arbitrary proof of reflexive equality, not a
-- constructor application. Admission permits the exact Eq K metadata, and
-- typed proof irrelevance plus the admitted iota law justify this conversion.
#guard accepted 0 kProof kProposition

#guard Equality.shape.SupportsK (β := Nat)
#guard ¬ Nonempty.shape.SupportsK (β := Nat)

def propextInput := input 0 (.const propextRef []) propextSpec.type
def propextWitness := Certificate.proofWitness? 2000 primitives propextInput

#guard propextWitness.isSome

def falseAxiom (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 106 then .axiom 0 primitives.falseExpr .safe else c
def unsafeAxiom (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 106 then .axiom 0 propextSpec.type.erase .unsafe else c
def wrongArity (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 106 then .axiom 1 propextSpec.type.erase .safe else c

#guard [falseAxiom, unsafeAxiom, wrongArity].all fun alter => propextWitness.any fun witness =>
  !acceptsCertified.{0,0} 2000 primitives { propextInput with store := store alter } witness

-- A standard schema cannot be admitted before its realized prerequisites.
#guard propextWitness.any fun witness =>
  let axioms := witness.declarations.filter fun declaration => match declaration with
    | .standard _ => true
    | _ => false
  let rest := witness.declarations.filter fun declaration => match declaration with
    | .standard _ => false
    | _ => true
  !acceptsCertified.{0,0} 2000 primitives propextInput { witness with declarations := axioms ++ rest }

-- Removing the actual dependent eliminator's certificate is also a failure.
#guard propextWitness.any fun witness =>
  let declarations := witness.declarations.filter fun declaration => match declaration with
    | .ordinary w => w.source != 100
    | _ => true
  !acceptsCertified.{0,0} 2000 primitives propextInput { witness with declarations }

end Tests.Theory.Standard
