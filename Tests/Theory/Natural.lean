/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Theory.Standard

open Ix.Theory

namespace Tests.Theory.Natural

open Ix.Theory.Model Ix.Theory.Certified Ix.Theory.Certified.Basis Ix.Theory.Certificate
open Tests.Theory.Certified (primitives)

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def nat : AExpr Nat := .const (.member 200 0) []
def zero : AExpr Nat := .const (.ctor 200 0 0) []
def succ (n : AExpr Nat) : AExpr Nat := .app (.const (.ctor 200 0 1) []) n
def numeral : Nat → AExpr Nat
  | 0 => zero
  | n + 1 => succ (numeral n)

def profile : PrimitiveSignature Nat := { primitives with natType := some (.member 200 0) }
def binaryType : AExpr Nat := .forallE .never nat (.forallE .never nat nat)
def motive : AExpr Nat := .lam .never nat nat
def addBody : AExpr Nat :=
  .lam .never nat (.lam .never nat
    (.appN (.const (.member 201 0) [.succ .zero])
      [motive, .bvar 1, .lam .never nat (.lam .never nat (succ (.bvar 0))), .bvar 0]))
def add (n m : AExpr Nat) : AExpr Nat := .appN (.const (.member 300 0) []) [n, m]
def mulBody : AExpr Nat :=
  .lam .never nat (.lam .never nat
    (.appN (.const (.member 201 0) [.succ .zero])
      [motive, .natLit 0, .lam .never nat (.lam .never nat (add (.bvar 3) (.bvar 0))), .bvar 0]))
def mul (n m : AExpr Nat) : AExpr Nat := .appN (.const (.member 301 0) []) [n, m]

def declaration : Nat → Const Nat
  | 200 => Certified.Natural.shape.source 200
  | 201 => Certified.Natural.shape.recursorSource 200 201 .large
  | 300 => .defn 0 .definition binaryType.erase addBody.erase .safe
  | 301 => .defn 0 .definition binaryType.erase mulBody.erase .safe
  | 302 => .defn 0 .definition nat.erase (.natLit 3) .safe
  | b => Standard.declaration b

def store (alter : Nat → Const Nat → Const Nat := fun _ c => c) : Store Nat where
  dom := [10, 11, 100, 101, 200, 201, 300, 301, 302]
  nodup := by decide
  blocks b := if b ∈ [10, 11, 100, 101, 200, 201, 300, 301, 302] then some ⟨[alter b (declaration b)]⟩ else none
  mem_dom b := by split <;> simp_all

def proposition (lhs rhs : AExpr Nat) : AExpr Nat := Equality.applied Standard.eq (.succ .zero) nat lhs rhs
def proof (n : Nat) : AExpr Nat := Equality.reflexivity Standard.refl (.succ .zero) nat (.natLit n)
def input (lhs : AExpr Nat) (value : Nat) : ProofInput Nat :=
  ⟨store, 0, (proof value).erase, (proposition lhs (.natLit value)).erase⟩
def accepted (lhs : AExpr Nat) (value : Nat) : Bool :=
  let input := input lhs value
  (Certificate.proofWitness? 3200 profile input).any (acceptsCertified.{0,0} 6400 profile input)

#guard accepted zero 0
#guard accepted (numeral 4) 4
#guard accepted (succ (.natLit 8)) 9
#guard accepted (.const (.member 302 0) []) 3
#guard accepted (add (.natLit 0) (.natLit 0)) 0
#guard accepted (add (.natLit 2) (.natLit 3)) 5
#guard accepted (mul (.natLit 2) (.natLit 3)) 6
#guard accepted (mul (.natLit 5) (.natLit 0)) 0

def sampleInput := input (add (.natLit 2) (.natLit 3)) 5
def sampleWitness := Certificate.proofWitness? 3200 profile sampleInput

#guard sampleWitness.isSome
#guard sampleWitness.any fun witness => witness.declarations.any fun declaration => match declaration with
  | .natural _ => true
  | _ => false

-- The original successful witness must fail when the primitive selection,
-- authenticated source, claimed answer or admitted literal fact is changed.
#guard sampleWitness.any fun witness => !acceptsCertified.{0,0} 6400 primitives sampleInput witness
#guard sampleWitness.any fun witness =>
  !acceptsCertified.{0,0} 6400 { profile with natType := some (.member 100 0) } sampleInput witness
#guard sampleWitness.any fun witness => !acceptsCertified.{0,0} 6400 profile
  { sampleInput with proposition := (proposition (add (.natLit 2) (.natLit 3)) (.natLit 6)).erase } witness
#guard sampleWitness.any fun witness =>
  let declarations := witness.declarations.map fun declaration => match declaration with
    | .natural block => .ordinary block
    | _ => declaration
  !acceptsCertified.{0,0} 6400 profile sampleInput { witness with declarations }

def unsafeNat (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 200 then match c with
    | .induct n p i type ctors _ => .induct n p i type ctors .unsafe
    | _ => c
  else c
def forgedRule (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 201 then match c with
    | .recursor n p i m r type rules k safety =>
      .recursor n p i m r type (rules.map fun rule => { rule with rhs := zero.erase }) k safety
    | _ => c
  else c
def changedAdd (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 300 then .defn 0 .definition binaryType.erase (.lam nat.erase (.lam nat.erase (.natLit 0))) .safe else c

#guard [unsafeNat, forgedRule, changedAdd].all fun alter => sampleWitness.any fun witness =>
  !acceptsCertified.{0,0} 6400 profile { sampleInput with store := store alter } witness

end Tests.Theory.Natural
