/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Theory.Standard

open Ix.Theory

namespace Tests.Theory.Structure

open Ix.Theory.Model Ix.Theory.Certified Ix.Theory.Certified.Basis Ix.Theory.Certificate
open Tests.Theory.Certified (primitives)

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def box : Certified.Structure.Description Nat :=
  ⟨1, [], [⟨.sort (.param 0), .succ (.param 0)⟩, ⟨.bvar 0, .param 0⟩], .succ (.param 0)⟩

def pair : Certified.Structure.Description Nat :=
  ⟨1, [.sort (.param 0)], [⟨.bvar 0, .param 0⟩, ⟨.bvar 1, .param 0⟩], .param 0⟩

def store (d : Certified.Structure.Description Nat) (alter : Nat → Const Nat → Const Nat := fun _ c => c) : Store Nat where
  dom := [10, 11, 100, 101, 200, 201]
  nodup := by decide
  blocks b := if b ∈ [10, 11, 100, 101, 200, 201] then some ⟨[alter b (match b with
    | 200 => d.ordinary.source 200
    | 201 => d.ordinary.recursorSource 200 201 .large
    | _ => Standard.declaration b)]⟩ else none
  mem_dom b := by split <;> simp_all

def input (d : Certified.Structure.Description Nat) (n : Nat) (proof proposition : AExpr Nat) : ProofInput Nat :=
  ⟨store d, n, proof.erase, proposition.erase⟩

def accepted (d : Certified.Structure.Description Nat) (n : Nat) (proof proposition : AExpr Nat) : Bool :=
  let input := input d n proof proposition
  (Certificate.proofWitness? 2400 primitives input).any (acceptsCertified.{0,0} 4000 primitives input)

def boxType (u : VLevel) : AExpr Nat := .const (.member 200 0) [u]
def boxMk (u : VLevel) (A a : AExpr Nat) : AExpr Nat := .appN (.const (.ctor 200 0 0) [u]) [A, a]
def proj (i : Nat) (s : AExpr Nat) : AExpr Nat := .proj (.member 200 0) i s

def boxProof : AExpr Nat :=
  .lam .always (.sort .zero) (.lam .always (.bvar 0) (proj 1 (boxMk .zero (.bvar 1) (.bvar 0))))
def boxProposition : AExpr Nat :=
  .forallE .always (.sort .zero) (.forallE .always (.bvar 0) (.bvar 1))

#guard accepted box 0 boxProof boxProposition

def etaProof (u : VLevel) : AExpr Nat :=
  .lam .always (boxType u) (Equality.reflexivity Standard.refl (.succ u) (boxType u) (.bvar 0))
def etaProposition (u : VLevel) : AExpr Nat :=
  .forallE .always (boxType u) (Equality.applied Standard.eq (.succ u) (boxType u)
    (boxMk u (proj 0 (.bvar 0)) (proj 1 (.bvar 0))) (.bvar 0))

#guard accepted box 0 (etaProof .zero) (etaProposition .zero)
#guard accepted box 1 (etaProof (.param 0)) (etaProposition (.param 0))

def pairProof : AExpr Nat :=
  .lam .always (.sort .zero) (.lam .always (.bvar 0)
    (proj 1 (.appN (.const (.ctor 200 0 0) [.zero]) [.bvar 1, .bvar 0, .bvar 0])))

#guard accepted pair 0 pairProof boxProposition

def fieldProof (u : VLevel) : AExpr Nat :=
  .lam .always (.sort u) (.lam .always (.bvar 0)
    (Equality.reflexivity Standard.refl u (.bvar 1) (.bvar 0)))
def fieldProposition (u : VLevel) : AExpr Nat :=
  .forallE .always (.sort u) (.forallE .always (.bvar 0)
    (Equality.applied Standard.eq u (.bvar 1) (proj 1 (boxMk u (.bvar 1) (.bvar 0))) (.bvar 0)))

#guard accepted box 0 (fieldProof .zero) (fieldProposition .zero)
#guard accepted box 0 (fieldProof (.succ .zero)) (fieldProposition (.succ .zero))
#guard accepted box 1 (fieldProof (.param 0)) (fieldProposition (.param 0))

def pairType (u : VLevel) (A : AExpr Nat) : AExpr Nat := .app (boxType u) A
def pairEtaProof (u : VLevel) : AExpr Nat :=
  .lam .always (.sort u) (.lam .always (pairType u (.bvar 0))
    (Equality.reflexivity Standard.refl u (pairType u (.bvar 1)) (.bvar 0)))
def pairEtaProposition (u : VLevel) : AExpr Nat :=
  .forallE .always (.sort u) (.forallE .always (pairType u (.bvar 0))
    (Equality.applied Standard.eq u (pairType u (.bvar 1))
      (.appN (.const (.ctor 200 0 0) [u]) [.bvar 1, proj 0 (.bvar 0), proj 1 (.bvar 0)]) (.bvar 0)))

#guard accepted pair 0 (pairEtaProof .zero) (pairEtaProposition .zero)
#guard accepted pair 1 (pairEtaProof (.param 0)) (pairEtaProposition (.param 0))

def boxInput := input box 0 boxProof boxProposition
def boxWitness := Certificate.proofWitness? 2400 primitives boxInput

#guard boxWitness.isSome
#guard boxWitness.any fun w => w.declarations.any fun d => match d with
  | .structure _ => true
  | _ => false

-- These mutations are sent to the validator with the original successful
-- certificate, so a producer decline is not the rejection being tested.
def wrongFieldCount (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 200 then match c with
    | .induct n p i type ctors safety => .induct n p i type (ctors.map fun c => { c with nfields := 1 }) safety
    | _ => c
  else c
def wrongRecursor (b : Nat) (c : Const Nat) : Const Nat :=
  if b = 201 then match c with
    | .recursor n p i m r type rules _ safety => .recursor n p i m r type rules true safety
    | _ => c
  else c

#guard [wrongFieldCount, wrongRecursor].all fun alter => boxWitness.any fun w =>
  !acceptsCertified.{0,0} 4000 primitives { boxInput with store := store box alter } w

def badProjectionProof (r : ConstRef Nat) (i : Nat) : AExpr Nat :=
  .lam .always (.sort .zero) (.lam .always (.bvar 0)
    (.proj r i (boxMk .zero (.bvar 1) (.bvar 0))))

#guard [(.member 200 0, 2), (.member 100 0, 1)].all fun (r, i) => boxWitness.any fun w =>
  !acceptsCertified.{0,0} 4000 primitives { boxInput with proof := (badProjectionProof r i).erase } w

#guard boxWitness.any fun w =>
  let declarations := w.declarations.map fun declaration => match declaration with
    | .structure s => .ordinary s.facts.block
    | _ => declaration
  !acceptsCertified.{0,0} 4000 primitives boxInput { w with declarations }

#guard boxWitness.any fun w =>
  let declarations := w.declarations.map fun declaration => match declaration with
    | .structure s => .structure { s with facts := { s.facts with description :=
        { s.facts.description with fields := s.facts.description.fields.map fun f => { f with level := .zero } } } }
    | _ => declaration
  !acceptsCertified.{0,0} 4000 primitives boxInput { w with declarations }

#guard boxWitness.any fun w =>
  let declarations := w.declarations.map fun declaration => match declaration with
    | .structure s => .structure { s with iota := s.iota.reverse }
    | _ => declaration
  !acceptsCertified.{0,0} 4000 primitives boxInput { w with declarations }

-- A Prop constructor with a data field remains an ordinary inductive. Even
-- a hand-built structure description cannot grant a projection from it.
def nonempty : Certified.Structure.Description Nat :=
  ⟨1, [.sort (.param 0)], [⟨.bvar 0, .param 0⟩], .zero⟩
def nonemptyStore : Store Nat := store nonempty (fun b c =>
  if b = 201 then nonempty.ordinary.recursorSource 200 201 .small else c)
def nonemptyBlock := Certificate.Ordinary.sourceBlock? 2400 primitives.environment nonemptyStore 200 201

#guard nonemptyBlock.isSome
#guard nonemptyBlock.any fun block =>
  (Certified.Ordinary.checkBlock.{0,0} 4000 primitives.environment nonemptyStore block).isSome &&
    (Certificate.Structure.description? block).isNone
#guard nonemptyBlock.any fun block =>
  let domains := Certificate.Ordinary.domains? 2400 nonempty.universes
    (nonempty.ordinary.publishedEnvironment primitives.environment 200 201 .small) []
    (nonempty.projectionDomains 200)
  domains.any fun domains =>
    let witness : Certified.Structure.FactsWitness Nat := ⟨nonempty, block, [.bvar], domains⟩
    (Certified.Structure.checkFacts.{0,0} 4000 primitives.environment nonemptyStore witness).isNone

end Tests.Theory.Structure
