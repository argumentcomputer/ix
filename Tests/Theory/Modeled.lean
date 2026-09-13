/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Modeled
import Ix.Theory.Certificate.Build
import Tests.Theory.Ordinary
import Tests.Theory.Certified
import Tests.Theory.ModeledFixtures

open Ix.Theory

/-! Model declarations and certificates are generated from actual anonymous
source data, then checked through the public store entry point. This corpus
does not substitute a caller-supplied realization for declaration checking. -/

namespace Tests.Theory.Modeled

open Ix.Theory.Model Ix.Theory.Certified Ix.Theory.Certificate Ix.Theory.Inductive
open Tests.Theory.Certified (primitives)

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

def ref (block member : Nat := 0) : ConstRef Nat := .member block member
def const (block member : Nat := 0) (levels : List VLevel := []) : VExpr Nat := .const (ref block member) levels
def type0 : VExpr Nat := .sort (.succ .zero)
def natType : VExpr Nat := const 20

def mutualSource : Block Nat := ModeledFixtures.mutualSource
def mutualRecursors : Block Nat := ModeledFixtures.mutualRecursors

/-- Both families are modeled by Nat. B's constructor is identity; A has zero
and successor. The dependent mutual fold is built from the checked Nat fold. -/
def modelTargets : List (ConstRef Nat) :=
  [ref 20, .ctor 20 0 0, .ctor 20 0 1, ref 20, ref 40, ref 41, ref 42]
def modelPairs : List (ConstRef Nat × ConstRef Nat) :=
  [ref 30, .ctor 30 0 0, .ctor 30 0 1, ref 30 1, .ctor 30 1 0, ref 31, ref 31 1].zip modelTargets
def mapped (expression : VExpr Nat) : VExpr Nat := expression.mapRefs (Certificate.Modeled.target modelPairs)
def recursorType (index : Nat) : VExpr Nat :=
  mapped ((mutualRecursors.members[index]?).map Const.type |>.getD type0)
def recPrefix : List (VExpr Nat) := (recursorType 0).telN 5

def modelA : VExpr Nat :=
  .lamN recPrefix (.appN (const 21 0 [.param 0]) [
    .bvar 4, .bvar 2,
    .lam natType (.lam (.app (.bvar 5) (.bvar 0))
      (.appN (.bvar 3) [.bvar 1, .appN (.bvar 2) [.bvar 1, .bvar 0]]))])

def modelB : VExpr Nat :=
  .lamN (recPrefix ++ [natType]) (.appN (.bvar 1)
    [.bvar 0, .appN (const 41 0 [.param 0]) (VExpr.bvarRevRange 1 5 ++ [.bvar 0])])

def block : Nat → Block Nat
  | 10 => ⟨[PrimitiveSignature.falseDeclaration]⟩
  | 11 => ⟨[primitives.falseElimDeclaration]⟩
  | 20 => ⟨[Tests.Theory.Ordinary.natShape.source 20]⟩
  | 21 => ⟨[Tests.Theory.Ordinary.natShape.recursorSource 20 21 .large]⟩
  | 30 => mutualSource
  | 31 => mutualRecursors
  | 40 => ⟨[.defn 0 .definition (.forallE natType natType) (.lam natType (.bvar 0)) .safe]⟩
  | 41 => ⟨[.defn 1 .definition (recursorType 0) modelA .safe]⟩
  | 42 => ⟨[.defn 1 .definition (recursorType 1) modelB .safe]⟩
  | _ => ⟨[]⟩

def store (alter : Nat → Block Nat → Block Nat := fun _ b => b) : Store Nat where
  dom := List.range 43
  nodup := List.nodup_range
  blocks b := if b < 43 then some (alter b (block b)) else none
  mem_dom b := by split <;> simp_all

def prefixWitnesses? : Option (Environment Nat × List (DeclarationWitness Nat)) :=
  declarationWitnesses? 3000 store primitives.environment
    [.ordinary 20 21, .definition (ref 40), .definition (ref 41), .definition (ref 42)]

def modeledWitness? : Option (Ix.Theory.Certified.Modeled.Witness Nat) := do
  let (entries, _) ← prefixWitnesses?
  Certificate.Modeled.witness? 3000 entries store 30 [ref 31, ref 31 1] modelTargets

def witnesses? : Option (List (DeclarationWitness Nat)) := do
  let (_, earlier) ← prefixWitnesses?
  return earlier ++ [.modeled (← modeledWitness?)]

def accepted : Bool := witnesses?.any fun witnesses =>
  acceptsStoreCertified.{0,0} 3000 primitives store [ref 30, ref 30 1, ref 31, ref 31 1] witnesses

#guard (Ix.Theory.Certified.Modeled.sourceRefs? store 30 [ref 31, ref 31 1]).isSome
#guard (Ix.Theory.Certified.Modeled.recursorRules? store (ref 31)).any (fun rules => rules.length == 2)
#guard (Ix.Theory.Certified.Modeled.recursorRules? store (ref 31 1)).any (fun rules => rules.length == 1)
#guard store.ctorRuleIndex? (.ctor 30 1 0) == some 2
#guard prefixWitnesses?.isSome
#guard modeledWitness?.isSome
#guard accepted

def candidate : Certificate.Modeled.Candidate Nat := ⟨30, [ref 31, ref 31 1], modelTargets, []⟩
def generated? : Option (List (DeclarationWitness Nat)) :=
  Certificate.storeWitness? 3000 primitives store [ref 31, ref 31 1] [candidate]
#guard generated?.any (acceptsStoreCertified.{0,0} 3000 primitives store [ref 31, ref 31 1])

def computed : VExpr Nat := .appN (const 31 0 [.succ .zero]) [
  .lam (const 30) (.sort .zero), .lam (const 30 1) (.sort .zero), .bvar 1,
  .lam (const 30 1) (.lam (.sort .zero) (.bvar 0)),
  .lam (const 30) (.lam (.sort .zero) (.bvar 0)),
  .app (.const (.ctor 30 0 1) [])
    (.app (.const (.ctor 30 1 0) []) (.const (.ctor 30 0 0) []))]
def proof : VExpr Nat := .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))
def proposition : VExpr Nat := .forallE (.sort .zero) (.forallE (.bvar 0) computed)
def input : ProofInput Nat := ⟨store, 0, proof, proposition⟩
def proofAccepted : Bool := (Certificate.proofWitness? 3000 primitives input [candidate]).any
  (acceptsCertified.{0,0} 3000 primitives input)
#guard proofAccepted

def withRecursor (alter : Const Nat → Const Nat) : Store Nat :=
  store fun n b => if n = 31 then ⟨b.members.map alter⟩ else b
def withRules (alter : List (RecRule Nat) → List (RecRule Nat)) : Store Nat :=
  withRecursor fun c => match c with
    | .recursor u p i m n t rules k s => .recursor u p i m n t (alter rules) k s
    | c => c
def sourceRejected (source : Store Nat) : Bool := witnesses?.any fun witnesses =>
  !(acceptsStoreCertified.{0,0} 3000 primitives source [ref 31, ref 31 1] witnesses)

-- Both families contribute to the same table. Slot 2 must not become slot 1,
-- and an equation about the other recursor cannot justify the selected rule.
#guard sourceRejected (withRules fun rules => rules.reverse)
#guard sourceRejected (withRules fun rules => rules.take 2)
#guard sourceRejected (withRules fun rules => rules.map fun r => { r with nfields := r.nfields + 1 })
#guard sourceRejected (withRules fun rules => rules.map fun r => { r with rhs := .sort .zero })
#guard sourceRejected (withRecursor fun c => match c with
  | .recursor u p i m n t rs _ s => .recursor u p i m n t rs true s | c => c)
#guard sourceRejected (withRecursor fun c => match c with
  | .recursor u p i m n t rs k _ => .recursor u p i m n t rs k .unsafe | c => c)
#guard sourceRejected (store fun n b => if n = 40 then
  ⟨[.axiom 0 (.forallE natType natType) .safe]⟩ else b)
#guard sourceRejected (store fun n b => if n = 40 then
  ⟨[.defn 0 .definition (.forallE natType natType) (.const (.ctor 30 1 0) []) .safe]⟩ else b)

def witnessRejected (alter : Ix.Theory.Certified.Modeled.Witness Nat → Ix.Theory.Certified.Modeled.Witness Nat) : Bool :=
  (prefixWitnesses?).any fun (_, declarations) => (modeledWitness?).any fun witness =>
    !(acceptsStoreCertified.{0,0} 3000 primitives store [ref 31, ref 31 1]
      (declarations ++ [.modeled (alter witness)]))

#guard witnessRejected fun w => { w with recursors := w.recursors.reverse }
#guard witnessRejected fun w => { w with companions := w.companions.reverse }
#guard witnessRejected fun w => { w with companions := w.companions.drop 1 }
#guard witnessRejected fun w => { w with equations := w.equations.drop 1 }
#guard witnessRejected fun w => { w with companions := w.companions.map fun c => { c with model := c.header.ref } }
#guard witnessRejected fun w => { w with companions := w.companions.map fun c =>
  { c with rules := c.rules.map fun r => { r with lhs := r.rhs } } }
#guard witnessRejected fun w => { w with equations := w.equations.map (fun es =>
  es.map (fun e => { e with proof := .conversion .refl })) }

-- The generic dependency walker rejects a model that depends on the new
-- source, and does not turn a missing model witness into ordinary admission.
#guard (Certificate.storeWitness? 3000 primitives store [ref 31] [{ candidate with models :=
  [ref 30, .ctor 30 0 0, .ctor 30 0 1, ref 30 1, .ctor 30 1 0, ref 31, ref 31 1] }]).isNone
#guard (Certificate.storeWitness? 3000 primitives store [ref 31]).isNone

-- Model admission supplies no projection or eta facts for the new families.
#guard (modeledWitness?).all fun w => w.companions.all (fun c => c.entry.facts.isEmpty)
#guard (prefixWitnesses?).any fun (entries, _) => (modeledWitness?).any fun w =>
  (inferSource? 3000 0 (Ix.Theory.Certified.Modeled.environment entries w.companions) []
    (.proj (ref 30 1) 0 (.app (.const (.ctor 30 1 0) []) (.const (.ctor 30 0 0) [])))).isNone

end Tests.Theory.Modeled
