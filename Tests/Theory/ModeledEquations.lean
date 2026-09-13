/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Theory.Modeled

open Ix.Theory

namespace Tests.Theory.ModeledEquations

open Ix.Theory.Model Ix.Theory.Certified Ix.Theory.Certificate
open Tests.Theory.Certified (primitives)
open Tests.Theory.Modeled (ref)

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def eqRef : ConstRef Nat := ref 60
def reflRef : ConstRef Nat := .ctor 60 0 0
def eqRec : ConstRef Nat := ref 61
def block : Nat → Block Nat
  | 60 => ⟨[Basis.Equality.shape.source 60]⟩
  | 61 => ⟨[Basis.Equality.shape.recursorSource 60 61 .large true]⟩
  | n => Tests.Theory.Modeled.block n
def store : Store Nat where
  dom := List.range 62
  nodup := List.nodup_range
  blocks b := if b < 62 then some (block b) else none
  mem_dom b := by split <;> simp_all

def prefixWitnesses? := declarationWitnesses? 4000 store primitives.environment
  [.ordinary 60 61, .ordinary 20 21, .definition (ref 40), .definition (ref 41), .definition (ref 42)]

/-- Use a checked proof of equality of the complete functions, with their
entire telescopes as endpoints. No equation is reflected into Theory.IsDefEq. -/
def propositional? (entries : Environment Nat) (rule : Signature.Rule Nat)
    (witness : Ix.Theory.Certified.Modeled.EquationWitness Nat) :
    Option (Ix.Theory.Certified.Modeled.EquationWitness Nat) := do
  let proof := Basis.Equality.reflexivity reflRef witness.formation.level rule.type rule.lhs
  let inferred ← inferAnnotated? 4000 rule.universes entries [] proof
  let typed ← castWith? 4000 rule.universes entries [] inferred
    (Basis.Equality.applied eqRef witness.formation.level rule.type rule.lhs rule.rhs)
  return { witness with proof := .propositional eqRef reflRef eqRec proof typed }

def witness? : Option (Ix.Theory.Certified.Modeled.Witness Nat) := do
  let (entries, _) ← prefixWitnesses?
  let witness ← Tests.Theory.Modeled.candidate.witness? 4000 entries store
  let equations ← (witness.companions.zip witness.equations).mapM fun (companion, proofs) =>
    (companion.rules.zip proofs).mapM fun (rule, proof) =>
      propositional? entries (Ix.Theory.Certified.Modeled.mapRule witness.companions rule) proof
  return { witness with equations }

def accepted (alter : Ix.Theory.Certified.Modeled.Witness Nat → Ix.Theory.Certified.Modeled.Witness Nat := id) : Bool :=
  prefixWitnesses?.any fun (_, earlier) => witness?.any fun witness =>
    acceptsStoreCertified.{0,0} 4000 primitives store [ref 31, ref 31 1] (earlier ++ [.modeled (alter witness)])

#guard accepted
#guard !accepted fun w => { w with equations := w.equations.map (fun proofs => proofs.map fun proof =>
  { proof with proof := .propositional eqRef reflRef eqRec (.sort .zero) .sort }) }
#guard !accepted fun w => { w with equations := w.equations.map (fun proofs => proofs.map fun proof =>
  match proof.proof with
  | .propositional _ r rec term typed => { proof with proof := .propositional (ref 20) r rec term typed }
  | _ => proof) }
#guard !accepted fun w => { w with companions := w.companions.map (fun c =>
  { c with rules := c.rules.map fun rule => { rule with lhs := rule.rhs } }) }

/-- Actual model equation declarations for serialization and command tests.
Each proof is part of the source store and checked as a normal theorem. -/
def equationDeclarations? : Option (List (Const Nat)) := do
  let (entries, _) ← prefixWitnesses?
  let witness ← Tests.Theory.Modeled.candidate.witness? 4000 entries store
  return (witness.companions.zip witness.equations).flatMap fun (companion, proofs) =>
    (companion.rules.zip proofs).map fun (rule, proof) =>
      let rule := Ix.Theory.Certified.Modeled.mapRule witness.companions rule
      let type := Basis.Equality.applied eqRef proof.formation.level rule.type rule.lhs rule.rhs
      let body := Basis.Equality.reflexivity reflRef proof.formation.level rule.type rule.lhs
      .defn rule.universes .theorem type.erase body.erase .safe

def proofBlock (n : Nat) : Block Nat :=
  if n < 70 then block n else ⟨((equationDeclarations?.getD [])[n - 70]?).toList⟩
def proofStore : Store Nat where
  dom := List.range 73
  nodup := List.nodup_range
  blocks b := if b < 73 then some (proofBlock b) else none
  mem_dom b := by split <;> simp_all
def hint (n : Nat) : Certificate.Modeled.ProofHint Nat :=
  ⟨eqRef, reflRef, eqRec, .const (ref n) [.param 0]⟩
def candidate : Certificate.Modeled.Candidate Nat :=
  { Tests.Theory.Modeled.candidate with proofs :=
    [(ref 31, [some (hint 70), some (hint 71)]), (ref 31 1, [some (hint 72)])] }
def input : ProofInput Nat := ⟨proofStore, 0, Tests.Theory.Modeled.proof, Tests.Theory.Modeled.proposition⟩
def generatedAccepted : Bool := (Certificate.proofWitness? 4000 primitives input [candidate]).any
  (acceptsCertified.{0,0} 4000 primitives input)
#guard generatedAccepted
#guard (Certificate.proofWitness? 4000 primitives input
  [{ candidate with proofs := [(ref 31, [some (hint 71), some (hint 70)])] }]).isNone

end Tests.Theory.ModeledEquations
