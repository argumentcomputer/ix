/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Standard
import Ix.Theory.Certified.Quotient.Publish

namespace Ix.Theory.Certificate.Quotient

open Model Certified Certified.Quotient

universe u
variable {β : Type u} [DecidableEq β]
variable [Hints β]

def memberRefs (store : Store β) : List (ConstRef β) :=
  store.dom.flatMap fun block =>
    match store.blocks block with
    | some value => (List.range value.members.length).map (.member block ·)
    | none => []

def findSource? (store : Store β) (source : Const β) : Option (ConstRef β) :=
  (memberRefs store).find? fun r => store.lookup r == some source

/-- Discover the quotient package from an exact lift type. The other members
are found by declaration content, independently of addresses or source names. -/
def refsForLift? (store : Store β) (lift : ConstRef β) : Option (Refs β) := do
  let .quot .lift 2 type ← store.lookup lift | none
  type.refs.findSome? fun eq => do
    let .member esource 0 := eq | none
    let eqRefl := ConstRef.ctor esource 0 0
    let eqRec ← Standard.recursorFor? store 2 (Certified.Basis.Equality.recType eq eqRefl)
    type.refs.findSome? fun family => do
      let refs : Refs β := { eq, type := family, ctor := lift, lift, ind := lift, eqRefl, eqRec, sound := lift }
      if (refs.source .lift) != .quot .lift 2 type then none else do
        let ctor ← findSource? store (refs.source .ctor)
        let refs := { refs with ctor }
        let ind ← findSource? store (refs.source .ind)
        let sound ← findSource? store (refs.source .sound)
        let refs := { refs with ind, sound }
        if refs.ExactSource store then some refs else none

def refs? (store : Store β) (ref : ConstRef β) : Option (Refs β) :=
  (memberRefs store).findSome? fun lift => do
    let refs ← refsForLift? store lift
    if (kinds.map refs.ref).contains ref then some refs else none

def typeWitnesses? (fuel : Nat) (entries : Environment β) :
    List (Signature.Header β) → Option (List (Signature.TypeWitness β))
  | [] => some []
  | header :: headers => do
    let inferred ← inferAnnotated? fuel header.universes entries [] header.type
    let .sort level := inferred.type | none
    let rest ← typeWitnesses? fuel (entries.insert header.ref header.entry) headers
    return ⟨level, inferred.witness⟩ :: rest

def ruleWitness? (fuel : Nat) (entries : Environment β) (rule : Signature.Rule β) :
    Option (Signature.RuleWitness β) := do
  let type ← inferAnnotated? fuel rule.universes entries [] rule.type
  let .sort level := type.type | none
  let lhs ← inferAnnotated? fuel rule.universes entries [] rule.lhs
  let lhs ← castWith? fuel rule.universes entries [] lhs rule.type
  let rhs ← inferAnnotated? fuel rule.universes entries [] rule.rhs
  let rhs ← castWith? fuel rule.universes entries [] rhs rule.type
  return ⟨level, type.witness, lhs, rhs⟩

def witness? (fuel : Nat) (entries : Environment β) (refs : Refs β) : Option (Witness β) := do
  let types ← typeWitnesses? fuel entries refs.headers
  let formed := refs.typeEnvironment entries
  let liftRule ← ruleWitness? fuel formed refs.liftRule
  let indRule ← ruleWitness? fuel formed refs.indRule
  return ⟨refs, types, liftRule, indRule⟩

end Ix.Theory.Certificate.Quotient
