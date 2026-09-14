/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.OrdinarySource
import Ix.Theory.Certificate.Standard
import Ix.Theory.Certificate.Quotient
import Ix.Theory.Certificate.Structure
import Ix.Theory.Certificate.Modeled
import Ix.Theory.Certified.Accept

namespace Ix.Theory.Certificate

open Model Certified

universe u
variable {β : Type u} [DecidableEq β]
variable [Hints β]

def hasLiteral : VExpr β → Bool
  | .natLit _ => true
  | .app a b | .lam a b | .forallE a b => hasLiteral a || hasLiteral b
  | .proj _ _ e => hasLiteral e
  | _ => false

def constantHasLiteral : Const β → Bool
  | .defn _ _ type body _ => hasLiteral type || hasLiteral body
  | .induct _ _ _ type ctors _ => hasLiteral type || ctors.any (hasLiteral ·.type)
  | .recursor _ _ _ _ _ type rules _ _ => hasLiteral type || rules.any (hasLiteral ·.rhs)
  | .axiom _ type _ | .quot _ _ type => hasLiteral type

def literalDependencies? (natural : Option (ConstRef β)) (used : Bool) : Option (List (ConstRef β)) :=
  if used then natural.map (fun r => [r]) else some []

inductive DeclarationSource (β : Type u) where
  | definition (ref : ConstRef β)
  | ordinary (source recursor : β)
  | standard (ref : ConstRef β)
  | quotient (refs : Certified.Quotient.Refs β)
  | modeled (candidate : Modeled.Candidate β)

structure SourceGroup (β : Type u) where
  declaration : DeclarationSource β
  references : List (ConstRef β)
  dependencies : List (ConstRef β)

def recursorFamily? : VExpr β → Option β
  | .forallE _ (.forallE A B) => recursorFamily? (.forallE A B)
  | .forallE A _ => match A.appHead with
    | .const (.member source 0) _ => some source
    | _ => none
  | _ => none

def findRecursor? (store : Store β) (source : β) : Option β :=
  store.dom.find? fun candidate => match store.blocks candidate with
    | some ⟨[.recursor _ _ _ _ _ type _ _ .safe]⟩ => recursorFamily? type == some source
    | _ => false

def ordinaryGroup? (store : Store β) (source recursor : β)
    (natural : Option (ConstRef β) := none) : Option (SourceGroup β) := do
  let ⟨[family@(.induct _ _ _ _ ctors .safe)]⟩ ← store.blocks source | none
  let ⟨[recr@(.recursor _ _ _ _ _ _ _ _ .safe)]⟩ ← store.blocks recursor | none
  let references := [.member source 0, .member recursor 0] ++
    (List.range ctors.length).map (.ctor source 0 ·)
  let literals ← literalDependencies? natural (constantHasLiteral family || constantHasLiteral recr)
  return ⟨.ordinary source recursor, references,
    ((family.refs ++ recr.refs).filter fun r => !references.contains r) ++ literals⟩

def quotientGroup (refs : Certified.Quotient.Refs β) : SourceGroup β :=
  ⟨.quotient refs, Certified.Quotient.kinds.map refs.ref, [refs.eq, refs.eqRefl, refs.eqRec]⟩

def modeledGroup? (store : Store β) (candidate : Modeled.Candidate β)
    (natural : Option (ConstRef β) := none) : Option (SourceGroup β) := do
  let references ← Certified.Modeled.sourceRefs? store candidate.source candidate.recursors
  let sources := references.filterMap (store.lookup ·)
  let rawReferences := sources.flatMap Const.refs
  let literals ← literalDependencies? natural (sources.any constantHasLiteral)
  return ⟨.modeled candidate, references,
    rawReferences.filter (fun ref => !references.contains ref) ++ candidate.models ++
      candidate.proofReferences ++ literals⟩

def sourceGroup? (store : Store β) (r : ConstRef β)
    (natural : Option (ConstRef β) := none) (models : List (Modeled.Candidate β) := []) : Option (SourceGroup β) := do
  match models.findSome? (fun candidate => do
    let group ← modeledGroup? store candidate natural
    if group.references.contains r then some group else none) with
  | some group => return group
  | none => pure ⟨⟩
  match r with
  | .ctor source 0 _ => ordinaryGroup? store source (← findRecursor? store source) natural
  | .ctor .. => none
  | .member source member =>
    match ← store.lookup r with
    | .defn _ _ type body .safe =>
      return ⟨.definition r, [r], type.refs ++ body.refs ++
        (← literalDependencies? natural (hasLiteral type || hasLiteral body))⟩
    | .axiom _ type .safe =>
      match Quotient.refs? store r with
      | some refs => return quotientGroup refs
      | none => return ⟨.standard r, [r], type.refs ++ (← literalDependencies? natural (hasLiteral type))⟩
    | .quot .. => return quotientGroup (← Quotient.refs? store r)
    | .induct .. =>
      if member != 0 then none else ordinaryGroup? store source (← findRecursor? store source) natural
    | .recursor _ _ _ _ _ type _ _ .safe =>
      if member != 0 then none else ordinaryGroup? store (← recursorFamily? type) source natural
    | _ => none

/-- Dependency order groups a whole ordinary family and recursor as one unit.
A cycle, missing reference, or unsupported declaration produces no suggestion. -/
def dependencyOrder? (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (pending visited active : List (ConstRef β))
    (order : List (DeclarationSource β) := []) (models : List (Modeled.Candidate β) := []) :
    Option (List (ConstRef β) × List (DeclarationSource β)) :=
  match fuel, pending with
  | _, [] => some (visited, order)
  | 0, _ :: _ => none
  | fuel + 1, r :: rest =>
    if r = signature.falseType ∨ r = signature.falseElim ∨ r ∈ visited then
      dependencyOrder? fuel signature store rest visited active order models
    else if r ∈ active then none
    else do
      let group ← sourceGroup? store r signature.natType models
      if group.references.any (active.contains ·) then none else do
        let (visited, order) ← dependencyOrder? fuel signature store
          group.dependencies visited (group.references ++ active) order models
        dependencyOrder? fuel signature store rest (visited ++ group.references) active
          (order ++ [group.declaration]) models

def definitionWitness? (fuel : Nat) (entries : Environment β) (r : ConstRef β)
    (source : Const β) : Option (DefinitionWitness β) :=
  match source with
  | .defn n _ type body .safe => do
    let T ← inferSource? fuel n entries [] type
    let .sort l := T.type | none
    let b ← inferSource? fuel n entries [] body
    let bw ← castWith? fuel n entries [] b T.expression
    return ⟨r, annotations T.expression, annotations b.expression, l, T.witness, bw⟩
  | _ => none

def declarationWitnesses? (fuel : Nat) (store : Store β) (entries : Environment β) :
    List (DeclarationSource β) → Option (Environment β × List (DeclarationWitness β))
  | [] => some (entries, [])
  | .definition r :: rest => do
    let source ← store.lookup r
    let witness ← definitionWitness? fuel entries r source
    let reading ← readDefinition? source witness.typeAnnotations witness.bodyAnnotations
    let (entries', witnesses) ←
      declarationWitnesses? fuel store (entries.insert r reading.val.entry) rest
    return (entries', .definition witness :: witnesses)
  | .ordinary source recursor :: rest => do
    let witness ← Ordinary.sourceBlock? fuel entries store source recursor
    if Hints.natural (β := β) = some (.member source 0) then
      if witness.shape.shape != Certified.Natural.shape then none else do
        let (entries', witnesses) ← declarationWitnesses? fuel store
          (Certified.Natural.environment entries source recursor witness.mode) rest
        return (entries', .natural witness :: witnesses)
    else
      match Structure.witness? fuel entries witness with
      | some structured =>
        let (entries', witnesses) ← declarationWitnesses? fuel store
          (structured.facts.description.publishedEnvironment entries source recursor witness.mode) rest
        return (entries', .structure structured :: witnesses)
      | none =>
        let (entries', witnesses) ← declarationWitnesses? fuel store
          (witness.shape.shape.publishedEnvironment entries source recursor witness.mode) rest
        return (entries', .ordinary witness :: witnesses)
  | .standard ref :: rest => do
    let source ← store.lookup ref
    let witness ← Standard.witness? fuel store entries ref source
    let (entries', witnesses) ← declarationWitnesses? fuel store (entries.insert ref witness.spec.entry) rest
    return (entries', .standard witness :: witnesses)
  | .quotient refs :: rest => do
    let witness ← Quotient.witness? fuel entries refs
    let (entries', witnesses) ← declarationWitnesses? fuel store (refs.environment entries) rest
    return (entries', .quotient witness :: witnesses)
  | .modeled candidate :: rest => do
    let witness ← candidate.witness? fuel entries store
    let (entries', witnesses) ← declarationWitnesses? fuel store
      (Certified.Modeled.environment entries witness.companions) rest
    return (entries', .modeled witness :: witnesses)

/-- A generic search driver over the exact input store and source syntax.
This is untrusted preprocessing: the final acceptance call validates the
entire returned witness again, including the primitive metadata and policy. -/
def proofWitness? (fuel : Nat) (signature : PrimitiveSignature β)
    (input : ProofInput β) (models : List (Modeled.Candidate β) := []) : Option (ProofWitness β) :=
  letI : Hints β := ⟨signature.natType⟩
  do
    let literals ← literalDependencies? signature.natType (hasLiteral input.proposition || hasLiteral input.proof)
    let (_, order) ← dependencyOrder? fuel signature input.store
      (input.proposition.refs ++ input.proof.refs ++ literals) [] [] [] models
    let (entries, declarations) ←
      declarationWitnesses? fuel input.store signature.environment order
    let P ← inferSource? fuel input.universes entries [] input.proposition
    let Pw ← castWith? fuel input.universes entries [] P (.sort .zero)
    let e ← inferSource? fuel input.universes entries [] input.proof
    let ew ← castWith? fuel input.universes entries [] e P.expression
    return ⟨declarations, annotations e.expression, annotations P.expression, ew, Pw⟩

/-- Declaration-only search also covers data declarations and complete source
groups. The independent store validator checks every requested reference. -/
def storeWitness? (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (targets : List (ConstRef β)) (models : List (Modeled.Candidate β) := []) : Option (List (DeclarationWitness β)) :=
  letI : Hints β := ⟨signature.natType⟩
  do
    let (_, order) ← dependencyOrder? fuel signature store targets [] [] [] models
    let (_, declarations) ← declarationWitnesses? fuel store signature.environment order
    return declarations

end Ix.Theory.Certificate
