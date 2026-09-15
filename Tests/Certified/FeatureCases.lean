/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Certified.Serialize
import Ix.Certified.Corpus
import Tests.Theory.Standard
import Tests.Theory.Quotient
import Tests.Theory.Structure
import Tests.Theory.Natural

/-! Canonical serialized acceptance corpus. All certificates are generated
from decoded stores, and all outcomes run the independent serialized gate. -/

namespace Tests.Certified.Features

open Ix.Theory Ix.Theory.Model Ix.Theory.Certified Ix.Certified Serialize
open Tests.Theory.Certified (primitives)
open Lean (toJson)

set_option maxRecDepth 32768
set_option maxHeartbeats 32000000

abbrev std := Tests.Theory.Standard.input
abbrev quo := Tests.Theory.Quotient.input
abbrev struc := Tests.Theory.Structure.input
abbrev natural := Tests.Theory.Natural.input

structure Scenario where
  name : String
  input : ProofInput Nat
  signature : PrimitiveSignature Nat := primitives

def positive : List Scenario := [
  ⟨"propext", Tests.Theory.Standard.propextInput, primitives⟩,
  ⟨"choice-Prop", std 0 (.const Tests.Theory.Standard.choiceRef [.zero])
      (Tests.Theory.Standard.choiceSpec.type.instL [.zero]), primitives⟩,
  ⟨"choice-universe", std 1 (Tests.Theory.Standard.choiceRefl (.param 0))
      (Tests.Theory.Standard.choiceReflType (.param 0)), primitives⟩,
  ⟨"choice-Type", std 0 (Tests.Theory.Standard.choiceRefl (.succ .zero))
      (Tests.Theory.Standard.choiceReflType (.succ .zero)), primitives⟩,
  ⟨"choice-Type1", std 0 (Tests.Theory.Standard.choiceRefl (.succ (.succ .zero)))
      (Tests.Theory.Standard.choiceReflType (.succ (.succ .zero))), primitives⟩,
  ⟨"Eq-K", std 0 Tests.Theory.Standard.kProof Tests.Theory.Standard.kProposition, primitives⟩,
  ⟨"Quot-sound", quo 1 (.const Tests.Theory.Quotient.refs.sound [.param 0])
      (Certified.Quotient.soundType Tests.Theory.Quotient.refs), primitives⟩,
  ⟨"Quot-ind", quo 1 (.const Tests.Theory.Quotient.refs.ind [.param 0])
      (Certified.Quotient.indType Tests.Theory.Quotient.refs), primitives⟩,
  ⟨"Quot-lift-universe", Tests.Theory.Quotient.betaInput, primitives⟩,
  ⟨"Quot-lift-Prop", quo 0 (Tests.Theory.Quotient.betaProof .zero)
      (Tests.Theory.Quotient.betaProposition .zero), primitives⟩,
  ⟨"Quot-lift-Type", quo 0 (Tests.Theory.Quotient.betaProof (.succ .zero))
      (Tests.Theory.Quotient.betaProposition (.succ .zero)), primitives⟩,
  ⟨"Quot-proof-universe", quo 1 (Tests.Theory.Quotient.propLiftProof (.param 0))
      (Tests.Theory.Quotient.propLiftProposition (.param 0)), primitives⟩,
  ⟨"Quot-proof-Prop", quo 0 (Tests.Theory.Quotient.propLiftProof .zero)
      (Tests.Theory.Quotient.propLiftProposition .zero), primitives⟩,
  ⟨"Box-dependent-projection", Tests.Theory.Structure.boxInput, primitives⟩,
  ⟨"Box-eta-Prop", struc Tests.Theory.Structure.box 0 (Tests.Theory.Structure.etaProof .zero)
      (Tests.Theory.Structure.etaProposition .zero), primitives⟩,
  ⟨"Box-eta-universe", struc Tests.Theory.Structure.box 1 (Tests.Theory.Structure.etaProof (.param 0))
      (Tests.Theory.Structure.etaProposition (.param 0)), primitives⟩,
  ⟨"Pair-projection", struc Tests.Theory.Structure.pair 0 Tests.Theory.Structure.pairProof
      Tests.Theory.Structure.boxProposition, primitives⟩,
  ⟨"Box-field-Prop", struc Tests.Theory.Structure.box 0 (Tests.Theory.Structure.fieldProof .zero)
      (Tests.Theory.Structure.fieldProposition .zero), primitives⟩,
  ⟨"Box-field-Type", struc Tests.Theory.Structure.box 0 (Tests.Theory.Structure.fieldProof (.succ .zero))
      (Tests.Theory.Structure.fieldProposition (.succ .zero)), primitives⟩,
  ⟨"Box-field-universe", struc Tests.Theory.Structure.box 1 (Tests.Theory.Structure.fieldProof (.param 0))
      (Tests.Theory.Structure.fieldProposition (.param 0)), primitives⟩,
  ⟨"Pair-eta-Prop", struc Tests.Theory.Structure.pair 0 (Tests.Theory.Structure.pairEtaProof .zero)
      (Tests.Theory.Structure.pairEtaProposition .zero), primitives⟩,
  ⟨"Pair-eta-universe", struc Tests.Theory.Structure.pair 1 (Tests.Theory.Structure.pairEtaProof (.param 0))
      (Tests.Theory.Structure.pairEtaProposition (.param 0)), primitives⟩,
  ⟨"Nat-zero", natural Tests.Theory.Natural.zero 0, Tests.Theory.Natural.profile⟩,
  ⟨"Nat-literal", natural (Tests.Theory.Natural.numeral 4) 4, Tests.Theory.Natural.profile⟩,
  ⟨"Nat-succ", natural (Tests.Theory.Natural.succ (.natLit 8)) 9, Tests.Theory.Natural.profile⟩,
  ⟨"Nat-definition", natural (.const (.member 302 0) []) 3, Tests.Theory.Natural.profile⟩,
  ⟨"Nat-add-zero", natural (Tests.Theory.Natural.add (.natLit 0) (.natLit 0)) 0, Tests.Theory.Natural.profile⟩,
  ⟨"Nat-add", Tests.Theory.Natural.sampleInput, Tests.Theory.Natural.profile⟩,
  ⟨"Nat-mul", natural (Tests.Theory.Natural.mul (.natLit 2) (.natLit 3)) 6, Tests.Theory.Natural.profile⟩,
  ⟨"Nat-mul-zero", natural (Tests.Theory.Natural.mul (.natLit 5) (.natLit 0)) 0, Tests.Theory.Natural.profile⟩
]

#guard positive.length = 30

def witness? (c : Case) : Option (PreparedInput × ProofWitness Address) := do
  let p ← prepare? 6400 c.profile c.target c.blobs c.literals
  let w ← Ix.Theory.Certificate.proofWitness? 6400 p.signature p.input
  return (p, w)

def accepted (c : Case) : Bool :=
  (witness? c).any fun (_, w) => acceptsSerialized.{0} 6400 c.profile c.target c.blobs w c.literals

#guard positive.all fun s => (make? s.name s.signature s.input).any accepted

structure Mutation where
  name : String
  original : ProofInput Nat
  altered : ProofInput Nat
  signature : PrimitiveSignature Nat := primitives

def mutatedSources : List Mutation :=
  [Tests.Theory.Standard.falseAxiom, Tests.Theory.Standard.unsafeAxiom,
    Tests.Theory.Standard.wrongArity].zipIdx.map (fun (alter, i) =>
      ⟨s!"bad-standard-{i}", Tests.Theory.Standard.propextInput,
        { Tests.Theory.Standard.propextInput with store := Tests.Theory.Standard.store alter }, primitives⟩) ++
  [Tests.Theory.Quotient.wrongKind, Tests.Theory.Quotient.wrongArity,
    Tests.Theory.Quotient.falseSound, Tests.Theory.Quotient.unsafeSound,
    Tests.Theory.Quotient.wrongLift].zipIdx.map (fun (alter, i) =>
      ⟨s!"bad-quotient-{i}", Tests.Theory.Quotient.betaInput,
        { Tests.Theory.Quotient.betaInput with store := Tests.Theory.Quotient.store alter }, primitives⟩) ++
  [Tests.Theory.Structure.wrongFieldCount, Tests.Theory.Structure.wrongRecursor].zipIdx.map (fun (alter, i) =>
      ⟨s!"bad-structure-{i}", Tests.Theory.Structure.boxInput,
        { Tests.Theory.Structure.boxInput with store := Tests.Theory.Structure.store Tests.Theory.Structure.box alter }, primitives⟩) ++
  [Tests.Theory.Natural.unsafeNat, Tests.Theory.Natural.forgedRule,
    Tests.Theory.Natural.changedAdd].zipIdx.map (fun (alter, i) =>
      ⟨s!"bad-natural-{i}", Tests.Theory.Natural.sampleInput,
        { Tests.Theory.Natural.sampleInput with store := Tests.Theory.Natural.store alter }, Tests.Theory.Natural.profile⟩) ++
  [(.member 200 0, 2), (.member 100 0, 1)].zipIdx.map (fun ((r, field), i) =>
      ⟨s!"bad-projection-{i}", Tests.Theory.Structure.boxInput,
        { Tests.Theory.Structure.boxInput with proof := (Tests.Theory.Structure.badProjectionProof r field).erase }, primitives⟩) ++
  [⟨"bad-Nat-answer", Tests.Theory.Natural.sampleInput,
    { Tests.Theory.Natural.sampleInput with proposition :=
      (Tests.Theory.Natural.proposition (Tests.Theory.Natural.add (.natLit 2) (.natLit 3)) (.natLit 6)).erase },
    Tests.Theory.Natural.profile⟩]

/-- The altered bytes are validly hashed. A certificate is obtained for the
original complete declarations at these addresses and first validated on the
control input. Reusing it on the altered authenticated input must fail. -/
def rejectsSource (m : Mutation) : Bool := Id.run do
  let some c := make? m.name m.signature m.altered | return false
  let some p := repaired? c m.original | return false
  let some w := Ix.Theory.Certificate.proofWitness? 6400 p.signature p.input | return false
  return acceptsCertified.{0,0} 6400 p.signature p.input w &&
    !acceptsSerialized.{0} 6400 c.profile c.target c.blobs w c.literals

#guard mutatedSources.length = 16
#guard mutatedSources.all rejectsSource


structure WitnessMutation where
  scenario : Nat
  name : String
  alter : ProofWitness Address → ProofWitness Address

def mapDeclarations (f : DeclarationWitness Address → DeclarationWitness Address)
    (w : ProofWitness Address) : ProofWitness Address :=
  { w with declarations := w.declarations.map f }

def witnessMutations : List WitnessMutation := [
  ⟨0, "standard-before-prerequisites", fun w => { w with declarations := w.declarations.reverse }⟩,
  ⟨8, "quotient-missing-type", mapDeclarations fun d => match d with
    | .quotient q => .quotient { q with types := q.types.drop 1 }
    | other => other⟩,
  ⟨8, "quotient-wrong-rule", mapDeclarations fun d => match d with
    | .quotient q => .quotient { q with liftRule := q.indRule }
    | other => other⟩,
  ⟨8, "quotient-wrong-owner", mapDeclarations fun d => match d with
    | .quotient q => .quotient { q with refs := { q.refs with ctor := q.refs.type } }
    | other => other⟩,
  ⟨13, "structure-without-facts", mapDeclarations fun d => match d with
    | .structure s => .ordinary s.facts.block
    | other => other⟩,
  ⟨13, "structure-wrong-field-sorts", mapDeclarations fun d => match d with
    | .structure s => .structure { s with facts := { s.facts with description :=
        { s.facts.description with fields := s.facts.description.fields.map fun f => { f with level := .zero } } } }
    | other => other⟩,
  ⟨13, "structure-dependent-rule-order", mapDeclarations fun d => match d with
    | .structure s => .structure { s with iota := s.iota.reverse }
    | other => other⟩,
  ⟨27, "natural-without-facts", mapDeclarations fun d => match d with
    | .natural n => .ordinary n
    | other => other⟩
]

def rejectsWitness (m : WitnessMutation) : Bool := Id.run do
  let some s := positive[m.scenario]? | return false
  let some c := make? s.name s.signature s.input | return false
  let some (_, w) := witness? c | return false
  return acceptsSerialized.{0} 6400 c.profile c.target c.blobs w c.literals &&
    !acceptsSerialized.{0} 6400 c.profile c.target c.blobs (m.alter w) c.literals

#guard witnessMutations.all rejectsWitness

def naturalCase := make? "Nat-add" Tests.Theory.Natural.profile Tests.Theory.Natural.sampleInput

def missingPin (c : Case) : Case := { c with profile := { c.profile with natType := none } }
def wrongPin (c : Case) : Case :=
  { c with profile := { c.profile with natType := reference c.references (.member 100 0) } }

def rejectsProfile (alter : Case → Case) : Bool := Id.run do
  let some c := naturalCase | return false
  let some (_, w) := witness? c | return false
  let changed := alter c
  return !acceptsSerialized.{0} 6400 changed.profile changed.target changed.blobs w changed.literals

#guard [missingPin, wrongPin].all rejectsProfile

structure IngressMutation where
  name : String
  altered : Option Case

def ingressMutations : List IngressMutation := [
  ⟨"missing-literal-blob", naturalCase.map fun c => { c with literals := [] }⟩,
  ⟨"literal-bytes-under-old-hash", naturalCase.map fun c =>
    { c with literals := c.literals.map fun (a, bytes) => (a, bytes.push 1) }⟩,
  ⟨"noncanonical-literal-new-hash", naturalCase.bind fun c => rehash? c (fun bytes => bytes.push 0)⟩,
  ⟨"duplicate-literal-blob", naturalCase.map fun c => { c with literals := c.literals ++ c.literals }⟩,
  ⟨"literal-in-constant-domain", naturalCase.map fun c => { c with blobs := c.blobs ++ c.literals, literals := [] }⟩,
  ⟨"constant-in-literal-domain", naturalCase.bind fun c => do
    let eq ← reference c.references (.member 100 0)
    rehash? c id fun a source =>
      if a = c.target then match source.info with
        | .defn d => { source with
            refs := source.refs.push eq
            info := .defn { d with
              typ := mapLiterals source.refs.size.toUInt64 d.typ
              value := mapLiterals source.refs.size.toUInt64 d.value } }
        | _ => source
      else source⟩,
  ⟨"projection-wrapper-wrong-kind", do
    let c ← make? "Box-dependent-projection" primitives Tests.Theory.Structure.boxInput
    let owner ← reference c.references (.member 200 0)
    rehash? c id fun a source => if a = owner then match source.info with
      | .iPrj p => { source with info := .rPrj ⟨p.idx, p.block⟩ }
      | _ => source
    else source⟩
]

def rejectsIngress (m : IngressMutation) : Bool :=
  m.altered.any fun c => (prepare? 6400 c.profile c.target c.blobs c.literals).isNone

#guard ingressMutations.length = 7
#guard ingressMutations.all rejectsIngress

def writeCase (directory : System.FilePath) (c : Case) : IO Unit := do
  let directory := directory / c.name
  IO.FS.createDirAll directory
  for (a, bytes) in c.blobs do
    IO.FS.writeBinFile (directory / s!"{hexOfBytes a.hash}.ixon") bytes
  for (a, bytes) in c.literals do
    IO.FS.writeBinFile (directory / s!"{hexOfBytes a.hash}.nat") bytes
  let metadata := Lean.Json.mkObj [
    ("target", toJson (hexOfBytes c.target.hash)),
    ("falseType", toJson (hexOfBytes c.profile.falseType.hash)),
    ("falseElim", toJson (hexOfBytes c.profile.falseElim.hash)),
    ("natType", toJson (c.profile.natType.map fun a => hexOfBytes a.hash)),
    ("constants", toJson (c.blobs.map fun (a, _) => hexOfBytes a.hash)),
    ("naturals", toJson (c.literals.map fun (a, _) => hexOfBytes a.hash))]
  IO.FS.writeFile (directory / "target.json") (metadata.pretty ++ "\n")

def run (directory : Option System.FilePath) : IO Unit := do
  for s in positive do
    let some c := make? s.name s.signature s.input | throw (IO.userError s!"fixture construction failed: {s.name}")
    unless accepted c do throw (IO.userError s!"serialized acceptance failed: {s.name}")
    if let some directory := directory then writeCase directory c
  for m in mutatedSources do
    unless rejectsSource m do throw (IO.userError s!"source rejection failed: {m.name}")
    if let some directory := directory then
      let some c := make? m.name m.signature m.altered | throw (IO.userError s!"mutation construction failed: {m.name}")
      writeCase directory c
  for m in witnessMutations do
    unless rejectsWitness m do throw (IO.userError s!"witness rejection failed: {m.name}")
  for (name, alter) in [("missing-Nat-pin", missingPin), ("wrong-Nat-pin", wrongPin)] do
    unless rejectsProfile alter do throw (IO.userError s!"profile rejection failed: {name}")
    if let some directory := directory then
      let some c := naturalCase | throw (IO.userError "natural fixture construction failed")
      writeCase directory { (alter c) with name }
  for m in ingressMutations do
    unless rejectsIngress m do throw (IO.userError s!"ingress rejection failed: {m.name}")
    if let some directory := directory then
      let some c := m.altered | throw (IO.userError s!"ingress mutation construction failed: {m.name}")
      writeCase directory { c with name := m.name }
  IO.println <| (Lean.Json.mkObj [
    ("serializedAccepted", toJson positive.length),
    ("sourceRejectedWithValidWitness", toJson mutatedSources.length),
    ("forgedWitnessRejected", toJson witnessMutations.length),
    ("profileRejected", toJson (2 : Nat)),
    ("ingressRejected", toJson ingressMutations.length),
    ("unexpectedErrors", toJson (0 : Nat))]).compress

end Tests.Certified.Features
