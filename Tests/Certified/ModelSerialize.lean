/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Certified.Serialize
import Ix.Certified.ModelHints

/-! General test serializer for complete mutual blocks, including recursors
and every public member/constructor projection. All model declarations are
ordinary source objects in the same authenticated .ixe environment. -/

namespace Tests.Certified.ModelSerialize

open Ix.Theory Ix.Theory.Certified Ix.Certified Serialize

def mutualInfo (self : Nat) (resolve : ConstRef Nat → Option Address) (source : Const Nat) :
    Write Ixon.MutConst := do
  match ← constantInfo self resolve source with
  | .muts #[.indc family] => return .indc family
  | .defn definition => return .defn definition
  | .recr recursor => return .recr recursor
  | _ => failure

def block (self : Nat) (resolve : ConstRef Nat → Option Address) (source : Block Nat) :
    Option (Ixon.Constant × ConstantBlobs) := do
  let action : Write Ixon.ConstantInfo := match source.members with
    | [member] => constantInfo self resolve member
    | [] => failure
    | members => return .muts (← members.mapM (mutualInfo self resolve)).toArray
  let (info, tables) ← action {}
  return (⟨info, #[], tables.refs, tables.univs⟩, tables.literals)

def memberProjection? (kind : ConstKind) (index : Nat) (address : Address) : Option Ixon.Constant :=
  match kind with
  | .induct => some ⟨.iPrj ⟨index.toUInt64, address⟩, #[], #[], #[]⟩
  | .recursor => some ⟨.rPrj ⟨index.toUInt64, address⟩, #[], #[], #[]⟩
  | .defn _ => some ⟨.dPrj ⟨index.toUInt64, address⟩, #[], #[], #[]⟩
  | _ => none

/-- The finite domain is in source dependency order; unused empty slots are
omitted. Every nonempty member and source field is serialized literally. -/
def make? (name : String) (signature : PrimitiveSignature Nat) (input : ProofInput Nat) : Option Case := do
  if 900 ∈ input.store.dom then none else do
    let mut blobs : ConstantBlobs := []
    let mut literals : ConstantBlobs := []
    let mut references : List (ConstRef Nat × Address) := []
    let mut blocks : List (Nat × Address) := []
    for b in input.store.dom do
      let source ← input.store.blocks b
      if !source.members.isEmpty then
        let (raw, extra) ← block b (reference references) source
        let encoded := Fixtures.encode raw
        blobs := blobs ++ [encoded]
        literals := literals ++ extra
        blocks := blocks ++ [(b, encoded.1)]
        for (member, index) in source.members.zipIdx do
          let address ← match raw.info with
            | .muts _ => do
              let projection ← memberProjection? member.kind index encoded.1
              let projection := Fixtures.encode projection
              blobs := blobs ++ [projection]
              pure projection.1
            | _ => pure encoded.1
          references := references ++ [(.member b index, address)]
          match member with
          | .induct _ _ _ _ ctors _ =>
            for ctor in List.range ctors.length do
              let projection := Fixtures.encode ⟨.cPrj ⟨index.toUInt64, ctor.toUInt64, encoded.1⟩, #[], #[], #[]⟩
              blobs := blobs ++ [projection]
              references := references ++ [(.ctor b index ctor, projection.1)]
          | _ => pure ()
    let (raw, extra) ← constant 900 (reference references)
      (.defn input.universes .theorem input.proposition input.proof .safe)
    let target := Fixtures.encode raw
    let falseType ← reference references signature.falseType
    let falseElim ← reference references signature.falseElim
    let natType ← signature.natType.mapM (reference references)
    return ⟨name, ⟨falseType, falseElim, natType⟩, target.1, uniqueBlobs (blobs ++ [target]),
      uniqueBlobs (literals ++ extra), references ++ [(.member 900 0, target.1)], blocks ++ [(900, target.1)]⟩

def hint? (c : Case) (candidate : Certificate.Modeled.Candidate Nat) : Option ModelHint := do
  let source ← ((c.blocks.find? (fun (key, _) => key = candidate.source)).map Prod.snd)
  let recursors ← candidate.recursors.mapM (reference c.references)
  let targets ← candidate.models.mapM (reference c.references)
  let proofs ← candidate.proofs.mapM fun (owner, proofs) => do
    let owner ← reference c.references owner
    let proofs ← proofs.mapM fun proof => proof.mapM fun proof => do
      let .const term _ := proof.proof | none
      return (⟨← reference c.references proof.equality, ← reference c.references proof.reflexivity,
        ← reference c.references proof.recursor, ← reference c.references term⟩ : ModelProofHint)
    return (⟨owner, proofs⟩ : ModelRuleHints)
  return ⟨source, recursors, targets, proofs⟩

/-- Reconstruct every original mutual member at the mutated wire addresses.
This deliberately unauthenticated control is used only to obtain a complete,
valid certificate before attacking the authenticated acceptance gate. -/
def repaired? (c : Case) (original : ProofInput Nat) : Option PreparedInput := do
  let prepared ← prepare? 6400 c.profile c.target c.blobs c.literals
  let mapping := fun b => ((c.blocks.find? fun (key, _) => key = b).map Prod.snd).getD c.target
  let originals := c.blocks.map fun (b, a) => (a, (if b = 900 then
    some (⟨[.defn original.universes .theorem original.proposition original.proof .safe]⟩ : Block Nat)
    else original.store.blocks b).map (fun source =>
      (⟨source.members.map (renameConstant mapping)⟩ : Block Address)))
  let old := prepared.input.store
  let store : Store Address := {
    dom := old.dom, nodup := old.nodup,
    blocks := fun a => (old.blocks a).map fun block => ((lookup originals a).join).getD block,
    mem_dom := by intro a; simp [old.mem_dom] }
  let .defn _ _ proposition proof _ ← store.lookup (.member c.target 0) | none
  return { prepared with input := { prepared.input with store, proposition, proof } }

end Tests.Certified.ModelSerialize
