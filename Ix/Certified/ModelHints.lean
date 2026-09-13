/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Bytes
import Ix.Theory.Certificate.Modeled

/-! Optional untrusted model-package hints refer to actual stored objects.
No mathematical declaration is supplied by a hint: model definitions and
equation proofs come from the selected authenticated source store and are
admitted before the original block by the ordinary certified checker. -/

namespace Ix.Certified

open Ix.Theory

structure ModelProofHint where
  equality : Address
  reflexivity : Address
  eliminator : Address
  proof : Address

structure ModelRuleHints where
  owner : Address
  proofs : List (Option ModelProofHint)

structure ModelHint where
  source : Address
  recursors : List Address
  targets : List Address
  proofs : List ModelRuleHints := []

def modelCandidate? (objects : Objects) (store : Store Address) (hint : ModelHint) :
    Option (Certificate.Modeled.Candidate Address) := do
  let recursors ← hint.recursors.mapM (resolveReference? objects)
  let targets ← hint.targets.mapM (resolveReference? objects)
  let proofs ← hint.proofs.mapM fun rules => do
    let owner ← resolveReference? objects rules.owner
    let universes ← store.uvars owner
    let proofs ← rules.proofs.mapM fun proof => proof.mapM fun proof => do
      let equality ← resolveReference? objects proof.equality
      let reflexivity ← resolveReference? objects proof.reflexivity
      let eliminator ← resolveReference? objects proof.eliminator
      let ref ← resolveReference? objects proof.proof
      return (⟨equality, reflexivity, eliminator,
        .const ref ((List.range universes).map VLevel.param)⟩ : Certificate.Modeled.ProofHint Address)
    return (owner, proofs)
  return ⟨hint.source, recursors, targets, proofs⟩

def modelCandidates? (objects : Objects) (store : Store Address) (hints : List ModelHint) :
    Option (List (Certificate.Modeled.Candidate Address)) := hints.mapM (modelCandidate? objects store)

namespace ModelHint

def address (value : String) : Except String Address :=
  match Address.fromString value with
  | none => .error "expected a 32-byte hexadecimal model address"
  | some address => .ok address

def readProof (json : Lean.Json) : Except String ModelProofHint := do
  return ⟨← address (← json.getObjValAs? String "equality"),
    ← address (← json.getObjValAs? String "reflexivity"),
    ← address (← json.getObjValAs? String "eliminator"),
    ← address (← json.getObjValAs? String "proof")⟩

def readRules (json : Lean.Json) : Except String ModelRuleHints := do
  let owner ← address (← json.getObjValAs? String "owner")
  let values ← json.getObjValAs? (List (Option Lean.Json)) "proofs"
  let proofs ← values.mapM (Option.mapM readProof)
  return ⟨owner, proofs⟩

def read (json : Lean.Json) : Except String ModelHint := do
  let source ← address (← json.getObjValAs? String "source")
  let recursors ← (← json.getObjValAs? (List String) "recursors").mapM address
  let targets ← (← json.getObjValAs? (List String) "targets").mapM address
  let proofs ← match json.getObjVal? "proofs" with
    | .error _ => pure []
    | .ok values => (← values.getArr?).toList.mapM readRules
  return ⟨source, recursors, targets, proofs⟩

def readOptional (json : Lean.Json) : Except String (List ModelHint) := do
  match json.getObjVal? "models" with
  | .error _ => pure []
  | .ok models => (← models.getArr?).toList.mapM read

def proofJson (hint : ModelProofHint) : Lean.Json := Lean.Json.mkObj [
  ("equality", Lean.toJson (hexOfBytes hint.equality.hash)),
  ("reflexivity", Lean.toJson (hexOfBytes hint.reflexivity.hash)),
  ("eliminator", Lean.toJson (hexOfBytes hint.eliminator.hash)),
  ("proof", Lean.toJson (hexOfBytes hint.proof.hash))]

def rulesJson (hint : ModelRuleHints) : Lean.Json := Lean.Json.mkObj [
  ("owner", Lean.toJson (hexOfBytes hint.owner.hash)),
  ("proofs", Lean.toJson (hint.proofs.map (Option.map proofJson)))]

def json (hint : ModelHint) : Lean.Json := Lean.Json.mkObj [
  ("source", Lean.toJson (hexOfBytes hint.source.hash)),
  ("recursors", Lean.toJson (hint.recursors.map (hexOfBytes ·.hash))),
  ("targets", Lean.toJson (hint.targets.map (hexOfBytes ·.hash))),
  ("proofs", Lean.toJson (hint.proofs.map rulesJson))]

end ModelHint
end Ix.Certified
