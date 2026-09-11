/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Ingress
import Ix.Theory.Certificate.Build
import Ix.Certified.ModelHints

namespace Ix.Certified

open Ix.Theory.Certified

/-- Untrusted witness search from selected addresses in the actual source
store. A returned witness still has to pass the certified TcM entry point. -/
def suggestSource? (fuel : Nat) (source : Ixon.Env) (profile : Profile) (target : Address)
    (selection : InputSelection) (hints : List ModelHint := []) : Option (ProofWitness Address) := do
  let (snapshot, _) ← readSnapshot? fuel source selection {}
  let prepared ← snapshot.prepare? fuel profile target
  let models ← modelCandidates? snapshot.decodedObjects prepared.input.store hints
  Ix.Theory.Certificate.proofWitness? fuel prepared.signature prepared.input models

/-- Search for complete declaration groups for every requested source subject. -/
def suggestStore? (fuel : Nat) (source : Ixon.Env) (profile : Profile) (subjects : List Address)
    (selection : InputSelection) (hints : List ModelHint := []) : Option (List (DeclarationWitness Address)) := do
  let (snapshot, _) ← readSnapshot? fuel source selection {}
  let prepared ← snapshot.prepareStore? fuel profile subjects
  let models ← modelCandidates? snapshot.decodedObjects prepared.store hints
  Ix.Theory.Certificate.storeWitness? fuel prepared.signature prepared.store prepared.targets models

end Ix.Certified
