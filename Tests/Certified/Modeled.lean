/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Certified.FeatureCases
import Tests.Certified.ModelSerialize
import Tests.Certified.Claims
import Ix.Certified.Command
import Tests.Theory.ModeledNested
import Tests.Theory.ModeledPermutation
import Tests.Theory.ModeledEquations

/-! C7 exercises actual canonical mutual Ixon blocks, lazy .ixe loading,
checked model declarations, public TcM execution and versioned claims. -/

namespace Tests.Certified.Modeled

open Ix.Theory Ix.Theory.Certified Ix.Certified Ix.Kernel Serialize
open Tests.Theory.Certified (primitives)
open Lean (toJson)

set_option maxRecDepth 32768
set_option maxHeartbeats 64000000

def fuel := 6400

structure Scenario where
  name : String
  input : ProofInput Nat
  candidate : Certificate.Modeled.Candidate Nat

def scenarios : List Scenario := [
  ⟨"mutual-unequal", Tests.Theory.Modeled.input, Tests.Theory.Modeled.candidate⟩,
  ⟨"mutual-permuted", Tests.Theory.ModeledPermutation.input, Tests.Theory.ModeledPermutation.candidate⟩,
  ⟨"auxiliary-merged", Tests.Theory.ModeledPermutation.mergedInput, Tests.Theory.ModeledPermutation.mergedCandidate⟩,
  ⟨"nested-parameter", Tests.Theory.ModeledNested.input false, Tests.Theory.ModeledNested.candidate⟩,
  ⟨"nested-recursive-Pi", Tests.Theory.ModeledNested.input true, Tests.Theory.ModeledNested.candidate⟩,
  ⟨"propositional-equations", Tests.Theory.ModeledEquations.input, Tests.Theory.ModeledEquations.candidate⟩]

structure Fixture where
  scenario : Scenario
  source : Case
  model : ModelHint

def fixture? (scenario : Scenario) : Option Fixture := do
  let source ← ModelSerialize.make? scenario.name primitives scenario.input
  let model ← ModelSerialize.hint? source scenario.candidate
  return ⟨scenario, source, model⟩

def Fixture.request (f : Fixture) : Command.Request :=
  ⟨f.source.profile, f.source.target, Source.subjects f.source, Source.selection f.source, [f.model]⟩

def requestJson (request : Command.Request) : Lean.Json := Lean.Json.mkObj [
  ("falseType", toJson (hexOfBytes request.profile.falseType.hash)),
  ("falseElim", toJson (hexOfBytes request.profile.falseElim.hash)),
  ("natType", toJson (request.profile.natType.map (hexOfBytes ·.hash))),
  ("target", toJson (hexOfBytes request.target.hash)),
  ("subjects", toJson (request.subjects.map (hexOfBytes ·.hash))),
  ("objects", toJson (request.selection.objects.map (hexOfBytes ·.hash))),
  ("naturals", toJson (request.selection.naturals.map (hexOfBytes ·.hash))),
  ("models", toJson (request.models.map ModelHint.json))]

def sourceAccepted (f : Fixture) : Bool := Id.run do
  let some (_, env) := Source.loadedIxe? f.source | return false
  let .ok request := Command.readRequest (requestJson f.request) | return false
  return (Command.run.{0} "proof" fuel env request).isOk && (Command.run.{0} "store" fuel env request).isOk

def pilotDeclines (f : Fixture) : Bool := Id.run do
  let some prepared := prepare? fuel f.source.profile f.source.target f.source.blobs f.source.literals | return false
  let some models := modelCandidates? (decodeObjects? f.source.blobs |>.getD []) prepared.input.store [f.model] | return false
  let some witness := Certificate.proofWitness? fuel prepared.signature prepared.input models | return false
  return !(Packet.words prepared.signature prepared.input witness).isOk

/-- Poisoned legacy caches do not skip either a model declaration or an
equation proof. Failed model checks leave the actual byte cache unchanged. -/
def warmAndRollback (f : Fixture) : Bool := Id.run do
  let some (_, env) := Source.loadedIxe? f.source | return false
  let c := f.source
  let count := c.blobs.length + c.literals.length
  let some witness := suggestSource? fuel env c.profile c.target (Source.selection c) [f.model] | return false
  let .ok _ cold := (certifiedStep.{0} fuel env c.profile c.target (Source.selection c) witness).run initialCertifiedState
    | return false
  if cold.inputCache.misses != count || cold.inputCache.hits != 0 then return false
  let start := { cold with checker := Source.poisonedChecker c }
  let .ok _ warm := (certifiedStep.{0} fuel env c.profile c.target (Source.selection c) witness).run start | return false
  if warm.inputCache.hits != count || warm.inputCache.misses != count then return false
  let bad := { witness with declarations := witness.declarations.map fun declaration => match declaration with
    | .modeled model => .modeled { model with equations := model.equations.map (fun proofs =>
        proofs.map (fun proof => { proof with proof := .conversion .refl })) }
    | declaration => declaration }
  let .error _ failed := (certifiedStep.{0} fuel env c.profile c.target (Source.selection c) bad).run warm | return false
  if failed.inputCache.hits != warm.inputCache.hits || failed.inputCache.misses != warm.inputCache.misses then return false
  let .error _ exhausted := (certifiedStep.{0} 0 env c.profile c.target (Source.selection c) witness).run failed | return false
  if exhausted.inputCache.hits != warm.inputCache.hits || exhausted.inputCache.misses != warm.inputCache.misses then return false
  let .ok _ retry := (certifiedStep.{0} fuel env c.profile c.target (Source.selection c) witness).run exhausted | return false
  return retry.inputCache.hits == 2 * count && retry.inputCache.misses == count

def checkClaim? (f : Fixture) : Option Claims.Fixture :=
  Claims.finish? s!"{f.scenario.name}-check" f.source (.check f.source.target none)
    ⟨Source.selection f.source, [⟨.check f.source.target none, none, none⟩], none, none, none, none, [f.model]⟩

def environmentClaim? (f : Fixture) : Option Claims.Fixture := do
  let subjects := Claims.tree (Source.subjects f.source)
  let claim := Ix.Claim.checkEnv (treeRoot subjects) none
  Claims.finish? s!"{f.scenario.name}-environment" f.source claim
    ⟨Source.selection f.source, [⟨claim, some (treeBytes subjects), none⟩],
      some (treeBytes subjects), none, none, none, [f.model]⟩

def sharedClaim? (f : Fixture) : Option Claims.Fixture := do
  let model ← f.model.targets.getLast?
  let subjects := Claims.tree [model, f.source.target]
  let claim := Ix.Claim.checkEnv (treeRoot subjects) none
  Claims.finish? s!"{f.scenario.name}-shared-model" f.source claim
    ⟨Source.selection f.source, [⟨.check model none, none, none⟩, ⟨.check f.source.target none, none, none⟩],
      some (treeBytes subjects), none, none, none, [f.model]⟩

def claimCases? (f : Fixture) : Option (List Claims.WireCase) := do
  let fixtures ← [checkClaim? f, environmentClaim? f, sharedClaim? f].mapM id
  return fixtures.flatMap fun fixture => [
    ⟨fixture.name, fixture.source, fixture.envelope, .logical fixture.hint, true⟩,
    ⟨s!"{fixture.name}-old-checker", fixture.source,
      { fixture.envelope with protocol := { fixture.envelope.protocol with checker := 1 } },
      .logical fixture.hint, false⟩]

def writeSource (directory : System.FilePath) (f : Fixture) : IO Unit := do
  let directory := directory / f.scenario.name
  IO.FS.createDirAll directory
  let some (bytes, _) := Source.loadedIxe? f.source | throw (IO.userError "cannot write modeled .ixe")
  IO.FS.writeBinFile (directory / "source.ixe") bytes
  IO.FS.writeFile (directory / "request.json") ((requestJson f.request).pretty ++ "\n")
  IO.FS.writeFile (directory / "expected.json")
    ((Lean.Json.mkObj [("proof", toJson true), ("store", toJson true)]).compress ++ "\n")

def run (directory : Option System.FilePath := none) : IO Unit := do
  for scenario in scenarios do
    let some f := fixture? scenario | throw (IO.userError s!"C7 serialization failed: {scenario.name}")
    unless sourceAccepted f do throw (IO.userError s!"C7 source acceptance failed: {scenario.name}")
    unless pilotDeclines f do throw (IO.userError s!"C7 unexpectedly selected C2 VM: {scenario.name}")
    unless warmAndRollback f do throw (IO.userError s!"C7 cache or rollback failed: {scenario.name}")
    let some claims := claimCases? f | throw (IO.userError s!"C7 claim construction failed: {scenario.name}")
    for claim in claims do Claims.runWire (directory.map (· / "claims")) claim
    if let some directory := directory then writeSource (directory / "source") f
    IO.println <| (Lean.Json.mkObj [("case", toJson scenario.name), ("source", toJson true),
      ("cacheRollback", toJson true), ("pilotDeclines", toJson true), ("claims", toJson claims.length)]).compress

end Tests.Certified.Modeled
