/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.Suggest
import Ix.Kernel.Certified

/-! Generic source-file driver for the certified profile. The JSON request
selects the expected target/subjects, primitive signature and finite source
closure. Witness search is untrusted and always followed by certified TcM
validation. There is no inference-only or unchecked fallback command. -/

namespace Ix.Certified.Command

universe v

structure Request where
  profile : Profile
  target : Address
  subjects : List Address
  selection : InputSelection
  models : List ModelHint := []

def readAddress (value : String) : Except String Address :=
  match Address.fromString value with
  | none => .error "expected a 32-byte hexadecimal address"
  | some address => .ok address

def readRequest (json : Lean.Json) : Except String Request := do
  let falseType ← readAddress (← json.getObjValAs? String "falseType")
  let falseElim ← readAddress (← json.getObjValAs? String "falseElim")
  let natural ← json.getObjValAs? (Option String) "natType"
  let natType ← natural.mapM readAddress
  let target ← readAddress (← json.getObjValAs? String "target")
  let subjects ← (← json.getObjValAs? (List String) "subjects").mapM readAddress
  let objects ← (← json.getObjValAs? (List String) "objects").mapM readAddress
  let naturals ← (← json.getObjValAs? (List String) "naturals").mapM readAddress
  return ⟨⟨falseType, falseElim, natType⟩, target, subjects, ⟨objects, naturals⟩, ← ModelHint.readOptional json⟩

def run (mode : String) (fuel : Nat) (source : Ixon.Env) (request : Request) : Except String Unit := do
  if mode = "proof" then
    let some witness := suggestSource? fuel source request.profile request.target request.selection request.models
      | throw "certified proof witness search declined"
    if Kernel.acceptsCertifiedSource.{v} fuel source request.profile request.target request.selection witness then
      return ()
    else throw "certified proof validation rejected the witness"
  else if mode = "store" then
    let some witness := suggestStore? fuel source request.profile request.subjects request.selection request.models
      | throw "certified declaration witness search declined"
    if Kernel.acceptsCertifiedStoreSource.{v} fuel source request.profile request.subjects request.selection witness then
      return ()
    else throw "certified declaration validation rejected the witness"
  else throw "mode must be proof or store"

/-- The generic command can report success only after an actual certified
source run. Witness search is not an alternate acceptance path. -/
theorem run_success {mode : String} {fuel : Nat} {source : Ixon.Env} {request : Request}
    (h : run.{v} mode fuel source request = .ok ()) :
    (mode = "proof" ∧ ∃ witness, Kernel.acceptsCertifiedSource.{v} fuel source
      request.profile request.target request.selection witness = true) ∨
    (mode = "store" ∧ ∃ witness, Kernel.acceptsCertifiedStoreSource.{v} fuel source
      request.profile request.subjects request.selection witness = true) := by
  by_cases hp : mode = "proof"
  · cases hw : suggestSource? fuel source request.profile request.target request.selection request.models with
    | none => simp [run, hp, hw] at h
    | some witness =>
      by_cases ha : Kernel.acceptsCertifiedSource.{v} fuel source request.profile request.target request.selection witness = true
      · exact .inl ⟨hp, witness, ha⟩
      · simp [run, hp, hw, ha] at h
  · by_cases hs : mode = "store"
    · cases hw : suggestStore? fuel source request.profile request.subjects request.selection request.models with
      | none => simp [run, hs, hw] at h
      | some witness =>
        by_cases ha : Kernel.acceptsCertifiedStoreSource.{v} fuel source request.profile request.subjects request.selection witness = true
        · exact .inr ⟨hs, witness, ha⟩
        · simp [run, hs, hw, ha] at h
    · simp [run, hp, hs] at h

def main (args : List String) : IO UInt32 := do
  let [mode, sourcePath, requestPath] := args | do
    IO.eprintln "usage: certified-check proof|store SOURCE.ixe REQUEST.json"
    return 2
  let bytes ← IO.FS.readBinFile sourcePath
  let requestText ← IO.FS.readFile requestPath
  let result := do
    let request ← readRequest (← Lean.Json.parse requestText)
    let parts ← Ixon.deEnvVerifiedLazy bytes
    run.{0} mode 6400 parts.env request
  match result with
  | .error error => IO.eprintln error; return 1
  | .ok () =>
    IO.println <| (Lean.Json.mkObj [("accepted", Lean.toJson true), ("mode", Lean.toJson mode)]).compress
    return 0

end Ix.Certified.Command
