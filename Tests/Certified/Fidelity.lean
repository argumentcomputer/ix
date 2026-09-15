/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Certified.Source
import Ix.Certified.SourceMeaning

namespace Tests.Certified.Fidelity

open Ix.Theory Ix.Theory.Certified Ix.Certified Ix.Kernel Serialize
open Lean (toJson)

set_option maxRecDepth 32768
set_option maxHeartbeats 32000000

def whole (source : Ixon.Constant) : Ixon.Constant :=
  match source.info with
  | .defn value => { source with
      info := .defn { value with typ := .share 0, value := .share 1 },
      sharing := #[value.typ, value.value] }
  | _ => source

def base := whole Fixtures.identity

def nested : Ixon.Constant :=
  match base.info with
  | .defn value => { base with
      info := .defn { value with typ := .share 2, value := .share 3 },
      sharing := base.sharing ++ #[.share 0, .share 1] }
  | _ => base

def permuted : Ixon.Constant :=
  match base.info with
  | .defn value => { base with
      info := .defn { value with typ := .share 1, value := .share 0 },
      sharing := #[Corpus.idBody 0, Corpus.idType 0] }
  | _ => base

def underBinders : Ixon.Constant :=
  match base.info with
  | .defn value => { base with
      info := .defn { value with
        typ := .leanAll (.sort 0) (.share 0), value := .leanLam (.sort 0) (.share 1) },
      sharing := #[.leanAll (.var 0) (.var 1), .leanLam (.var 0) (.var 0)] }
  | _ => base

def input (name : String) (source : Ixon.Constant) (dependencies : List Ixon.Constant := []) : Case :=
  let c := Corpus.one name source dependencies
  { name, profile := Fixtures.profile, target := c.target, blobs := c.blobs,
    literals := [], references := [], blocks := c.blobs.map fun (a, _) => (0, a) }

def positive : List Case := [
  input "sharing-whole-identity" base,
  input "sharing-nested-identity" nested,
  input "sharing-permuted-identity" permuted,
  input "sharing-under-binders" underBinders,
  input "sharing-beta-statement" (whole Corpus.betaStatement),
  input "sharing-eta-statement" (whole Corpus.etaStatement),
  input "sharing-dependent-polymorphic" (whole (Corpus.dependent 1 (.var 0))),
  input "sharing-defined-polymorphic-use" (whole (Corpus.polyUse .defn true)) [Corpus.polyId .defn]
]

#guard positive.length = 8
#guard positive.all Source.accepted
#guard positive.all Source.storeAccepted
#guard positive.all Source.ixeAccepted
#guard positive.all Source.warmAndRollback

def negative : List Case := [
  input "sharing-out-of-bounds" { base with sharing := #[.share 999, Corpus.idBody 0] },
  input "sharing-self-cycle" { base with sharing := #[.share 0, Corpus.idBody 0] },
  input "sharing-mutual-cycle" { base with sharing := #[.share 1, .share 0] },
  input "sharing-altered-statement" { base with
    sharing := #[.ref 0 #[], Corpus.idBody 0], refs := #[Fixtures.falseObject.1] },
  input "sharing-linear-body" { base with
    sharing := #[Corpus.idType 0, .lam .linear (.sort 0) (.leanLam (.var 0) (.var 0))] },
  input "sharing-missing-universe" { base with univs := #[] },
  input "sharing-free-variable" { base with sharing := #[Corpus.idType 0, .var 0] },
  input "sharing-missing-reference" { base with sharing := #[Corpus.idType 0, .ref 999 #[]] }
]

/-- The control certificate checks the complete original declaration at the
altered address. It is then submitted to the actual authenticated source
gate, so witness-search refusal cannot explain these rejections. -/
def validControlRejected (c : Case) : Bool := Id.run do
  let some objects := decodeObjects? c.blobs | return false
  let original := objects.map fun (a, value) => (a, if a = c.target then base else value)
  let some signature := readSignature? c.profile original | return false
  let some prepared := readProofInput? 6400 original c.target | return false
  let some witness := Ix.Theory.Certificate.proofWitness? 6400 signature prepared | return false
  return acceptsCertified.{0,0} 6400 signature prepared witness &&
    !acceptsCertifiedSource.{0} 6400 (Source.source c) c.profile c.target (Source.selection c) witness &&
    !acceptsCertifiedStoreSource.{0} 6400 (Source.source c) c.profile [c.target] (Source.selection c) witness.declarations

#guard negative.length = 8
#guard negative.all validControlRejected

/-- Equal expanded statements do not identify their different wire encodings.
The current bytes must still authenticate under the exact requested address. -/
def distinctEncoding : Bool := Id.run do
  let first := input "first" base
  let second := input "second" permuted
  if first.target = second.target then return false
  let some a := prepare? 6400 first.profile first.target first.blobs | return false
  let some b := prepare? 6400 second.profile second.target second.blobs | return false
  if a.input.proposition != b.input.proposition then return false
  let some witness := suggestSource? 6400 (Source.source first) first.profile first.target (Source.selection first)
    | return false
  let some value := (Source.source second).consts.get? second.target | return false
  let changed := { (Source.source first) with
    consts := (Source.source first).consts.insert first.target value }
  return !acceptsCertifiedSource.{0} 6400 changed first.profile first.target (Source.selection first) witness

#guard distinctEncoding

def run (directory : Option System.FilePath) : IO Unit := do
  for c in positive do
    unless Source.accepted c && Source.storeAccepted c && Source.ixeAccepted c && Source.warmAndRollback c do
      throw (IO.userError s!"source fidelity acceptance failed: {c.name}")
    if let some directory := directory then Source.writeCase directory c
  for c in negative do
    unless validControlRejected c do throw (IO.userError s!"source fidelity mutation escaped: {c.name}")
    if let some directory := directory then Source.writeCase directory c
  unless distinctEncoding do throw (IO.userError "semantic equality was used as byte identity")
  IO.println <| (Lean.Json.mkObj [
    ("proofAccepted", toJson positive.length), ("storesAccepted", toJson positive.length),
    ("ixeAccepted", toJson positive.length), ("warmProofScenarios", toJson positive.length),
    ("validControlSourceMutationsRejected", toJson negative.length),
    ("distinctEncodingRejected", toJson distinctEncoding), ("unexpectedErrors", toJson (0 : Nat))]).compress

end Tests.Certified.Fidelity
