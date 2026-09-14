/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Certified.Modeled

namespace Tests.Certified.ModeledAdversarial

open Ix.Theory Ix.Theory.Certified Ix.Certified Ix.Kernel Serialize Modeled
open Lean (toJson)

set_option maxRecDepth 32768
set_option maxHeartbeats 64000000

def changeBlock (input : ProofInput Nat) (key : Nat) (alter : Block Nat → Block Nat) : ProofInput Nat :=
  let old := input.store
  { input with store := {
      dom := old.dom, nodup := old.nodup,
      blocks := fun b => (old.blocks b).map fun block => if b = key then alter block else block,
      mem_dom := by intro b; simp [old.mem_dom] } }

def changeMembers (input : ProofInput Nat) (key : Nat) (alter : Const Nat → Const Nat) : ProofInput Nat :=
  changeBlock input key fun block => ⟨block.members.map alter⟩

def changeRecursor (tag : String) : Const Nat → Const Nat
  | .recursor u p i m n t rs k s => match tag with
    | "global-rule-order" => .recursor u p i m n t rs.reverse k s
    | "omitted-global-rule" => .recursor u p i m n t (rs.take 2) k s
    | "rule-fields" => .recursor u p i m n t (rs.map fun r => { r with nfields := r.nfields + 1 }) k s
    | "rule-rhs" => .recursor u p i m n t (rs.map fun r => { r with rhs := .sort .zero }) k s
    | "rule-telescope" => .recursor u p i m n t (rs.map fun r => { r with rhs := match r.rhs with
        | .lam _ body => .lam (.sort .zero) body | body => body }) k s
    | "k" => .recursor u p i m n t rs true s
    | "unsafe-recursor" => .recursor u p i m n t rs k .unsafe
    | "parameters" => .recursor u (p + 1) i m n t rs k s
    | "indices" => .recursor u p (i + 1) m n t rs k s
    | "motives" => .recursor u p i (m + 1) n t rs k s
    | "minors" => .recursor u p i m (n + 1) t rs k s
    | "levels" => .recursor (u + 1) p i m n t rs k s
    | "level-permutation" => .recursor u p i m n (t.instL [.param 1, .param 0]) rs k s
    | _ => .recursor u p i m n t rs k s
  | c => c

def changeFamily (tag : String) : Const Nat → Const Nat
  | .induct u p i t cs s => match tag with
    | "constructor-order" => .induct u p i t cs.reverse s
    | "constructor-fields" => .induct u p i t (cs.map fun c => { c with nfields := c.nfields + 1 }) s
    | "constructor-levels" => .induct u p i t (cs.map fun c => { c with uvars := c.uvars + 1 }) s
    | "constructor-parameters" => .induct u p i t (cs.map fun c => { c with nparams := c.nparams + 1 }) s
    | "unsafe-family" => .induct u p i t cs .unsafe
    | "unsafe-constructor" => .induct u p i t (cs.map fun c => { c with safety := .unsafe }) s
    | _ => .induct u p i t cs s
  | c => c

structure SourceMutation where
  name : String
  original : Scenario
  input : ProofInput Nat

def mutualCase : Scenario := ⟨"mutual-unequal", Tests.Theory.Modeled.input, Tests.Theory.Modeled.candidate⟩
def nested : Scenario := ⟨"nested-parameter", Tests.Theory.ModeledNested.input false, Tests.Theory.ModeledNested.candidate⟩
def recursivePi : Scenario := ⟨"nested-recursive-Pi", Tests.Theory.ModeledNested.input true, Tests.Theory.ModeledNested.candidate⟩
def propositional : Scenario := ⟨"propositional-equations", Tests.Theory.ModeledEquations.input, Tests.Theory.ModeledEquations.candidate⟩

def sourceMutations : List SourceMutation :=
  (["global-rule-order", "omitted-global-rule", "rule-fields", "rule-rhs", "rule-telescope",
    "k", "unsafe-recursor", "parameters", "indices", "motives", "minors", "levels"].map fun tag =>
      ⟨s!"mutual-{tag}", mutualCase, changeMembers mutualCase.input 31 (changeRecursor tag)⟩) ++
  (["constructor-order", "constructor-fields", "constructor-levels", "constructor-parameters",
    "unsafe-family", "unsafe-constructor"].map fun tag =>
      ⟨s!"mutual-{tag}", mutualCase, changeMembers mutualCase.input 30 (changeFamily tag)⟩) ++ [
    ⟨"mutual-family-type", mutualCase, changeMembers mutualCase.input 30 fun c => match c with
      | .induct u p i _ cs s => .induct u p i (.sort (.succ (.succ .zero))) cs s | c => c⟩,
    ⟨"mutual-recursor-order", mutualCase, changeBlock mutualCase.input 31 fun b => ⟨b.members.reverse⟩⟩,
    ⟨"unproved-model-axiom", mutualCase, changeMembers mutualCase.input 40 fun c => .axiom c.uvars c.type .safe⟩,
    ⟨"changed-model-body", mutualCase, changeMembers mutualCase.input 40 fun c => match c with
      | .defn n k t _ s => .defn n k t (.lam Tests.Theory.Modeled.natType (.const (.ctor 20 0 0) [])) s
      | c => c⟩,
    ⟨"circular-model", mutualCase, changeMembers mutualCase.input 40 fun c => match c with
      | .defn n k t _ s => .defn n k t (.const (.ctor 30 1 0) []) s | c => c⟩,
    ⟨"nested-level-permutation", nested, changeMembers nested.input 41 (changeRecursor "level-permutation")⟩,
    ⟨"nested-rule-fields", nested, changeMembers nested.input 41 (changeRecursor "rule-fields")⟩,
    ⟨"recursive-Pi-level-permutation", recursivePi,
      changeMembers recursivePi.input 41 (changeRecursor "level-permutation")⟩,
    ⟨"recursive-Pi-rule-telescope", recursivePi,
      changeMembers recursivePi.input 41 (changeRecursor "rule-telescope")⟩,
    ⟨"unproved-equation-axiom", propositional,
      changeMembers propositional.input 70 fun c => .axiom c.uvars c.type .safe⟩,
    ⟨"unrelated-equation-proof", propositional,
      changeMembers propositional.input 70 fun c => match c with
        | .defn n k t _ s => .defn n k t (.const (.member 40 0) []) s
        | c => c⟩]

def mutationFixture? (m : SourceMutation) : Option Fixture :=
  fixture? { m.original with name := m.name, input := m.input }

def control? (f : Fixture) (original : ProofInput Nat) : Option (PreparedInput × ProofWitness Address) := do
  let prepared ← ModelSerialize.repaired? f.source original
  let objects ← decodeObjects? f.source.blobs
  let models ← modelCandidates? objects prepared.input.store [f.model]
  let witness ← Certificate.proofWitness? fuel prepared.signature prepared.input models
  return (prepared, witness)

/-- A complete semantic certificate succeeds on the original declarations at
the new addresses, then fails on the actual authenticated altered source.
The same declaration certificate is submitted to the claim acceptance root. -/
def rejectsSource (f : Fixture) (original : ProofInput Nat) : Bool := Id.run do
  let some (prepared, witness) := control? f original | return false
  unless acceptsCertified.{0,0} fuel prepared.signature prepared.input witness do return false
  let some (_, env) := Source.loadedIxe? f.source | return false
  if acceptsCertifiedSource.{0} fuel env f.source.profile f.source.target (Source.selection f.source) witness then
    return false
  if acceptsCertifiedStoreSource.{0} fuel env f.source.profile (Source.subjects f.source)
      (Source.selection f.source) witness.declarations then return false
  let claim := Ix.Claim.check f.source.target none
  let envelope : Envelope := ⟨Protocol.current, f.source.profile, claim, none⟩
  let leaf : LeafWitness := ⟨claim, none, none, [], witness.declarations⟩
  let logical : LogicalWitness := ⟨Source.selection f.source, [leaf], none, none, none, [], none⟩
  let bytes := envelopeBytes envelope
  return !acceptsCertifiedClaim.{0} fuel env (Address.blake3 bytes) bytes (.logical logical)

def witnessMutations : List (String × (Ix.Theory.Certified.Modeled.Witness Address →
    Ix.Theory.Certified.Modeled.Witness Address)) := [
  ("recursor-order", fun w => { w with recursors := w.recursors.reverse }),
  ("companion-order", fun w => { w with companions := w.companions.reverse }),
  ("missing-companion", fun w => { w with companions := w.companions.drop 1 }),
  ("missing-equation", fun w => { w with equations := w.equations.drop 1 }),
  ("self-model", fun w => { w with companions := w.companions.map fun c => { c with model := c.header.ref } }),
  ("unrelated-left-side", fun w => { w with companions := w.companions.map fun c =>
      { c with rules := c.rules.map fun r => { r with lhs := r.rhs } } }),
  ("forged-conversion", fun w => { w with equations := w.equations.map (fun ps =>
      ps.map fun p => { p with proof := .conversion .refl }) })]

def rejectsWitnesses (f : Fixture) : Bool := Id.run do
  let env := Source.source f.source
  let some witness := suggestSource? fuel env f.source.profile f.source.target (Source.selection f.source) [f.model]
    | return false
  return witnessMutations.all fun (_, alter) =>
    let witness := { witness with declarations := witness.declarations.map fun declaration => match declaration with
      | .modeled model => .modeled (alter model) | declaration => declaration }
    !acceptsCertifiedSource.{0} fuel env f.source.profile f.source.target (Source.selection f.source) witness &&
      !acceptsCertifiedStoreSource.{0} fuel env f.source.profile (Source.subjects f.source)
        (Source.selection f.source) witness.declarations

def negativeWire (f : Fixture) : Claims.WireCase :=
  let claim := Ix.Claim.check f.source.target none
  ⟨f.scenario.name, f.source, ⟨Protocol.current, f.source.profile, claim, none⟩,
    .logical ⟨Source.selection f.source, [⟨claim, none, none⟩], none, none, none, none, [f.model]⟩, false⟩

def writeNegative (directory : System.FilePath) (f : Fixture) : IO Unit := do
  let directory := directory / f.scenario.name
  IO.FS.createDirAll directory
  let some (bytes, _) := Source.loadedIxe? f.source | throw (IO.userError "cannot write mutated .ixe")
  IO.FS.writeBinFile (directory / "source.ixe") bytes
  IO.FS.writeFile (directory / "request.json") ((Modeled.requestJson f.request).pretty ++ "\n")
  IO.FS.writeFile (directory / "expected.json")
    ((Lean.Json.mkObj [("proof", toJson false), ("store", toJson false)]).compress ++ "\n")

def ingressNames : List String := ["family-order", "constructor-index", "family-wrapper-kind",
  "family-wrapper-slot", "recursor-wrapper-kind", "recursor-wrapper-slot", "constructor-wrapper-slot",
  "missing-universe-table", "missing-reference-table"]

/-- These mutations preserve fresh hashes and update every dependent address.
Malformed mutual projections and tables must fail even before model search. -/
def ingressFixture? (name : String) : Option Fixture := do
  let original ← fixture? mutualCase
  let family ← reference original.source.references (.member 30 0)
  let recursor ← reference original.source.references (.member 31 0)
  let constructor ← reference original.source.references (.ctor 30 1 0)
  let source ← rehash? original.source id fun address source =>
    if address = original.model.source && name = "family-order" then
      match source.info with
      | .muts members => { source with info := .muts members.reverse }
      | _ => source
    else if address = original.model.source && name = "constructor-index" then
      match source.info with
      | .muts members => { source with info := .muts (members.map fun member => match member with
          | .indc family => .indc { family with ctors := family.ctors.map fun ctor => { ctor with cidx := ctor.cidx + 1 } }
          | member => member) }
      | _ => source
    else if address = family && name = "family-wrapper-kind" then
      match source.info with
      | .iPrj p => { source with info := .rPrj ⟨p.idx, p.block⟩ } | _ => source
    else if address = family && name = "family-wrapper-slot" then
      match source.info with
      | .iPrj p => { source with info := .iPrj { p with idx := 999 } } | _ => source
    else if address = recursor && name = "recursor-wrapper-kind" then
      match source.info with
      | .rPrj p => { source with info := .dPrj ⟨p.idx, p.block⟩ } | _ => source
    else if address = recursor && name = "recursor-wrapper-slot" then
      match source.info with
      | .rPrj p => { source with info := .rPrj { p with idx := 999 } } | _ => source
    else if address = constructor && name = "constructor-wrapper-slot" then
      match source.info with
      | .cPrj p => { source with info := .cPrj { p with cidx := 999 } } | _ => source
    else if address = original.source.target && name = "missing-universe-table" then { source with univs := #[] }
    else if address = original.source.target && name = "missing-reference-table" then { source with refs := #[] }
    else source
  let name := s!"ingress-{name}"
  let model ← ModelSerialize.hint? source mutualCase.candidate
  return ⟨{ mutualCase with name }, { source with name }, model⟩

def run (directory : Option System.FilePath := none) : IO Unit := do
  for scenario in scenarios do
    let some f := fixture? scenario | throw (IO.userError s!"modeled witness fixture failed: {scenario.name}")
    unless rejectsWitnesses f do throw (IO.userError s!"modeled forged witness escaped: {scenario.name}")
  for m in sourceMutations do
    let some f := mutationFixture? m | throw (IO.userError s!"modeled mutation serialization failed: {m.name}")
    unless rejectsSource f m.original.input do throw (IO.userError s!"modeled valid-control source mutation escaped: {m.name}")
    let some (_, env) := Source.loadedIxe? f.source | throw (IO.userError s!"modeled mutation load failed: {m.name}")
    if (Command.run.{0} "proof" fuel env f.request).isOk || (Command.run.{0} "store" fuel env f.request).isOk then
      throw (IO.userError s!"modeled mutated command accepted: {m.name}")
    Claims.runWire (directory.map (· / "claims")) (negativeWire f)
    if let some directory := directory then writeNegative (directory / "source") f
    IO.println <| (Lean.Json.mkObj [("sourceMutation", toJson m.name), ("controlAccepted", toJson true),
      ("sourceRejected", toJson true), ("claimRejected", toJson true)]).compress
  for name in ingressNames do
    let some f := ingressFixture? name | throw (IO.userError s!"modeled ingress construction failed: {name}")
    unless (prepare? fuel f.source.profile f.source.target f.source.blobs f.source.literals).isNone do
      throw (IO.userError s!"modeled malformed mutual source decoded: {name}")
    let some (_, env) := Source.loadedIxe? f.source | throw (IO.userError s!"modeled ingress .ixe load failed: {name}")
    if (Command.run.{0} "proof" fuel env f.request).isOk || (Command.run.{0} "store" fuel env f.request).isOk then
      throw (IO.userError s!"modeled malformed mutual command accepted: {name}")
    Claims.runWire (directory.map (· / "claims")) (negativeWire f)
    if let some directory := directory then writeNegative (directory / "source") f
  IO.println <| (Lean.Json.mkObj [("sourceMutations", toJson sourceMutations.length),
    ("forgedWitnesses", toJson (scenarios.length * witnessMutations.length)),
    ("ingressMutations", toJson ingressNames.length),
    ("unexpectedErrors", toJson (0 : Nat))]).compress

end Tests.Certified.ModeledAdversarial
