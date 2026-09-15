/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Certified.FeatureCases
import Tests.Certified.Source
import Ix.Certified.ClaimSuggest
import Ix.Certified.ClaimCommand
import Tests.Theory.Claims

/-! Native tests of the versioned claim byte boundary. All hints are built
outside the checker and every outcome goes through `acceptsClaimBytes`. -/

namespace Tests.Certified.Claims

open Ix.Theory Ix.Theory.Certified Ix.Theory.Model Ix.Certified Serialize
open Lean (toJson)

set_option maxRecDepth 32768
set_option maxHeartbeats 32000000

def fuel : Nat := 6400

def tree : List Address → Ix.AssumptionTree
  | [] => .padding
  | [a] => .leaf a
  | a :: rest => .node (.leaf a) (tree rest)

def optionalRoot (addresses : List Address) : Option Address :=
  if addresses.isEmpty then none else some (treeRoot (tree addresses))

def optionalBytes (addresses : List Address) : Option ByteArray :=
  if addresses.isEmpty then none else some (treeBytes (tree addresses))

structure Fixture where
  name : String
  source : Case
  envelope : Envelope
  hint : LogicalHint
  witness : LogicalWitness

def Fixture.bytes (f : Fixture) : ByteArray := envelopeBytes f.envelope
def Fixture.address (f : Fixture) : Address := Address.blake3 f.bytes
def Fixture.accepted (f : Fixture) : Bool :=
  acceptsClaimBytes.{0} fuel (Source.source f.source) f.address f.bytes (.logical f.witness)

/-- Untrusted test producer computes the logical-use tree from the checked
leaf manifest. The public acceptance call independently recomputes it. -/
def finish? (name : String) (c : Case) (claim : Ix.Claim) (hint : LogicalHint) : Option Fixture := do
  let envelope : Envelope := ⟨Protocol.current, c.profile, claim, none⟩
  let source := Source.source c
  let witness ← suggestLogical? fuel source envelope hint
  let (snapshot, _) ← readSnapshot? fuel source hint.selection {}
  let signature ← readSignature? c.profile snapshot.decodedObjects
  let store ← readStore? fuel snapshot.decodedObjects snapshot.decodedNaturals
  let leaves ← witness.leaves.mapM (readLeafInput? fuel snapshot.decodedObjects)
  let batch ← checkBatch?.{0,0} fuel signature store witness.frontier
    (leaves.map (fun leaf => leaf.prepared.node signature))
  let axioms := hint.selection.objects.filter fun address =>
    (subjectReferences? snapshot.decodedObjects address).any fun refs =>
      !refs.isEmpty && refs.all batch.logicalUses.contains
  let axiomTree := optionalBytes axioms
  return ⟨name, c, { envelope with logicalAxioms := optionalRoot axioms },
    { hint with axiomTree }, { witness with axiomTree }⟩

def single? (c : Case) : Option Fixture :=
  let claim : Ix.Claim := .check c.target none
  finish? (c.name ++ "-check") c claim
    ⟨Source.selection c, [⟨claim, none, none⟩], none, none, none, none, []⟩

def environment? (c : Case) : Option Fixture :=
  let subjects := tree (Source.subjects c)
  let claim : Ix.Claim := .checkEnv (treeRoot subjects) none
  finish? (c.name ++ "-environment") c claim
    ⟨Source.selection c, [⟨claim, some (treeBytes subjects), none⟩],
      some (treeBytes subjects), none, none, none, []⟩

def rejectsEnvelope (f : Fixture) (envelope : Envelope) : Bool :=
  let bytes := envelopeBytes envelope
  !acceptsClaimBytes.{0} fuel (Source.source f.source) (Address.blake3 bytes) bytes (.logical f.witness)

def hostile (f : Fixture) : Bool := Id.run do
  let source := Source.source f.source
  let check := fun w => acceptsClaimBytes.{0} fuel source f.address f.bytes (.logical w)
  if !f.accepted then return false
  if acceptsClaimBytes.{0} 0 source f.address f.bytes (.logical f.witness) then return false
  if acceptsClaimBytes.{0} fuel source f.source.target f.bytes (.logical f.witness) then return false
  let trailing := f.bytes.push 0
  if acceptsClaimBytes.{0} fuel source (Address.blake3 trailing) trailing (.logical f.witness) then return false
  for protocol in [
      { Protocol.current with format := 2 }, { Protocol.current with codec := 2 },
      { Protocol.current with checker := Protocol.current.checker + 1 }, { Protocol.current with policy := 2 },
      { Protocol.current with aggregation := 2 }] do
    if !rejectsEnvelope f { f.envelope with protocol } then return false
  if !rejectsEnvelope f { f.envelope with profile := { f.envelope.profile with
      falseType := f.source.profile.falseElim, falseElim := f.source.profile.falseType } } then return false
  if check { f.witness with leaves := [] } then return false
  if check { f.witness with leaves := f.witness.leaves.map fun leaf => { leaf with declarations := [] } } then
    return false
  if check { f.witness with selection := { f.witness.selection with
      objects := f.source.target :: f.witness.selection.objects } } then return false
  if check { f.witness with selection := { f.witness.selection with
      objects := f.witness.selection.objects.filter (· != f.source.target) } } then return false
  let forged := treeBytes (.leaf f.source.target)
  if check { f.witness with frontierTree := some forged } then return false
  if check { f.witness with axiomTree := some forged } then return false
  if check { f.witness with leaves := f.witness.leaves.map fun leaf =>
      { leaf with
        claim := .contains (treeRoot (.leaf f.source.target)) f.source.target,
        subjects := none } } then return false
  if !rejectsEnvelope f { f.envelope with claim := .eval f.source.target f.source.target none } then
    return false
  if f.envelope.logicalAxioms.isSome && !rejectsEnvelope f { f.envelope with logicalAxioms := none } then
    return false
  return true

def diamondCase? : Option Case :=
  let T := (Tests.Theory.Checker.identityType (.param 0)).erase
  let store := Tests.Theory.Claims.store fun n c => if n = 14 then
    .defn 1 .theorem T (.app (.lam T (.bvar 0)) (.const (.member 12 0) [.param 0])) .safe else c
  make? "diamond" Tests.Theory.Certified.primitives
    ⟨store, 1, .const (.member 15 0) [.param 0], T⟩

def checkLeaf (subject : Address) (frontier : List Address) : LeafHint :=
  ⟨.check subject (optionalRoot frontier), none, optionalBytes frontier⟩

def envLeaf (subjects frontier : List Address) : LeafHint :=
  ⟨.checkEnv (treeRoot (tree subjects)) (optionalRoot frontier),
    some (treeBytes (tree subjects)), optionalBytes frontier⟩

def diamond? (openFrontier : Bool := false) (catalog : Bool := false) : Option Fixture := do
  let c ← diamondCase?
  let a ← reference c.references (.member 12 0)
  let b ← reference c.references (.member 13 0)
  let d ← reference c.references (.member 14 0)
  let e ← reference c.references (.member 15 0)
  let specs := if openFrontier then [([b], [a]), ([d], [a]), ([e], [b, d])]
    else [([a], []), ([b], [a]), ([d], [a]), ([e], [b, d])]
  let leaves := specs.map fun (subjects, frontier) =>
    if catalog then envLeaf subjects frontier else checkLeaf subjects[0]! frontier
  let content := tree (specs.flatMap Prod.fst)
  let frontier := if openFrontier then [a] else []
  let members := tree (leaves.filterMap fun leaf => environmentRoot? leaf.claim)
  let claim := if catalog then .catalog (treeRoot members) (treeRoot content) (optionalRoot frontier)
    else .checkEnv (treeRoot content) (optionalRoot frontier)
  finish? s!"diamond-{openFrontier}-{catalog}" c claim
    ⟨Source.selection c, leaves, some (treeBytes content),
      if catalog then some (treeBytes members) else none, optionalBytes frontier, none, []⟩

def diamondTests (f : Fixture) : Bool := Id.run do
  if !f.accepted then return false
  let source := Source.source f.source
  let check := fun w => acceptsClaimBytes.{0} fuel source f.address f.bytes (.logical w)
  if check { f.witness with leaves := f.witness.leaves.reverse } then return false
  if check { f.witness with leaves := f.witness.leaves.drop 1 } then return false
  if !check { f.witness with leaves := f.witness.leaves ++ f.witness.leaves } then return false
  if check { f.witness with frontier := [] } && (claimFrontier f.envelope.claim).isSome then return false
  if check { f.witness with members := f.witness.subjects } && f.witness.members.isSome then return false
  return true

def warm (f : Fixture) : Bool := Id.run do
  let source := Source.source f.source
  let step := Ix.Kernel.certifiedClaimStep.{0} fuel source f.address f.bytes (.logical f.witness)
  let .ok _ cold := step.run Ix.Kernel.initialCertifiedState | return false
  let start := { cold with checker := Source.poisonedChecker f.source }
  let .ok _ cached := step.run start | return false
  let size := f.witness.selection.objects.length + f.witness.selection.naturals.length
  if cached.inputCache.hits != size || cached.inputCache.misses != size then return false
  let .error _ failed := (Ix.Kernel.certifiedClaimStep.{0} fuel source f.address f.bytes
    (.logical { f.witness with leaves := [] })).run cached | return false
  if failed.inputCache.hits != cached.inputCache.hits || failed.inputCache.misses != cached.inputCache.misses then
    return false
  let changed := { source with consts := source.consts.erase f.source.target }
  let .error _ absent := (Ix.Kernel.certifiedClaimStep.{0} fuel changed f.address f.bytes (.logical f.witness)).run failed
    | return false
  if absent.inputCache.hits != cached.inputCache.hits || absent.inputCache.misses != cached.inputCache.misses then
    return false
  let .ok _ retry := step.run absent | return false
  return retry.inputCache.hits == 2 * size && retry.inputCache.misses == size && retry.checker.inferOnly

structure WireCase where
  name : String
  source : Case
  envelope : Envelope
  hint : ClaimCommand.Hint
  expected : Bool := true

def WireCase.bytes (w : WireCase) : ByteArray := envelopeBytes w.envelope
def WireCase.request (w : WireCase) : ClaimCommand.Request := ⟨Address.blake3 w.bytes, w.hint⟩
def WireCase.passes (w : WireCase) : Bool :=
  (ClaimCommand.run.{0} fuel (Source.source w.source) w.bytes w.request).isOk == w.expected

def Fixture.wire (f : Fixture) : WireCase := ⟨f.name, f.source, f.envelope, .logical f.hint, true⟩

def rawFalseAlias (index : UInt64) : Ixon.MutConst := .defn {
  kind := .thm, safety := .safe, lvls := 0, typ := .ref 0 #[], value := .recur index #[] }

/-- Self-block indices make this a finite, canonically hashed source cycle;
there is no assumed collision or circular hash-address construction. -/
def cycleCase : Case :=
  let block := Fixtures.encode ⟨.muts #[rawFalseAlias 1, rawFalseAlias 0], #[], #[Fixtures.profile.falseType], #[]⟩
  let a := Fixtures.encode ⟨.dPrj ⟨0, block.1⟩, #[], #[], #[]⟩
  let b := Fixtures.encode ⟨.dPrj ⟨1, block.1⟩, #[], #[], #[]⟩
  ⟨"cycle", Fixtures.profile, a.1, Fixtures.prelude ++ [block, a, b], [],
    [(.member 20 0, a.1), (.member 20 1, b.1)], [(20, block.1)]⟩

def cycleWires? : Option (List WireCase) := do
  let c := cycleCase
  let a ← reference c.references (.member 20 0)
  let b ← reference c.references (.member 20 1)
  let left := checkLeaf a [b]
  let right := checkLeaf b [a]
  let one := fun leaf => LogicalHint.mk (Source.selection c) [leaf] none none leaf.frontierTree none []
  let subjects := tree [a, b]
  let envelope : Envelope := ⟨Protocol.current, c.profile, .checkEnv (treeRoot subjects) none, none⟩
  let both := fun leaves => LogicalHint.mk (Source.selection c) leaves (some (treeBytes subjects)) none none none []
  return [
    (← finish? "cycle-A-assuming-B" c left.claim (one left)).wire,
    (← finish? "cycle-B-assuming-A" c right.claim (one right)).wire,
    ⟨"cycle-closed-AB", c, envelope, .logical (both [left, right]), false⟩,
    ⟨"cycle-closed-BA", c, envelope, .logical (both [right, left]), false⟩,
    ⟨"cycle-own-assumption", c, ⟨Protocol.current, c.profile, (checkLeaf a [a]).claim, none⟩,
      .logical (one (checkLeaf a [a])), false⟩]

def containsWires (c : Case) : List WireCase :=
  let content : Ix.AssumptionTree := .node (.leaf c.target) (.node .padding (.leaf c.profile.falseType))
  let claim := Ix.Claim.contains (treeRoot content) c.target
  let envelope : Envelope := ⟨Protocol.current, c.profile, claim, none⟩
  [⟨"contains-padding", c, envelope, .contains (treeBytes content), true⟩,
   ⟨"contains-absent", c, { envelope with claim := .contains (treeRoot content) c.profile.falseElim },
     .contains (treeBytes content), false⟩,
   ⟨"contains-wrong-root", c, { envelope with claim := .contains c.target c.target },
     .contains (treeBytes content), false⟩,
   ⟨"contains-trailing-tree", c, envelope, .contains ((treeBytes content).push 0), false⟩,
   ⟨"contains-logical-axioms", c, { envelope with logicalAxioms := some (treeRoot content) },
     .contains (treeBytes content), false⟩,
   ⟨"contains-as-logical", c, envelope,
     .logical ⟨Source.selection c, [⟨claim, none, none⟩], none, none, none, none, []⟩, false⟩]

def revealCtor (ctor : Ixon.Constructor) : Ix.RevealConstructorInfo :=
  ⟨some ctor.isUnsafe, some ctor.lvls, some ctor.cidx, some ctor.params, some ctor.fields,
    some (expressionAddress ctor.typ)⟩

def revealCtors (ctors : Array Ixon.Constructor) : Option (Array (UInt64 × Ix.RevealConstructorInfo)) :=
  some (ctors.toList.zipIdx.map fun (ctor, index) => (index.toUInt64, revealCtor ctor)).toArray

def revealRules (rules : Array Ixon.RecursorRule) : Option (Array Ix.RevealRecursorRule) :=
  some (rules.toList.zipIdx.map fun (rule, index) =>
    ⟨index.toUInt64, rule.fields, expressionAddress rule.rhs⟩).toArray

def revealMut : Ixon.MutConst → Ix.RevealMutConstInfo
  | .defn d => .defn (some d.kind) (some d.safety) (some d.lvls)
      (some (expressionAddress d.typ)) (some (expressionAddress d.value))
  | .indc d => .indc (some d.isUnsafe) (some d.lvls) (some d.params) (some d.indices)
      (some (expressionAddress d.typ)) (revealCtors d.ctors)
  | .recr d => .recr (some d.k) (some d.isUnsafe) (some d.lvls) (some d.params) (some d.indices)
      (some d.motives) (some d.minors) (some (expressionAddress d.typ)) (revealRules d.rules)

def revealInfo : Ixon.ConstantInfo → Ix.RevealConstantInfo
  | .defn d => .defn (some d.kind) (some d.safety) (some d.lvls)
      (some (expressionAddress d.typ)) (some (expressionAddress d.value))
  | .recr d => .recr (some d.k) (some d.isUnsafe) (some d.lvls) (some d.params) (some d.indices)
      (some d.motives) (some d.minors) (some (expressionAddress d.typ)) (revealRules d.rules)
  | .axio d => .axio (some d.isUnsafe) (some d.lvls) (some (expressionAddress d.typ))
  | .quot d => .quot (some d.kind) (some d.lvls) (some (expressionAddress d.typ))
  | .cPrj d => .cPrj (some d.idx) (some d.cidx) (some d.block)
  | .iPrj d => .iPrj (some d.idx) (some d.block)
  | .rPrj d => .rPrj (some d.idx) (some d.block)
  | .dPrj d => .dPrj (some d.idx) (some d.block)
  | .muts ds => .muts (ds.toList.zipIdx.map fun (d, index) => (index.toUInt64, revealMut d)).toArray

def corruptInfo : Ix.RevealConstantInfo → Ix.RevealConstantInfo
  | .defn k s u t b => .defn k s ((u.getD 0 + 1) |> some) t b
  | .recr k s u p i m n t r => .recr k s u p i (some (m.getD 0 + 1)) n t r
  | .axio s u t => .axio (some (!(s.getD false))) u t
  | .quot k u t => .quot k (some (u.getD 0 + 1)) t
  | .cPrj i c b => .cPrj i (some (c.getD 0 + 1)) b
  | .iPrj i b => .iPrj (some (i.getD 0 + 1)) b
  | .rPrj i b => .rPrj (some (i.getD 0 + 1)) b
  | .dPrj i b => .dPrj (some (i.getD 0 + 1)) b
  | .muts ds => .muts (ds.push (100000, .defn none none none none none))

def revealWires? (c : Case) : Option (List WireCase) := do
  let mut result := []
  for ((address, bytes), index) in c.blobs.zipIdx do
    let object ← decodeObject? address bytes
    let info := revealInfo object.val.info
    let opening : Ixon.Comm := ⟨Address.blake3 "C6 reveal secret".toUTF8, address⟩
    let envelope : Envelope := ⟨Protocol.current, c.profile, .reveal opening.commit info, none⟩
    result := result ++ [
      ⟨s!"{c.name}-reveal-{index}", c, envelope, .reveal ⟨opening⟩, true⟩,
      ⟨s!"{c.name}-reveal-altered-{index}", c,
        { envelope with claim := .reveal opening.commit (corruptInfo info) }, .reveal ⟨opening⟩, false⟩,
      ⟨s!"{c.name}-reveal-secret-{index}", c, envelope,
        .reveal ⟨{ opening with secret := c.target }⟩, false⟩]
  return result

def hexJson (bytes : Option ByteArray) : Lean.Json := toJson (bytes.map hexOfBytes)

def leafJson (hint : LeafHint) : Lean.Json := Lean.Json.mkObj [
  ("claim", toJson (hexOfBytes (Ix.Claim.ser hint.claim))),
  ("subjects", hexJson hint.subjects), ("frontier", hexJson hint.frontierTree)]

def requestJson (request : ClaimCommand.Request) : Lean.Json :=
  let fields := match request.hint with
    | .logical hint => [
      ("kind", toJson "logical"),
      ("objects", toJson (hint.selection.objects.map fun a => hexOfBytes a.hash)),
      ("naturals", toJson (hint.selection.naturals.map fun a => hexOfBytes a.hash)),
      ("leaves", toJson (hint.leaves.map leafJson)),
      ("subjects", hexJson hint.subjects), ("members", hexJson hint.members),
      ("frontier", hexJson hint.frontierTree), ("axioms", hexJson hint.axiomTree)] ++
      (if hint.models.isEmpty then [] else [("models", toJson (hint.models.map ModelHint.json))])
    | .contains bytes => [("kind", toJson "contains"), ("tree", toJson (hexOfBytes bytes))]
    | .reveal witness => [("kind", toJson "reveal"),
      ("secret", toJson (hexOfBytes witness.opening.secret.hash)),
      ("payload", toJson (hexOfBytes witness.opening.payload.hash))]
  Lean.Json.mkObj (("address", toJson (hexOfBytes request.address.hash)) :: fields)

def writeWire (directory : System.FilePath) (w : WireCase) : IO Unit := do
  let directory := directory / w.name
  IO.FS.createDirAll directory
  let .ok source := Ixon.serEnv (Source.source w.source)
    | throw (IO.userError s!"cannot serialize {w.name}")
  IO.FS.writeBinFile (directory / "source.ixe") source
  IO.FS.writeBinFile (directory / "envelope.bin") w.bytes
  IO.FS.writeFile (directory / "request.json") ((requestJson w.request).pretty ++ "\n")
  IO.FS.writeFile (directory / "expected.json")
    ((Lean.Json.mkObj [("accepted", toJson w.expected)]).compress ++ "\n")

def runWire (directory : Option System.FilePath) (w : WireCase) : IO Unit := do
  unless w.passes do throw (IO.userError s!"claim command outcome failed: {w.name}")
  let .ok request := ClaimCommand.readRequest (requestJson w.request)
    | throw (IO.userError s!"claim request parsing failed: {w.name}")
  unless (ClaimCommand.run.{0} fuel (Source.source w.source) w.bytes request).isOk == w.expected do
    throw (IO.userError s!"claim parsed request outcome failed: {w.name}")
  if let some directory := directory then writeWire directory w

def run (directory : Option System.FilePath) : IO Unit := do
  let mut count := 0
  let mut axioms := 0
  let mut revelations := 0
  for c in Source.cases do
    for (label, produce) in [("check", single?), ("environment", environment?)] do
      let some f := produce c | throw (IO.userError s!"claim producer declined {c.name}/{label}")
      unless f.accepted do throw (IO.userError s!"claim rejected {f.name}")
      unless hostile f do throw (IO.userError s!"claim mutation escaped {f.name}")
      unless warm f do throw (IO.userError s!"claim cache rollback failed {f.name}")
      runWire directory f.wire
      count := count + 1
      if f.envelope.logicalAxioms.isSome then axioms := axioms + 1
    let some reveals := revealWires? c | throw (IO.userError s!"reveal producer declined {c.name}")
    for w in reveals do runWire directory w
    revelations := revelations + reveals.length
  for openFrontier in [false, true] do
    for catalog in [false, true] do
      let some f := diamond? openFrontier catalog | throw (IO.userError s!"diamond producer declined {openFrontier}/{catalog}")
      unless diamondTests f do throw (IO.userError s!"diamond failed {f.name}")
      runWire directory f.wire
  let some cycles := cycleWires? | throw (IO.userError "cycle producer declined")
  for w in cycles do runWire directory w
  let some cycleReveals := revealWires? cycleCase | throw (IO.userError "cycle reveal producer declined")
  for w in cycleReveals do runWire directory w
  revelations := revelations + cycleReveals.length
  for w in containsWires cycleCase do runWire directory w
  IO.println <| (Lean.Json.mkObj [
    ("sourceClaimsAccepted", toJson count), ("nonemptyAxiomRoots", toJson axioms),
    ("sourceMutationScenarios", toJson count), ("diamondScenarios", toJson (4 : Nat)),
    ("warmClaimScenarios", toJson count), ("cycleScenarios", toJson cycles.length),
    ("containsScenarios", toJson (containsWires cycleCase).length),
    ("revealScenarios", toJson revelations),
    ("unexpectedErrors", toJson (0 : Nat))]).compress

end Tests.Certified.Claims
