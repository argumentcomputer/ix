import Ix.CompileCert.Certifier
import Ix.CompileCert.StrongCone
import Ix.CompileCert.StrongChanged
import Ix.CompileCert.SourcePinGen

/-! # The certifier's S path: the strong-model endpoint per cone

After the W verdicts (`Certifier.run`), `compile-certify --strong` decides the
strong-model endpoint S (`SourceNormalizedInstallation.artifact_strong_model`,
restated for every target model as `artifact_strong_model_all`) on **cones**:
a root, its closed dependency cone as the source, and the records the cone's
names reach, admitted on their own. For each cone the certifier builds, itself:

* the `Input` (source, roots, name map, records, blobs, limits) and its W
  association (`prepareArtifact`, then `checkIndexed` with position hints);
* the Lean-kernel-checked projection-lowering witnesses
  (`LoweringLean.sourceWitnesses`: `addDeclCore` with checking on) and the
  normalised source installation (`installSourceNormalized`, the verified fold
  over the exported cone), with the source-named Nat-operation pins
  (`sourcePins`: `SourcePinGen`'s committed variant, the operations' Lean values
  and the certificate theorems exported under Lean's names), over a cone that
  carries its operations' certificate ground and, with `Quot`, Lean's `Eq`
  first (`coneMembers`);
* the name map: every source declaration to its target name under the accepted
  pins (`ExportContext.name`), the generated-helper bindings
  (`proposeSourceHelperBindings`) and the basis bindings, with the priority of
  `sourceAndHelperNames`, served from a hash map;
* the support declarations: the installed source rows with no target row under
  the map, renamed into the target (`proposeRenamedSupport`); an empty support
  reuses the artifact's own fold (`admittedSupportEmpty`);
* the Nat/DivMod/reduce receipt names: none are proposed (a name that is never
  installed), so the receipt checks accept only their identity case (the
  source operation maps to the target's canonical operation).

then decides `decideStrongCone` (`Ix/CompileCert/StrongCone.lean`). **An
S-Certified constant is a member of the source of a cone for which
`decideStrongCone` returned a `StrongCone`; `StrongCone.sound` is then the
conclusion for it** (W for the cone's input, and for every strong target model
of the admitted cone plus support a strong source model that is its pull-back,
every original declaration installed as its export or through a lowering
receipt).

**Executable-only (no proof):** the choice and order of cones, the cone
budget, the classification of what is not certified (S-Unsupported with a
class, S-Blocked by a dependency, S-Rejected with a diagnostic), the
diagnosis of a refused strong check (which check family, which row), and the
proposal itself (names, support, receipt names). A wrong proposal or triage
can only leave a constant uncertified. The Lean environment is trusted as for W
(`captureCone`), the lowering witnesses as accepted by Lean's kernel (KB), and
the Lean runtime that executes the checks.
-/

namespace Ix.CompileCert.Strong

open Benchmarks.Kernel.CheckIxeStep
open Ix.CompileCert Ix.CompileCert.Certifier

/-! ## Cones (untrusted) -/

/-- The closure of `roots` under `refs` (the certifier's `declarationRefs` sets),
restricted to `known` names; a reference outside `known` is returned as missing. -/
def coneOf (refs : Std.HashMap Lean.Name (Array Lean.Name)) (known : Lean.Name → Bool)
    (roots : Array Lean.Name) : Array Lean.Name × Array Lean.Name := Id.run do
  let mut seen : Std.HashSet Lean.Name := {}
  let mut out : Array Lean.Name := #[]
  let mut missing : Array Lean.Name := #[]
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if !known n then
      missing := missing.push n
      continue
    out := out.push n
    for r in refs.getD n #[] do
      unless seen.contains r do todo := todo.push r
  return (out, missing)

/-- The records a cone's named addresses reach (owners of projection records,
then every stored reference), from the loaded record store. -/
def coneRecords (store : RecordStore) (isBlob : Address → Bool) (seeds : Array Address) :
    Except String RecordStore := Id.run do
  let mut out : RecordStore := {}
  let mut todo := seeds
  while h : todo.size > 0 do
    let a := todo[todo.size - 1]
    todo := todo.pop
    if out.contains a then continue
    let some record := store[a]? | if isBlob a then continue else return .error s!"missing stored dependency {a}"
    let owners := match record.info with
      | .iPrj p => #[p.block]
      | .cPrj p => #[p.block]
      | .rPrj p => #[p.block]
      | .dPrj p => #[p.block]
      | _ => #[]
    todo := todo ++ owners ++ record.refs
    out := out.insert a record
  return .ok out

/-- One cone's `Input` (as `Tests/Ix/CompileCert/Stored.lean`'s `rootInput`, from
the certifier's loaded store): the source in the given order, the map entries
resolved by the cone's own reader setup, the records in check order with the
projection records after them, every blob, limits from the records. -/
def coneInput (env : Lean.Environment) (produced : Ixon.Env) (store : RecordStore)
    (namedAddr : Std.HashMap Lean.Name Address) (roots : List Lean.Name) (members : Array Lean.Name) :
    Except String Input := do
  let source : Source := ⟨members.toList.filterMap env.find?⟩
  let seeds ← members.mapM fun n => match namedAddr[n]? with
    | some a => pure a
    | none => throw s!"no artifact name for {n}"
  let sub ← coneRecords store (produced.blobs.contains ·) seeds
  let pins ← Kernel.Reader.defaultPins
  let pre ← Kernel.Reader.builtinPrelude
  let hints := Hints.ofStore sub produced.anonHints
  let st := setup sub (produced.blobs[·]?) pins pre hints.lookup
  let primaries := st.ordered.filterMap (fun a => (sub[a]?).map (a, ·))
  let projections := (sub.toArray.filter fun (a, c) => owner a c != a).qsort
    (fun a b => a.1.cmpBytes b.1 == .lt)
  let map ← source.declarations.mapM fun ci => do
    let some a := namedAddr[ci.name]? | throw s!"no artifact name for {ci.name}"
    let some target := Kernel.Reader.resolve st.cx.store a
      | throw s!"unresolved artifact name {ci.name}"
    return MapEntry.mk ci.name a target
  let records := (primaries ++ projections).toList.map (fun (a, c) => (a, Ixon.serConstant c))
  let blobs := produced.blobs.toList
  let limits : Kernel.Admission.Limits := ⟨records.length + 1, blobs.length + 1,
    records.foldl (fun n (_, b) => n + b.size) 0 + blobs.foldl (fun n (_, b) => n + b.size) 0 + 1,
    records.foldl (fun n (_, b) => max n b.size) 0 + 1, 1 <<< 24⟩
  return { source, roots, map, limits, records, blobs, hint := hints.lookup }

/-! ## The proposal (untrusted) -/

/-- The first place two kernel expressions differ (diagnostics). -/
def firstDiff : Kernel.Expr → Kernel.Expr → String
  | .app f a, .app g b => if decide (f = g) then firstDiff a b else firstDiff f g
  | .lam d b _, .lam e c _ | .forallE d b _, .forallE e c _ =>
    if decide (d = e) then firstDiff b c else firstDiff d e
  | .proj s i e, .proj t j f => if decide (s = t ∧ i = j) then firstDiff e f else s!"proj {s}.{i} vs {t}.{j}"
  | a, b => if decide (a = b) then "none" else s!"{(reprStr a).take 300} vs {(reprStr b).take 300}"

/-- Constant (`c`) and projection-owner (`p`) references of a kernel expression (diagnostics). -/
def exprConsts : Kernel.Expr → List (String × Kernel.Name)
  | .const n _ => [("c", n)]
  | .app f a => exprConsts f ++ exprConsts a
  | .lam d b _ | .forallE d b _ => exprConsts d ++ exprConsts b
  | .letE t v b => exprConsts t ++ exprConsts v ++ exprConsts b
  | .proj t _ e => ("p", t) :: exprConsts e
  | _ => []

def leanNameOf : Kernel.Name → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (leanNameOf p) s
  | .num p i => .num (leanNameOf p) i

/-- The Nat-operation pin sets of the source fold (`installSourceNormalizedWith`):
the committed source-named variant (`SourcePinGen.sourceNatOpPinSets`,
`SourceNatOpPinData.lean`: the operations' Lean values and the certificate
theorems of `IxC/Kernel/PinGen/Certs.lean` exported under Lean's names, closed
over each operation's Lean cone). The same for every cone: an operation's Lean
cone is in every closed cone that contains it. Untrusted: the fold checks every
pin and certificate it uses, and is sound for any pins. -/
def sourcePins (_input : Input) (_pins : Kernel.Reader.Pins) : List Kernel.NatOpPinSet :=
  SourcePinGen.sourceNatOpPinSets

/-- The builtin Nat-operation pin sets with their constants renamed from the
target's names (the pins name ground constants by Ix address) into the cone's
source names: M4-d's first attempt at the source pins, kept for the `--explain`
diagnostic only (the target merges alias fibers the source keeps apart, so the
renamed certificates do not type-check in the source, M4-d §2.4). -/
def renamedBuiltinPins (input : Input) (pins : Kernel.Reader.Pins) : List Kernel.NatOpPinSet :=
  let cx : ExportContext := ⟨input.source, input.map, pins, noImages⟩
  let inverse : Std.HashMap Kernel.Name Kernel.Name := input.source.declarations.foldl (fun m ci =>
    match cx.name ci.name with
    | .ok t => if m.contains t then m else m.insert t (sourceName ci.name)
    | .error _ => m) {}
  let r := kernelRenameAll (fun n => inverse.getD n n)
  -- a pin is compared with the declaration's own value by definitional equality; the
  -- cone's exported value is proposed when the cone has the operation (the certificates,
  -- checked by the fold, carry the meaning)
  let own (c : Kernel.Name) (pin : Kernel.Expr) : Kernel.Expr :=
    match input.source.find (leanNameOf c) with
    | some ci => match exportSourceEntry ci with
      | .ok (.defn _ value _) => value
      | _ => r pin
    | none => r pin
  match Kernel.Reader.builtinNatOpPins with
  | .error _ => []
  | .ok sets => sets.map fun ps => { ps with
      divPin := own Kernel.natDivName ps.divPin, modPin := own Kernel.natModName ps.modPin,
      gcdPin := own Kernel.natGcdName ps.gcdPin, landPin := own Kernel.natLandName ps.landPin,
      lorPin := own Kernel.natLorName ps.lorPin, xorPin := own Kernel.natXorName ps.xorPin,
      shiftLeftPin := own Kernel.natShiftLeftName ps.shiftLeftPin,
      shiftRightPin := own Kernel.natShiftRightName ps.shiftRightPin, divProofs := ps.divProofs.map r, modProofs := ps.modProofs.map r,
      gcdProofs := ps.gcdProofs.map r, landProofs := ps.landProofs.map r, lorProofs := ps.lorProofs.map r,
      xorProofs := ps.xorProofs.map r, shiftLeftProofs := ps.shiftLeftProofs.map r,
      shiftRightProofs := ps.shiftRightProofs.map r }

/-- A list of pairs under their keys, the first pair of a key winning (as `List.find?`). -/
def firstIndex (pairs : List (Kernel.Name × Kernel.Name)) : Std.HashMap Kernel.Name Kernel.Name :=
  pairs.foldr (fun (k, v) m => m.insert k v) {}

/-- `renameGeneratedSuffix` through an index of the anchors (the first anchor of a name wins,
as `List.find?` takes it). -/
def renameGeneratedSuffixIdx (anchors : Std.HashMap Kernel.Name Kernel.Name) :
    Kernel.Name → Option Kernel.Name
  | .anonymous => anchors[Kernel.Name.anonymous]?
  | name@(.str parent component) => match anchors[name]? with
    | some target => some target
    | none => (renameGeneratedSuffixIdx anchors parent).map (·.str component)
  | name@(.num parent component) => match anchors[name]? with
    | some target => some target
    | none => (renameGeneratedSuffixIdx anchors parent).map (·.num component)

/-- `proposeSourceHelperBindings` with its list scans through hash maps (M7 WP-F; untrusted,
like the original: the same bindings in the same order, computed without the scans of the
original name list per helper and the quadratic conflict check of the anchors). -/
def proposeSourceHelperBindingsIdx {source : Source} (proposal : SourceModelProposal source)
    (original : List (Kernel.Name × Kernel.Name)) : ExportM (List (Kernel.Name × Kernel.Name)) := do
  let originalIdx := firstIndex original
  let mapped (name : Kernel.Name) : Kernel.Name := originalIdx.getD name name
  let mut anchors := original.map fun (sourceName, targetName) =>
    (sourceName.str "_model", targetName.str "_model")
  let mut projections := []
  for evidence in proposal.blocks do
    let block := evidence.shape
    if !Kernel.Frontend.InModel.wants block then continue
    let some owner := block.types.head? | throw "source helper recipe has no owner"
    let some recursor := block.recs.find? (fun r => r.cv.name == owner.cv.name.str "rec")
      | throw "source helper recipe has no primary recursor"
    let some (_, afterParams) := recursor.cv.type.stripPis owner.nP
      | throw "source helper recipe parameter telescope"
    let some (motives, _) := afterParams.stripPis recursor.nM
      | throw "source helper recipe motive telescope"
    let members ← Kernel.Frontend.InModel.readMems owner.cv.levelParams owner.nP
      block.types (motives.map (·.1))
    for member in members do
      let recursorName ← match member.real? with
        | some index => match block.types[index]? with
          | some type => pure (type.cv.name.str "rec")
          | none => throw "source helper recipe member index"
        | none => pure (owner.cv.name.str s!"rec_{member.j + 1}")
      let some memberRecursor := block.recs.find? (fun r => r.cv.name == recursorName)
        | throw "source helper recipe member recursor"
      for rule in memberRecursor.rules do
        anchors := (Kernel.Frontend.InModel.auxCtorName owner.cv.name member.tag rule.ctor,
          Kernel.Frontend.InModel.auxCtorName (mapped owner.cv.name) member.tag (mapped rule.ctor)) :: anchors
    for type in block.types do
      for constructorName in type.ctors do
        let some constructor := block.ctors.find? (fun c => c.cv.name == constructorName)
          | throw "source helper recipe constructor"
        for index in List.range constructor.nF do
          projections := (Kernel.projFnName type.cv.name index,
            Kernel.projFnName (mapped type.cv.name) index) :: projections
  -- conflicting source keys: every pair agrees with the first pair of its key
  let anchorIdx := firstIndex anchors
  unless anchors.all (fun (k, v) => anchorIdx.getD k v == v) do
    throw "conflicting source helper recipe bindings"
  let generated := proposal.declarations.toList.flatMap Kernel.Declaration.names
  return projections ++ generated.filterMap (fun name =>
    (renameGeneratedSuffixIdx anchorIdx name).map (name, ·))

/-- Names, support and receipt names for one cone, given the accepted pins, the image claims and
the admitted target environment (`propose` for W's association; M7 S+a's value-level cones pass
W+'s). Nothing here is trusted: the decision checks every part. -/
def proposeWith {input : Input} (pins : Kernel.Reader.Pins) (images : Lean.Name → Bool) (target : Kernel.Env)
    (installed : SourceNormalizedInstallation input.source input.roots) :
    Except String StrongProposal := do
  -- the export names through the source and map indices (`contextNameL`: `ExportContext.name`
  -- with its lookups given), not the list scans of `cx.name`
  let sIdx := sourceIndex input.source
  let mIdx := mapIndex input.map
  let mappings ← input.source.declarations.mapM fun ci => do
    return (sourceName ci.name, ← contextNameL (fun n => sIdx[n]?) (fun n => mIdx[n]?) pins images ci.name)
  let helpers ← proposeSourceHelperBindingsIdx installed.modelProposal mappings
  let direct : Std.HashMap Kernel.Name Kernel.Name := mappings.foldl (fun m (k, v) => m.insert k v) {}
  -- the projection tables of the installed direct structures, under their owner's image
  let tables := installed.env.consts.filterMap fun entry => match entry with
    | .projInfo tbl => (direct[tbl.structName]?).map fun t => (entry.name, Kernel.projTableName t)
    | _ => none
  -- the indexed projection names an eta capability uses, under their owner's image
  let etaProjections := installed.env.consts.flatMap fun entry => match entry with
    | .indInfo header caps => match direct[header.name]? with
      | some t => (List.range caps.etaFields).map fun i =>
          (Kernel.projFnName header.name i, Kernel.projFnName t i)
      | none => []
    | _ => []
  let bindings := helpers ++ installed.semanticSupport.nameBindings ++ tables ++ etaProjections
  -- the priority of `sourceAndHelperNames`: the first original binding, else the first helper
  let table : Std.HashMap Kernel.Name Kernel.Name :=
    (bindings.reverse ++ mappings.reverse).foldl (fun m (k, v) => m.insert k v) {}
  let names : Kernel.Name → Kernel.Name := fun n => table.getD n n
  let targetNames : Std.HashSet Kernel.Name :=
    target.consts.foldl (fun s e => s.insert e.name) {}
  let mut support : Array Kernel.Declaration := #[]
  for declaration in installed.declarations do
    let declared := declaration.names
    if declared.all (fun n => targetNames.contains (names n)) then continue
    -- an axiom the source fold installs no row for has no source row to pull back, so it
    -- needs no support: `sorryAx`, whose record the checker skips on both sides (any use of
    -- it declines). Every other axiom the fold accepts is pinned and installed under its
    -- pinned name on both sides; a support axiom row would be refused by the support fold
    -- (non-standard axiom). Untrusted: the decision checks every installed source row.
    if let .axiomDecl cv := declaration then
      if (installed.env.find? cv.name).isNone then continue
    match declaration with
    | .basisDecl _ => throw s!"basis declaration {declared} has no target row"
    | _ => support := support.push (← (proposeRenamedSupport names declaration).mapError
        (fun e => s!"{e}: {declared.map leanNameOf}"))
  let never : Kernel.Name → Kernel.Name := fun n => n.str "_ix_no_value_certificate"
  return { names, support, certificates := never, operationCertificates := never,
           elementCertificates := never, levels := fun _ => .succ .zero }

/-- Names, support and receipt names for one cone of W's association. Nothing here is trusted:
`decideStrongCone` checks every part. -/
def propose {input : Input} (accepted : AcceptedAssociation input)
    (installed : SourceNormalizedInstallation input.source input.roots) :
    Except String StrongProposal :=
  proposeWith accepted.pins noImages accepted.env installed

/-! ## Diagnosis of a refused strong check (untrusted) -/

/-- The per-row comparison of `checkInstalledComparisonAvailability`, evaluated
row by row to name the first row it does not accept (`none`: no comparison,
`some false`: refused). -/
def availabilityRow (fS fT : Lookup) (names : Kernel.Name → Kernel.Name)
    (entry : Kernel.ConstantInfo) : Option Bool := do
  let some targetEntry := fT (names entry.name) | return false
  let typeResult ← checkInstalledMemberExprF fS fT names entry.name
    entry.toConstantVal.type targetEntry.toConstantVal.type
  if !typeResult then return false
  match entry, targetEntry with
  | .defnInfo header value _, .defnInfo _ targetValue _ =>
    checkInstalledMemberExprF fS fT names header.name value targetValue
  | .recInfo header _ _ rules, .recInfo _ _ _ targetRules =>
    checkInstalledRulesF fS fT names header.name rules targetRules
  | .indInfo header caps, .indInfo _ targetCaps =>
    checkInstalledMemberExprF fS fT names header.name
      (capabilityDatumExpr caps) (capabilityDatumExpr targetCaps)
  | _, _ => return true

def kindOf : Kernel.ConstantInfo → String
  | .defnInfo .. => "definition" | .thmInfo .. => "theorem" | .recInfo .. => "recursor"
  | .indInfo .. => "inductive" | .ctorInfo .. => "constructor" | .axiomInfo .. => "axiom"
  | .projInfo .. => "projection table"

/-- Which part of the strong check refuses, and on which row when it is a row
check: `(family, row?, unavailable)`. -/
def diagnoseStrong {input : Input} (accepted : AcceptedAssociation input)
    (installed : SourceNormalizedInstallation input.source input.roots) (target : Kernel.Env)
    (names : Kernel.Name → Kernel.Name) : String × Option Kernel.Name × Bool := Id.run do
  let source := installed.env
  let fS := envFind source
  let fT := envFind target
  if !decide (SemanticNamesAgree accepted names) then return ("names: semantic name map", none, false)
  for entry in source.consts do
    match availabilityRow fS fT names entry with
    | some true => pure ()
    | some false =>
      let why := if (fT (names entry.name)).isNone then "no target row" else "refused"
      return (s!"comparison ({kindOf entry}): {why}", some entry.name, false)
    | none => return (s!"comparison ({kindOf entry}): unavailable (let, free variable or level)",
        some entry.name, true)
  let checks : List (String × Option Bool) := [
    ("telescopes", some (checkTelescopes source target names)),
    ("types", some (checkInstalledTypes source target names)),
    ("definitions", some (checkInstalledDefinitions source target names)),
    ("False pin", some (checkInstalledPin source names Kernel.falseName 0)),
    ("Eq pin", some (checkInstalledPin source names Kernel.eqName 1)),
    ("capabilities", some (checkInstalledCapabilities source target names)),
    ("recursors", some (checkInstalledRecursors source target names)),
    ("constructors", some (checkInstalledConstructors source target names)),
    ("eta associations", checkInstalledEtaAssociations source target names),
    ("rule level links", checkInstalledRuleLevelLinks source target names),
    ("reserved names", some (checkReservedNameMap source names)),
    ("type literal support", some (checkTypeLiteralSupport source target)),
    ("definition literal support", some (checkDefinitionLiteralSupport source target)),
    ("projection towers", checkInstalledTowers source target names)]
  for (family, result) in checks do
    match result with
    | some true => pure ()
    | some false =>
      if family == "eta associations" then
        for entry in source.consts do
          if let .indInfo header caps := entry then
            unless checkInstalledEtaEntry source target names entry == some true do
              let part :=
                if !checkInstalledEtaAt target (names header.name) then
                  match target.find? (names header.name) with
                  | some (.indInfo _ tcaps) =>
                    let missing := (List.range tcaps.etaFields).filter fun i =>
                      match target.find? (Kernel.projFnName (names header.name) i) with
                      | some (.recInfo ..) => false
                      | _ => true
                    s!"target eta family incomplete (projections {missing} not stored)"
                  | _ => "target eta family row"
                else if checkInstalledFamilyMember source target names header.name caps.etaCtor != some true then
                  "eta constructor"
                else "eta projection"
              return (s!"{family}: {part}", some header.name, false)
      return (family, none, false)
    | none => return (s!"{family}: unavailable", none, true)
  return ("Nat/DivMod/reduce receipts", none, false)

/-! ## One cone -/

inductive ConeOutcome where
  /-- Accepted: every member of the cone's source is S-Certified. -/
  | certified (members : Array Lean.Name)
  /-- Not accepted: the class, the responsible member (if known), and whether
  the cause is an unsupported construct rather than a refusal. -/
  | failed (cls : String) (culprit : Option Lean.Name) (unsupported : Bool)
  deriving Inhabited

structure ConeStats where
  members : Nat := 0
  records : Nat := 0
  support : Nat := 0
  witnesses : Nat := 0
  msInput : Nat := 0
  msAdmit : Nat := 0
  msW : Nat := 0
  msInstall : Nat := 0
  msStrong : Nat := 0
  deriving Inhabited

/-- A target name, or its nearest prefix, in a map from target names (diagnostics and triage). -/
def findTarget (m : Std.HashMap Kernel.Name Lean.Name) : Nat → Kernel.Name → Option Lean.Name
  | 0, _ => none
  | fuel + 1, k => match m[k]? with
    | some n => some n
    | none => match k with
      | .str p _ | .num p _ => findTarget m fuel p
      | .anonymous => none

/-- The eight pin-certified Nat operations, by their Lean names. -/
def natOpLeanNames : Array Lean.Name :=
  #[`Nat.div, `Nat.mod, `Nat.gcd, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight]

/-- Per pin-certified Nat operation (by Lean name), what a cone containing it also takes
(untrusted, `coneMembers`): the Lean names of the target names its builtin pins and
certificates mention (the records the target fold needs; any member of an alias fiber:
the members share a record), and the Lean declarations its source-named pins and
certificates name (`SourcePinGen.groundOf`: the declarations the source fold needs
installed when it meets the operation). `names` are the candidates, `certified` those a
cone may contain. -/
def natOpPinGround (env : Lean.Environment) (store : RecordStore)
    (namedAddr : Std.HashMap Lean.Name Address) (readerPins : Kernel.Reader.Pins)
    (names : Array Lean.Name) (certified : Lean.Name → Bool) :
    Std.HashMap Lean.Name (Array Lean.Name) := Id.run do
  let targetToLean : Std.HashMap Kernel.Name Lean.Name := names.foldl (fun m n =>
    if !certified n then m else
    match namedAddr[n]? with
    | some a => match Kernel.Reader.resolve (store[·]?) a with
      | some r =>
        let k := readerPins.names.getD r (Kernel.Reader.keyName r)
        if m.contains k then m else m.insert k n
      | none => m
    | none => m) {}
  let mut out : Std.HashMap Lean.Name (Array Lean.Name) := {}
  for (op, opK, _) in SourcePinGen.certSpecs do
    let mut ground : Std.HashSet Lean.Name := {}
    for ps in Kernel.Reader.builtinNatOpPins.toOption.getD [] do
      for e in Kernel.divModDeclPin ps opK :: Kernel.divModCertProofs ps opK do
        for (_, c) in exprConsts e do
          if let some n := findTarget targetToLean 8 c then ground := ground.insert n
    for ps in SourcePinGen.sourceNatOpPinSets do
      for n in SourcePinGen.groundOf env.find? ps opK do
        ground := ground.insert n
    out := out.insert op ((ground.erase op).toArray.qsort (fun a b => toString a < toString b))
  return out

/-- A cone's members with `Eq`'s block first. The checker installs the quotient block
only over the pinned `Eq` basis (`checkBasisDecl .quotK`, `IxC/Kernel/Checker.lean`), and
the source fold installs Lean's `Eq` as that basis (`basisPinHit`) where it meets it. `Eq`
and `Quot` are both declaration groups without dependencies, which the source order
(`orderSourceGroups`) keeps in the cone's order, so `Eq` listed first is installed before
`Quot`. Untrusted: the order of the cone's source, nothing else. -/
def eqFirst (members : Array Lean.Name) : Array Lean.Name :=
  let basis := #[`Eq, `Eq.refl, `Eq.rec].filter members.contains
  if basis.isEmpty then members else basis ++ members.filter (!basis.contains ·)

/-- A cone (untrusted): the closure of `roots` under `refs` within `known`, closed under two
additions, to a fixpoint: the certificate ground of every pin-certified Nat operation it
contains (`ground`: the records its pins need on the target side and the declarations its
source pins name), and `Eq` when it contains `Quot`; members in `eqFirst` order. Returns
the members and the references outside `known`. -/
def coneMembersOf (refs : Std.HashMap Lean.Name (Array Lean.Name)) (known : Lean.Name → Bool)
    (ground : Std.HashMap Lean.Name (Array Lean.Name)) (roots : Array Lean.Name) :
    Array Lean.Name × Array Lean.Name := Id.run do
  let mut seeds : Array Lean.Name := roots
  let mut result := coneOf refs known seeds
  for _ in [0:8] do
    let present : Std.HashSet Lean.Name := result.1.foldl (·.insert ·) {}
    let mut extra : Array Lean.Name := #[]
    for op in natOpLeanNames do
      if present.contains op then
        for g in ground.getD op #[] do
          unless present.contains g || extra.contains g do extra := extra.push g
    if present.contains `Quot && !present.contains `Eq && !extra.contains `Eq then
      extra := extra.push `Eq
    if extra.isEmpty then break
    seeds := seeds ++ extra
    result := coneOf refs known seeds
  return (eqFirst result.1, result.2)

/-- A root's cone (`coneMembersOf` of the root alone). -/
def coneMembers (refs : Std.HashMap Lean.Name (Array Lean.Name)) (known : Lean.Name → Bool)
    (ground : Std.HashMap Lean.Name (Array Lean.Name)) (root : Lean.Name) :
    Array Lean.Name × Array Lean.Name :=
  coneMembersOf refs known ground #[root]

/-- A last name component Lean gives to an auxiliary declaration that belongs to the
declaration it hangs under: generated lemmas and proofs (`_simp_1`, `_proof_1`, `eq_1`,
`eq_def`, `congr_simp`, `sizeOf_spec`, `injEq`, …), defaults, unfolding and structural helpers
(`_sunfold`, `_default`, `match_1`, `recOn`, `casesOn`, …). -/
def auxiliarySuffix (s : String) : Bool :=
  s.startsWith "_" || s.startsWith "eq_" || s.startsWith "match_" ||
    ["congr_simp", "sizeOf_spec", "injEq", "inj", "recOn", "casesOn", "below", "brecOn",
      "noConfusion", "noConfusionType", "ctorIdx", "induct", "fun_cases", "splitter"].contains s

/-- The batch group of a root (`coverBatches`): the namespace of the declaration it belongs
to. An auxiliary declaration (`f._simp_1`, `f.eq_1`, `f.congr_simp`, …) is grouped with `f`'s
siblings, not alone under `f` (on Init+Std most roots nothing uses that ran alone in a cone of
1,000 or more declarations were such auxiliaries). -/
def batchGroup : Lean.Name → Lean.Name
  | n@(.str p s) => if auxiliarySuffix s then batchGroup p else n.getPrefix
  | .num p _ => batchGroup p
  | .anonymous => .anonymous

/-- Batches of a cover's roots (untrusted orchestration). Each root nothing uses needs a
cone of its own, and the cost of a cone grows faster than its size (on Init+Std the strong
check about as size^2.5, and every cone that reaches the `String`/`TreeMap` lemma core pays
for it again), so roots whose cones overlap are decided as **one cone whose source is the
union of theirs**: the decision then S-certifies every member at once (the S conclusion holds
for any closed source; nothing about the verdict's meaning changes). `order` are the roots
nothing uses in the cover's order (largest cone first); they are grouped by the namespace of
the declaration they belong to (`batchGroup`); in each group a leader takes, from the next
`window` roots of its group not yet taken, those whose cones keep the union within 3/2 of
the leader's cone (plus 16), at most `maxRoots` roots per batch (the cover passes 128 and
256). On Init+Std-a3 before W+ (every constant W-certified by the direct route) this planned
3,939 cones where namespace groups with 32 and 64 and 5/4 planned 11,905; with W+ (12 constants
outside S, 15 blocked by them) it plans 3,952. Returns, per leader, the other roots of its batch. -/
def coverBatches (refs : Std.HashMap Lean.Name (Array Lean.Name)) (known : Lean.Name → Bool)
    (order : Array Lean.Name) (window maxRoots : Nat) : Std.HashMap Lean.Name (Array Lean.Name) := Id.run do
  let mut groups : Std.HashMap Lean.Name (Array Lean.Name) := {}
  let mut prefixes : Array Lean.Name := #[]
  for n in order do
    let p := batchGroup n
    match groups[p]? with
    | some g => groups := groups.insert p (g.push n)
    | none =>
      groups := groups.insert p #[n]
      prefixes := prefixes.push p
  let mut out : Std.HashMap Lean.Name (Array Lean.Name) := {}
  for p in prefixes do
    let group := groups.getD p #[]
    if group.size < 2 then continue
    let closures := group.map fun n => coneOf refs known #[n]
    let cones : Array (Array Lean.Name) := closures.map (·.1)
    -- a root whose cone reaches a constant outside `known` (one W certifies by a W+ route, say)
    -- cannot run a cone: it is never batched, so it cannot dissolve a batch of roots that can
    let mut taken : Array Bool := closures.map fun c => !c.2.isEmpty
    for i in [0:group.size] do
      if taken[i]! then continue
      let lead := cones[i]!
      let limit := lead.size * 3 / 2 + 16
      let mut union : Std.HashSet Lean.Name := lead.foldl (·.insert ·) {}
      let mut batch : Array Lean.Name := #[]
      let mut looked := 0
      let mut j := i + 1
      while j < group.size && looked < window && batch.size + 1 < maxRoots do
        if !taken[j]! then
          looked := looked + 1
          let extra := cones[j]!.filter (!union.contains ·)
          if union.size + extra.size ≤ limit then
            union := extra.foldl (·.insert ·) union
            batch := batch.push group[j]!
            taken := taken.set! j true
        j := j + 1
      if !batch.isEmpty then out := out.insert group[i]! batch
  return out

/-- The **global cone** (M7 WP-F, untrusted orchestration): every constant of `names` in
`known` whose closure under `refs` stays in `known`, in `names` order with `Eq`'s block first
(`eqFirst`). The constants of `known` left out are those that reach, through constants of
`known`, a reference outside it; each is returned with that reference (its blocking constant).
The global cone is closed, so it is one cone's source; nothing about the meaning of a verdict
depends on this choice. -/
def globalConeMembers (names : Array Lean.Name) (refs : Std.HashMap Lean.Name (Array Lean.Name))
    (known : Lean.Name → Bool) : Array Lean.Name × Std.HashMap Lean.Name Lean.Name := Id.run do
  let mut users : Std.HashMap Lean.Name (Array Lean.Name) := {}
  let mut todo : Array (Lean.Name × Lean.Name) := #[]
  for n in names do
    if known n then
      for r in refs.getD n #[] do
        if r != n then users := pushUser users r n
        if !known r then todo := todo.push (n, r)
  let mut blocked : Std.HashMap Lean.Name Lean.Name := {}
  while h : todo.size > 0 do
    let (n, cause) := todo[todo.size - 1]
    todo := todo.pop
    if blocked.contains n then continue
    blocked := blocked.insert n cause
    for u in users.getD n #[] do
      unless blocked.contains u do todo := todo.push (u, cause)
  let members := names.filter fun n => known n && !blocked.contains n
  return (eqFirst members, blocked)

/-- The longest prefix of a name that is a source declaration. -/
def knownPrefix (source : Source) : Lean.Name → Option Lean.Name
  | .anonymous => none
  | n@(.str p _) => if (source.find n).isSome then some n else knownPrefix source p
  | n@(.num p _) => if (source.find n).isSome then some n else knownPrefix source p

/-- The Lean name of the declaration at a position of the source fold's stream
(recomputed for a diagnostic: export, model proposal, normalisation, basis
completion; a generated helper is named by its source prefix). -/
def foldDeclarationAt (source : Source) (witnesses : LoweringWitnesses) (position : Nat) : Option Lean.Name := do
  let original ← (exportSourceDeclarations source).toOption
  let proposal ← (proposeSourceModels source original).toOption
  let output ← (normalizeSourceProjections source witnesses {} proposal.declarations.toList).toOption
  let declarations := (completeSourceSemanticBasis output.val).declarations
  let declaration ← declarations[position]?
  let name ← declaration.names.head?
  knownPrefix source (leanNameOf name)

def sourceErrorLabel : SourceModelError → String × Bool
  | .incomplete => ("source installation: incomplete source", false)
  | .exportFailure why =>
    (s!"source installation: export: {(why.splitOn ":").headD why}", (why.splitOn "unsupported").length > 1)
  | .proposalFailure why => (s!"source installation: model proposal: {(why.splitOn ":").headD why}", false)
  | .changedOriginal => ("source installation: original stream changed", false)
  | .correspondence => ("source installation: entry correspondence", false)
  | .supportMismatch => ("source installation: basis support", false)
  | .checking (.notImplemented what) _ => (s!"source fold: not implemented: {what}", true)
  | .checking error _ => (s!"source fold: {(toString error).take 120}", false)

def supportLabel : SupportError → String
  | .conflictingNames => "support: names not fresh"
  | .setup r => s!"support: setup: {r}"
  | .checking e _ => s!"support fold: {(toString e).take 120}"
  | .changedOriginal => "support: original rows changed"

/-- The position-hint queries of a cone's W association (`buildHints`): a name, and for an
inductive its block's members, recursors, nested recursors and constructors, with the
references of all of them and their prefixes. -/
def hintQueries (env : Lean.Environment) (n : Lean.Name) : Array Lean.Name := Id.run do
  let some ci := env.find? n | return #[n]
  let mut out : Array Lean.Name := #[n]
  match ci with
  | .inductInfo v =>
    for m in v.all do
      out := out.push m |>.push (m.str "rec")
      if let some (.inductInfo iv) := env.find? m then out := out ++ iv.ctors.toArray
    for i in [0:v.numNested] do
      if let some h := v.all.head? then out := out.push (h.str s!"rec_{i + 1}")
  | _ => pure ()
  let mut all := out
  for d in out do
    if let some dci := env.find? d then
      for r in refsOf dci do all := all.push r |>.push r.getPrefix
  return all

/-- Decide S on one cone. `witnesses` is the cone's list of Lean-kernel-checked
lowering theorems (computed in `IO` by the caller). -/
def runCone (env : Lean.Environment) (produced : Ixon.Env) (store : RecordStore)
    (namedAddr : Std.HashMap Lean.Name Address) (workers : Nat)
    (root : Lean.Name) (members : Array Lean.Name) (witnesses : LoweringWitnesses) :
    IO (ConeOutcome × ConeStats) := do
  let mut stats : ConeStats := { members := members.size, witnesses := witnesses.length }
  -- each stage is forced in its own action (`IO.lazyPure`), so the clock reads between them
  let stage {α : Type} (f : Unit → α) : IO (α × Nat) := do
    let t ← IO.monoMsNow
    let a ← IO.lazyPure f
    return (a, (← IO.monoMsNow) - t)
  let (input?, ms) ← stage fun _ => coneInput env produced store namedAddr [root] members
  stats := { stats with msInput := ms }
  let input ← match input? with
    | .ok i => pure i
    | .error why => return (.failed s!"cone input: {(why.splitOn " ").take 3 |> " ".intercalate}" (some root) false, stats)
  stats := { stats with records := input.records.length }
  let (artifact?, ms) ← stage fun _ => prepareArtifact input.toArtifactInput
  stats := { stats with msAdmit := ms }
  let artifact ← match artifact? with
    | .ok a => pure a
    | .error _ => return (.failed "cone admission refused" (some root) false, stats)
  let (accepted?, ms) ← stage fun _ =>
    checkIndexed input artifact (buildHints input (Shared.ofArtifact input artifact) (hintQueries env) workers)
  stats := { stats with msW := ms }
  let accepted ← match accepted? with
    | .ok a => pure a
    | .error _ => return (.failed "cone W association refused" (some root) false, stats)
  let (installed?, ms) ← stage fun _ =>
    installSourceNormalizedComplete accepted.domain.1 (sourcePins input accepted.pins) witnesses
  stats := { stats with msInstall := ms }
  let installed ← match installed? with
    | .ok i => pure i
    | .error e =>
      let (cls, unsupported) := sourceErrorLabel e
      let culprit := match e with
        | .checking _ position => (foldDeclarationAt input.source witnesses position).getD root
        | _ => root
      return (.failed cls (some culprit) unsupported, stats)
  let proposal ← match propose accepted installed with
    | .ok p => pure p
    -- the proposal generators cover definitions, theorems and opaques (and the basis): a cone
    -- needing support of another kind is outside what the certifier proposes (unsupported)
    | .error why => return (.failed s!"proposal: {(why.splitOn ":").headD why}" (some root) true, stats)
  stats := { stats with support := proposal.support.size }
  let (decided, ms) ← stage fun _ => decideStrongCone accepted installed proposal
  stats := { stats with msStrong := ms }
  match decided with
  | .ok _cone =>
    -- `StrongCone.sound` holds for `_cone`: every member of `input.source` is S-Certified.
    return (.certified (input.source.declarations.toArray.map (·.name)), stats)
  | .error (.support e) => return (.failed (supportLabel e) (some root) false, stats)
  | .error (.strong _) =>
    let target := match admitSupport accepted.toAdmittedArtifact proposal.support with
      | .ok bundle => bundle.env
      | .error _ => accepted.env
    let (family, row, unavailable) := diagnoseStrong accepted installed target proposal.names
    return (.failed s!"strong check: {family}" (row.map leanNameOf) unavailable, stats)

/-! ## Value-level cones (M7 S+a; untrusted orchestration)

A constant W certifies by a W+ route outside a changed inductive block (a theorem by its
statement, a definition by a value row) and the constants that use it are decided by
`decideStrongCone'` (`StrongChanged.lean`): the cone's W association is W+'s
(`checkIndexed'`, with the rows of the cone's members as support, folded once by the certified
checker), and the conclusion is `StrongCone'.sound`, at the value level. -/

/-- The S class of a W+-route constant over a changed inductive block (a member of a changed
block, an image recursor, a header matched through a type row): decided by S+b, not here. -/
def changedBlockClass : String :=
  "certified by a W+ route over a changed inductive block (a member, an image recursor or a type row); S for it is S+b"

/-- The S class of a transported clique member W certifies by Lean's `eq_def` only: an unfolding
equation does not determine a value in an existence-only model; its value row is package V's. -/
def valueRowClass : String :=
  "transported clique member certified by its eq_def only (no value row); S for it needs package V"

/-- The value-level class of a constant W certifies by the W+ route `route`, or `none` when
value-level S decides it: a theorem by the `theorem` route, a definition by an `equations:`
route with a value row (W+'s `rfl` rows, package V's value rows), no type row, no changed
block. -/
def valueClassOf (env : Lean.Environment) (n : Lean.Name) (route : String) : Option String :=
  if (route.splitOn "changed-block").length > 1 || (route.splitOn "type-row").length > 1 then
    some changedBlockClass
  else if route.startsWith "equations:eq_def" then some valueRowClass
  else match env.find? n with
    | some (.recInfo _) => some changedBlockClass
    | some (.thmInfo _) => if route == "theorem" then none else some s!"W+ route {route} of a theorem"
    | some (.defnInfo _) => if route.startsWith "equations:" then none else some s!"W+ route {route} of a definition"
    | _ => some s!"W+ route {route}"

/-- The class of a refused W+ association of a value cone: the support fold's refusal (with the
checker's word), or the association's own decline. -/
def changedDeclineLabel : Decline' → String
  | .fold (.checking error _) => s!"cone W+ support fold refused: {(checkOutcome error).1}: {((checkOutcome error).2.take 100)}"
  | .fold (.setup reason) => s!"cone W+ support fold: setup: {reason}"
  | .base _ => "cone W+ association refused"

/-- The W+ rows of a cone's members (the global pre-pass's support rows, uniquely named), in
member order, with each member's row indices into them. -/
def coneRows (w : WState) (members : Array Lean.Name) :
    Array Kernel.Declaration × Std.HashMap Lean.Name (Array Nat) := Id.run do
  let mut rows : Array Kernel.Declaration := #[]
  let mut rowsFinal : Std.HashMap Lean.Name (Array Nat) := {}
  for n in members do
    if let some idx := w.rowsOf[n]? then
      let start := rows.size
      for i in idx do
        if let some row := w.support[i]? then rows := rows.push row
      rowsFinal := rowsFinal.insert n ((List.range (rows.size - start)).toArray.map (start + ·))
  return (rows, rowsFinal)

/-- The row proposed for each target definition: a support theorem whose statement is
`@Eq T c r` with `c` the definition's constant, by the target name of `c` (the first such
row; untrusted: the decision reads the row's installed statement and compares its right side
with the source value). -/
def rowHints (rows : Array Kernel.Declaration) : Std.HashMap Kernel.Name Kernel.Name :=
  rows.foldl (fun m d => match d with
    | .thmDecl cv _ => match eqParts cv.type with
      | some (_, _, .const t _, _) => if m.contains t then m else m.insert t cv.name
      | _ => m
    | _ => m) {}

/-- The Lean constants the W+ rows of each constant mention (statements and proofs). A value cone
takes them, so that its records hold what its members' rows need: a certifier-generated value
row's proof cites `WellFounded.fix_eq`, `funext`, … which the member's own dependencies need not
reach. Target names are resolved to Lean names through the given constants' records (the first
Lean name of a record wins); a name with no Lean counterpart (a canonical `_ix` constant) is
reached through the references of its user's record. Untrusted: it only adds members to a cone. -/
def rowGround (w : WState) (readerPins : Kernel.Reader.Pins) (known : Lean.Name → Bool) :
    Std.HashMap Lean.Name (Array Lean.Name) := Id.run do
  let targetToLean : Std.HashMap Kernel.Name Lean.Name := w.names.foldl (fun m n =>
    if !known n then m else
    match w.namedAddr[n]? with
    | some a => match Kernel.Reader.resolve (w.store[·]?) a with
      | some r =>
        let k := readerPins.names.getD r (Kernel.Reader.keyName r)
        if m.contains k then m else m.insert k n
      | none => m
    | none => m) {}
  let mut out : Std.HashMap Lean.Name (Array Lean.Name) := {}
  for (owner, idx) in w.rowsOf.toList do
    let mut ground : Std.HashSet Lean.Name := {}
    for i in idx do
      if let some (.thmDecl cv proof) := w.support[i]? then
        for (_, c) in exprConsts cv.type ++ exprConsts proof do
          if let some n := targetToLean[c]? then
            if n != owner then ground := ground.insert n
    unless ground.isEmpty do
      out := out.insert owner (ground.toArray.qsort (fun a b => toString a < toString b))
  return out

/-- Which part of the value-level check refuses, and on which source row (diagnostics). -/
def diagnoseChanged (source target : Kernel.Env) (names rows : Kernel.Name → Kernel.Name) :
    String × Option Kernel.Name := Id.run do
  let fS := envFind source
  let fT := envFind target
  for entry in source.consts do
    match fT (names entry.name) with
    | none => return ("no target row", some entry.name)
    | some targetEntry =>
      unless decide (TelescopeEntry entry targetEntry) do return ("telescopes", some entry.name)
      unless checkInstalledMemberExprF fS fT names entry.name entry.toConstantVal.type
          targetEntry.toConstantVal.type == some true do
        return (s!"types ({kindOf entry})", some entry.name)
      if let .defnInfo header value _ := entry then
        let direct := match targetEntry with
          | .defnInfo _ targetValue _ =>
            checkInstalledMemberExprF fS fT names header.name value targetValue == some true
          | _ => false
        unless direct || definitionRowF fS fT names rows header.name value do
          let why := match fT (rows header.name) with
            | some (.thmInfo ..) => "definitions: the value differs and the proposed row does not state it"
            | _ => "definitions: the value differs and no theorem row is proposed"
          return (why, some header.name)
  let checks : List (String × Bool) := [
    ("False pin", checkInstalledPin source names Kernel.falseName 0),
    ("Eq pin", checkInstalledPin source names Kernel.eqName 1),
    ("capabilities", checkInstalledCapabilitiesF source fS fT names),
    ("recursors", checkInstalledRecursorsF source fS fT names),
    ("constructors", checkInstalledConstructorsF source fS fT names),
    ("eta associations", checkInstalledEtaAssociationsF source fS fT names == some true),
    ("rule level links", checkInstalledRuleLevelLinksF source fS fT names == some true)]
  for (family, ok) in checks do
    unless ok do return (family, none)
  return ("unexplained", none)

/-- The decision on one value-level cone and, when it refuses, the diagnosis. -/
def decideChanged {input : Input} {images : Lean.Name → Bool} {support : Array Kernel.Declaration}
    (accepted : AcceptedAssociation' input images support)
    (installed : SourceNormalizedInstallation input.source input.roots) (proposal : StrongProposal')
    (root : Lean.Name) : ConeOutcome :=
  match decideStrongCone' accepted installed proposal with
  | .ok _cone =>
    -- `StrongCone'.sound` holds for `_cone`: every member of `input.source` is S-Certified at
    -- the value level.
    .certified (input.source.declarations.toArray.map (·.name))
  | .error .names => .failed "value check: the name map against W+'s" (some root) false
  | .error .check =>
    let (family, row) := diagnoseChanged installed.env accepted.folded.env proposal.names proposal.rows
    .failed s!"value check: {family}" (some ((row.map leanNameOf).getD root)) false

/-- Decide value-level S on one cone (M7 S+a): its input, its admission (staged, so W+'s fold
of the rows continues it), W+'s association with the rows of its members (`checkIndexed'`), the
normalised source installation, the proposal (names, source-owned support, row names) and
`decideStrongCone'`. Source-owned support, when the cone needs any, is folded with the rows
(W+'s association decided again on rows and support). -/
def runConeChanged (w : WState) (workers : Nat) (root : Lean.Name) (members : Array Lean.Name)
    (witnesses : LoweringWitnesses) : IO (ConeOutcome × ConeStats) := do
  let mut stats : ConeStats := { members := members.size, witnesses := witnesses.length }
  let stage {α : Type} (f : Unit → α) : IO (α × Nat) := do
    let t ← IO.monoMsNow
    let a ← IO.lazyPure f
    return (a, (← IO.monoMsNow) - t)
  let (input?, ms) ← stage fun _ => coneInput w.env w.produced w.store w.namedAddr [root] members
  stats := { stats with msInput := ms }
  let input ← match input? with
    | .ok i => pure i
    | .error why => return (.failed s!"cone input: {(why.splitOn " ").take 3 |> " ".intercalate}" (some root) false, stats)
  stats := { stats with records := input.records.length }
  let (admitted?, ms) ← stage fun _ => prepareArtifactStaged input.toArtifactInput
  stats := { stats with msAdmit := ms }
  let ⟨artifact, staged⟩ ← match admitted? with
    | .ok a => pure a
    | .error _ => return (.failed "cone admission refused" (some root) false, stats)
  let imagesFn : Lean.Name → Bool := fun n => w.images.contains n
  let (rows, rowsFinal) := coneRows w members
  let coneEntries : Std.HashMap Lean.Name MapEntry := input.map.foldl (fun m e => m.insert e.source e) {}
  let queries := queriesFor w.env w.refs
  let association (support : Array Kernel.Declaration) :=
    let sh := SharedW.ofArtifact input imagesFn artifact support
    let entryPos := entryPositions sh.entries
    let hints := buildHintsW input sh entryPos queries workers
      (rowsAtWith coneEntries entryPos sh.reader rowsFinal sh.entries.size)
    checkIndexed' input imagesFn artifact support hints staged
  let (accepted?, ms) ← stage fun _ => association rows
  stats := { stats with msW := ms }
  let accepted ← match accepted? with
    | .ok a => pure a
    | .error e => return (.failed (changedDeclineLabel e) (some root) false, stats)
  let (installed?, ms) ← stage fun _ =>
    installSourceNormalizedComplete accepted.domain.1 (sourcePins input accepted.pins) witnesses
  stats := { stats with msInstall := ms }
  let installed ← match installed? with
    | .ok i => pure i
    | .error e =>
      let (cls, unsupported) := sourceErrorLabel e
      let culprit := match e with
        | .checking _ position => (foldDeclarationAt input.source witnesses position).getD root
        | _ => root
      return (.failed cls (some culprit) unsupported, stats)
  let proposal ← match proposeWith accepted.pins imagesFn accepted.env installed with
    | .ok p => pure p
    | .error why => return (.failed s!"proposal: {(why.splitOn ":").headD why}" (some root) true, stats)
  stats := { stats with support := proposal.support.size }
  let hints := rowHints rows
  let proposal' : StrongProposal' :=
    { names := proposal.names, rows := fun n => hints.getD (proposal.names n) (n.str "_ix_no_row") }
  if proposal.support.isEmpty then
    let (outcome, ms) ← stage fun _ => decideChanged accepted installed proposal' root
    stats := { stats with msStrong := ms }
    return (outcome, stats)
  else
    let (accepted2?, ms) ← stage fun _ => association (rows ++ proposal.support)
    stats := { stats with msW := stats.msW + ms }
    match accepted2? with
    | .error e => return (.failed s!"{changedDeclineLabel e} (with the source-owned support)" (some root) false, stats)
    | .ok accepted2 =>
      let (outcome, ms) ← stage fun _ => decideChanged accepted2 installed proposal' root
      stats := { stats with msStrong := ms }
      return (outcome, stats)

/-- The number of rounds `orderSourceGroups` takes on `groups` (diagnostics only: the depth of
the source's dependency order, computed with a hash set of the available names). -/
def orderRounds (groups : List SourceDeclGroup) : Nat := Id.run do
  let mut available : Std.HashSet Lean.Name := {}
  let mut pending := groups
  let mut rounds := 0
  for _ in [0:groups.length + 1] do
    if pending.isEmpty then break
    let ready := pending.filter fun g => g.dependencies.all available.contains
    if ready.isEmpty then break
    pending := pending.filter fun g => !g.dependencies.all available.contains
    available := ready.foldl (fun s g => g.members.foldl (·.insert ·) s) available
    rounds := rounds + 1
  return rounds

/-- The stages of one cone's decision, each forced and timed on its own (diagnostics,
`--explain`): the cone's input, its admission, the W association's hints and check, the source
installation (export, model proposal, the two decided preservation facts, normalisation, the
whole installation, the fold alone), the proposal, the support, and every family of the strong
check, with a baseline of the strong check's list lookups (one `Kernel.Env.find?` per source
row). Nothing here decides a verdict. -/
def explainCone (env : Lean.Environment) (produced : Ixon.Env) (store : RecordStore)
    (namedAddr : Std.HashMap Lean.Name Address) (root : Lean.Name) (members : Array Lean.Name)
    (witnesses : LoweringWitnesses) : IO Unit := do
  let time {α : Type} (label : String) (f : Unit → α) (show_ : α → String) : IO α := do
    let t ← IO.monoMsNow
    let a ← IO.lazyPure f
    say s!"[explain-S] {root}: stage {label}: {show_ a}; {(← IO.monoMsNow) - t} ms"
    return a
  let flag : Bool → String := fun b => if b then "true" else "false"
  let opt : Option Bool → String := fun | some b => flag b | none => "unavailable"
  let input? ← time "cone input" (fun _ => coneInput env produced store namedAddr [root] members)
    (fun | .ok i => s!"{i.source.declarations.length} declarations, {i.records.length} records" | .error e => e)
  let .ok input := input? | return
  let artifact? ← time "admission" (fun _ => prepareArtifact input.toArtifactInput)
    (fun | .ok a => s!"{a.declarations.size} declarations" | .error _ => "refused")
  let .ok artifact := artifact? | return
  let hints ← time "W hints" (fun _ => buildHints input (Shared.ofArtifact input artifact) (hintQueries env) 1)
    (fun _ => "built")
  let accepted? ← time "W association" (fun _ => checkIndexed input artifact hints)
    (fun | .ok _ => "accepted" | .error _ => "refused")
  let .ok accepted := accepted? | return
  -- the export's parts, each timed on its own (diagnostics only)
  let built? ← time "source export: groups built" (fun _ => buildSourceGroupsF input.source)
    (fun | .ok g => s!"{g.length} groups, {(g.map (·.dependencies.length)).foldl (· + ·) 0} dependencies" | .error e => e)
  if let .ok built := built? then
    let _ ← time "source export: groups validated" (fun _ => validateSourceGroupsF input.source built)
      (fun | .ok _ => "covered" | .error e => e)
    let _ ← time "source export: groups ordered" (fun _ => orderF (built.length + 1) built {} [])
      (fun | .ok o => s!"{o.length} declarations" | .error e => e)
    let _ ← time "source export: rounds of the order (hash set)" (fun _ => orderRounds built) toString
    let _ ← time "source export: entries alone (exportSourceEntry, all members)"
      (fun _ => input.source.declarations.foldl (fun n ci => if (exportSourceEntry ci).toOption.isSome then n + 1 else n) 0)
      toString
  let original? ← time "source export" (fun _ => exportSourceDeclarations input.source)
    (fun | .ok o => s!"{o.size} declarations" | .error e => e)
  let .ok original := original? | return
  let proposal? ← time "model proposal" (fun _ => proposeSourceModels input.source original)
    (fun | .ok p => s!"{p.declarations.size} declarations" | .error e => e)
  let .ok modelProposal := proposal? | return
  let _ ← time "original preserved (sublist)"
    (fun _ => decide (original.toList.Sublist modelProposal.declarations.toList)) flag
  let _ ← time "entry correspondence"
    (fun _ => decide (SourceEntryCorrespondence input.source modelProposal.declarations)) flag
  let _ ← time "projection normalisation"
    (fun _ => normalizeSourceProjections input.source witnesses {} modelProposal.declarations.toList)
    (fun | .ok o => s!"{o.val.length} declarations" | .error e => e)
  let installed? ← time "installation (all of it)"
    (fun _ => installSourceNormalizedComplete accepted.domain.1 (sourcePins input accepted.pins) witnesses)
    (fun | .ok i => s!"{i.declarations.length} declarations" | .error e => (sourceErrorLabel e).1)
  let .ok installed := installed? | return
  let _ ← time "source fold alone"
    (fun _ => (Kernel.Cached.checkDecls .verified installed.pins installed.declarations.toArray).toOption.isSome)
    flag
  let proposal? ← time "proposal" (fun _ => propose accepted installed)
    (fun | .ok p => s!"{p.support.size} support declarations" | .error e => e)
  let .ok proposal := proposal? | return
  let bundle? ← time "support" (fun _ => admitSupport accepted.toAdmittedArtifact proposal.support)
    (fun | .ok _ => "admitted" | .error e => supportLabel e)
  let .ok bundle := bundle? | return
  let source := installed.env
  let target := bundle.env
  let names := proposal.names
  say s!"[explain-S] {root}: strong check over {source.consts.length} source rows and {target.consts.length} target rows"
  let _ ← time "lookups only (one indexed target lookup per source row, index built)"
    (fun _ => let fT := envFind target; source.consts.all fun e => (fT (names e.name)).isSome) flag
  let _ ← time "names (SemanticNamesAgree)" (fun _ => decide (SemanticNamesAgree accepted names)) flag
  let _ ← time "comparison availability" (fun _ => checkInstalledComparisonAvailability source target names) opt
  let _ ← time "telescopes" (fun _ => checkTelescopes source target names) flag
  let _ ← time "types" (fun _ => checkInstalledTypes source target names) flag
  let _ ← time "definitions" (fun _ => checkInstalledDefinitions source target names) flag
  let _ ← time "False and Eq pins" (fun _ => checkInstalledPin source names Kernel.falseName 0 &&
    checkInstalledPin source names Kernel.eqName 1) flag
  let _ ← time "capabilities" (fun _ => checkInstalledCapabilities source target names) flag
  let _ ← time "recursors" (fun _ => checkInstalledRecursors source target names) flag
  let _ ← time "constructors" (fun _ => checkInstalledConstructors source target names) flag
  let _ ← time "eta associations" (fun _ => checkInstalledEtaAssociations source target names) opt
  let _ ← time "rule level links" (fun _ => checkInstalledRuleLevelLinks source target names) opt
  let _ ← time "reserved names and literal support" (fun _ => checkReservedNameMap source names &&
    checkTypeLiteralSupport source target && checkDefinitionLiteralSupport source target) flag
  let _ ← time "projection towers" (fun _ => checkInstalledTowers source target names) opt
  let _ ← time "reduce receipts" (fun _ => checkReduceOperationReceipts source target names
    proposal.operationCertificates proposal.elementCertificates) opt
  let _ ← time "Nat receipts" (fun _ => checkNatOperationReceipts source target names
    proposal.certificates proposal.levels) opt
  let _ ← time "Nat.div/mod receipts" (fun _ => checkDivModReceipts source target names
    proposal.certificates proposal.levels) opt
  let _ ← time "strong check (all of it)" (fun _ => checkNormalizedArtifactStrongAssociation accepted bundle
    installed names proposal.certificates proposal.operationCertificates proposal.elementCertificates
    proposal.levels) opt
  return


/-! ## The run (untrusted orchestration) -/

/-- An S verdict, beside the W verdict. -/
inductive SVerdict where
  | certified (root : Lean.Name)
  /-- S-certified at the value level (M7 S+a): a member of an accepted value-level cone
  (`StrongCone'.sound`). -/
  | certifiedValue (root : Lean.Name)
  | unsupported (cls : String)
  | blocked (dependency : Lean.Name) (cls : String)
  | rejected (diagnostic : String)
  deriving Inhabited

def SVerdict.word : SVerdict → String
  | .certified _ | .certifiedValue _ => "S-certified" | .unsupported _ => "S-unsupported"
  | .blocked .. => "S-blocked" | .rejected _ => "S-rejected"

def SVerdict.cls : SVerdict → String
  | .certified _ | .certifiedValue _ => "certified" | .unsupported c => c | .blocked _ c => c | .rejected d => d

def SVerdict.cause : SVerdict → String
  | .certified r => s!"cone {r}" | .certifiedValue r => s!"value cone {r}" | .unsupported c => c | .blocked d c => s!"{d}: {c}" | .rejected d => d

def SVerdict.isFinalFailure : SVerdict → Bool
  | .unsupported _ | .rejected _ => true
  | _ => false

/-- The W routes whose constants S decides (`runStrong`): W's own decision, `direct` or `raw`
(`direct/raw` when the whole input passed `checkIndexed` at once). -/
def sRoute (route : String) : Bool :=
  route == "direct" || route == "raw" || route == "direct/raw"

/-- The S class of a constant W certifies by a W+ route (M5: a theorem or equation row, a type
row, a changed block): outside what S decides. -/
def wPlusClass : String := "certified by a W+ route; S for changed constants is M7"

/-- The S verdict a constant gets from its W verdict when W did not certify it. -/
def ofW : Verdict → SVerdict
  | .certified => .unsupported "no S verdict"
  | .unsupported c => .unsupported s!"W unsupported: {c}"
  | .blocked d c => .blocked d s!"W: {c}"
  | .rejected d => .rejected s!"W rejected: {(d.splitOn ":").headD d}"

structure ConeRecord where
  root : Lean.Name
  outcome : ConeOutcome
  stats : ConeStats
  ms : Nat
  /-- The roots the cone was built from (more than one: a batch, `coverBatches`). -/
  roots : Nat := 1

def coneHeader : String :=
  "root\troots\tmembers\trecords\tsupport\twitnesses\tms\tms input\tms admission\tms W\tms installation\tms strong\toutcome\tclass\tculprit"

/-- The plan's rows (`--strong-plan`): the cone's position in the cover, its root (the batch
leader), the roots it was built from, its members, the W-certified constants it is the first
cone to contain, and the running total of those. -/
def planHeader : String :=
  "cone\troot\troots\tmembers\tnew\tcovered"

def coneRow (c : ConeRecord) : String :=
  let (o, cls, cul) := match c.outcome with
    | .certified _ => ("certified", "", "")
    | .failed cls culprit _ => ("failed", cls, toString (culprit.getD c.root))
  s!"{c.root}\t{c.roots}\t{c.stats.members}\t{c.stats.records}\t{c.stats.support}\t{c.stats.witnesses}\t{c.ms}\t\
    {c.stats.msInput}\t{c.stats.msAdmit}\t{c.stats.msW}\t{c.stats.msInstall}\t{c.stats.msStrong}\t{o}\t\
    {oneLine cls}\t{cul}"

/-- Decide S over the W run's certified constants: every one (a cover by
cones, largest-first by user count), a sample, or given roots. Writes
`<out>.strong.tsv`, `<out>.strong.cones.tsv`, `<out>.strong.classes.tsv`,
`<out>.strong.json`; returns the exit code (1 iff something is S-rejected or
nothing is S-certified). -/
def runStrong (cfg : Config) (w : WState) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  -- W+ (M5): S decides only the constants W certifies by the direct or raw route. A constant W
  -- certifies by a W+ route (a theorem or equation row, a type row, a changed block) has a
  -- target row that is not its Lean declaration's export, which S's per-cone W association
  -- (`checkIndexed`) and strong checks compare against; S for changed constants is M7. Such a
  -- constant is S-unsupported (`wPlusClass`), is never put in a cone (so never S-rejected for
  -- it), and every cone that reaches it is S-blocked by it. Untrusted orchestration: this only
  -- keeps constants out of cones; a wrong route label cannot certify anything, since a cone's
  -- members are certified only by the cone's own W association and strong check.
  let wPlus : Std.HashMap Lean.Name String := w.names.foldl (fun m n =>
    if (w.verdicts.getD n (.unsupported "")).isCertified then
      match w.routes[n]? with
      | some r => if sRoute r then m else m.insert n r
      | none => m
    else m) {}
  let wCertified : Std.HashSet Lean.Name := w.names.foldl (fun s n =>
    if (w.verdicts.getD n (.unsupported "")).isCertified && !wPlus.contains n then s.insert n else s) {}
  say s!"[certify-S] W+ routes: {wPlus.size} W-certified constants are certified by a W+ route \
    ({wPlusClass})"
  -- the Lean-kernel-checked lowering witnesses, once (KB): projection functions of
  -- mutual, nested or recursive structure-likes among the W-certified constants
  let decls := w.names.toList.filterMap fun n => if wCertified.contains n then w.env.find? n else none
  let functions := LoweringLean.projectionFunctionsIn w.env decls
  let mut witnessOf : Std.HashMap Lean.Name Lean.TheoremVal := {}
  let mut witnessRefused : Std.HashMap Lean.Name String := {}
  for f in functions do
    match ← LoweringLean.kernelCheckedWitnesses w.env [f] with
    | .ok [wv] => witnessOf := witnessOf.insert f wv
    | .ok _ => witnessRefused := witnessRefused.insert f "no witness"
    | .error why => witnessRefused := witnessRefused.insert f why
  say s!"[certify-S] lowering witnesses: {witnessOf.size} accepted by Lean's kernel, {witnessRefused.size} refused; \
    {(← IO.monoMsNow) - t0} ms"
  -- diagnostics: the source pins of the requested cones, and which of their constants the
  -- cone does not rename (absent from the cone)
  for n in cfg.explain do
    let (members, _) := coneOf w.refs wCertified.contains #[n]
    match coneInput w.env w.produced w.store w.namedAddr [n] members, Kernel.Reader.defaultPins with
    | .ok input, .ok pins =>
      for p in renamedBuiltinPins input pins do
        let all := (p.modPin :: p.divPin :: p.gcdPin :: p.modProofs ++ p.divProofs ++ p.gcdProofs).flatMap exprConsts
        let left := (all.filter (fun (_, c) => (toString c).startsWith "ix.")).eraseDups
        say s!"[explain-S] {n}: cone {members.size}; renamed builtin pins {p.toolchain}: {all.length} references, \
          not in the cone: {left.map (fun (k, c) => s!"{k}:{c}")}"
      -- the source-named pins: per operation of the cone, its certificate ground absent from the cone
      for p in sourcePins input pins do
        for (op, opK, _) in SourcePinGen.certSpecs do
          if members.contains op then
            let left := (SourcePinGen.groundOf w.env.find? p opK).filter (!members.contains ·)
            say s!"[explain-S] {n}: source pins {p.toolchain}: {op}: certificate ground not in the cone: {left}"
      -- the installation's stages, timed one by one
      let time {α : Type} (label : String) (f : Unit → α) (show_ : α → String) : IO Unit := do
        let t ← IO.monoMsNow
        let a ← IO.lazyPure f
        say s!"[explain-S] {n}: {label}: {show_ a}; {(← IO.monoMsNow) - t} ms"
      -- the builtin pin renamed into the cone versus the cone's own value
      match Kernel.Reader.builtinNatOpPins with
      | .ok (ps :: _) =>
        let cx : ExportContext := ⟨input.source, input.map, pins, noImages⟩
        let inverse : Std.HashMap Kernel.Name Kernel.Name := input.source.declarations.foldl (fun m ci =>
          match cx.name ci.name with
          | .ok t => if m.contains t then m else m.insert t (sourceName ci.name)
          | .error _ => m) {}
        let r := kernelRenameAll (fun n => inverse.getD n n)
        for (c, pin) in [(Kernel.natDivName, ps.divPin), (Kernel.natModName, ps.modPin)] do
          match input.source.find (leanNameOf c) with
          | some ci => match exportSourceEntry ci with
            | .ok (.defn _ value _) =>
              say s!"[explain-S] {n}: {c}: renamed pin = own value: {decide (r pin = value)}; first difference: {firstDiff (r pin) value}"
            | _ => pure ()
          | none => pure ()
      | _ => pure ()
      match exportSourceDeclarations input.source with
      | .error e => say s!"[explain-S] {n}: export failed: {e}"
      | .ok original =>
        time "export" (fun _ => (exportSourceDeclarations input.source).toOption.map (·.size)) toString
        match proposeSourceModels input.source original with
        | .error e => say s!"[explain-S] {n}: proposal failed: {e}"
        | .ok proposal =>
          time "model proposal" (fun _ => (proposeSourceModels input.source original).toOption.map (·.declarations.size)) toString
          time "sublist" (fun _ => decide (original.toList.Sublist proposal.declarations.toList)) toString
          time "entry correspondence" (fun _ => decide (SourceEntryCorrespondence input.source proposal.declarations)) toString
          time "fold" (fun _ => (Kernel.Cached.checkDecls .verified (sourcePins input pins) proposal.declarations).toOption.isSome) toString
    | _, _ => say s!"[explain-S] {n}: no cone input"
  -- what a cone containing a pin-certified Nat operation also takes (`coneMembers`)
  let readerPins ← IO.ofExcept Kernel.Reader.defaultPins
  let pinGround := natOpPinGround w.env w.store w.namedAddr readerPins w.names wCertified.contains
  say s!"[certify-S] source pins: {(SourcePinGen.sourceNatOpPinSets).map (·.toolchain)}"
  say s!"[certify-S] pin ground of the Nat operations: {natOpLeanNames.map (fun op => (pinGround.getD op #[]).size)} constants"
  -- the global cone (M7 WP-F): one cone over every W-certified (direct or raw) constant whose
  -- closure stays among them, decided before the cover is planned; the cover then decides only
  -- what it did not certify (everything, if it is refused)
  let mut globalRecord : Option ConeRecord := none
  let mut globalCertified : Std.HashSet Lean.Name := {}
  if cfg.strongGlobal || cfg.explainGlobal then
    let (members, outside) := globalConeMembers w.names w.refs wCertified.contains
    let memberSet : Std.HashSet Lean.Name := members.foldl (·.insert ·) {}
    let missingGround := natOpLeanNames.foldl (fun acc op =>
      if memberSet.contains op then acc ++ (pinGround.getD op #[]).filter (!memberSet.contains ·) else acc) #[]
    say s!"[certify-S] global cone: {members.size} members; {outside.size} W-certified constants outside it \
      (each reaches a constant outside S's domain); Nat pin ground not in it: {missingGround.toList.take 5}"
    if let some root := members[0]? then
      let witnesses := members.toList.filterMap witnessOf.get?
      if cfg.explainGlobal then
        explainCone w.env w.produced w.store w.namedAddr root members witnesses
      if cfg.strongGlobal && !cfg.strongPlan then
        let began ← IO.monoMsNow
        let (outcome, stats) ← runCone w.env w.produced w.store w.namedAddr cfg.workers root members witnesses
        let record : ConeRecord := { root, outcome, stats, ms := (← IO.monoMsNow) - began, roots := members.size }
        globalRecord := some record
        match outcome with
        | .certified certified =>
          globalCertified := certified.foldl (·.insert ·) {}
          say s!"[certify-S] global cone: accepted, {certified.size} S-certified; {record.ms} ms \
            (input {stats.msInput}, admission {stats.msAdmit}, W {stats.msW}, installation {stats.msInstall}, \
            strong {stats.msStrong})"
        | .failed cls culprit _ =>
          say s!"[certify-S] global cone: refused ({cls}; {culprit}); {record.ms} ms; the cover decides every root"
  -- users, for the order of a full cover (constants nothing uses first)
  let mut userCount : Std.HashMap Lean.Name Nat := {}
  for n in w.names do
    if wCertified.contains n then
      for r in w.refs.getD n #[] do
        if r != n then userCount := userCount.insert r (userCount.getD r 0 + 1)
  -- the cover plans only what the global cone (if any) did not certify
  let certifiedSorted := w.names.filter fun n => wCertified.contains n && !globalCertified.contains n
  -- decided first (a sample or a cover): the constants whose own source fold decides every cone
  -- that contains them (the pin-certified Nat operations, through the source-named pins; `Quot`,
  -- over the pinned `Eq`); every later cone that contains one with a final failure is S-blocked
  -- by it without running
  let firstRoots : Array Lean.Name := natOpLeanNames.push `Quot
  let roots : Array Lean.Name :=
    if !cfg.strongRoots.isEmpty then cfg.strongRoots
    else if cfg.strongEvery > 0 then Id.run do
      let mut out : Array Lean.Name := firstRoots.filter wCertified.contains
      let mut seen : Std.HashSet Lean.Name := out.foldl (·.insert ·) {}
      for f in functions do
        unless seen.contains f do out := out.push f; seen := seen.insert f
      for i in [0:certifiedSorted.size] do
        if i % cfg.strongEvery == 0 then
          let n := certifiedSorted[i]!
          unless seen.contains n do out := out.push n; seen := seen.insert n
      return out
    else
      -- constants nothing uses, largest cone first (they cover the most), then the rest
      let sized := (certifiedSorted.filter (fun n => userCount.getD n 0 == 0)).map fun n =>
        ((coneOf w.refs wCertified.contains #[n]).1.size, n)
      let top := (sized.qsort (fun a b => a.1 > b.1 || (a.1 == b.1 && toString a.2 < toString b.2))).map (·.2)
      let rest := certifiedSorted.filter (fun n => userCount.getD n 0 != 0)
      -- the pin-certified Nat operations first: their verdicts decide every cone that has them
      let ops := natOpLeanNames.filter fun n => wCertified.contains n && !globalCertified.contains n
      ops ++ (top ++ rest).filter (fun n => !ops.contains n)
  let cover := cfg.strongRoots.isEmpty && cfg.strongEvery == 0
  -- the cover's profile (diagnostic): each root nothing uses needs its own cone
  if cover then
    let sizes := (certifiedSorted.filter (fun n => userCount.getD n 0 == 0)).map fun n =>
      (coneOf w.refs wCertified.contains #[n]).1.size
    let band (lo hi : Nat) : Nat := (sizes.filter (fun s => lo ≤ s && s < hi)).size
    say s!"[certify-S] cover: {sizes.size} roots nothing uses; their cones: <1k {band 0 1000}, \
      1k–5k {band 1000 5000}, 5k–10k {band 5000 10000}, 10k–20k {band 10000 20000}, \
      ≥20k {band 20000 (1 <<< 62)}; {sizes.foldl (· + ·) 0} members in all"
  -- diagnostics: the explained roots' cones (with their certificate ground), stage by stage
  for n in cfg.explain do
    if wCertified.contains n then
      let (members, missing) := coneMembers w.refs wCertified.contains pinGround n
      if missing.isEmpty then
        explainCone w.env w.produced w.store w.namedAddr n members (members.toList.filterMap witnessOf.get?)
      else
        say s!"[explain-S] {n}: the cone reaches constants that are not W-certified: {missing.toList.take 5}"
  say s!"[certify-S] {roots.size} roots ({if !cfg.strongRoots.isEmpty then "given" else if cfg.strongEvery > 0 then s!"sample: every {cfg.strongEvery}th W-certified constant and {functions.length} projection functions" else "cover of every W-certified constant"}); \
    {cfg.strongTasks} cones at once; cone budget {cfg.strongMaxCone} declarations"
  -- a cover decides overlapping roots nothing uses together (`coverBatches`); a batch that
  -- cannot run or fails as one cone is dissolved and its roots get cones of their own
  let mut batchOf : Std.HashMap Lean.Name (Array Lean.Name) :=
    if cover then coverBatches w.refs wCertified.contains
      (roots.filter fun n => wCertified.contains n && userCount.getD n 0 == 0) 128 256
    else {}
  if cover then
    let merged := batchOf.fold (fun k _ b => k + b.size) 0
    say s!"[certify-S] cover batches: {batchOf.size} batches take {merged} further roots nothing uses"
  let mut sv : Std.HashMap Lean.Name SVerdict := {}
  let mut cones : Array ConeRecord := #[]
  let mut queue : Array Lean.Name := roots.reverse  -- a stack: the next root is `back`
  let mut attempted : Std.HashSet Lean.Name := {}
  -- a plan (`--strong-plan`) runs no cone: each is recorded as if accepted, in the cover's order,
  -- with the constants it adds; it writes `<out>.strong.plan.tsv` and no verdict
  let live ← IO.FS.Handle.mk
    (if cfg.strongPlan then s!"{cfg.out}.strong.plan.tsv" else s!"{cfg.out}.strong.live.tsv") .write
  live.putStrLn (if cfg.strongPlan then planHeader else coneHeader)
  let mut covered := 0
  let mut firstCone : Std.HashMap Lean.Name Nat := {}
  let mut lastReport := t0
  -- the global cone's record, inserted as the first cone below
  if let some record := globalRecord then
    live.putStrLn (coneRow record)
    live.flush
    cones := cones.push record
    if let .certified certified := record.outcome then
      for m in certified do sv := sv.insert m (.certified record.root)
      covered := covered + certified.size
  while queue.size > 0 do
    -- one wave: up to `strongTasks` roots that still need a cone
    let mut wave : Array (Lean.Name × Array Lean.Name) := #[]
    -- members of this wave's cones: a root among them waits for the wave (its cone is
    -- expected to certify it), so one wave does not decide the same cone twice
    let mut inWave : Std.HashSet Lean.Name := {}
    let mut deferred : Array Lean.Name := #[]
    -- a cover decides waves of `strongTasks` cones in order; a sample or given roots run every
    -- root's own cone, all at once on the task pool (deterministic either way)
    let firstPending := cfg.strongRoots.isEmpty && firstRoots.any (fun n => wCertified.contains n && !attempted.contains n)
    let waveSize := if cover then cfg.strongTasks
      else if firstPending then (firstRoots.filter wCertified.contains).size else queue.size
    while queue.size > 0 && wave.size < waveSize do
      let root := queue.back!
      queue := queue.pop
      if attempted.contains root then continue
      if cover then if let some (.certified _) := sv[root]? then continue
      if cover && inWave.contains root then
        deferred := deferred.push root
        continue
      attempted := attempted.insert root
      unless wCertified.contains root do
        sv := sv.insert root (if wPlus.contains root then .unsupported wPlusClass
          else match w.verdicts[root]? with
          | some v => ofW v
          | none => .unsupported "not in the artifact or the environment")
        continue
      -- a cone with a pin-certified Nat operation carries the records its pins need; a cone
      -- with `Quot` carries `Eq`, listed first (`coneMembers`); a batch leader's cone is the
      -- union with its batch's roots when that can run as one cone, else it is dissolved
      let batch := (batchOf[root]?).getD #[]
      let batchCone : Option (Array Lean.Name) :=
        if batch.isEmpty then none else
          let (bm, bmissing) := coneMembersOf w.refs wCertified.contains pinGround (#[root] ++ batch)
          if bmissing.isEmpty && bm.size ≤ cfg.strongMaxCone &&
              !bm.any (fun m => (sv[m]?.map SVerdict.isFinalFailure).getD false) &&
              (bm.findSome? witnessRefused.get?).isNone then some bm else none
      if batchCone.isNone && !batch.isEmpty then batchOf := batchOf.erase root
      let (members, missing) := match batchCone with
        | some bm => (bm, #[])
        | none => coneMembers w.refs wCertified.contains pinGround root
      if let some m := missing[0]? then
        let cls := if wPlus.contains m then wPlusClass
          else s!"W: {(ofW (w.verdicts.getD m (.unsupported "outside the artifact"))).cls}"
        sv := sv.insert root (.blocked m cls)
        continue
      -- a member with a final S failure blocks the cone without running it
      match members.find? (fun m => (cover || (cfg.strongRoots.isEmpty && firstRoots.contains m)) && m != root &&
          (sv[m]?.map SVerdict.isFinalFailure).getD false) with
      | some m =>
        let cls := (sv[m]?.map SVerdict.cls).getD ""
        sv := sv.insert root (.blocked m cls)
        continue
      | none => pure ()
      if members.size > cfg.strongMaxCone then
        sv := sv.insert root (.unsupported s!"cone over budget ({cfg.strongMaxCone} declarations)")
        continue
      if let some why := members.findSome? witnessRefused.get? then
        sv := sv.insert root (.unsupported s!"projection lowering: {(why.splitOn ":").headD why}")
        continue
      wave := wave.push (root, members)
      inWave := members.foldl (·.insert ·) inWave
    for d in deferred.reverse do queue := queue.push d
    if wave.isEmpty then continue
    -- at most `strongTasks` cones run at once; each finished cone's row is appended to the
    -- live log at once; the verdicts are committed in the wave's order (deterministic)
    let mut running : Array (Nat × Task (Except IO.Error ConeRecord)) := #[]
    let mut finished : Array (Nat × ConeRecord) := #[]
    let mut next := 0
    while next < wave.size || running.size > 0 do
      while next < wave.size && running.size < cfg.strongTasks do
        let (root, members) := wave[next]!
        let witnesses := members.toList.filterMap witnessOf.get?
        let nRoots := 1 + ((batchOf[root]?).map (·.size)).getD 0
        -- a plan runs nothing: the cone is recorded as if accepted
        let planned : ConeRecord :=
          { root, outcome := .certified members, stats := { members := members.size }, ms := 0, roots := nRoots }
        let task : Task (Except IO.Error ConeRecord) ← if cfg.strongPlan then pure (Task.pure (.ok planned))
          else IO.asTask (prio := .dedicated) do
            let began ← IO.monoMsNow
            let (outcome, stats) ← runCone w.env w.produced w.store w.namedAddr 1 root members witnesses
            return { root, outcome, stats, ms := (← IO.monoMsNow) - began, roots := nRoots : ConeRecord }
        running := running.push (next, task)
        next := next + 1
      let tasks := running.toList.map (·.2)
      if h : tasks.length > 0 then
        let _ ← IO.waitAny tasks h
      let mut still : Array (Nat × Task (Except IO.Error ConeRecord)) := #[]
      for (i, t) in running do
        if ← IO.hasFinished t then
          let record ← IO.ofExcept t.get
          unless cfg.strongPlan do
            live.putStrLn (coneRow record)
            live.flush
          finished := finished.push (i, record)
        else still := still.push (i, t)
      running := still
      let now ← IO.monoMsNow
      if now - lastReport > 60000 && !cfg.strongPlan then
        lastReport := now
        say s!"[certify-S] progress: {cones.size + finished.size} cones decided, {running.size} running, {queue.size + wave.size - next} roots queued; {now - t0} ms"
    for (_, record) in finished.qsort (fun a b => a.1 < b.1) do
      cones := cones.push record
      match record.outcome with
      | .certified members =>
        let mut fresh := 0
        for m in members do
          unless (match sv[m]? with | some (.certified _) => true | _ => false) do
            fresh := fresh + 1
            if cfg.strongPlan then firstCone := firstCone.insert m cones.size
          sv := sv.insert m (.certified record.root)
        covered := covered + fresh
        if cfg.strongPlan then
          live.putStrLn s!"{cones.size}\t{record.root}\t{record.roots}\t{record.stats.members}\t{fresh}\t{covered}"
      | .failed cls culprit unsupported =>
        if record.roots > 1 then
          -- a batch that fails is dissolved: its leader is decided again on its own cone next,
          -- and its other roots on theirs when the cover reaches them
          batchOf := batchOf.erase record.root
          attempted := attempted.erase record.root
          queue := queue.push record.root
          continue
        let culprit := culprit.getD record.root
        let own : SVerdict := if unsupported then .unsupported cls else .rejected cls
        let (_, inCone) := (wave.find? (·.1 == record.root)).getD (record.root, #[])
        let certifiedAlready := match sv[record.root]? with | some (.certified _) => true | _ => false
        if certifiedAlready then pure ()
        else if culprit == record.root || !inCone.contains culprit then
          sv := sv.insert record.root own
        else
          -- the cone fails on a member: the root is blocked by it, and (in a cover) the
          -- member gets its own cone next
          sv := sv.insert record.root (.blocked culprit cls)
          if cover then unless attempted.contains culprit do queue := queue.push culprit
    let now ← IO.monoMsNow
    if now - lastReport > 60000 && !cfg.strongPlan then
      lastReport := now
      let done := sv.fold (fun n _ v => match v with | .certified _ => n + 1 | _ => n) 0
      say s!"[certify-S] progress: {cones.size} cones, {done} S-certified, {queue.size} roots queued; {now - t0} ms"
  -- M7 S+a (`--strong-changed`): after the strong cones, S at the value level for what they left
  -- for W+'s sake. The W+-route constants outside a changed inductive block (theorems; definitions
  -- with a value row) are decided with the W-certified constants S-blocked by them, as one cone
  -- (its own W association W+'s, `decideStrongCone'`, `StrongCone'.sound`); if it is refused,
  -- each root on its own cone. A W+ constant over a changed block (S+b) or a transported member
  -- without a value row (package V) is S-unsupported with its class, and what reaches it S-blocked.
  -- Untrusted orchestration: the strong verdicts above are not touched, and a member is certified
  -- only by an accepted cone.
  let mut valueCertified := 0
  if cfg.strongChanged && !cfg.strongPlan then
    let tA ← IO.monoMsNow
    let mut domainA : Std.HashSet Lean.Name := {}
    let mut outsideA : Std.HashMap Lean.Name String := {}
    for n in w.names do
      if let some r := wPlus[n]? then
        match valueClassOf w.env n r with
        | none => domainA := domainA.insert n
        | some cls => outsideA := outsideA.insert n cls
    let knownA : Lean.Name → Bool := fun n => wCertified.contains n || domainA.contains n
    let leftForWPlus (n : Lean.Name) : Bool := match sv[n]? with
      | some (.blocked _ c) | some (.unsupported c) => c == wPlusClass
      | _ => false
    let rootsAll := w.names.filter fun n => domainA.contains n || (wCertified.contains n && leftForWPlus n)
    let (closedA, blockedA) := globalConeMembers w.names w.refs knownA
    let closedSet : Std.HashSet Lean.Name := closedA.foldl (·.insert ·) {}
    let rootsA := rootsAll.filter closedSet.contains
    for (n, c) in outsideA.toList do sv := sv.insert n (.unsupported c)
    for n in rootsAll do
      unless closedSet.contains n do
        if let some b := blockedA[n]? then
          let cls := match outsideA[b]? with
            | some c => c
            | none => match sv[b]? with
              | some v => v.cls
              | none => (ofW (w.verdicts.getD b (.unsupported "outside the artifact"))).cls
          sv := sv.insert n (.blocked b cls)
    let countClass (c : String) : Nat := outsideA.fold (fun k _ v => if v == c then k + 1 else k) 0
    say s!"[certify-S] value level (S+a): {domainA.size} W+ constants decided at the value level, \
      {outsideA.size} not ({countClass changedBlockClass} over a changed inductive block: S+b; \
      {countClass valueRowClass} transported members without a value row: package V); {rootsA.size} roots, \
      {rootsAll.size - rootsA.size} blocked"
    -- a value cone: the closure of its roots, with the constants its members' W+ rows mention
    let ground := rowGround w readerPins knownA
    let valueCone (roots : Array Lean.Name) : Array Lean.Name := Id.run do
      let mut seeds := roots
      let mut members := (coneMembersOf w.refs knownA pinGround seeds).1
      for _ in [0:4] do
        let present : Std.HashSet Lean.Name := members.foldl (·.insert ·) {}
        let extra := (members.flatMap fun m => ground.getD m #[]).filter fun g => knownA g && !present.contains g
        if extra.isEmpty then break
        seeds := seeds ++ extra
        members := (coneMembersOf w.refs knownA pinGround seeds).1
      return members
    let commit (root : Lean.Name) (certified : Array Lean.Name) (sv : Std.HashMap Lean.Name SVerdict) :
        Std.HashMap Lean.Name SVerdict × Nat := Id.run do
      let mut sv := sv
      let mut fresh := 0
      for m in certified do
        unless (match sv[m]? with | some (.certified _) | some (.certifiedValue _) => true | _ => false) do
          sv := sv.insert m (.certifiedValue root)
          fresh := fresh + 1
      return (sv, fresh)
    if let some root := rootsA[0]? then
      let members := valueCone rootsA
      let began ← IO.monoMsNow
      let (outcome, stats) ← runConeChanged w cfg.workers root members (members.toList.filterMap witnessOf.get?)
      let record : ConeRecord := { root, outcome, stats, ms := (← IO.monoMsNow) - began, roots := rootsA.size }
      cones := cones.push record
      live.putStrLn (coneRow record)
      live.flush
      match outcome with
      | .certified certified =>
        let (sv', fresh) := commit root certified sv
        sv := sv'
        valueCertified := valueCertified + fresh
        say s!"[certify-S] value cone: accepted, {members.size} members, {fresh} S-certified at the value level; \
          {record.ms} ms (input {stats.msInput}, admission {stats.msAdmit}, W+ {stats.msW}, installation \
          {stats.msInstall}, value check {stats.msStrong}; {stats.support} source-owned support declarations)"
      | .failed cls culprit _ =>
        say s!"[certify-S] value cone: refused ({cls}; {culprit}); {record.ms} ms; each root on its own cone"
        for r in rootsA do
          if (match sv[r]? with | some (.certified _) | some (.certifiedValue _) => true | _ => false) then continue
          let rm := valueCone #[r]
          let began ← IO.monoMsNow
          let (o, st) ← runConeChanged w cfg.workers r rm (rm.toList.filterMap witnessOf.get?)
          let rr : ConeRecord := { root := r, outcome := o, stats := st, ms := (← IO.monoMsNow) - began }
          cones := cones.push rr
          live.putStrLn (coneRow rr)
          live.flush
          match o with
          | .certified cs =>
            let (sv', fresh) := commit r cs sv
            sv := sv'
            valueCertified := valueCertified + fresh
          | .failed c culprit unsupported =>
            let culprit := culprit.getD r
            sv := sv.insert r (if culprit == r || !rm.contains culprit then
                (if unsupported then .unsupported c else .rejected c)
              else .blocked culprit c)
    say s!"[certify-S] value level (S+a): {valueCertified} S-certified at the value level; {(← IO.monoMsNow) - tA} ms"
  if cfg.strongPlan then
    live.flush
    -- per W-certified constant: the first cone of the plan that contains it, or why none does
    let mut rows := "name\tcone\tcause\n"
    let mut without : Std.HashMap String Nat := {}
    for n in w.names do
      if wPlus.contains n then
        rows := rows ++ s!"{n}\t-\tS-unsupported: {wPlusClass}\n"
        continue
      unless wCertified.contains n do continue
      match firstCone[n]? with
      | some i => rows := rows ++ s!"{n}\t{i}\t\n"
      | none =>
        let cls := match sv[n]? with
          | some v => s!"{v.word}: {v.cls}"
          | none => "no cone"
        rows := rows ++ s!"{n}\t-\t{oneLine cls}\n"
        without := without.insert cls (without.getD cls 0 + 1)
    IO.FS.writeFile s!"{cfg.out}.strong.plan.names.tsv" rows
    let sizes := cones.map (·.stats.members)
    let band (lo hi : Nat) : Nat := (sizes.filter (fun s => lo ≤ s && s < hi)).size
    let batched := (cones.filter (·.roots > 1)).size
    let classes := without.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
    say s!"[certify-S] plan (no cone run; each counted as accepted): {cones.size} cones ({batched} batches), \
      {sizes.foldl (· + ·) 0} members in all; cone sizes <1k {band 0 1000}, 1k–2k {band 1000 2000}, \
      2k–5k {band 2000 5000}, 5k–10k {band 5000 10000}, ≥10k {band 10000 (1 <<< 62)}; \
      {covered} of {wCertified.size} W-certified constants (direct or raw) in a cone, \
      {wCertified.size - covered} in none; {wPlus.size} certified by a W+ route, outside S\
      {String.join (classes.toList.map fun (c, k) => s!"; {k} {c}")}"
    return 0
  -- every W-certified constant without an S verdict was not reached (sample or roots mode)
  let sampled := !cfg.strongRoots.isEmpty || cfg.strongEvery > 0
  let mut tsv := "name\tW verdict\tS verdict\tcause\n"
  let mut byWord : Std.HashMap String Nat := {}
  let mut byClass : Std.HashMap (String × String) Nat := {}
  for n in w.names do
    let wv := w.verdicts.getD n (.unsupported "no verdict")
    let some v := (sv[n]?).orElse (fun _ =>
        if wPlus.contains n then some (.unsupported wPlusClass)
        else if wv.isCertified then none else some (ofW wv))
      | continue
    tsv := tsv ++ s!"{n}\t{if w.wRun then wv.word else "not run"}\t{v.word}\t{oneLine v.cause}\n"
    byWord := byWord.insert v.word (byWord.getD v.word 0 + 1)
    match v with
    | .certified _ | .certifiedValue _ => pure ()
    | _ => byClass := byClass.insert (v.word, v.cls) (byClass.getD (v.word, v.cls) 0 + 1)
  let notReached := w.names.foldl (fun k n => if wCertified.contains n && !sv.contains n then k + 1 else k) 0
  IO.FS.writeFile s!"{cfg.out}.strong.tsv" tsv
  let mut coneText := coneHeader ++ "\n"
  for c in cones.qsort (fun a b => toString a.root < toString b.root) do
    coneText := coneText ++ coneRow c ++ "\n"
  IO.FS.writeFile s!"{cfg.out}.strong.cones.tsv" coneText
  let classes := byClass.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && toString a.1 < toString b.1))
  let mut classText := "S verdict\tclass\tcount\n"
  for ((v, c), k) in classes do classText := classText ++ s!"{v}\t{oneLine c}\t{k}\n"
  IO.FS.writeFile s!"{cfg.out}.strong.classes.tsv" classText
  let words := #["S-certified", "S-unsupported", "S-blocked", "S-rejected"]
  let coneMs := cones.foldl (fun n c => n + c.ms) 0
  let json := Lean.Json.mkObj [
    ("mode", Lean.toJson (if !cfg.strongRoots.isEmpty then "roots" else if cfg.strongEvery > 0 then s!"sample every {cfg.strongEvery}" else "cover")),
    ("roots", Lean.toJson roots.size), ("cones", Lean.toJson cones.size),
    ("conesCertified", Lean.toJson (cones.filter (fun c => match c.outcome with | .certified _ => true | _ => false)).size),
    ("coneMsTotal", Lean.toJson coneMs), ("witnesses", Lean.toJson witnessOf.size),
    ("witnessesRefused", Lean.toJson witnessRefused.size), ("notReached", Lean.toJson notReached),
    ("wPlusRoute", Lean.toJson wPlus.size), ("valueCertified", Lean.toJson valueCertified),
    ("perName", Lean.Json.mkObj (words.toList.map fun v => (v, Lean.toJson (byWord.getD v 0)))),
    ("classes", Lean.Json.arr (classes.map fun ((v, c), k) => Lean.Json.mkObj
      [("verdict", Lean.toJson v), ("class", Lean.toJson c), ("count", Lean.toJson k)]))]
  IO.FS.writeFile s!"{cfg.out}.strong.json" json.pretty
  let counts := " ".intercalate (words.toList.map fun v => s!"{v}={byWord.getD v 0}")
  say s!"[certify-S] per name: {counts}; not reached: {notReached}{if sampled then " (sample)" else ""}; \
    {cones.size} cones ({coneMs} ms in cones); total {(← IO.monoMsNow) - t0} ms"
  if byWord.getD "S-certified" 0 == 0 then
    IO.eprintln "[certify-S] FAIL: nothing S-certified"
    return 1
  if byWord.getD "S-rejected" 0 != 0 then
    IO.eprintln s!"[certify-S] FAIL: {byWord.getD "S-rejected" 0} S-rejected"
    return 1
  return 0

end Ix.CompileCert.Strong
