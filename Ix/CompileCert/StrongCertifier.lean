import Ix.CompileCert.Certifier
import Ix.CompileCert.StrongCone

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
  over the exported cone);
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

/-- The builtin Nat-operation pin sets with their constants renamed from the
target's names (the pins name ground constants by Ix address) into the cone's
source names, for the source fold (`installSourceNormalizedWith`). Untrusted:
the fold checks every pin and certificate it uses, and is sound for any pins. -/
def sourcePins (input : Input) (pins : Kernel.Reader.Pins) : List Kernel.NatOpPinSet :=
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

/-- Names, support and receipt names for one cone. Nothing here is trusted:
`decideStrongCone` checks every part. -/
def propose {input : Input} (accepted : AcceptedAssociation input)
    (installed : SourceNormalizedInstallation input.source input.roots) :
    Except String StrongProposal := do
  let cx : ExportContext := ⟨input.source, input.map, accepted.pins, noImages⟩
  let mappings ← input.source.declarations.mapM fun ci => do
    return (sourceName ci.name, ← cx.name ci.name)
  let helpers ← proposeSourceHelperBindings installed.modelProposal mappings
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
    accepted.env.consts.foldl (fun s e => s.insert e.name) {}
  let mut support : Array Kernel.Declaration := #[]
  for declaration in installed.declarations do
    let declared := declaration.names
    if declared.all (fun n => targetNames.contains (names n)) then continue
    match declaration with
    | .basisDecl _ => throw s!"basis declaration {declared} has no target row"
    | _ => support := support.push (← (proposeRenamedSupport names declaration).mapError
        (fun e => s!"{e}: {declared.map leanNameOf}"))
  let never : Kernel.Name → Kernel.Name := fun n => n.str "_ix_no_value_certificate"
  return { names, support, certificates := never, operationCertificates := never,
           elementCertificates := never, levels := fun _ => .succ .zero }

/-! ## Diagnosis of a refused strong check (untrusted) -/

/-- The per-row comparison of `checkInstalledComparisonAvailability`, evaluated
row by row to name the first row it does not accept (`none`: no comparison,
`some false`: refused). -/
def availabilityRow (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (entry : Kernel.ConstantInfo) : Option Bool := do
  let some targetEntry := target.find? (names entry.name) | return false
  let typeResult ← checkInstalledMemberExpr source target names entry.name
    entry.toConstantVal.type targetEntry.toConstantVal.type
  if !typeResult then return false
  match entry, targetEntry with
  | .defnInfo header value _, .defnInfo _ targetValue _ =>
    checkInstalledMemberExpr source target names header.name value targetValue
  | .recInfo header _ _ rules, .recInfo _ _ _ targetRules =>
    checkInstalledRules source target names header.name rules targetRules
  | .indInfo header caps, .indInfo _ targetCaps =>
    checkInstalledMemberExpr source target names header.name
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
  if !decide (SemanticNamesAgree accepted names) then return ("names: semantic name map", none, false)
  for entry in source.consts do
    match availabilityRow source target names entry with
    | some true => pure ()
    | some false =>
      let why := if (target.find? (names entry.name)).isNone then "no target row" else "refused"
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
  let queries : Lean.Name → Array Lean.Name := fun n => Id.run do
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
  let (accepted?, ms) ← stage fun _ =>
    checkIndexed input artifact (buildHints input (Shared.ofArtifact input artifact) queries workers)
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


/-! ## The run (untrusted orchestration) -/

/-- An S verdict, beside the W verdict. -/
inductive SVerdict where
  | certified (root : Lean.Name)
  | unsupported (cls : String)
  | blocked (dependency : Lean.Name) (cls : String)
  | rejected (diagnostic : String)
  deriving Inhabited

def SVerdict.word : SVerdict → String
  | .certified _ => "S-certified" | .unsupported _ => "S-unsupported"
  | .blocked .. => "S-blocked" | .rejected _ => "S-rejected"

def SVerdict.cls : SVerdict → String
  | .certified _ => "certified" | .unsupported c => c | .blocked _ c => c | .rejected d => d

def SVerdict.cause : SVerdict → String
  | .certified r => s!"cone {r}" | .unsupported c => c | .blocked d c => s!"{d}: {c}" | .rejected d => d

def SVerdict.isFinalFailure : SVerdict → Bool
  | .unsupported _ | .rejected _ => true
  | _ => false

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

def coneHeader : String :=
  "root\tmembers\trecords\tsupport\twitnesses\tms\tms input\tms admission\tms W\tms installation\tms strong\toutcome\tclass\tculprit"

def coneRow (c : ConeRecord) : String :=
  let (o, cls, cul) := match c.outcome with
    | .certified _ => ("certified", "", "")
    | .failed cls culprit _ => ("failed", cls, toString (culprit.getD c.root))
  s!"{c.root}\t{c.stats.members}\t{c.stats.records}\t{c.stats.support}\t{c.stats.witnesses}\t{c.ms}\t\
    {c.stats.msInput}\t{c.stats.msAdmit}\t{c.stats.msW}\t{c.stats.msInstall}\t{c.stats.msStrong}\t{o}\t\
    {oneLine cls}\t{cul}"

/-- Decide S over the W run's certified constants: every one (a cover by
cones, largest-first by user count), a sample, or given roots. Writes
`<out>.strong.tsv`, `<out>.strong.cones.tsv`, `<out>.strong.classes.tsv`,
`<out>.strong.json`; returns the exit code (1 iff something is S-rejected or
nothing is S-certified). -/
def runStrong (cfg : Config) (w : WState) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let wCertified : Std.HashSet Lean.Name := w.names.foldl (fun s n =>
    if (w.verdicts.getD n (.unsupported "")).isCertified then s.insert n else s) {}
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
      for p in sourcePins input pins do
        let all := (p.modPin :: p.divPin :: p.gcdPin :: p.modProofs ++ p.divProofs ++ p.gcdProofs).flatMap exprConsts
        let left := (all.filter (fun (_, c) => (toString c).startsWith "ix.")).eraseDups
        say s!"[explain-S] {n}: cone {members.size}; pins {p.toolchain}: {all.length} references, not in the cone: \
          {left.map (fun (k, c) => s!"{k}:{c}")}"
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
      time "complete source (lists)" (fun _ => decide (CompleteSource input.source input.roots)) toString
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
  -- users, for the order of a full cover (constants nothing uses first)
  let mut userCount : Std.HashMap Lean.Name Nat := {}
  for n in w.names do
    if wCertified.contains n then
      for r in w.refs.getD n #[] do
        if r != n then userCount := userCount.insert r (userCount.getD r 0 + 1)
  let certifiedSorted := w.names.filter wCertified.contains
  -- decided first (a sample or a cover): the constants whose own source fold is known to be
  -- refused (the pin-certified Nat operations, `Quot`); every later cone that contains one with
  -- a final failure is S-blocked by it without running
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
      let ops := natOpLeanNames.filter wCertified.contains
      ops ++ (top ++ rest).filter (fun n => !ops.contains n)
  let cover := cfg.strongRoots.isEmpty && cfg.strongEvery == 0
  -- the records a pin-certified Nat operation's pin and certificates need: the Lean names of
  -- the target names they mention (any member of an alias fiber: the members share a record)
  let readerPins ← IO.ofExcept Kernel.Reader.defaultPins
  let targetToLean : Std.HashMap Kernel.Name Lean.Name := w.names.foldl (fun m n =>
    if !wCertified.contains n then m else
    match w.namedAddr[n]? with
    | some a => match Kernel.Reader.resolve (w.store[·]?) a with
      | some r =>
        let k := readerPins.names.getD r (Kernel.Reader.keyName r)
        if m.contains k then m else m.insert k n
      | none => m
    | none => m) {}
  -- per operation: the constants its pin and certificates mention, over every variant
  let pinGround : Std.HashMap Lean.Name (Array Lean.Name) := match Kernel.Reader.builtinNatOpPins with
    | .error _ => {}
    | .ok sets => Id.run do
      let mut out : Std.HashMap Lean.Name (Array Lean.Name) := {}
      for (op, opK) in natOpLeanNames.zip #[Kernel.natDivName, Kernel.natModName, Kernel.natGcdName,
          Kernel.natLandName, Kernel.natLorName, Kernel.natXorName, Kernel.natShiftLeftName,
          Kernel.natShiftRightName] do
        let mut ground : Std.HashSet Lean.Name := {}
        for ps in sets do
          for e in Kernel.divModDeclPin ps opK :: Kernel.divModCertProofs ps opK do
            for (_, c) in exprConsts e do
              if let some n := findTarget targetToLean 8 c then ground := ground.insert n
        out := out.insert op (ground.toArray.qsort (fun a b => toString a < toString b))
      return out
  say s!"[certify-S] pin ground of the Nat operations: {natOpLeanNames.map (fun op => (pinGround.getD op #[]).size)} constants"
  say s!"[certify-S] {roots.size} roots ({if !cfg.strongRoots.isEmpty then "given" else if cfg.strongEvery > 0 then s!"sample: every {cfg.strongEvery}th W-certified constant and {functions.length} projection functions" else "cover of every W-certified constant"}); \
    {cfg.strongTasks} cones at once; cone budget {cfg.strongMaxCone} declarations"
  let mut sv : Std.HashMap Lean.Name SVerdict := {}
  let mut cones : Array ConeRecord := #[]
  let mut queue : Array Lean.Name := roots.reverse  -- a stack: the next root is `back`
  let mut attempted : Std.HashSet Lean.Name := {}
  let live ← IO.FS.Handle.mk s!"{cfg.out}.strong.live.tsv" .write
  live.putStrLn coneHeader
  let mut lastReport := t0
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
        sv := sv.insert root (match w.verdicts[root]? with
          | some v => ofW v
          | none => .unsupported "not in the artifact or the environment")
        continue
      let (members0, _) := coneOf w.refs wCertified.contains #[root]
      -- a cone with a pin-certified Nat operation carries the records its pins need
      let ground := (natOpLeanNames.filter members0.contains).foldl (fun acc op => acc ++ pinGround.getD op #[]) #[]
      let (members, missing) := if ground.isEmpty then coneOf w.refs wCertified.contains #[root]
        else coneOf w.refs wCertified.contains (#[root] ++ ground)
      if let some m := missing[0]? then
        sv := sv.insert root (.blocked m s!"W: {(ofW (w.verdicts.getD m (.unsupported "outside the artifact"))).cls}")
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
        let task ← IO.asTask (prio := .dedicated) do
          let began ← IO.monoMsNow
          let (outcome, stats) ← runCone w.env w.produced w.store w.namedAddr 1 root members witnesses
          return { root, outcome, stats, ms := (← IO.monoMsNow) - began : ConeRecord }
        running := running.push (next, task)
        next := next + 1
      let tasks := running.toList.map (·.2)
      if h : tasks.length > 0 then
        let _ ← IO.waitAny tasks h
      let mut still : Array (Nat × Task (Except IO.Error ConeRecord)) := #[]
      for (i, t) in running do
        if ← IO.hasFinished t then
          let record ← IO.ofExcept t.get
          live.putStrLn (coneRow record)
          live.flush
          finished := finished.push (i, record)
        else still := still.push (i, t)
      running := still
      let now ← IO.monoMsNow
      if now - lastReport > 60000 then
        lastReport := now
        say s!"[certify-S] progress: {cones.size + finished.size} cones decided, {running.size} running, {queue.size + wave.size - next} roots queued; {now - t0} ms"
    for (_, record) in finished.qsort (fun a b => a.1 < b.1) do
      cones := cones.push record
      match record.outcome with
      | .certified members =>
        for m in members do sv := sv.insert m (.certified record.root)
      | .failed cls culprit unsupported =>
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
    if now - lastReport > 60000 then
      lastReport := now
      let done := sv.fold (fun n _ v => match v with | .certified _ => n + 1 | _ => n) 0
      say s!"[certify-S] progress: {cones.size} cones, {done} S-certified, {queue.size} roots queued; {now - t0} ms"
  -- every W-certified constant without an S verdict was not reached (sample or roots mode)
  let sampled := !cfg.strongRoots.isEmpty || cfg.strongEvery > 0
  let mut tsv := "name\tW verdict\tS verdict\tcause\n"
  let mut byWord : Std.HashMap String Nat := {}
  let mut byClass : Std.HashMap (String × String) Nat := {}
  for n in w.names do
    let wv := w.verdicts.getD n (.unsupported "no verdict")
    let some v := (sv[n]?).orElse (fun _ => if wv.isCertified then none else some (ofW wv))
      | continue
    tsv := tsv ++ s!"{n}\t{if w.wRun then wv.word else "not run"}\t{v.word}\t{oneLine v.cause}\n"
    byWord := byWord.insert v.word (byWord.getD v.word 0 + 1)
    match v with
    | .certified _ => pure ()
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
