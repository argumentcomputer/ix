import Ix.CompileCert.StrongCertifier

/-! One global S cone (M7 WP-F) on the fixtures, run in-process (`Certifier.runW`, then
`Strong.runStrong` with `strongGlobal`), read back from the files it writes, beside the cover
(`runStrong` without it) on the same W state. Both explicitly disable `strongChanged`
so this control compares the direct/raw cone algorithms:

1. `BlockDefs` over `compiled.ixe` and `ChangedDefs` over `changed.ixe`: the global cone is the
   only cone run and it is accepted; the S verdict of every constant is the cover's (the cover
   runs several cones on `BlockDefs`; on `ChangedDefs` the W+-route constants stay S-unsupported
   and their users S-blocked, as in the cover);
2. negative, beside it: every W+ route of `ChangedDefs` forged to `direct`. The global cone then
   contains the forged constants and is refused by its own W association; the cover is the
   fallback and its verdicts are exactly the forged cover's; none of the forged constants is
   S-certified;
3. on the global cone of each fixture (the real installed source and admitted target), the fast
   decisions, as compiled code runs them, equal the list and tree decisions they replace:
   the source export (`exportSourceDeclarations` against the list export), the model proposal
   (`proposeSourceModels` against its block evidence through `Source.find`), the entry
   correspondence (against list membership), the normalisation (against the list lookup), and
   the strong check (`checkStrongAssociationF` against `checkStrongAssociation`, which was
   compiled before the substitutions and so runs the list lookups and tree walks).

Fixture results, not library claims. -/

namespace Tests.Ix.CompileCert.StrongGlobal

open _root_.Ix.CompileCert _root_.Ix.CompileCert.Certifier _root_.Ix.CompileCert.Strong

def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"strong global check failed: {label}")
  IO.println s!"PASS: {label}"

def rowsOf (path : System.FilePath) : IO (Array (Array String)) := do
  let text ← IO.FS.readFile path
  let lines := (text.splitOn "\n").filter (· ≠ "")
  return (lines.drop 1).toArray.map fun l => (l.splitOn "\t").toArray

def cell (row : Array String) (i : Nat) : String := row.getD i ""

/-- name ↦ (S verdict, cause). -/
def sVerdicts (pre : String) : IO (Std.HashMap String (String × String)) := do
  let rows ← rowsOf s!"{pre}.strong.tsv"
  return rows.foldl (fun m r => m.insert (cell r 0) (cell r 2, cell r 3)) {}

/-- The same S verdict for every constant, and the same cause for every one not S-certified (the
cause of an S-certified constant names its cone's root, which differs between a global cone and the
cover's cones). -/
def sameVerdicts (a b : Std.HashMap String (String × String)) : Bool :=
  a.size == b.size && a.toList.all fun (n, v) => match b.get? n with
    | some w => v.1 == w.1 && (v.1 == "S-certified" || v.2 == w.2)
    | none => false

/-- `(cones, cones accepted)` from `<prefix>.strong.json`. -/
def coneCounts (pre : String) : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"{pre}.strong.json"))
  let cones ← IO.ofExcept (json.getObjValAs? Nat "cones")
  let accepted ← IO.ofExcept (json.getObjValAs? Nat "conesCertified")
  return (cones, accepted)

/-- The list export (the reference of `exportSourceDeclarations`). -/
def exportList (s : Source) : ExportM (Array _root_.Ix.Kernel.Declaration) := do
  let groups ← buildSourceGroupsP (exportSourceInductive s) (sourceGroupDependencies s) s.declarations
  let groups ← validateSourceGroups s groups
  return (← orderSourceGroups (groups.length + 1) groups [] []).toArray

/-- The fast decisions against their references on one fixture's global cone. -/
def equalities (label : String) (w : WState) : IO Unit := do
  let wCertified : Std.HashSet Lean.Name := w.names.foldl (fun s n =>
    if (w.verdicts.getD n (.unsupported "")).isCertified &&
        (match w.routes[n]? with | some r => sRoute r | none => true) then s.insert n else s) {}
  let (members, _) := globalConeMembers w.names w.refs wCertified.contains
  let some root := members[0]? | throw (IO.userError s!"{label}: empty global cone")
  let input ← IO.ofExcept (coneInput w.env w.produced w.store w.namedAddr [root] members)
  let artifact ← match prepareArtifact input.toArtifactInput with
    | .ok a => pure a
    | .error _ => throw (IO.userError s!"{label}: admission refused")
  let accepted ← match checkIndexed input artifact
      (buildHints input (Shared.ofArtifact input artifact) (hintQueries w.env) 1) with
    | .ok a => pure a
    | .error _ => throw (IO.userError s!"{label}: W association refused")
  let source := input.source
  -- the Lean-kernel-checked lowering witnesses of the cone, as `runStrong` computes them
  let mut witnesses : LoweringWitnesses := []
  for f in LoweringLean.projectionFunctionsIn w.env (members.toList.filterMap w.env.find?) do
    if let .ok [wv] := ← LoweringLean.kernelCheckedWitnesses w.env [f] then witnesses := witnesses ++ [wv]
  let original ← IO.ofExcept (exportSourceDeclarations source)
  require s!"{label}: the source export equals the list export ({original.size} declarations)"
    (match exportList source with
     | .ok reference => decide (reference.toList = original.toList)
     | .error _ => false)
  let proposal ← IO.ofExcept (proposeSourceModels source original)
  require s!"{label}: the model proposal equals the one through Source.find \
    ({proposal.declarations.size} declarations, {proposal.blocks.length} blocks)"
    (match proposeSourceModelsP source (exportSourceBlockEvidence source) original with
     | .ok reference => decide (reference.declarations.toList = proposal.declarations.toList) &&
        reference.blocks.length == proposal.blocks.length
     | .error _ => false)
  let listMembers := source.declarations.all fun ci => match exportSourceEntry ci with
    | .ok e => (streamEntries proposal.declarations).contains e
    | .error _ => false
  require s!"{label}: the entry correspondence decided through the index equals list membership \
    ({listMembers})"
    (decide (SourceEntryCorrespondence source proposal.declarations) == listMembers && listMembers)
  let normalized ← IO.ofExcept (normalizeSourceProjections source witnesses {} proposal.declarations.toList)
  require s!"{label}: the normalisation through the index equals the list lookup's"
    (match normalizeSourceProjectionsP (source := source) (sourceKernelFind source) (fun _ => rfl) witnesses {}
        proposal.declarations.toList with
     | .ok reference => decide (reference.val = normalized.val)
     | .error _ => false)
  let installed ← match installSourceNormalizedComplete accepted.domain.1 (sourcePins input accepted.pins) witnesses with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"{label}: installation refused: {(sourceErrorLabel e).1}")
  let strongProposal ← IO.ofExcept (propose accepted installed)
  let bundle ← match admitSupport accepted.toAdmittedArtifact strongProposal.support with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"{label}: support refused: {supportLabel e}")
  let fast := checkStrongAssociationF installed.env bundle.env strongProposal.names strongProposal.certificates
    strongProposal.operationCertificates strongProposal.elementCertificates strongProposal.levels
  let reference := checkStrongAssociation installed.env bundle.env strongProposal.names strongProposal.certificates
    strongProposal.operationCertificates strongProposal.elementCertificates strongProposal.levels
  require s!"{label}: the strong check on the index and the DAG equals the list and tree check \
    ({fast}, over {installed.env.consts.length} source rows)" (fast == reference && fast == some true)
  -- a forged name map: one source row mapped to another target row; both refuse alike
  let some victim := installed.env.consts.find? (fun c => match c with | .defnInfo .. => true | _ => false)
    | throw (IO.userError s!"{label}: no definition row")
  let some other := installed.env.consts.find? (fun c => match c with
      | .defnInfo .. => c.name != victim.name &&
        !decide (c.toConstantVal.type = victim.toConstantVal.type) | _ => false)
    | throw (IO.userError s!"{label}: one definition row only")
  let forged : _root_.Ix.Kernel.Name → _root_.Ix.Kernel.Name := fun n =>
    if n == victim.name then strongProposal.names other.name else strongProposal.names n
  let fastForged := checkStrongAssociationF installed.env bundle.env forged strongProposal.certificates
    strongProposal.operationCertificates strongProposal.elementCertificates strongProposal.levels
  let referenceForged := checkStrongAssociation installed.env bundle.env forged strongProposal.certificates
    strongProposal.operationCertificates strongProposal.elementCertificates strongProposal.levels
  require s!"{label}: forged: {victim.name} mapped to {other.name}'s target refused ({fastForged}) as by \
    the list check, beside the honest map above" (fastForged == referenceForged && fastForged != some true)

def baseConfig (label : String) (mods : Lean.Name) (ixe dir : String) : Config :=
  { lean := .modules #[mods], ixe, out := s!"{dir}/strong-global-{label}-cover",
    strong := true, strongChanged := false, workers := 4, strongTasks := 4 }

def checks (compiledIxe changedIxe dir : String) : IO Unit := do
  for (label, mods, ixe) in [("BlockDefs", `Tests.Ix.CompileCert.BlockDefs, compiledIxe),
      ("ChangedDefs", `Tests.Ix.CompileCert.ChangedDefs, changedIxe)] do
    let base := baseConfig label mods ixe dir
    let (_, some w) ← runW base | throw (IO.userError "W produced no state")
    let _ ← runStrong base w
    let globalCfg := { base with out := s!"{dir}/strong-global-{label}", strongGlobal := true }
    let _ ← runStrong globalCfg w
    let cover ← sVerdicts base.out
    let global ← sVerdicts globalCfg.out
    let (cones, accepted) ← coneCounts globalCfg.out
    let (coverCones, _) ← coneCounts base.out
    let certified := (global.toList.filter fun (_, v) => v.1 == "S-certified").length
    require s!"{label}: the global cone is the only cone run and it is accepted ({cones} cone, \
      {certified} S-certified; the cover ran {coverCones})" (cones == 1 && accepted == 1 && certified > 0)
    require s!"{label}: every S verdict is the cover's ({global.size} constants)" (sameVerdicts cover global)
    equalities label w
    if label == "ChangedDefs" then
      -- negative, beside the honest run above: every W+ route forged to `direct`
      let rows ← rowsOf s!"{base.out}.tsv"
      let wPlus := (rows.filter fun r => cell r 2 == "certified" && cell r 3 != "" && !sRoute (cell r 3)).map (cell · 0)
      let isWPlus : Std.HashSet String := wPlus.foldl (·.insert ·) {}
      let forgedRoutes := w.names.foldl (fun m n =>
        if isWPlus.contains (toString n) then m.insert n "direct" else m) w.routes
      let wf := { w with routes := forgedRoutes }
      let forgedCover := { base with out := s!"{dir}/strong-global-forged-cover" }
      let forgedGlobal := { base with out := s!"{dir}/strong-global-forged", strongGlobal := true }
      let _ ← runStrong forgedCover wf
      let _ ← runStrong forgedGlobal wf
      let fc ← sVerdicts forgedCover.out
      let fg ← sVerdicts forgedGlobal.out
      let (fCones, fAccepted) ← coneCounts forgedGlobal.out
      let liveRows ← rowsOf s!"{forgedGlobal.out}.strong.live.tsv"
      let firstFailed := match liveRows[0]? with
        | some r => cell r 12 == "failed"
        | none => false
      let forgedCertified := wPlus.filter fun n => ((fg.get? n).map (·.1)) == some "S-certified"
      require s!"forged: {wPlus.size} W+ routes given as direct: the global cone refused (its first \
        cone row), the cover ran as its fallback ({fCones} cones, {fAccepted} accepted), none of the \
        {wPlus.size} S-certified, every verdict the forged cover's; the honest global run above: one \
        accepted cone" (wPlus.size > 0 && firstFailed && fCones > 1 && forgedCertified.isEmpty &&
          sameVerdicts fc fg)
  IO.println s!"strong global: one accepted global cone on BlockDefs and on ChangedDefs, every S verdict \
    the cover's; the fast export, proposal, correspondence, normalisation and strong check equal their \
    list and tree references on both global cones, a forged name map refused by both; with every W+ \
    route forged the global cone is refused and the cover's verdicts result, beside the honest run"

def run (compiledIxe changedIxe dir : String) : IO Unit := do
  try
    checks compiledIxe changedIxe dir
    (← IO.getStdout).flush
    IO.Process.exit 0
  catch e =>
    IO.eprintln s!"{e}"
    (← IO.getStdout).flush
    IO.Process.exit 1

end Tests.Ix.CompileCert.StrongGlobal
