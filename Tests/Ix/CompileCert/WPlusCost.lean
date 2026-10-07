import Tests.Ix.CompileCert.Changed

/-! # Package C: the costs of W+ (C-cutsat, C-fold)

On `Tests.Ix.CompileCert.ChangedDefs` compiled in-process under Pass 3 (as the
`changed` mode does), with the certifier's own functions:

* **C-cutsat (the universe of a row).** With the admitted environment's index,
  `proposeRows` states a type row and an `rfl` row at the universe the certified
  checker infers for Lean's exported type (`checkerSortLevel`), which is also the
  one it infers for the compiled type: typing the row compares the two sorts by
  syntactic equality instead of `Level.leq` (exponential on the nested `imax`
  chain of a long telescope: the Cutsat `brecOn(_k).go`, `plans/review2/M7-C-wplus-cost.md`).
  **Valid neighbour:** both rows of `Reord.Even.brecOn.go` at that universe are
  accepted by the certified fold; **negative:** the type row at the successor of
  that universe is refused.
* **C-fold (the support folded on top of the admission).** `prepareArtifactStaged`
  admits the same artifact as `prepareArtifact` and keeps its fold's phase A;
  `foldSupportStaged` continues it over the support. **Valid neighbour:** on the
  support the pre-pass proposes, it returns the environment `foldSupport`
  (artifact + support folded again) returns, and the W+ decision through it
  accepts the cone with every route as in the `changed` mode; **negatives, each
  beside its neighbour:** a row the fold refuses (an `rfl` row at the successor of
  its universe) and a row named like an artifact constant (a duplicate
  declaration) are refused by the staged fold at the position the full fold
  refuses them at, and with them the W+ decision is refused. -/

namespace Tests.Ix.CompileCert.WPlusCost

open _root_.Ix.CompileCert
open _root_.Ix.CompileCert.Certifier
open Tests.Ix.CompileCert.Changed

/-- The position of a fold's refusal, or `none`. -/
def refusedAt {base support : Array _root_.Ix.Kernel.Declaration} :
    Except FoldError (FoldedSupport base support) → Option Nat
  | .error (.checking _ position) => some position
  | _ => none

def foldedNames {base support : Array _root_.Ix.Kernel.Declaration} :
    Except FoldError (FoldedSupport base support) → Option (List _root_.Ix.Kernel.Name)
  | .ok folded => some (folded.env.consts.map (·.name))
  | .error _ => none

def run : IO Unit := do
  let (env, captured, compiled) ← compile
  let b ← build env captured compiled.env
  let sc1 := prefixName ++ `SC1
  let source : Source := ⟨captured.declarations.filter fun ci => !sc1.isPrefixOf ci.name⟩
  let input := inputOf b source
  -- the staged admission admits what the plain one admits
  let ⟨artifact, staged?⟩ ← match prepareArtifactStaged input.toArtifactInput with
    | .ok a => pure a
    | .error _ => throw (IO.userError "C-fold: the staged admission failed")
  let some staged := staged? | throw (IO.userError "C-fold: the admission did not keep its fold")
  let plain ← match prepareArtifact input.toArtifactInput with
    | .ok a => pure a
    | .error _ => throw (IO.userError "C-fold: the plain admission failed")
  unless plain.declarations.size == artifact.declarations.size &&
      plain.env.consts.map (·.name) == artifact.env.consts.map (·.name) &&
      staged.installed.2.1.env.consts.length == artifact.env.consts.length do
    throw (IO.userError "C-fold: the staged admission's artifact is not the plain one")
  IO.println s!"PASS: staged admission: the artifact of prepareArtifact ({artifact.declarations.size} \
    declarations, {artifact.env.consts.length} constants), phase A kept ({staged.installed.2.2.size} records)"
  -- C-cutsat: the rows of `Reord.Even.brecOn.go` at the checker's universe
  let sh0 := SharedW.ofArtifact input (fun n => b.images.contains n) artifact #[]
  let hints0 := buildHintsW input sh0 (entryPositions sh0.entries) (queriesFor env b.refs) 4 (fun _ => [])
  let fe := _root_.Ix.Kernel.mkFEnv artifact.env
  let goName := prefixName ++ `Reord.Even.brecOn.go
  let some goCi := env.find? goName | throw (IO.userError "missing Reord.Even.brecOn.go")
  let pg ← proposeRows env sh0 hints0 goCi (some fe)
  let some (_, typeRow) := pg.rows.find? (·.1 == "type")
    | throw (IO.userError s!"brecOn.go: no type row ({pg.failure})")
  let some (_, rflRow) := pg.rows.find? (·.1 == "rfl")
    | throw (IO.userError s!"brecOn.go: no rfl row ({pg.failure})")
  let .thmDecl tcv _ := typeRow | throw (IO.userError "brecOn.go: the type row is not a theorem")
  let some (_, .sort level, ixType, leanType) := eqParts tcv.type
    | throw (IO.userError "brecOn.go: the type row is not an equation of sorts")
  unless (checkerSortLevel fe leanType).toOption == some level &&
      (checkerSortLevel fe ixType).toOption == some level do
    throw (IO.userError "brecOn.go: the type row is not at the universe the checker infers")
  let .thmDecl rcv _ := rflRow | throw (IO.userError "brecOn.go: the rfl row is not a theorem")
  let some (rflLevel, _, _, _) := eqParts rcv.type | throw (IO.userError "brecOn.go: the rfl row is not an equation")
  unless rflLevel == level do throw (IO.userError "brecOn.go: the rfl row is not at the checker's universe")
  let (_, rowsOk) ← decideW env b input b.images artifact (#[typeRow, rflRow].map (renameRow 200000))
  match rowsOk with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"brecOn.go: the rows at the checker's universe were refused: {declineLabel e}")
  let some above := supportRow tcv.name tcv.levelParams
      (kernelEq (.succ (.succ level)) (.sort (.succ level)) ixType leanType)
    | throw (IO.userError "brecOn.go: no type row at the successor universe")
  let (_, aboveResult) ← decideW env b input b.images artifact #[renameRow 200001 above]
  expectRefused "the type row of Reord.Even.brecOn.go at the successor of the checker's universe" aboveResult isFold
  IO.println s!"PASS: checker universe: the type and rfl rows of Reord.Even.brecOn.go at the universe the \
    checker infers for both types ({kernelLevelNodes level} nodes) accepted (valid neighbour)"
  -- C-fold: the staged fold returns the environment of the full fold, and the decision through it
  let (pre, valid) ← decideW env b input b.images artifact (staged := some staged)
  match valid with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"C-fold: the W+ decision through the staged fold refused the cone: {declineLabel e}")
  for (n, wanted) in expectedRoutes do
    unless pre.routes[n]? == some wanted do
      throw (IO.userError s!"C-fold: {n}: route {pre.routes[n]?}, expected {wanted}")
  let (support, _, _) := finalSupport input.source.names.toArray pre
  unless support.size > 0 do throw (IO.userError "C-fold: the fixture proposes no support row")
  let full := foldSupport artifact support
  let continued := foldSupportStaged artifact staged support
  match foldedNames full, foldedNames continued with
  | some a, some c =>
    unless a == c do throw (IO.userError "C-fold: the staged fold's environment differs from the full fold's")
  | _, _ => throw (IO.userError "C-fold: a fold refused the proposed support")
  IO.println s!"PASS: staged fold: {support.size} support rows folded on top of the admission; the environment \
    of the full fold ({((foldedNames full).map (·.length)).getD 0} constants); the W+ decision through it accepts the cone \
    with its {expectedRoutes.length} routes (valid neighbour)"
  -- negatives: a refused row, a duplicate declaration; the position of the full fold
  let some wrong := supportRow rcv.name rcv.levelParams
      (match eqParts rcv.type with
       | some (l, carrier, left, right) => kernelEq (.succ l) carrier left right
       | none => rcv.type)
    | throw (IO.userError "C-fold: no rfl row at the successor universe")
  let artifactName? : Option _root_.Ix.Kernel.Name := artifact.declarations.findSome? fun d => match d with
    | .defnDecl cv' _ _ => some cv'.name
    | _ => none
  let some artifactName := artifactName? | throw (IO.userError "C-fold: the artifact has no definition")
  let duplicate : _root_.Ix.Kernel.Declaration := match typeRow with
    | .thmDecl cv proof => .thmDecl { cv with name := artifactName } proof
    | d => d
  for (label, bad) in [("an rfl row at the successor of its universe", renameRow 300000 wrong),
      ("a row named like an artifact definition (duplicate declaration)", duplicate)] do
    let badSupport := support.push bad
    let fullBad := foldSupport artifact badSupport
    let stagedBad := foldSupportStaged artifact staged badSupport
    match refusedAt fullBad, refusedAt stagedBad with
    | some p, some q =>
      unless p == q do throw (IO.userError s!"C-fold: {label}: refused at {q} by the staged fold, at {p} by the full fold")
      IO.println s!"PASS: C-fold: {label}: refused by the staged fold at position {q}, as by the full fold"
    | _, _ => throw (IO.userError s!"C-fold: {label}: not refused by both folds")
  let (_, wrongResult) ← decideW env b input b.images artifact #[renameRow 300001 wrong] (staged := some staged)
  expectRefused "the W+ decision through the staged fold with a refused row" wrongResult isFold
  IO.println s!"wplus-cost: rows at the checker's universe accepted, one above it refused; staged admission = \
    plain admission; staged fold = full fold on {support.size} rows, W+ accepted through it; 3 refusals at the \
    full fold's positions"

/-- The resident set of this process (kB, `/proc/self/status`; 0 elsewhere). -/
def residentKb (field : String := "VmRSS") : IO Nat := do
  let text ← try IO.FS.readFile "/proc/self/status" catch _ => pure ""
  for line in text.splitOn "\n" do
    if line.startsWith s!"{field}:" then
      return (((line.drop (field.length + 1)).toString.trimAscii.toString).takeWhile Char.isDigit).toNat!
  return 0

/-- Measurement (not a `check-cert` step): `compile-cert-c1 wplus-cost-measure <env.ixe> [--plain]`
admits the records the certifier would select from an artifact (`prepareArtifactStaged`, or
`prepareArtifact` with `--plain`), then folds one support row (`_ix_fold_probe : Sort 0 = Sort 0`,
proof `Eq.refl`) on top of it both ways, `foldSupportStaged` (the admission's fold continued) and
`foldSupport` (artifact and row folded again), reporting each phase's time and the resident set. -/
def measure (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "wplus-cost-measure <env.ixe> [--plain]")
  let plain := args.contains "--plain"
  let t0 ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile path
  let produced ← IO.ofExcept (Ixon.deEnv bytes)
  let mut store : Benchmarks.Kernel.CheckIxeStep.RecordStore := {}
  for (address, lazy) in produced.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let pins ← IO.ofExcept _root_.Ix.Kernel.Reader.defaultPins
  let pre ← IO.ofExcept _root_.Ix.Kernel.Reader.builtinPrelude
  let readerHints := Benchmarks.Kernel.CheckIxeStep.Hints.ofStore store produced.anonHints
  let s := Benchmarks.Kernel.CheckIxeStep.setup store (produced.blobs[·]?) pins pre readerHints.lookup
  let (records, _) := selectRecords s
  let recordBytes := records.toList.map fun (a, c) => (a, Ixon.serConstant c)
  let blobs := produced.blobs.toList
  let limits : _root_.Ix.Kernel.Admission.Limits := ⟨recordBytes.length + 1, blobs.length + 1,
    recordBytes.foldl (fun n (_, b) => n + b.size) 0 + blobs.foldl (fun n (_, b) => n + b.size) 0 + 1,
    recordBytes.foldl (fun n (_, b) => max n b.size) 0 + 1, 1 <<< 24⟩
  let ai : ArtifactInput := { limits, records := recordBytes, blobs, hint := readerHints.lookup }
  let t1 ← IO.monoMsNow
  IO.println s!"[measure] {path}: {records.size} records selected; {t1 - t0} ms; rss {← residentKb} kB"
  let admitted := (Task.spawn (prio := .dedicated) fun _ =>
    if plain then
      (prepareArtifact ai).map fun a => (⟨a, none⟩ : (a : AdmittedArtifact ai) × Option (StagedAdmission a))
    else prepareArtifactStaged ai).get
  let ⟨artifact, staged?⟩ ← match admitted with
    | .ok a => pure a
    | .error _ => throw (IO.userError "admission failed")
  let t2 ← IO.monoMsNow
  IO.println s!"[measure] admission ({if plain then "plain" else "staged"}): {artifact.declarations.size} \
    declarations; {t2 - t1} ms; rss {← residentKb} kB, peak {← residentKb "VmHWM"} kB"
  let probeLevel : _root_.Ix.Kernel.Level := .succ .zero
  let some row := supportRow (_root_.Ix.Kernel.Name.anonymous.str "_ix_fold_probe") []
      (kernelEq (.succ probeLevel) (.sort probeLevel) (.sort .zero) (.sort .zero))
    | throw (IO.userError "no probe row")
  let report (label : String) {base : Array _root_.Ix.Kernel.Declaration}
      (r : Except FoldError (FoldedSupport base #[row])) (ms : Nat) : IO Unit := do
    match r with
    | .ok folded =>
      IO.println s!"[measure] {label}: accepted, {folded.env.consts.length} constants; {ms} ms; rss \
        {← residentKb} kB, peak {← residentKb "VmHWM"} kB"
    | .error (.checking _ position) => IO.println s!"[measure] {label}: refused at {position}; {ms} ms"
    | .error (.setup r) => IO.println s!"[measure] {label}: setup {r}"
  if let some staged := staged? then
    let t3 ← IO.monoMsNow
    let r := (Task.spawn (prio := .dedicated) fun _ => foldSupportStaged artifact staged #[row]).get
    let n := match r with | .ok f => f.env.consts.length | .error _ => 0
    let t4 ← IO.monoMsNow
    report s!"support fold continued from the admission (foldSupportStaged, {n})" r (t4 - t3)
  let t5 ← IO.monoMsNow
  let r := (Task.spawn (prio := .dedicated) fun _ => foldSupport artifact #[row]).get
  let n := match r with | .ok f => f.env.consts.length | .error _ => 0
  let t6 ← IO.monoMsNow
  report s!"support fold with the artifact again (foldSupport, {n})" r (t6 - t5)
  IO.println s!"[measure] total {t6 - t0} ms"
  -- the fold's two phases apart, on a fresh read: phase A, then phase B with phase A's memo
  -- state dropped (as `checkDecls` runs it) or kept alive (as a staged admission holds it)
  if args.contains "--phases" then
    let natPins ← IO.ofExcept _root_.Ix.Kernel.Reader.builtinNatOpPins
    for keep in [false, true] do
      let task ← IO.asTask (prio := .dedicated) do
        let t0 ← IO.monoMsNow
        match _root_.Ix.Kernel.Admission.readStream artifact.pins artifact.prelude artifact.constants
            ai.blobs ai.hint with
        | .error _ => return "read failed"
        | .ok decls =>
          let prepared := _root_.Ix.Kernel.Frontend.preparePrelude artifact.prelude.ix decls
          let t1 ← IO.monoMsNow
          match (prepared.foldlM (_root_.Ix.Kernel.Cached.annotDeclStep .verified natPins)
              (0, _root_.Ix.Kernel.mkFEnv _root_.Ix.Kernel.Env.empty, #[])) {} with
          | .error _ => return "phase A refused"
          | .ok (pa, sa) =>
            let t2 ← IO.monoMsNow
            match _root_.Ix.Kernel.Cached.checkPendingList .verified pa.2.1 pa.2.2.toList with
            | .error _ => return "phase B refused"
            | .ok () =>
              let t3 ← IO.monoMsNow
              let kept := if keep then sa.ienv.size else 0
              return s!"read {t1 - t0} ms, phase A {t2 - t1} ms ({pa.2.2.size} records), phase B {t3 - t2} ms; \
                rss {← residentKb} kB (ienv kept: {kept})"
      match ← IO.wait task with
      | .ok text => IO.println s!"[measure] phases, phase A's state {if keep then "kept" else "dropped"}: {text}"
      | .error e => IO.println s!"[measure] phases: {e}"

end Tests.Ix.CompileCert.WPlusCost
