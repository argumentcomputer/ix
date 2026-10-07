import Ix.CompileCert.Certifier
import Ix.CompileDriver
import Ix.Meta
import Benchmarks.Kernel.CheckIxeStep
import Tests.Ix.CompileCert.ChangedDefs
import Tests.Ix.CompileCert.LoweringDefs

/-! # W+ on compiler output: changed constants (M5)

`Tests.Ix.CompileCert.ChangedDefs` is compiled in-process with the Lean compiler
under Pass 3 (`compileLeanConsts … (pass3? := some true)`, the default), its
bytes written to `$C1_OUTPUT_DIR/changed.ixe` (the `certify-changed` step of
`lake run check-cert` runs `compile-certify` on them). Then, on the same
compiled cone, with the certifier's own functions (`imageClaims`,
`wPrePass`, `finalSupport`, `checkIndexed'`):

* **positive:** the W+ decision accepts the cone; every root is certified and
  the route of each changed constant is the expected one (asserted per name);
  the transported clique without Lean's `eq_def`s (`SC1`) is Unsupported with
  its named class, not Rejected;
* **negatives, each beside its valid neighbour (the unmutated decision):**
  a forged equation (a definition's source value replaced by another value of
  its type: the checker refuses the `rfl` row; with the row forced into the
  support the certified fold refuses it), a theorem with another statement
  (the type row is refused), a kind forgery (a recursor's image record stored
  as a theorem), lying image claims (an unchanged recursor claimed, an image
  unclaimed), and a changed block whose Ix block holds a member foreign to
  the Lean block (containment);
* **the certifier's rows (M5 §5):** the rows of an alias fiber (two Lean
  constants, one Ix constant) are proposed under one name: as they are, the
  certified fold refuses the duplicate, named apart they are accepted (and the
  certifier names its support rows apart); a row's universe is a small level
  equal to Lean's, and the same row at the successor level is refused; at a
  zero pre-screen time budget no row is checked and every changed constant that
  needs one is Unsupported, never Rejected or certified, while a definite
  refusal beside a row over the budget stays Rejected. -/

namespace Tests.Ix.CompileCert.Changed

open _root_.Ix.CompileCert
open _root_.Ix.CompileCert.Certifier

def prefixName : Lean.Name := `Tests.Ix.CompileCert.ChangedDefs

def roots : List Lean.Name :=
  [`Reord.three, `Reord.Even.isZero, `Reord.viaRec_zero,
   `ReordProp.even_two, `ReordProp.even_true,
   `Split.len2, `Split.lenCopy2, `Split.viaRec_nil,
   `Collapse.f_ab, `Collapse.A.isNil,
   `Evap.useRec_ex, `Evap.A.isMk,
   `WF0.wa_unfold, `WF0.wb_unfold, `WF0.wa_zero,
   `WF1.wa_unfold, `WF1.wb_unfold, `WF1.wa_zero,
   `SC0.ev4, `SC0.unfold_used].map (prefixName ++ ·)

/-- Expected Unsupported (with this class): the transported structural clique
with no `eq_def` in Lean's environment. -/
def expectedUnsupported : List Lean.Name := [`SC1.ev, `SC1.od].map (prefixName ++ ·)

/-- The route of each changed constant, as the certifier reports it. -/
def expectedRoutes : List (Lean.Name × String) :=
  [(`Reord.Even, "direct, changed-block"), (`Reord.Odd, "direct, changed-block"),
   (`Reord.Even.rec, "equations:rfl"), (`Reord.Odd.rec, "equations:rfl"),
   (`Reord.Even.casesOn, "equations:rfl"), (`Reord.Even.below, "equations:rfl"),
   (`Reord.Even.brecOn, "equations:rfl, type-row"), (`Reord.Even.brecOn.go, "equations:rfl, type-row"),
   (`ReordProp.Even, "direct, changed-block"), (`ReordProp.Even.rec, "equations:rfl"),
   (`ReordProp.even_true, "theorem"),
   (`Split.A, "direct, changed-block"), (`Split.B, "direct, changed-block"),
   (`Split.A.rec, "equations:rfl"), (`Split.A.len._f, "equations:rfl, type-row"),
   (`Split.A.len, "equations:rfl"), (`Split.A.lenCopy, "equations:rfl"),
   (`Split.A.lenCopy._f, "equations:rfl, type-row"),
   (`Collapse.A, "direct, changed-block"), (`Collapse.B, "direct, changed-block"),
   (`Collapse.A.rec, "equations:rfl"), (`Collapse.B.rec, "equations:rfl"),
   (`Evap.A, "direct, changed-block"), (`Evap.A.rec_1, "equations:rfl"),
   (`WF0.wa, "equations:eq_def"), (`WF0.wb, "equations:eq_def"), (`WF0.wa.eq_def, "theorem"),
   (`WF1.wa, "direct"), (`SC0.ev.eq_def, "direct"),
   (`SC0.ev, "direct")].map fun (n, r) => (prefixName ++ n, r)

/-- Compile the fixture's cone under Pass 3 and write `changed.ixe`. -/
def compile : IO (Lean.Environment × Source × Ix.CompileM.LeanPipelineOut) := do
  let env ← getCompileEnv #[prefixName]
  let captured ← IO.ofExcept (captureCone env.find? (roots ++ expectedUnsupported) 128)
  let compiled ← match ← _root_.Ix.CompileM.compileLeanConsts
      (captured.source.declarations.map (fun ci => (ci.name, ci))) (numWorkers := 1) (pass3? := some true) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compiler failed: {e}")
  unless compiled.ungroundedCount == 0 do throw (IO.userError "compiler output contains ungrounded declarations")
  IO.println s!"compiled {captured.source.declarations.length} declarations: {compiled.bytes.size} bytes; \
    Blake3: {Address.blake3 compiled.bytes}"
  if let some directory ← IO.getEnv "C1_OUTPUT_DIR" then
    IO.FS.createDirAll directory
    IO.FS.writeBinFile (System.FilePath.mk directory / "changed.ixe") compiled.bytes
  return (env, captured.source, compiled)

/-- The certifier's construction for one cone: records the reader keeps, the
name map, the image claims, the admission. -/
structure Built where
  store : Benchmarks.Kernel.CheckIxeStep.RecordStore
  namedAddr : Std.HashMap Lean.Name Address
  entries : Std.HashMap Lean.Name MapEntry
  refs : Std.HashMap Lean.Name (Array Lean.Name)
  artifactInput : ArtifactInput
  images : Std.HashSet Lean.Name

def build (env : Lean.Environment) (source : Source) (produced : Ixon.Env) : IO Built := do
  let mut store : Benchmarks.Kernel.CheckIxeStep.RecordStore := {}
  for (address, lazy) in produced.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let pins ← IO.ofExcept _root_.Ix.Kernel.Reader.defaultPins
  let pre ← IO.ofExcept _root_.Ix.Kernel.Reader.builtinPrelude
  let readerHints := Benchmarks.Kernel.CheckIxeStep.Hints.ofStore store produced.anonHints
  let s := Benchmarks.Kernel.CheckIxeStep.setup store (produced.blobs[·]?) pins pre readerHints.lookup
  let (records, failures) := selectRecords s
  unless failures.isEmpty do throw (IO.userError s!"the reader declined {failures.size} records")
  let mut namedAddr : Std.HashMap Lean.Name Address := {}
  let mut entries : Std.HashMap Lean.Name MapEntry := {}
  for ci in source.declarations do
    let some named := produced.named[_root_.Ix.Name.fromLeanName ci.name]?
      | throw (IO.userError s!"producer omitted {ci.name}")
    namedAddr := namedAddr.insert ci.name named.addr
    let some target := _root_.Ix.Kernel.Reader.resolve s.cx.store named.addr
      | throw (IO.userError s!"unresolved {ci.name}")
    entries := entries.insert ci.name ⟨ci.name, named.addr, target⟩
  let recordBytes := records.toList.map fun (a, c) => (a, Ixon.serConstant c)
  let blobs := produced.blobs.toList
  let limits : _root_.Ix.Kernel.Admission.Limits := ⟨recordBytes.length + 1, blobs.length + 1,
    recordBytes.foldl (fun n (_, b) => n + b.size) 0 + blobs.foldl (fun n (_, b) => n + b.size) 0 + 1,
    recordBytes.foldl (fun n (_, b) => max n b.size) 0 + 1, 1 <<< 24⟩
  let names := source.declarations.toArray.map (·.name)
  let refs := source.declarations.foldl (fun m ci => m.insert ci.name (refsOf ci)) {}
  return { store, namedAddr, entries, refs
           artifactInput := { limits, records := recordBytes, blobs, hint := readerHints.lookup }
           images := imageClaims env store names namedAddr }

def inputOf (b : Built) (source : Source) : Input :=
  { toArtifactInput := b.artifactInput, source, roots := source.names,
    map := source.declarations.filterMap (b.entries[·.name]?) }




/-- The W+ decision on an input as the certifier makes it (pre-pass, support,
`checkIndexed'`), with the pre-pass's routes and diagnoses. -/
def decideW (env : Lean.Environment) (b : Built) (input : Input) (images : Std.HashSet Lean.Name)
    (artifact : AdmittedArtifact input.toArtifactInput) (extraSupport : Array _root_.Ix.Kernel.Declaration := #[])
    (rowBudget : Lean.Name → String → Nat := fun _ _ => defaultRowBudget) :
    IO (PrePass × Except Decline' Unit) := do
  let quiet : String → IO Unit := fun _ => pure ()
  let pre ← wPrePass env b.entries input images artifact (queriesFor env b.refs) 4 quiet (rowBudget := rowBudget)
  let names := input.source.names.toArray
  let (sup, _, rowsFinal) := finalSupport names pre
  let support := sup ++ extraSupport
  let imagesFn : Lean.Name → Bool := fun n => images.contains n
  let sh := SharedW.ofArtifact input imagesFn artifact support
  let entryPos := entryPositions sh.entries
  let extraRows : Std.HashMap Lean.Name (Array Nat) := rowsFinal
  let hints := buildHintsW input sh entryPos (queriesFor env b.refs) 4
    (fun n => rowsAtWith b.entries entryPos sh.reader extraRows sh.entries.size n ++
      ((List.range extraSupport.size).map (sh.entries.size + sup.size + ·)))
  return (pre, (checkIndexed' input imagesFn artifact support hints).map fun _ => ())

def declineLabel : Decline' → String
  | .fold (.checking e position) => s!"certified fold refused at {position}: {(Benchmarks.Kernel.CheckIxeStep.checkOutcome e).2.take 120}"
  | .fold (.setup r) => s!"fold setup: {r}"
  | .base .sourceDomain => "source domain"
  | .base .mapMismatch => "map"
  | .base .correspondence => "correspondence"
  | .base .definitionGroupCorrespondence => "definition groups"
  | .base (.setup r) => s!"setup: {r}"
  | .base _ => "other"

def expectRefused (label : String) (result : Except Decline' Unit) (wanted : Decline' → Bool) : IO Unit := do
  match result with
  | .ok () => throw (IO.userError s!"{label}: the forged input was accepted")
  | .error e =>
    unless wanted e do throw (IO.userError s!"{label}: refused for another reason: {declineLabel e}")
    IO.println s!"PASS: {label}: refused ({declineLabel e})"

def isFold : Decline' → Bool
  | .fold _ => true
  | _ => false

def isBase (d : Decline) : Decline' → Bool
  | .base e => match d, e with
    | .mapMismatch, .mapMismatch | .correspondence, .correspondence => true
    | _, _ => false
  | _ => false

def replace (source : Source) (ci : Lean.ConstantInfo) : Source :=
  ⟨source.declarations.map fun c => if c.name == ci.name then ci else c⟩

/-- `λ xs, k` for a type `∀ xs, B` (a forged value of the type's arity). -/
def constLambda : Lean.Expr → Lean.Expr → Lean.Expr
  | .forallE n d b bi, k => .lam n d (constLambda b k) bi
  | _, k => k


/-- M4-d §8 item 5: a projection onto a proof field of a mutual structure-like
is a *theorem* in Lean 4.34.1 (`Sized.ok`); the reader rewrites its record's
value (`projRewrite`) and keeps its statement, so the theorem-statement match
covers it. Its own cone, compiled in-process. -/
def runSized : IO Unit := do
  let lowering : Lean.Name := `Tests.Ix.CompileCert.LoweringDefs
  let ok := lowering ++ `Sized.ok
  let env ← getCompileEnv #[lowering]
  let captured ← IO.ofExcept (captureCone env.find? [ok, lowering ++ `Sized.vec, lowering ++ `Rose.children] 128)
  let compiled ← match ← _root_.Ix.CompileM.compileLeanConsts
      (captured.source.declarations.map (fun ci => (ci.name, ci))) (numWorkers := 1) (pass3? := some true) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compiler failed: {e}")
  let b ← build env captured.source compiled.env
  let input := inputOf b captured.source
  let artifact ← match prepareArtifact input.toArtifactInput with
    | .ok a => pure a
    | .error _ => throw (IO.userError "admission of the LoweringDefs cone failed")
  let (pre, result) ← decideW env b input b.images artifact
  match result with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"W+ refused the LoweringDefs cone: {declineLabel e}")
  match pre.routes[ok]? with
  | some "theorem" =>
    IO.println s!"PASS: Sized.ok (projection onto a proof field of a mutual structure-like, a theorem) \
      certified by its statement; the cone of {captured.source.declarations.length} declarations accepted \
      ({b.images.size} image claims, {pre.support.size} support rows)"
  | other => throw (IO.userError s!"Sized.ok: route {other}, expected theorem")

def run : IO Unit := do
  let (env, captured, compiled) ← compile
  let b ← build env captured compiled.env
  IO.println s!"image claims: {b.images.size}"
  -- the certified part of the cone: everything but the expected-Unsupported clique and its users
  let sc1 := prefixName ++ `SC1
  let source : Source := ⟨captured.declarations.filter fun ci => !sc1.isPrefixOf ci.name⟩
  let input := inputOf b source
  let artifact ← match prepareArtifact input.toArtifactInput with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"admission of the compiled cone failed: {match e with | .admission err => s!"admission {err}" | .reading err => s!"reading {err}" | .setup r => s!"setup {r}" | .malformedInput r => s!"malformed {r}" | .decoding _ => "decoding" | _ => "other"}")
  -- positive: the W+ decision, routes per name
  let (pre, valid) ← decideW env b input b.images artifact
  match valid with
  | .ok () => IO.println s!"PASS: valid neighbour: W+ accepts the cone ({source.declarations.length} declarations, \
      {pre.support.size} support rows, {b.images.size} image claims)"
  | .error e => throw (IO.userError s!"the W+ decision refused the valid cone: {declineLabel e}")
  unless pre.failed.isEmpty do
    throw (IO.userError s!"pre-pass failures on the valid cone: {pre.failed.toList.map (·.1)}")
  for root in roots do
    unless pre.routes.contains root do throw (IO.userError s!"root {root} has no route")
  let mut checkedRoutes := 0
  for (n, wanted) in expectedRoutes do
    match pre.routes[n]? with
    | some r =>
      unless r == wanted do throw (IO.userError s!"{n}: route {r}, expected {wanted}")
      checkedRoutes := checkedRoutes + 1
    | none => throw (IO.userError s!"{n}: no route (expected {wanted})")
  IO.println s!"PASS: {roots.length} roots certified; {checkedRoutes} routes as expected"
  -- the expected Unsupported clique, with its class
  let inputAll := inputOf b captured
  let preAll ← wPrePass env b.entries inputAll b.images artifact (queriesFor env b.refs) 4 (fun _ => pure ())
  for n in expectedUnsupported do
    match preAll.failed[n]? with
    | some (.unsupported c) =>
      unless c == "changed definition: transported clique member without eq_def" do
        throw (IO.userError s!"{n}: unsupported with class {c}")
      IO.println s!"PASS: expected unsupported {n}: {c}"
    | some v => throw (IO.userError s!"{n}: {v.word} {v.cause}, expected unsupported")
    | none => throw (IO.userError s!"{n}: certified, expected unsupported")
  -- N1: a forged equation: `useRec`'s source value replaced by another value of its type
  let useRec := prefixName ++ `Evap.useRec
  let some (.defnInfo d) := env.find? useRec | throw (IO.userError "missing useRec")
  let other : Lean.Expr := .lam `x (.const (prefixName ++ `Evap.A) []) (.lit (.natVal 0)) .default
  let forgedSource := replace source (.defnInfo { d with value := other })
  let forged := { input with source := forgedSource }
  let (preF, resultF) ← decideW env b forged b.images artifact
  match preF.failed[useRec]? with
  | some (.rejected c) => IO.println s!"PASS: forged equation for useRec: rejected ({c.take 160})"
  | some v => throw (IO.userError s!"forged equation: {v.word} {v.cause}")
  | none => throw (IO.userError s!"forged equation: useRec passed the pre-pass by route {preF.routes[useRec]?}; refusal {preF.refusals[useRec]?}; rows {preF.rowsOf[useRec]?}")
  expectRefused "forged equation for useRec (row dropped by the pre-screen)" resultF
    (isBase .correspondence)
  -- the same forged row forced into the support: the certified fold refuses it
  let shF := SharedW.ofArtifact forged (fun n => b.images.contains n) artifact #[]
  let entryPosF := entryPositions shF.entries
  let hintsF := buildHintsW forged shF entryPosF (queriesFor env b.refs) 4 (fun _ => [])
  let p ← proposeRows env shF hintsF (.defnInfo { d with value := other })
  let forcedRows := p.rows.map (·.2)
  unless forcedRows.size == 1 do throw (IO.userError s!"forged equation: {forcedRows.size} rows proposed")
  let (_, resultForced) ← decideW env b forged b.images artifact forcedRows
  expectRefused "forged equation row for useRec forced into the support" resultForced isFold
  -- N2: a theorem with another statement
  let evenTrue := prefixName ++ `ReordProp.even_true
  let some (.thmInfo t) := env.find? evenTrue | throw (IO.userError "missing even_true")
  let otherStatement : Lean.Expr := .forallE `h (.const ``True []) (.const ``True []) .default
  let (preT, resultT) ← decideW env b
    { input with source := replace source (.thmInfo { t with type := otherStatement }) } b.images artifact
  match preT.failed[evenTrue]? with
  | some (.rejected c) => IO.println s!"PASS: theorem with another statement: rejected ({c.take 160})"
  | some v => throw (IO.userError s!"theorem statement: {v.word} {v.cause}")
  | none => throw (IO.userError "theorem statement: even_true passed the pre-pass")
  expectRefused "theorem with another statement" resultT (isBase .correspondence)
  -- N3: a kind forgery: the record of a recursor's image stored as a theorem
  let evenRec := prefixName ++ `ReordProp.Even.rec
  let some recAddr := b.namedAddr[evenRec]? | throw (IO.userError "missing Even.rec address")
  let some recRecord := b.store[recAddr]? | throw (IO.userError "missing Even.rec record")
  let .defn image := recRecord.info | throw (IO.userError "Even.rec is not stored as a definition")
  let thmRecord : Ixon.Constant := { recRecord with info := .defn { image with kind := .thm } }
  let kindInput : Input := { input with records := input.records.map fun (a, bytes) =>
    if a == recAddr then (a, Ixon.serConstant thmRecord) else (a, bytes) }
  match prepareArtifact kindInput.toArtifactInput with
  | .error _ => IO.println "PASS: kind forgery: the image stored as a theorem is refused at admission"
  | .ok kindArtifact =>
    let (preK, resultK) ← decideW env b kindInput b.images kindArtifact
    match preK.failed[evenRec]? with
    | some (.rejected c) => IO.println s!"PASS: kind forgery: Even.rec rejected ({c.take 120})"
    | some v => throw (IO.userError s!"kind forgery: {v.word} {v.cause}")
    | none => throw (IO.userError "kind forgery: Even.rec passed the pre-pass")
    expectRefused "kind forgery (recursor image stored as a theorem)" resultK (isBase .mapMismatch)
  -- N4: lying image claims
  let some unchanged := source.declarations.find? fun ci => match ci with
      | .recInfo _ => !b.images.contains ci.name
      | _ => false
    | throw (IO.userError "no unchanged recursor in the cone")
  let (_, resultClaim) ← decideW env b input (b.images.insert unchanged.name) artifact
  expectRefused s!"lying image claim on the unchanged recursor {unchanged.name}" resultClaim
    (isBase .mapMismatch)
  let (_, resultUnclaim) ← decideW env b input (b.images.erase evenRec) artifact
  expectRefused "image unclaimed (ReordProp.Even.rec)" resultUnclaim (isBase .mapMismatch)
  -- N5: a changed block whose Ix block holds a member foreign to the Lean block
  let even := prefixName ++ `Reord.Even
  let some (.inductInfo iv) := env.find? even | throw (IO.userError "missing Reord.Even")
  let foreignSource := replace source (.inductInfo { iv with all := [even] })
  let foreign := { input with source := foreignSource }
  let sh := SharedW.ofArtifact input (fun n => b.images.contains n) artifact #[]
  let shForeign := SharedW.ofArtifact foreign (fun n => b.images.contains n) artifact #[]
  unless Decidable.decide (ChangedBlockMatch sh.cx sh.state (.inductInfo iv)) do
    throw (IO.userError "valid neighbour: Reord.Even's changed block does not match")
  if Decidable.decide (ChangedBlockMatch shForeign.cx shForeign.state (.inductInfo { iv with all := [even] })) then
    throw (IO.userError "containment: a block with a foreign member matched")
  IO.println "PASS: containment: Reord.Even's Ix block holds Reord.Odd, foreign to a Lean block {Reord.Even}; \
    valid neighbour matches"
  let (_, resultForeign) ← decideW env b foreign b.images artifact
  expectRefused "changed block with a foreign member (containment)" resultForeign (isBase .correspondence)
  -- the certifier's own rows, proposed against the valid cone (no support yet)
  let sh0 := SharedW.ofArtifact input (fun n => b.images.contains n) artifact #[]
  let hints0 := buildHintsW input sh0 (entryPositions sh0.entries) (queriesFor env b.refs) 4 (fun _ => [])
  let rowNames (rs : Array _root_.Ix.Kernel.Declaration) : List _root_.Ix.Kernel.Name :=
    rs.toList.filterMap fun d => match d with
      | .thmDecl cv _ => some cv.name
      | _ => none
  -- F1: an alias fiber of changed constants (`Split.A.len._f`, `Split.A.lenCopy._f`: one Ix
  -- constant, one reader name). As proposed, their rows share their names; the certifier names
  -- the support rows apart (`renameRow`). Valid neighbour: the decision above (both certified,
  -- their support rows under four names) and the proposed rows named apart; negative: the
  -- proposed rows as they are (the certified fold refuses the duplicate declaration).
  let lenF := prefixName ++ `Split.A.len._f
  let copyF := prefixName ++ `Split.A.lenCopy._f
  unless (b.namedAddr[lenF]?).isSome && b.namedAddr[lenF]? == b.namedAddr[copyF]? do
    throw (IO.userError "fixture: Split.A.len._f and Split.A.lenCopy._f are not one Ix constant")
  let some (.defnInfo lenD) := env.find? lenF | throw (IO.userError "missing Split.A.len._f")
  let some copyCi := env.find? copyF | throw (IO.userError "missing Split.A.lenCopy._f")
  let rowsLen := (← proposeRows env sh0 hints0 (.defnInfo lenD)).rows.map (·.2)
  let rowsCopy := (← proposeRows env sh0 hints0 copyCi).rows.map (·.2)
  unless rowsLen.size == 2 && rowNames rowsLen == rowNames rowsCopy do
    throw (IO.userError s!"alias fiber: proposed rows {rowNames rowsLen} and {rowNames rowsCopy}, \
      expected two each under the same names")
  let supportNames (n : Lean.Name) : List _root_.Ix.Kernel.Name :=
    rowNames ((pre.rowsOf.getD n #[]).filterMap (pre.support[·]?))
  let (lenNames, copyNames) := (supportNames lenF, supportNames copyF)
  unless lenNames.length == 2 && copyNames.length == 2 && lenNames.all (!copyNames.contains ·) do
    throw (IO.userError s!"alias fiber: support rows {lenNames} and {copyNames} are not named apart")
  let (_, resultDup) ← decideW env b input b.images artifact (rowsLen ++ rowsCopy)
  expectRefused "alias fiber rows under the one name they are proposed with" resultDup isFold
  let (_, resultApart) ← decideW env b input b.images artifact
    (rowsLen.map (renameRow 100000) ++ rowsCopy.map (renameRow 100001))
  match resultApart with
  | .ok () => IO.println s!"PASS: alias fiber {lenF} = {copyF} (one Ix constant): both certified, their \
      support rows named apart; the same proposed rows named apart are accepted (valid neighbour)"
  | .error e => throw (IO.userError s!"alias fiber: the rows named apart were refused: {declineLabel e}")
  -- F2: the universe of a row, a small level equal to Lean's (untrusted: the fold validates it)
  let u : Lean.Name := `u
  let pu := Lean.Level.param u
  let chain := (List.range 40).foldl (fun acc _ => Lean.Level.imax (.max (.succ .zero) pu) acc) pu
  unless smallEquivalentLevel [u] chain == some pu do
    throw (IO.userError s!"small level: a 40-fold imax chain gave {smallEquivalentLevel [u] chain}, expected u")
  unless smallEquivalentLevel [u] (.imax (.succ pu) pu) == some (.imax (.succ pu) pu) do
    throw (IO.userError "small level: imax (u+1) u (a casesOn's type) not found")
  unless smallEquivalentLevel [u] (.succ (.succ (.succ (.succ (.succ pu))))) == none do
    throw (IO.userError "small level: u+5 matched a small candidate")
  let casesOn := prefixName ++ `Reord.Even.casesOn
  let some casesCi := env.find? casesOn | throw (IO.userError "missing Reord.Even.casesOn")
  let pc ← proposeRows env sh0 hints0 casesCi
  let some (_, rflRow) := pc.rows.find? (·.1 == "rfl")
    | throw (IO.userError s!"Reord.Even.casesOn: no rfl row ({pc.failure})")
  let .thmDecl cv _ := rflRow | throw (IO.userError "Reord.Even.casesOn: the rfl row is not a theorem")
  let some (level, carrier, left, right) := eqParts cv.type
    | throw (IO.userError "Reord.Even.casesOn: the rfl row is not an equation")
  let some wrong := supportRow cv.name cv.levelParams (kernelEq (.succ level) carrier left right)
    | throw (IO.userError "Reord.Even.casesOn: no row at the successor level")
  let (_, resultWrong) ← decideW env b input b.images artifact #[wrong]
  expectRefused "the rfl row of Reord.Even.casesOn at the successor of its universe" resultWrong isFold
  let (_, resultRight) ← decideW env b input b.images artifact #[rflRow]
  match resultRight with
  | .ok () => IO.println "PASS: small levels: a 40-fold imax chain is u, imax (u+1) u is found, u+5 is not; \
      the rfl row of Reord.Even.casesOn at the proposed universe accepted (valid neighbour)"
  | .error e => throw (IO.userError s!"Reord.Even.casesOn: the rfl row at its universe was refused: {declineLabel e}")
  -- F3: the pre-screen time budget. At a zero budget no row is checked (not decided): every
  -- changed constant that needs a row is Unsupported (`overBudgetClass`), none is Rejected or
  -- certified; the others keep their routes. Valid neighbour: the default budget (above).
  let (pre0, _) ← decideW env b input b.images artifact (rowBudget := fun _ _ => 0)
  unless pre0.proposedRows > 0 && pre0.overBudgetRows == pre0.proposedRows && pre0.support.isEmpty do
    throw (IO.userError s!"zero budget: {pre0.overBudgetRows} of {pre0.proposedRows} rows over the budget, \
      {pre0.support.size} folded")
  let needsRows (r : String) : Bool :=
    (r.splitOn "equations:rfl").length > 1 || (r.splitOn "type-row").length > 1
  let mut asserted := 0
  for (n, r) in expectedRoutes do
    if needsRows r then
      match pre0.failed[n]? with
      | some (.unsupported c) =>
        unless c == overBudgetClass do throw (IO.userError s!"zero budget: {n}: unsupported with class {c}")
        asserted := asserted + 1
      | some v => throw (IO.userError s!"zero budget: {n}: {v.word} {v.cause}")
      | none => throw (IO.userError s!"zero budget: {n} passed by route {pre0.routes[n]?} with no row checked")
    else unless pre0.routes[n]? == some r do
      throw (IO.userError s!"zero budget: {n}: route {pre0.routes[n]?}, expected {r}")
  for (n, v) in pre0.failed.toList do
    match v with
    | .unsupported c => unless c == overBudgetClass do throw (IO.userError s!"zero budget: {n}: unsupported {c}")
    | _ => throw (IO.userError s!"zero budget: {n}: {v.word} {v.cause}")
  IO.println s!"PASS: zero row budget: {pre0.proposedRows} rows not checked; {pre0.failed.size} changed \
    constants Unsupported ({overBudgetClass}), {asserted} of them asserted per name, none rejected; the \
    other routes unchanged"
  -- a row over the budget never hides a refused one: `Split.A.len._f` with its type row not
  -- checked (budget 0) and its `rfl` row checked. Valid neighbour (Lean's value): Unsupported,
  -- the type row is all it lacks; negative (a forged value, the `rfl` row refused): Rejected.
  let typeRowOnly : Lean.Name → String → Nat := fun n what =>
    if n == lenF && what == "type" then 0 else defaultRowBudget
  let (preM, _) ← decideW env b input b.images artifact (rowBudget := typeRowOnly)
  match preM.failed[lenF]? with
  | some (.unsupported c) =>
    unless c == overBudgetClass do throw (IO.userError s!"type row over the budget: {lenF}: unsupported {c}")
  | some v => throw (IO.userError s!"type row over the budget: {lenF}: {v.word} {v.cause}")
  | none => throw (IO.userError s!"type row over the budget: {lenF} passed by route {preM.routes[lenF]?}")
  let forgedLen := { input with
    source := replace source (.defnInfo { lenD with value := constLambda lenD.type (.lit (.natVal 0)) }) }
  let (preMF, _) ← decideW env b forgedLen b.images artifact (rowBudget := typeRowOnly)
  match preMF.failed[lenF]? with
  | some (.rejected c) =>
    unless ((preMF.refusals.getD lenF "").splitOn "rfl row refused by the checker").length > 1 do
      throw (IO.userError s!"forged value beside a row over the budget: refusal {preMF.refusals[lenF]?}")
    IO.println s!"PASS: a refused rfl row beside a type row over the budget: {lenF} rejected ({c.take 140}); \
      valid neighbour (Lean's value): unsupported ({overBudgetClass})"
  | some v => throw (IO.userError s!"forged value beside a row over the budget: {v.word} {v.cause}")
  | none => throw (IO.userError "forged value beside a row over the budget: passed the pre-pass")
  runSized
  IO.println s!"changed constants: {roots.length}/{roots.length} roots certified with their routes; \
    {expectedUnsupported.length} expected unsupported; 9 forgeries refused beside their valid neighbour; \
    alias-fiber rows named apart; {pre0.failed.size} changed constants unsupported at a zero row budget, none \
    rejected; Sized.ok certified by its statement"

/-- Probe (not a `check-cert` step): compile the cone of `roots` from a Lean
environment (`--module <M>` imports a module, `--file <F>` elaborates a file as
`compile-certify --file` does) in-process under Pass 3 and write it to `out`,
for `compile-certify` to decide. Used to try W+ on a library's changed blocks
before a library run. -/
def probe (args : List String) : IO Unit := do
  let (env, rest) ← match args with
    | "--module" :: m :: rest => pure (← getCompileEnv #[m.toName], rest)
    | "--file" :: f :: rest => pure (← getFileEnv f, rest)
    | _ => throw (IO.userError "changed-probe (--module <M> | --file <F>) <out.ixe> <root>…")
  let some out := rest.head? | throw (IO.userError "changed-probe: missing output path")
  let auxOnly := rest.tail.contains "--aux-only"
  let explicit := (rest.tail.filter (· != "--aux-only")).map String.toName |>.filter fun r =>
    env.contains r
  IO.println s!"changed-probe: roots present {explicit}"
  -- every constant in the namespace of a root's block member (its auxiliaries and users);
  -- with `--aux-only`, the members, their constructors and Lean's auxiliaries only
  let members : List Lean.Name := explicit.flatMap fun r => match env.find? r with
    | some (.inductInfo v) => v.all
    | _ => [r]
  let auxiliary (m n : Lean.Name) : Bool :=
    let last := match n with
      | .str _ s => s
      | _ => ""
    n == m || (n.getPrefix == m && (["rec", "casesOn", "recOn", "below", "brecOn", "noConfusion",
        "noConfusionType", "ctorIdx", "ctorElim", "sizeOf_spec", "inj", "injEq"].contains last ||
        last.startsWith "rec_" || last.startsWith "below_" || last.startsWith "brecOn_" ||
        last.startsWith "_sizeOf" || (match env.find? n with | some (.ctorInfo _) => true | _ => false))) ||
      (n.getPrefix.getPrefix == m && (last == "go" || last == "eq"))
  let mut roots : Array Lean.Name := explicit.toArray
  for (n, _) in env.constants.toList do
    if members.any fun m => if auxOnly then auxiliary m n else m.isPrefixOf n then roots := roots.push n
  IO.println s!"changed-probe: {roots.size} roots in the namespaces of {members.length} members"
  -- the closure under `declarationRefs`, by a hash set (the probe's cones are large)
  let mut seen : Std.HashSet Lean.Name := {}
  let mut todo : Array Lean.Name := roots
  let mut decls : Array Lean.ConstantInfo := #[]
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throw (IO.userError s!"changed-probe: {n} is referenced but absent")
    decls := decls.push ci
    for r in refsOf ci do
      unless seen.contains r do todo := todo.push r
  IO.println s!"changed-probe: {decls.size} declarations in the cone"
  let compiled ← match ← _root_.Ix.CompileM.compileLeanConsts
      (decls.toList.map (fun ci => (ci.name, ci))) (numWorkers := 16) (pass3? := some true) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compiler failed: {e}")
  IO.FS.writeBinFile out compiled.bytes
  IO.println s!"changed-probe: wrote {out}: {compiled.bytes.size} bytes, ungrounded {compiled.ungroundedCount}, \
    Blake3 {Address.blake3 compiled.bytes}"

end Tests.Ix.CompileCert.Changed
