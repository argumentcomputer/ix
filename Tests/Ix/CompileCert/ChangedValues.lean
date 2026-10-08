import Tests.Ix.CompileCert.Changed
import Tests.Ix.CompileCert.ValueRowDefs
import Tests.Ix.Compile.Twins.Cliques
import Tests.Ix.Compile.CliqueOwnership.Sources

/-! # Package V: value rows for transported clique members (`changed-values`)

The clique twins (`Tests.Ix.Compile.Twins.Cliques`: every family, each in two or
three presentations, so that one presentation of each clique is transported
whatever the canonical order) and the clique-ownership sources
(`Tests.Ix.Compile.CliqueOwnership.Sources`: well-founded, structural and
`partial_fixpoint` cliques whose user code has the shape of the encoding;
the refused caller `WF8` left out) are compiled in-process under Pass 3 with
`Tests.Ix.CompileCert.ValueRowDefs` (a root reaching the library lemmas a value
row's proof uses). Then, with the certifier's own functions (`wPrePass` with the
artifact, so with value rows; `finalSupport`; `checkIndexed'`):

* **positive:** every transported member of a well-founded clique, and every
  transported structural member outside `expectedResidual`, is certified by
  `equations:value-row`; the expected residuals (`partial_fixpoint` and lattice
  cliques, structural cliques over the changed `Common.Tr`/`Fo` block) have no value row and the reason, and are never Rejected: each keeps
  Lean's `eq_def` when Lean realized one, its `rfl` row when its value is
  convertible after all, else the named Unsupported class; the W+ decision
  accepts the cone with the value rows folded;
* **control:** without value rows (`produced? := none`, the certifier's
  `--no-value-rows`) the same well-founded members are not certified by a
  value row (they take Lean's `eq_def`, which the twins realize);
* **negatives, each beside its valid neighbour (the decision above):** a
  forged value row (a member's statement with another member's value on the
  right, its own proof) and a row for the wrong member (one member's proof
  under another member's statement) are refused by the certified fold, as
  rows of the support of the W+ decision. -/

namespace Tests.Ix.CompileCert.ChangedValues

open _root_.Ix.CompileCert
open _root_.Ix.CompileCert.Certifier
open Tests.Ix.CompileCert.Changed

def twinsPrefix : Lean.Name := `Tests.Ix.Compile.Twins.Cliques
def ownershipPrefix : Lean.Name := `Tests.Ix.Compile.CliqueOwnership.Src
def lemmasRoot : Lean.Name := `Tests.Ix.CompileCert.ValueRowDefs.lemmas

/-- The transported members expected without a value row (the generators'
failures and one limit of the decompiled side): `partial_fixpoint` and lattice
cliques (no generator); the
structural cliques over the changed block `Common.Tr`/`Common.Fo` (`SX`, `SM`,
`TM`: their compiled constants reach the canonical block's recursor
`Common.Tr._ix.rec`, which the generator does not add to Lean's environment).
Every other transported member must be certified by its value row (or, where
its value is convertible after all, by its `rfl` row). -/
def expectedResidual : List Lean.Name :=
  [`PF, `LI, `LC, `PU, `SX, `SM, `TM].map (twinsPrefix ++ ·) ++
  [`PF1A, `PF1B, `PF2A, `PF2B, `PF3A, `PF3B, `PF4A, `PF4B, `PF2CA, `PF2CB, `PF3CA, `PF3CB, `PF4CA, `PF4CB,
   `PF5A, `PF5B, `PF6A, `PF6B, `PF7A, `PF7B].map (ownershipPrefix ++ ·)

/-- The fixture's roots: every constant of the twins and of the ownership
sources (but the refused caller's clique `WF8`), and the lemma root. -/
def rootsOf (env : Lean.Environment) : List Lean.Name := Id.run do
  let wf8 := ownershipPrefix ++ `WF8A
  let wf8b := ownershipPrefix ++ `WF8B
  let mut out : Array Lean.Name := #[lemmasRoot]
  for (n, _) in env.constants.toList do
    if (twinsPrefix.isPrefixOf n || ownershipPrefix.isPrefixOf n) &&
        !wf8.isPrefixOf n && !wf8b.isPrefixOf n && !n.isInternalDetail then
      out := out.push n
  return (out.qsort (fun a b => toString a < toString b)).toList

/-- Compile the fixture's cone under Pass 3 (`changed-values.ixe` in `$C1_OUTPUT_DIR`). -/
def compileFixture : IO (Lean.Environment × Source × Ix.CompileM.LeanPipelineOut) := do
  let env ← getCompileEnv #[`Tests.Ix.Compile.Twins.Cliques, `Tests.Ix.Compile.CliqueOwnership.Sources,
    `Tests.Ix.CompileCert.ValueRowDefs]
  let roots := rootsOf env
  -- the closure under `declarationRefs`, by a hash set (`captureCone`'s list rounds are quadratic
  -- on a cone of this size; the source is untrusted input either way: W+ decides its domain)
  let mut seen : Std.HashSet Lean.Name := {}
  let mut todo : Array Lean.Name := roots.toArray
  let mut decls : Array Lean.ConstantInfo := #[]
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throw (IO.userError s!"{n} is referenced but absent")
    decls := decls.push ci
    for r in refsOf ci do
      unless seen.contains r do todo := todo.push r
  let compiled ← match ← _root_.Ix.CompileM.compileLeanConsts
      (decls.toList.map (fun ci => (ci.name, ci))) (numWorkers := 16) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compiler failed: {e}")
  unless compiled.ungroundedCount == 0 do throw (IO.userError "compiler output contains ungrounded declarations")
  IO.println s!"compiled {decls.size} declarations ({roots.length} roots): \
    {compiled.bytes.size} bytes; Blake3: {Address.blake3 compiled.bytes}"
  if let some directory ← IO.getEnv "C1_OUTPUT_DIR" then
    IO.FS.createDirAll directory
    IO.FS.writeBinFile (System.FilePath.mk directory / "changed-values.ixe") compiled.bytes
  return (env, ⟨decls.toList⟩, compiled)

/-- The final input of a pre-pass: the source without the constants it did not
pass and their users, the support of the rest. -/
def finalOf (b : Built) (source : Source) (pre : PrePass) : Array Lean.Name :=
  let names := source.names.toArray
  let survivors := names.filter (fun n => !pre.failed.contains n)
  (closeCandidates b.refs pre.failed survivors).2

/-- The W+ decision on the final input, with `extra` rows appended to its support. -/
def decideFinal (env : Lean.Environment) (b : Built) (source : Source) (pre : PrePass)
    (artifact : AdmittedArtifact (inputOf b source).toArtifactInput)
    (extra : Array _root_.Ix.Kernel.Declaration := #[]) : Except Decline' Unit :=
  let finalNames := finalOf b source pre
  let input : Input := { inputOf b source with
    source := ⟨source.declarations.filter fun ci => finalNames.contains ci.name⟩
    roots := finalNames.toList
    map := finalNames.toList.filterMap (b.entries[·]?) }
  let (sup, _, rowsFinal) := finalSupport finalNames pre
  let support := sup ++ extra
  let imagesFn : Lean.Name → Bool := fun n => b.images.contains n
  -- the input's artifact is the cone's (the same records): reuse the admission
  let artifact' : AdmittedArtifact input.toArtifactInput := artifact
  let sh := SharedW.ofArtifact input imagesFn artifact' support
  let entryPos := entryPositions sh.entries
  let hints := buildHintsW input sh entryPos (queriesFor env b.refs) 4
    (fun n => rowsAtWith b.entries entryPos sh.reader rowsFinal sh.entries.size n ++
      ((List.range extra.size).map (sh.entries.size + sup.size + ·)))
  (checkIndexed' input imagesFn artifact' support hints).map fun _ => ()

/-- A row with another statement and the same proof. -/
def withStatement (row : _root_.Ix.Kernel.Declaration) (statement : _root_.Ix.Kernel.Expr) :
    _root_.Ix.Kernel.Declaration :=
  match row with
  | .thmDecl cv v => .thmDecl { cv with type := statement } v
  | d => d

def run : IO Unit := do
  let (env, captured, compiled) ← compileFixture
  let b ← build env captured compiled.env
  let some (.thmInfo lemmas) := env.find? lemmasRoot | throw (IO.userError "missing the lemma root")
  for c in [``WellFounded.induction, ``WellFounded.fix_eq, ``WellFounded.Nat.fix_eq, ``InvImage.wf, ``funext] do
    unless lemmas.value.getUsedConstants.contains c do
      throw (IO.userError s!"the lemma root does not reach {c}")
  let input := inputOf b captured
  let artifact ← match prepareArtifact input.toArtifactInput with
    | .ok a => pure a
    | .error _ => throw (IO.userError "admission of the compiled cone failed")
  let quiet : String → IO Unit := fun _ => pure ()
  let pre ← wPrePass env b.entries input b.images artifact (queriesFor env b.refs) 4 quiet
    (produced? := some compiled.env)
  -- the transported members and their outcomes
  let wf := pre.values.filter (·.encoding == "well-founded")
  let accepted := pre.values.filter (·.outcome == "accepted")
  let residual := pre.values.filter (·.outcome != "accepted")
  IO.println s!"transported clique members with a value-row attempt: {pre.values.size} \
    (well-founded {wf.size}, structural {(pre.values.filter (·.encoding == "structural")).size}, \
    other {(pre.values.filter fun v => v.encoding != "well-founded" && v.encoding != "structural").size})"
  if wf.size < 30 then throw (IO.userError s!"only {wf.size} transported well-founded members (expected ≥ 30)")
  for v in accepted do
    unless (pre.routes.getD v.name "").startsWith "equations:value-row" do
      throw (IO.userError s!"{v.name}: value row accepted, route {pre.routes[v.name]?}")
  let mut kept := 0
  let mut unsupported := 0
  let mut byRfl := 0
  let mut unexpected : Array String := #[]
  for v in residual do
    IO.println s!"  residual {v.name} ({v.encoding}): {v.outcome}: {(v.detail.take 160).toString}"
    if v.encoding == "well-founded" || (expectedResidual.all (!·.isPrefixOf v.name) &&
        !(pre.routes.getD v.name "").startsWith "equations:rfl") then
      unexpected := unexpected.push s!"{v.name} ({v.encoding}): value row {v.outcome}"
    match pre.failed[v.name]? with
    | some (.unsupported c) =>
      unless c == "changed definition: transported clique member without eq_def" do
        throw (IO.userError s!"{v.name}: unsupported with class {c}")
      unsupported := unsupported + 1
    | some verdict => throw (IO.userError s!"{v.name}: {verdict.word} {verdict.cause}")
    | none =>
      match pre.routes[v.name]? with
      | some "equations:eq_def" => kept := kept + 1
      | some r =>
        -- convertible after all (its `rfl` row accepted): no value row needed, no residual trust
        unless r.startsWith "equations:rfl" do throw (IO.userError s!"{v.name}: route {r}")
        byRfl := byRfl + 1
      | none => throw (IO.userError s!"{v.name}: no route")
  for (n, verdict) in pre.failed.toList do
    if let .rejected c := verdict then throw (IO.userError s!"{n}: rejected ({c})")
  unless unexpected.isEmpty do
    throw (IO.userError s!"{unexpected.size} transported members without a value row that are not expected \
      residuals: {unexpected.toList}")
  IO.println s!"PASS: {accepted.size} transported members certified by equations:value-row \
    ({(accepted.filter (·.encoding == "well-founded")).size} well-founded: all of them, \
    {(accepted.filter (·.encoding == "structural")).size} structural); {residual.size} expected residuals \
    ({kept} by Lean's eq_def, {byRfl} by their rfl row, {unsupported} unsupported), none rejected"
  -- the W+ decision with the value rows (the valid neighbour of the negatives)
  let finalNames := finalOf b captured pre
  let finalRows := (finalSupport finalNames pre).1
  let finalValueRows := (finalRows.filter isValueRow).size
  match decideFinal env b captured pre artifact with
  | .ok () => IO.println s!"PASS: valid neighbour: W+ accepts the cone ({finalNames.size} \
      declarations, {finalRows.size} support rows, {finalValueRows} value rows)"
  | .error e => throw (IO.userError s!"the W+ decision refused the cone with its value rows: {declineLabel e}")
  -- control: no value rows
  let pre0 ← wPrePass env b.entries input b.images artifact (queriesFor env b.refs) 4 quiet
  let mut noRow := 0
  for v in wf do
    if (pre0.routes.getD v.name "").startsWith "equations:value-row" then
      throw (IO.userError s!"control: {v.name} certified by a value row without value rows")
    if pre0.failed.contains v.name || pre0.routes[v.name]? == some "equations:eq_def" then noRow := noRow + 1
  unless noRow == wf.size do throw (IO.userError s!"control: {wf.size - noRow} members neither unsupported nor eq_def")
  IO.println s!"PASS: control without value rows: the {wf.size} well-founded members are not certified by a \
    value row ({(wf.filter fun v => pre0.routes[v.name]? == some "equations:eq_def").size} by Lean's eq_def, \
    {(wf.filter fun v => pre0.failed.contains v.name).size} unsupported)"
  -- negatives: two value rows of one clique (members of the same type)
  let valueRowOf (n : Lean.Name) : Option _root_.Ix.Kernel.Declaration :=
    ((pre.rowsOf.getD n #[]).filterMap (pre.support[·]?)).find? isValueRow
  let some (a, bName) := (wf.toList.flatMap fun v => wf.toList.filterMap fun w =>
      if v.name != w.name && v.name.getPrefix == w.name.getPrefix then some (v.name, w.name) else none).head?
    | throw (IO.userError "no clique with two value rows")
  let (some rowA, some rowB) := (valueRowOf a, valueRowOf bName)
    | throw (IO.userError s!"no value rows for {a}, {bName}")
  let (.thmDecl cvA _, .thmDecl cvB proofB) := (rowA, rowB) | throw (IO.userError "value rows are not theorems")
  -- (1) a forged value row: A's statement with B's value on the right, A's proof
  let some (lA, tA, leftA, _) := eqParts cvA.type | throw (IO.userError "value row of A is not an equation")
  let some (_, _, _, rightB) := eqParts cvB.type | throw (IO.userError "value row of B is not an equation")
  let forged := renameRow 900000 (withStatement rowA (kernelEq lA tA leftA rightB))
  match decideFinal env b captured pre artifact #[forged] with
  | .ok () => throw (IO.userError s!"forged value row ({a} = value of {bName}) accepted")
  | .error e =>
    unless isFold e do throw (IO.userError s!"forged value row: refused for another reason: {declineLabel e}")
    IO.println s!"PASS: forged value row ({a} = Lean's value of {bName}, {a}'s proof): refused ({declineLabel e})"
  -- (2) a row for the wrong member: B's proof under A's statement
  let wrong := renameRow 900001 (.thmDecl cvA proofB)
  match decideFinal env b captured pre artifact #[wrong] with
  | .ok () => throw (IO.userError s!"{bName}'s value proof accepted for {a}")
  | .error e =>
    unless isFold e do throw (IO.userError s!"wrong member: refused for another reason: {declineLabel e}")
    IO.println s!"PASS: a row for the wrong member ({bName}'s proof under {a}'s statement): refused \
      ({declineLabel e})"
  IO.println s!"changed values: {accepted.size} transported members certified by their value rows \
    ({wf.size} well-founded, {accepted.size - wf.size} structural); {residual.size} expected residuals \
    ({kept} eq_def, {byRfl} rfl, {unsupported} unsupported), none rejected; 2 forgeries refused beside their \
    valid neighbour; control without value rows"

end Tests.Ix.CompileCert.ChangedValues
