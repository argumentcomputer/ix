/-
  pass3: the gates of Pass 3, the faithful rewrite (`IX_PASS3=images`;
  design document §4.5-4.6, `Ix.Compile.Pass`), on every fixture family:
  the aux-cert reproducers (`Tests/Ix/Compile/AuxCert/*.lean`), the
  prototype's cases (`Tests/Ix/Compile/Image/C*.lean`), the twin families
  (`Tests/Ix/Compile/Twins/*`) and the decompile-diff corpus
  (`validateAuxClosure`).

  Per compile unit (a fixture's closure), compiled in-process by the Lean
  pipeline (`compileLeanInput`) with the switch off and on:

  1. **identity**: with no changed block the two outputs are byte-identical;
     otherwise every name whose address moved is in the cone of a changed
     block (the block's own constants and everything that references them,
     transitively), and every new name is a reserved `_ix` name;
  2. **decompile**: the switch-on output, decompiled by the Lean decompiler
     (`decompileEnvFullParallel`), equals the source constants (the
     decompile-diff buckets: plain, aux, call-site, coverage, all zero);
  3. **kernels**: `ix check-rs`, `ix check-lean` (meta mode) and the
     certified checker (`kernel-check-ixe`) on the switch-on output, every
     fixture constant and every `_ix` name; failures must be recorded
     (`knownFails`), declines only in documented classes;
  4. **computation rules**: for each changed block, the images of its
     recursors and their rule statements (`RuleStmt`, proof `Eq.refl`) are
     compiled into a test-only copy of the output (never into `E`) and
     checked by the three kernels;
  5. the `_ix` display names exist for every changed block.

  Run with: `lake test -- --ignored pass3` (after `lake build ix
  kernel-check-ixe`). `PASS3_ONLY` restricts the units (comma-separated
  stems or `twins`, `corpus`); `PASS3_KEEP=<dir>` keeps the outputs.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.CompileM
import Ix.CompileDriver
import Ix.DecompileDriver
import Ix.Compile.Pass
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.Compile.AuxCert
import Lean.Data.Json
import Ix.Tc.Validate
import Tests.Ix.Compile.Image

open Lean

namespace Tests.Ix.Compile.Pass3

/-! ## Units -/

/-- A compile unit: its fixture constants (`seeds`) and their closure. -/
structure CUnit where
  name : String
  env : Environment
  seeds : Array Name
  closure : List (Name × ConstantInfo)

/-- Constants of the file itself (not imported). -/
def ownConstants (env : Environment) : Array Name :=
  env.constants.map₂.foldl (init := #[]) fun acc n _ => acc.push n

/-- The constants images are built from (`PProd`, `And`, `True`, and `Eq` for
the rule statements): a closure compile must contain them, as a whole-library
compile does. -/
def packing : List Name :=
  [``PProd, ``PProd.mk, ``And, ``And.intro, ``True, ``True.intro, ``Eq, ``Eq.refl]

def closureOf (env : Environment) (seeds : List Name) : List (Name × ConstantInfo) :=
  Tests.Ix.Compile.Twins.closeWithRecursors env
    (Ix.EnvScope.collectDeps env (seeds ++ packing.filter env.contains))

def unitOfFile (path : String) : IO CUnit := do
  let env ← getFileEnv path
  let seeds := ownConstants env
  let closure := closureOf env seeds.toList
  let stem := (System.FilePath.mk path).fileStem.getD path
  return { name := stem, env, seeds, closure }

/-! ## Compiles -/

def compileUnit (u : CUnit) (pass3 : Bool) : IO Ix.CompileM.LeanPipelineOut := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv u.env u.closure).mapError toString)
  match ← Ix.CompileM.compileLeanInput input (numWorkers := 32) (pass3? := some pass3) with
  | .ok o => pure o
  | .error e => throw (IO.userError s!"{u.name}: Lean compile (pass3={pass3}) failed: {e}")

def ixN (n : Name) : _root_.Ix.Name := _root_.Ix.Name.fromLeanName n

def toLeanName : _root_.Ix.Name → Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (toLeanName p) s
  | .num p n _ => .num (toLeanName p) n

/-- Synthetic `Muts` names (`Ix.<64 hex>.…`) are keyed by block address. -/
def isSyntheticMuts (n : _root_.Ix.Name) : Bool :=
  match (n.pretty.splitOn ".") with
  | "Ix" :: h :: _ => h.length == 64 && h.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')
  | _ => false

/-! ## 1. Identity and cones -/

structure IdentityReport where
  changedBlocks : Array (Array _root_.Ix.Name) := #[]
  identical : Bool := false
  equalNames : Nat := 0
  movedInCone : Nat := 0
  newReserved : Nat := 0
  newCompiled : Nat := 0
  problems : Array String := #[]

/-- The reverse-dependency cone of a changed block: its members' constants
(every name with a member as a prefix) and everything that references them,
transitively, within the closure. -/
def cone (u : CUnit) (blocks : Array (Array _root_.Ix.Name)) : Std.HashSet Name := Id.run do
  let members : Array Name := blocks.foldl (fun acc b => acc ++ b.map toLeanName) #[]
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ci) in u.closure do
    for r in ci.getUsedConstantsAsSet do
      rev := rev.insert r ((rev.getD r #[]).push n)
    -- an inductive owns its constructors and recursors
    match ci with
    | .ctorInfo cv => rev := rev.insert cv.induct ((rev.getD cv.induct #[]).push n)
    | _ => pure ()
  let mut out : Std.HashSet Name := {}
  let mut todo : Array Name := #[]
  for (n, _) in u.closure do
    if members.any (·.isPrefixOf n) then todo := todo.push n
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if out.contains n then continue
    out := out.insert n
    for d in rev.getD n #[] do
      if !out.contains d then todo := todo.push d
  return out

def identityCheck (u : CUnit) (off on : Ix.CompileM.LeanPipelineOut) : IdentityReport := Id.run do
  let blocks := on.cenv.p3Blocks.toArray.map (·.2)
  let mut r : IdentityReport := { changedBlocks := blocks }
  if blocks.isEmpty then
    r := { r with identical := off.bytes == on.bytes }
    if !r.identical then
      r := { r with problems := r.problems.push "no changed block, but the outputs differ" }
    return r
  let c := cone u blocks
  for (n, nd) in off.env.named do
    if isSyntheticMuts n then continue
    match on.env.named.get? n with
    | none => r := { r with problems := r.problems.push s!"{n.pretty} missing with the switch on" }
    | some nd' =>
      if nd'.addr == nd.addr then r := { r with equalNames := r.equalNames + 1 }
      else if c.contains (toLeanName n) then r := { r with movedInCone := r.movedInCone + 1 }
      else r := { r with problems := r.problems.push s!"{n.pretty} moved outside the changed blocks' cones" }
  for (n, _) in on.env.named do
    if isSyntheticMuts n || off.env.named.contains n then continue
    if Ix.Compile.Pass.hasReserved n then r := { r with newReserved := r.newReserved + 1 }
    -- refused or failed with the switch off (A0's collapse refusal is on the
    -- surgery path only)
    else if off.cenv.ungrounded.contains n then r := { r with newCompiled := r.newCompiled + 1 }
    else r := { r with problems := r.problems.push s!"{n.pretty} is new with the switch on and not reserved" }
  return r

/-! ## 2. Decompile -/

/-- Decompile the switch-on output and compare with the source constants
(the decompile-diff buckets). -/
def decompileCheck (u : CUnit) (on : Ix.CompileM.LeanPipelineOut) : IO (Array String × String) := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv u.env u.closure).mapError toString)
  let prepared ← IO.ofExcept input.prepare
  let src : Std.HashMap _root_.Ix.Name _root_.Ix.ConstantInfo :=
    (_root_.Ix.CanonM.canonChunk prepared.toArray).foldl (fun m (n, ci) => m.insert n ci) {}
  -- the ungrounded constants are not compiled; leave them out of coverage
  let (decompiled, errors, _) ← _root_.Ix.DecompileM.decompileEnvFullParallel on.env (some src)
  let mut problems : Array String := #[]
  let mut matched := 0
  for (n, ci) in decompiled do
    match src.get? n with
    | none => problems := problems.push s!"decompiled, not in source: {n.pretty}"
    | some orig =>
      if ci == orig then matched := matched + 1
      else problems := problems.push s!"decompile mismatch: {n.pretty}"
  for (n, e) in errors do
    problems := problems.push s!"decompile error {n.pretty}: {e.take 200}"
  let errNames : Std.HashSet _root_.Ix.Name := errors.foldl (fun s (n, _) => s.insert n) {}
  for (n, _) in src do
    if !decompiled.contains n && !errNames.contains n && !on.cenv.ungrounded.contains n then
      problems := problems.push s!"not decompiled: {n.pretty}"
  return (problems, s!"{matched}/{src.size} decompiled equal")

/-! ## 3. Kernels -/

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"
private def certExe : System.FilePath := ".lake" / "build" / "bin" / "kernel-check-ixe"
private def spawnEnv : Array (String × Option String) := #[("LD_LIBRARY_PATH", none)]

private def runProc (cmd : System.FilePath) (args : Array String) : IO IO.Process.Output := do
  let exe ← IO.FS.realPath cmd
  IO.Process.output { cmd := exe.toString, args, env := spawnEnv }

private def failLines (out : String) : List (String × String) :=
  out.splitOn "\n" |>.filterMap fun line =>
    let l := line.trimAsciiStart.toString
    if l.startsWith "✗ " then
      let body := (l.drop 2).toString
      match body.splitOn ": " with
      | name :: rest => some (name, ": ".intercalate rest)
      | [] => none
    else none

/-- `(leg, name, message)` of every failure of the three kernels on `names`
of the file `path`. Declines of the certified checker in documented classes
are not failures. -/
def kernelFailures (dir : System.FilePath) (path : System.FilePath) (names : Array String)
    (anon : Bool := false) : IO (Array (String × String × String)) := do
  let mut failed : Array (String × String × String) := #[]
  let namesFile := dir / "names.txt"
  IO.FS.writeFile namesFile ("\n".intercalate names.toList ++ "\n")
  let nameSet : Std.HashSet String := names.foldl (·.insert ·) {}
  -- certified checker (whole file: its rows name every constant)
  let certPath := dir / "cert.jsonl"
  let cert ← runProc certExe #[path.toString, certPath.toString, "--jobs", "8"]
  if ← certPath.pathExists then
    for line in (← IO.FS.readFile certPath).splitOn "\n" do
      if line.isEmpty then continue
      let .ok j := Json.parse line | continue
      let ns := (j.getObjValAs? (Array String) "names").toOption.getD #[]
      let outcome := (j.getObjValAs? String "outcome").toOption.getD ""
      let reason := (j.getObjValAs? String "reason").toOption.getD ""
      let ours := ns.filter nameSet.contains
      if ours.isEmpty || outcome == "accept" then continue
      if outcome == "decline" && Tests.Ix.Compile.AuxCert.documentedDecline reason then continue
      for n in ours do failed := failed.push ("cert", n, s!"{outcome}: {reason}")
  else
    failed := failed.push ("cert", "*", s!"kernel-check-ixe wrote no rows (exit {cert.exitCode})")
  -- check-rs, meta mode, the names
  let rs ← runProc ixExe ((#["check-rs", path.toString, "--consts-file", namesFile.toString]
    ++ if anon then #["--anon"] else #[]))
  for (n, m) in failLines (rs.stdout ++ rs.stderr) do failed := failed.push ("rs", n, m)
  if rs.exitCode != 0 && (failLines (rs.stdout ++ rs.stderr)).isEmpty then
    failed := failed.push ("rs", "*", s!"check-rs exit {rs.exitCode}: {((rs.stdout ++ rs.stderr).takeEnd 300).toString}")
  -- check-lean, meta mode, the names
  let failOut := dir / "lean.fail"
  let ln ← runProc ixExe (#["check-lean", path.toString, "--consts-file", namesFile.toString,
    "--fail-out", failOut.toString, "--workers", "8"] ++ if anon then #["--anon"] else #[])
  let leanFails ← if ← failOut.pathExists then
      pure ((← IO.FS.readFile failOut).splitOn "\n" |>.filter fun l => !l.isEmpty && !l.startsWith "#")
    else pure []
  let msgs := (failLines (ln.stdout ++ ln.stderr)).filter fun (n, _) => (n.splitOn "@").length ≤ 1
  for n in leanFails do
    let n := n.trimAscii.toString
    let m := (msgs.find? (·.1 == n)).map (·.2) |>.getD ""
    failed := failed.push ("lean", n, m)
  if leanFails.isEmpty && ln.exitCode != 0 then
    failed := failed.push ("lean", "*", s!"check-lean exit {ln.exitCode}: {((ln.stdout ++ ln.stderr).takeEnd 300).toString}")
  return failed

/-! ## 4. Computation rules in a test-only environment -/

/-- Compile one definition or theorem into `env` (names, blobs, constant,
`Named` entry), resolving the names of `known` first. -/
def addConst (cenv : Ix.CompileM.CompileEnv) (known : Std.HashMap _root_.Ix.Name Address)
    (env : Ixon.Env) (ci : _root_.Ix.ConstantInfo) : Except String (Ixon.Env × Address) := do
  let name := ci.getCnst.name
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := ({} : _root_.Ix.Set _root_.Ix.Name).insert name, current := name,
      mutCtx := default, univCtx := [] }
  let init : Ix.CompileM.BlockState := { blockNameToAddr := known }
  match Ix.CompileM.CompileM.run cenv blockEnv init (Ix.CompileM.compileConstantInfo ci) with
  | .error e => throw s!"{name.pretty}: {e}"
  | .ok (r, bs) =>
    let (names, blobs) := Ixon.RawEnv.addNameComponentsWithBlobs
      (bs.blockNames.fold (fun m k v => m.insert k v) env.names)
      (bs.blockBlobs.fold (fun m k v => m.insert k v) env.blobs) name
    let env := { env with
      consts := env.consts.insert r.blockAddr { buf := r.blockBytes, len := r.blockBytes.size }
      named := env.named.insert name { addr := r.blockAddr, constMeta := r.blockMeta }
      names, blobs }
    return (env, r.blockAddr)

/-- The images and rule statements of every changed block, added to a copy of
`on`'s environment. Returns the environment, the image names and the rule
names. -/
def ruleEnv (on : Ix.CompileM.LeanPipelineOut) :
    Except String (Ixon.Env × Array String × Array String) := do
  let cenv := on.cenv
  let inp := Ix.Compile.Pass.viewInput cenv
  let mut env := on.env
  let mut known : Std.HashMap _root_.Ix.Name Address := {}
  let mut images : Array String := #[]
  let mut rules : Array String := #[]
  let mut stmts : Array (_root_.Ix.Name × _root_.Ix.Compile.Image.RuleStmt) := #[]
  for (_, all) in cenv.p3Blocks do
    let v ← Ix.Compile.Pass.buildView inp all
    for r in Ix.Compile.Pass.imageKinds inp.const? all do
      let some (.recInfo rv) := inp.const? r | continue
      let img ← v.image inp r
      let name := Ix.Compile.Pass.imageName r
      if let some nd := env.named.get? name then
        known := known.insert name nd.addr
      else
        let dv : _root_.Ix.DefinitionVal := {
          cnst := { name, levelParams := img.levelParams, type := img.type }
          value := img.value, hints := .abbrev
          safety := if rv.isUnsafe then .unsafe else .safe, all := #[name] }
        let (env', a) ← addConst cenv known env (.defnInfo dv)
        env := env'
        known := known.insert name a
      images := images.push name.pretty
      for s in img.rules do stmts := stmts.push (name, s)
  for (_, s) in stmts do
    let tv : _root_.Ix.TheoremVal := {
      cnst := { name := s.name, levelParams := s.levelParams, type := s.type }
      value := s.proof, all := #[s.name] }
    let (env', _) ← addConst cenv known env (.thmInfo tv)
    env := env'
    rules := rules.push s.name.pretty
  return (env, images, rules)

/-! ## Expectations -/

/-- Recorded kernel failures under the switch: `(unit, leg, name, cause)`;
name `*` stands for every name of the unit on that leg. -/
def knownFails : List (String × String × String × String) := [
  -- WB-B6 (RecAlias): fails with the switch off too; the switch-off run lists it
  -- under its sibling, so it is recorded by name.
  ("twins", "rs", "Tests.Ix.Compile.Twins.Repro.Orig.RecAlias.PA.triv.match_1_7",
    "WB-B6, also with the switch off"),
  -- BELOW-ORDER: Lean's own IndPredBelow block of the collapsed Prop pair
  -- (`Repro.Orig.PropCollapse`), compiled as its own block under the switch, is
  -- ordered by Pass 1's refinement on a bound-variable difference found while
  -- both members were one class; with the final class indices the first
  -- difference is the cross reference `Q.below`/`P.below`, which compares the
  -- other way, so check-lean's whole-environment meta ingress rejects the block
  -- (the certified checker accepts). A Pass 1 fixed-point defect (A2).
  ("twins", "lean", "*", "BELOW-ORDER"),
  -- A0's evaporation refusal of `C4b.Src.A2` (Pass 2) in both modes: B2's
  -- display entry names the refused block.
  ("C4Evap", "rs", "C4b.Src.B2._ix.below", "A0 refusal of C4b.Src.A2, both modes")]

def isKnown (unit leg name : String) : Option String :=
  knownFails.findSome? fun (u, l, n, c) =>
    if u == unit && l == leg && (n == name || n == "*") then some c else none

/-- The Lean name an `_ix` display name stands for (`x._ix.S ↦ x.S`, an image
`a._ix ↦ a`). -/
def leanOf (s : String) : String :=
  let s := if s.endsWith "._ix" then (s.dropEnd 4).toString else s
  String.intercalate "." ((s.splitOn ".").filter (· != "_ix"))

/-! ## One unit -/

def runUnit (u : CUnit) (keep? : Option System.FilePath) : IO (Array String × Array String) := do
  let mut problems : Array String := #[]
  let mut lines : Array String := #[]
  let t0 ← IO.monoMsNow
  let off ← compileUnit u false
  let on ← compileUnit u true
  let failOff := off.cenv.ungrounded.size
  let failOn := on.cenv.ungrounded.size
  lines := lines.push s!"{u.name}: {u.seeds.size} fixture constants, {u.closure.length} in the \
    closure; block failures off {failOff}, on {failOn} ({(← IO.monoMsNow) - t0} ms)"
  for (n, e) in on.cenv.ungrounded.toList.take 6 do
    lines := lines.push s!"  failed with the switch on: {n.pretty}: {e.take 240}"
  -- 1. identity
  let idr := identityCheck u off on
  lines := lines.push s!"  changed blocks: {idr.changedBlocks.map (·.map (·.pretty))}; \
    identical {idr.identical}; equal names {idr.equalNames}, moved in cones {idr.movedInCone}, \
    new reserved {idr.newReserved}, compiled only with the switch on {idr.newCompiled}"
  problems := problems ++ idr.problems.map (s!"{u.name}: " ++ ·)
  -- 5. display names of the changed blocks' auxiliaries
  for all in idr.changedBlocks do
    let some x := all[0]? | continue
    let ixRec := _root_.Ix.Name.mkStr (_root_.Ix.Name.mkStr x "_ix") "rec"
    let hasIx := on.env.named.toList.any fun (n, _) =>
      Ix.Compile.Pass.hasReserved n && all.any fun m => (toLeanName m).isPrefixOf (toLeanName n)
    if !hasIx then problems := problems.push s!"{u.name}: no `_ix` name for the block of {x.pretty} ({ixRec.pretty})"
  -- no new failure with the switch on
  for (n, e) in on.cenv.ungrounded do
    if !off.cenv.ungrounded.contains n then
      problems := problems.push s!"{u.name}: {n.pretty} fails only with the switch on: {e.take 240}"
  for (n, e) in off.cenv.ungrounded.toList.take 3 do
    lines := lines.push s!"  failed with the switch off: {n.pretty}: {e.take 200}"
  -- 2. decompile (of a complete output: a partial one, where Pass 2 refused a
  -- block in both modes, is not decompilable as a whole)
  if on.cenv.ungrounded.isEmpty then
    let (dprob, dsum) ← decompileCheck u on
    -- the same decompile of the switch-off output, for pre-existing problems
    let (dprobOff, _) ← if dprob.isEmpty then pure (#[], "")
      else decompileCheck u off
    let pre := dprob.filter dprobOff.contains
    lines := lines.push s!"  decompile: {dsum}, {dprob.size} problem(s) ({pre.size} also with the switch off)"
    for p in dprob.toList.take 8 do lines := lines.push s!"    {p}"
    -- a problem the switch-off output has too is pre-existing, outside this package
    problems := problems ++ (dprob.filter (!dprobOff.contains ·)).map (s!"{u.name}: " ++ ·)
  else
    lines := lines.push s!"  decompile: skipped, {on.cenv.ungrounded.size} block failure(s) in both modes"
  -- 3. kernels on the switch-on output; 4. rules in a test-only copy
  let dir ← match keep? with
    | some d => do
      let d := d / u.name
      IO.FS.createDirAll d
      pure d
    | none => IO.FS.createTempDir
  try
    let path := dir / "on.ixe"
    IO.FS.writeBinFile path on.bytes
    IO.FS.writeBinFile (dir / "off.ixe") off.bytes
    let seedSet : Std.HashSet String := u.seeds.foldl (fun s n => s.insert (ixN n).pretty) {}
    let names := on.env.named.toArray.filterMap fun (n, _) =>
      let s := n.pretty
      if seedSet.contains s || Ix.Compile.Pass.hasReserved n then some s else none
    let failed ← kernelFailures dir path names
    -- the same kernels on the switch-off output, for the pre-existing failures
    let offDir := dir / "off"
    IO.FS.createDirAll offDir
    let offNames := off.env.named.toArray.filterMap fun (n, _) =>
      let s := n.pretty
      if seedSet.contains s then some s else none
    let offFailed ← kernelFailures offDir (dir / "off.ixe") offNames
    let offSet : Std.HashSet (String × String) := offFailed.foldl (fun s (l, n, _) => s.insert (l, n)) {}
    let onSet : Std.HashSet (String × String) := failed.foldl (fun s (l, n, _) => s.insert (l, n)) {}
    -- Acceptance (in this order): a failure the switch-off output has too, for
    -- the name or the Lean name an `_ix` name displays (pre-existing, outside
    -- this package); a meta-mode failure (check-rs, check-lean) on a constant
    -- the certified checker accepts, in a unit with a collapsed changed block
    -- or a moved `IndPredBelow` family (documented classes BB-F7, BB-F1 and
    -- BELOW-ORDER, see the report); anything else is a problem.
    let collapseUnit := idr.changedBlocks.any (fun all => all.any fun m =>
        ((on.cenv.blocks.get? m).getD #[]).any (·.size > 1))
      || on.env.named.toList.any fun (n, nd) =>
        Ix.Compile.Pass.hasReserved n && nd.constMeta.info.kindName == "indc"
    let certFail : Std.HashSet String := failed.foldl (fun s (l, n, _) =>
      if l == "cert" then s.insert n else s) {}
    let mut nKnown := 0
    let mut nPre := 0
    let mut nMeta := 0
    for (leg, n, m) in failed do
      let pre := offSet.contains (leg, n) || offSet.contains (leg, leanOf n)
        || offSet.contains (leg, "*")
      let metaOnly := (leg == "rs" || leg == "lean") && collapseUnit
        && (if n == "*" then certFail.isEmpty else !certFail.contains n)
      match isKnown u.name leg n with
      | some _ => nKnown := nKnown + 1
      | none =>
        if pre then nPre := nPre + 1
        else if metaOnly then nMeta := nMeta + 1
        else problems := problems.push s!"{u.name}: {leg}: {n} fails: {m.take 240}"
    let fixed := offFailed.filter fun (l, n, _) => !onSet.contains (l, n)
    lines := lines.push s!"  kernels: {names.size} names, {failed.size} failure(s): {nPre} also with the switch off, {nMeta} meta-mode only on a collapsed or IndPredBelow block (certified checker accepts), {nKnown} recorded; switch off: {offFailed.size} failure(s), {fixed.size} of them pass with the switch on"
    if !idr.changedBlocks.isEmpty && on.cenv.ungrounded.isEmpty then
      match ruleEnv on with
      | .error e => problems := problems.push s!"{u.name}: rule environment: {e}"
      | .ok (renv, images, rules) =>
        match Ixon.serEnv renv with
        | .error e => problems := problems.push s!"{u.name}: rule environment: {e}"
        | .ok bytes =>
          let rpath := dir / "rules.ixe"
          IO.FS.writeBinFile rpath bytes
          let rdir := dir / "rules"
          IO.FS.createDirAll rdir
          let rfailed ← kernelFailures rdir rpath (images ++ rules) (anon := true)
          lines := lines.push s!"  rules: {images.size} images, {rules.size} rule statements by rfl, \
            {rfailed.size} kernel failure(s)"
          for (leg, n, m) in rfailed do
            problems := problems.push s!"{u.name}: rule {leg}: {n} fails: {m.take 240}"
  finally
    if keep?.isNone then IO.FS.removeDirAll dir
  return (problems, lines)

/-! ## Library comparison (`PASS3_LIB=<switch-off.ixe>,<switch-on.ixe>`) -/

/-- The constant's metadata carries a Pass 3 decompile record. -/
def hasRecord (cm : Ixon.ConstantMeta) : Bool :=
  let arena := match cm.info with
    | .defn _ _ _ _ a _ _ => a
    | .axio _ _ a _ => a
    | .quot _ _ a _ => a
    | .indc _ _ _ _ _ a _ => a
    | .ctor _ _ _ a _ => a
    | .recr _ _ _ _ _ a _ _ => a
    | .empty | .muts _ _ => {}
  arena.nodes.any fun node => match node with
    | .mdata kvmaps _ => kvmaps.any fun kv => kv.any fun (k, _) =>
      k == Ix.Compile.Pass.inlineKey.getHash
    | _ => false

/-- Compare a switch-off and a switch-on compile of a library: every moved
name is a rewritten constant (a root carrying a decompile record) or a
dependent of one (Rust's ripple verdict); every new name is reserved; and
the constants the surgery rewrote (altering call-site metadata in the
switch-off output) are counted as byte-identical or not. -/
def runLib (offPath onPath : String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let diff ← Ixon.rsDiffEnvFiles offPath onPath false
  IO.println s!"[pass3-lib] diff: {diff.namedChanged.size} changed, {diff.namedAdded.size} added, \
    {diff.namedRemoved.size} removed ({(← IO.monoMsNow) - t0} ms)"
  let offParts ← IO.ofExcept (Ixon.deEnvVerifiedLazy (← IO.FS.readBinFile offPath))
  let onParts ← IO.ofExcept (Ixon.deEnvVerifiedLazy (← IO.FS.readBinFile onPath))
  let metaOf := fun (parts : Ixon.LazyEnvParts) (n : _root_.Ix.Name) =>
    match parts.rowIdx.get? n with
    | some i => (parts.namedRows[i]!.materialize parts.backing parts.nameRev).toOption
    | none => none
  let mut problems : Array String := #[]
  -- moved names
  let mut roots := 0
  let mut rippled := 0
  let mut rewritten := 0
  let mut changedSet : Std.HashSet String := {}
  let byPretty : Std.HashMap String _root_.Ix.Name :=
    onParts.namedRows.foldl (fun m r => m.insert r.name.pretty r.name) {}
  for d in diff.namedChanged do
    changedSet := changedSet.insert d.name
    if d.rippled then
      rippled := rippled + 1
      continue
    roots := roots + 1
    let n := byPretty.get? d.name
    let named? := n.bind (metaOf onParts)
    match named? with
    | some nd =>
      if hasRecord nd.constMeta then rewritten := rewritten + 1
      else problems := problems.push s!"root without a decompile record: {d.name} ({d.fields})"
    | none => problems := problems.push s!"root not found: {d.name}"
  let mut added := 0
  for (n, _) in diff.namedAdded do
    if isSyntheticMuts (_root_.Ix.Name.mkStr _root_.Ix.Name.mkAnon n) || (n.splitOn "._ix").length > 1
        || n.startsWith "Ix." then
      added := added + 1
    else problems := problems.push s!"new name not reserved: {n}"
  for (n, _) in diff.namedRemoved do
    if !n.startsWith "Ix." then problems := problems.push s!"name removed with the switch on: {n}"
  IO.println s!"[pass3-lib] moved: {roots} roots ({rewritten} rewritten call-site constants), \
    {rippled} rippled; added {added} (reserved or synthetic)"
  -- the surgery's rewritten constants
  let mut surgered : Array _root_.Ix.Name := #[]
  for row in offParts.namedRows do
    if isSyntheticMuts row.name then continue
    if let .ok nd := row.materialize offParts.backing offParts.nameRev then
      if Ix.Tc.metaHasAlteringSurgery nd.constMeta then surgered := surgered.push row.name
  let mut same := 0
  let mut differ : Array String := #[]
  for n in surgered do
    if changedSet.contains n.pretty then differ := differ.push n.pretty else same := same + 1
  IO.println s!"[pass3-lib] surgery-rewritten constants (switch off): {surgered.size}; \
    byte-identical with the switch on: {same}; baseline (differ): {differ.size}"
  for n in (differ.qsort (· < ·)).toList do IO.println s!"[pass3-lib]   differs: {n}"
  for p in problems.toList.take 50 do IO.println s!"[pass3-lib] FAIL {p}"
  IO.println s!"[pass3-lib] {problems.size} problem(s) ({(← IO.monoMsNow) - t0} ms)"
  return if problems.isEmpty then 0 else 1

/-- Debugging aid: `PASS3_FIND=<file.ixe>,<hex prefix>,…` lists the named
entries and constants whose address starts with a prefix. -/
def runFind (path : String) (pfxs : List String) : IO UInt32 := do
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
  for (n, nd) in env.named do
    let a := toString nd.addr
    if pfxs.any (a.startsWith ·) then
      IO.println s!"[pass3-find] named {a} {n.pretty} meta={nd.constMeta.info.kindName}"
  for (a, _) in env.consts do
    if pfxs.any ((toString a).startsWith ·) then IO.println s!"[pass3-find] const {a}"
  return 0

/-- Debugging aid: `PASS3_VIEW=<file.lean>` compiles the file's closure with
the switch on and prints, per changed block, Pass 1's classes, the compiler's
classes, the view's canonical recursor types and the images. -/
def runView (path : String) : IO UInt32 := do
  let u ← unitOfFile path
  let on ← compileUnit u true
  for (n, cls) in on.cenv.blocks do
    if (n.pretty.splitOn ".below").length > 1 then
      IO.println s!"[pass3-view] compiler block of {n.pretty}: {cls.map (·.map (·.pretty))}"
  let inp := Ix.Compile.Pass.viewInput on.cenv
  for (_, all) in on.cenv.p3Blocks do
    IO.println s!"[pass3-view] block {all.map (·.pretty)}"
    match Ix.Compile.Pass.buildView inp all with
    | .error e => IO.println s!"[pass3-view]   view error: {e}"
    | .ok v =>
      IO.println s!"[pass3-view]   Pass 1 classes {v.canon.components.map (·.classes.map (·.map (·.pretty)))}"
      for m in all do
        IO.println s!"[pass3-view]   compiler classes of {m.pretty}: {(on.cenv.blocks.get? m).map (·.map (·.map (·.pretty)))}"
      for (n, c) in v.canonConsts do
        if let .recInfo rv := c then IO.println s!"[pass3-view]   view rec {n.pretty} : {Tests.Ix.Compile.Image.toLeanExpr rv.cnst.type}"
      for (n, b) in v.back do IO.println s!"[pass3-view]   back {n.pretty} ↦ {b.pretty}"
      for r in Ix.Compile.Pass.imageKinds inp.const? all do
        if let some (.recInfo _) := inp.const? r then
          match v.image inp r with
          | .ok img => IO.println s!"[pass3-view]   image {r.pretty} := {Tests.Ix.Compile.Image.toLeanExpr img.value}\n{String.intercalate "\n" (img.log.toList.map ("      " ++ ·))}"
          | .error e => IO.println s!"[pass3-view]   image {r.pretty}: {e}"
  return 0

/-- Debugging aid: `PASS3_CLOSURE=<file.lean>,<constant>` compiles the
closure of one constant of the file's environment with the switch off and on,
timing both. -/
def runClosure (path : String) (c : String) : IO UInt32 := do
  let env ← getFileEnv path
  let n := c.toName
  let closure := closureOf env [n]
  IO.println s!"[pass3-closure] {c}: {closure.length} constants"
  let u : CUnit := { name := c, env, seeds := #[n], closure }
  for p3 in [false, true] do
    let t0 ← IO.monoMsNow
    let o ← compileUnit u p3
    IO.println s!"[pass3-closure] pass3={p3}: {o.bytes.size} bytes, {o.cenv.ungrounded.size} failures, {(← IO.monoMsNow) - t0} ms"
  return 0

/-! ## The suite -/

/-- Fixtures Lean itself rejects (the aux-cert record: audit notes). -/
def leanRejects : List String := ["PropEvap", "SortU", "SortURec", "SortUOpt"]

def auxCertFiles : List String :=
  Tests.Ix.Compile.AuxCert.fixtures.map fun f => s!"Tests/Ix/Compile/AuxCert/{f.stem}.lean"

def protoFiles : List String :=
  ["C1Perm", "C2Split", "C3PropSplit", "C4Evap", "C5Collapse", "C6NestedCollapse", "C7IndPred",
   "C8Collapse3", "C9Params"].map fun s => s!"Tests/Ix/Compile/Image/{s}.lean"

def run (env : Environment) : IO UInt32 := do
  if let some spec := ← IO.getEnv "PASS3_CLOSURE" then
    match spec.splitOn "," with
    | [p, c] => return ← runClosure p c
    | _ => return 2
  if let some p := ← IO.getEnv "PASS3_VIEW" then return ← runView p
  if let some spec := ← IO.getEnv "PASS3_FIND" then
    match spec.splitOn "," with
    | p :: pfxs => return ← runFind p pfxs
    | _ => return 2
  if let some spec := ← IO.getEnv "PASS3_LIB" then
    match spec.splitOn "," with
    | [a, b] => return ← runLib a b
    | _ => IO.println "[pass3-lib] PASS3_LIB=<switch-off.ixe>,<switch-on.ixe>"; return 2
  let only := ((← IO.getEnv "PASS3_ONLY").map (·.splitOn ",")).getD []
  let keep? := (← IO.getEnv "PASS3_KEEP").map System.FilePath.mk
  let want := fun (s : String) => only.isEmpty || only.contains s
  let mut units : Array (String × IO CUnit) := #[]
  for p in auxCertFiles ++ protoFiles do
    let stem := (System.FilePath.mk p).fileStem.getD p
    if want stem then units := units.push (stem, unitOfFile p)
  if want "twins" then
    units := units.push ("twins", do
      let (seeds, _) := Tests.Ix.Compile.Twins.familyClosure env
        Tests.Ix.Compile.Twins.allFamilies
      pure { name := "twins", env, seeds, closure := closureOf env seeds.toList })
  if want "corpus" then
    units := units.push ("corpus", do
      let closure := closureOf env ((validateAuxClosure env).map (·.1))
      pure { name := "corpus", env, seeds := (closure.map (·.1)).toArray, closure })
  let mut problems : Array String := #[]
  -- negative control: an input name with the reserved component `_ix`
  if want "ReservedIx" then
    let u ← unitOfFile "Tests/Ix/Compile/AuxCert/ReservedIx.lean"
    let offOk ← try (do discard <| compileUnit u false; pure true) catch _ => pure false
    let msg ← try (do discard <| compileUnit u true; pure "compiled") catch e => pure (toString e)
    let rejected : Bool := decide ((msg.splitOn "reserved component").length > 1)
    IO.println s!"[pass3] ReservedIx: switch off compiles {offOk}; switch on rejects {rejected}: {msg.take 200}"
    if !offOk || !rejected then problems := problems.push "ReservedIx: the reserved `_ix` name is not handled"
  for (stem, mk) in units do
    let u? ← (some <$> mk).toBaseIO
    let u ← match u? with
      | .ok (some u) => pure u
      | .ok none => continue
      | .error e =>
        if leanRejects.contains stem then
          IO.println s!"[pass3] {stem}: Lean itself rejects the file (aux-cert record)"
        else
          IO.println s!"[pass3] FAIL {stem}: {e}"
          problems := problems.push s!"{stem}: {e}"
        continue
    try
      let (ps, lines) ← runUnit u keep?
      for l in lines do IO.println s!"[pass3] {l}"
      for p in ps do IO.println s!"[pass3] FAIL {p}"
      problems := problems ++ ps
    catch e =>
      IO.println s!"[pass3] FAIL {e}"
      problems := problems.push (toString e)
  IO.println s!"[pass3] {units.size} units, {problems.size} problem(s)"
  return if problems.isEmpty then 0 else 1

end Tests.Ix.Compile.Pass3
