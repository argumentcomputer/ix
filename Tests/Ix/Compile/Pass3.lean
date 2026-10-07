/-
  pass3: the gates of Pass 3, the faithful rewrite (the only mode of both
  compilers since M6R slice 6; design document §4.5-4.6, `Ix.Compile.Pass`),
  on every fixture family:
  the aux-cert reproducers (`Tests/Ix/Compile/AuxCert/*.lean`), the
  prototype's cases (`Tests/Ix/Compile/Image/C*.lean`), the twin families
  (`Tests/Ix/Compile/Twins/*`) and the decompile-diff corpus
  (`validateAuxClosure`).

  Per compile unit (a fixture's closure), compiled in-process by the Lean
  pipeline (`compileLeanInput`):

  1. **names**: every input constant is emitted or has a recorded block
     failure; every named entry of the output is an input constant, a
     reserved `_ix` name or a synthetic `Muts` name; every block failure is a
     recorded root (`Pass3Kernels.compileFailures`), a consequence of one, or
     a recorded refusal of the images (`switchOnRefusals`). (Until M6R slice
     6 the unit was also compiled with the legacy surgery, `IX_PASS3=off`, and
     step 1 was the identity of the two outputs outside the changed blocks'
     cones; that mode is deleted.)
  2. **decompile**: the output, decompiled by the Lean decompiler
     (`decompileEnvFullParallel`), equals the source constants (the
     decompile-diff buckets: plain, aux, call-site, coverage, all zero), but
     for the documented roundtrip defects (`Pass3Kernels.decompileKnown`,
     by unit and constant, checked both ways);
  3. **kernels**: `ix check-rs`, `ix check-lean` (meta mode) and the
     certified checker (`kernel-check-ixe`) on the output (every fixture
     constant and every `_ix` name); every failure, and only those, must
     be in the record (`Tests.Ix.Compile.Pass3Kernels.table`, by cause), and
     each leg must check every requested name (declines only in documented
     classes);
  4. **computation rules**: for each changed block, the images of its
     recursors and their rule statements (`RuleStmt`, proof `Eq.refl`) are
     compiled into a test-only copy of the output (never into `E`) and
     checked by the three kernels;
  5. the `_ix` display names exist for every changed block.

  Run with: `lake test -- --ignored pass3` (after `lake build ix
  kernel-check-ixe`). `PASS3_ONLY` restricts the units (comma-separated
  stems or `twins`, `corpus`); `PASS3_KEEP=<dir>` keeps the outputs;
  `PASS3_FAILURES=<file>` writes every kernel failure; `PASS3_RECHECK` and
  `PASS3_EXPECT_EMIT` rerun the kernels on kept outputs and write the record
  from the dumps (see `runRecheck` and `Pass3Kernels.emit`).
-/
import Ix.Meta
import Ix.EnvScope
import Ix.Benchmark.Results
import Ix.CompileM
import Ix.CompileDriver
import Ix.DecompileDriver
import Ix.Compile.Pass
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.Compile.AuxCert
import Tests.Ix.Compile.KernelReport
import Tests.Ix.Compile.Pass3Kernels
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

def compileUnit (u : CUnit) : IO Ix.CompileM.LeanPipelineOut := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv u.env u.closure).mapError toString)
  match ← Ix.CompileM.compileLeanInput input (numWorkers := 32) with
  | .ok o => pure o
  | .error e => throw (IO.userError s!"{u.name}: Lean compile failed: {e}")

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

/-! ## 1. Changed blocks and names -/

/-- What step 1 reports: the changed blocks, the counts of the output's named
entries by kind, and the problems. -/
structure NamesReport where
  changedBlocks : Array (Array _root_.Ix.Name) := #[]
  inputNames : Nat := 0
  reserved : Nat := 0
  problems : Array String := #[]

/-- The changed blocks of the output (`CompileEnv.p3Blocks`), and its named
entries: every input constant is emitted or recorded as ungrounded, and
every output entry is a constant of the input environment, a reserved `_ix`
name (D14) or a synthetic `Muts` name, so Pass 3 invents no other name. Until
M6R slice 6 this step compared the output with the legacy surgery's
(`IX_PASS3=off`): byte-identical without a changed block, every moved name in
a changed block's cone, every new name reserved. That mode is deleted; the
identity it checked is the flip's (M6) evidence, and the fixture outputs are
compared before and after the deletion by the slice's own gate. -/
def namesCheck (u : CUnit) (on : Ix.CompileM.LeanPipelineOut) : NamesReport := Id.run do
  let blocks := on.cenv.p3Blocks.toArray.map (·.2)
  let mut r : NamesReport := { changedBlocks := blocks }
  -- Partial outputs skip the whole-environment decompile below, and kernel
  -- requests are built from emitted names. Check source coverage here too:
  -- a missing name must not disappear from both checks without a refusal.
  for (n, _) in u.closure do
    let name := ixN n
    unless on.env.named.contains name || on.cenv.ungrounded.contains name do
      r := { r with problems := r.problems.push s!"{name.pretty} is neither emitted nor recorded as ungrounded" }
  for (n, _) in on.env.named do
    if isSyntheticMuts n then continue
    if Ix.Compile.Pass.hasReserved n then r := { r with reserved := r.reserved + 1 }
    else if u.env.contains (toLeanName n) then r := { r with inputNames := r.inputNames + 1 }
    else r := { r with problems := r.problems.push s!"{n.pretty} is neither an input constant nor a reserved name" }
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

/-- The failures of one kernel run, `(leg, name, message)`, and the number of
constants each leg reports it checked. -/
structure KernelRun where
  failed : Array (String × String × String)
  checked : List (String × Nat)

/-- `(leg, name, message)` of every failure of the three kernels on `names`
of the file `path`, and each leg's checked count. Declines of the certified
checker in documented classes are not failures. Process/report failures
throw instead of entering the per-name known-failure accounting. -/
def kernelRun (dir : System.FilePath) (path : System.FilePath) (names : Array String)
    (anon : Bool := false) (skipDeps : Bool := false) :
    IO KernelRun := do
  if names.isEmpty then throw (IO.userError "kernel check requested no names")
  let mut failed : Array (String × String × String) := #[]
  let namesFile := dir / "names.txt"
  IO.FS.writeFile namesFile ("\n".intercalate names.toList ++ "\n")
  -- Resolve all requested names from the environment. The certified checker
  -- reports owning records, with at most three display names per record.
  let parts ← IO.ofExcept (Ixon.deEnvVerifiedLazy (← IO.FS.readBinFile path))
  let byName : Std.HashMap String String := parts.namedRows.foldl (fun m row =>
    m.insert row.name.pretty (toString (Tests.Ix.Compile.AuxCert.recordOf parts.env row.addr))) {}
  let rawAddresses : Std.HashMap String String := parts.namedRows.foldl
    (fun m row => m.insert row.name.pretty (toString row.addr)) {}
  let mut expected : Array (String × String) := #[]
  let mut anonNames : Std.HashMap String (Array String) := {}
  for n in names do
    let some address := byName[n]?
      | throw (IO.userError s!"kernel check requested a name absent from the output: {n}")
    expected := expected.push (n, address)
    let some rawAddress := rawAddresses[n]?
      | throw (IO.userError s!"missing anonymous address for {n}")
    anonNames := anonNames.insert rawAddress ((anonNames.getD rawAddress #[]).push n)
  -- certified checker (whole file; acceptance is a row verdict, not exit 0)
  let certPath := dir / "cert.jsonl"
  let cert ← runProc certExe #[path.toString, certPath.toString, "--jobs", "8"]
  IO.FS.writeFile (dir / "cert.stdout") cert.stdout
  IO.FS.writeFile (dir / "cert.stderr") cert.stderr
  unless ← certPath.pathExists do
    throw (IO.userError s!"kernel-check-ixe wrote no report (exit {cert.exitCode})")
  let report ← IO.ofExcept (KernelReport.parse (← IO.FS.readFile certPath) cert.exitCode)
  IO.ofExcept (KernelReport.checkCoverage report expected)
  for (n, address) in expected do
    let some verdict := report[address]?
      | throw (IO.userError s!"missing certified verdict for {n}@{address}")
    if verdict.outcome == "accept" then continue
    if verdict.outcome == "decline" && Tests.Ix.Compile.AuxCert.documentedDecline verdict.reason then continue
    failed := failed.push ("cert", n, s!"{verdict.outcome}: {verdict.reason}")
  -- check-rs, meta mode, the names
  -- every failure comes from the fail-out file (stdout shows the first 30)
  let rsFailOut := dir / "rs.fail"
  if ← rsFailOut.pathExists then IO.FS.removeFile rsFailOut
  let rs ← runProc ixExe ((#["check-rs", path.toString, "--consts-file", namesFile.toString,
    "--fail-out", rsFailOut.toString] ++ (if anon then #["--anon"] else #[])
    ++ (if anon && skipDeps then #["--skip-deps"] else #[])))
  IO.FS.writeFile (dir / "rs.stdout") rs.stdout
  IO.FS.writeFile (dir / "rs.stderr") rs.stderr
  if rs.exitCode == 0 && ((rs.stdout ++ rs.stderr).splitOn "[check] 0/0 passed").length > 1 then
    throw (IO.userError "check-rs checked zero targets")
  let rsNames := fun (label : String) => match KernelReport.anonymousAddress? label with
    | some address => anonNames.getD address #[label]
    | none => #[label]
  let rsRows ← if ← rsFailOut.pathExists then pure (KernelReport.failOutRows (← IO.FS.readFile rsFailOut))
    else pure #[]
  for (label, m) in rsRows do
    for n in rsNames label do failed := failed.push ("rs", n, m)
  let rsN := KernelReport.rsChecked (rs.stdout ++ rs.stderr)
  if rs.exitCode != 0 && rsRows.isEmpty then
    failed := failed.push ("rs", "*", s!"check-rs exit {rs.exitCode}: {((rs.stdout ++ rs.stderr).takeEnd 300).toString}")
  -- Lean anon selectors are addresses, unlike Rust's source-name selectors.
  -- Write bare hex: the shared names-file grammar treats `#` as a comment.
  let leanNamesFile := dir / "lean-names.txt"
  let leanNames := if anon then (anonNames.toArray.map (·.1)).qsort (· < ·) else names
  IO.FS.writeFile leanNamesFile ("\n".intercalate leanNames.toList ++ "\n")
  let failOut := dir / "lean.fail"
  -- meta mode: every work item from a fresh worker state (`--clear-every 1`).
  -- The kernel's caches are keyed by name-insensitive expression addresses,
  -- so with warm caches a reference to an alias without its own entry
  -- (BB-F7) resolves through a type another item of the same worker cached,
  -- and whether it fails would depend on the work-stealing order (FU item
  -- 13: one run in many counted one `unknown constant` more).
  let ln ← runProc ixExe (#["check-lean", path.toString, "--consts-file", leanNamesFile.toString,
    "--fail-out", failOut.toString, "--workers", "8"]
    ++ if anon then #["--anon"] else #["--clear-every", "1"])
  IO.FS.writeFile (dir / "lean.stdout") ln.stdout
  IO.FS.writeFile (dir / "lean.stderr") ln.stderr
  let leanN ← if ln.exitCode == 0 || ln.exitCode == Ix.Benchmark.Results.exitRejected then
      some <$> IO.ofExcept (KernelReport.checkedLeanTargets ln.stdout)
    else pure none
  let leanFails ← if ← failOut.pathExists then
      pure (KernelReport.leanFailureLabels (← IO.FS.readFile failOut) anon)
    else pure #[]
  -- messages from the fail-out file (stdout shows the first 30)
  let msgs ← if ← failOut.pathExists then pure (KernelReport.failOutRows (← IO.FS.readFile failOut))
    else pure #[]
  let reportNames := fun label => if anon then
      let address := (KernelReport.anonymousAddress? label).getD label
      anonNames.getD address #[label]
    else #[label]
  for label in KernelReport.leanUnmatched (ln.stdout ++ ln.stderr) do
    for n in reportNames label do
      failed := failed.push ("lean", n, "requested selector matched no checkable work item")
  for n in leanFails do
    let n := n.trimAscii.toString
    let m := (msgs.find? fun (label, _) =>
      if anon then KernelReport.anonymousAddress? label == some n else label == n).map (·.2) |>.getD ""
    for original in reportNames n do failed := failed.push ("lean", original, m)
  if leanFails.isEmpty && ln.exitCode != 0 then
    failed := failed.push ("lean", "*", s!"check-lean exit {ln.exitCode}: {((ln.stdout ++ ln.stderr).takeEnd 300).toString}")
  return { failed, checked := [("cert", expected.size), ("rs", rsN.getD 0), ("lean", leanN.getD 0)] }

/-- `(leg, name, message)` of every failure of the three kernels on `names`
of the file `path` (`kernelRun` without the checked counts). -/
def kernelFailures (dir : System.FilePath) (path : System.FilePath) (names : Array String)
    (anon : Bool := false) : IO (Array (String × String × String)) :=
  (·.failed) <$> kernelRun dir path names anon

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
      let name := r
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

/-! ## O11a: is Lean's mutual `_sizeOf` of a split member the instance form, by δ? -/

/-- The members of `Linear.EqCnstr`'s block (the library twins, `Oracle.Lib`). -/
def o11aMembers : List Name :=
  [`EqCnstr, `EqCnstrProof, `IneqCnstr, `IneqCnstrProof, `DiseqCnstr, `DiseqCnstrProof,
   `UnsatProof].map (`Lean.Meta.Grind.Arith.Linear ++ ·)

/-- One `rfl` per member, in a test-only copy of the twins' switch-on output:
`(fun t => @sizeOf Orig.X Orig.X._sizeOf_inst t) = (fun t => @sizeOf Twin.X
Twin.X._sizeOf_inst t)`. `Orig` is the block as Lean declares it (its
`_sizeOf_N` inline the block recursor, relocated by Pass 3 for the split);
`Twin` declares the components separately (its `_sizeOf` goes through the
instances of the other components). The kernels decide whether the two are
definitionally equal (δ of the instances and the `_sizeOf` functions, β,
projection; no induction). -/
def o11aEnv (on : Ix.CompileM.LeanPipelineOut) : Except String (Ixon.Env × Array String) := do
  let mut env := on.env
  let mut names : Array String := #[]
  let one := _root_.Ix.Level.mkSucc _root_.Ix.Level.mkZero
  let nat := _root_.Ix.Expr.mkConst (ixN ``Nat) #[]
  let mut known : Std.HashMap _root_.Ix.Name Address := {}
  for m in o11aMembers do
    let o := `Tests.Ix.Compile.Oracle.Lib.Orig ++ m
    let t := `Tests.Ix.Compile.Oracle.Lib.Twin ++ m
    let side := fun (x : Name) =>
      _root_.Ix.Expr.mkLam (ixN `t) (_root_.Ix.Expr.mkConst (ixN x) #[])
        (_root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkApp
          (_root_.Ix.Expr.mkConst (ixN ``SizeOf.sizeOf) #[one]) (_root_.Ix.Expr.mkConst (ixN x) #[]))
          (_root_.Ix.Expr.mkConst (ixN (x ++ `_sizeOf_inst)) #[])) (_root_.Ix.Expr.mkBVar 0))
        .default
    let ty := _root_.Ix.Expr.mkForallE (ixN `t) (_root_.Ix.Expr.mkConst (ixN t) #[]) nat .default
    let lhs := side o
    let rhs := side t
    let stmt := _root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkApp
      (_root_.Ix.Expr.mkConst (ixN ``Eq) #[one]) ty) lhs) rhs
    let pf := _root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkApp
      (_root_.Ix.Expr.mkConst (ixN ``Eq.refl) #[one]) ty) lhs
    let name := ixN (`o11a ++ m)
    let tv : _root_.Ix.TheoremVal := {
      cnst := { name, levelParams := #[], type := stmt }, value := pf, all := #[name] }
    let (env', a) ← addConst on.cenv known env (.thmInfo tv)
    env := env'
    known := known.insert name a
    names := names.push name.pretty
  return (env, names)

/-! ## Expectations

The kernel failures of both switch states are recorded per unit in
`Tests.Ix.Compile.Pass3Kernels.table` (KF triage, 2026-10-05). -/

/-- The Lean name an `_ix` display name stands for (`x._ix.S ↦ x.S`, a
re-typed handler `p._ix_retyped.s ↦ p.s`, an image `a._ix ↦ a`). -/
def leanOf (s : String) : String :=
  let s := if s.endsWith "._ix" then (s.dropEnd 4).toString else s
  String.intercalate "." ((s.splitOn ".").filter (fun c => c != "_ix" && c != "_ix_retyped"))

/-- The failures that follow from recorded root failures (`roots`, the
constants `Pass3Kernels.compileFailures` names): a failure whose message names
(a member of) a root or an earlier consequence, to a fixed point. (Until M6R
slice 6 the roots were the constants failing in both switch states.) -/
def refusalClosure (roots : Std.HashSet _root_.Ix.Name) (on : Ix.CompileM.LeanPipelineOut) :
    Std.HashSet _root_.Ix.Name := Id.run do
  let mut bad : Std.HashSet String := roots.fold (fun s n => s.insert n.pretty) {}
  let mut out : Std.HashSet _root_.Ix.Name := {}
  let mut changed := true
  while changed do
    changed := false
    for (n, e) in on.cenv.ungrounded do
      if out.contains n || roots.contains n then continue
      let msg := leanOf e
      if bad.toList.any fun b => (msg.splitOn b).length > 1 then
        out := out.insert n
        bad := bad.insert n.pretty
        changed := true
  return out

/-! ## One unit -/

/-- A dotted name with numeric components (`_private.M.0.f`). -/
def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (init := .anonymous) fun n c =>
    match c.toNat? with
    | some k => .num n k
    | none => .str n c

/-! ## Expression comparison helpers (the pass checks, `PASS3_LIB`) -/

/-- The expressions of the constant at `addr`, with the constant whose tables
they index (a projection's block). -/
def ixonBody (env : Ixon.Env) (addr : Address) : Option (Ixon.Constant × Array (String × Ixon.Expr)) := do
  let c ← env.getConst? addr
  let ofMut (b : Ixon.Constant) (idx : UInt64) (cidx : Option UInt64) : Option (Ixon.Constant × Array (String × Ixon.Expr)) :=
    match b.info with
    | .muts ms => match ms[idx.toNat]?, cidx with
      | some (.defn d), _ => some (b, #[("type", d.typ), ("value", d.value)])
      | some (.recr r), _ => some (b, #[("type", r.typ)] ++ r.rules.zipIdx.map fun (rr, i) => (s!"rule{i}", rr.rhs))
      | some (.indc i), none => some (b, #[("type", i.typ)])
      | some (.indc i), some k => (i.ctors[k.toNat]?).map fun ct => (b, #[("type", ct.typ)])
      | none, _ => none
    | _ => none
  match c.info with
  | .defn d => some (c, #[("type", d.typ), ("value", d.value)])
  | .recr r => some (c, #[("type", r.typ)] ++ r.rules.zipIdx.map fun (rr, i) => (s!"rule{i}", rr.rhs))
  | .axio a => some (c, #[("type", a.typ)])
  | .quot q => some (c, #[("type", q.typ)])
  | .dPrj p => do ofMut (← env.getConst? p.block) p.idx none
  | .rPrj p => do ofMut (← env.getConst? p.block) p.idx none
  | .iPrj p => do ofMut (← env.getConst? p.block) p.idx none
  | .cPrj p => do ofMut (← env.getConst? p.block) p.idx (some p.cidx)
  | .muts _ => none

/-- Expand a sharing reference (bounded: a sharing entry only refers to
earlier entries). -/
def ixonExpand (c : Ixon.Constant) : Nat → Ixon.Expr → Ixon.Expr
  | fuel + 1, .share i => match c.sharing[i.toNat]? with
    | some e => ixonExpand c fuel e
    | none => .share i
  | _, e => e

/-- The application spine of an Ixon expression (shares expanded). -/
def ixonSpine (c : Ixon.Constant) (e : Ixon.Expr) : Ixon.Expr × Array Ixon.Expr := Id.run do
  let mut args : Array Ixon.Expr := #[]
  let mut cur := ixonExpand c 64 e
  for _ in [0:1 <<< 20] do
    match cur with
    | .app f a => args := args.push a; cur := ixonExpand c 64 f
    | _ => break
  return (cur, args.reverse)

/-- A compact, depth-limited rendering (refs by name). -/
partial def ixonShow (c : Ixon.Constant) (nm : Address → String) (d : Nat) (e : Ixon.Expr) : String :=
  if d == 0 then "…" else
  let e := ixonExpand c 64 e
  let univ := fun (i : UInt64) => match c.univs[i.toNat]? with
    | some u => reprStr u
    | none => s!"?u{i}"
  match e with
  | .sort i => s!"Sort({univ i})"
  | .var i => s!"#{i}"
  | .ref i us => s!"{(c.refs[i.toNat]?).map nm |>.getD s!"?r{i}"}.{us.toList.map univ}"
  | .recur i _ => s!"rec#{i}"
  | .prj t i x => s!"({ixonShow c nm (d - 1) x}).{(c.refs[t.toNat]?).map nm |>.getD "?"}#{i}"
  | .str i => s!"str:{(c.refs[i.toNat]?).map toString |>.getD "?"}"
  | .nat i => s!"nat:{(c.refs[i.toNat]?).map toString |>.getD "?"}"
  | .app .. =>
    let (h, as) := ixonSpine c e
    "(" ++ " ".intercalate ((#[h] ++ as).toList.map (ixonShow c nm (d - 1))) ++ ")"
  | .lam _ t b => s!"(λ {ixonShow c nm (d - 1) t}. {ixonShow c nm (d - 1) b})"
  | .all _ _ t b => s!"(∀ {ixonShow c nm (d - 1) t}. {ixonShow c nm (d - 1) b})"
  | .letE _ t v b => s!"(let {ixonShow c nm (d - 1) t} := {ixonShow c nm (d - 1) v}; {ixonShow c nm (d - 1) b})"
  | .share i => s!"share#{i}"

/-- The first difference of two Ixon expressions over their own tables: the
path (`argK`, `body`, …) and the two subterms. -/
partial def ixonFirstDiff (ca cb : Ixon.Constant) (path : String) (a b : Ixon.Expr) :
    Option (String × Ixon.Expr × Ixon.Expr) :=
  let a := ixonExpand ca 64 a
  let b := ixonExpand cb 64 b
  let uEq := fun (us vs : Array UInt64) =>
    us.size == vs.size && (us.zip vs).all fun (i, j) => ca.univs[i.toNat]? == cb.univs[j.toNat]?
  let rEq := fun (i j : UInt64) => ca.refs[i.toNat]? == cb.refs[j.toNat]?
  let here := some (path, a, b)
  match a, b with
  | .sort i, .sort j => if uEq #[i] #[j] then none else here
  | .var i, .var j => if i == j then none else here
  | .ref i us, .ref j vs => if rEq i j && uEq us vs then none else here
  | .recur i us, .recur j vs => if i == j && uEq us vs then none else here
  | .prj t i x, .prj t' i' y => if rEq t t' && i == i' then ixonFirstDiff ca cb (path ++ ".proj") x y else here
  | .str i, .str j | .nat i, .nat j => if rEq i j then none else here
  | .app .., .app .. =>
    let (f, xs) := ixonSpine ca a
    let (g, ys) := ixonSpine cb b
    if xs.size != ys.size then here else
    match ixonFirstDiff ca cb (path ++ ".head") f g with
    | some d => some d
    | none => (xs.zip ys).zipIdx.findSome? fun ((x, y), k) => ixonFirstDiff ca cb (path ++ s!".arg{k}") x y
  | .lam _ t x, .lam _ t' y | .all _ _ t x, .all _ _ t' y =>
    match ixonFirstDiff ca cb (path ++ ".dom") t t' with
    | some d => some d
    | none => ixonFirstDiff ca cb (path ++ ".body") x y
  | .letE _ t v x, .letE _ t' v' y =>
    match ixonFirstDiff ca cb (path ++ ".ty") t t' with
    | some d => some d
    | none => match ixonFirstDiff ca cb (path ++ ".val") v v' with
      | some d => some d
      | none => ixonFirstDiff ca cb (path ++ ".body") x y
  | _, _ => here

/-- An address ↦ name map of an output (one name per address, `_ix` names last). -/
def addrNames (env : Ixon.Env) : Std.HashMap Address String :=
  env.named.fold (init := {}) fun m n nd =>
    match m.get? nd.addr with
    | some old => if (old.splitOn "._ix").length > 1 then m.insert nd.addr n.pretty else m
    | none => m.insert nd.addr n.pretty

/-- The first difference between the switch-off and switch-on forms of a
constant, rendered. -/
def describeDiff (off on : Ixon.Env) (offNames onNames : Std.HashMap Address String)
    (a b : Address) : String := Id.run do
  let some (ca, xs) := ixonBody off a | return "no switch-off body"
  let some (cb, ys) := ixonBody on b | return "no switch-on body"
  if xs.size != ys.size then return s!"different shapes ({xs.size} vs {ys.size} expressions)"
  for ((l, x), (_, y)) in xs.zip ys do
    if let some (p, u, v) := ixonFirstDiff ca cb l x y then
      let nmA := fun (ad : Address) => (offNames.get? ad).getD (String.ofList ((toString ad).toList.take 12))
      let nmB := fun (ad : Address) => (onNames.get? ad).getD (String.ofList ((toString ad).toList.take 12))
      return s!"{p}\n        off: {(ixonShow ca nmA 6 u).take 1200}\n        on:  {(ixonShow cb nmB 6 v).take 1200}"
  let extra := ca.refs.filter (!cb.refs.contains ·)
  let missing := cb.refs.filter (!ca.refs.contains ·)
  return s!"same expressions; tables: refs {ca.refs.size}/{cb.refs.size} (only off: {extra.toList.map fun ad => (offNames.get? ad).getD (toString ad)}; only on: {missing.toList.map fun ad => (onNames.get? ad).getD (toString ad)}), univs {ca.univs.size}/{cb.univs.size}, sharing {ca.sharing.size}/{cb.sharing.size}; same order: refs {ca.refs == cb.refs}, univs {ca.univs == cb.univs}, sharing {ca.sharing == cb.sharing}"

/-- `describeDiff` within one output, following a differing reference up to
`depth` times (twin diagnostics). -/
partial def describeDeep (env : Ixon.Env) (nm : Std.HashMap Address String) (a b : Address)
    (depth : Nat) : String := Id.run do
  let here := describeDiff env env nm nm a b
  if depth == 0 then return here
  let some (ca, xs) := ixonBody env a | return here
  let some (cb, ys) := ixonBody env b | return here
  for ((l, x), (_, y)) in xs.zip ys do
    if let some (_, .ref i _, .ref j _) := ixonFirstDiff ca cb l x y then
      if let (some ra, some rb) := (ca.refs[i.toNat]?, cb.refs[j.toNat]?) then
        if ra != rb then
          return s!"{here}\n      → {(nm.get? ra).getD "?"} / {(nm.get? rb).getD "?"}: {describeDeep env nm ra rb (depth - 1)}"
  return here

/-! ## The definitional passes' fixtures (A4, `Tests/Ix/Compile/Pass/`) -/

/-- The per-pass fixtures. -/
def passFiles : List String :=
  ["O1Perm", "O2Split", "O3Cases", "O4BRecOn", "O5PropSplit"].map
    fun s => s!"Tests/Ix/Compile/Pass/{s}.lean"

/-- Twins with the switch on: the two constants have one address (the pass
made the permuted presentation's term the canonical one's). -/
def passTwins : List (String × String × String) := [
  ("O1Perm", "PassO1.Src.Even.viaRec", "PassO1.Can.Even.viaRec"),
  ("O1Perm", "PassO1.Src.Odd.viaRecOn", "PassO1.Can.Odd.viaRecOn"),
  ("O1Perm", "PassO1.Src.viaRec_two", "PassO1.Can.viaRec_two"),
  ("O1Perm", "PassO1.Src.viaRecOn_three", "PassO1.Can.viaRecOn_three"),
  ("O3Cases", "PassO3.Src.Even.isZero", "PassO3.Can.Even.isZero"),
  ("O3Cases", "PassO3.Src.SA.isStop", "PassO3.Can.SA.isStop"),
  ("O3Cases", "PassO3.Src.SB.isLeaf", "PassO3.Can.SB.isLeaf"),
  ("O4BRecOn", "PassO4.Src.Odd.toNat", "PassO4.Can.Odd.toNat"),
  ("O4BRecOn", "PassO4.Src.Even.toNat", "PassO4.Can.Even.toNat"),
  ("O4BRecOn", "PassO4.Src.three", "PassO4.Can.three"),
  ("O4BRecOn", "PassO4.Src.SB.depth", "PassO4.Can.SB.depth"),
  ("O4BRecOn", "PassO4.Src.depth_two", "PassO4.Can.depth_two")]
  -- O11a (A6f): Lean's mutual `_sizeOf_N` of the split Linear block, in the
  -- instance form, is the separately declared components' `_sizeOf`, so the
  -- library twins' instances (`SizeOf.mk X X._sizeOf_k`) have one address
  ++ o11aMembers.map fun m =>
    ("twins", s!"{`Tests.Ix.Compile.Oracle.Lib.Orig ++ m ++ `_sizeOf_inst}",
     s!"{`Tests.Ix.Compile.Oracle.Lib.Twin ++ m ++ `_sizeOf_inst}")

/-- Pass firing, read off the switch-on output: the constant references (or
does not reference) the named constant. `(unit, constant, referenced name,
expected)`. -/
def passRefs : List (String × String × String × Bool) := [
  -- O1: `recOn` goes to the Ix `recOn`; the collapsed block keeps the paired image
  ("O1Perm", "PassO1.Src.Odd.viaRecOn", "PassO1.Src.Odd._ix.recOn", true),
  ("O1Perm", "PassO1.Col.A.viaRec", "PProd", true),
  -- O3: the Ix `casesOn` of the class (permuted, split); declines on a collapsed block
  ("O3Cases", "PassO3.Src.Even.isZero", "PassO3.Src.Even._ix.casesOn", true),
  ("O3Cases", "PassO3.Src.SA.isStop", "PassO3.Src.SA._ix.casesOn", true),
  ("O3Cases", "PassO3.Src.SB.isLeaf", "PassO3.Src.SB._ix.casesOn", true),
  ("O3Cases", "PassO3.Col.A.isNil", "PassO3.Col.A._ix.casesOn", false),
  -- O4: the Ix `brecOn`/`below` (permuted pair; the split block's lower component);
  -- declines on the upper component (cross field)
  ("O4BRecOn", "PassO4.Src.Odd.toNat", "PassO4.Src.Odd._ix.brecOn", true),
  ("O4BRecOn", "PassO4.Src.Even.toNat", "PassO4.Src.Even._ix.brecOn", true),
  ("O4BRecOn", "PassO4.Src.SB.depth", "PassO4.Src.SB._ix.brecOn", true),
  ("O4BRecOn", "PassO4.Src.SA.size", "PassO4.Src.SA._ix.brecOn", false),
  -- O2/O6: the component recursors; the bare occurrence keeps the image constant
  ("O2Split", "PassO2.SA.viaRec", "PassO2.SA._ix.rec", true),
  ("O2Split", "PassO2.SA.viaRec", "PassO2.SB._ix.rec", true),
  ("O2Split", "PassO2.SB.viaRec", "PassO2.SB._ix.rec", true),
  ("O2Split", "PassO2.SA.recBare", "PassO2.SA.rec", true),
  -- O5: the Ix auxiliaries at universe 0
  ("O5PropSplit", "PassO5.P.toQ", "PassO5.P._ix.casesOn", true),
  ("O5PropSplit", "PassO5.Q.elim", "PassO5.Q._ix.rec", true),
  ("O5PropSplit", "PassO5.P.viaRec", "PassO5.P._ix.rec", true)]

/-- Constants whose term reproduces the legacy surgery's (the definitional
pass rewrites the call site to the surgery's canonical spine), pinned by
address: until M6R slice 6 they were compared with the switch-off output
(`IX_PASS3=off`), byte for byte (`true`) or expression for expression with
the tables differing only by the surgery's leftover entries of dropped
arguments (`false`; design document §4.7 (e)). With the surgery deleted the
addresses are pinned instead, as measured by this suite on the slice-6 tree
(2026-10-07; the Rust compiler gives the same, `pass3-rust-parity`). Slice 6
changed no Pass 3 code path (`compileExprPartial` is the former driver path
with its plan maps, always empty under Pass 3, removed), so for a `true` row
the pin is the surgery's own address, the switch-off comparison having passed
at `e020a72e`. An empty pin is reported with the measured address. -/
def passSameAsSurgery : List (String × String × Bool × String) := [
  ("O1Perm", "PassO1.Src.Even.viaRec", true, ""),
  ("O1Perm", "PassO1.Src.viaRec_two", true, ""),
  ("O2Split", "PassO2.SA.viaRec", false, ""),
  ("O2Split", "PassO2.SB.viaRec", false, ""),
  ("O4BRecOn", "PassO4.Src.Odd.toNat", true, ""),
  ("O4BRecOn", "PassO4.Src.Even.toNat", true, ""),
  ("O4BRecOn", "PassO4.Src.SB.depth._f", false, "")]

/-! ## The proof-justified passes' fixtures (A6p, `Tests/Ix/Compile/Pass/`) -/

/-- The per-pass fixtures of O7–O12. -/
def pjPassFiles : List String :=
  ["O7Collapse", "O8Cases", "O9Split", "O10O12Collapse", "O11bNoConfusion"].map fun s => s!"Tests/Ix/Compile/Pass/{s}.lean"

/-- Twins with the switch on (one address). Decision 5 (D1): a
proof-justified pass writes its canonical form under `c._ix`, so the pairs
compare the `_ix` constants (and the helpers `p._ix_retyped.s`, `fg`) with the
canonical presentation's constants; constants no pass touches are compared
under their own names. -/
def pjPassTwins : List (String × String × String) := [
  ("O7Collapse", "PassO7.Src.A.viaRec._ix", "PassO7.Can.A.viaRec"),
  ("O7Collapse", "PassO7.Src.B.viaRecOn._ix", "PassO7.Can.B.viaRecOn"),
  ("O7Collapse", "PassO7.Src.Z.viaRec._ix", "PassO7.Can.Z.viaRec"),
  ("O8Cases", "PassO8.Src.A.isNil._ix", "PassO8.Can.A.isNil"),
  ("O8Cases", "PassO8.Src.B.isNil.match_1._ix", "PassO8.Can.B.isNil.match_1"),
  ("O8Cases", "PassO8.Src.Z.isE.match_1._ix", "PassO8.Can.Z.isE.match_1"),
  ("O8Cases", "PassO8.Src.A.noConfusionType._ix", "PassO8.Can.A.noConfusionType"),
  ("O8Cases", "PassO8.Src.A.isNil'._ix", "PassO8.Can.A.isNil'"),
  ("O11bNoConfusion", "PassO11b.Src.B.noConfusionType._ix", "PassO11b.Can.B.noConfusionType"),
  ("O11bNoConfusion", "PassO11b.Src.B.noConfusion._ix", "PassO11b.Can.B.noConfusion"),
  ("O11bNoConfusion", "PassO11b.Src.B.val", "PassO11b.Can.B.val"),
  ("O9Split", "PassO9.Src.A.len._ix", "PassO9.Can.A.len"),
  ("O9Split", "PassO9.Src.A.len._ix_retyped._f", "PassO9.Can.A.len._f"),
  ("O9Split", "PassO9.Src.A.sum._ix", "PassO9.Can.A.sum"),
  ("O9Split", "PassO9.Src.A.sum._ix_retyped._f", "PassO9.Can.A.sum._f"),
  ("O9Split", "PassO9.Src.A.cnt._ix", "PassO9.Can.A.cnt"),
  ("O9Split", "PassO9.Src.B.val", "PassO9.Can.B.val")]
  -- `O10O12Collapse`: its structural cliques are transported by the clique hook (A5), so O10
  -- and O12 do not fire there (design document §1.6.2): no `_ix` pair, see `passTwinsNC`

/-- Twin pairs that still differ with the switch on: each must have its entry
in `Tests.Ix.Compile.NonCanonical.nonCanonicalPasses` (fixture
`Tests.Ix.Compile.Pass.<unit>`, the `Src` constant), with the measured
addresses, and every entry must name a pair listed here. Decision 5 (D1):
the Lean name of every constant a proof-justified pass rewrote (cause
`PJ-FORM-<pass>`), and the constants over such a Lean name that no pass
rewrote (`INHERITED`: they refer to the Lean name, whose form did not change;
a caller that wants the canonical form refers to the `_ix` name). -/
def passTwinsNC : List (String × String × String) := [
  ("O7Collapse", "PassO7.Src.A.viaRec", "PassO7.Can.A.viaRec"),
  ("O7Collapse", "PassO7.Src.B.viaRecOn", "PassO7.Can.B.viaRecOn"),
  ("O7Collapse", "PassO7.Src.Z.viaRec", "PassO7.Can.Z.viaRec"),
  ("O8Cases", "PassO8.Src.A.isNil", "PassO8.Can.A.isNil"),
  ("O8Cases", "PassO8.Src.B.isNil.match_1", "PassO8.Can.B.isNil.match_1"),
  ("O8Cases", "PassO8.Src.B.isNil", "PassO8.Can.B.isNil"),
  ("O8Cases", "PassO8.Src.Z.isE.match_1", "PassO8.Can.Z.isE.match_1"),
  ("O8Cases", "PassO8.Src.Z.isE", "PassO8.Can.Z.isE"),
  ("O8Cases", "PassO8.Src.A.noConfusionType", "PassO8.Can.A.noConfusionType"),
  ("O8Cases", "PassO8.Src.A.isNil'", "PassO8.Can.A.isNil'"),
  ("O11bNoConfusion", "PassO11b.Src.B.noConfusionType", "PassO11b.Can.B.noConfusionType"),
  ("O11bNoConfusion", "PassO11b.Src.B.noConfusion", "PassO11b.Can.B.noConfusion"),
  ("O11bNoConfusion", "PassO11b.Src.nc", "PassO11b.Can.nc"),
  ("O11bNoConfusion", "PassO11b.Src.E.noConfusionType", "PassO11b.Can.E.noConfusionType"),
  ("O11bNoConfusion", "PassO11b.Src.E.noConfusion", "PassO11b.Can.E.noConfusion"),
  ("O9Split", "PassO9.Src.A.len", "PassO9.Can.A.len"),
  ("O9Split", "PassO9.Src.A.sum", "PassO9.Can.A.sum"),
  ("O9Split", "PassO9.Src.A.cnt", "PassO9.Can.A.cnt"),
  ("O9Split", "PassO9.Src.len2", "PassO9.Can.len2"),
  ("O9Split", "PassO9.Src.len3", "PassO9.Can.len3"),
  ("O9Split", "PassO9.Src.sum2", "PassO9.Can.sum2"),
  ("O9Split", "PassO9.Src.len_succ", "PassO9.Can.len_succ"),
  ("O9Split", "PassO9.Src.cnt1", "PassO9.Can.cnt1"),
  ("O9Split", "PassO9.Src.A.len._f", "PassO9.Can.A.len._f"),
  ("O9Split", "PassO9.Src.A.sum._f", "PassO9.Can.A.sum._f"),
  ("O10O12Collapse", "PassO10.Src.A.h", "PassO10.Can.X.h"),
  ("O10O12Collapse", "PassO10.Src.B.k", "PassO10.Can.X.h"),
  ("O10O12Collapse", "PassO10.Src.h_two", "PassO10.Can.h_two"),
  ("O10O12Collapse", "PassO10.Src.A.f", "PassO10.Perm.A.f"),
  ("O10O12Collapse", "PassO10.Src.B.g", "PassO10.Perm.B.g"),
  ("O10O12Collapse", "PassO10.Src.fg_ab", "PassO10.Perm.fg_ab"),
  ("O10O12Collapse", "PassO10.Src.fg_bab", "PassO10.Perm.fg_bab"),
  ("O10O12Collapse", "PassO10.C8.Src.A.h", "PassO10.C8.Can.X.h"),
  ("O10O12Collapse", "PassO10.C8.Src.B.h", "PassO10.C8.Can.X.h"),
  ("O10O12Collapse", "PassO10.C8.Src.C.h", "PassO10.C8.Can.C.h"),
  ("O10O12Collapse", "PassO10.C8.Src.h_ex", "PassO10.C8.Can.h_ex")]

/-- Pass firing, read off the switch-on output (as `passRefs`). Decision 5
(D1): the `_ix` form carries the pass's output, the Lean name keeps the
baseline (the packed image: `PProd` for a collapsed block, Lean's handler
for a split one). -/
def pjPassRefs : List (String × String × String × Bool) := [
  -- O7: the Ix recursor, single motives (no packing); declines on distinct minors
  ("O7Collapse", "PassO7.Src.A.viaRec._ix", "PProd", false),
  ("O7Collapse", "PassO7.Src.B.viaRecOn._ix", "PProd", false),
  ("O7Collapse", "PassO7.Src.Z.viaRec._ix", "PProd", false),
  ("O7Collapse", "PassO7.Src.A.viaRec", "PProd", true),
  ("O7Collapse", "PassO7.Src.A.distinct", "PProd", true),
  -- O8: the Ix `casesOn` of the class, in matchers too; the Lean names keep their images
  ("O8Cases", "PassO8.Src.A.isNil._ix", "PProd", false),
  ("O8Cases", "PassO8.Src.B.isNil.match_1._ix", "PProd", false),
  ("O8Cases", "PassO8.Src.Z.isE.match_1._ix", "PProd", false),
  ("O8Cases", "PassO8.Src.A.isNil'._ix", "PProd", false),
  ("O8Cases", "PassO8.Src.A.isNil", "PProd", true),
  ("O8Cases", "PassO8.Src.B.isNil.match_1", "PProd", true),
  ("O8Cases", "PassO8.Src.A.isNil'", "PProd", true),
  -- O11b: the enumeration form (no `casesOn`) in the `_ix` forms, whose `noConfusion`
  -- is typed over the canonical `noConfusionType`; declines on two constructors (O3 still fires)
  ("O11bNoConfusion", "PassO11b.Src.B.noConfusionType._ix", "PassO11b.Src.B._ix.casesOn", false),
  ("O11bNoConfusion", "PassO11b.Src.B.noConfusion._ix", "PassO11b.Src.B._ix.casesOn", false),
  ("O11bNoConfusion", "PassO11b.Src.B.noConfusion._ix", "PassO11b.Src.B.noConfusionType._ix", true),
  ("O11bNoConfusion", "PassO11b.Src.B.noConfusionType", "PassO11b.Src.B._ix.casesOn", true),
  ("O11bNoConfusion", "PassO11b.Src.E.noConfusionType", "PassO11b.Src.E._ix.casesOn", true),
  -- O9: the Ix `brecOn` with the canonical handler (also for `A.cnt`: Lean compiles `B.cnt b` as a
  -- call, `B.cnt` not being recursive through `A`, so the handler reads no cross field)
  ("O9Split", "PassO9.Src.A.len._ix", "PassO9.Src.A._ix.brecOn", true),
  ("O9Split", "PassO9.Src.A.len._ix", "PassO9.Src.A.len._ix_retyped._f", true),
  ("O9Split", "PassO9.Src.A.sum._ix", "PassO9.Src.A._ix.brecOn", true),
  ("O9Split", "PassO9.Src.A.cnt._ix", "PassO9.Src.A._ix.brecOn", true),
  ("O9Split", "PassO9.Src.A.len", "PassO9.Src.A.len._ix_retyped._f", false),
  ("O9Split", "PassO9.Src.A.len", "PassO9.Src.A.len._f", true),
  -- O10/O12 do not fire on the transported cliques: no image of the paired recursor is
  -- rewritten for them, and O12's helper is not emitted
  ("O10O12Collapse", "PassO10.Src.A.h", "PProd", true),
  ("O10O12Collapse", "PassO10.C8.Src.A.f", "PProd", true),
  ("O10O12Collapse", "PassO10.Src.A.f", "PassO10.Src.A.f._ix.fg", false)]

/-- The proof-justified passes' non-canonical set, exact in both directions
for the unit (`passTwinsNC` against `nonCanonicalPasses`). -/
def passNonCanonicalChecks (u : CUnit) (on : Ix.CompileM.LeanPipelineOut) : Array String × Nat := Id.run do
  let fixture := Name.mkStr `Tests.Ix.Compile.Pass u.name
  let entries := Tests.Ix.Compile.NonCanonical.nonCanonicalPasses.filter (·.fixture == fixture)
  let addr := fun (s : String) => on.env.getAddr? (ixN (parseName s))
  let mut problems : Array String := #[]
  let mut n := 0
  for (unit, a, b) in passTwinsNC do
    if unit != u.name then continue
    n := n + 1
    match addr a, addr b with
    | some x, some y =>
      match entries.find? (·.constant == parseName a) with
      | none => problems := problems.push s!"{u.name}: {a} / {b} differ ({x} / {y}) with no entry in nonCanonicalPasses"
      | some en =>
        if x == y then
          problems := problems.push s!"{u.name}: stale non-canonical entry {a} ({en.cause.tag}): the pair is byte-equal"
        else if en.evidence.addrA != toString x || en.evidence.addrB != toString y then
          problems := problems.push s!"{u.name}: evidence moved for {a} ({en.cause.tag}): \"{x}\" \"{y}\""
    | _, _ => problems := problems.push s!"{u.name}: non-canonical pair missing: {a} / {b}"
  for en in entries do
    if !(passTwinsNC.any fun (unit, a, _) => unit == u.name && parseName a == en.constant) then
      problems := problems.push s!"{u.name}: non-canonical entry {en.constant} names no listed pair"
  return (problems, n)

/-- The per-pass checks of one fixture unit. -/
def passChecks (u : CUnit) (on : Ix.CompileM.LeanPipelineOut) : Array String × Array String := Id.run do
  let mut problems : Array String := #[]
  let mut lines : Array String := #[]
  let addr := fun (o : Ix.CompileM.LeanPipelineOut) (s : String) => o.env.getAddr? (ixN (parseName s))
  let mut nt := 0
  for (unit, a, b) in passTwins ++ pjPassTwins do
    -- the debugging unit `names` (`PASS3_NAMES`) takes the twins unit's pairs it contains
    if unit != u.name && !(unit == "twins" && u.name == "names" && (addr on a).isSome) then continue
    nt := nt + 1
    match addr on a, addr on b with
    | some x, some y =>
      if x != y then
        problems := problems.push s!"{u.name}: twins differ with the switch on: {a} / {b}: {describeDeep on.env (addrNames on.env) x y 3}"
    | _, _ => problems := problems.push s!"{u.name}: twin missing: {a} / {b}"
  -- every name of an address
  let names : Std.HashMap Address (Array String) := on.env.named.fold (init := {}) fun m n nd =>
    m.insert nd.addr ((m.getD nd.addr #[]).push n.pretty)
  let mut nr := 0
  for (unit, c, r, want) in passRefs ++ pjPassRefs do
    if unit != u.name then continue
    nr := nr + 1
    let some ad := addr on c | problems := problems.push s!"{u.name}: {c} missing"; continue
    let some (k, _) := ixonBody on.env ad | problems := problems.push s!"{u.name}: {c} has no body"; continue
    let has := k.refs.any fun x => (names.getD x #[]).contains r
    if has != want then
      problems := problems.push s!"{u.name}: {c} {if want then "does not reference" else "references"} {r}"
  let mut ns := 0
  for (unit, c, _, pin) in passSameAsSurgery do
    if unit != u.name then continue
    ns := ns + 1
    let some b := addr on c | problems := problems.push s!"{u.name}: {c} missing"; continue
    if pin.isEmpty then
      problems := problems.push s!"{u.name}: {c}: no pinned address (measured \"{b}\")"
    else if toString b != pin then
      problems := problems.push s!"{u.name}: {c}: address {b}, pinned {pin} (the surgery's term)"
  let (ncp, nnc) := passNonCanonicalChecks u on
  problems := problems ++ ncp
  lines := lines.push s!"  passes: {nt} twin pairs equal with the switch on, {nr} firing checks, {ns} constants with the surgery's term (pinned), {nnc} recorded non-canonical pairs ({problems.size} problem(s))"
  return (problems, lines)

/-- `PASS3_FAILURES=<file>`: append every kernel failure of a unit, one
tab-separated row `unit switch leg name message` (the message whole, its
newlines and tabs replaced by spaces), and one row `#checked unit switch leg
count` per leg. -/
def dumpRuns (unit : String) (runs : List (String × KernelRun)) : IO Unit := do
  let some f := ← IO.getEnv "PASS3_FAILURES" | return
  let h ← IO.FS.Handle.mk f .append
  let clean := fun (s : String) => (s.replace "\n" " | ").replace "\t" " "
  for (sw, r) in runs do
    for (leg, n) in r.checked do h.putStrLn s!"#checked\t{unit}\t{sw}\t{leg}\t{n}"
    for (leg, n, m) in r.failed do h.putStrLn s!"{unit}\t{sw}\t{leg}\t{n}\t{clean m}"
  h.flush

def dumpFailures (unit : String) (onRun : KernelRun) : IO Unit :=
  dumpRuns unit [("on", onRun)]

/-- `PASS3_RECHECK=<dir>` (a `PASS3_KEEP` directory, possibly written by an
older revision): rerun this revision's kernels on every unit's kept `on.ixe`
and `off.ixe` with the kept name lists, in meta mode and, with
`PASS3_RECHECK_ANON`, in anonymous mode (check-rs subject-only), dumping
the rows (`PASS3_FAILURES`) with switch `on-meta`, `off-meta`, `on-anon`,
`off-anon`. -/
def runRecheck (d : System.FilePath) : IO UInt32 := do
  let anonToo := (← IO.getEnv "PASS3_RECHECK_ANON").isSome
  -- `PASS3_RECHECK_TAG` keeps the working directories of concurrent rechecks apart
  let tag := (← IO.getEnv "PASS3_RECHECK_TAG").getD ""
  let mut n := 0
  for e in ← d.readDir do
    let p := e.path
    unless ← p.isDir do continue
    for (sw, ixe, nf) in [("on", p / "on.ixe", p / "names.txt"),
        ("off", p / "off.ixe", p / "off" / "names.txt")] do
      unless (← ixe.pathExists) && (← nf.pathExists) do continue
      let names := ((← IO.FS.readFile nf).splitOn "\n").toArray.filter (!·.isEmpty)
      if names.isEmpty then continue
      for anon in (if anonToo then [false, true] else [false]) do
        let mode := if anon then "anon" else "meta"
        let rdir := p / s!"recheck{tag}-{sw}-{mode}"
        IO.FS.createDirAll rdir
        let r ← kernelRun rdir ixe names (anon := anon) (skipDeps := true)
        dumpRuns e.fileName [(s!"{sw}-{mode}", r)]
        IO.println s!"[pass3-recheck] {e.fileName} {sw}-{mode}: {r.failed.size} failure(s), checked {r.checked}"
        n := n + 1
  IO.println s!"[pass3-recheck] {n} run(s)"
  return 0

def runUnit (u : CUnit) (keep? : Option System.FilePath) : IO (Array String × Array String) := do
  let mut problems : Array String := #[]
  let mut lines : Array String := #[]
  let t0 ← IO.monoMsNow
  let on ← compileUnit u
  lines := lines.push s!"{u.name}: {u.seeds.size} fixture constants, {u.closure.length} in the \
    closure; block failures {on.cenv.ungrounded.size} ({(← IO.monoMsNow) - t0} ms)"
  for (n, e) in on.cenv.ungrounded.toList.take 6 do
    lines := lines.push s!"  failed: {n.pretty}: {e.take 240}"
  -- 1. changed blocks and names
  let idr := namesCheck u on
  lines := lines.push s!"  changed blocks: {idr.changedBlocks.map (·.map (·.pretty))}; \
    named entries: {idr.inputNames} input constants, {idr.reserved} reserved"
  problems := problems ++ idr.problems.map (s!"{u.name}: " ++ ·)
  if u.name == "twins" || u.name == "names" || (passFiles ++ pjPassFiles).any (fun p => (System.FilePath.mk p).fileStem == some u.name) then
    let (pp, pl) := passChecks u on
    problems := problems ++ pp
    lines := lines ++ pl
  -- 5. display names of the changed blocks' auxiliaries
  for all in idr.changedBlocks do
    let some x := all[0]? | continue
    let ixRec := _root_.Ix.Name.mkStr (_root_.Ix.Name.mkStr x "_ix") "rec"
    let hasIx := on.env.named.toList.any fun (n, _) =>
      Ix.Compile.Pass.hasReserved n && all.any fun m => (toLeanName m).isPrefixOf (toLeanName n)
    if !hasIx then problems := problems.push s!"{u.name}: no `_ix` name for the block of {x.pretty} ({ixRec.pretty})"
  -- every block failure is recorded (`Pass3Kernels.compileFailures`: the
  -- refusals of Pass 2 and the compile totality defects, by name), a
  -- consequence of one (a failure whose message names a recorded root or an
  -- earlier consequence: under Pass 3 a Lean auxiliary of a changed block is
  -- its image, whose type mentions every member of the Lean block, the
  -- refused component included, REFUSED-SIBLING), or a recorded refusal of
  -- Pass 3's images (`Pass3Kernels.switchOnRefusals`); checked both ways
  -- (`PASS3_EMIT_FAILURES=1` prints the unrecorded roots as rows)
  let recorded := Pass3Kernels.compileFailures.filter (·.unit == u.name)
  let roots : Std.HashSet _root_.Ix.Name := on.cenv.ungrounded.fold (init := {}) fun s n e =>
    if recorded.any (fun r => r.names.contains n.pretty && (e.splitOn r.msg).length > 1) then s.insert n else s
  let consequence := refusalClosure roots on
  let recordedOn := Pass3Kernels.switchOnRefusals.filter (·.unit == u.name)
  let recordedOnly (n : _root_.Ix.Name) (e : String) : Bool :=
    recordedOn.any fun r => r.names.contains n.pretty && (e.splitOn r.msg).length > 1
  let emit := (← IO.getEnv "PASS3_EMIT_FAILURES").isSome
  let mut nRefused := 0
  let mut nRecordedOn := 0
  for (n, e) in on.cenv.ungrounded do
    if roots.contains n then continue
    if consequence.contains n then nRefused := nRefused + 1
    else if recordedOnly n e then nRecordedOn := nRecordedOn + 1
    else
      problems := problems.push s!"{u.name}: {n.pretty} fails, not recorded: {e.take 240}"
      if emit then
        lines := lines.push s!"  emit: \{ unit := {u.name.quote}, cause := \"?\", msg := {((e.take 60).toString).quote}, names := [{n.pretty.quote}] },"
  lines := lines.push s!"  block failures: {roots.size} recorded root(s) \
    [{", ".intercalate (recorded.map (·.cause))}], {nRefused} consequence(s) (REFUSED-SIBLING), \
    {nRecordedOn} recorded image refusal(s)"
  for r in recorded do
    for nm in r.names do
      let ok := on.cenv.ungrounded.toList.any fun (n, e) => n.pretty == nm && (e.splitOn r.msg).length > 1
      if !ok then
        problems := problems.push s!"{u.name}: {nm} is recorded as failing ({r.cause}: {r.msg}) but does not (stale)"
  for r in recordedOn do
    for nm in r.names do
      let ok := on.cenv.ungrounded.toList.any fun (n, e) => n.pretty == nm && (e.splitOn r.msg).length > 1
      if !ok then
        problems := problems.push s!"{u.name}: {nm} is recorded as failing ({r.msg}) but does not (stale)"
  -- 2. decompile (of a complete output: a partial one, where Pass 2 refused a
  -- block, is not decompilable as a whole)
  if on.cenv.ungrounded.isEmpty then
    let (dprob, dsum) ← decompileCheck u on
    -- the documented roundtrip defects (`Pass3Kernels.decompileKnown`), by the
    -- constant each problem names; checked both ways
    let known : Std.HashSet String := (Pass3Kernels.decompileKnown.filter (·.unit == u.name)).foldl
      (fun s k => k.names.foldl (·.insert ·) s) {}
    let subjectOf (p : String) : String :=
      if p.startsWith "decompile mismatch: " then (p.drop 20).toString
      else if p.startsWith "not decompiled: " then (p.drop 16).toString
      else if p.startsWith "decompile error " then (((p.drop 16).toString.splitOn ": ").headD "")
      else p
    let recorded := dprob.filter (fun p => known.contains (subjectOf p))
    lines := lines.push s!"  decompile: {dsum}, {dprob.size} problem(s) ({recorded.size} recorded \
      as documented roundtrip defects)"
    for p in dprob.toList.take 8 do lines := lines.push s!"    {p}"
    problems := problems ++ (dprob.filter (fun p => !known.contains (subjectOf p))).map (s!"{u.name}: " ++ ·)
    for k in known do
      unless dprob.any (subjectOf · == k) do
        problems := problems.push s!"{u.name}: {k} is recorded as a decompile problem but has none (stale)"
  else
    lines := lines.push s!"  decompile: skipped, {on.cenv.ungrounded.size} block failure(s)"
  -- 3. kernels on the output; 4. rules in a test-only copy
  let dir ← match keep? with
    | some d => do
      let d := d / u.name
      IO.FS.createDirAll d
      pure d
    | none => IO.FS.createTempDir
  try
    let path := dir / "on.ixe"
    IO.FS.writeBinFile path on.bytes
    let seedSet : Std.HashSet String := u.seeds.foldl (fun s n => s.insert (ixN n).pretty) {}
    let names := on.env.named.toArray.filterMap fun (n, _) =>
      let s := n.pretty
      if seedSet.contains s || Ix.Compile.Pass.hasReserved n then some s else none
    let onRun ← kernelRun dir path names
    dumpFailures u.name onRun
    -- Every failure against the record (`Tests.Ix.Compile.Pass3Kernels.table`),
    -- both ways, and each leg's checked count against the names requested.
    -- where the meta verdicts vary between runs, the anonymous kernels on
    -- the same output decide which failures are meta-only
    let anon? : Option (Std.HashSet (String × String)) ←
      if Pass3Kernels.table.any (fun e => e.unit == u.name && e.switch == "on" && e.varies)
      then do
        let adir := dir / "anon-on"
        IO.FS.createDirAll adir
        let a ← kernelRun adir path names (anon := true) (skipDeps := true)
        pure (some (a.failed.foldl (fun s (l, n, _) => s.insert (l, n)) {}))
      else pure none
    let (ps, summary) :=
      Pass3Kernels.check Pass3Kernels.table u.name "on" onRun.failed onRun.checked names.size anon?
    problems := problems ++ ps
    lines := lines.push s!"  kernels: {summary}"
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
    -- O11a (A4): one `rfl` per Linear member, under the three kernels (a verdict, not a gate)
    if u.name == "twins" then
      match o11aEnv on with
      | .error e => lines := lines.push s!"  o11a: {e}"
      | .ok (oenv, onames) =>
        match Ixon.serEnv oenv with
        | .error e => lines := lines.push s!"  o11a: {e}"
        | .ok bytes =>
          let opath := dir / "o11a.ixe"
          IO.FS.writeBinFile opath bytes
          let odir := dir / "o11a"
          IO.FS.createDirAll odir
          let ofailed ← kernelFailures odir opath onames (anon := true)
          lines := lines.push s!"  o11a: {onames.size} rfl statements (Orig `_sizeOf` = Twin instance form), {ofailed.size} kernel failure(s)"
          for (leg, n, m) in ofailed do
            lines := lines.push s!"    o11a {leg}: {n}: {m.take 300}"
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
  let mut siblings := 0
  let mut images := 0
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
      -- a member of a mutual block whose sibling was rewritten: only the
      -- block (and its index in it) moved
      else if d.fields.all (fun f => f == "idx" || f.startsWith "block") then
        siblings := siblings + 1
      -- A3 decision 3: the Lean name of a changed block's image-kind auxiliary
      -- denotes its image, a definition with Lean's type, so it moves (no record)
      else if (n.bind fun x => (Ix.Compile.Pass.Opt.classify x).map (·.1)).isSome then
        images := images + 1
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
  IO.println s!"[pass3-lib] moved: {roots} roots ({rewritten} rewritten call-site constants, {siblings} block siblings of one, {images} Lean auxiliaries of changed blocks now denoting their images), \
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
  -- A4: classify each difference: the same expressions (the tables differ: the
  -- surgery's leftover entries of dropped arguments or their order) or not
  let rowsNames := fun (p : Ixon.LazyEnvParts) => p.namedRows.foldl (init := ({} : Std.HashMap Address String))
    fun m r => if m.contains r.addr && (r.name.pretty.splitOn "._ix").length > 1 then m else m.insert r.addr r.name.pretty
  let offNm := rowsNames offParts
  let onNm := rowsNames onParts
  let addrOf := fun (p : Ixon.LazyEnvParts) (s : String) =>
    (byPretty.get? s).bind fun n => (p.rowIdx.get? n).map fun i => p.namedRows[i]!.addr
  let mut tablesOnly := 0
  for n in (differ.qsort (· < ·)).toList do
    let detail := match addrOf offParts n, addrOf onParts n with
      | some a, some b => describeDiff offParts.env onParts.env offNm onNm a b
      | _, _ => "missing"
    if detail.startsWith "same expressions" then tablesOnly := tablesOnly + 1
    IO.println s!"[pass3-lib]   differs: {n}: {detail.take 1500}"
  IO.println s!"[pass3-lib] of the {differ.size} that differ: {tablesOnly} have the switch-off expressions (tables only), {differ.size - tablesOnly} differ in an expression"
  let shown := if (← IO.getEnv "PASS3_LIB_ALL").isSome then problems.size else 50
  for p in problems.toList.take shown do IO.println s!"[pass3-lib] FAIL {p}"
  IO.println s!"[pass3-lib] {problems.size} problem(s) ({(← IO.monoMsNow) - t0} ms)"
  return if problems.isEmpty then 0 else 1

/-- `PASS3_SURGERED=<file.ixe>`: the constants of a switch-off output that
carry altering call-site metadata (the surgery's rewritten constants), one
per line. -/
def runSurgered (path : String) : IO UInt32 := do
  let parts ← IO.ofExcept (Ixon.deEnvVerifiedLazy (← IO.FS.readBinFile path))
  let mut n := 0
  for row in parts.namedRows do
    if isSyntheticMuts row.name then continue
    if let .ok nd := row.materialize parts.backing parts.nameRev then
      if Ix.Tc.metaHasAlteringSurgery nd.constMeta then
        n := n + 1
        IO.println s!"[pass3-surgered] {row.name.pretty}"
  IO.println s!"[pass3-surgered] {n} constant(s)"
  return 0

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
Pass 3 and prints, per changed block, Pass 1's classes, the compiler's
classes, the view's canonical recursor types and the images. -/
def runView (path : String) : IO UInt32 := do
  let u ← unitOfFile path
  let on ← compileUnit u
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
closure of one constant of the file's environment, timing it. -/
def runClosure (path : String) (c : String) : IO UInt32 := do
  let env ← getFileEnv path
  let n := c.toName
  let closure := closureOf env [n]
  IO.println s!"[pass3-closure] {c}: {closure.length} constants"
  let u : CUnit := { name := c, env, seeds := #[n], closure }
  let t0 ← IO.monoMsNow
  let o ← compileUnit u
  IO.println s!"[pass3-closure] {o.bytes.size} bytes, {o.cenv.ungrounded.size} failures, {(← IO.monoMsNow) - t0} ms"
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
  if let some p := ← IO.getEnv "PASS3_SURGERED" then return ← runSurgered p
  if let some d := ← IO.getEnv "PASS3_RECHECK" then return ← runRecheck d
  if let some spec := ← IO.getEnv "PASS3_EXPECT_EMIT" then
    match spec.splitOn "," with
    | rows :: recheck :: more => return ← Pass3Kernels.emit rows recheck more
    | _ =>
      IO.println "[pass3] PASS3_EXPECT_EMIT=<rows.tsv>,<recheck.tsv>[,<meta recheck.tsv>…]"
      return 2
  if let some spec := ← IO.getEnv "PASS3_LIB" then
    match spec.splitOn "," with
    | [a, b] => return ← runLib a b
    | _ => IO.println "[pass3-lib] PASS3_LIB=<switch-off.ixe>,<switch-on.ixe>"; return 2
  let only := ((← IO.getEnv "PASS3_ONLY").map (·.splitOn ",")).getD []
  let keep? := (← IO.getEnv "PASS3_KEEP").map System.FilePath.mk
  let want := fun (s : String) => only.isEmpty || only.contains s
  let mut units : Array (String × IO CUnit) := #[]
  for p in auxCertFiles ++ protoFiles ++ passFiles ++ pjPassFiles do
    let stem := (System.FilePath.mk p).fileStem.getD p
    if want stem then units := units.push (stem, unitOfFile p)
  if want "twins" then
    units := units.push ("twins", do
      let (seeds, _) := Tests.Ix.Compile.Twins.familyClosure env
        Tests.Ix.Compile.Twins.allFamilies
      pure { name := "twins", env, seeds, closure := closureOf env seeds.toList })
  -- a unit of named constants of the test environment (Lean core included)
  if let some ns := ← IO.getEnv "PASS3_NAMES" then
    let seeds := (ns.splitOn ",").toArray.filterMap fun s =>
      let n := parseName s.trimAscii.toString
      if env.contains n then some n else none
    units := units.push ("names", pure { name := "names", env, seeds, closure := closureOf env seeds.toList })
  if want "corpus" then
    units := units.push ("corpus", do
      let closure := closureOf env ((validateAuxClosure env).map (·.1))
      pure { name := "corpus", env, seeds := (closure.map (·.1)).toArray, closure })
  let mut problems : Array String := #[]
  -- the record's `mayBeEmpty` rows (`Pass3Kernels.mayBeEmptyControl`)
  let (mbe, mbeLine) := Pass3Kernels.mayBeEmptyControl
  IO.println s!"[pass3] {mbeLine}"
  for p in mbe do IO.println s!"[pass3] FAIL {p}"
  problems := problems ++ mbe
  -- negative control: an input name with the reserved component `_ix`
  if want "ReservedIx" then
    let u ← unitOfFile "Tests/Ix/Compile/AuxCert/ReservedIx.lean"
    let msg ← try (do discard <| compileUnit u; pure "compiled") catch e => pure (toString e)
    let rejected : Bool := decide ((msg.splitOn "reserved component").length > 1)
    IO.println s!"[pass3] ReservedIx: rejected {rejected}: {msg.take 200}"
    if !rejected then problems := problems.push "ReservedIx: the reserved `_ix` name is not handled"
    -- with several reserved names, both compilers name the least by pretty
    -- form (design document §11.6 item 3)
    let least := "input name 'ReservedIx.A._ix.g'"
    let rustMsg ← try (do
        let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv u.env u.closure).mapError toString)
        let constants ← IO.ofExcept input.prepare
        let dir ← IO.FS.createTempDir
        try
          discard <| Ix.CompileM.rsCompileEnvBytesFFI constants (dir / "rust.ixe").toString true
          pure "compiled"
        finally IO.FS.removeDirAll dir) catch e => pure (toString e)
    let leanNames : Bool := decide ((msg.splitOn least).length > 1)
    let rustNames : Bool := decide ((rustMsg.splitOn least).length > 1)
    IO.println s!"[pass3] ReservedIx: Lean names the least reserved name {leanNames}, Rust {rustNames}: {rustMsg.take 200}"
    if !leanNames || !rustNames then
      problems := problems.push "ReservedIx: the two compilers do not name the least reserved name"
  -- Units load one after the other (each elaborates its file in this process),
  -- and each loaded unit's checks start at once in a task of their own, at most
  -- `PASS3_JOBS` (default 8) at a time: the units are independent (own closure,
  -- own temporary directory, own kernel subprocesses). Every unit's lines are
  -- printed, and its problems collected, in unit order.
  let jobs := max 1 (((← IO.getEnv "PASS3_JOBS").bind String.toNat?).getD 8)
  -- per unit: the lines of a load failure, or the task of its checks
  let mut slots : Array (Option (Array String × Array String ⊕ Task (Except IO.Error (Array String × Array String)))) :=
    Array.replicate units.size none
  let mut live : Array (Task (Except IO.Error (Array String × Array String))) := #[]
  -- the longest units start first (their order in the log is unchanged)
  let heavy := ["twins", "corpus", "MdataSpine"]
  let order := (List.range units.size).filter (heavy.contains units[·]!.1) ++
    (List.range units.size).filter (!heavy.contains units[·]!.1)
  for i in order do
    let (stem, mk) := units[i]!
    let u? ← (some <$> mk).toBaseIO
    let u ← match u? with
      | .ok (some u) => pure u
      | .ok none => continue
      | .error e =>
        if leanRejects.contains stem then
          slots := slots.set! i (some <| .inl (#[s!"[pass3] {stem}: Lean itself rejects the file (aux-cert record)"], #[]))
        else
          slots := slots.set! i (some <| .inl (#[s!"[pass3] FAIL {stem}: {e}"], #[s!"{stem}: {e}"]))
        continue
    -- a free slot as soon as any unit finishes (not only the oldest: the
    -- long units start first)
    while live.size ≥ jobs do
      live ← live.filterM fun t => return !(← IO.hasFinished t)
      if live.size ≥ jobs then IO.sleep 50
    let t ← IO.asTask (prio := .dedicated) do
      try
        let (ps, lines) ← runUnit u keep?
        pure (lines.map (s!"[pass3] " ++ ·) ++ ps.map (s!"[pass3] FAIL " ++ ·), ps)
      catch e =>
        pure (#[s!"[pass3] FAIL {e}"], #[toString e])
    live := live.push t
    slots := slots.set! i (some (.inr t))
  for slot? in slots do
    let some slot := slot? | continue
    let (out, ps) ← match slot with
      | .inl r => pure r
      | .inr t => IO.ofExcept (← IO.wait t)
    for l in out do IO.println l
    problems := problems ++ ps
  IO.println s!"[pass3] {units.size} units, {problems.size} problem(s)"
  return if problems.isEmpty then 0 else 1

end Tests.Ix.Compile.Pass3
