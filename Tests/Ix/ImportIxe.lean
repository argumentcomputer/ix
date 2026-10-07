/-
  Materialization FFI + `import_ixe` tests (plan C6/C8).

  A self-contained fixture environment is built by direct kernel
  `addDecl` on an empty env (no Init, so the compiled `.ixe` is closed
  over exactly the fixture constants), exercising every ConstantInfo
  kind the materializer must construct — inductives (plain + mutual),
  constructors, kernel-generated recursors, definitions (all three
  reducibility hints, implicit/inst-implicit binders, letE, mdata with
  string/bool/nat/name payloads, `Expr.proj`), theorems, axioms with
  max/imax level polymorphism, and opaques.

  The original alpha-collapsed mutual pair is also checked with Pass 3's
  declared image-support closure replayed into the empty environment.
  The ordinary fixture's distinct pair is its support-free neighbour.

  Gates:
  - C6 parity: `rs_decompile_env_consts` output matches the original
    constants field-for-field (types, values, level params, hints,
    recursor rules — the round trip is exact on this fixture).
  - Root equality: recompiling every materialized original-source constant
    reproduces the original canonical root. The collapsed case has exactly
    42 source constants and two additional canonical recursors, A._ix.rec
    and B._ix.rec. All 42 source fields must match; all 44 names and the two
    extra recursor kinds are checked. Recompiling the full 44 is required
    to refuse with D14: reserved `_ix` names are never compiler input.
    The no-extra neighbour recompiles its complete materialized output.
  - Fresh kernel replay: `Ix.Replay.planDeclarations` consumes the complete
    materialized map and replays clean into an empty kernel env. Every
    source constant must be present and exact after replay; source recursors
    are regenerated with their inductives; replay does not independently
    kernel-check the two reserved recursor records. A certified artifact check
    covers those two names by owning record, with only the fixture's two
    non-standard axioms permitted to decline.
  - Closure scoping: `only [TIxImp.dbl]` returns the reference closure
    and nothing else.
  - C8: an in-process consumer file `import_ixe`s the artifact and
    defines a term over the materialized constants (interpreter +
    linked FFI, `supportInterpreter`).
-/
module

public import LSpec
public import Ix.ImportIxe
-- The C8 consumer subprocess `import`s Ix.IxEval; importing it here keeps
-- its olean in the test target's build closure (hermetic builds ship only
-- that closure — a local `lake build ix` leftover masked this once).
public import Ix.IxEval
public import Ix.Replay
public import Ix.CompileM
public import Ix.Commit
public import Ix.Meta
public import Ix.EnvScope
public import Tests.Ix.Compile.KernelReport

public section

open LSpec

namespace Tests.Ix.ImportIxe

/-! ### Fixture environment (kernel-level, Init-free) -/

private def nN : Lean.Name := `TIxImp.N
private def nZero : Lean.Name := `TIxImp.N.zero
private def nSucc : Lean.Name := `TIxImp.N.succ
private def nRec : Lean.Name := `TIxImp.N.rec

private def cN : Lean.Expr := .const nN []
private def eZero : Lean.Expr := .const nZero []
private def eSucc (e : Lean.Expr) : Lean.Expr := .app (.const nSucc []) e
private def type1 : Lean.Expr := .sort (.succ .zero)

private def arrow (a b : Lean.Expr) : Lean.Expr :=
  .forallE `a a b .default

/-- The fixture declarations, in dependency order. -/
private def fixtureDecls (collapsed : Bool := false) : List Lean.Declaration := [
  -- Plain inductive with a recursive constructor (recursor exercised).
  .inductDecl [] 0 [{
    name := nN
    type := type1
    ctors := [
      { name := nZero, type := cN },
      { name := nSucc, type := arrow cN cN } ] }] false,
  -- Prop inductive backing the theorem.
  .inductDecl [] 0 [{
    name := `TIxImp.T
    type := .sort .zero
    ctors := [{ name := `TIxImp.T.intro, type := .const `TIxImp.T [] }] }]
    false,
  -- Structure-shaped inductive for `Expr.proj`.
  .inductDecl [] 0 [{
    name := `TIxImp.P
    type := type1
    ctors := [{
      name := `TIxImp.P.mk
      type := arrow cN (arrow cN (.const `TIxImp.P [])) }] }] false,
  -- Mutual inductive pair (grouped inductDecl, mutual recursors). The minimal
  -- Init-free fixture has distinct members. The collapsed variant retains
  -- the original alpha-equivalent pair, with Pass 3's declared image support
  -- replayed into the otherwise empty environment before these declarations.
  .inductDecl [] 0 [
    { name := `TIxImp.A, type := type1
      ctors := [{ name := `TIxImp.A.mk
                  type := arrow (.const `TIxImp.B []) (.const `TIxImp.A []) }] },
    { name := `TIxImp.B, type := type1
      ctors := [{ name := `TIxImp.B.mk
                  type := arrow (.const `TIxImp.A [])
                    (if collapsed then .const `TIxImp.B []
                     else arrow cN (.const `TIxImp.B [])) }] }]
    false,
  -- Doubling via the recursor: const-with-levels, app spine, lambdas.
  .defnDecl {
    name := `TIxImp.dbl
    levelParams := []
    type := arrow cN cN
    value := .lam `n cN
      (Lean.mkApp4 (.const nRec [.succ .zero])
        (.lam `x cN cN .default)
        eZero
        (.lam `a cN (.lam `ih cN (eSucc (eSucc (.bvar 0))) .default) .default)
        (.bvar 0))
      .default
    hints := .regular 2
    safety := .safe
    all := [`TIxImp.dbl] },
  -- Structure projection.
  .defnDecl {
    name := `TIxImp.fst
    levelParams := []
    type := arrow (.const `TIxImp.P []) cN
    value := .lam `p (.const `TIxImp.P []) (.proj `TIxImp.P 0 (.bvar 0))
      .default
    hints := .abbrev
    safety := .safe
    all := [`TIxImp.fst] },
  -- letE with an ordinary dependent-irrelevant binding.
  .defnDecl {
    name := `TIxImp.letD
    levelParams := []
    type := arrow cN cN
    value := .lam `n cN
      (.letE `m cN (eSucc (.bvar 0)) (eSucc (.bvar 0)) false) .default
    hints := .regular 1
    safety := .safe
    all := [`TIxImp.letD] },
  -- mdata wrapping with all constructible payload kinds.
  .defnDecl {
    name := `TIxImp.mdt
    levelParams := []
    type := cN
    value := .mdata
      ((({} : Lean.KVMap).insert `s (.ofString "marker")
        |>.insert `b (.ofBool true)
        |>.insert `n (.ofNat 42)
        |>.insert `nm (.ofName `TIxImp.some.name))
      ) eZero
    hints := .opaque
    safety := .safe
    all := [`TIxImp.mdt] },
  -- Implicit and instance-implicit binders.
  .defnDecl {
    name := `TIxImp.bin
    levelParams := []
    type := .forallE `n cN
      (.forallE `i (.const `TIxImp.T []) cN .instImplicit) .implicit
    value := .lam `n cN
      (.lam `i (.const `TIxImp.T []) (.bvar 1) .instImplicit) .implicit
    hints := .regular 1
    safety := .safe
    all := [`TIxImp.bin] },
  -- Theorem over the Prop inductive.
  .thmDecl {
    name := `TIxImp.thm
    levelParams := []
    type := .const `TIxImp.T []
    value := .const `TIxImp.T.intro []
    all := [`TIxImp.thm] },
  -- Level-polymorphic axioms: max and imax spellings.
  .axiomDecl {
    name := `TIxImp.axm
    levelParams := [`u, `v]
    type := .sort (.max (.param `u) (.param `v))
    isUnsafe := false },
  .axiomDecl {
    name := `TIxImp.axi
    levelParams := [`u, `v]
    type := .sort (.imax (.param `u) (.param `v))
    isUnsafe := false },
  -- Opaque with a value.
  .opaqueDecl {
    name := `TIxImp.opq
    levelParams := []
    type := cN
    value := eZero
    isUnsafe := false
    all := [`TIxImp.opq] } ]

/-- Kernel-replay the fixture into an empty environment and return its
    constants. -/
private def buildFixtureConsts (collapsed : Bool := false) :
    IO (Array (Lean.Name × Lean.ConstantInfo)) := do
  let env ← Lean.mkEmptyEnvironment
  let mut kenv := env.toKernelEnv
  if collapsed then
    -- Use the compiler's own support declaration, then replay only its
    -- dependency closure. Importing Init wholesale would lose this fixture's
    -- empty-environment replay check.
    Lean.initSearchPath (← Lean.findSysroot)
    let supportEnv ← Lean.importModules #[{ module := `Init }] {}
    let rec toLean : Ix.Name → Lean.Name
      | .anonymous _ => .anonymous
      | .str p s _ => .str (toLean p) s
      | .num p i _ => .num (toLean p) i
    let support := Ix.EnvScope.collectDeps supportEnv
      (Ix.Compile.Image.imageSupport.toList.map toLean)
      (withRecursors := true) (withCompilerSupport := true)
    let supportMap := support.foldl (fun m (n, ci) => m.insert n ci)
      ({} : Lean.NameMap Lean.ConstantInfo)
    let supportPlan ← IO.ofExcept (Ix.Replay.planDeclarations supportMap supportMap.find?)
    for (key, decl) in supportPlan do
      match kenv.addDecl {} decl with
      | .ok kenv' => kenv := kenv'
      | .error e =>
        throw <| IO.userError
          s!"fixture support replay failed at {key}: {Ix.Replay.renderKernelException e}"
  for decl in fixtureDecls collapsed do
    match kenv.addDecl {} decl with
    | .ok kenv' => kenv := kenv'
    | .error _ =>
      throw <| IO.userError
        s!"fixture kernel replay failed at {decl.getNames}"
  return kenv.constants.fold (init := #[]) fun acc name info =>
    acc.push (name, info)

/-! ### Comparators -/

private def compareExpr (what : String) (a b : Lean.Expr) :
    Option String :=
  if a == b then none else some s!"{what} differs"

private def compareCI (name : Lean.Name) (a b : Lean.ConstantInfo) :
    Option String := Id.run do
  if a.levelParams != b.levelParams then
    return some s!"{name}: levelParams differ"
  if let some e := compareExpr s!"{name}: type" a.type b.type then
    return some e
  match a, b with
  | .axiomInfo x, .axiomInfo y =>
    if x.isUnsafe != y.isUnsafe then return some s!"{name}: isUnsafe"
  | .defnInfo x, .defnInfo y =>
    if let some e := compareExpr s!"{name}: value" x.value y.value then
      return some e
    if x.hints != y.hints then return some s!"{name}: hints differ"
    if x.safety != y.safety then return some s!"{name}: safety differs"
    if x.all != y.all then return some s!"{name}: all differs"
  | .thmInfo x, .thmInfo y =>
    if let some e := compareExpr s!"{name}: value" x.value y.value then
      return some e
    if x.all != y.all then return some s!"{name}: all differs"
  | .opaqueInfo x, .opaqueInfo y =>
    if let some e := compareExpr s!"{name}: value" x.value y.value then
      return some e
    if x.isUnsafe != y.isUnsafe then return some s!"{name}: isUnsafe"
  | .inductInfo x, .inductInfo y =>
    if x.numParams != y.numParams || x.numIndices != y.numIndices then
      return some s!"{name}: inductive arity differs"
    if x.all != y.all || x.ctors != y.ctors then
      return some s!"{name}: inductive family differs"
    if x.isRec != y.isRec || x.isReflexive != y.isReflexive
        || x.numNested != y.numNested then
      return some s!"{name}: inductive flags differ"
  | .ctorInfo x, .ctorInfo y =>
    if x.induct != y.induct || x.cidx != y.cidx
        || x.numParams != y.numParams || x.numFields != y.numFields then
      return some s!"{name}: constructor shape differs"
  | .recInfo x, .recInfo y =>
    if x.all != y.all || x.numParams != y.numParams
        || x.numIndices != y.numIndices || x.numMotives != y.numMotives
        || x.numMinors != y.numMinors || x.k != y.k then
      return some s!"{name}: recursor shape differs"
    if x.rules.length != y.rules.length then
      return some s!"{name}: rule count differs"
    for (rx, ry) in x.rules.zip y.rules do
      if rx.ctor != ry.ctor || rx.nfields != ry.nfields then
        return some s!"{name}: rule {rx.ctor} shape differs"
      if let some e :=
          compareExpr s!"{name}: rule {rx.ctor} rhs" rx.rhs ry.rhs then
        return some e
  | .quotInfo _, .quotInfo _ => pure ()
  | _, _ => return some s!"{name}: kind differs"
  return none

/-! ### The tests -/

/-- The replay planner regenerates source recursors; the certified artifact
    checker separately covers the two canonical recursor records. -/
private def checkCollapsedArtifact (path : String) (dir : System.FilePath)
    (extra : Array Lean.Name) : IO (Option String) := do
  let exe ← IO.FS.realPath ".lake/build/bin/kernel-check-ixe"
  let reportPath := dir / "certified.jsonl"
  let out ← IO.Process.output {
    cmd := exe.toString
    args := #[path, reportPath.toString, "--jobs", "8"]
    env := #[("LD_LIBRARY_PATH", none)] }
  let reportText ← IO.FS.readFile reportPath
  let evidence? := (← IO.getEnv "IMPORT_IXE_EVIDENCE").map System.FilePath.mk
  if let some evidence := evidence? then
    if ← evidence.pathExists then
      return some s!"refusing existing ImportIxe evidence directory {evidence}"
    IO.FS.createDirAll evidence
    IO.FS.writeBinFile (evidence / "collapsed.ixe") (← IO.FS.readBinFile path)
    IO.FS.writeFile (evidence / "certified.jsonl") reportText
    let version ← IO.Process.output { cmd := "lean", args := #["--version"] }
    IO.FS.writeFile (evidence / "certified.log")
      (version.stdout ++ s!"COMMAND {exe} {path} {reportPath} --jobs 8\n" ++
        out.stdout ++ out.stderr ++ s!"\nEXIT {out.exitCode}\n")
  let report ← match Tests.Ix.Compile.KernelReport.parse reportText out.exitCode with
    | .ok report => pure report
    | .error e => return some s!"certified artifact report: {e}; {out.stderr}"
  let compiled ← IO.ofExcept (Ixon.rsDeEnv (← IO.FS.readBinFile path))
  let owner (addr : Address) : Address :=
    match (compiled.consts.get? addr).bind (·.get?) with
    | some c => match c.info with
      | .dPrj p => p.block
      | .iPrj p => p.block
      | .rPrj p => p.block
      | .cPrj p => p.block
      | _ => addr
    | none => addr
  let expected := compiled.named.toArray.map fun (n, entry) =>
    (toString n, toString (owner entry.addr))
  if let some evidence := evidence? then
    IO.FS.writeFile (evidence / "covered-names.tsv")
      (String.intercalate "\n" (expected.toList.map fun (n, a) => s!"{n}\t{a}") ++ "\n")
  if let .error e := Tests.Ix.Compile.KernelReport.checkCoverage report expected then
    return some s!"certified artifact coverage: {e}"
  for n in extra do
    let some named := compiled.named.get? (Ix.Name.fromLeanName n)
      | return some s!"artifact lacks canonical recursor {n}"
    let address := toString (owner named.addr)
    let some verdict := report.get? address
      | return some s!"certified checker omitted canonical recursor {n}@{address}"
    unless verdict.outcome == "accept" do
      return some s!"certified canonical recursor {n}: {verdict.outcome}: {verdict.reason}"
    IO.println s!"[import-ixe] certified canonical recursor {n}@{address}: accept"
  let axiomNames := #["TIxImp.axm", "TIxImp.axi"]
  let mut declined : Array String := #[]
  for (address, verdict) in report do
    if verdict.outcome == "accept" then continue
    let names := (expected.filter (·.2 == address)).map (·.1)
    unless verdict.outcome == "decline" &&
        verdict.reason.startsWith "non-standard axiom (" &&
        !names.isEmpty && names.all axiomNames.contains do
      return some s!"unexpected certified outcome {address} {names}: {verdict.outcome}: {verdict.reason}"
    declined := declined ++ names
  unless declined.size == 2 && axiomNames.all declined.contains do
    return some s!"certified fixture axiom declines: {declined}, expected {axiomNames}"
  IO.println s!"[import-ixe] certified artifact: {expected.size} names covered; \
{report.size} records; exactly two non-standard fixture axioms declined; canonical recursors accepted"
  return none

private def roundtripTest (collapsed : Bool := false) : IO (Bool × Nat × Nat × Option String) := do
  let dir ← IO.FS.createTempDir
  let path := (dir / "fixture.ixe").toString
  try
    let original ← buildFixtureConsts collapsed
    let status ← Ix.CompileM.rsCompileEnvBytesFFI original.toList path false
    if status.ungrounded.size > 0 then
      return (false, 0, 0,
        some s!"fixture compile ungrounded: {status.ungrounded}")
    if collapsed then
      unless original.size == 42 do
        return (false, 0, 0, some s!"collapsed source fixture has {original.size} constants, expected 42")
      let compiled ← IO.ofExcept (Ixon.rsDeEnv (← IO.FS.readBinFile path))
      let address (n : Lean.Name) :=
        (compiled.named.get? (Ix.Name.fromLeanName n)).map (·.addr)
      unless (address `TIxImp.A).isSome && address `TIxImp.A == address `TIxImp.B do
        return (false, 0, 0, some "alpha-equivalent mutual members did not collapse")
    -- C6 parity: materialize everything and compare per constant.
    let materialized ← Ix.ImportIxe.materializeIxe path
    -- A changed block also exports its canonical recursors under reserved
    -- names. Require this fixture's exact pair, while retaining every source
    -- constant, source-root equality and full-materialized replay below.
    let expectedExtra : Array Lean.Name := if collapsed then
      #[`TIxImp.A._ix.rec, `TIxImp.B._ix.rec] else #[]
    let extra := materialized.filter fun (n, _) => !original.any (·.1 == n)
    let missing := original.filter fun (n, _) => !materialized.any (·.1 == n)
    if materialized.size != original.size + expectedExtra.size || !missing.isEmpty ||
        (extra.map (·.1)).qsort (·.cmp · == .lt) != expectedExtra then
      return (false, 0, 0, some s!"materialized names: original \
{original.size}, materialized {materialized.size}; extra {extra.map (·.1)}, missing {missing.map (·.1)}")
    let mut origMap : Lean.NameMap Lean.ConstantInfo := {}
    for (n, ci) in original do
      origMap := origMap.insert n ci
    let mut matMap : Lean.NameMap Lean.ConstantInfo := {}
    for (n, ci) in materialized do
      match origMap.find? n with
      | some oci =>
        if let some e := compareCI n oci ci then
          return (false, 0, 0, some e)
      | none =>
        unless expectedExtra.contains n do
          return (false, 0, 0, some s!"unexpected constant {n}")
        unless (match ci with | .recInfo _ => true | _ => false) do
          return (false, 0, 0, some s!"introduced constant {n} is not a recursor")
      matMap := matMap.insert n ci
    -- D14 is part of the source contract: full materialized output that
    -- includes reserved compiler names must refuse as fresh compiler input.
    if collapsed then
      let allPath := dir / "all-materialized.ixe"
      match ← (Ix.CompileM.rsCompileEnvBytesFFI materialized.toList
          allPath.toString false).toBaseIO with
      | .ok _ => return (false, 0, 0, some "full materialized output unexpectedly passed D14")
      | .error e =>
        if (e.toString.splitOn "contains the reserved component `_ix` (D14:").length ≤ 1 then
          return (false, 0, 0, some s!"full materialized output refused for the wrong reason: {e}")
      if ← allPath.pathExists then
        return (false, 0, 0, some "D14 refusal wrote an output")
    -- Recompile exactly the original-source names, all checked field-for-field
    -- above. The no-extra neighbour takes every materialized constant here.
    let sourceMaterialized := materialized.filter fun (n, _) => origMap.contains n
    unless sourceMaterialized.size == original.size do
      return (false, 0, 0, some "source projection lost a materialized constant")
    let path2 := (dir / "rebuilt.ixe").toString
    let status2 ← Ix.CompileM.rsCompileEnvBytesFFI sourceMaterialized.toList
      path2 false
    if status2.root != status.root then
      return (false, 0, 0, some s!"root drift: {status.root.take 12}… → \
{status2.root.take 12}…")
    -- Fresh kernel replay via the shared planner (import_ixe core).
    let matMapFrozen := matMap
    let plan ← match Ix.Replay.planDeclarations matMap
        matMapFrozen.find? with
      | .ok plan => pure plan
      | .error e => return (false, 0, 0, some s!"planDeclarations: {e}")
    let emptyEnv ← Lean.mkEmptyEnvironment
    let mut kenv := emptyEnv.toKernelEnv
    for (key, decl) in plan do
      match kenv.addDecl {} decl with
      | .ok kenv' => kenv := kenv'
      | .error _ =>
        return (false, 0, 0, some s!"fresh kernel replay rejected {key}")
    for (n, expected) in original do
      let some actual := kenv.constants.find? n
        | return (false, 0, 0, some s!"fresh replay lost source constant {n}")
      if let some e := compareCI n expected actual then
        return (false, 0, 0, some s!"fresh replay: {e}")
    if collapsed then
      if let some e ← checkCollapsedArtifact path dir expectedExtra then
        return (false, 0, 0, some e)
    return (true, original.size, 0, none)
  finally
    IO.FS.removeDirAll dir

private def closureTest : IO (Bool × Nat × Nat × Option String) := do
  let dir ← IO.FS.createTempDir
  let path := (dir / "fixture.ixe").toString
  try
    let original ← buildFixtureConsts
    let _ ← Ix.CompileM.rsCompileEnvBytesFFI original.toList path false
    let subset ← Ix.ImportIxe.materializeIxe path #[`TIxImp.dbl]
    let names : Std.HashSet Lean.Name :=
      subset.foldl (fun s (n, _) => s.insert n) {}
    let checks : List (String × Bool) := [
      ("dbl present", names.contains `TIxImp.dbl),
      ("N pulled in", names.contains nN),
      ("N.succ pulled in", names.contains nSucc),
      ("N.rec pulled in", names.contains nRec),
      ("axiom excluded", !names.contains `TIxImp.axm),
      ("theorem excluded", !names.contains `TIxImp.thm),
      ("proj fixture excluded", !names.contains `TIxImp.P) ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none => return (true, subset.size, 0, none)
  finally
    IO.FS.removeDirAll dir

/-- C8: a consumer file `import_ixe`s the fixture artifact through the
    real command elaborator (in-process frontend + interpreter) and
    defines a term over the materialized constants. -/
private def elabTest : IO (Bool × Nat × Nat × Option String) := do
  let dir ← IO.FS.createTempDir
  let ixePath := (dir / "fixture.ixe").toString
  let consumerPath := dir / "Consumer.lean"
  try
    let original ← buildFixtureConsts
    let _ ← Ix.CompileM.rsCompileEnvBytesFFI original.toList ixePath false
    -- Materialized constants carry no compiled code (kernel-level
    -- import), so consumer definitions over them are `noncomputable`;
    -- execution is `#ixeval`'s job, Lean-native code the post-hoc LCNF
    -- path (plan D5).
    IO.FS.writeFile consumerPath
      s!"import Ix.ImportIxe\n\
         import Ix.IxEval\n\
         import_ixe \"{ixePath}\"\n\
         noncomputable def Consumer.uses : TIxImp.N := TIxImp.dbl \
         (TIxImp.N.succ TIxImp.N.zero)\n\
         theorem Consumer.alsoUses : TIxImp.T := TIxImp.thm\n\
         #ixeval TIxImp.dbl (TIxImp.N.succ TIxImp.N.zero)\n"
    let env ← getFileEnv consumerPath
    let checks : List (String × Bool) := [
      ("consumer def elaborated", env.contains `Consumer.uses),
      ("consumer theorem elaborated", env.contains `Consumer.alsoUses),
      ("materialized inductive present", env.contains nN),
      ("materialized recursor present", env.contains nRec),
      ("materialized defn present", env.contains `TIxImp.dbl) ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none => return (true, 0, 0, none)
  catch e =>
    return (false, 0, 0, some s!"consumer elaboration failed: {e}")
  finally
    IO.FS.removeDirAll dir

/-- C9: the ZkVoting consumption pattern against an imported artifact —
    `import_ixe` the fixture, commit a private value of an imported
    type (`Ix.Commit.commitDef`), and build an evaluation claim over an
    imported function applied to the commitment
    (`Ix.Commit.evalClaim`) — all with a closure-scoped compile, so
    cost tracks the claim, not the environment. (Proving the claim is
    `ix prove`'s job; the IxVM eval arm is still landing.) -/
private def zkPatternTest : IO (Bool × Nat × Nat × Option String) := do
  let dir ← IO.FS.createTempDir
  let ixePath := (dir / "fixture.ixe").toString
  let consumerPath := dir / "Consumer.lean"
  try
    let original ← buildFixtureConsts
    let _ ← Ix.CompileM.rsCompileEnvBytesFFI original.toList ixePath false
    IO.FS.writeFile consumerPath
      s!"import Ix.ImportIxe\nimport_ixe \"{ixePath}\"\n"
    let env ← getFileEnv consumerPath
    -- Closure-scoped compile env over what the claim touches.
    let mut seen : Lean.NameSet := {}
    let mut work : Array Lean.Name := #[`TIxImp.dbl, nN, nZero, nSucc]
    let mut closure : List (Lean.Name × Lean.ConstantInfo) := []
    while !work.isEmpty do
      let n := work.back!
      work := work.pop
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n
        | return (false, 0, 0, some s!"consumer env missing {n}")
      closure := (n, ci) :: closure
      for r in Ix.Replay.constantInfoReferences ci do
        unless seen.contains r do
          work := work.push r
    let phases ← Ix.CompileM.rsCompilePhasesOf closure
    let compileEnv := Ix.Commit.mkCompileEnv phases
    -- Commit a private value of the imported type.
    let voteType := Lean.Expr.const nN []
    let vote := Lean.Expr.app (.const nSucc []) (.const nZero [])
    let (commitAddr, env', compileEnv') ←
      Ix.Commit.commitDef compileEnv env [] voteType vote
    let commitName := Address.toUniqueName commitAddr
    unless env'.contains commitName do
      return (false, 0, 0,
        some "commitDef did not register the commitment constant")
    -- Claim: an imported function applied to the commitment evaluates
    -- to the public result.
    let input := Lean.mkApp (.const `TIxImp.dbl []) (.const commitName [])
    let output := Lean.mkApp (.const nSucc [])
      (Lean.mkApp (.const nSucc []) (.const nZero []))
    let claim ← match Ix.Commit.evalClaim compileEnv' [] input output
        voteType with
      | .ok claim => pure claim
      | .error e => return (false, 0, 0, some s!"evalClaim failed: {e}")
    match claim with
    | .eval i o _ =>
      if i == o then
        return (false, 0, 0, some "degenerate claim: input addr = output addr")
      return (true, 0, 0, none)
    | _ => return (false, 0, 0, some "expected an eval claim")
  finally
    IO.FS.removeDirAll dir

def suite : List TestSeq := [
  .individualIO "materialize ∘ compile is exact and root-stable" none
    (roundtripTest false) .done,
  .individualIO "alpha-collapsed mutual materialization is exact and root-stable" none
    (roundtripTest true) .done,
  .individualIO "only-scoped materialization returns the closure" none
    closureTest .done,
  .individualIO "import_ixe elaborates a consumer file (C8)" none
    elabTest .done,
  .individualIO "commit + eval claim over imported constants (C9)" none
    zkPatternTest .done ]

end Tests.Ix.ImportIxe
