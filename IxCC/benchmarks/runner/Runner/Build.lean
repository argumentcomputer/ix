import Runner.Manifest

/-! Build every row of every selected fixture once, in both timing profiles,
then check each binary's output against the fixture's recorded outputs.

**Process profile** (`OUT/bin/<row>/<fixture>`): the fixture's own program,
run once per process with the arguments on the command line; it prints what
the fixture's `main` prints.

**Entry profile** (`OUT/entry/<row>/<fixture>`): the timing driver
`entry/driver.c` linked with the row's adapter `entry/row_<row>.c` and the
row's code; one process initialises the row once and times repetitions of
the fixture's `entry` (see `Runner.Measure`).

The `ixcc` row compiles the fixture's frozen closure
(`<closures>/<fixture>.ixe` with its `.equations.json`) with the
`ixcc` executable, `compile … --no-typecheck` (typing is gated by the
compiler's own suites and costs 35–40 s on two closures). A decline or
rejection is recorded as the row's status, with the compiler's
`stage: code: message`, and the row is left out. All C of the entry profile
(driver, adapters, twins) is compiled with `cc` and the same flags, without
the nixpkgs wrapper's hardening (`NIX_HARDENING_ENABLE=`), as MEAS-4 does. -/

namespace Runner

open Lean System

def run (cmd : String) (args : List String) (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let output ← IO.Process.output { cmd, args := args.toArray, cwd, env }
  if output.exitCode != 0 then
    throw (IO.userError s!"{cmd} {" ".intercalate args} exited {output.exitCode}:\n{output.stderr}")
  return output

/-- The process profile's binary of `row` for `fixture`. -/
def binary (out : FilePath) (row : Row) (fixture : Fixture) : FilePath :=
  out / "bin" / row.name / fixture.name

/-- The entry profile's binary of `row` for `fixture`. -/
def entryBinary (out : FilePath) (row : Row) (fixture : Fixture) : FilePath :=
  out / "entry" / row.name / fixture.name

/-- Build options; paths are relative to the runner's directory. -/
structure Options where
  /-- Restrict to these fixtures. -/
  fixtures : Option (List String) := none
  /-- The compiler command: an executable and any leading arguments, for
  example `nix run ../..#ixcc --`. -/
  ixcc : List String := ["../../.lake/build/bin/ixcc"]
  /-- The frozen closures (`<fixture>.ixe`, `<fixture>.equations.json`). -/
  closures : FilePath := "../../fixtures/ixon-v4/bench-k1"
  /-- `backend-probe`, for the diagnostic `lir-kernel` row (left out when absent). -/
  probe : Option FilePath := none
  /-- The C compiler of the entry profile. -/
  cc : String := "cc"
  /-- Diagnostic `ixcc@NAME` rows: objects `DIR/<fixture>.o` with the
  ixcc row's interface (`cx_init`, `cx_entry`). -/
  variants : List (String × FilePath) := []

def Options.selects (o : Options) (f : Fixture) : Bool := o.fixtures.all (·.contains f.name)

/-- How the entry profile compiles C: clang at `level`, without the nixpkgs
wrapper's hardening (zeroing call-used registers, stack protectors,
fortify, PIE) and with frame pointers omitted, as upstream clang does at
`-O2`. -/
def ccFlags (level : String) : List String :=
  [level, "-fomit-frame-pointer", "-momit-leaf-frame-pointer", "-Wall", "-Wextra", "-Werror"]
def ccEnv : Array (String × Option String) := #[("NIX_HARDENING_ENABLE", some "")]

def firstLine (cmd : String) (args : List String) : IO String := do
  try
    let output ← IO.Process.output { cmd, args := args.toArray }
    return ((output.stdout ++ output.stderr).splitOn "\n").headD "" |>.trimAscii.toString
  catch _ => return "unavailable"

/-- Toolchain versions recorded with every build. -/
def versions (o : Options) : IO Json := do
  let ixccPath := o.ixcc.headD ""
  let digest ← try
      pure ((← run "sha256sum" [ixccPath]).stdout.splitOn " ").head!
    catch _ => pure "unavailable"
  return Json.mkObj [
    ("lean", Json.str (← firstLine "lean" ["--version"])),
    ("leanc", Json.str (← firstLine "leanc" ["--version"])),
    ("clang", Json.str (← firstLine "clang" ["--version"])),
    ("clang++", Json.str (← firstLine "clang++" ["--version"])),
    ("cc", Json.str (← firstLine o.cc ["--version"])),
    ("objdump", Json.str (← firstLine "objdump" ["--version"])),
    ("ixcc", Json.str (" ".intercalate o.ixcc)),
    ("ixcc_sha256", Json.str digest),
    ("repository", Json.str (← firstLine "git" ["-C", "../..", "describe", "--always", "--dirty", "--abbrev=12"]))]

/-- A build outcome, recorded in `build.json`. -/
structure Status where
  profile : String
  row : String
  fixture : String
  status : String
  detail : String := ""

def Status.json (s : Status) : Json :=
  Json.mkObj [("profile", Json.str s.profile), ("row", Json.str s.row),
    ("fixture", Json.str s.fixture), ("status", Json.str s.status), ("detail", Json.str s.detail)]

/-! ## The ixcc row's object -/

/-- `ixcc compile` of the fixture's closure into `OUT/ixcc/`:
`ok` with the wall time and `--stats` text, or the compiler's diagnostic. -/
def compileClosure (o : Options) (out : FilePath) (fixture : Fixture) (arity : Nat) :
    IO (Except String (Float × String)) := do
  let closure := o.closures / s!"{fixture.name}.ixe"
  let equations := o.closures / s!"{fixture.name}.equations.json"
  unless ← closure.pathExists do return .error s!"no frozen closure {closure}"
  let dir := out / "ixcc"
  IO.FS.createDirAll dir
  let obj := dir / s!"{fixture.name}.o"
  let sig := dir / s!"{fixture.name}.sig.json"
  let common := ["compile", closure.toString, "--equations", equations.toString,
    "-o", obj.toString, "--no-typecheck"]
  let cmd := o.ixcc.headD "ixcc"
  let lead := o.ixcc.drop 1
  let start ← IO.monoNanosNow
  let output ← IO.Process.output { cmd, args := (lead ++ common ++ ["--signatures", sig.toString, "--stats"]).toArray }
  let stop ← IO.monoNanosNow
  if output.exitCode != 0 then
    return .error (output.stderr.trimAscii.toString)
  IO.FS.writeFile (dir / s!"{fixture.name}.stats.txt") output.stdout
  -- the IR at every level, for attribution (an untimed second run)
  let dump ← IO.Process.output { cmd, args := (lead ++ common ++ ["--dump-ir", "all"]).toArray }
  IO.FS.writeFile (dir / s!"{fixture.name}.ir.txt") dump.stdout
  -- the root must be `entry` with the fixture's arity and a Nat result
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile sig))
  let roots ← IO.ofExcept ((json.getObjValD "roots").getArr?)
  match roots.toList with
  | [root] =>
    let params := (root.getObjValD "params").getNat?.toOption
    let ty := (root.getObjValD "type").getStr?.toOption
    let symbol := (root.getObjValD "symbol").getStr?.toOption
    unless params == some arity && ty == some "n" && symbol == some "cx_entry" do
      return .error s!"unexpected root signature {root.compress}"
  | _ => return .error s!"expected one root, got {roots.size}"
  return .ok ((stop - start).toFloat / 1e6, output.stdout)

/-! ## Entry-profile objects shared by rows -/

/-- Compile `src` with the entry profile's C flags. -/
def cc (o : Options) (level : String) (args : List String) : IO Unit := do
  let _ ← run o.cc (ccFlags level ++ args) (env := ccEnv)

def objdump (obj target : FilePath) : IO Unit := do
  try
    let text := (← run "objdump" ["-d", "-M", "intel", "--no-show-raw-insn", obj.toString]).stdout
    IO.FS.createDirAll (target.parent.getD ".")
    IO.FS.writeFile target text
  catch _ => pure ()

/-- The fixture's Lean source with the entry exported as `bench_entry` and
its `main` renamed (so Lean emits no C `main`). -/
def benchEntrySource (text : String) (fixture : Fixture) (arity : Nat) : Except String String := do
  let pieces := text.splitOn "\ndef main "
  unless pieces.length == 2 do throw s!"{fixture.lean}: expected one `def main`"
  let params := (List.range arity).map (s!"a{·}")
  let binders := " ".intercalate (params.map (s!"({·} : Nat)"))
  return "\ndef fixtureMain ".intercalate pieces ++
    s!"\n/-- The benchmark runner's entry-profile export (appended by the runner). -/\n@[export bench_entry] def benchEntry {binders} : Nat := {fixture.entryName} {" ".intercalate params}\n"

/-- Build one entry-profile row for a fixture; `none` when the row has no
implementation for it. -/
def buildEntryRow (o : Options) (root out : FilePath) (row : Row) (fixture : Fixture) (arity : Nat) :
    IO (Option String) := do
  let obj := out / "entry-obj" / row.name / fixture.name
  IO.FS.createDirAll obj
  let target := entryBinary out row fixture
  IO.FS.createDirAll (target.parent.getD out)
  let driver := (out / "entry-obj" / "driver.o").toString
  let here ← IO.FS.realPath "entry"
  let fixtureMacro := s!"-DFIXTURE_{fixture.ident}"
  match row with
  | .ixcc =>
    let object := out / "ixcc" / s!"{fixture.name}.o"
    unless ← object.pathExists do return none
    cc o "-O2" ["-c", (here / "row_ixcc.c").toString, "-o", (obj / "row.o").toString]
    cc o "-O2" ["-o", target.toString, driver, (obj / "row.o").toString, object.toString]
    objdump object (out / "asm" / row.name / s!"{fixture.name}.txt")
    return some "built"
  | .leanClang =>
    let src := out / "entry-src" / fixture.name
    IO.FS.createDirAll src
    let text ← IO.FS.readFile (root / fixture.lean)
    IO.FS.writeFile (src / "BenchEntry.lean") (← IO.ofExcept (benchEntrySource text fixture arity))
    let c := obj / "BenchEntry.c"
    let _ ← run "lean" ["-c", c.toString, "BenchEntry.lean"] (cwd := some src)
    let _ ← run "leanc" ["-O3", "-DNDEBUG", "-c", c.toString, "-o", (obj / "BenchEntry.o").toString]
    let _ ← run "leanc" ["-O2", s!"-DARITY={arity}", "-c", (here / "row_lean.c").toString,
      "-o", (obj / "row.o").toString]
    let _ ← run "leanc" ["-o", target.toString, driver, (obj / "row.o").toString, (obj / "BenchEntry.o").toString]
    objdump (obj / "BenchEntry.o") (out / "asm" / row.name / s!"{fixture.name}.txt")
    -- Lean's final IR, for attribution (an untimed second run with the trace on)
    let ir ← IO.Process.output { cmd := "lean", args := #["-Dtrace.compiler.ir.result=true", "-c",
      (obj / "ir.c").toString, "BenchEntry.lean"], cwd := some src }
    IO.FS.createDirAll (out / "ir" / row.name)
    IO.FS.writeFile (out / "ir" / row.name / s!"{fixture.name}.txt") ir.stdout
    return some "built"
  | .clangO2 | .clangO3 =>
    unless k1Twins.contains fixture.name do return none
    let level := if row == .clangO2 then "-O2" else "-O3"
    let twin ← IO.FS.realPath (root / fixture.twin.path)
    cc o level [s!"-DTWIN_SOURCE=\"{twin}\"", fixtureMacro, "-c", (here / "row_idiomatic.c").toString,
      "-o", (obj / "twin.o").toString]
    cc o level ["-o", target.toString, driver, (obj / "twin.o").toString]
    objdump (obj / "twin.o") (out / "asm" / row.name / s!"{fixture.name}.txt")
    return some "built"
  | .clangTagged =>
    unless k1Twins.contains fixture.name do return none
    let twins := out / "entry-obj" / "twins.o"
    let tagged := out / "entry-obj" / "tagged.o"
    cc o "-O2" [fixtureMacro, "-c", (here / "row_tagged.c").toString, "-o", (obj / "row.o").toString]
    cc o "-O2" ["-o", target.toString, driver, (obj / "row.o").toString, twins.toString, tagged.toString]
    return some "built"
  | .lirKernel =>
    let some (_, stem) := lirKernels.find? (·.1 == fixture.name) | return none
    let object := out / "probe" / s!"lir_{stem}.o"
    unless ← object.pathExists do return none
    cc o "-O2" [fixtureMacro, "-c", (here / "row_lir.c").toString, "-o", (obj / "row.o").toString]
    cc o "-O2" ["-o", target.toString, driver, (obj / "row.o").toString, object.toString]
    objdump object (out / "asm" / row.name / s!"{fixture.name}.txt")
    return some "built"
  | .variant name =>
    let some (_, dir) := o.variants.find? (·.1 == name) | return none
    let object := dir / s!"{fixture.name}.o"
    unless ← object.pathExists do return none
    -- keep the measured object with the session
    let kept := out / "variants" / name / s!"{fixture.name}.o"
    IO.FS.createDirAll (out / "variants" / name)
    IO.FS.writeBinFile kept (← IO.FS.readBinFile object)
    cc o "-O2" ["-c", (here / "row_ixcc.c").toString, "-o", (obj / "row.o").toString]
    cc o "-O2" ["-o", target.toString, driver, (obj / "row.o").toString, kept.toString]
    objdump kept (out / "asm" / row.name / s!"{fixture.name}.txt")
    return some "built"

/-! ## Build -/

/-- Build the process-profile row for a fixture. -/
def buildProcessRow (o : Options) (manifest : Manifest) (root out : FilePath) (row : Row) (fixture : Fixture) :
    IO (Option String) := do
  let target := binary out row fixture
  IO.FS.createDirAll (target.parent.getD out)
  match row with
  | .leanClang =>
    let c := out / "c" / (fixture.name ++ ".c")
    IO.FS.createDirAll (c.parent.getD out)
    -- Lean requires the source inside its working root, so compile from `root`.
    let subst := [("src", fixture.lean), ("c", c.toString), ("out", target.toString)]
    let compile := expand manifest.leanCompile subst
    let _ ← run compile.head! compile.tail! (cwd := some root)
    let link := expand manifest.leanLink subst
    let _ ← run link.head! link.tail!
    return some "built"
  | .clangO2 | .clangO3 =>
    let level := if row == .clangO2 then "-O2" else "-O3"
    let command := expand fixture.twin.compile
      [("src", (root / fixture.twin.path).toString), ("out", target.toString)]
    let command := command.map fun word => if word == "-O2" then level else word
    let _ ← run command.head! command.tail!
    return some "built"
  | .ixcc =>
    let object := out / "ixcc" / s!"{fixture.name}.o"
    unless ← object.pathExists do return none
    let rowObj := out / "entry-obj" / row.name / fixture.name / "row.o"
    cc o "-O2" ["-o", target.toString, (out / "entry-obj" / "driver-process.o").toString,
      rowObj.toString, object.toString]
    return some "built"
  | .clangTagged | .lirKernel | .variant _ => return none

def build (manifest : Manifest) (root out : FilePath) (o : Options) : IO Unit := do
  IO.FS.createDirAll out
  let out ← IO.FS.realPath out
  let fixtures := manifest.fixtures.filter o.selects
  -- shared entry-profile objects
  let common := out / "entry-obj"
  IO.FS.createDirAll common
  let here ← IO.FS.realPath "entry"
  cc o "-O2" ["-c", (here / "driver.c").toString, "-o", (common / "driver.o").toString]
  cc o "-O2" ["-DPROCESS", "-c", (here / "driver.c").toString, "-o", (common / "driver-process.o").toString]
  cc o "-O2" ["-c", (← IO.FS.realPath "../meas4/twins.c").toString, "-o", (common / "twins.o").toString]
  cc o "-O2" ["-c", (here / "tagged.c").toString, "-o", (common / "tagged.o").toString]
  objdump (common / "twins.o") (out / "asm" / "clang-tagged" / "twins.txt")
  objdump (common / "tagged.o") (out / "asm" / "clang-tagged" / "tagged.txt")
  -- MEAS-4's hand-written kernels, when the probe is given
  let mut statuses : Array Status := #[]
  let mut compiles : Array Json := #[]
  if let some probe := o.probe then
    IO.FS.createDirAll (out / "probe")
    let probed ← run probe.toString [(out / "probe").toString, "--reps", "20"]
    IO.FS.writeFile (out / "probe" / "probe.jsonl") probed.stdout
  for fixture in fixtures do
    let arity := fixture.natArity?
    -- the ixcc object, shared by both profiles
    if let some k := arity then
      match ← compileClosure o out fixture k with
      | .ok (ms, stats) =>
        compiles := compiles.push (Json.mkObj [("fixture", Json.str fixture.name),
          ("wall_ms", toJson ms), ("stats", Json.str stats)])
      | .error why =>
        statuses := statuses.push
          { profile := "both", row := "ixcc", fixture := fixture.name,
            status := "declined or unavailable", detail := why }
        IO.eprintln s!"ixcc/{fixture.name}: {why}"
      for row in Row.entry ++ o.variants.map (Row.variant ·.1) do
        match ← buildEntryRow o root out row fixture k with
        | some s => statuses := statuses.push { profile := "entry", row := row.name, fixture := fixture.name, status := s }
        | none => pure ()
    for row in Row.process do
      match ← buildProcessRow o manifest root out row fixture with
      | some s => statuses := statuses.push { profile := "process", row := row.name, fixture := fixture.name, status := s }
      | none => pure ()
    IO.println s!"built {fixture.name}"
  IO.FS.writeFile (out / "build.json") ((Json.mkObj [
    ("format", Json.str "ixcc/benchmark-build/3"),
    ("process_rows", Json.arr (Row.process.map (Json.str ·.name)).toArray),
    ("entry_rows", Json.arr ((Row.entry ++ o.variants.map (Row.variant ·.1)).map (Json.str ·.name)).toArray),
    ("variants", Json.mkObj (o.variants.map fun (n, d) => (n, Json.str d.toString))),
    ("fixtures", Json.arr (fixtures.map (Json.str ·.name))),
    ("statuses", Json.arr (statuses.map Status.json)),
    ("ixcc_compiles", Json.arr compiles),
    ("versions", ← versions o),
    ("entry_cc_flags", toJson (ccFlags "-O2|-O3")),
    ("entry_cc_env", Json.str "NIX_HARDENING_ENABLE="),
    ("entry_lean", Json.str "lean -c; leanc -O3 -DNDEBUG (BenchEntry.c); leanc -O2 (row_lean.c); leanc link")]).pretty ++ "\n")

/-! ## Check -/

/-- The rows of a profile whose binary exists for `fixture`. -/
def builtRows (out : FilePath) (entry : Bool) (fixture : Fixture) : IO (List Row) := do
  let variants ← if entry && (← (out / "entry").pathExists) then do
      let dirs ← (out / "entry").readDir
      let names := (dirs.map (·.fileName)).qsort (· < ·) |>.toList
      pure (names.filterMap fun n => match Row.ofName? n with
        | some (.variant v) => some (Row.variant v)
        | _ => none)
    else pure []
  (if entry then Row.entry ++ variants else Row.process).filterM fun row =>
    (if entry then entryBinary out row fixture else binary out row fixture).pathExists

def trimmed (s : String) : String := s.trimAscii.toString

/-- Every process binary prints its fixture's expected output at the test
arguments; every entry binary returns it at the test arguments and returns
`bench_expected` at the bench arguments. -/
def check (manifest : Manifest) (root out : FilePath) (only : Option (List String)) : IO Unit := do
  let mut failures := 0
  let mut checked := 0
  for fixture in manifest.fixtures.filter (fun f => only.all (·.contains f.name)) do
    let expected ← IO.FS.readFile (root / fixture.expected)
    for row in ← builtRows out false fixture do
      let output ← run (binary out row fixture).toString fixture.testArgs
      checked := checked + 1
      if output.stdout != expected then
        failures := failures + 1
        IO.eprintln s!"process {row.name}/{fixture.name}: output differs from {fixture.expected}"
    for row in ← builtRows out true fixture do
      for (args, want) in [(fixture.testArgs, some expected), (fixture.benchArgs, fixture.benchExpected)] do
        let some want := want | continue
        let output ← run (entryBinary out row fixture).toString (["1", "1"] ++ args)
        checked := checked + 1
        match (trimmed output.stdout).splitOn " " with
        | [_, result, _, _, _] =>
          if result != trimmed want then
            failures := failures + 1
            IO.eprintln s!"entry {row.name}/{fixture.name} {" ".intercalate args}: {result}, expected {trimmed want}"
        | _ =>
          failures := failures + 1
          IO.eprintln s!"entry {row.name}/{fixture.name}: malformed output {output.stdout}"
  if failures > 0 then throw (IO.userError s!"{failures} of {checked} outputs differ")
  IO.println s!"checked {checked} outputs"

end Runner
