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
`ixcc` executable (`compile …`). A decline or
rejection is recorded as the row's status, with the compiler's
`stage: code: message`, and the row is left out. All C of both profiles
(driver, adapters, twins, and `leanc`'s C compilation) is compiled with the
same unhardened flags, without the nixpkgs wrapper's hardening
(`NIX_HARDENING_ENABLE=`) and with frame pointers omitted, as upstream clang
does at `-O2`/`-O3`. -/

namespace Runner

open Lean System

def run (cmd : String) (args : List String) (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let output ← IO.Process.output { cmd, args := args.toArray, cwd, env }
  if output.exitCode != 0 then
    throw (IO.userError s!"{cmd} {" ".intercalate args} exited {output.exitCode}:\n{output.stderr}")
  return output

/-- Remove `path` if it exists so a failed rebuild can never leave a stale artifact behind. -/
def removeIfExists (path : FilePath) : IO Unit := do
  if ← path.pathExists then
    try IO.FS.removeFile path catch _ => pure ()

/-- Compute the lowercase hex SHA-256 digest of `path` using `sha256sum`. -/
def fileSha256 (path : FilePath) : IO String := do
  let out ← run "sha256sum" [path.toString]
  let some hex := (out.stdout.splitOn " ").head?
    | throw (IO.userError s!"sha256sum returned empty output for {path}")
  let hex := hex.trimAscii.toString
  if hex.length != 64 then
    throw (IO.userError s!"unexpected sha256sum digest '{hex}' for {path}")
  return hex

/-- Compute the SHA-256 digest of `path` if it exists, otherwise `none`. -/
def fileSha256? (path : FilePath) : IO (Option String) := do
  if ← path.pathExists then some <$> fileSha256 path else pure none

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

/-- Flags that omit frame pointers, matching upstream clang at `-O2`/`-O3`
when Nixpkgs wrapper hardening is disabled (`ccEnv`). -/
def omitFpFlags : List String := ["-fomit-frame-pointer", "-momit-leaf-frame-pointer"]

/-- How the entry profile compiles C: clang at `level`, without the nixpkgs
wrapper's hardening (zeroing call-used registers, stack protectors,
fortify, PIE) and with frame pointers omitted, as upstream clang does at
`-O2`. -/
def ccFlags (level : String) : List String :=
  [level] ++ omitFpFlags ++ ["-Wall", "-Wextra", "-Werror"]
def ccEnv : Array (String × Option String) := #[("NIX_HARDENING_ENABLE", some "")]

/-- Resolve extra `-I`/`-L`/`-Wl,-rpath` flags needed to compile and link with `-lgmp`
when `gmp.h` is not on the default compiler search path (e.g. inside `nix develop`). -/
def resolveGmpFlags : IO (List String) := do
  -- 1. Explicit environment override
  if let (some dev, some lib) := (← IO.getEnv "GMP_DEV", ← IO.getEnv "GMP_LIB") then
    return [s!"-I{dev}/include", s!"-L{lib}/lib", s!"-Wl,-rpath,{lib}/lib"]
  -- 2. Standard system header path
  for p in ["/usr/include/gmp.h", "/usr/include/x86_64-linux-gnu/gmp.h"] do
    if ← (p : FilePath).pathExists then return []
  -- 3. pkg-config if configured
  try
    let pc ← IO.Process.output { cmd := "pkg-config", args := #["--cflags", "--libs", "gmp"] }
    if pc.exitCode == 0 then
      let words := (pc.stdout.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
      let flags := words.filter (· != "-lgmp")
      unless flags.isEmpty do return flags
  catch _ => pure ()
  -- 4. Nix fallback (`nixpkgs#gmp.dev` and `nixpkgs#gmp`)
  try
    let devOut ← IO.Process.output { cmd := "nix", args := #["build", "--no-link", "--print-out-paths", "nixpkgs#gmp.dev"] }
    let libOut ← IO.Process.output { cmd := "nix", args := #["build", "--no-link", "--print-out-paths", "nixpkgs#gmp"] }
    if devOut.exitCode == 0 && libOut.exitCode == 0 then
      let dev := ((devOut.stdout.trimAscii.toString.splitOn "\n").headD "").trimAscii.toString
      let lib := ((libOut.stdout.trimAscii.toString.splitOn "\n").headD "").trimAscii.toString
      if !dev.isEmpty && !lib.isEmpty then
        return [s!"-I{dev}/include", s!"-L{lib}/lib", s!"-Wl,-rpath,{lib}/lib"]
  catch _ => pure ()
  return []

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
  sha256 : Option String := none

def Status.json (s : Status) : Json :=
  Json.mkObj ([("profile", Json.str s.profile), ("row", Json.str s.row),
    ("fixture", Json.str s.fixture), ("status", Json.str s.status), ("detail", Json.str s.detail)] ++
    match s.sha256 with | some h => [("sha256", Json.str h)] | none => [])

/-! ## The ixcc row's object -/

/-- `ixcc compile` of the fixture's closure into `OUT/ixcc/`:
`ok` with the wall time and `--stats` text, or the compiler's diagnostic. -/
def compileClosure (o : Options) (out : FilePath) (fixture : Fixture) (arity : Nat) :
    IO (Except String (Float × String)) := do
  let dir := out / "ixcc"
  IO.FS.createDirAll dir
  let obj := dir / s!"{fixture.name}.o"
  let sig := dir / s!"{fixture.name}.sig.json"
  let statsFile := dir / s!"{fixture.name}.stats.txt"
  let irFile := dir / s!"{fixture.name}.ir.txt"
  -- Invalidate any stale object/metadata from an earlier run before compiling.
  removeIfExists obj
  removeIfExists sig
  removeIfExists statsFile
  removeIfExists irFile
  let closure := o.closures / s!"{fixture.name}.ixe"
  let equations := o.closures / s!"{fixture.name}.equations.json"
  unless ← closure.pathExists do return .error s!"no frozen closure {closure}"
  let common := ["compile", closure.toString, "--equations", equations.toString,
    "-o", obj.toString]
  let cmd := o.ixcc.headD "ixcc"
  let lead := o.ixcc.drop 1
  let start ← IO.monoNanosNow
  let output ← IO.Process.output { cmd, args := (lead ++ common ++ ["--signatures", sig.toString, "--stats"]).toArray }
  let stop ← IO.monoNanosNow
  if output.exitCode != 0 then
    removeIfExists obj
    removeIfExists sig
    return .error (output.stderr.trimAscii.toString)
  IO.FS.writeFile statsFile output.stdout
  -- the IR at every level, for attribution (an untimed second run)
  let dump ← IO.Process.output { cmd, args := (lead ++ common ++ ["--dump-ir", "all"]).toArray }
  IO.FS.writeFile irFile dump.stdout
  -- the root must be `entry` with the fixture's arity and a Nat result
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile sig))
  let roots ← IO.ofExcept ((json.getObjValD "roots").getArr?)
  match roots.toList with
  | [root] =>
    let params := (root.getObjValD "params").getNat?.toOption
    let ty := (root.getObjValD "type").getStr?.toOption
    let symbol := (root.getObjValD "symbol").getStr?.toOption
    unless params == some arity && ty == some "n" && symbol == some "cx_entry" do
      removeIfExists obj
      return .error s!"unexpected root signature {root.compress}"
  | _ =>
    removeIfExists obj
    return .error s!"expected one root, got {roots.size}"
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
  removeIfExists target
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
    let _ ← run "leanc" (["-O3", "-DNDEBUG"] ++ omitFpFlags ++ ["-c", c.toString, "-o", (obj / "BenchEntry.o").toString]) (env := ccEnv)
    let _ ← run "leanc" (["-O2"] ++ omitFpFlags ++ [s!"-DARITY={arity}", "-c", (here / "row_lean.c").toString,
      "-o", (obj / "row.o").toString]) (env := ccEnv)
    let _ ← run "leanc" ["-o", target.toString, driver, (obj / "row.o").toString, (obj / "BenchEntry.o").toString] (env := ccEnv)
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
def buildProcessRow (o : Options) (manifest : Manifest) (root out : FilePath) (row : Row) (fixture : Fixture)
    (gmpFlags : IO (List String) := resolveGmpFlags) :
    IO (Option String) := do
  let target := binary out row fixture
  IO.FS.createDirAll (target.parent.getD out)
  removeIfExists target
  match row with
  | .leanClang =>
    let c := out / "c" / (fixture.name ++ ".c")
    IO.FS.createDirAll (c.parent.getD out)
    -- Lean requires the source inside its working root, so compile from `root`.
    let subst := [("src", fixture.lean), ("c", c.toString), ("out", target.toString)]
    let compile := expand manifest.leanCompile subst
    let _ ← run compile.head! compile.tail! (cwd := some root)
    let link := expand manifest.leanLink subst
    let linkArgs :=
      if link.tail!.any (fun w => w == "-O3" || w == "-O2") then
        link.tail!.flatMap fun w => if w == "-O3" || w == "-O2" then w :: omitFpFlags else [w]
      else
        omitFpFlags ++ link.tail!
    let _ ← run link.head! linkArgs (env := ccEnv)
    return some "built"
  | .clangO2 | .clangO3 =>
    let level := if row == .clangO2 then "-O2" else "-O3"
    let command := expand fixture.twin.compile
      [("src", (root / fixture.twin.path).toString), ("out", target.toString)]
    let args :=
      if command.tail!.any (fun w => w == "-O2" || w == "-O3") then
        command.tail!.flatMap fun word =>
          if word == "-O2" || word == "-O3" then level :: omitFpFlags else [word]
      else
        level :: omitFpFlags ++ command.tail!
    let args ← if args.contains "-lgmp" then do
        let gmp ← gmpFlags
        pure (args.flatMap fun w => if w == "-lgmp" then gmp ++ [w] else [w])
      else pure args
    let _ ← run command.head! args (env := ccEnv)
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
  -- Remove any stale build manifest before rebuilding so a failed build cannot leave yesterday's record.
  removeIfExists (out / "build.json")
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
  -- The early backend probe's hand-written kernels, when the probe is given
  let mut statuses : Array Status := #[]
  let mut compiles : Array Json := #[]
  if let some probe := o.probe then
    IO.FS.createDirAll (out / "probe")
    let probed ← run probe.toString [(out / "probe").toString, "--reps", "20"]
    IO.FS.writeFile (out / "probe" / "probe.jsonl") probed.stdout
  let gmpCache ← IO.mkRef (none : Option (List String))
  let getGmpFlags : IO (List String) := do
    match ← gmpCache.get with
    | some fs => pure fs
    | none =>
      let fs ← resolveGmpFlags
      gmpCache.set (some fs)
      pure fs
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
        | some s =>
          let digest ← if s == "built" then some <$> fileSha256 (entryBinary out row fixture) else pure none
          statuses := statuses.push { profile := "entry", row := row.name, fixture := fixture.name, status := s, sha256 := digest }
        | none => pure ()
    for row in Row.process do
      match ← buildProcessRow o manifest root out row fixture getGmpFlags with
      | some s =>
        let digest ← if s == "built" then some <$> fileSha256 (binary out row fixture) else pure none
        statuses := statuses.push { profile := "process", row := row.name, fixture := fixture.name, status := s, sha256 := digest }
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
    ("entry_lean", Json.str "lean -c; NIX_HARDENING_ENABLE= leanc -O3 -DNDEBUG -fomit-frame-pointer -momit-leaf-frame-pointer (BenchEntry.c); leanc -O2 -fomit-frame-pointer -momit-leaf-frame-pointer (row_lean.c); leanc link"),
    ("process_cc_env", Json.str "NIX_HARDENING_ENABLE="),
    ("process_omit_fp_flags", toJson omitFpFlags)]).pretty ++ "\n")

/-! ## Check -/

/-- A build record loaded from `build.json`. -/
structure BuildRecord where
  profile : String
  row : String
  fixture : String
  status : String
  sha256 : Option String

/-- Load all recorded row build outcomes from `OUT/build.json`. -/
def loadBuildRecords (out : FilePath) : IO (Array BuildRecord) := do
  let path := out / "build.json"
  unless ← path.pathExists do
    throw (IO.userError s!"missing build manifest {path}; run `build` first")
  let json ← IO.ofExcept ((Json.parse (← IO.FS.readFile path)).mapError IO.userError)
  let raw ← IO.ofExcept (((json.getObjValD "statuses").getArr?).mapError IO.userError)
  raw.mapM fun e => IO.ofExcept ((do
    return {
      profile := ← (← e.getObjVal? "profile").getStr?
      row := ← (← e.getObjVal? "row").getStr?
      fixture := ← (← e.getObjVal? "fixture").getStr?
      status := ← (← e.getObjVal? "status").getStr?
      sha256 := (e.getObjValD "sha256").getStr?.toOption
    } : Except String BuildRecord).mapError IO.userError)

/-- The rows of a profile that `build.json` records as `"built"` for `fixture`,
after verifying each executable exists on disk and matches its recorded SHA-256 digest. -/
def builtRowsWithDigests (out : FilePath) (entry : Bool) (fixture : Fixture) :
    IO (List (Row × String)) := do
  let records ← loadBuildRecords out
  let profile := if entry then "entry" else "process"
  let matching := records.filter fun r =>
    r.profile == profile && r.fixture == fixture.name && r.status == "built"
  let mut result : List (Row × String) := []
  for rec in matching do
    let some row := Row.ofName? rec.row
      | throw (IO.userError s!"build.json: unknown row '{rec.row}' for {fixture.name}")
    let path := if entry then entryBinary out row fixture else binary out row fixture
    unless ← path.pathExists do
      throw (IO.userError s!"build.json records {profile}/{rec.row}/{fixture.name} as built, but {path} is missing")
    let some expected := rec.sha256
      | throw (IO.userError s!"build.json entry for {profile}/{rec.row}/{fixture.name} is missing sha256; re-run `build`")
    let actual ← fileSha256 path
    if actual != expected then
      throw (IO.userError s!"digest mismatch for {path}: build.json has {expected}, on-disk binary has {actual}")
    unless result.any (·.1 == row) do
      result := result ++ [(row, actual)]
  return result

/-- The rows of a profile verified against `build.json` and their on-disk SHA-256 digests. -/
def builtRows (out : FilePath) (entry : Bool) (fixture : Fixture) : IO (List Row) := do
  return (← builtRowsWithDigests out entry fixture).map (·.1)

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
