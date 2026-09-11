import Benchmarks.Compiler.Check

namespace Benchmarks.Compiler
open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

structure Toolchains where
  gcc : String := "gcc"
  clang : String := "clang"
  compcert : String := "ccomp"
  cakeml : String := "cake"
  timerTool : String := "time"
  deriving ToJson, FromJson

def cFlags : Array String := #["-O3", "-march=x86-64", "-mtune=generic", "-fno-lto", "-fomit-frame-pointer"]
def runtimeEnv : Array (String × Option String) :=
  #[("CML_HEAP_SIZE", some "64"), ("CML_STACK_SIZE", some "8")]

def buildEnvNames : Array String := #["PATH", "LIBCLANG_PATH", "LEAN_PATH", "LEAN_CC", "LEAN_SYSROOT",
  "NIX_CFLAGS_COMPILE", "NIX_LDFLAGS", "NIX_ENFORCE_PURITY", "NIX_CC", "NIX_BINTOOLS",
  "NIX_CC_WRAPPER_TARGET_HOST_x86_64_unknown_linux_gnu", "NIX_BINTOOLS_WRAPPER_TARGET_HOST_x86_64_unknown_linux_gnu",
  "NIX_HARDENING_ENABLE", "NIX_ENFORCE_NO_NATIVE", "LD_LIBRARY_PATH", "LIBRARY_PATH", "CPATH",
  "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH", "NIX_STORE", "NIX_BUILD_TOP", "SOURCE_DATE_EPOCH", "LANG", "LC_ALL"]

def absolute (path : FilePath) : IO FilePath := do
  if path.isAbsolute then return path
  return (← IO.currentDir) / path

def fresh (output : FilePath) : IO Unit := do
  need (!(← output.pathExists)) s!"fresh output directory required: {output}"
  IO.FS.createDirAll output

def writeJson (path : FilePath) (json : Json) : IO Unit :=
  IO.FS.writeFile path (json.pretty 120 ++ "\n")

def binaryOutput (args : IO.Process.SpawnArgs) (input : Option String) : IO (UInt32 × ByteArray × String) := do
  let child ← if let some input := input then do
      let (stdin, child) ← (← IO.Process.spawn { args with stdout := .piped, stderr := .piped, stdin := .piped }).takeStdin
      stdin.putStr input
      stdin.flush
      pure child
    else IO.Process.spawn { args with stdout := .piped, stderr := .piped, stdin := .null }
  let stdout ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  return (exitCode, ← IO.ofExcept stdout.get, stderr)

/-- Persist each raw timing record as it arrives, including partial output
from interrupted or failed processes. The reader runs outside the worker. -/
def streamed (args : IO.Process.SpawnArgs) (path : FilePath) : IO IO.Process.Output := do
  let child ← IO.Process.spawn { args with stdout := .piped, stderr := .piped, stdin := .null }
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let file ← IO.FS.Handle.mk path .write
  let mut stdout := ""
  repeat
    let line ← child.stdout.getLine
    if line.isEmpty then break
    file.putStr line
    file.flush
    stdout := stdout ++ line
  let exitCode ← child.wait
  return { exitCode, stdout, stderr := ← IO.ofExcept stderr.get }

def logged (directory : FilePath) (name command : String) (args : Array String)
    (env : Array (String × Option String) := #[]) (input : Option String := none)
    (timeTool : String := "time") : IO String := do
  IO.FS.createDirAll directory
  let before ← IO.monoNanosNow
  let (exitCode, stdout, stderr) ← binaryOutput {
    cmd := timeTool
    args := #["-f", "{\"user_seconds\":%U,\"system_seconds\":%S,\"wall_seconds\":%e,\"peak_rss_kb\":%M,\"exit_code\":%x}",
      "-o", (directory / s!"{name}.resources.json").toString, command] ++ args
    env := env } input
  let elapsed := (← IO.monoNanosNow) - before
  IO.FS.writeBinFile (directory / s!"{name}.stdout") stdout
  IO.FS.writeFile (directory / s!"{name}.stderr") stderr
  writeJson (directory / s!"{name}.command.json") (Json.mkObj [
    ("command", toJson command), ("arguments", toJson args), ("environment_overrides", toJson env),
    ("stdin_blake3", toJson (input.map (digest ·.toUTF8))), ("exit_code", toJson exitCode.toNat),
    ("envelope_ns", toJson elapsed)])
  need (exitCode == 0) s!"{name} exited {exitCode}; see {directory / s!"{name}.stderr"}\n{stderr}"
  -- CakeML's exploration stream contains raw byte-string literals. Preserve
  -- the exact bytes above; an ASCII projection is sufficient to inspect calls.
  match String.fromUTF8? stdout with
  | some text => return text
  | none => return stdout.foldl (fun text byte => text.push (if byte.toNat < 128 then Char.ofNat byte.toNat else '?')) ""

def recordFiles (root : FilePath) : IO Json := do
  let paths ← files root
  let rows ← paths.toArray.mapM fun path => do
    let bytes ← IO.FS.readBinFile path
    return Json.mkObj [("path", toJson (path.toString.drop (root.toString.length + 1)).toString),
      ("bytes", toJson bytes.size), ("blake3", toJson (digest bytes))]
  return Json.arr rows

def inspectFiles (root : FilePath) (inventory : Json) : IO Unit := do
  need ((← recordFiles root) == inventory) s!"artifact inventory or digest changed: {root}"

def sourceSnapshot (output : FilePath) : IO Json := do
  let git ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  let names ← if git.exitCode == 0 then run "git" #["ls-files", "-z", "--cached", "--others", "--exclude-standard"]
    else run "rg" #["--files", "--hidden", "-g", "!.lake", "-g", "!.git", "-0"]
  let paths := names.splitOn "\x00" |>.filter (!·.isEmpty) |>.mergeSort (· ≤ ·)
  let mut rows := #[]
  let mut included := []
  for name in paths do
    if !(← (FilePath.mk name).pathExists) then continue
    let bytes ← IO.FS.readBinFile name
    rows := rows.push (Json.mkObj [("path", toJson name), ("bytes", toJson bytes.size), ("blake3", toJson (digest bytes))])
    included := name :: included
  IO.FS.writeFile (output / "source-files.list0") (String.intercalate "\x00" included.reverse ++ "\x00")
  let _ ← run "tar" #["--null", "--verbatim-files-from", "--files-from", (output / "source-files.list0").toString,
    "--sort=name", "--mtime=@1", "--owner=0", "--group=0", "--numeric-owner", "-czf", (output / "source.tar.gz").toString]
  let snapshot := Json.mkObj [("revision", toJson (if git.exitCode == 0 then git.stdout.trimAscii.toString else "source-snapshot-without-git")),
    ("status", toJson (← if git.exitCode == 0 then run "git" #["status", "--short"] else pure "Nix or extracted source snapshot")), ("files", Json.arr rows),
    ("archive", toJson "source.tar.gz"), ("archive_blake3", toJson (digest (← IO.FS.readBinFile (output / "source.tar.gz"))))]
  writeJson (output / "source.json") snapshot
  return snapshot

def buildSuite (output : FilePath) (tools : Toolchains) : IO Unit := do
  let output ← absolute output
  let cFlags := cFlags ++ #[s!"-ffile-prefix-map={output}=/benchmark-build"]
  fresh output
  for name in ["bin", "tools-bin", "artifacts/driver", "artifacts/lean", "artifacts/cakeml", "diagnostics/build"] do
    IO.FS.createDirAll (output / name)
  writeDatasets (output / "datasets")
  let logs := output / "diagnostics/build"
  let _ ← logged logs "worker-launcher" tools.gcc
    (cFlags ++ #["-Wall", "-Wextra", "-Werror", "Benchmarks/Compiler/native/worker_launcher.c",
      "-o", (output / "bin/worker-launcher").toString]) #[] none tools.timerTool
  let mut versions := #[]
  for (name, command, args, expected) in [
      ("gcc", tools.gcc, #["--version"], "14.3.0"),
      ("clang", tools.clang, #["--version"], "21.1.2"),
      ("compcert", tools.compcert, #["-version"], "3.16"),
      ("cakeml", tools.cakeml, #["--version"], "e8eca63affd1653105ca4b9cc2f5ca87a01cd0af"),
      ("lean", "lean", #["--version"], "4.33.1")] do
    let version ← logged logs s!"version-{name}" command args #[] none tools.timerTool
    need (version.contains expected) s!"pinned {name} version unavailable"
    versions := versions.push (Json.mkObj [("name", toJson name), ("version_output", toJson version)])
  let n2 := output / "artifacts/compilatrix"
  let _ ← logged logs "compilatrix-produce" ".lake/build/bin/compiler-source-native-runtime" #[n2.toString] #[] none tools.timerTool
  let _ ← logged logs "compilatrix-independent-gate" ".lake/build/bin/compiler-check-source-native-runtime"
    #["--fixture", ".lake/build/bin/compiler-source-native-runtime", "--cc", tools.gcc,
      "--harness", "Tests/Fixtures/Compiler/source-native-runtime/native_harness.c"] #[] none tools.timerTool
  for (name, value) in [("applyClosed", 3), ("letClosed", 4)] do
    let upstream := output / s!"artifacts/upstream-{name}"
    let _ ← logged logs s!"upstream-{name}-produce" ".lake/build/bin/compiler-source-native-upstream"
      #[upstream.toString, name] #[] none tools.timerTool
    let _ ← logged logs s!"upstream-{name}-check" ".lake/build/bin/compiler-check-source-native-upstream"
      #["inspect", upstream.toString] #[] none tools.timerTool
    let object := upstream / s!"upstream-{name}.o"
    let executable := output / s!"bin/upstream-{name}"
    let _ ← logged logs s!"upstream-{name}-link" tools.gcc
      (cFlags ++ #["-Wall", "-Wextra", "-Werror", s!"-DEXPECTED_RESULT={value}",
        "Tests/Fixtures/Compiler/source-native-upstream/native_harness.c", object.toString, "-Wl,-z,noexecstack", "-o", executable.toString])
      #[] none tools.timerTool
    let _ ← logged logs s!"upstream-{name}-native-check" executable.toString #[] #[] none tools.timerTool
    let _ ← logged logs s!"upstream-{name}-size" "size" #["-A", object.toString, executable.toString] #[] none tools.timerTool
    let _ ← logged logs s!"upstream-{name}-disassembly" "objdump" #["-d", object.toString] #[] none tools.timerTool
  let manifest ← readJson "Benchmarks/Compiler/manifest.json"
  let report ← readJson (n2 / "report.json")
  for key in ["source_identity", "ixir1_root", "main_identity", "release_identity", "pipeline_identity"] do
    need ((← field report key) == (← field (← field manifest "compilatrix") key)) s!"N2 {key} drifted"
  for name in ["common", "driver", "arena_backend"] do
    let _ ← logged logs s!"driver-{name}" tools.gcc (cFlags ++ #["-Wall", "-Wextra", "-Werror", "-c",
      s!"Benchmarks/Compiler/native/{name}.c", "-o", (output / s!"artifacts/driver/{name}.o").toString]) #[] none tools.timerTool
  for (name, command, flags) in [("gcc", tools.gcc, cFlags), ("clang", tools.clang, cFlags), ("compcert", tools.compcert, #["-O"])] do
    IO.FS.createDirAll (output / s!"artifacts/{name}")
    let _ ← logged logs s!"kernel-{name}" command (flags ++ #["-c", "Benchmarks/Compiler/native/arena_kernel.c",
      "-o", (output / s!"artifacts/{name}/kernel.o").toString]) #[] none tools.timerTool
  let driverObjects := #["common", "driver"].map fun name => (output / s!"artifacts/driver/{name}.o").toString
  for name in ["compilatrix", "compcert", "gcc", "clang"] do
    let kernels := if name == "compilatrix" then #[(n2 / "main.o").toString, (n2 / "release.o").toString]
      else #[(output / s!"artifacts/{name}/kernel.o").toString]
    let _ ← logged logs s!"link-{name}" tools.gcc (cFlags ++ driverObjects ++
      #[(output / "artifacts/driver/arena_backend.o").toString] ++ kernels ++
      #["-Wl,-z,noexecstack", "-o", (output / s!"bin/{name}").toString]) #[] none tools.timerTool
  let leanRoot := ((← run "lean" #["--print-prefix"]).trimAscii.toString : FilePath)
  let leanC := output / "artifacts/lean/LeanReverse.c"
  let _ ← logged logs "lean-generate-c" "lean" #["--root=Benchmarks/Compiler/lean", "-c", leanC.toString, "Benchmarks/Compiler/lean/LeanReverse.lean"] #[] none tools.timerTool
  let generated ← IO.FS.readFile leanC
  requireAll generated ["lean_is_exclusive", "lean_ctor_set", "LEAN_EXPORT lean_object* bench_lean_reverse", "l_benchReverseOnto"] "Lean operation boundary"
  for (name, source) in [("kernel", leanC.toString), ("backend", "Benchmarks/Compiler/native/lean_backend.c")] do
    -- Lake's ordinary release configuration is -O3 -DNDEBUG. Use leanc's
    -- installed C/ABI flags as well as the declared target and opaque boundary.
    let _ ← logged logs s!"lean-{name}" "leanc" (cFlags ++ #["-DNDEBUG", "-I", (leanRoot / "include").toString,
      "-c", source, "-o", (output / s!"artifacts/lean/{name}.o").toString]) #[("LEAN_CC", some tools.gcc)] none tools.timerTool
  let _ ← logged logs "link-lean" "leanc" (cFlags ++ driverObjects ++
    #["-Wl,-z,noexecstack", (output / "artifacts/lean/kernel.o").toString, (output / "artifacts/lean/backend.o").toString,
      "-o", (output / "bin/lean").toString]) #[("LEAN_CC", some tools.gcc)] none tools.timerTool
  let cakeDir := (FilePath.mk tools.cakeml).parent.getD "."
  let basis := cakeDir / "basis_ffi.c"
  need (← basis.pathExists) "CakeML bootstrap basis_ffi.c must be beside its executable"
  IO.FS.writeFile (output / "artifacts/cakeml/basis_ffi.c") (← IO.FS.readFile basis)
  let source ← IO.FS.readFile "Benchmarks/Compiler/cakeml/reverse.cml"
  for (name, extra) in [("kernel", #[]), ("diagnostic", #["--emit_empty_ffi=true"])] do
    let assembly ← logged logs s!"cakeml-{name}" tools.cakeml
      (#["--target=x64", "--reg_alg=2", "--gc=simple"] ++ extra) #[] (some source) tools.timerTool
    IO.FS.writeFile (output / s!"artifacts/cakeml/{name}.S") assembly
    let definitions := if name == "diagnostic" then #["-DDEBUG_FFI", "-DBENCH_CAKEML_GC", "-include", "sys/time.h"] else #[]
    let _ ← logged logs s!"cakeml-assemble-{name}" tools.gcc
      (cFlags ++ #["-c", (output / s!"artifacts/cakeml/{name}.S").toString, "-o",
        (output / s!"artifacts/cakeml/{name}.o").toString]) #[] none tools.timerTool
    let _ ← logged logs s!"link-cakeml-{name}" tools.gcc (cFlags ++ definitions ++
      #[(output / "artifacts/driver/common.o").toString, "Benchmarks/Compiler/native/cakeml_ffi.c",
        (output / "artifacts/cakeml/basis_ffi.c").toString, (output / s!"artifacts/cakeml/{name}.o").toString,
        "-lm", "-Wl,-z,noexecstack", "-o", (output / (if name == "kernel" then "bin/cakeml" else "bin/cakeml-diagnostic")).toString]) #[] none tools.timerTool
  let explore ← logged logs "cakeml-explore" tools.cakeml
    #["--target=x64", "--reg_alg=2", "--gc=simple", "--explore"] #[] (some source) tools.timerTool
  requireAll explore ["(jump reverseOnto@", "(jump digest_loop@", "(jump make@", "(lifecycle_loop_clos@"] "CakeML operation boundary"
  let _ ← logged logs "compress-cakeml-explore" "gzip" #["-n", (logs / "cakeml-explore.stdout").toString] #[] none tools.timerTool
  for name in implementations do
    let _ ← logged logs s!"size-{name}" "size" #["-A", (output / s!"bin/{name}").toString] #[] none tools.timerTool
    let _ ← logged logs s!"dependencies-{name}" "ldd" #[(output / s!"bin/{name}").toString] #[] none tools.timerTool
    let _ ← logged logs s!"disassembly-{name}" "objdump" #["-d", (output / s!"bin/{name}").toString] #[] none tools.timerTool
  for (name, path) in [("compilatrix-main", n2 / "main.o"), ("compilatrix-release", n2 / "release.o"),
      ("gcc-kernel", output / "artifacts/gcc/kernel.o"), ("clang-kernel", output / "artifacts/clang/kernel.o"),
      ("compcert-kernel", output / "artifacts/compcert/kernel.o"), ("lean-kernel", output / "artifacts/lean/kernel.o"),
      ("cakeml-kernel", output / "artifacts/cakeml/kernel.o")] do
    let _ ← logged logs s!"size-{name}" "size" #["-A", path.toString] #[] none tools.timerTool
  IO.FS.writeFile (output / "manifest.json") (← IO.FS.readFile "Benchmarks/Compiler/manifest.json")
  IO.FS.writeFile (output / "toolchains.json") (← IO.FS.readFile "Benchmarks/Compiler/toolchains.json")
  let mut toolRows := #[]
  let mut storePaths : Array String := #[]
  for (name, command) in [("gcc", tools.gcc), ("clang", tools.clang), ("compcert", tools.compcert),
      ("cakeml", tools.cakeml), ("lean", "lean"), ("lake", "lake"), ("leanc", "leanc")] do
    let path := ((← run "which" #[command]).trimAscii.toString : FilePath)
    let resolved := (← run "readlink" #["-f", path.toString]).trimAscii.toString
    toolRows := toolRows.push (Json.mkObj [("name", toJson name), ("command", toJson command),
      ("resolved", toJson resolved), ("retained_path", if name == "cakeml" then toJson "tools-bin/cakeml-bootstrap" else Json.null),
      ("blake3", toJson (digest (← IO.FS.readBinFile resolved)))])
    if resolved.startsWith "/nix/store/" then
      let storePath := String.intercalate "/" ((resolved.splitOn "/").take 4)
      if !storePaths.contains storePath then storePaths := storePaths.push storePath
  writeJson (output / "tool-identities.json") (Json.arr toolRows)
  let closure ← IO.Process.output { cmd := "nix-store", args := #["--query", "--requisites"] ++ storePaths }
  IO.FS.writeFile (output / "nix-closure.txt") closure.stdout
  writeJson (output / "nix-closure-status.json") (Json.mkObj [("exit_code", toJson closure.exitCode.toNat),
    ("stderr", toJson closure.stderr), ("roots", toJson storePaths)])
  for name in ["benchmark", "source-native-runtime", "check-source-native-runtime", "source-native-upstream", "check-source-native-upstream"] do
    let _ ← run "cp" #[s!".lake/build/bin/compiler-{name}", (output / s!"tools-bin/compiler-{name}").toString]
  let _ ← run "cp" #[tools.cakeml, (output / "tools-bin/cakeml-bootstrap").toString]
  IO.FS.writeFile (output / "tools-bin/basis_ffi.c") (← IO.FS.readFile basis)
  writeJson (output / "build.json") (Json.mkObj [
    ("format", toJson "compilatrix/benchmark-build/1"), ("tool_commands", toJson tools), ("versions", Json.arr versions),
    ("build_environment", toJson (← buildEnvNames.mapM fun name => do return (name, ← IO.getEnv name))),
    ("datasets_blake3", toJson (digest datasetBytes)), ("artifacts", ← recordFiles (output / "artifacts")),
    ("executables", ← recordFiles (output / "bin")), ("tools", ← recordFiles (output / "tools-bin")),
    ("tool_identities_blake3", toJson (digest (← IO.FS.readBinFile (output / "tool-identities.json")))),
    ("manifest_blake3", toJson (digest (← IO.FS.readBinFile (output / "manifest.json")))),
    ("toolchains_blake3", toJson (digest (← IO.FS.readBinFile (output / "toolchains.json"))))])
  let _ ← sourceSnapshot output
  IO.println s!"benchmark build: six implementations and separate CakeML GC executable in {output}"

end Benchmarks.Compiler
