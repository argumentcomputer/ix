import Runner.Manifest

/-! Build every row of every fixture once, then check each binary's output at
the fixture's test arguments against its recorded expected output. -/

namespace Runner

open Lean System

def run (cmd : String) (args : List String) (cwd : Option FilePath := none) :
    IO IO.Process.Output := do
  let output ← IO.Process.output { cmd, args := args.toArray, cwd }
  if output.exitCode != 0 then
    throw (IO.userError s!"{cmd} {" ".intercalate args} exited {output.exitCode}:\n{output.stderr}")
  return output

def binary (out : FilePath) (row : Row) (fixture : Fixture) : FilePath :=
  out / "bin" / row.name / fixture.name

/-- Toolchain versions recorded with every build. -/
def versions : IO Json := do
  let line (cmd : String) (args : List String) : IO String := do
    let output ← IO.Process.output { cmd, args := args.toArray }
    return ((output.stdout ++ output.stderr).splitOn "\n").headD "" |>.trimAscii.toString
  return Json.mkObj [
    ("lean", Json.str (← line "lean" ["--version"])),
    ("leanc", Json.str (← line "leanc" ["--version"])),
    ("clang", Json.str (← line "clang" ["--version"])),
    ("clang++", Json.str (← line "clang++" ["--version"]))]

/-- Build `row` for `fixture` into `out/bin/<row>/<name>`. -/
def buildOne (manifest : Manifest) (root out : FilePath) (row : Row) (fixture : Fixture) : IO Unit := do
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
  | .clangO2 | .clangO3 =>
    let level := if row == .clangO2 then "-O2" else "-O3"
    let command := expand fixture.twin.compile
      [("src", (root / fixture.twin.path).toString), ("out", target.toString)]
    let command := command.map fun word => if word == "-O2" then level else word
    let _ ← run command.head! command.tail!

def build (manifest : Manifest) (root out : FilePath) : IO Unit := do
  IO.FS.createDirAll out
  for fixture in manifest.fixtures do
    for row in Row.all do
      buildOne manifest root out row fixture
    IO.println s!"built {fixture.name}"
  IO.FS.writeFile (out / "build.json") ((Json.mkObj [
    ("format", Json.str "compilatrix/benchmark-build/2"),
    ("rows", Json.arr (Row.all.map (Json.str ·.name)).toArray),
    ("fixtures", Json.arr (manifest.fixtures.map (Json.str ·.name))),
    ("versions", ← versions)]).pretty ++ "\n")

/-- Every binary prints its fixture's expected output at the test arguments. -/
def check (manifest : Manifest) (root out : FilePath) : IO Unit := do
  let mut failures := 0
  for fixture in manifest.fixtures do
    let expected ← IO.FS.readFile (root / fixture.expected)
    for row in Row.all do
      let output ← run (binary out row fixture).toString fixture.testArgs
      if output.stdout != expected then
        failures := failures + 1
        IO.eprintln s!"{row.name}/{fixture.name}: output differs from {fixture.expected}"
  if failures > 0 then throw (IO.userError s!"{failures} outputs differ")
  IO.println s!"checked {manifest.fixtures.size} fixtures × {Row.all.length} rows"

end Runner
