import Lean.Data.Json
import LSpec
import IxC.Kernel.Ixon.Prelude

/-! # Init+Std through the `ix` binary (merge queue tier `ci:landing-initstd-cli`)

* `initstd-reference`: `ix compile-lean Benchmarks/Compile/CompileInitStd.lean
  --rust-check`, the certified compile of Init+Std, which refuses the compile
  on any failed report check, with the default role binding. Its bytes are
  compared with the Rust compiler's output
  (`ALIGNED`). The artifact's SHA-256 and size must equal the reference in
  `Tests/Fixtures/initstd-reference.txt`. The Rust kernel then checks the
  artifact (`ix check-rs --anon`): it must admit every role the default role
  table binds and refuse no role group, and pass the reference's count of
  constants. A change that moves the compiler's bytes, or the Rust kernel's
  verdicts on the artifact, updates that file in the same commit.
* `fidelity-initstd`: `ix validate-lean Benchmarks/Compile/CompileInitStd.lean
  --report`, gated on the report: every phase (the compile with its role
  binding, the serde gate, projection and block-order fidelity, the reader
  against the Lean source, decompilation) passed and none failed.

Both run the `ix` binary (`.lake/build/bin/ix`, which `IxTests` builds), as a
user would, in a subprocess. -/

namespace Tests.Ix.InitStd

def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

/-- The Init+Std driver, from the repository root. -/
def source : String := "Benchmarks/Compile/CompileInitStd.lean"

def referencePath : System.FilePath := "Tests" / "Fixtures" / "initstd-reference.txt"

/-- The reference artifact's digest and size, and the Rust kernel's verdicts on it. -/
structure Reference where
  sha256 : String
  bytes : Nat
  rustPassed : Nat
  rustChecked : Nat

def isHex64 (s : String) : Bool :=
  s.length == 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The reference file: `#` comments and `key<TAB>value` lines, each key once,
no other key. -/
def parseReference (text : String) : Except String Reference := do
  let keys := ["sha256", "bytes", "rust-kernel-passed", "rust-kernel-checked"]
  let mut kv : Std.HashMap String String := {}
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | [k, v] =>
      unless keys.contains k do throw s!"unknown key '{k}'"
      if kv.contains k then throw s!"key '{k}' given twice"
      kv := kv.insert k v
    | _ => throw s!"malformed line '{line}' (expected key<TAB>value)"
  let get (k : String) : Except String String :=
    match kv.get? k with
    | some v => .ok v
    | none => .error s!"no '{k}' line"
  let sha ← get "sha256"
  unless isHex64 sha do throw s!"sha256 '{sha}' is not 64 lowercase hex digits"
  let nat (k : String) : Except String Nat := do
    let v ← get k
    match v.toNat? with
    | some n => .ok n
    | none => .error s!"{k} '{v}' is not a number"
  return {
    sha256 := sha
    bytes := (← nat "bytes")
    rustPassed := (← nat "rust-kernel-passed")
    rustChecked := (← nat "rust-kernel-checked") }

private def sample (sha : String) (more : String) : String :=
  s!"# c\nsha256\t{sha}\nbytes\t12\nrust-kernel-passed\t3\nrust-kernel-checked\t4\n{more}"

#guard (parseReference (sample ("".pushn 'a' 64) "")).toOption.map
  (fun r => (r.bytes, r.rustPassed, r.rustChecked)) == some (12, 3, 4)
#guard (parseReference (sample "ab" "")).toOption.isNone
#guard (parseReference (sample ("".pushn 'a' 64) "bytes\t1")).toOption.isNone
#guard (parseReference (sample ("".pushn 'a' 64) "size\t1")).toOption.isNone
#guard (parseReference ("sha256\t" ++ "".pushn 'a' 64 ++ "\nbytes\t1")).toOption.isNone

/-- The `bound roles: N admitted, M group(s) refused` line of `ix check-rs`:
`(N, M)`. -/
def admission (out : String) : Option (Nat × Nat) := do
  let line ← (out.splitOn "\n").find? fun l => (l.splitOn "bound roles: ").length > 1
  let rest ← ((line.splitOn "bound roles: ")[1]?)
  let [admitted, refused] := rest.splitOn " admitted, " | none
  let refused ← (refused.splitOn " group").head?
  return ((← admitted.trimAscii.toString.toNat?), (← refused.trimAscii.toString.toNat?))

/-- The `[check] P/T passed` line of `ix check-rs`: `(P, T)`. -/
def passedCount (out : String) : Option (Nat × Nat) := do
  let line ← (out.splitOn "\n").find? fun l => l.startsWith "[check] " && l.endsWith " passed"
  let [_, frac, _] := line.splitOn " " | none
  let [p, t] := frac.splitOn "/" | none
  return ((← p.toNat?), (← t.toNat?))

#guard admission "x\n[rs_kernel_check_anon] bound roles: 59 admitted, 0 group(s) refused (1ms)\n" ==
  some (59, 0)
#guard admission "[rs_kernel_check_anon] bound roles: 57 admitted, 2 group(s) refused" == some (57, 2)
#guard admission "no binding" == none
#guard passedCount "[check] checked 4 constants in 1s\n[check] 3/4 passed\n" == some (3, 4)

/-- Run `ix` with `args`, logging the command line, its exit code and time. -/
def runIx (args : Array String) : IO IO.Process.Output := do
  unless ← ixExe.pathExists do
    throw (IO.userError s!"{ixExe} missing: run `lake build ix`")
  let exe ← IO.FS.realPath ixExe
  IO.println s!"[initstd] ix {" ".intercalate args.toList}"
  let t0 ← IO.monoMsNow
  let out ← IO.Process.output { cmd := exe.toString, args }
  IO.println s!"[initstd]   exit {out.exitCode} in {(← IO.monoMsNow) - t0} ms"
  return out

/-- The lines of `s` that contain one of `needles`. -/
def linesWith (s : String) (needles : List String) : List String :=
  (s.splitOn "\n").filter fun l => needles.any fun n => (l.splitOn n).length > 1

/-- The end of a process's output, for a failure message. -/
def tail (out : IO.Process.Output) : String :=
  s!"{(out.stdout.takeEnd 2000).toString}\n{(out.stderr.takeEnd 2000).toString}"

/-- The SHA-256 of a file, by `sha256sum`. -/
def sha256File (path : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  unless out.exitCode == 0 do
    throw (IO.userError s!"sha256sum {path} exited {out.exitCode}: {out.stderr}")
  match (out.stdout.splitOn " ").head? with
  | some h => if isHex64 h then pure h else throw (IO.userError s!"sha256sum printed {out.stdout}")
  | none => throw (IO.userError s!"sha256sum printed nothing")

def reportChecks (name : String) (checks : Array (String × Bool)) : IO UInt32 :=
  LSpec.lspecIO (.ofList [(name, checks.toList.map fun (label, ok) => LSpec.test label ok)]) []

/-- `initstd-reference`. -/
def reference : IO UInt32 := do
  let expected ← IO.ofExcept ((parseReference (← IO.FS.readFile referencePath)).mapError
    fun e => s!"{referencePath}: {e}")
  let dir ← IO.FS.createTempDir
  try
    let artifact := dir / "initstd.ixe"
    let compiled ← runIx #["compile-lean", source, "--rust-check", "--out", artifact.toString]
    for l in linesWith compiled.stdout ["] compile:", "post-steps", "wrote", "ALIGNED", "DIVERGED"] do
      IO.println l
    unless compiled.exitCode == 0 && (← artifact.pathExists) do
      IO.eprintln (tail compiled)
      return ← reportChecks "initstd-reference"
        #[("ix compile-lean on Init+Std passes its report checks and matches the Rust compiler", false)]
    let aligned := !(linesWith compiled.stdout ["[compile-lean] ALIGNED:"]).isEmpty
    let sha ← sha256File artifact
    let size := (← artifact.metadata).byteSize.toNat
    IO.println s!"[initstd] artifact sha256 {sha}, {size} bytes; reference {expected.sha256}, \
      {expected.bytes} bytes"
    unless sha == expected.sha256 && size == expected.bytes do
      IO.eprintln s!"[initstd] the Init+Std artifact differs from {referencePath}. If the change \
        is meant to move the compiler's bytes, record sha256 {sha} and bytes {size} there."
    -- the Rust kernel on the artifact, under its role binding; it exits 3 when
    -- some constant fails, which the count of passing constants decides
    let roles := (← IO.ofExcept Ix.Kernel.Reader.defaultTable).bound.size
    let checked ← runIx #["check-rs", artifact.toString, "--anon"]
    let both := checked.stdout ++ "\n" ++ checked.stderr
    for l in linesWith both ["bound roles:", " passing, ", "[check] ", "  ✗ "] do
      IO.println l
    let exited := checked.exitCode == 0 || checked.exitCode == 3
    unless exited do IO.eprintln (tail checked)
    let admitted := admission both
    let counts := passedCount checked.stdout
    if exited && counts != some (expected.rustPassed, expected.rustChecked) then
      IO.eprintln s!"[initstd] the Rust kernel's count on the artifact differs from \
        {referencePath}. If the change is meant to move it, record it there."
    reportChecks "initstd-reference" #[
      ("ix compile-lean on Init+Std passes its report checks and matches the Rust compiler \
        byte for byte", aligned),
      (s!"the artifact's SHA-256 is the reference's ({expected.sha256})", sha == expected.sha256),
      (s!"the artifact's size is the reference's ({expected.bytes} bytes)", size == expected.bytes),
      ("ix check-rs --anon exits 0, or 3 for failed constants", exited),
      (s!"the Rust kernel admits all {roles} roles the default table binds and refuses no \
        role group", admitted == some (roles, 0)),
      (s!"the Rust kernel passes {expected.rustPassed} of {expected.rustChecked} constants, \
        as the reference says", counts == some (expected.rustPassed, expected.rustChecked))]
  finally
    IO.FS.removeDirAll dir

/-- The phase rows of a `validate-lean` report that did not pass, and the
number of rows; an error if the report does not parse or does not pass. -/
def fidelityRows (report : String) : Except String Nat := do
  let json ← Lean.Json.parse report
  let passed ← (← json.getObjVal? "passed").getBool?
  let totalFailures ← (← json.getObjVal? "totalFailures").getNat?
  let phases ← (← json.getObjVal? "phases").getArr?
  let notPassed := phases.filterMap fun ph =>
    match ph.getObjVal? "name", ph.getObjVal? "result" with
    | .ok (.str _), .ok (.str "pass") => none
    | .ok (.str name), .ok (.str r) => some s!"{name}: {r}"
    | _, _ => some "a malformed phase row"
  unless passed && totalFailures == 0 && notPassed.isEmpty do
    throw s!"{totalFailures} failure(s); phases not passed: {", ".intercalate notPassed.toList}"
  return phases.size

/-- `fidelity-initstd`. -/
def fidelity : IO UInt32 := do
  let dir ← IO.FS.createTempDir
  try
    let reportPath := dir / "validate-report.json"
    let out ← runIx #["validate-lean", source, "--report", reportPath.toString]
    for l in linesWith out.stdout ["[validate-lean]   ", "RESULT:"] do
      IO.println l
    let content ← try IO.FS.readFile reportPath catch _ => pure ""
    let verdict : Except String Nat :=
      if content.isEmpty then .error "no report written" else fidelityRows content
    match verdict with
    | .ok n => IO.println s!"[initstd] validate-lean: all {n} phases passed"
    | .error e => IO.eprintln s!"[initstd] validate-lean: {e}\n{tail out}"
    reportChecks "fidelity-initstd" #[
      ("ix validate-lean on Init+Std exits 0", out.exitCode == 0),
      ("its report has the five phases, every one passed",
        match verdict with | .ok n => n ≥ 5 | .error _ => false)]
  finally
    IO.FS.removeDirAll dir

end Tests.Ix.InitStd
