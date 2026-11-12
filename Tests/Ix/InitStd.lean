import Lean.Data.Json
import LSpec
import IxCK.Kernel.Ixon.Prelude
import Ix.FileDigest

/-! # Init+Std through the `ix` binary (merge queue tier `ci:landing-initstd-cli`)

* `initstd-reference`: `ix compile-lean Benchmarks/Compile/CompileInitStd.lean`,
  the certified compile of Init+Std, which refuses the compile
  on any failed report check, with the default role binding. The artifact's
  Blake3 digest and size must equal the reference in
  `Tests/Fixtures/initstd-reference.txt`. The kernel then checks the
  artifact (`ix check-lean --anon`), strict as every entry is by default: it
  must admit every role the default role table binds and refuse none, pass
  the reference's count of constants, and refuse exactly the reference's
  constants (`Lean.trustCompiler`, the one native-evaluation axiom it declines,
  and the four constants that depend on it), so the whole-artifact entry does
  not run and the check exits 3. A change that moves the compiler's bytes, or
  the kernel's verdicts on the artifact, updates that file in the same commit.
  (`--allow-user-axioms`, the uncertified conditional path, is covered on
  small fixtures by `RoleArtifactConsumer`: a second pass here would add
  almost three minutes.)
* `fidelity-initstd`: `ix validate-lean Benchmarks/Compile/CompileInitStd.lean
  --report`, gated on the report: every phase (the compile with its role
  binding, the serde gate, projection and block-order fidelity, the reader
  against the Lean source, decompilation) passed and none failed.
* `initstd-stack`: the record-by-record check (`kernel-check-ixe`, the step
  `ix check-lean` also runs) on the artifact `initstd-reference` keeps, with
  every thread's stack at 8 MiB (`LEAN_STACK_SIZE_KB`), gives the verdicts it
  gives on the runtime's default stack. Before the kernel's reduction loops,
  its index build and the host's record loop iterated, it aborted with a stack
  overflow on every stack up to 16 MiB (`docs/kernel.md`, "Native stack").

They run the `ix` binary (`.lake/build/bin/ix`, which `IxTests` builds) or
`kernel-check-ixe`, as a user would, in a subprocess. -/

namespace Tests.Ix.InitStd

def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

/-- The Init+Std driver, from the repository root. -/
def source : String := "Benchmarks/Compile/CompileInitStd.lean"

def referencePath : System.FilePath := "Tests" / "Fixtures" / "initstd-reference.txt"

/-- Where `initstd-reference` leaves a copy of its artifact, for the later
entries of its partition that read Init+Std (`admission-hash-diff-initstd`).
A run removes the previous copy first, and writes one only when the compile
passes. -/
def keptArtifact : System.FilePath := ".lake" / "build" / "initstd-reference.ixe"

/-- The reference artifact's digest and size, and the Lean kernel's strict
verdicts on it: the constants it passes and checks, and the ones it refuses. -/
structure Reference where
  blake3 : String
  bytes : Nat
  leanPassed : Nat
  leanChecked : Nat
  /-- `lean-kernel-refused` lines: the addresses strict checking refuses. -/
  refused : Array String

def isHex64 (s : String) : Bool :=
  s.length == 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The keys a reference file gives once. -/
def singleKeys : List String := ["blake3", "bytes", "lean-kernel-passed", "lean-kernel-checked"]

/-- The reference file: `#` comments, `key<TAB>value` lines, each key above
once, and `lean-kernel-refused<TAB>address[<TAB>name]` lines, each address
once, the name for the reader; no other key. The refused addresses are
exactly the constants not passed. -/
def parseReference (text : String) : Except String Reference := do
  let mut kv : Std.HashMap String String := {}
  let mut refused : Array String := #[]
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | k :: v :: rest =>
      if k == "lean-kernel-refused" then
        unless isHex64 v && rest.length ≤ 1 do
          throw s!"malformed line '{line}' (expected {k}<TAB><64 hex digits>[<TAB>name])"
        if refused.contains v then throw s!"{k} {v} given twice"
        refused := refused.push v
      else
        unless singleKeys.contains k do throw s!"unknown key '{k}'"
        unless rest.isEmpty do throw s!"malformed line '{line}' (expected key<TAB>value)"
        if kv.contains k then throw s!"key '{k}' given twice"
        kv := kv.insert k v
    | _ => throw s!"malformed line '{line}' (expected key<TAB>value)"
  let get (k : String) : Except String String :=
    match kv.get? k with
    | some v => .ok v
    | none => .error s!"no '{k}' line"
  let digest ← get "blake3"
  unless isHex64 digest do throw s!"blake3 '{digest}' is not 64 lowercase hex digits"
  let nat (k : String) : Except String Nat := do
    let v ← get k
    match v.toNat? with
    | some n => .ok n
    | none => .error s!"{k} '{v}' is not a number"
  let leanPassed ← nat "lean-kernel-passed"
  let leanChecked ← nat "lean-kernel-checked"
  unless leanPassed + refused.size == leanChecked do
    throw s!"{refused.size} lean-kernel-refused lines for {leanChecked - leanPassed} constants not passed"
  return { blake3 := digest, bytes := (← nat "bytes"), leanPassed, leanChecked, refused }

private def sample (digest : String) (more : String) : String :=
  s!"# c\nblake3\t{digest}\nbytes\t12\nlean-kernel-passed\t3\nlean-kernel-checked\t4\n\
    lean-kernel-refused\t{"".pushn 'b' 64}\tA.b\n{more}"

#guard (parseReference (sample ("".pushn 'a' 64) "")).toOption.map
  (fun r => (r.bytes, r.leanPassed, r.leanChecked, r.refused)) == some (12, 3, 4, #["".pushn 'b' 64])
#guard (parseReference (sample "ab" "")).toOption.isNone
#guard (parseReference (sample ("".pushn 'a' 64) "bytes\t1")).toOption.isNone
#guard (parseReference (sample ("".pushn 'a' 64) "size\t1")).toOption.isNone
#guard (parseReference ("blake3\t" ++ "".pushn 'a' 64 ++ "\nbytes\t1")).toOption.isNone
-- every constant not passed is listed, once, by its address
#guard (parseReference (sample ("".pushn 'a' 64) s!"lean-kernel-refused\t{"".pushn 'c' 64}")).toOption.isNone
#guard (parseReference (sample ("".pushn 'a' 64) s!"lean-kernel-refused\t{"".pushn 'b' 64}")).toOption.isNone
#guard (parseReference ((sample ("".pushn 'a' 64) "").replace "\tA.b" "")).toOption.isSome
#guard (parseReference ((sample ("".pushn 'a' 64) "").replace "\tA.b" "\tA.b\tC")).toOption.isNone

/-- The `bound roles: N admitted, M refused` line of `ix check-lean`: `(N, M)`. -/
def admission (out : String) : Option (Nat × Nat) := do
  let line ← (out.splitOn "\n").find? fun l => (l.splitOn "bound roles: ").length > 1
  let rest ← ((line.splitOn "bound roles: ")[1]?)
  let [admitted, refused] := rest.splitOn " admitted, " | none
  let refused ← (refused.splitOn " refused").head?
  return ((← admitted.trimAscii.toString.toNat?), (← refused.trimAscii.toString.toNat?))

/-- The `[check-lean] P/T subjects passed` line of `ix check-lean`: `(P, T)`. -/
def passedCount (out : String) : Option (Nat × Nat) := do
  let line ← (out.splitOn "\n").find? fun l =>
    l.startsWith "[check-lean] " && (l.splitOn " subjects passed").length > 1
  let rest ← ((line.splitOn "[check-lean] ")[1]?)
  let frac ← (rest.splitOn " subjects passed").head?
  let [p, t] := frac.splitOn "/" | none
  return ((← p.trimAscii.toString.toNat?), (← t.trimAscii.toString.toNat?))

#guard admission "x\n[check-lean] bound roles: 103 admitted, 0 refused\n" == some (103, 0)
#guard admission "[check-lean] bound roles: 57 admitted, 2 refused" == some (57, 2)
#guard admission "no binding" == none
#guard passedCount "[check-lean] 3/4 subjects passed (0 typed only), 4 checked/read records\n" ==
  some (3, 4)

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

def reportChecks (name : String) (checks : Array (String × Bool)) : IO UInt32 :=
  LSpec.lspecIO (.ofList [(name, checks.toList.map fun (label, ok) => LSpec.test label ok)]) []

/-- `initstd-reference`. -/
def reference : IO UInt32 := do
  let expected ← IO.ofExcept ((parseReference (← IO.FS.readFile referencePath)).mapError
    fun e => s!"{referencePath}: {e}")
  if ← keptArtifact.pathExists then IO.FS.removeFile keptArtifact
  let dir ← IO.FS.createTempDir
  try
    let artifact := dir / "initstd.ixe"
    let compiled ← runIx #["compile-lean", source, "--out", artifact.toString]
    for l in linesWith compiled.stdout ["] compile:", "post-steps", "wrote"] do
      IO.println l
    unless compiled.exitCode == 0 && (← artifact.pathExists) do
      IO.eprintln (tail compiled)
      return ← reportChecks "initstd-reference"
        #[("ix compile-lean on Init+Std passes its report checks", false)]
    IO.FS.createDirAll (keptArtifact.parent.getD ".")
    IO.FS.writeBinFile keptArtifact (← IO.FS.readBinFile artifact)
    let digest ← Ix.FileDigest.blake3File artifact
    let size := (← artifact.metadata).byteSize.toNat
    IO.println s!"[initstd] artifact blake3 {digest}, {size} bytes; reference {expected.blake3}, \
      {expected.bytes} bytes"
    unless digest == expected.blake3 && size == expected.bytes do
      IO.eprintln s!"[initstd] the Init+Std artifact differs from {referencePath}. If the change \
        is meant to move the compiler's bytes, record blake3 {digest} and bytes {size} there."
    -- the kernel on the artifact, under its role binding: strict, as every
    -- entry's default, it declines `Lean.trustCompiler` and blocks what depends
    -- on it, so the whole-artifact entry does not run and the run exits 3
    let roles := (← IO.ofExcept Ix.Kernel.Reader.defaultTable).bound.size
    let failOut := dir / "refused.txt"
    let checked ← runIx #["check-lean", artifact.toString, "--anon", "--fail-out", failOut.toString]
    let both := checked.stdout ++ "\n" ++ checked.stderr
    for l in linesWith both ["bound roles:", "subjects passed", "[check-lean]"] do
      IO.println l
    let exited := checked.exitCode == 3
    unless exited do IO.eprintln (tail checked)
    let refused := ((← try IO.FS.readFile failOut catch _ => pure "").splitOn "\n").toArray.filterMap
      fun l => let l := l.trimAscii.toString; if l.isEmpty || l.startsWith "#" then none else some l
    let sorted (xs : Array String) := xs.qsort (· < ·)
    let refusedOk := sorted refused == sorted expected.refused
    let admitted := admission both
    let counts := passedCount checked.stdout
    if exited && (counts != some (expected.leanPassed, expected.leanChecked) || !refusedOk) then
      IO.eprintln s!"[initstd] the kernel's verdicts on the artifact differ from {referencePath}: \
        refused {refused}. If the change is meant to move them, record them there."
    reportChecks "initstd-reference" #[
      ("ix compile-lean on Init+Std passes its report checks", compiled.exitCode == 0),
      (s!"the artifact's Blake3 digest is the reference's ({expected.blake3})", digest == expected.blake3),
      (s!"the artifact's size is the reference's ({expected.bytes} bytes)", size == expected.bytes),
      ("ix check-lean --anon exits 3: strict checking refuses constants", exited),
      (s!"the kernel admits all {roles} roles the default table binds and refuses none",
        admitted == some (roles, 0)),
      (s!"the kernel passes {expected.leanPassed} of {expected.leanChecked} constants, \
        as the reference says", counts == some (expected.leanPassed, expected.leanChecked)),
      (s!"the kernel refuses exactly the reference's {expected.refused.size} constants", refusedOk),
      ("it claims no whole-artifact acceptance and no host statement",
        !checked.stdout.contains "accepted all" && !checked.stdout.contains "host admission statement" &&
        !checked.stdout.contains "CONDITIONAL")]
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

def kernelCheckIxe : System.FilePath := ".lake" / "build" / "bin" / "kernel-check-ixe"

def pairsOf : List String → List (String × String)
  | a :: b :: t => (a, b) :: pairsOf t
  | _ => []

/-- The counts of `kernel-check-ixe`'s `check-ixe: done in … ms; [(OUTCOME, N), …]`
line, sorted by outcome (`none`: no such line). -/
def doneCounts (stderr : String) : Option (List (String × String)) := do
  let line ← (stderr.splitOn "\n").find? (·.startsWith "check-ixe: done in ")
  let rest ← (line.splitOn " ms; ")[1]?
  let clean := rest.foldl (fun acc c => if "[]()".contains c then acc else acc.push c) ""
  pure ((pairsOf (clean.splitOn ", ")).toArray.qsort (fun x y => x.1 < y.1)).toList

#guard doneCounts "x\ncheck-ixe: done in 5 ms; [(decline, 2), (accept, 9)]\ny" ==
  some [("accept", "9"), ("decline", "2")]

/-- `initstd-stack`: `kernel-check-ixe` on Init+Std with every thread's stack
at 8 MiB, and on the runtime's default, with the same counts. The artifact is
the one `initstd-reference` keeps, or `$IX_INITSTD_IXE`. -/
def stack : IO UInt32 := do
  let artifact := ((← IO.getEnv "IX_INITSTD_IXE").map System.FilePath.mk).getD keptArtifact
  unless ← artifact.pathExists do
    IO.eprintln s!"[initstd] {artifact} is missing: run initstd-reference first"
    return 1
  let dir ← IO.FS.createTempDir
  try
    let check (label : String) (stackKb : Option Nat) :
        IO (UInt32 × Option (List (String × String))) := do
      let t0 ← IO.monoMsNow
      -- no core file if it aborts
      let out ← IO.Process.output {
        cmd := "sh", args := #["-c", "ulimit -c 0; exec \"$0\" \"$@\"", kernelCheckIxe.toString,
          "--jobs", "4", artifact.toString, (dir / s!"{label}.jsonl").toString],
        env := #[("LEAN_STACK_SIZE_KB", stackKb.map toString)] }
      let counts := doneCounts out.stderr
      IO.println s!"[initstd] kernel-check-ixe, {label}: exit {out.exitCode} in \
        {(← IO.monoMsNow) - t0} ms; {(counts.map fun cs => cs.map fun (k, v) => s!"{k} {v}").getD ["no summary"]}\
        {if out.stderr.contains "Stack overflow" then "; STACK OVERFLOW" else ""}"
      return (out.exitCode, counts)
    let (rcDefault, countsDefault) ← check "default stack" none
    let (rc8, counts8) ← check "8 MiB stacks" (some 8192)
    reportChecks "initstd-stack" #[
      ("kernel-check-ixe on Init+Std exits 0 on the default stack", rcDefault == 0),
      ("kernel-check-ixe on Init+Std exits 0 with every thread at 8 MiB", rc8 == 0),
      ("with the same counts", countsDefault.isSome && counts8 == countsDefault)]
  finally
    IO.FS.removeDirAll dir

end Tests.Ix.InitStd
