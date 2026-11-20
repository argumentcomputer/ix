import IxAIVerify.Sandbox
import IxAIVerify.Ixon
import IxAIVerify.Tools

/-!
# `ixai reward`: the reward harness on the real Ix checker

An agent supplies only proof text. Every submission gets a fresh job directory of its own, and
every step that reads the submission runs in bubblewrap (`IxAIVerify.Sandbox`), which shows the
worker only the toolchain, the bundle's built `IxAICore` and that directory; without `bwrap` the
harness refuses. The harness

1. parses the text with the toolchain that compiles it and refuses anything but exactly one term
   without denied syntax (`IxAIVerify.checkSubmission`, run as a script under that toolchain);
2. compiles it with only the job directory writable;
3. reads the compiled `.ixe` once and checks from its bytes that `IxAIReward.goal` is a safe theorem
   whose type is the constant at the target address the harness computed itself, from a file no
   submission touched (`IxAIVerify.Ixon.checkGoalType`), and that `IxAIReward.target` has that
   address;
4. runs Ix's strict checker on the goal with the job directory read-only, and requires the `.ixe`
   to be unchanged afterwards.

The statement is `IxAIReward.target`, an `abbrev` the harness writes.
-/

namespace IxAICli

open IxAI IxAIVerify

/- Closed subterms such as a reference training run would otherwise become module initializers,
run at every start of `ixai` whatever the command. -/
set_option compiler.extract_closed false

/-- A task: the harness writes the statement; an agent supplies only the proof text. -/
structure RewardTask where
  name : String
  statement : String

/-- Statements about formulas: the first two are valid, the third is not, so no honest proof of
it exists. -/
def rewardTasks : List RewardTask :=
  [⟨"identity", "Formula.valid (.imp (.atom 0) (.atom 0)) = true"⟩,
   ⟨"projection", "Formula.valid (.imp (.and (.atom 0) (.atom 1)) (.atom 1)) = true"⟩,
   ⟨"converse", "Formula.valid (.imp (.atom 0) (.atom 1)) = true"⟩]

/-- Candidate proofs, from an honest agent and from one trying every known shortcut. -/
def rewardCandidates : List (String × String) :=
  [("honest", "by decide"),
   ("sorry", "by sorry"),
   ("native", "by native_decide"),
   ("smuggled", "by exact cheat\naxiom cheat {p : Prop} : p")]

inductive RewardVerdict where
  | accepted
  /-- The proof does not elaborate or does not check. -/
  | illTyped
  /-- It checks only with axioms beyond the standard three, such as `sorryAx` or
  `Lean.ofReduceBool`. -/
  | policyViolation
  /-- Not exactly one term, or a term with denied syntax; never elaborated. -/
  | rejectedSubmission
  /-- The compiled goal is not a theorem of the target the harness fixed. -/
  | wrongTarget
  /-- Not evaluated: elaboration cannot be isolated here, or a harness tool failed. -/
  | refused
  deriving Repr, BEq

def rewardHeader : String := "import IxAICore\nopen IxAICore\n\nnamespace IxAIReward\n\n"

def targetSource (t : RewardTask) : String :=
  rewardHeader ++ s!"abbrev target : Prop := {t.statement}\n\nend IxAIReward\n"

def candidateSource (t : RewardTask) (proof : String) : String :=
  rewardHeader ++ s!"abbrev target : Prop := {t.statement}\n\ntheorem goal : target :=\n  {proof}\n\nend IxAIReward\n"

/-- The submission checker as a script for `lean --run`: `IxAIVerify/Submission.lean`, which
imports only Lean, and a `main`. -/
def checkerScript : String :=
  (include_str "../IxAIVerify/Submission.lean") ++
    "\ndef main (args : List String) : IO UInt32 := IxAIVerify.checkerMain args\n"

/-- The checkout of `ix/ixw`'s default (`ci`) profile: `IX_CI_CHECKOUT`, as for `ixw`. -/
def ciCheckout : IO System.FilePath := do
  return System.FilePath.mk ((← IO.getEnv "IX_CI_CHECKOUT").getD "/home/sam/repos/ix.ci-merge-tests")

/-- The `ix` binary of `ix/ixw`'s default (`ci`) profile; `IX_BIN` overrides it. -/
def defaultIxBin : IO System.FilePath := do
  return (← ciCheckout) / ".lake" / "build" / "bin" / "ix"

/-- The reward worker: the sandbox with everything it may read, `ixw`, and the Lean toolchain
`ixw` compiles with, which also parses the submissions. -/
structure RewardEnv where
  sb : Sandbox
  ixw : System.FilePath
  lean : System.FilePath
  bundle : System.FilePath

def RewardEnv.work (re : RewardEnv) : System.FilePath := re.bundle / "reward-work"

/-- The Lean toolchain `ixw` puts first on its `PATH` (its `IX_LEAN`, the caller's if set). -/
def ixwLean (ixw : System.FilePath) : IO (Except String System.FilePath) := do
  let query : IO.Process.SpawnArgs :=
    { cmd := ixw.toString, args := #["IX_LEAN"], env := #[("IX_BIN", some "printenv")] }
  let r ← try IO.Process.output query
    catch e => return .error s!"cannot run {ixw}: {e}"
  let l := r.stdout.trimAscii.toString
  if r.exitCode != 0 || l.isEmpty then return .error s!"{ixw} names no Lean toolchain"
  return .ok l

/-- Set up the reward worker for `bundle`. It may read: the toolchain's store closure, the `ix`
binary and its libraries, `ixw` and its artifacts, and the bundle's Lake files, its built
`IxAICore` and the sources they link to. Its environment is `PATH`, `IX_BIN` and `IX_LEAN`. -/
def RewardEnv.find? (bundle : System.FilePath) : IO (Except String RewardEnv) := do
  let bundle ← IO.FS.realPath bundle
  let ixw := IxAIVerify.projectDir / "ix" / "ixw"
  let ixBin ← IO.FS.realPath ((← IO.getEnv "IX_BIN").map System.FilePath.mk |>.getD (← defaultIxBin))
  let lean ← match ← ixwLean ixw with
    | .ok l => pure l
    | .error e => return .error e
  let closure ← match ← storeClosure lean with
    | .ok ps => pure ps
    | .error e => return .error e
  let ixDir := ixBin.parent.getD "/"
  let ixLib := (ixDir.parent.getD "/") / "lib"
  let candidates := [ixDir, ixLib, ixw, IxAIVerify.projectDir / "ix" / "artifacts"] ++
    (["lakefile.toml", "lake-manifest.json", "lean-toolchain", ".lake", "IxAICore.lean", "IxAICore"].map
      fun (n : String) => bundle / n)
  let present ← candidates.filterM (·.pathExists)
  let env := [("PATH", s!"{lean / "bin"}:/usr/bin:/bin"), ("IX_BIN", ixBin.toString),
    ("IX_LEAN", lean.toString)]
  match ← Sandbox.find? (closure ++ present) env with
  | .ok sb => return .ok { sb, ixw, lean, bundle }
  | .error e => return .error e

/-- Run `ixw args` in the sandbox: `job` writable, or read-only. -/
def RewardEnv.ixwIn (re : RewardEnv) (job : System.FilePath) (writable : Bool) (args : Array String) :
    IO IO.Process.Output :=
  if writable then re.sb.run [job] job re.ixw.toString args
  else { re.sb with readOnly := re.sb.readOnly ++ [job] }.run [] job re.ixw.toString args

/-- Compile `src` as `job/base.lean` in the sandbox; the `.ixe` path on success. -/
def compileIsolated (re : RewardEnv) (job : System.FilePath) (base src : String) :
    IO (Except String System.FilePath) := do
  let file := job / s!"{base}.lean"
  let out := job / s!"{base}.ixe"
  IO.FS.writeFile file src
  let r ← re.ixwIn job true #["compile", file.toString, "--local", "--no-build", "--out", out.toString]
  if r.exitCode != 0 || !(r.stdout.splitOn "Compiled").length > 1 || !(← out.pathExists) then
    return .error s!"does not elaborate ({lastChars (r.stderr ++ r.stdout) 400})"
  return .ok out

/-- The address of `name` in the job's `.ixe`, read with the job directory read-only. -/
def addressIn (re : RewardEnv) (job ixe : System.FilePath) (name : String) : IO (Option Digest) := do
  let r ← re.ixwIn job false #["addr-of", "--ixe", ixe.toString, name]
  if r.exitCode != 0 then return none
  return ((r.stdout.splitOn "\n").map (·.trimAscii.toString)).reverse.findSome? Digest.ofHex?

/-- The target's address, from a file only the harness writes, compiled in a directory of its
own before any submission is compiled. -/
def expectedTarget (re : RewardEnv) (t : RewardTask) : IO (Except String Digest) := do
  let job ← freshDir re.work s!"target_{t.name}"
  let r ← match ← compileIsolated re job "Target" (targetSource t) with
    | .error e => pure (.error s!"target does not compile: {e}")
    | .ok ixe =>
      match ← addressIn re job ixe "IxAIReward.target" with
      | some a => pure (.ok a)
      | none => pure (.error "target address not found")
  IO.FS.removeDirAll job
  return r

/-- Parse `job/proof.txt` with the compiling toolchain; `none` if it is exactly one term without
denied syntax. -/
def parseCheck (re : RewardEnv) (job : System.FilePath) : IO (Option (RewardVerdict × String)) := do
  IO.FS.writeFile (job / "Check.lean") checkerScript
  let r ← { re.sb with readOnly := re.sb.readOnly ++ [job] }.run [] job (re.lean / "bin" / "lean").toString
    #["--run", (job / "Check.lean").toString, (job / "proof.txt").toString]
  match r.exitCode with
  | 0 => return none
  | 1 => return some (.rejectedSubmission, r.stdout.trimAscii.toString)
  | c => return some (.refused, s!"the submission checker did not run (exit {c}): {lastChars (r.stderr ++ r.stdout) 300}")

/-- Judge one submission in its own fresh job directory, removed afterwards. `target` gives the
target's address; it is asked for only once the text has passed the parse check. -/
def rewardOne (re : RewardEnv) (t : RewardTask) (target : IO (Except String Digest))
    (agent proof : String) : IO (Except String (RewardVerdict × String)) := do
  let job ← freshDir re.work s!"Reward_{t.name}_{agent}"
  IO.FS.writeFile (job / "proof.txt") proof
  let verdict ← do
    if let some v ← parseCheck re job then pure (.ok v) else
    match ← target with
    | .error e => pure (.error e)
    | .ok target =>
      match ← compileIsolated re job "Candidate" (candidateSource t proof) with
      | .error e => pure (.ok (.illTyped, e))
      | .ok ixe => pure (.ok (← judgeCompiled re job ixe target))
  IO.FS.removeDirAll job
  return verdict
where
  judgeCompiled (re : RewardEnv) (job ixe : System.FilePath) (target : Digest) :
      IO (RewardVerdict × String) := do
    let bytes ← IO.FS.readBinFile ixe
    let digest := blake3 bytes
    let some a ← addressIn re job ixe "IxAIReward.target"
      | return (.wrongTarget, "no IxAIReward.target in the compiled environment")
    if a != target then return (.wrongTarget, s!"target address {a}, expected {target}")
    let some goal ← addressIn re job ixe "IxAIReward.goal"
      | return (.illTyped, "no IxAIReward.goal in the compiled environment")
    if let .error e := Ixon.checkGoalType bytes goal target then return (.wrongTarget, e)
    let check ← re.ixwIn job false #["check-lean", ixe.toString, "--consts", "IxAIReward.goal"]
    unless blake3 (← IO.FS.readBinFile ixe) == digest do
      return (.refused, "the compiled environment changed while it was checked")
    let out := check.stdout ++ check.stderr
    match check.exitCode with
    | 0 => return (.accepted, s!"checked; the goal {goal.short} states the target {target.short}; standard axioms only")
    | 3 =>
      let axiomLine := ((out.splitOn "\n").filter fun l =>
        (l.splitOn "axiom").length > 1 || (l.splitOn "declin").length > 1).headD "declined"
      return (.policyViolation, axiomLine.trimAscii.toString)
    | c => return (.illTyped, s!"check-lean exit {c}")

/-- A reason as one TSV field: line breaks and tabs become spaces. -/
def oneLine (s : String) : String := String.map (fun c => if c == '\n' || c == '\t' then ' ' else c) s

def verdictExit : RewardVerdict → UInt32
  | .accepted => 0
  | .refused => 3
  | _ => 1

/-- Judge one proof file for one task: the harness's path for a single agent submission. -/
def rewardSubmit (bundle : System.FilePath) (task : String) (proofFile : System.FilePath) : IO UInt32 := do
  let some t := rewardTasks.find? (·.name == task) | IO.eprintln s!"unknown task {task}"; return 2
  let proof ← IO.FS.readFile proofFile
  match ← RewardEnv.find? bundle with
  | .error e => IO.println s!"{t.name}\tsubmission\t{repr RewardVerdict.refused}\t{oneLine e}"; return 3
  | .ok re =>
    match ← rewardOne re t (expectedTarget re t) "submission" proof with
    | .error e => IO.eprintln e; return 2
    | .ok (v, why) =>
      IO.println s!"{t.name}\tsubmission\t{repr v}\t{oneLine why}"
      return verdictExit v

/-- Compile a whole Lean file in the sandbox, without the submission check: what isolation alone
contains. Exit 0 if it compiled, 1 if not. -/
def sandboxCompile (bundle : System.FilePath) (file : System.FilePath) : IO UInt32 := do
  match ← RewardEnv.find? bundle with
  | .error e => IO.println e; return 3
  | .ok re =>
    let job ← freshDir re.work "isolated"
    let r ← compileIsolated re job ((file.fileStem.getD "Isolated")) (← IO.FS.readFile file)
    IO.FS.removeDirAll job
    match r with
    | .ok _ => IO.println "compiled in the sandbox"; return 0
    | .error e => IO.println e; return 1

/-- Judge every candidate on every task; the verdicts go to `out`. -/
def reward (bundle out : System.FilePath) : IO UInt32 := do
  let re ← match ← RewardEnv.find? bundle with
    | .ok re => pure re
    | .error e => IO.eprintln e; return 3
  let mut rows : Array String := #[]
  for t in rewardTasks do
    let target ← match ← expectedTarget re t with
      | .ok a => pure a
      | .error e => IO.eprintln s!"{t.name}: {e}"; return 2
    for (agent, proof) in rewardCandidates do
      match ← rewardOne re t (pure (.ok target)) agent proof with
      | .error e => IO.eprintln s!"{t.name} {agent}: {e}"; return 2
      | .ok (v, why) =>
        let line := s!"{t.name}\t{agent}\t{repr v}\t{oneLine why}"
        IO.println line
        rows := rows.push line
  if let some dir := out.parent then IO.FS.createDirAll dir
  IO.FS.writeFile out ("\n".intercalate rows.toList ++ "\n")
  IO.println s!"wrote {out}"
  return 0

/-- Where `ixai reward` records its verdicts without `--out`: the project's Truth Mines record,
which `ixai bench` reads. -/
def rewardsDefault : System.FilePath := IxAIVerify.projectDir / ".truthmines" / "rewards.tsv"

end IxAICli
