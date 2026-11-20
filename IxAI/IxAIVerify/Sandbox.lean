/-!
# Isolated elaboration

Elaborating Lean runs code: `#eval`, macros, tactics and `initialize` execute while a file is
compiled, before any kernel check. Untrusted proof text is therefore only ever elaborated inside
bubblewrap, and the sandbox shows the worker only what elaboration needs:

* the system's `/usr` (and `/bin`, `/lib*`, `/sbin` where they exist), read-only, for the loader and
  the shell utilities a wrapper script uses;
* the paths the caller declares (`readOnly`): the toolchain's store paths, the binaries and the
  inputs of the job, each read-only at its own path;
* the directories it may write (`writable`): the job's own fresh directory, nothing else;
* a private `/tmp`, `/dev` and `/proc`, and no network, IPC, PID, UTS or user namespace shared.

Everything else on the host (home directories, other repositories, the project's records and Ix
store) does not exist inside. The worker's environment is exactly `env`: nothing is inherited
from the caller. Without `bwrap` the harness refuses to elaborate.
-/

namespace IxAIVerify

structure Sandbox where
  bwrap : System.FilePath
  /-- Host paths visible inside, read-only, each at its own path. -/
  readOnly : List System.FilePath := []
  /-- The worker's whole environment. -/
  env : List (String × String) := []
  /-- Seconds before the command is killed. -/
  timeout : Nat := 900

def findOnPath (exe : String) : IO (Option System.FilePath) := do
  let path := (← IO.getEnv "PATH").getD ""
  for d in path.splitOn ":" do
    if d.isEmpty then continue
    let p := System.FilePath.mk d / exe
    if ← p.pathExists then return some p
  return none

def refusalNoBwrap : String :=
  "refusing to elaborate untrusted proof text: bubblewrap (`bwrap`) is not on PATH, and elaboration runs the submission's code; install bubblewrap or run the harness where it is available"

def Sandbox.find? (readOnly : List System.FilePath) (env : List (String × String)) :
    IO (Except String Sandbox) := do
  match ← findOnPath "bwrap" with
  | some b => return .ok { bwrap := b, readOnly, env }
  | none => return .error refusalNoBwrap

/-- System directories bound read-only when the host has them. -/
def systemPaths : List String := ["/usr", "/bin", "/sbin", "/lib", "/lib32", "/lib64"]

def Sandbox.argv (sb : Sandbox) (writable : List System.FilePath) (cwd : System.FilePath)
    (cmd : String) (args : Array String) : Array String :=
  #[toString sb.timeout, sb.bwrap.toString, "--unshare-all", "--die-with-parent", "--new-session",
    "--clearenv"] ++
  (sb.env.toArray.flatMap fun (k, v) => #["--setenv", k, v]) ++
  #["--tmpfs", "/tmp", "--dev", "/dev", "--proc", "/proc"] ++
  (systemPaths.toArray.flatMap fun p => #["--ro-bind-try", p, p]) ++
  (sb.readOnly.toArray.flatMap fun p => #["--ro-bind", p.toString, p.toString]) ++
  (writable.toArray.flatMap fun p => #["--bind", p.toString, p.toString]) ++
  #["--chdir", cwd.toString, "--", cmd] ++ args

/-- Run `cmd args` in the sandbox with `writable` as the only writable directories. -/
def Sandbox.run (sb : Sandbox) (writable : List System.FilePath) (cwd : System.FilePath)
    (cmd : String) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "timeout", args := sb.argv writable cwd cmd args }

/-- The store paths a Nix store path needs at run time (its closure), or the path itself when it
is not in a Nix store. -/
def storeClosure (p : System.FilePath) : IO (Except String (List System.FilePath)) := do
  let p ← IO.FS.realPath p
  unless p.toString.startsWith "/nix/store/" do return .ok [p]
  let r ← try IO.Process.output { cmd := "nix-store", args := #["-qR", p.toString] }
    catch e => return .error s!"cannot list the closure of {p}: {e}"
  if r.exitCode != 0 then return .error s!"cannot list the closure of {p}: {r.stderr.trimAscii}"
  return .ok ((r.stdout.splitOn "\n").filter (· ≠ "") |>.map System.FilePath.mk)

/-- A fresh directory below `parent` that no other run uses: the name carries the time and the
process, and creation fails rather than reuse an existing directory. -/
partial def freshDir (parent : System.FilePath) (stem : String) : IO System.FilePath := do
  IO.FS.createDirAll parent
  let dir := parent / s!"{stem}-{← IO.monoNanosNow}-{← IO.Process.getPID}"
  try
    IO.FS.createDir dir
    return dir
  catch e =>
    if ← dir.pathExists then freshDir parent stem else throw e

end IxAIVerify
