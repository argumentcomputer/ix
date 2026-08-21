/-
  Typed RAM watchdog: run a subprocess tree under a hard cgroup memory
  cap. This is the in-process replacement for the retired
  `.github/scripts/watchdog.sh` — every lake exe is standalone, so the
  semantics live here as typed IO instead of a shell script the binaries
  must locate at runtime. Consumers: `ix bench run` (every measured
  tool) and `lake exe truthmines build` (the corpus workspace build and
  the `ix catalog` leg).

  Semantics (unchanged from the script, validated on ubuntu-latest and
  warp runners — see ix-cpu-info's cgroup-memcap.yml):

  * a systemd user scope with cgroup-v2 `MemoryMax=<ceiling>G` and
    `MemorySwapMax=0`: the kernel OOM-kills at the cap — SIGKILL, exit
    137 (`oomExitCode`) — with no sampler to race and nothing to sum;
    the cgroup charges the whole tree's resident memory, and cached
    allocator reservations don't count. Swap stays off so a breach
    kills the scope instead of thrashing the box.
  * `memory.oom.group=1`: on breach the kernel kills the WHOLE scope,
    not just its biggest process. Without it, Zisk's ASM service gets
    singled out and the surviving host converts the memory kill into a
    clean exit 1 — which an orchestrator must treat as a deterministic
    failure. The scope's cgroup is user-delegated, so the write needs no
    sudo; if it fails, the wrapper exits 2 rather than run with wrong
    kill semantics.
  * empty `OMPI_MCA_opal_signal`: Open MPI (linked into zisk-host via
    proofman) registers a stacktrace-printing handler on fatal signals;
    when the fault originates inside malloc, that handler allocates
    while the corrupted arena lock is held and wedges at flat memory
    forever — the cap never fires. An empty list skips handler
    registration so fatal signals keep their default disposition.
    Harmless for tools that don't link Open MPI.
  * a user systemd instance must exist: the best-effort linger call
    boots one on CI (passwordless sudo); it no-ops locally, where a
    desktop session already provides the user manager. `available`
    probes the whole path end to end.
-/
module

public import Lean

public section

namespace Ix.Watchdog

/-- The kernel's cgroup OOM kill is SIGKILL on the scope: exit 137. -/
def oomExitCode : UInt32 := 137

/-- Default RAM ceiling, one rule for every consumer: the machine's
    total RAM minus 15 GB (the ~123 GiB CI runner lands at ~108 — above
    Mathlib `ix compile`'s ~100 GB peak, the largest legitimate
    workload). The 15 GB stays outside the cap for the OS, runner
    agent, and page cache. -/
def defaultCeilingGb : IO Nat := do
  let s ← try IO.FS.readFile "/proc/meminfo" catch _ => pure ""
  let kb := (s.splitOn "\n").findSome? fun l =>
    if l.startsWith "MemTotal:" then
      ((l.splitOn " ").filter (· ≠ "") |>.drop 1).head?.bind (·.toNat?)
    else none
  return match kb with
    | some kb => max 8 (kb / (1024 * 1024) - 15)
    | none => 16

/-- The two-line cgroup shim that must run INSIDE the scope (it reads
    its own cgroup path): set whole-scope kill semantics, then exec the
    tool. Fail closed (exit 2) if the knob cannot be set. -/
private def oomGroupThenExec : String :=
  "echo 1 > \"/sys/fs/cgroup$(cut -d: -f3- /proc/self/cgroup)/memory.oom.group\" \
|| { echo \"watchdog: cannot set memory.oom.group\" >&2; exit 2; }; exec \"$@\""

/-- `IO.Process.output` that reports spawn failure as a nonzero exit
    instead of throwing (probing must not abort the caller). -/
private def commandOutput (cmd : String) (args : Array String) :
    IO IO.Process.Output := do
  try
    IO.Process.output { cmd, args }
  catch _ =>
    pure { exitCode := 1, stdout := "", stderr := "" }

/-- Best-effort user-manager bootstrap: enable linger on CI runners
    (passwordless sudo); silently a no-op wherever a session manager
    already runs or sudo is absent. -/
private def ensureUserManager : IO Unit := do
  let user ← match ← IO.getEnv "USER" with
    | some user => pure user
    | none =>
      let out ← commandOutput "id" #["-un"]
      pure out.stdout.trimAscii.toString
  if user.isEmpty then return
  let _ ← commandOutput "sudo" #["-n", "loginctl", "enable-linger", user]
  return

/-- Environment for the scope: the Open MPI signal-handler opt-out, and
    a default `XDG_RUNTIME_DIR` where the caller's environment lacks one
    (headless shells; `systemd-run --user` needs it to find the bus). -/
private def scopeEnv : IO (Array (String × Option String)) := do
  let mut env : Array (String × Option String) :=
    #[("OMPI_MCA_opal_signal", some "")]
  if (← IO.getEnv "XDG_RUNTIME_DIR").isNone then
    let out ← commandOutput "id" #["-u"]
    if out.exitCode == 0 then
      let uid := out.stdout.trimAscii.toString
      unless uid.isEmpty do
        env := env.push ("XDG_RUNTIME_DIR", some s!"/run/user/{uid}")
  return env

/-- Spawn `cmd args` (inheriting stdio) under a `ceilingGb` cgroup cap
    and wait: exit 137 (`oomExitCode`) means the kernel killed the whole
    scope at the ceiling. -/
def run (ceilingGb : Nat) (cmd : String) (args : Array String)
    (cwd : Option System.FilePath := none) : IO UInt32 := do
  ensureUserManager
  let child ← IO.Process.spawn {
    cmd := "systemd-run"
    args := #["--user", "--scope", "--quiet",
      "-p", s!"MemoryMax={ceilingGb}G", "-p", "MemorySwapMax=0",
      "bash", "-c", oomGroupThenExec, "watchdog", cmd] ++ args
    cwd
    env := ← scopeEnv }
  child.wait

/-- End-to-end availability probe: a trivial command must survive a
    scope with the oom.group shim. False on non-systemd platforms,
    missing user managers, or a cgroup layout the shim cannot write. -/
def available : IO Bool := do
  try
    return (← run 1 "true" #[]) == 0
  catch _ =>
    return false

end Ix.Watchdog
