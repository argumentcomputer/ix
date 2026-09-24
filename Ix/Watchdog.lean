/-
  Typed RAM watchdog: run a subprocess tree under a hard cgroup memory
  cap. This is the in-process replacement for the retired
  `.github/scripts/watchdog.sh` — every lake exe is standalone, so the
  semantics live here as typed IO instead of a shell script the binaries
  must locate at runtime. Consumers: `ix bench run` (every measured
  tool) and `lake exe truthmines build` (the corpus workspace build and
  the `ix catalog` leg).

  Semantics:

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
  * a user systemd instance must exist: reuse a reachable manager or
    bootstrap the effective UID's manager on CI (passwordless sudo).
    Wait for startup and report bootstrap errors. `available` probes
    the whole path end to end.
-/
module

public import Lean

public section

namespace Ix.Watchdog

/-- The kernel's cgroup OOM kill is SIGKILL on the scope: exit 137. -/
def oomExitCode : UInt32 := 137

/-- Default RAM ceiling: the machine's total RAM minus 15 GB,
    reserved for the OS, runner agent, and page cache. -/
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
private def commandOutput (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) :
    IO IO.Process.Output := do
  try
    IO.Process.output { cmd, args, env }
  catch e =>
    pure { exitCode := 1, stdout := "", stderr := toString e }

/-- Bootstrap the actual process user's manager, not the possibly inherited
    `$USER`. Starting the unit explicitly waits for readiness; enabling linger
    alone is not a readiness check. Scope execution still fails closed if this
    best-effort bootstrap cannot establish a working manager. -/
private def ensureUserManager (uid : Nat) : IO Unit := do
  for args in #[#["-n", "loginctl", "enable-linger", toString uid],
      #["-n", "systemctl", "start", s!"user@{uid}.service"]] do
    let out ← commandOutput "sudo" args
    if out.exitCode != 0 then
      IO.eprintln s!"watchdog: sudo {String.intercalate " " args.toList} failed \
(exit {out.exitCode}): {out.stderr.trimAscii}"

/-- Preserve a working session, but recover from missing/stale session
    environment on headless runners using the effective UID's runtime directory.
    Check connectivity before sudo so normal desktop runs need no bootstrap. -/
private def scopeEnv : IO (Array (String × Option String)) := do
  let base : Array (String × Option String) :=
    #[("OMPI_MCA_opal_signal", some "")]
  let out ← commandOutput "id" #["-u"]
  let some uid := out.stdout.trimAscii.toString.toNat? | return base
  if out.exitCode != 0 then return base
  let runtime := s!"/run/user/{uid}"
  let inherited := (← IO.getEnv "XDG_RUNTIME_DIR").getD runtime
  let session := base.push ("XDG_RUNTIME_DIR", some inherited)
  if (← commandOutput "systemctl" #["--user", "show-environment"] session).exitCode == 0 then
    return session
  let env := base ++ #[("XDG_RUNTIME_DIR", some runtime),
    ("DBUS_SESSION_BUS_ADDRESS", none)]
  if inherited != runtime then
    if (← commandOutput "systemctl" #["--user", "show-environment"] env).exitCode == 0 then
      return env
  ensureUserManager uid
  return env

/-- Process arguments for a command inside the memory-capped scope. Keeping
    this construction shared makes the inherited-stdio and captured-output
    entry points enforce exactly the same cgroup and environment semantics. -/
private def scopeArgs (ceilingGb : Nat) (cmd : String) (args : Array String)
    (cwd : Option System.FilePath)
    (env : Array (String × Option String)) : IO IO.Process.SpawnArgs := do
  return {
    cmd := "systemd-run"
    args := #["--user", "--scope", "--quiet",
      "-p", s!"MemoryMax={ceilingGb}G", "-p", "MemorySwapMax=0",
      "bash", "-c", oomGroupThenExec, "watchdog", cmd] ++ args
    cwd
    -- Process settings are applied left-to-right. The watchdog's safety
    -- settings come last so callers cannot accidentally override them.
    env := env ++ (← scopeEnv) }

/-- Spawn `cmd args` (inheriting stdio) under a `ceilingGb` cgroup cap
    and wait: exit 137 (`oomExitCode`) means the kernel killed the whole
    scope at the ceiling. -/
def run (ceilingGb : Nat) (cmd : String) (args : Array String)
    (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO UInt32 := do
  let child ← IO.Process.spawn (← scopeArgs ceilingGb cmd args cwd env)
  child.wait

/-- Captured-output counterpart of `run`. This is intended for bounded
    parallel orchestrators: each subprocess can retain an attribution-safe
    log instead of interleaving several inherited stderr streams. -/
def output (ceilingGb : Nat) (cmd : String) (args : Array String)
    (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  IO.Process.output (← scopeArgs ceilingGb cmd args cwd env)

/-- End-to-end availability probe: a trivial command must survive a
    scope with the oom.group shim. False on non-systemd platforms,
    missing user managers, or a cgroup layout the shim cannot write. -/
def available : IO Bool := do
  try
    return (← run 1 "true" #[]) == 0
  catch _ =>
    return false

end Ix.Watchdog
