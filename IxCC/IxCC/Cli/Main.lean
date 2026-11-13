import IxCC.Cli

/-! The `ixcc` executable's root (`IxCC.Cli`).

**Why a second process appears.** The certified kernel and IxCC's own decoder
recurse on the native stack, as deep as the input nests, and the kernel's
limits fix how deep that is (`Ix.Kernel.Admission.Limits.stackFor`: 16 KiB per
level of the depth limit, at least 256 MiB). IxCC links no native code, so it
cannot size a thread itself; Lean's runtime sizes every thread, the main one
included, from `LEAN_STACK_SIZE_KB` at start. So for `compile` and `check-cert`
`ixcc` runs itself again, once, with `LEAN_STACK_SIZE_KB` set to that size,
unless it is already at least that, and waits: Lean has no `exec`, so the first
process stays until the second ends and exits with its status (death by signal
`n` as `128 + n`, as Lean's `wait` reports it). The second process has the same
arguments, standard input, output and error, and environment, plus
`LEAN_STACK_SIZE_KB`, `LEAN_NUM_THREADS` (the `--workers` setting, only if the
variable is unset) and `IXCC_REEXECED=1`, which stops it from running itself
again. `IXCC_REEXEC=0` turns this off, for a caller that sizes the stack
itself. Before starting it the first process runs the address-space check
(`Ix.Kernel.Host.spaceCheck`, against `ulimit -v`): exit 2 when the second
process certainly cannot fit (one stack, or `--workers` stacks, over the
limit), a warning line when it may not, and exit 2 if it cannot start the
second process. `LEAN_NUM_THREADS` sizes the runtime's pool, which the check
counts; the first process sets it to the `--workers` setting when it is unset,
so that a run under a cap can be bounded by `--workers` alone.

Signals: a terminal's interrupt reaches both processes (they share the process
group); a signal sent to the first process alone does not reach the second,
which checks every half second that its parent is still the process that
started it and stops (exit 1) when it is not. That check is a task that never
ends, and Lean's runtime waits for every task before a process ends, so the
second process ends by `IO.Process.exit` with `main`'s status. -/

namespace IxCC.Cli.Process

/-- The parent process id, from `/proc/self/stat` (`none` if it cannot be read). -/
def parentPid : IO (Option Nat) := do
  let text ← match ← (IO.FS.readFile "/proc/self/stat").toBaseIO with
    | .ok t => pure t
    | .error _ => return none
  -- `pid (comm) state ppid …`; the command name may hold spaces and parentheses
  let some rest := (text.splitOn ")").getLast? | return none
  let fields := (rest.splitOn " ").filter (· ≠ "")
  return fields[1]?.bind String.toNat?

/-- In the second process: stop when the process that started it is gone. -/
def watchParent : IO Unit := do
  let some started ← parentPid | return
  let _ ← IO.asTask (prio := .dedicated) do
    while true do
      IO.sleep 500
      if (← parentPid) != some started then
        -- standard error may be a pipe nobody reads any more: a failed write must not end
        -- this task before the exit (it did: the process then stayed)
        try IO.eprintln "ixcc: the process that started this one ended; stopping" catch _ => pure ()
        IO.Process.exit 1
  return

/-- `ixcc`: for `compile` and `check-cert`, run again on the stack the kernel's limits
need (the module's comment), else `IxCC.Cli.main` here. -/
def run (args : List String) : IO UInt32 := do
  if (← IO.getEnv "IXCC_REEXECED").isSome then
    watchParent
    -- The watcher never ends, and Lean's runtime waits for every task before the process
    -- ends, so the second process leaves by `IO.Process.exit` once `main` is done (with an
    -- uncaught error reported as the runtime reports it, exit 1); returning would hang.
    let code ← try IxCC.Cli.main args catch e => do
      IO.eprintln s!"uncaught exception: {e}"; pure 1
    IO.Process.exit code.toUInt8
  let some o := (IxCC.Cli.parse args).toOption | IxCC.Cli.main args
  unless o.command == "compile" || o.command == "check-cert" do return ← IxCC.Cli.main args
  if (← IO.getEnv "IXCC_REEXEC") == some "0" then return ← IxCC.Cli.main args
  -- a malformed setting is reported by `main`, in this process
  let .ok settings ← IxCC.Cli.settingsOf o | IxCC.Cli.main args
  let kb := Ix.Kernel.Host.stackKiB settings.limits
  let given := (← IO.getEnv "LEAN_STACK_SIZE_KB").bind (·.trimAscii.toString.toNat?)
  if given.any (kb ≤ ·) then return ← IxCC.Cli.main args
  -- the second process's pool: `--workers` when `LEAN_NUM_THREADS` is unset (it is given to it)
  let threadsUnset := (← IO.getEnv "LEAN_NUM_THREADS").isNone
  let pool ← match settings.limits.workers with
    | some w => if threadsUnset then pure w else Ix.Kernel.Host.poolSize
    | none => Ix.Kernel.Host.poolSize
  let D := Ix.Kernel.Host.Setting.maxDepth.var
  let W := Ix.Kernel.Host.Setting.workers.var
  match ← Ix.Kernel.Host.spaceCheck settings.limits.stackFor settings.limits.workers pool
      s!"--workers or {W}, or --max-depth or {D} (the stack is 16 KiB per level, at least 256 MiB)"
      s!"--workers or {W}, or --max-depth or {D}" with
  | .refuse why => IO.eprintln s!"ixcc: {why}"; return 2
  | .warn line => IO.eprintln s!"ixcc: {line}"
  | .fits => pure ()
  let fail (why : String) : IO UInt32 := do
    IO.eprintln s!"ixcc: cannot re-run itself on a {kb} KiB stack ({why}); \
set LEAN_STACK_SIZE_KB={kb} (and IXCC_REEXEC=0) and run again"
    return 2
  let app ← match ← IO.appPath.toBaseIO with
    | .ok p => pure p
    | .error e => return ← fail (toString e)
  let threadsVar : Array (String × Option String) :=
    match settings.limits.workers with
    | some w => if threadsUnset then #[("LEAN_NUM_THREADS", some (toString w))] else #[]
    | none => #[]
  let env := #[("LEAN_STACK_SIZE_KB", some (toString kb)), ("IXCC_REEXECED", some "1")] ++ threadsVar
  let spawn : IO.Process.SpawnArgs := {
    cmd := app.toString, args := args.toArray, env
    stdin := .inherit, stdout := .inherit, stderr := .inherit }
  match ← (IO.Process.spawn spawn).toBaseIO with
  | .error e => fail (toString e)
  | .ok child => child.wait

end IxCC.Cli.Process

def main (args : List String) : IO UInt32 := IxCC.Cli.Process.run args
