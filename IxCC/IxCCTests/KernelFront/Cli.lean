import IxCCTests.Support.Envelope
import IxCK.Ixon.Codec

/-! # `ixcc` at the command line: the kernel's limits, the re-execution, signals

Through the built executable (`.lake/build/bin/ixcc`, which `tests-kernel-front` requires), on the
committed `fib` closure (`fixtures/ixon-v4/bench-k1`):

* each kernel limit lowered by its flag and by its variable declines (exit 6) with the message
  naming the limit, its value and source and how to raise it; raised, the object is the default's;
  a malformed value is a usage error (exit 2);
* the re-execution is invisible: a success, a decline, a refusal of IxCC's own and a usage error
  give the same exit status, standard output and standard error with it (the default) and without
  it (`IXCC_REEXEC=0` with `LEAN_STACK_SIZE_KB` set by hand), and the closure read from standard
  input through `/dev/stdin` gives the same object;
* the second process exists exactly when it should (a FIFO as the closure holds both processes
  while the test looks): one child with `IXCC_REEXECED=1` by default, none with `IXCC_REEXEC=0`;
* signals: the child killed (SIGKILL), the parent exits 137 (Lean's `wait` reports a death by
  signal `n` as `128 + n`); the parent terminated alone (SIGTERM), the child stops within 2 s; an
  interrupt to the process group (SIGINT) ends both;
* a record of IxCC's largest size (1 MiB) nested as deep as its bytes allow, added to the closure:
  with the re-execution, IxCC's own envelope check refuses it (exit 1: it nests past 2,560 levels,
  `IxCC.Ixon.V3.kernelDepthLimit`, which IxCC's decoder checks before the kernel sees the closure);
  without it, on an 8 MiB stack, IxCC's decoder overflows the stack (a death by signal), the
  reason the re-execution exists. -/

namespace IxCCTests.KernelFront.Cli

open System

def ixccPath : FilePath := ".lake/build/bin/ixcc"
def fx : FilePath := "fixtures/ixon-v4/bench-k1"

def check (cond : Bool) (what : String) : IO Unit :=
  unless cond do throw (IO.userError s!"ixcc CLI: {what}")

def has (out : IO.Process.Output) (needle : String) : Bool :=
  (out.stderr.splitOn needle).length > 1 || (out.stdout.splitOn needle).length > 1

def run (args : Array String) (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  IO.Process.output { cmd := (← IO.FS.realPath ixccPath).toString, args, env }

def sh (script : String) (env : Array (String × Option String) := #[]) : IO IO.Process.Output :=
  IO.Process.output { cmd := "bash", args := #["-c", script], env }

/-- The variables that select the re-execution, cleared for the default run. -/
def plain : Array (String × Option String) :=
  #[("IXCC_REEXEC", none), ("IXCC_REEXECED", none), ("LEAN_STACK_SIZE_KB", none)]
/-- Without the re-execution, on the stack it would choose (256 MiB). -/
def direct : Array (String × Option String) :=
  #[("IXCC_REEXEC", some "0"), ("IXCC_REEXECED", none), ("LEAN_STACK_SIZE_KB", some "262144")]

/-- The children of a process: `/proc` lists a child under the thread that started it, which
for `ixcc` is not the main thread, so every thread's list is read. -/
def children (pid : Nat) : IO (List Nat) := do
  let threads ← match ← (System.FilePath.readDir s!"/proc/{pid}/task").toBaseIO with
    | .ok es => pure es | .error _ => return []
  let mut kids := []
  for t in threads do
    let text ← match ← (IO.FS.readFile (t.path / "children")).toBaseIO with
      | .ok t => pure t | .error _ => pure ""
    kids := kids ++ (text.splitOn " ").filterMap (·.trimAscii.toString.toNat?)
  return kids

/-- A process exists and has not ended (a zombie, not yet reaped by its new parent, counts as
ended). -/
def alive (pid : Nat) : IO Bool := do
  match ← (IO.FS.readFile s!"/proc/{pid}/stat").toBaseIO with
  | .error _ => return false
  | .ok text =>
    let some rest := (text.splitOn ")").getLast? | return false
    return ((rest.splitOn " ").filter (· ≠ "")).head? != some "Z"

def environHas (pid : Nat) (entry : String) : IO Bool := do
  match ← (IO.FS.readBinFile s!"/proc/{pid}/environ").toBaseIO with
  | .ok b => return ((String.fromUTF8! b).splitOn "\x00").contains entry
  | .error _ => return false

/-- A held run: `ixcc` started with its standard streams piped. -/
abbrev HeldChild := IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }

/-- A run held on a FIFO given as the closure, started in a session of its own
(`SpawnArgs.setsid`: the child's pid is the first `ixcc` process, the leader of a process group
of its own; the `setsid` command, used at first, forked here, so the pid read was not `ixcc`'s),
after its tree has settled. It is started through `env --default-signal=INT` (which execs
`ixcc` in place): a job started in the background by a non-interactive shell inherits SIGINT
ignored, and the interrupt case then hung the suite (KK-gates1). Recorded in `spawned`, which
the caller kills and reaps on every way out. -/
def held (spawned : IO.Ref (Array HeldChild)) (dir : FilePath) (env : Array (String × Option String)) :
    IO (HeldChild × FilePath) := do
  let fifo := dir / s!"hold-{← IO.monoNanosNow}"
  let made ← IO.Process.output { cmd := "mkfifo", args := #[fifo.toString] }
  check (made.exitCode == 0) "mkfifo"
  let app := (← IO.FS.realPath ixccPath).toString
  let child ← IO.Process.spawn {
    cmd := "env", stdin := .null, stdout := .piped, stderr := .piped, env, setsid := true
    args := #["--default-signal=INT", app, "compile", fifo.toString, "--equations",
      (fx / "fib.equations.json").toString,
      "-o", (dir / "held.o").toString] }
  spawned.modify (·.push child)
  IO.sleep 1500
  return (child, fifo)

/-- Wait for a held run at most `secs` seconds; past that, kill its process group and fail, so
that a run which outlives a signal fails the suite instead of hanging it. -/
def waitAtMost (child : HeldChild)
    (secs : Nat) : IO UInt32 := do
  for _ in [0:secs * 10] do
    if let some code ← child.tryWait then return code
    IO.sleep 100
  let _ ← sh s!"kill -KILL -{child.pid}"
  throw (IO.userError s!"a held run still running after {secs} s (its group killed)")

/-- Feed the FIFO (so a held run can finish), ignoring a reader that is gone. -/
def feed (fifo : FilePath) : IO Unit := do
  let _ ← sh s!"timeout 5 cp {fx / "fib.ixe"} {fifo} 2>/dev/null; true"

/-- A record of at most `size` bytes nested as deep as it fits: a definition whose value is
`var 0` applied to itself, `app (var 0) (app (var 0) (…))`. -/
def deepRecord (size : Nat) : ByteArray := Id.run do
  let nest (n : Nat) : _root_.Ixon.Expr := Id.run do
    let mut e : _root_.Ixon.Expr := .var 0
    for _ in [0:n] do e := .app (.var 0) e
    return e
  let mk (n : Nat) : ByteArray := _root_.Ixon.serConstant
    { info := .defn { kind := .defn, safety := .safe, lvls := 0, typ := .sort 0, value := nest n },
      sharing := #[], refs := #[], univs := #[] }
  let per := ((mk 1001).size - (mk 1).size) / 1000
  let mut n := size / max 1 per
  while (mk n).size > size do n := n - 1000
  return mk n

/-- The signals this process ignores (`SigIgn` of `/proc/self/status`, hexadecimal). A job
that a non-interactive shell starts in the background (`cmd &`: `run.sh`'s jobs, the `suites`
check's `launch`) inherits SIGINT and SIGQUIT ignored, and an exec keeps that. -/
def sigIgn : IO String := do
  let text ← match ← (IO.FS.readFile "/proc/self/status").toBaseIO with
    | .ok t => pure t | .error _ => return "unknown"
  let some line := (text.splitOn "\n").find? (·.startsWith "SigIgn:") | return "unknown"
  return (line.drop "SigIgn:".length).toString.trimAscii.toString

/-- Whether `/proc` lists a thread's children here (`CONFIG_PROC_CHILDREN`). -/
def childrenListed : IO Bool := do
  let pid ← IO.Process.getPID
  System.FilePath.pathExists s!"/proc/{pid}/task/{pid}/children"

/-- Kill a held run's process group and reap it, within 2 s (a run already reaped is left). -/
def reap (child : HeldChild) : IO Unit := do
  let _ ← sh s!"kill -KILL -{child.pid} 2>/dev/null; true"
  for _ in [0:20] do
    match ← (child.tryWait).toBaseIO with
    | .ok (some _) | .error _ => return
    | .ok none => IO.sleep 100

/-- **The held runs** (the second process, held on a FIFO given as the closure; signals). Every
wait is bounded (`waitAtMost`, 12 s; the FIFO fed within 5 s) and every run started is killed and
reaped on every way out (`finally`), so the part ends within about 90 s: five runs, each 1.5 s to
settle and at most 12 s of wait, two of them fed (at most 5 s each), 4 s of sleeps, at most 2 s
of reaping each. Returns the assertions and the skips: where `/proc` lists no children the part
is skipped by name (the plain gate still runs it). -/
def heldPart (dir : FilePath) : IO (Nat × Nat) := do
  IO.println s!"ixcc at the command line: held runs; signals this process ignores (SigIgn) {← sigIgn}"
  unless ← childrenListed do
    IO.println "SKIP: ixcc at the command line: held runs (no /proc children lists here)"
    return (0, 1)
  let t0 ← IO.monoMsNow
  let spawned ← IO.mkRef (#[] : Array HeldChild)
  let n ← IO.mkRef 0
  try
    for (env, expected) in [(plain, 1), (direct, 0)] do
      let (child, fifo) ← held spawned dir env
      let kids ← children child.pid.toNat
      check (kids.length == expected) s!"{kids.length} second processes, expected {expected}"
      if let some k := kids.head? then
        check (← environHas k "IXCC_REEXECED=1") "the second process lacks IXCC_REEXECED=1"
      feed fifo
      let code ← waitAtMost child 12
      check (code == 0) s!"held run: exit {code}"
      n.modify (· + 1)
    -- the second process killed: the first exits 128 + 9
    let (child, _) ← held spawned dir plain
    let some kid := (← children child.pid.toNat).head? | throw (IO.userError "no second process")
    let _ ← sh s!"kill -KILL {kid}"
    let code ← waitAtMost child 12
    check (code == 137) s!"the parent exited {code} when its child was killed, expected 137"
    n.modify (· + 1)
    -- the first process terminated: the second stops within 2.5 s
    let (child, _) ← held spawned dir plain
    let top := child.pid.toNat
    let some kid := (← children top).head? | throw (IO.userError "no second process")
    let _ ← sh s!"kill -TERM {top}"
    let _ ← waitAtMost child 12
    IO.sleep 2500
    check (!(← alive kid)) "the second process outlived its parent by 2.5 s"
    n.modify (· + 1)
    -- an interrupt to the group (both processes run with SIGINT at its default: `held`)
    let (child, _) ← held spawned dir plain
    let top := child.pid.toNat
    let some kid := (← children top).head? | throw (IO.userError "no second process")
    let _ ← sh s!"kill -INT -{top}"
    let code ← waitAtMost child 12
    IO.sleep 1500
    check (code == 130 && !(← alive kid))
      s!"an interrupt to the group: the parent exited {code}, the child alive {← alive kid}"
    n.modify (· + 1)
  finally
    for c in ← spawned.get do reap c
  -- the part's own duration, asserted under its worst case
  let ms := (← IO.monoMsNow) - t0
  IO.println s!"ixcc at the command line: held runs in {ms} ms (bound 90000)"
  check (ms < 90000) s!"the held runs took {ms} ms, over their 90 s bound"
  let k ← n.get
  return (k + 1, 0)

def suite (dir : FilePath) : IO (Nat × Nat) := do
  check (← ixccPath.pathExists) s!"{ixccPath} is not built"
  let eq := (fx / "fib.equations.json").toString
  let ixe := (fx / "fib.ixe").toString
  let compile (o : String) (flags : Array String := #[]) :=
    #["compile", ixe, "--equations", eq, "-o", (dir / o).toString] ++ flags
  let mut n := 0
  let base ← run (compile "base.o") plain
  check (base.exitCode == 0) s!"compile at the defaults: {base.exitCode}\n{base.stderr}"
  let object ← IO.FS.readBinFile (dir / "base.o")
  -- each limit, lowered by its flag and by its variable
  for (flag, var, word, v) in [("max-records", "IX_KERNEL_MAX_RECORDS", "record count", "1"),
      ("max-total-bytes", "IX_KERNEL_MAX_TOTAL_BYTES", "total bytes", "1"),
      ("max-record-bytes", "IX_KERNEL_MAX_RECORD_BYTES", "record bytes", "1"),
      ("max-depth", "IX_KERNEL_MAX_DEPTH", "depth", "2")] do
    let byFlag ← run (compile "x.o" #[s!"--{flag}", v]) plain
    check (byFlag.exitCode == 6 && has byFlag
      s!"declined by the {word} limit ({v}, --{flag}); raise it with --{flag} N or {var}=N")
      s!"--{flag} {v}: {byFlag.exitCode}\n{byFlag.stderr}"
    let byVar ← run (compile "x.o") (plain.push (var, some v))
    check (byVar.exitCode == 6 && has byVar s!"declined by the {word} limit ({v}, {var})")
      s!"{var}={v}: {byVar.exitCode}\n{byVar.stderr}"
    n := n + 2
  -- raised: the default's object
  for (flags, env) in [(#["--max-depth", "100000"], plain), (#[], plain.push ("IX_KERNEL_MAX_DEPTH", some "100000"))] do
    let r ← run (compile "raised.o" flags) env
    check (r.exitCode == 0 && has r "max-depth 100000") s!"raised {flags}: {r.exitCode}\n{r.stderr}"
    check ((← IO.FS.readBinFile (dir / "raised.o")) == object) "raised: a different object"
    n := n + 1
  -- malformed: usage errors
  for (flags, env) in [(#["--max-depth", "x"], plain), (#["--workers", "0"], plain),
      (#[], plain.push ("IX_KERNEL_MAX_DEPTH", some "0"))] do
    let r ← run (compile "x.o" flags) env
    check (r.exitCode == 2 && has r "takes a positive whole number") s!"malformed {flags}: {r.exitCode}"
    n := n + 1
  -- the re-execution is invisible: status, standard output and standard error
  for (label, args) in [("success", compile "same.o"), ("decline", compile "same.o" #["--max-depth", "2"]),
      ("refusal", compile "same.o" #["--root", "nosuch"]), ("usage", compile "same.o" #["--rc", "sideways"])] do
    let a ← run args plain
    let b ← run args direct
    check (a.exitCode == b.exitCode && a.stdout == b.stdout && a.stderr == b.stderr)
      s!"{label}: differs with and without the re-execution ({a.exitCode}/{b.exitCode})\n{a.stderr}\n{b.stderr}"
    n := n + 1
  let viaStdin ← sh s!"{← IO.FS.realPath ixccPath} compile /dev/stdin --equations {eq} -o {dir / "stdin.o"} < {ixe}" plain
  check (viaStdin.exitCode == 0) s!"the closure on standard input: {viaStdin.exitCode}\n{viaStdin.stderr}"
  check ((← IO.FS.readBinFile (dir / "stdin.o")) == object) "standard input: a different object"
  n := n + 1
  let (h, skips) ← heldPart dir
  n := n + h
  -- a record of 1 MiB nested as deep as it fits, added to the closure
  let env ← IO.ofExcept (IxCC.Ixon.V3.decodeAnonymousEnv (← IO.FS.readBinFile (fx / "fib.ixe")))
  let record := deepRecord (1024 * 1024)
  let deep := { env with consts := env.consts.insert (IxCC.Ixon.Address.blake3Pure record) record }
  let deepIxe := dir / "deep.ixe"
  IO.FS.writeBinFile deepIxe (IxCCTests.Support.Envelope.envelope deep (env.binding.map fun b => (b.address, b.bytes)))
  let deepArgs := #["compile", deepIxe.toString, "--equations", eq, "-o", (dir / "deep.o").toString]
  let a ← run deepArgs plain
  check (a.exitCode == 1 && has a "nests deeper than the kernel reads (2560")
    s!"the deep record with the re-execution: {a.exitCode}\n{a.stderr}"
  let b ← run deepArgs #[("IXCC_REEXEC", some "0"), ("IXCC_REEXECED", none), ("LEAN_STACK_SIZE_KB", some "8192")]
  check (b.exitCode > 128) s!"the deep record on 8 MiB without the re-execution: {b.exitCode}, expected a death by signal"
  n := n + 2
  return (n, skips)

end IxCCTests.KernelFront.Cli
