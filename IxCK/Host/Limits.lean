module

public import IxCK.Kernel.Admission.Tier

/-! # The kernel's limits as a host's settings

Every bound the certified entry applies to its input is a field of
`Ix.Kernel.Admission.Limits` (`docs/kernel.md`, "Limits"). A host that runs the
kernel on input it did not make reads each one as a setting: a command-line flag
first, then an environment variable `IX_KERNEL_<LIMIT>`, then the host's own
default (`resolve`). It prints the settings that are not at their defaults
before it runs the kernel (`header`), and when the kernel declines by a limit it
names the limit, its value, where the value came from and how to raise it
(`declineMessage`), and exits with `exitDeclined`.

This module is the hosts', not the kernel's: no `IxCK.Kernel` module imports
it, and nothing here is part of any entry. A limit only turns an answer into a
decline, so a setting cannot make the kernel accept what it would reject.

The exit codes of the hosts that run the kernel (`docs/kernel.md`, "Exit
codes"): 0 accepted, 1 an infrastructure failure, 2 a usage error, 3 rejected or
failed (including the fixed declines no setting raises), 4 and 5 `ix
check-lean`'s partial and conditional runs, 6 declined by a limit
(`exitDeclined`); `kernel-check-ixe`'s watchdog exits 7 (`exitWatchdog`). -/

@[expose] public section

namespace Ix.Kernel.Host

open Ix.Kernel.Admission

/-- Declined by a limit a setting raises. -/
def exitDeclined : UInt32 := 6

/-- `kernel-check-ixe`'s watchdog: a check ran past its time or the process past
its memory. -/
def exitWatchdog : UInt32 := 7

/-- The settings, one per field of `Limits`. -/
inductive Setting where
  | maxRecords
  | maxBlobs
  | maxTotalBytes
  | maxRecordBytes
  | maxRecordUnivNodes
  | maxDepth
  | workers
  deriving Repr, DecidableEq, Inhabited

namespace Setting

def all : List Setting :=
  [.maxRecords, .maxBlobs, .maxTotalBytes, .maxRecordBytes, .maxRecordUnivNodes, .maxDepth, .workers]

/-- The flag, without its leading `--`. -/
def flag : Setting → String
  | .maxRecords => "max-records"
  | .maxBlobs => "max-blobs"
  | .maxTotalBytes => "max-total-bytes"
  | .maxRecordBytes => "max-record-bytes"
  | .maxRecordUnivNodes => "max-record-univ-nodes"
  | .maxDepth => "max-depth"
  | .workers => "workers"

/-- The environment variable. -/
def var : Setting → String
  | .maxRecords => "IX_KERNEL_MAX_RECORDS"
  | .maxBlobs => "IX_KERNEL_MAX_BLOBS"
  | .maxTotalBytes => "IX_KERNEL_MAX_TOTAL_BYTES"
  | .maxRecordBytes => "IX_KERNEL_MAX_RECORD_BYTES"
  | .maxRecordUnivNodes => "IX_KERNEL_MAX_RECORD_UNIV_NODES"
  | .maxDepth => "IX_KERNEL_MAX_DEPTH"
  | .workers => "IX_KERNEL_WORKERS"

/-- What the limit bounds, for a decline: "declined by the `word` limit". -/
def word : Setting → String
  | .maxRecords => "record count"
  | .maxBlobs => "blob count"
  | .maxTotalBytes => "total bytes"
  | .maxRecordBytes => "record bytes"
  | .maxRecordUnivNodes => "universe nodes per record"
  | .maxDepth => "depth"
  | .workers => "workers"

/-- The setting a resource's decline names. -/
def ofResource : Resource → Setting
  | .records => .maxRecords
  | .blobs => .maxBlobs
  | .totalBytes => .maxTotalBytes
  | .recordBytes => .maxRecordBytes
  | .recordUnivNodes => .maxRecordUnivNodes
  | .depth => .maxDepth

/-- The setting's value in `l` (`workers`: `none` when unbounded). -/
def get (l : Limits) : Setting → Option Nat
  | .maxRecords => some l.maxRecords
  | .maxBlobs => some l.maxBlobs
  | .maxTotalBytes => some l.maxTotalBytes
  | .maxRecordBytes => some l.maxRecordBytes
  | .maxRecordUnivNodes => some l.maxRecordUnivNodes
  | .maxDepth => some l.maxDepth
  | .workers => l.workers

def set (l : Limits) (n : Nat) : Setting → Limits
  | .maxRecords => { l with maxRecords := n }
  | .maxBlobs => { l with maxBlobs := n }
  | .maxTotalBytes => { l with maxTotalBytes := n }
  | .maxRecordBytes => { l with maxRecordBytes := n }
  | .maxRecordUnivNodes => { l with maxRecordUnivNodes := n }
  | .maxDepth => { l with maxDepth := n }
  | .workers => { l with workers := some n }

end Setting

/-- Where a setting's value came from. -/
inductive Source where
  | default
  | flag
  | var
  deriving Repr, DecidableEq, Inhabited

/-- The limits a host runs the kernel under, with the source of every setting
that is not the host's default. -/
structure Resolved where
  limits : Limits
  sources : List (Setting × Source) := []

def Resolved.source (r : Resolved) (s : Setting) : Source :=
  ((r.sources.find? (·.1 == s)).map (·.2)).getD .default

/-- How a source is named in the header and in a decline. -/
def Source.render (s : Setting) : Source → String
  | .default => "default"
  | .flag => s!"--{s.flag}"
  | .var => s.var

/-- A setting's value as text: a positive whole number in decimal. `0` is not
a value of any setting: as a limit it declines every input, and as `workers`
it would run phase B on the calling thread, which no host offers. -/
def parseValue (text : String) : Option Nat :=
  match text.trimAscii.toString.toNat? with
  | some n => if n == 0 then none else some n
  | none => none

/-- **The settings**: for each limit, its flag if given (`flag`), else its
variable if set (`env`), else the host's default (`defaults`). A value that is
not a positive whole number is an error naming the flag or the variable, which
a host reports as a usage error (exit 2). -/
def resolve (defaults : Limits) (flag : Setting → Option String) (env : Setting → Option String) :
    Except String Resolved := do
  let mut limits := defaults
  let mut sources : List (Setting × Source) := []
  for s in Setting.all do
    let given : Option (Source × String) := match flag s, env s with
      | some v, _ => some (.flag, v)
      | none, some v => some (.var, v)
      | none, none => none
    if let some (src, text) := given then
      let some n := parseValue text
        | throw s!"{Source.render s src} takes a positive whole number, not '{text}'"
      limits := s.set limits n
      sources := sources ++ [(s, src)]
  return { limits, sources }

/-- `resolve` with the variables read from the environment. -/
def resolveIO (defaults : Limits) (flag : Setting → Option String) : IO (Except String Resolved) := do
  let mut vars : List (Setting × String) := []
  for s in Setting.all do
    if let some v ← IO.getEnv s.var then vars := (s, v) :: vars
  return resolve defaults flag fun s => (vars.find? (·.1 == s)).map (·.2)

/-- The line a host prints before it runs the kernel: every setting given by a
flag or a variable, with its value and source; `none` when there is none. -/
def header (r : Resolved) : Option String :=
  if r.sources.isEmpty then none else
  let parts := r.sources.map fun (s, src) =>
    s!"{s.flag} {(s.get r.limits).map toString |>.getD "unbounded"} ({Source.render s src})"
  some s!"kernel limits: {", ".intercalate parts}"

/-- **A decline by a limit, as every host prints it**: the limit, its value and
source, and how to raise it. -/
def declineMessage (r : Resolved) (res : Resource) : String :=
  let s := Setting.ofResource res
  let value := (s.get r.limits).map toString |>.getD "unbounded"
  s!"declined by the {s.word} limit ({value}, {Source.render s (r.source s)}); \
raise it with --{s.flag} N or {s.var}=N"

/-- The limit a byte-stage failure is a decline by, if it is one. -/
def limitOfBytes : ByteError → Option Resource
  | .limit r => some r
  | _ => none

/-- The limit an entry's failure is a decline by, if it is one. The fuels of
the reference core and the knot are not settings: their exhaustion is a fixed
decline (`none` here; exit 3). -/
def limitOfError : Error → Option Resource
  | .limit r => some r
  | _ => none

def limitOfTier : TierError → Option Resource
  | .entry e => limitOfError e
  | _ => none

/-- The limit a failure's text names, for a host whose kernel failures reach it as text: the
entry's own rendering of a decline (`Admission.Error`'s `limit: <resource>`). -/
def limitOfText (text : String) : Option Resource :=
  [Resource.records, Resource.blobs, Resource.totalBytes, Resource.recordBytes,
    Resource.recordUnivNodes, Resource.depth].find? fun r =>
    (text.splitOn s!"limit: {repr r}").length > 1

/-- The native stack, in KiB, a host gives the threads that run the kernel
(`Limits.stackFor`). -/
def stackKiB (l : Limits) : Nat := l.stackFor / 1024

/-- The soft "Max address space" of `/proc/self/limits`, in bytes; `none` when
it is `unlimited`, or the file is absent or unreadable. -/
def addressSpaceLimit : IO (Option Nat) := do
  let text ← match ← (IO.FS.readFile "/proc/self/limits").toBaseIO with
    | .ok t => pure t
    | .error _ => return none
  for line in text.splitOn "\n" do
    if line.startsWith "Max address space" then
      let fields := ((line.drop "Max address space".length).toString.splitOn " ").filter (· ≠ "")
      return fields.head?.bind String.toNat?
  return none

/-- What a thread reserves of the address space besides its stack: its malloc
arena's heap reservation (64 MiB on 64-bit glibc). -/
def threadReserve : Nat := 64 * 1024 * 1024

/-- The address space a host keeps for itself beyond its threads: the
executable, its libraries and the start of the heap. -/
def processReserve : Nat := 1024 * 1024 * 1024

/-- The runtime's task pool: `LEAN_NUM_THREADS`, else the processor count
(`nproc`), else 8. -/
def poolSize : IO Nat := do
  if let some n := (← IO.getEnv "LEAN_NUM_THREADS").bind (·.trimAscii.toString.toNat?) then
    return max 1 n
  match ← (IO.Process.output { cmd := "nproc" }).toBaseIO with
  | .ok out =>
    if out.exitCode != 0 then return 8
    return (out.stdout.trimAscii.toString.toNat?).map (max 1) |>.getD 8
  | .error _ => return 8

/-- **The threads a run may have, as estimated**: twice the runtime's pool
(it starts another worker when one blocks on a task) plus 8 (the main thread,
the run's own, the reporter, the runtime's I/O threads). An estimate, not a
bound: on a 64-processor machine `ix check-lean` ran 38-39 threads and
`kernel-check-ixe` 91-133 (`docs/kernel.md`, "Threads"). -/
def estimatedThreads (pool : Nat) : Nat := 2 * pool + 8

/-- The address-space check's answer. -/
inductive SpaceCheck where
  /-- no limit, or the estimate fits under it -/
  | fits
  /-- the run may fail to create a thread: a line the host prints before it runs -/
  | warn (line : String)
  /-- the run certainly cannot: a usage error (exit 2) -/
  | refuse (why : String)

/-- Bytes as whole MiB. -/
def mib (n : Nat) : Nat := n / (1024 * 1024)

/-- **The address-space check** of a host whose threads have `stack` bytes of
stack. The Lean runtime aborts the process when it cannot create a thread,
which no host can intercept, and the number of threads is the runtime's, so a
refusal is given only when failure is certain: one such stack, or (when the
caller gave `workers`) `workers` such stacks, exceed the soft address-space
limit (with none, a 64-bit process's 128 TiB, which a depth limit in the
billions overruns). Otherwise, when the estimate (`estimatedThreads` of the
pool (`pool`: the host's `poolSize`, or what it gives its child), each with its
stack and a 64 MiB malloc arena, plus 1 GiB for the
process) does not fit, a warning to print, naming `reduce`, the settings that
lower it in the host's words; `reduceCertain` names those for a refusal. -/
def spaceCheck (stack : Nat) (workers : Option Nat) (pool : Nat) (reduceCertain reduce : String) :
    IO SpaceCheck := do
  let limited ← addressSpaceLimit
  -- with no limit, the 128 TiB of a 64-bit process's user address space
  let cap := limited.getD (2 ^ 47)
  let capText := s!"the {mib cap} MiB this process may use (its `ulimit -v`, else the 128 TiB of \
a 64-bit address space)"
  if stack > cap then
    return .refuse s!"one thread stack of {stack / 1024} KiB exceeds {capText}; lower {reduceCertain}, \
or raise the limit"
  if let some w := workers then
    if w * stack > cap then
      return .refuse s!"{w} worker threads on {stack / 1024} KiB stacks need {mib (w * stack)} MiB, \
over {capText}; lower {reduceCertain}, or raise the limit"
  let some _ := limited | return .fits
  let n := estimatedThreads pool
  let need := n * (stack + threadReserve) + processReserve
  if need ≤ cap then return .fits
  return .warn s!"warning: this run may fail to create a thread under the address-space limit \
({mib cap} MiB), and the runtime then aborts it: about {n} threads (twice the runtime's pool of \
{pool}, plus 8) on {stack / 1024} KiB stacks need about {mib need} MiB; to lower it set \
LEAN_NUM_THREADS, then {reduce}"

/-- The stack the Lean runtime gives a thread when `LEAN_STACK_SIZE_KB` is unset
and the host did not resize its threads: 1 GiB (measured on Lean 4.34.1:
`kernel-check-ixe`'s thread stacks are mappings of 1,048,576 KiB, and of 8,320
KiB with `LEAN_STACK_SIZE_KB=8192`; `docs/kernel.md`, "Threads"). -/
def runtimeDefaultStack : Nat := 1024 * 1024 * 1024

/-- The stack of a host that does not resize its threads (`kernel-check-ixe`):
`LEAN_STACK_SIZE_KB`, else the runtime's default. -/
def callerStack : IO Nat := do
  return ((← IO.getEnv "LEAN_STACK_SIZE_KB").bind (·.trimAscii.toString.toNat?)).map (· * 1024)
    |>.getD runtimeDefaultStack

end Ix.Kernel.Host
