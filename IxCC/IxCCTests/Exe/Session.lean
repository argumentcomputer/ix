import IxCCTests.Exe.TestShell

/-!
# A session with a test executable

The host side of the test shell's protocol (`IxCCTests.Exe.TestShell`): start
an executable the test shell runs, call its exports, read and write its
region, and end it. Each request is answered before the next is sent, so
neither side ever waits on a full pipe.
-/

namespace IxCCTests.Exe.Session

open System
open IxCCTests.Exe.TestShell

/-- The standard streams of a running test executable. -/
abbrev Stdio : IO.Process.StdioConfig := { stdin := .null, stdout := .piped, stderr := .piped }

/-- A running test executable. -/
structure Session where
  exe : FilePath
  stdin : IO.FS.Handle
  child : IO.Process.Child Stdio

/-- `ws` as little-endian 64-bit words. -/
def words (ws : List Nat) : ByteArray :=
  ⟨(ws.flatMap fun w => (List.range 8).map fun i => UInt8.ofNat (w / 256 ^ i)).toArray⟩

/-- The little-endian 64-bit word at byte `i` of `b` (zero past its end). -/
def word (b : ByteArray) (i : Nat) : UInt64 :=
  (List.range 8).foldl (fun w k => w ||| (((b[i + k]?).getD 0).toUInt64 <<< (8 * k).toUInt64)) 0

/-- What an exit status of the test shell means. -/
def meaning (code : UInt32) : String :=
  if code == 0 then "end of the session"
  else if code.toNat == exitInput then "standard input failed or ended inside a request"
  else if code.toNat == exitRequest then "an unknown request"
  else if code.toNat == exitExport then "an export index out of range"
  else if code.toNat == exitRange then "a range outside the region"
  else if code.toNat == exitWrite then "a write failed"
  else if code.toNat == exitConfine then "the confinement was refused"
  else if code == 124 then "timed out"
  else "killed or crashed"

/-- Start `exe`, under `timeout` when `seconds` is given. -/
def start (exe : FilePath) (seconds : Option Nat := none) : IO Session := do
  let (cmd, args) := match seconds with
    | some s => ("timeout", #["--kill-after=5", toString s, exe.toString])
    | none => (exe.toString, #[])
  let child ← IO.Process.spawn { cmd, args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  pure { exe, stdin, child }

/-- The process has ended where it should not have: report how. -/
def ended {α : Type} (s : Session) (what : String) : IO α := do
  let err ← s.child.stderr.readToEnd
  let code ← s.child.wait
  throw (IO.userError s!"{s.exe}: {what}: the test shell exited {code} ({meaning code}){if err.isEmpty then "" else s!"\n{err}"}")

/-- Read exactly `n` bytes of the answer. -/
def readExact (s : Session) (n : Nat) (what : String) : IO ByteArray := do
  let mut out := ByteArray.empty
  while out.size < n do
    let chunk ← s.child.stdout.read (n - out.size).toUSize
    if chunk.isEmpty then ended s what
    out := out ++ chunk
  return out

def send (s : Session) (bytes : ByteArray) : IO Unit := do
  s.stdin.write bytes
  s.stdin.flush

/-- Call export `k` with the six argument registers `regs` (zero beyond):
`rax`, `rdx`, and whether the callee-saved registers and `rsp` came back. -/
def call (s : Session) (k : Nat) (regs : List Nat) : IO (UInt64 × UInt64 × Bool) := do
  let regs := (regs ++ List.replicate 6 0).take 6
  send s (words ([1, k] ++ regs))
  let a ← readExact s 24 s!"call {k}"
  return (word a 0, word a 8, word a 16 == 1)

/-- The `n` bytes at `address`. -/
def read (s : Session) (address n : Nat) : IO ByteArray := do
  send s (words [2, address, n, 0, 0, 0, 0, 0])
  readExact s n s!"read {n} bytes at {address}"

/-- Write `bytes` at `address`. -/
def write (s : Session) (address : Nat) (bytes : ByteArray) : IO Unit :=
  send s (words [3, address, bytes.size, 0, 0, 0, 0, 0] ++ bytes)

/-- Write the word `w` at `address`. -/
def writeWord (s : Session) (address w : Nat) : IO Unit := write s address (words [w])

/-- The word at `address`. -/
def readWord (s : Session) (address : Nat) : IO UInt64 := do
  return word (← read s address 8) 0

/-- End the session: the shell must exit 0. -/
def finish (s : Session) : IO Unit := do
  send s (words [0, 0, 0, 0, 0, 0, 0, 0])
  let err ← s.child.stderr.readToEnd
  let code ← s.child.wait
  unless code == 0 do
    throw (IO.userError s!"{s.exe}: the test shell exited {code} ({meaning code}) at the end{if err.isEmpty then "" else s!"\n{err}"}")

/-- Run `body` in a session with `exe`, ending it afterwards. -/
def withSession {α : Type} (exe : FilePath) (body : Session → IO α) (seconds : Option Nat := none) : IO α := do
  let s ← start exe seconds
  let r ← body s
  finish s
  return r

end IxCCTests.Exe.Session
