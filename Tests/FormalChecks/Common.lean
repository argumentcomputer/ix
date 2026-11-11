import Lean.Data.Json
import Ix.Address
import Ix.AiurInvocation

/-!
# Shared pieces of the formal-backend check drivers

The drivers (`formal-checks controller|cuda|ranges`, run by
`tools/ixvm/check-formal.sh`) drive the Rust hosts and the `ix` CLI on the
fixtures `check-formal.sh` leaves, log each command to a file in a fresh
directory beside the fixtures, and keep a JSON report there.
-/

namespace Tests.FormalChecks

open Lean System

/-- A check failed: the driver stops and exits nonzero. -/
def fail (message : String) : IO α := throw (IO.userError message)

/-- Command-line arguments: positionals, and `--flag value`, `--flag=value` or
a bare `--switch`. `switches` names the flags that take no value. -/
structure Args where
  positional : Array String := #[]
  flags : Array (String × String) := #[]

def Args.parse (switches : List String) : List String → Except String Args
  | [] => .ok {}
  | a :: rest =>
    if a.startsWith "--" then
      let body := (a.drop 2).toString
      match body.splitOn "=" with
      | key :: value :: more =>
        let value := "=".intercalate (value :: more)
        (Args.parse switches rest).map fun r => { r with flags := #[(key, value)] ++ r.flags }
      | _ =>
        if switches.contains body then
          (Args.parse switches rest).map fun r => { r with flags := #[(body, "")] ++ r.flags }
        else match rest with
          | value :: rest =>
            (Args.parse switches rest).map fun r => { r with flags := #[(body, value)] ++ r.flags }
          | [] => .error s!"argument --{body}: expected one argument"
    else (Args.parse switches rest).map fun r => { r with positional := #[a] ++ r.positional }

/-- The last value given for `--key`. -/
def Args.flag? (a : Args) (key : String) : Option String :=
  (a.flags.filter (·.1 == key)).back?.map (·.2)

def Args.has (a : Args) (key : String) : Bool := a.flags.any (·.1 == key)

/-- A usage error: printed with the usage line, exit code 2. -/
def usageError (usage message : String) : IO UInt32 := do
  IO.eprintln usage
  IO.eprintln s!"error: {message}"
  return 2

/-- The invocation of the accepted case labelled `label` in the Ixon case file
`cases` (`Ix.AiurInvocation`), as its bytes. -/
def caseInvocation (cases : FilePath) (label : String) : IO ByteArray := do
  let decoded ← IO.ofExcept (Ix.AiurInvocation.decodeCases (← IO.FS.readBinFile cases))
  let some c := decoded.find? fun c => c.accept && c.label == label
    | fail s!"{cases} has no accepted {label} case"
  return c.bytes

/-- `path` made absolute. -/
def absolute (path : FilePath) : IO FilePath := do
  if path.isAbsolute then return path
  return (← IO.currentDir) / path

/-- The SHA-256 of a file, in hexadecimal (`sha256sum`). -/
def sha256 (path : FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #["--", path.toString] }
  unless out.exitCode == 0 do fail s!"sha256sum {path}: {out.stderr}"
  return (out.stdout.splitOn " ").headD ""

/-- The checked-out revision. -/
def revision : IO String := do
  let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  unless out.exitCode == 0 do fail s!"git rev-parse HEAD: {out.stderr}"
  return out.stdout.trimAscii.toString

/-- A fresh directory `<parent>/<prefix>XXXXXXXX`. -/
partial def freshDir (parent : FilePath) (pre : String) : IO FilePath := do
  let stamp := (← IO.monoNanosNow) + 7919 * (← IO.Process.getPID).toNat
  let name := String.ofList (Nat.toDigits 16 (stamp % 16 ^ 8 + 16 ^ 8) |>.drop 1)
  let dir := parent / s!"{pre}{name}"
  try
    IO.FS.createDir dir
    return dir
  catch _ =>
    if ← dir.pathExists then freshDir parent pre else fail s!"cannot create {dir}"

/-- Monotonic seconds. -/
def seconds : IO Float := do
  return (← IO.monoNanosNow).toFloat / 1e9

/-- Spawn `command` with its standard output and error both written to `log`
(through `sh`, which `exec`s the command, so the child is the command). -/
def spawnLogged (command : Array String) (env : Array (String × Option String))
    (log : FilePath) : IO (IO.Process.Child {}) := do
  let some cmd := command[0]? | fail "empty command"
  IO.Process.spawn {
    cmd := "sh"
    args := #["-c", "log=$1; shift; exec \"$@\" >\"$log\" 2>&1", "sh", log.toString, cmd]
      ++ command.extract 1 command.size
    env }

/-- Wait for `child`, killing it and failing after `timeout` seconds. -/
partial def waitFor (child : IO.Process.Child {}) (timeout : Option Float) (what : String) :
    IO UInt32 := do
  let deadline := (← seconds) + timeout.getD 0
  let rec loop : IO UInt32 := do
    if let some code ← child.tryWait then return code
    if timeout.isSome && (← seconds) > deadline then
      child.kill
      let _ ← child.wait
      fail s!"{what} timed out after {timeout.getD 0} seconds"
    IO.sleep 20
    loop
  loop

/-- A JSON report kept in `dir/report.json`, rewritten after each change. -/
structure Report where
  dir : FilePath
  json : IO.Ref Json

def Report.new (dir : FilePath) (fields : List (String × Json)) : IO Report := do
  let ref ← IO.mkRef (Json.mkObj fields)
  return { dir := dir, json := ref }

def Report.save (r : Report) : IO Unit := do
  IO.FS.writeFile (r.dir / "report.json") ((← r.json.get).pretty ++ "\n")

def Report.get (r : Report) (key : String) : IO Json := do
  return (← r.json.get).getObjValD key

def Report.set (r : Report) (key : String) (value : Json) : IO Unit :=
  r.json.modify (·.setObjVal! key value)

/-- Append `value` to the array at `key`. -/
def Report.push (r : Report) (key : String) (value : Json) : IO Unit := do
  let items := ((← r.get key).getArr?).toOption.getD #[]
  r.set key (.arr (items.push value))

/-- The number of entries in the array at `key`. -/
def Report.count (r : Report) (key : String) : IO Nat := do
  return (((← r.get key).getArr?).toOption.getD #[]).size

/-- Two-digit, zero-padded. -/
def pad2 (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

def readJson (path : FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

/-- `j.k₁.k₂…` -/
def field (j : Json) (keys : List String) : IO Json :=
  keys.foldlM (init := j) fun j k => IO.ofExcept (j.getObjVal? k)

def natField (j : Json) (keys : List String) : IO Nat := do
  IO.ofExcept (← field j keys).getNat?

def boolField (j : Json) (keys : List String) : IO Bool := do
  IO.ofExcept (← field j keys).getBool?

/-- A JSON number from a float, as Python's `json` writes `time.monotonic()`
differences. -/
def floatJson (x : Float) : Json :=
  match JsonNumber.fromFloat? x with
  | .inr n => .num n
  | .inl _ => .null

end Tests.FormalChecks

/-! The Ixon invocation and case codecs (`Ix.AiurInvocation`) round-trip, and a
truncated case file is refused at every length. The Rust readers carry the
same checks (`aiur::artifact`); `check-formal.sh` runs files each side wrote
through the other. -/

private def sampleInvocation : Ix.AiurInvocation.Invocation :=
  { entry := "IxVM::verify_claim", args := #[0, 127, 128, 2 ^ 64 - 1],
    streams := #[{ channel := 2, key := #[1, 2], values := #[0, 255, 16512] },
      { channel := 7, key := #[], values := #[] }] }

#guard match sampleInvocation.encode >>= Ix.AiurInvocation.Invocation.decode with
  | .ok decoded => decoded == sampleInvocation
  | .error _ => false

#guard (({ sampleInvocation with args := #[2 ^ 64] } : Ix.AiurInvocation.Invocation).encode).toOption.isNone

#guard match sampleInvocation.encode with
  | .error _ => false
  | .ok bytes =>
    let file := Ix.AiurInvocation.encodeCases
      #[{ label := "case", accept := false, rejectsWith := some "why", invocation := bytes }]
    (match Ix.AiurInvocation.decodeCases file with
      | .ok #[c] => c.label == "case" && !c.accept && c.rejectsWith == some "why" &&
          c.exercises.isNone && c.bytes.data == bytes.data && c.invocation == sampleInvocation
      | _ => false) &&
    (List.range file.size).all fun n =>
      (Ix.AiurInvocation.decodeCases (file.extract 0 n)).toOption.isNone
