import Lean

/-! Shared IO for repository checks. Child processes receive argument arrays;
no check constructs a shell command. Temporary outputs are removed on failure. -/

namespace Ix.Compiler.Tools.Check

open Lean System

def need (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def checked (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def present (value : Option α) (message : String) : IO α :=
  match value with
  | some value => pure value
  | none => throw (IO.userError message)

def run (command : String) (args : Array String := #[]) : IO String := do
  let result ← IO.Process.output { cmd := command, args }
  need (result.exitCode == 0)
    s!"{command} exited {result.exitCode}\n{result.stdout}{result.stderr}"
  return result.stdout

def requireAll (output : String) (expected : List String) (label : String) : IO Unit := do
  for item in expected do
    need (output.contains item) s!"{label}: missing {repr item}\n{output}"

def words (value : String) : List String :=
  (value.splitToList Char.isWhitespace).filter (!·.isEmpty)

def hexDigit (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

def isHex (length : Nat) (value : String) : Bool :=
  value.length == length && value.toList.all (fun char =>
    char.isDigit || ('a' ≤ char && char ≤ 'f'))

def unhex (value : String) : Except String ByteArray := do
  let chars := (value.toList.filter (!·.isWhitespace)).toArray
  if chars.size % 2 != 0 then throw "hex input has odd length"
  let mut bytes := ByteArray.empty
  for index in [:chars.size / 2] do
    let some high := hexDigit chars[index * 2]! | throw "invalid hex digit"
    let some low := hexDigit chars[index * 2 + 1]! | throw "invalid hex digit"
    bytes := bytes.push (UInt8.ofNat (16 * high + low))
  return bytes

def hexNat (value : Nat) : String := String.ofList (Nat.toDigits 16 value)

def containsBytes (bytes part : ByteArray) : Bool :=
  part.size ≤ bytes.size &&
    (List.range (bytes.size - part.size + 1)).any fun index =>
      bytes.extract index (index + part.size) == part

def readJson (path : FilePath) : IO Json := do
  checked (Json.parse (← IO.FS.readFile path))

def field (value : Json) (key : String) : IO Json := checked (value.getObjVal? key)
def string (value : Json) : IO String := checked value.getStr?
def array (value : Json) : IO (Array Json) := checked value.getArr?
def nat (value : Json) : IO Nat := checked value.getNat?
def strField (value : Json) (key : String) : IO String := do string (← field value key)
def arrField (value : Json) (key : String) : IO (Array Json) := do array (← field value key)

def pairs (value : Json) : IO (List (String × Json)) := do
  let object ← checked value.getObj?
  return object.toList

def option (args : List (String × String)) (name : String) (fallback : String) : String :=
  (args.find? (·.1 == name)).map (·.2) |>.getD fallback

def optional (args : List (String × String)) (name : String) : Option String :=
  (args.find? (·.1 == name)).map (·.2)

def parseArgs (allowed : List String) (args : List String)
    (repeatable : List String := []) : Except String (List (String × String)) := do
  let rec go (args : List String) (result : List (String × String)) := do
    match args with
    | [] => return result.reverse
    | name :: value :: rest =>
        if !allowed.contains name then throw s!"unknown option {name}"
        if !repeatable.contains name && result.any (·.1 == name) then
          throw s!"duplicate option {name}"
        go rest ((name, value) :: result)
    | [name] => throw s!"missing value for {name}"
  go args []

def cli (label : String) (action : IO Unit) : IO UInt32 := do
  try
    action
    return 0
  catch error =>
    IO.eprintln s!"{label}: {error}"
    return 1

def sha256 (path : FilePath) : IO String := do
  let output ← run "sha256sum" #["--", path.toString]
  let digest := (words output).headD ""
  need (isHex 64 digest) s!"invalid SHA-256 tool output for {path}"
  return digest

partial def files (root : FilePath) (skipHidden : Bool := false) : IO (List FilePath) := do
  let mut result := []
  for entry in ← root.readDir do
    if skipHidden && entry.fileName.startsWith "." then continue
    if ← entry.path.isDir then result := result ++ (← files entry.path skipHidden)
    else result := entry.path :: result
  return result.mergeSort (fun a b => a.toString ≤ b.toString)

end Ix.Compiler.Tools.Check
