import CompilatrixTests.Rt.Support

/-! Native runs under the runtime driver (`fixtures/x86/runtime_driver.c`,
04 §6; untrusted, pinned in the trust ledger).

An object from `Rt.lower` and `Backend.emit` is linked with the driver for
one root (`-DENTRY=cx_<root>`). The driver maps a region and a stack, calls
`cx_init` and the root per input line, and prints `status value ok`, then
its C decoder's observation (with `--type`/`--sig`), the root's time (with
`--time`) and, with `--dump`, the object area. `decodeCheck` reads the dump
back into an `X86.Memory` at the driver's own addresses and checks that
`Rt.readback` gives what the C decoder printed. -/

namespace CompilatrixTests.Rt.Native

open Compilatrix CompilatrixTests.Src
open System

structure Tools where
  cc : String := "cc"
  driver : FilePath := "fixtures/x86/runtime_driver.c"
  work : FilePath

/-- Link `object` with the driver, calling `entry`. -/
def link (t : Tools) (name : String) (object : ByteArray) (entry : String) : IO FilePath := do
  let obj := t.work / s!"{name}.o"
  IO.FS.writeBinFile obj object
  let exe := t.work / name
  let out ← IO.Process.output {
    cmd := t.cc
    args := #["-std=c11", "-O1", "-Wall", "-Wextra", "-Werror", "-Wl,--fatal-warnings", "-no-pie",
      s!"-DENTRY={entry}", t.driver.toString, obj.toString, "-o", exe.toString] }
  unless out.exitCode == 0 do throw (IO.userError s!"linking {name} failed:\n{out.stdout}{out.stderr}")
  pure exe

/-- The object area a run left: region base, first object, bump, bytes. -/
structure Dump where
  base : Word
  start : Word
  bump : Word
  bytes : Array UInt8
  deriving Inhabited

/-- One result line. -/
structure Line where
  status : Word
  value : Word
  ok : Bool
  obs : Option String := none
  ns : Option Nat := none
  dump : Option Dump := none
  deriving Inhabited

def hexByte (s : String) : Option UInt8 := do
  let d := fun (c : Char) =>
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  match s.toList with
  | [h, l] => pure (UInt8.ofNat (16 * (← d h) + (← d l)))
  | _ => none

def parseDump (fields : List String) : Option Dump := do
  match fields with
  | [b, s, e] | [b, s, e, _] =>
    let hex := (fields.drop 3).head?.getD ""
    let cs := hex.toList
    let bytes ← ((List.range (cs.length / 2)).mapM fun i => hexByte (String.ofList [cs[2 * i]!, cs[2 * i + 1]!]))
    pure { base := UInt64.ofNat (← b.toNat?), start := UInt64.ofNat (← s.toNat?)
           bump := UInt64.ofNat (← e.toNat?), bytes := bytes.toArray }
  | _ => none

/-- Parse the driver's output: result lines, each followed by its dump line
when there is one. -/
def parse (out : String) (typed timed : Bool) : Option (List Line) := do
  let rows := ((out.splitOn "\n").filter (!·.isEmpty)).map fun l => (l.splitOn " ").filter (!·.isEmpty)
  -- lines in reverse; a dump row attaches to the line before it
  let lines ← rows.foldlM (init := ([] : List Line)) fun acc row =>
    match row, acc with
    | "dump" :: fs, l :: ls => do pure ({ l with dump := some (← parseDump fs) } :: ls)
    | s :: v :: ok :: rest, _ => do
      let (obs, rest) := if typed then (rest.head?, rest.drop 1) else (none, rest)
      let ns := if timed then (rest.head?.bind String.toNat?) else none
      pure ({ status := UInt64.ofNat (← s.toNat?), value := UInt64.ofNat (← v.toNat?), ok := ok == "1"
              obs := obs.filter (· != "-"), ns } :: acc)
    | _, _ => none
  pure lines.reverse

structure Options where
  region : Nat := 1 <<< 24
  stack : Nat := 1 <<< 23
  ty : Option (Rt.Sig × Rt.FoTy) := none
  dump : Bool := false
  time : Bool := false

/-- Run the linked driver on input lines. -/
def run (exe : FilePath) (o : Options) (inputs : List (List Nat)) : IO (List Line) := do
  let args := #["--region", toString o.region, "--stack", toString o.stack] ++
    (match o.ty with
     | some (sig, ty) => #["--type", ty.encode, "--sig", sig.encode]
     | none => #[]) ++
    (if o.dump then #["--dump"] else #[]) ++ (if o.time then #["--time"] else #[])
  let child ← IO.Process.spawn { cmd := exe.toString, args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr (String.join (inputs.map fun xs => " ".intercalate (xs.map toString) ++ "\n"))
  stdin.flush
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  unless code == 0 do throw (IO.userError s!"{exe} exited {code}\n{err}")
  match parse out o.ty.isSome o.time with
  | some ls =>
    unless ls.length == inputs.length do throw (IO.userError s!"{exe}: {ls.length} results for {inputs.length} inputs\n{out}")
    pure ls
  | none => throw (IO.userError s!"{exe}: malformed output\n{out}")

/-- The dumped object area as a memory: readable where the region is. -/
def Dump.memory (d : Dump) (regionSize : Nat) : X86.Memory :=
  let bytes := d.bytes
  let start := d.start
  { bytes := fun a => if start ≤ a && a < start + UInt64.ofNat bytes.size then bytes[(a - start).toNat]! else 0
    readable := fun a => d.base ≤ a && a < d.base + UInt64.ofNat regionSize
    writable := fun _ => false }

/-- `Rt.readback` of a native result, from its dump. -/
def Line.readback (l : Line) (regionSize : Nat) (sig : Rt.Sig) (ty : Rt.FoTy) : Option Sem.Obs := do
  let d ← l.dump
  Rt.readback sig (regionSize / 8) (d.memory regionSize) ty l.value

end CompilatrixTests.Rt.Native
