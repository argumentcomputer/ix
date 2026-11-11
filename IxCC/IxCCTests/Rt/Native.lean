import IxCCTests.Rt.Support
import IxCCTests.Rt.Decoder
import IxCCTests.Exe.Session

/-! Native runs of compiled objects, as test executables IxCC writes itself
(`IxCCTests.Exe.TestShell`): no C compiler, C library or linker takes part.

`link` writes the object to the work directory, records it with its root's
export, and writes its test executable for the default stack and region;
`run` writes the test executable for the run's stack and region (calling
`cx_init` and the root) and runs input lines through it (`runShell`). Per line
it stores the stack budget (`stack - 4096`) at `region + 16`, calls
`cx_init(region, size, budget)` (an `init` line if that fails) and then the
root with the line's words (at most five, zero beyond, saturated at
`2^64 - 1`), and reads back the status, the value, whether the callee-saved
registers and `rsp` came back, the observation, the root call's time
(measured around its request, so it includes the pipe's round trip) and, with
`dump`, the object area `[start, bump)`. The region is not cleared between
lines.

**Two decoders.** With a result type, every result the root returns with
status 0 is decoded twice over the region from `region + 16` to the bump
pointer, with fuel `(limit - region) / 8`: by `Rt.readback`, and by the
independent decoder `IxCCTests.Rt.Decoder` from the type's and signature's
text forms. The two must agree (`runShell` throws otherwise); the line's
observation is the independent decoder's, as it was the C decoder's before
X1, and `Line.readback` reads the dump back with `Rt.readback`, so the suites
that compare both with an expected value compare two decoders with it.
`decoded` counts the results decoded both ways. -/

namespace IxCCTests.Rt.Native

open IxCC IxCCTests.Src
open System
open IxCCTests.Exe

structure Tools where
  work : FilePath

/-- What `link` recorded: the object, its root's export, and where to write
its test executables. -/
structure Program where
  object : ByteArray
  entry : String
  work : FilePath
  name : String

initialize programs : IO.Ref (List (String × Program)) ← IO.mkRef []
initialize decodedResults : IO.Ref Nat ← IO.mkRef 0
initialize nativeLines : IO.Ref Nat ← IO.mkRef 0

/-- The results decoded by both decoders so far in this process. -/
def decoded : IO Nat := decodedResults.get

/-- The suites' summary of their native runs: the lines run and the results
the two decoders decoded alike; empty when nothing ran natively. -/
def agreement : IO String := do
  let lines ← nativeLines.get
  let n ← decoded
  return if lines == 0 then "" else
    s!"; {lines} native lines run as test executables, {n} results decoded alike by Rt.readback and the independent decoder"

/-- The object area a run left: region base, first object, bump, bytes. -/
structure Dump where
  base : Word
  start : Word
  bump : Word
  bytes : Array UInt8
  deriving Inhabited, BEq, Repr

/-- One result line. -/
structure Line where
  status : Word
  value : Word
  ok : Bool
  obs : Option String := none
  ns : Option Nat := none
  dump : Option Dump := none
  /-- `cx_init` failed with `status`, so the root did not run. -/
  init : Bool := false
  deriving Inhabited, Repr

structure Options where
  region : Nat := 1 <<< 24
  stack : Nat := 1 <<< 23
  ty : Option (Rt.Sig × Rt.FoTy) := none
  dump : Bool := false
  time : Bool := false

/-- The test shell's memory for a run with `o`. -/
def memOf (o : Options) : TestShell.Mem := { stack := o.stack, region := o.region }

/-- Write the test executable of `p` for memory `m`, calling `exports`. -/
def shellExe (p : Program) (m : TestShell.Mem) (exports : List String := [X86.Exe.initSymbol, p.entry]) :
    IO FilePath := do
  let path := p.work / s!"{p.name}.shell-{m.stack}-{m.region}"
  match TestShell.writeExe m exports p.object with
  | .ok bytes =>
    IO.FS.writeBinFile path bytes
    IO.setAccessRights path { user := { read := true, write := true, execution := true } }
    pure path
  | .error e => throw (IO.userError s!"{p.name}: no test executable: {e}")

/-- Write `object` to the work directory and its test executable for the
default stack and region, calling `entry`; `run` takes the executable's path. -/
def link (t : Tools) (name : String) (object : ByteArray) (entry : String) : IO FilePath := do
  IO.FS.writeBinFile (t.work / s!"{name}.o") object
  let p : Program := { object, entry, work := t.work, name }
  let exe ← shellExe p (memOf {})
  programs.modify fun ps => (exe.toString, p) :: ps.filter (·.1 != exe.toString)
  pure exe

/-- The region from `region + 16` to the bump pointer `bump`, as a memory:
readable up to the region's end, its bytes past `bump` zero (a well-formed
result reaches none of them). -/
def liveMemory (base size bump : Nat) (live : ByteArray) : X86.Memory :=
  { bytes := fun a => if base + 16 ≤ a.toNat && a.toNat < bump then live[a.toNat - (base + 16)]! else 0
    readable := fun a => base + 16 ≤ a.toNat && a.toNat < base + size
    writable := fun _ => false }

/-- Decode `value` both ways over the live region; they must agree. The
independent decoder's text. -/
def decodeBoth (exe : FilePath) (sig : Rt.Sig) (ty : Rt.FoTy) (base size bump : Nat) (live : ByteArray)
    (fuel : Nat) (value : Word) : IO (Option String) := do
  let lean := (Rt.readback sig fuel (liveMemory base size bump live) ty value).map Rt.renderObs
  let view : Decoder.View := { base := UInt64.ofNat base, size := UInt64.ofNat size, live }
  let independent := Decoder.decodeText ty.encode sig.encode view fuel value
  unless lean == independent do
    throw (IO.userError s!"{exe}: the result {value} decodes to {lean} by Rt.readback and to {independent} by \
      the independent decoder")
  decodedResults.modify (· + 1)
  return independent

/-- Run input lines through the test executable `exe` for memory `m` (see the
module note). -/
def runShell (exe : FilePath) (m : TestShell.Mem) (o : Options) (inputs : List (List Nat))
    (seconds : Option Nat := none) : IO (List Line) := do
  Session.withSession exe (seconds := seconds) fun s => do
    let base := m.base
    let mut out : Array Line := #[]
    for xs in inputs do
      Session.writeWord s (base + 16) m.budget
      let (status, value, ok) ← Session.call s 0 [base, o.region, m.budget]
      if status != 0 || !ok then
        out := out.push { status, value, ok, init := true }
        nativeLines.modify (· + 1)
        continue
      let args := (xs.take 5).map fun a => min a (2 ^ 64 - 1)
      let t0 ← IO.monoNanosNow
      let (status, value, ok) ← Session.call s 1 (base :: args)
      let t1 ← IO.monoNanosNow
      nativeLines.modify (· + 1)
      let mut line : Line := { status, value, ok, ns := if o.time then some (t1 - t0) else none }
      if o.ty.isSome || o.dump then
        let ctx ← Session.read s (base + 16) 48
        let bump := (Session.word ctx 8).toNat
        let limit := Session.word ctx 16
        let start := Rt.objectsStart base
        unless start ≤ bump && bump ≤ base + o.region do
          throw (IO.userError s!"{exe} {xs}: the bump pointer {bump} is outside the object area [{start}, {base + o.region}]")
        let live ← Session.read s (base + 16) (bump - (base + 16))
        if let some (sig, ty) := o.ty then
          if status == 0 then
            let fuel := (limit - UInt64.ofNat base).toNat / 8
            line := { line with obs := ← decodeBoth exe sig ty base o.region bump live fuel value }
        if o.dump then
          let d : Dump := { base := UInt64.ofNat base, start := UInt64.ofNat start, bump := UInt64.ofNat bump,
                            bytes := (live.extract (start - (base + 16)) (bump - (base + 16))).data }
          line := { line with dump := some d }
      out := out.push line
    return out.toList

/-- Run input lines as a test executable of the program `link` wrote at `exe`,
for the run's stack and region. -/
def run (exe : FilePath) (o : Options) (inputs : List (List Nat)) (seconds : Option Nat := none) :
    IO (List Line) := do
  let some p := (← programs.get).lookup exe.toString
    | throw (IO.userError s!"{exe}: no program was linked here")
  let m := memOf o
  runShell (← shellExe p m) m o inputs seconds

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

/-- A line as text, for logs: `status value ok [obs]`, or `init status value ok`. -/
def Line.render (l : Line) : String :=
  let ok := if l.ok then "1" else "0"
  if l.init then s!"init {l.status} {l.value} {ok}"
  else s!"{l.status} {l.value} {ok}{(l.obs.map (" " ++ ·)).getD ""}"

end IxCCTests.Rt.Native
