import IxCCTests.Backend.Support
import IxCCTests.Exe.Session

/-!
# Native execution of backend objects

An object runs as a test executable IxCC writes of it
(`IxCCTests.Exe.TestShell`, calling the object's one export), which the
session below drives as the back end's native harness requires. Inputs come
one per line, `budget a1 … an` (at most five arguments) or `seed S`, and each
`budget` line gives one result: `status value ok`, `ok` meaning the
callee-saved registers and `rsp` came back unchanged.

- The region is 64 KiB: at the Lean test region's address `0x10000`, in a
  zero-filled segment of its own, for a fixed case (generated programs compute
  with absolute addresses, which must agree with the Lean models); after the
  stack otherwise.
- `seed S` fills the region with `IxCCTests.Lir.Region.pattern` for seed `S`
  and sets `regionBase` (`ctx - 24`) to the test region's heap
  (`region + 0x400`).
- `budget a1 … an` sets the context block up as `cx_init` would, unless a
  pattern was written: the context and the heads cleared (704 bytes), and
  `bump` and `regionBase` at `region + 1024`, `limit` at the region's end; then
  it stores the budget at `ctx - 48` and calls the export with the region in
  `rdi` and the arguments in `rsi` … `r9` (zero beyond), with sentinels in the
  callee-saved registers, on an 8 MiB stack.
-/

namespace IxCCTests.Backend.Native

open System
open IxCCTests.Exe

structure Tools where
  work : FilePath

/-- What `link` recorded for an executable. -/
structure Program where
  object : ByteArray
  entry : String
  fixed : Bool
  work : FilePath
  name : String

initialize programs : IO.Ref (List (String × Program)) ← IO.mkRef []
initialize nativeLines : IO.Ref Nat ← IO.mkRef 0

/-- The native lines run so far in this process. -/
def lines : IO Nat := nativeLines.get

/-- The region's size and the fixed region's address. -/
def regionSize : Nat := 1 <<< 16
def fixedBase : Nat := 0x10000
/-- The Lean test region's heap, from its base. -/
def testHeap : Nat := 0x400

/-- The test executable's memory: an 8 MiB stack and the 64 KiB region. -/
def mem (fixed : Bool) : TestShell.Mem :=
  { stack := 8 <<< 20, region := regionSize, fixed := if fixed then some fixedBase else none }

/-- Write `object` and its test executable calling `entry`; `fixed` puts the
region at the Lean region's address. -/
def link (t : Tools) (name : String) (object : ByteArray) (entry : String) (fixed : Bool := false) :
    IO FilePath := do
  IO.FS.writeBinFile (t.work / s!"{name}.o") object
  let exe := t.work / name
  match TestShell.writeExe (mem fixed) [entry] object with
  | .ok bytes =>
    IO.FS.writeBinFile exe bytes
    IO.setAccessRights exe { user := { read := true, write := true, execution := true } }
  | .error e => throw (IO.userError s!"{name}: no test executable: {e}")
  programs.modify fun ps => (exe.toString, { object, entry, fixed, work := t.work, name }) ::
    ps.filter (·.1 != exe.toString)
  pure exe

/-- One native result line. -/
structure Line where
  status : Word
  value : Word
  ok : Bool
  deriving BEq, Repr

/-- The decimal words of an input line (saturating at `2^64 - 1`). -/
def lineWords (line : String) : List Nat :=
  ((line.splitOn " ").filter (!·.isEmpty)).filterMap fun w => w.toNat?.map (min · (2 ^ 64 - 1))

/-- Run an executable `link` wrote on input lines; one result per non-`seed`
line (see the module note). -/
def run (exe : FilePath) (lines : List String) : IO (List Line) := do
  let some p := (← programs.get).lookup exe.toString
    | throw (IO.userError s!"{exe}: no program was linked here")
  let m := mem p.fixed
  Session.withSession exe fun s => do
    let base := m.base
    let mut patterned := false
    let mut out : Array Line := #[]
    for line in lines do
      if line.startsWith "seed " then
        let seed := UInt64.ofNat ((lineWords (line.drop 5).toString).headD 0)
        let bytes : ByteArray := ⟨(Array.range regionSize).map fun i =>
          IxCCTests.Lir.Region.pattern seed (UInt64.ofNat (base + i))⟩
        Session.write s base bytes
        -- regionBase (ctx - 24) := the test region's heap
        Session.writeWord s (base + 40) (base + testHeap)
        patterned := true
        continue
      let budget :: args := lineWords line | continue
      unless patterned do
        -- cleared heads, and a bump allocator from region + 1024 to the end
        let block := (Session.words [0, 0, 0, base + 1024, base + regionSize, base + 1024]) ++
          ⟨Array.replicate (704 - 48) 0⟩
        Session.write s base block
      Session.writeWord s (base + 16) budget
      let (status, value, ok) ← Session.call s 0 (base :: (args.take 5))
      out := out.push { status, value, ok }
      nativeLines.modify (· + 1)
    return out.toList

end IxCCTests.Backend.Native
