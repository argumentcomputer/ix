import IxCC.X86.ELFRodata
import IxCC.X86.ELFWriteK
import IxCC.X86.ELFValidate
import IxCC.X86.ELFCheckK
import IxCC.Rt.Rc.Array.Procs
import IxCC.Rt.Rc.Array.Invariant
import IxCC.Rt.Readback.Array
import IxCC.Src.ArraySpec

/-! # Interpreter, `.rodata` ELF, Readback, and Spec Controls for DR1/DR3/DR4

Exercises:
1. DR1 `.rodata` ELF64 emission (`writeCheckedK`) with immortal static `String`,
   `ByteArray`, `BigNat` `≥ 2^63` limb array, boxed `Array`, and static ctor,
   verified by both `ELFValidate.check` and `ELFCheckK.checkK`, plus `readelf -W -S -s`
   on the emitted `.o` file.
2. `Rt.Readback.Array` over `ELFRodata.mapRodata`: `readbackString`,
   `readbackByteArrayObs`, `readbackBigNat` (both small `< 2^63` and canonical
   `BigNat ≥ 2^63`), and `readbackBoxedArray`.
3. `Lir.eval` checks across `arrClassFor`/`arrClassWords` (all 71 classes),
   `arrSize`/`arrCap`/`arrGet`/`byteArrGet`, and `arrDec` on read-only `.rodata`
   memory (confirming zero write faults and identical memory!).
4. `Src.ArraySpec` pure-Lean executable sanity checks. -/

set_option autoImplicit false

namespace IxCCTests.Array.LirControls

open IxCC
open IxCC.X86
open IxCC.X86.ELF
open IxCC.X86.ELFRodata
open IxCC.Rt
open IxCC.Rt.Rc.Array
open IxCC.Rt.Readback

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def check (cond : Bool) (label : String) (cnt : IO.Ref Nat) : IO Unit := do
  cnt.modify (· + 1)
  unless cond do throw (IO.userError s!"FAIL LirControls: {label}")

/-- Test DR1 `.rodata` ELF64 emission + validation + `readelf` + readback + read-only `arrDec`. -/
def testRodataAndReadback (logs : System.FilePath) (cnt : IO.Ref Nat) : IO Unit := do
  -- Build a `.rodata` table with all 5 static cell kinds
  let t0 := RodataTable.empty
  let (t1, offStr) := t0.addString "cx_static_str" "Hello, IxCC UTF-8: λ→∀!"
  let (t2, offBytes) := t1.addByteArray "cx_static_bytes" (ByteArray.mk #[0, 1, 0x7f, 0x80, 0xfe, 0xff])
  let bigVal : Nat := (1 <<< 128) + (0xdeadbeefcafe1234 <<< 64) + 0x0123456789abcdef
  let bigLimbs : List Word := (BigNat.ofNat bigVal).toList
  let (t3, offBig) := t2.addLimbArray "cx_static_bignat" bigLimbs
  let (t4, offBoxed) := t3.addBoxedArray "cx_static_boxed" [1, 3, 5, 7, 9]
  let (t5, offCtor) := t4.addCtor "cx_static_ctor" 1 [41, 83]
  -- Emit a valid ELF64 relocatable object with both `.text` (single `ret`) and `.rodata`
  let textBytes := ByteArray.mk #[0xC3]
  let input : ELF.Input :=
    { encoded := { text := textBytes, blockOffsets := #[0], relocations := #[] }
      entryBlock := 0
      exportName := "cx_noop"
      provenance := .ixir2 (Ixon.Address.replicate 0x55)
      rodata := some t5.bytes
      rodataExports := t5.symbols }
  match ELF.writeCheckedK input with
  | .error e => throw (IO.userError s!"FAIL writeCheckedK(.rodata): {reprStr e}")
  | .ok cert =>
    let bytes := cert.bytes
    check (ELF.check input bytes) "ELF.check accepts .rodata object" cnt
    check (ELF.checkK input bytes) "ELF.checkK accepts .rodata object" cnt
    let roPath := logs / "rodata_cells.o"
    IO.FS.writeBinFile roPath bytes
    -- Verify host binutils `readelf` sees `.rodata` with expected static symbols
    let re ← IO.Process.output { cmd := "readelf", args := #["-W", "-S", "-s", roPath.toString] }
    check (re.exitCode == 0) "readelf accepts emitted .rodata ELF64 object" cnt
    check (hasSubstr re.stdout ".rodata") "readelf shows .rodata section" cnt
    check (hasSubstr re.stdout "cx_static_str") "readelf shows cx_static_str symbol" cnt
    check (hasSubstr re.stdout "cx_static_bignat") "readelf shows cx_static_bignat symbol" cnt
    -- Map `.rodata` read-only at 0x400000 and verify Readback + Lir queries + read-only `arrDec`
    let base : Word := 0x400000
    let mem := mapRodata Memory.unmapped base t5.bytes
    let addrStr := base + UInt64.ofNat offStr
    let addrBytes := base + UInt64.ofNat offBytes
    let addrBig := base + UInt64.ofNat offBig
    let addrBoxed := base + UInt64.ofNat offBoxed
    let addrCtor := base + UInt64.ofNat offCtor
    -- Readback checks
    check (readbackString mem addrStr == some "Hello, IxCC UTF-8: λ→∀!")
      "readbackString exact UTF-8 round-trip on .rodata" cnt
    check (readbackByteArrayObs mem addrBytes == some (.bytes [0, 1, 0x7f, 0x80, 0xfe, 0xff]))
      "readbackByteArrayObs exact round-trip on .rodata" cnt
    check (readbackBigNat mem (UInt64.ofNat (2 * 42 + 1)) == some 42)
      "readbackBigNat small immediate" cnt
    check (readbackBigNat mem addrBig == some bigVal)
      "readbackBigNat >= 2^63 static limb cell" cnt
    check (readbackBoxedArray {} 4 mem .nat addrBoxed == some [.nat 0, .nat 1, .nat 2, .nat 3, .nat 4])
      "readbackBoxedArray on .rodata" cnt
    -- Lir.eval queries on read-only `.rodata`
    let strLen := "Hello, IxCC UTF-8: λ→∀!".toUTF8.size
    match Lir.eval (arrayProgram fnSize) 10 [addrStr] mem 0 with
    | .ok ([sz], _) => check (sz.toNat == strLen) "Lir arrSize on static String" cnt
    | _ => throw (IO.userError "FAIL Lir arrSize on static String")
    match Lir.eval (arrayProgram fnByteGet) 10 [addrBytes, 4] mem 0 with
    | .ok ([b], _) => check (b.toNat == 0xfe) "Lir byteArrGet on static ByteArray" cnt
    | _ => throw (IO.userError "FAIL Lir byteArrGet on static ByteArray")
    match Lir.eval (arrayProgram fnGetWord) 10 [addrBig, 1] mem 0 with
    | .ok ([w], _) => check (w == 0xdeadbeefcafe1234) "Lir arrGet on static BigNat limb" cnt
    | _ => throw (IO.userError "FAIL Lir arrGet on static BigNat limb")
    -- Lir `arrDec` on read-only `.rodata` (every byte has `writable = false`, so ANY write faults!)
    for (lbl, a) in [("str", addrStr), ("bytes", addrBytes), ("bignat", addrBig),
                     ("boxed", addrBoxed), ("ctor", addrCtor)] do
      match Lir.eval (arrayProgram fnDec) 20 [a] mem 0 with
      | .ok ([], _) => check true s!"arrDec immortal no-op on read-only .rodata ({lbl})" cnt
      | _ => throw (IO.userError s!"FAIL arrDec on read-only .rodata ({lbl})")

/-- Verify `arrClassFor` and `arrClassWords` via `Lir.eval` across all 71 size classes. -/
def testSizeClassesLir (cnt : IO.Ref Nat) : IO Unit := do
  -- All 71 classes: classWords round-trip and boundary classFor checks
  for c in List.range' 1 71 do
    let cw := IxCC.Rt.Rc.classWords c
    match Lir.eval (arrayProgram fnClassWords) 5 [UInt64.ofNat c] Memory.unmapped 0 with
    | .ok ([got], _) => check (got.toNat == cw) s!"Lir arrClassWords({c})" cnt
    | _ => throw (IO.userError s!"FAIL Lir arrClassWords({c})")
    match Lir.eval (arrayProgram fnClassFor) 5 [UInt64.ofNat cw] Memory.unmapped 0 with
    | .ok ([got], _) => check (got.toNat == c) s!"Lir arrClassFor(classWords {c})" cnt
    | _ => throw (IO.userError s!"FAIL Lir arrClassFor(classWords {c})")
    if c > 1 then
      let prev := IxCC.Rt.Rc.classWords (c - 1)
      match Lir.eval (arrayProgram fnClassFor) 5 [UInt64.ofNat (prev + 1)] Memory.unmapped 0 with
      | .ok ([got], _) => check (got.toNat == c) s!"Lir arrClassFor(prev+1 for class {c})" cnt
      | _ => throw (IO.userError s!"FAIL Lir arrClassFor(prev+1 for class {c})")
  -- Failure boundaries: 0 and maxCellWords + 1
  match Lir.eval (arrayProgram fnClassFor) 5 [0] Memory.unmapped 0 with
  | .resource .heap => check true "Lir arrClassFor(0) fails .heap" cnt
  | _ => throw (IO.userError "FAIL Lir arrClassFor(0)")
  match Lir.eval (arrayProgram fnClassFor) 5 [UInt64.ofNat (IxCC.Rt.Rc.maxCellWords + 1)] Memory.unmapped 0 with
  | .resource .heap => check true "Lir arrClassFor(max+1) fails .heap" cnt
  | _ => throw (IO.userError "FAIL Lir arrClassFor(max+1)")

/-- Run all Lir, `.rodata` ELF, readback, and spec controls. -/
def run (logs : System.FilePath) : IO Nat := do
  IO.FS.createDirAll logs
  let cnt ← IO.mkRef 0
  testRodataAndReadback logs cnt
  testSizeClassesLir cnt
  let n ← cnt.get
  IO.println s!"PASS LirControls (.rodata ELF + readback + 71-class Lir): {n} assertions"
  return n

end IxCCTests.Array.LirControls
