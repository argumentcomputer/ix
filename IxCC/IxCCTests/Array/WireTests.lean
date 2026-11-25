import IxCC.Recheck
import IxCC.Lam.Erase.Array
import IxCC.Fir.Rep
import IxCC.Rt.Rc.Array.Wire
import IxCC.Rt.Readback.Array
import IxCC.X86.ELFWriteK
import IxCC.X86.ELFValidate
import IxCC.X86.ELFCheckK
import IxCC.BigNat.Basic
import IxCC.BigNat.Linear
import IxCC.BigNat.Mul
import IxCC.BigNat.Div
import IxCCTests.Exe.Session

/-! # DR1 + DR3 + DR4 End-to-End Native Xeon Wiring Verification (`WireTests`)

Verifies the full `Src → Lam → Anf → Fir → Fir.Rep → Own → Cfg → Rt.lower / Rt.lowerRep
→ Backend.compile → TestShell` pipeline natively on x86-64 Xeon (seccomp-confined, zero C):

1. **Always-on wire runtime & committed fixture controls (zero external `ix` required):**
   * The array analyses (`Rt.LowerRep.liveInFix`, `taintedFix`, `paramMutFix`) on programs
     that need more rounds than their old fixed counts: each reaches its complete fixpoint within
     its bound, `checkArrayAnalyses` accepts them, and a bound too small is refused.
   * Relocated 36-proc extended array runtime (`Wire.lean`): `arrSwapBoxed`, `arrSwapLimbs`,
     `arrOfListBoxed`/`arrToListBoxed`, `arrOfListLimbs`/`arrToListLimbs` (across `< 2^63`
     immediates and `≥ 2^63` boxed 64-bit limbs), `byteArrOfArr`/`byteArrToArr`,
     `arrIncValue` (immediate / dynamic / static `.rodata` / immortal ctor), `strLitProc`
     (empty, ASCII, multi-byte UTF-8, > 32B), and `rodataStrProc`.
   * DR1 `.rodata` ELF64 round-trip (`LowerStr.buildStringRodata` → `ELF.writeCheckedK`
     → `ELFValidate.check` + `ELFCheckK.checkK` + `ELFRead.rodata?`).
   * `Decline.withPanic` (`fixtures/corpus/phase1-decline/panic.ixe`) via standard
     `Recheck.compileInput` + native Xeon (`0 → 0`, `7 → 0`, `42 → 42`).
   * `Decline.stringLength` (`fixtures/corpus/phase1-decline/strings.ixe`) via DR3+DR4
     `arrays-wire` + native Xeon (`0 → 3`, `10 → 13`, `100 → 103`).

2. **Full Lean-source-to-Xeon K3 / K4 / `BigNat` / Aliasing suite (auto-run whenever `ix`
   is available; mandatory under `--require-ix`):**
   * **K3 `rbmap_checkpoint`**: `entry 100000 10` → `(10001, 10000)` (`expected.txt`).
   * **K4 `array-qsort`**: `entry 1000` → `1000413603308` (`expected.txt`) + O(n) bump check.
   * **K4 `blake3`**: official vector `8193` → `ByteArray` cell matching
     `bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3b` (`expected.txt`),
     plus vectors `0`, `64`, `1024`, `1025`.
   * **`Array UInt64` `BigNat` smoke test**: `IxCC.BigNat.{add, mul, divMod}` on unboxed
     `LimbArray` (`tag = 0x7F03`) with `≥ 2^63` 64-bit limbs and fused `LimbOps` pins.
   * **Aliasing / COW / op coverage**: shared `Array`/`ByteArray` COW, local alias,
     `idArr` escape, nested `Array (Array Nat)`, `pop`, `extract`, `uget`/`uset`,
     `copySlice`, and multi-byte UTF-8 `String` literals. -/

set_option autoImplicit false

namespace IxCCTests.Array.WireTests

open IxCC
open IxCC.Rt
open IxCC.Rt.Rc.Array
open IxCC.X86
open IxCC.X86.ELFRodata
open IxCCTests.Exe
open System

/-! ## Helpers -/

private def require (cnt : IO.Ref Nat) (c : Bool) (label : String) : IO Unit := do
  cnt.modify (· + 1)
  unless c do throw (IO.userError s!"FAIL WireTests: {label}")

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def bytesToHex (bs : ByteArray) : String :=
  String.ofList (bs.data.toList.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

private def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def parseHexAddr? (s : String) : Option Ixon.Address := do
  let trimmed := s.trimAscii.toString
  if trimmed.length != 64 then none
  let cs := trimmed.toList.toArray
  let mut bs : Array UInt8 := Array.mkEmpty 32
  for i in List.range 32 do
    let hi ← hexVal? cs[2 * i]!
    let lo ← hexVal? cs[2 * i + 1]!
    bs := bs.push (UInt8.ofNat (hi * 16 + lo))
  if h : bs.size = 32 then
    some ⟨⟨bs⟩, h⟩
  else
    none

private def dummyProv : ELF.Provenance :=
  .ixir1Policy (Ixon.Address.replicate 0x57) 1 1

/-! ## 1. Relocated 36-proc `Wire.lean` + `strLitProc` + `rodataStrProc` Native Xeon Controls -/

private def wireBase : Lir.FunId := 4

private def effectWrap (name : String) (f : Lir.FunId) : Lir.Func :=
  { name, params := [0], results := 1, conv := .sysvExport name
    blocks := #[{ body := #[.call [] f [.v 0]], term := .ret [.imm 1] }] }

/-- Allocate a 2-field immortal constructor cell with `tag` (`List.cons` = 1) or
a 1-scalar-word boxed `UInt64` cell (`tag = 0`, `scan = 0`, `rc = 0x80000000`). -/
private def mkConsProc (tag : Nat) : Lir.Func :=
  { name := "test_mk_cons", params := [0, 1], results := 1, conv := .sysvExport "test_mk_cons"
    blocks := #[
      { body := #[
          .assign 2 (.load .w64 .zero (Rt.Rc.Procs.ctx Rt.bumpOff)),
          .assign 3 (.bin .add .w64 (.v 2) (.imm 24)),
          .store .w64 (Rt.Rc.Procs.ctx Rt.bumpOff) (.v 3),
          .store .w64 (Rt.Rc.Procs.cellAddr 2 0) (.imm (Rt.immortalHeader 2 tag)),
          .store .w64 (Rt.Rc.Procs.cellAddr 2 8) (.v 0),
          .store .w64 (Rt.Rc.Procs.cellAddr 2 16) (.v 1)]
        term := .ret [.v 2] } ] }

private def mkBox64Proc : Lir.Func :=
  { name := "test_mk_box64", params := [0], results := 1, conv := .sysvExport "test_mk_box64"
    blocks := #[
      { body := #[
          .assign 1 (.load .w64 .zero (Rt.Rc.Procs.ctx Rt.bumpOff)),
          .assign 2 (.bin .add .w64 (.v 1) (.imm 16)),
          .store .w64 (Rt.Rc.Procs.ctx Rt.bumpOff) (.v 2),
          .store .w64 (Rt.Rc.Procs.cellAddr 1 0) (.imm (Rt.immortalHeader 0 0)),
          .store .w64 (Rt.Rc.Procs.cellAddr 1 8) (.v 0)]
        term := .ret [.v 1] } ] }

private def testStrings : List String :=
  [ "", "hello", "λx. café 🚀", "The quick brown fox jumps over the lazy dog 0123456789!" ]

private def testWireProcs (logs : FilePath) (cnt : IO.Ref Nat) : IO Unit := do
  -- Place 4 functions at indices 0..3, then relocate all 36 extended array runtime procs to 4..39,
  -- followed by strLitProcs at 40..43 and rodataStrProc at 44!
  let nilTag : Nat := 0
  let consTag : Nat := 1
  let reloc := extendedArrayRuntimeFuncs wireBase nilTag consTag
  require cnt (reloc.length == 36) "extendedArrayRuntimeFuncs has length 36"
  let expAt (sym : String) (f : Lir.Func) : Lir.Func :=
    if f.results == 0 then f else { f with conv := .sysvExport sym }
  let relocExp := reloc.zipIdx.map fun (f, i) =>
    if i == fnEmptyCapBoxed then expAt "w_empty_boxed" f
    else if i == fnEmptyCapLimbs then expAt "w_empty_limbs" f
    else if i == fnByteEmptyCap then expAt "w_empty_byte" f
    else if i == fnSize then expAt "w_size" f
    else if i == fnGetWord then expAt "w_get" f
    else if i == fnByteGet then expAt "w_byte_get" f
    else if i == fnPushBoxed then expAt "w_push_boxed" f
    else if i == fnPushLimbs then expAt "w_push_limbs" f
    else if i == fnBytePush then expAt "w_byte_push" f
    else if i == fnSwapBoxed then expAt "w_swap_boxed" f
    else if i == fnSwapLimbs then expAt "w_swap_limbs" f
    else if i == fnArrOfListBoxed then expAt "w_arr_of_list_boxed" f
    else if i == fnArrToListBoxed then expAt "w_arr_to_list_boxed" f
    else if i == fnArrOfListLimbs then expAt "w_arr_of_list_limbs" f
    else if i == fnArrToListLimbs then expAt "w_arr_to_list_limbs" f
    else if i == fnByteArrOfArr then expAt "w_ba_of_arr" f
    else if i == fnByteArrToArr then expAt "w_ba_to_arr" f
    else f
  let strProcs := testStrings.zipIdx.map fun (s, i) =>
    { strLitProc i s with conv := .sysvExport s!"w_str_{i}" }
  let roProc := { rodataStrProc 0 0x0000000012345678 with conv := .sysvExport "w_rodata_str" }
  let prog : Lir.Program :=
    { funcs := (#[
        Rt.Procs.cxInit,
        effectWrap "w_inc_val" (wireBase + fnIncVal),
        mkConsProc consTag,
        mkBox64Proc
      ] ++ relocExp.toArray ++ strProcs.toArray ++ #[roProc])
      main := 0 }
  let p := prog.splitCriticalEdges
  match p.check with
  | .error e => throw (IO.userError s!"FAIL WireTests wireProcs Lir.check: {e}")
  | .ok () => pure ()
  let cfg : Backend.Config :=
    { provenance := dummyProv
      reps := fun f => (p.funcs[f]?).map fun fd => fd.params.map fun _ => .word }
  let art ← IO.ofExcept ((Backend.compile p cfg).mapError toString)
  let exportNames : List String := [
    "cx_init", "w_inc_val", "test_mk_cons", "test_mk_box64",
    "w_empty_boxed", "w_empty_limbs", "w_empty_byte",
    "w_size", "w_get", "w_byte_get",
    "w_push_boxed", "w_push_limbs", "w_byte_push",
    "w_swap_boxed", "w_swap_limbs",
    "w_arr_of_list_boxed", "w_arr_to_list_boxed",
    "w_arr_of_list_limbs", "w_arr_to_list_limbs",
    "w_ba_of_arr", "w_ba_to_arr",
    "w_str_0", "w_str_1", "w_str_2", "w_str_3", "w_rodata_str"
  ]
  let mem : TestShell.Mem := { stack := 65536, region := 524288 }
  let exePath := logs / "wire-procs-test"
  match TestShell.writeExe mem exportNames art.object with
  | .error err => throw (IO.userError s!"FAIL WireTests writeExe(wire-procs): {err}")
  | .ok exeBytes =>
    IO.FS.writeBinFile exePath exeBytes
    IO.setAccessRights exePath { user := { read := true, write := true, execution := true } }
  Session.withSession exePath (seconds := some 30) fun s => do
    let base := mem.base
    let callOk (k : Nat) (args : List Nat) (label : String) : IO Nat := do
      let (rax, rdx, ok) ← Session.call s k (base :: args)
      require cnt (ok && rax == 0) s!"{label}: ok={ok} rax={rax}"
      return rdx.toNat
    Session.writeWord s (base + 16) (mem.stack - 4096)
    discard <| callOk 0 [mem.region, mem.stack - 4096] "cx_init"
    -- 1. arrSwapBoxed: unique in-place + shared COW + OOB/equal no-op
    let mut ab ← callOk 4 [4] "empty_boxed"
    for v in [11, 23, 35, 47] do
      ab ← callOk 10 [ab, v] "push_boxed"
    let bumpPre ← Session.readWord s (base + 24)
    let abSw ← callOk 13 [ab, 1, 3] "swap_boxed unique"
    require cnt (abSw == ab && (← Session.readWord s (base + 24)) == bumpPre) "arrSwapBoxed unique in-place"
    require cnt ((← callOk 8 [abSw, 1] "get 1") == 47 && (← callOk 8 [abSw, 3] "get 3") == 23)
      "arrSwapBoxed unique values"
    let abOob ← callOk 13 [abSw, 0, 99] "swap_boxed oob"
    require cnt (abOob == abSw) "arrSwapBoxed OOB no-op"
    discard <| callOk 1 [abSw] "inc_val boxed"
    let abCow ← callOk 13 [abSw, 0, 2] "swap_boxed COW"
    require cnt (abCow != abSw && (← callOk 8 [abSw, 0] "orig 0") == 11 &&
      (← callOk 8 [abCow, 0] "cow 0") == 35 && (← callOk 8 [abCow, 2] "cow 2") == 11)
      "arrSwapBoxed shared COW"
    -- 2. arrSwapLimbs: unique & COW on raw 64-bit limbs >= 2^63
    let limbA : Nat := 0x8000000000000000
    let limbB : Nat := 0xFFFFFFFFFFFFFFFE
    let limbC : Nat := 0x123456789ABCDEF0
    let mut al ← callOk 5 [4] "empty_limbs"
    for v in [limbA, limbB, limbC] do
      al ← callOk 11 [al, v] "push_limbs"
    let alSw ← callOk 14 [al, 0, 2] "swap_limbs unique"
    require cnt (alSw == al && (← callOk 8 [alSw, 0] "limb 0") == limbC &&
      (← callOk 8 [alSw, 2] "limb 2") == limbA) "arrSwapLimbs unique >= 2^63"
    discard <| callOk 1 [alSw] "inc_val limbs"
    let alCow ← callOk 14 [alSw, 1, 2] "swap_limbs COW"
    require cnt (alCow != alSw && (← callOk 8 [alSw, 1] "orig limb 1") == limbB &&
      (← callOk 8 [alCow, 1] "cow limb 1") == limbA) "arrSwapLimbs COW >= 2^63"
    -- 3. arrOfListBoxed / arrToListBoxed round-trip
    let nilW := (Rt.ctor0Word nilTag).toNat
    let mut lst := nilW
    for v in [99, 77, 55, 33, 11] do
      lst ← callOk 2 [v, lst] "mk_cons boxed"
    let fromLst ← callOk 15 [lst] "arr_of_list_boxed"
    require cnt ((← callOk 7 [fromLst] "size") == 5 &&
      (← callOk 8 [fromLst, 0] "e0") == 11 && (← callOk 8 [fromLst, 4] "e4") == 99)
      "arrOfListBoxed round-trip"
    let backLst ← callOk 16 [fromLst] "arr_to_list_boxed"
    let mut cur := backLst
    for expected in [11, 33, 55, 77, 99] do
      let hd := (← Session.readWord s (cur + 8)).toNat
      require cnt (hd == expected) s!"arrToListBoxed elem {expected}"
      cur := (← Session.readWord s (cur + 16)).toNat
    require cnt (cur == nilW) "arrToListBoxed nil terminator"
    -- 4. arrOfListLimbs / arrToListLimbs mixing < 2^63 immediates & >= 2^63 boxed cells
    let limbVals : List Nat := [0, 1, (1 <<< 63) - 1, 1 <<< 63, (1 <<< 64) - 1, 0xFEDCBA9876543210]
    let mut limbLst := nilW
    for lv in limbVals.reverse do
      let elemW ← if lv < (1 <<< 63) then pure (2 * lv + 1) else callOk 3 [lv] "mk_box64"
      limbLst ← callOk 2 [elemW, limbLst] "mk_cons limbs"
    let limbsArr ← callOk 17 [limbLst] "arr_of_list_limbs"
    require cnt ((← callOk 7 [limbsArr] "limbs size") == limbVals.length) "arrOfListLimbs size"
    for (lv, idx) in limbVals.zipIdx do
      require cnt ((← callOk 8 [limbsArr, idx] s!"limb[{idx}]") == lv) s!"arrOfListLimbs[{idx}] exact 64-bit"
    let limbsBack ← callOk 18 [limbsArr] "arr_to_list_limbs"
    let mut lcur := limbsBack
    for lv in limbVals do
      let hd := (← Session.readWord s (lcur + 8)).toNat
      let decoded ← if hd % 2 == 1 then pure (hd / 2) else pure (← Session.readWord s (hd + 8)).toNat
      require cnt (decoded == lv) s!"arrToListLimbs decoded {lv}"
      lcur := (← Session.readWord s (lcur + 16)).toNat
    require cnt (lcur == nilW) "arrToListLimbs nil terminator"
    -- 5. byteArrOfArr / byteArrToArr round-trip
    let byteVals : List Nat := (List.range 33).map fun j => (j * 37 + 5) % 256
    let mut u8Arr ← callOk 4 [33] "empty u8 arr"
    for b in byteVals do
      u8Arr ← callOk 10 [u8Arr, 2 * b + 1] "push u8"
    let ba ← callOk 19 [u8Arr] "ba_of_arr"
    require cnt ((← callOk 7 [ba] "ba size") == 33) "byteArrOfArr size"
    for (b, idx) in byteVals.zipIdx do
      require cnt ((← callOk 9 [ba, idx] s!"ba[{idx}]") == b) s!"byteArrOfArr[{idx}]"
    let u8Back ← callOk 20 [ba] "ba_to_arr"
    require cnt ((← callOk 7 [u8Back] "u8Back size") == 33) "byteArrToArr size"
    for (b, idx) in byteVals.zipIdx do
      require cnt ((← callOk 8 [u8Back, idx] s!"u8Back[{idx}]") == 2 * b + 1) s!"byteArrToArr[{idx}]"
    -- 6. strLitProc (0..3) + arrIncValue on static string & immediates + rodataStrProc
    discard <| callOk 1 [1] "inc_val immediate 0"
    discard <| callOk 1 [43] "inc_val immediate 21"
    for (str, idx) in testStrings.zipIdx do
      let sp ← callOk (21 + idx) [] s!"strLitProc {idx}"
      let hdr := (← Session.readWord s sp).toNat
      let sz := (← Session.readWord s (sp + 8)).toNat
      let cap := (← Session.readWord s (sp + 16)).toNat
      let expectedHdr := (staticHeader 0 tagByteArray).toNat
      let utf := str.toUTF8
      require cnt (hdr == expectedHdr && sz == utf.size && cap == ELF.alignUp utf.size 8)
        s!"strLitProc {idx} header/size/cap"
      if utf.size > 0 then
        let payload ← Session.read s (sp + 24) utf.size
        require cnt (payload == utf) s!"strLitProc {idx} UTF-8 bytes exact"
      -- inc_val on static cell MUST preserve rc = 0x80000000
      discard <| callOk 1 [sp] s!"inc_val static str {idx}"
      require cnt ((← Session.readWord s sp).toNat == expectedHdr) s!"strLitProc {idx} static rc immortal"
    let bumpRo ← Session.readWord s (base + 24)
    let roAddr ← callOk 25 [] "rodataStrProc"
    require cnt (roAddr == 0x12345678 && (← Session.readWord s (base + 24)) == bumpRo)
      "rodataStrProc returns address without advancing bump"
  IO.println "PASS WireTests: relocated 36-proc Wire.lean + strLitProc + rodataStrProc natively on Xeon"

/-! ## 2. DR1 `.rodata` ELF64 Round-Trip (`LowerStr.buildStringRodata`) -/

private def testRodataElf (cnt : IO.Ref Nat) : IO Unit := do
  let (tbl, offs) := LowerStr.buildStringRodata testStrings
  require cnt (offs.length == testStrings.length) "buildStringRodata entry count"
  let inp : ELF.Input :=
    { encoded := { text := ByteArray.mk #[0xC3], blockOffsets := #[0], relocations := #[] }
      entryBlock := 0
      exportName := "cx_str_rodata_noop"
      provenance := dummyProv
      rodata := some tbl.bytes
      rodataExports := tbl.symbols }
  let cert ← IO.ofExcept ((ELF.writeCheckedK inp).mapError reprStr)
  let obj := cert.bytes
  require cnt (ELF.checkK inp obj) "ELFCheckK accepts .rodata string table object"
  require cnt (ELF.check inp obj) "ELFValidate accepts .rodata string table object"
  match ELFRead.rodata? obj with
  | none => throw (IO.userError "FAIL WireTests: ELFRead.rodata? returned none")
  | some ro =>
    require cnt (ro == tbl.bytes) "ELFRead.rodata? round-trips buildStringRodata bytes"
    for (str, off) in offs do
      let enc := encodeStaticString str
      require cnt (off % 8 == 0 && off + enc.size ≤ ro.size) s!"rodata offset aligned for {str}"
      let slice := ro.extract off (off + enc.size)
      require cnt (slice == enc) s!"rodata cell matches encodeStaticString for {str}"
  IO.println "PASS WireTests: DR1 .rodata ELF64 buildStringRodata round-trip & validation"

/-! ## 3. DR3+DR4 Compilation Helper (`arrays-wire`) -/

structure CompiledWire where
  lowered : Rt.Lowered
  cert : Fir.Rep.Cert
  info : Lam.Erase.Array.ArrayEraseInfo
  object : ByteArray
  rootSym : String

private def compileWireFromInput (inp : Recheck.Input)
    (limbPins : List (Src.CId × Src.LimbOp) := [])
    (prodKey : Option Key.CtorKey := none)
    (kindOverride : Option Src.ArrayRepKind := none)
    (useRep : Bool := true) : Except String CompiledWire := do
  let ps ← (Recheck.produceSource {} inp).mapError (·.render)
  if !useRep then
    let (_, art) ← (Recheck.compileInput {} inp).mapError (·.render)
    let some r := art.roots.head? | throw "compileWire: no root"
    return { lowered := art.lowered, cert := {}, info := {}, object := art.object, rootSym := r.symbol }
  let (lam, _, info) ← (Lam.Erase.Array.eraseWithArrays ps.src ps.checked
      .fixed limbPins prodKey kindOverride).mapError toString
  let budgets : Anf.Pipeline.Budgets :=
    { inline := { noInline := info.noInline } }
  let trace ← Anf.Pipeline.produce budgets lam
  let (anf, _) ← (Recheck.produceClosures ps.src trace).mapError (·.render)
  let fir ← (Fir.lower anf).mapError (·.render)
  let cert := Fir.Rep.inferWithArrays fir info
  unless Fir.Rep.checkWithArrays fir cert do
    throw "Fir.Rep.checkWithArrays failed"
  let own := Own.immortal fir
  let cfg := Cfg.lower own
  let lowered ← (Rt.lowerRep { names := inp.names } cert cfg).mapError (·.render)
  lowered.program.check
  let art ← (lowered.compile dummyProv).mapError toString
  let some (_, rootSym) := lowered.roots.head? | throw "compileWire: no lowered root"
  return { lowered, cert, info, object := art.object, rootSym }

private def writeWireExe (logs : FilePath) (name : String) (cw : CompiledWire)
    (mem : TestShell.Mem := { stack := 262144, region := 64 * 1024 * 1024 }) : IO FilePath := do
  let exePath := logs / name
  match TestShell.writeExe mem ["cx_init", cw.rootSym] cw.object with
  | .error err => throw (IO.userError s!"FAIL WireTests writeExe({name}): {err}")
  | .ok exeBytes =>
    IO.FS.writeBinFile exePath exeBytes
    IO.setAccessRights exePath { user := { read := true, write := true, execution := true } }
    return exePath

private def initSession (s : Session.Session) (mem : TestShell.Mem) (cnt : IO.Ref Nat) (label : String) : IO Nat := do
  let budget := mem.stack - 4096
  Session.writeWord s (mem.base + 16) budget
  let (rax, _, ok) ← Session.call s 0 [mem.base, mem.region, budget]
  require cnt (ok && rax == 0) s!"{label}: cx_init ok={ok} rax={rax}"
  return (← Session.readWord s (mem.base + 24)).toNat

private def callRoot (s : Session.Session) (mem : TestShell.Mem) (args : List Nat)
    (cnt : IO.Ref Nat) (label : String) : IO UInt64 := do
  let (rax, rdx, ok) ← Session.call s 1 (mem.base :: args)
  require cnt (ok && rax == 0) s!"{label}: root call ok={ok} rax={rax}"
  return rdx

/-! ## 4. Committed `phase1-decline` Fixtures (`panic.ixe` & `strings.ixe`) -/

private def testCommittedDeclines (logs : FilePath) (cnt : IO.Ref Nat) : IO Unit := do
  let declineDir : FilePath := "fixtures" / "corpus" / "phase1-decline"
  -- 4a. `Decline.withPanic` via standard `Recheck.compileInput` (`Rt.lower` + string hoisting!)
  let panicBytes ← IO.FS.readBinFile (declineDir / "panic.ixe")
  let panicJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (declineDir / "panic.equations.json")))
  let panicInp ← IO.ofExcept ((Recheck.ingress panicBytes panicJson).mapError (·.render))
  let panicCw ← IO.ofExcept (compileWireFromInput panicInp (useRep := false))
  -- Note: `panic` ignores its string message after ANF inlining/DCE, so `rodata` may be `none`!
  let mem : TestShell.Mem := { stack := 131072, region := 8 * 1024 * 1024 }
  let panicExe ← writeWireExe logs "decline-panic" panicCw mem
  Session.withSession panicExe (seconds := some 30) fun s => do
    for (x, expected) in [(0, 0), (7, 0), (42, 42)] do
      let _ ← initSession s mem cnt s!"panic({x})"
      let w ← callRoot s mem [x] cnt s!"panic({x})"
      require cnt (w.toNat % 2 == 1 && w.toNat / 2 == expected)
        s!"Decline.withPanic({x}) == {expected} (got {w.toNat / 2})"
  -- 4b. `Decline.stringLength` via DR3+DR4 `arrays-wire` (`Rt.lowerRep`)
  let strBytes ← IO.FS.readBinFile (declineDir / "strings.ixe")
  let strJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (declineDir / "strings.equations.json")))
  let strInp ← IO.ofExcept ((Recheck.ingress strBytes strJson).mapError (·.render))
  let strCw ← IO.ofExcept (compileWireFromInput strInp (useRep := true))
  require cnt strCw.lowered.rodata.isSome "strings.ixe lowered with .rodata strings"
  let strExe ← writeWireExe logs "decline-strings" strCw mem
  Session.withSession strExe (seconds := some 30) fun s => do
    for (x, expected) in [(0, 3), (10, 13), (100, 103)] do
      let _ ← initSession s mem cnt s!"strings({x})"
      let w ← callRoot s mem [x] cnt s!"strings({x})"
      require cnt (w.toNat % 2 == 1 && w.toNat / 2 == expected)
        s!"Decline.stringLength({x}) == {expected} (got {w.toNat / 2})"
  IO.println "PASS WireTests: Decline.withPanic (0,7,42) & Decline.stringLength (0,10,100) natively on Xeon"

/-! ## 5. External `ix` Discovery & Lean-Source Freezing -/

private def findIx (cliIx : Option String) : IO (Option String) := do
  if let some p := cliIx then
    if ← System.FilePath.pathExists p then return some p
  if let some p ← IO.getEnv "IX_BIN" then
    if ← System.FilePath.pathExists p then return some p
  for cand in ["../.lake/build/bin/ix", "/home/john/runs/ixcc-megapr/.lake/build/bin/ix"] do
    if ← System.FilePath.pathExists cand then return some cand
  let out ← IO.Process.output { cmd := "which", args := #["ix"] }
  if out.exitCode == 0 then
    let p := out.stdout.trimAscii.toString
    if !p.isEmpty then return some p
  return none

private def runIxCompile (ixBin : String) (leanFile ixeOut eqOut : FilePath)
    (rootConst : String) (extraEnv : Array (String × Option String) := #[]) : IO Unit := do
  let args := #[
    "compile",
    "--no-build",
    "--consts", rootConst,
    "--out", ixeOut.toString,
    "--equations-out", eqOut.toString,
    "--word-equations",
    leanFile.toString
  ]
  let out ← IO.Process.output { cmd := ixBin, args, env := extraEnv }
  if out.exitCode != 0 then
    throw (IO.userError s!"FAIL WireTests: ix compile {leanFile} exited {out.exitCode}:\n{out.stdout}\n{out.stderr}")

private def addrBytesLt (a b : Ixon.Address) : Bool := Id.run do
  let n := min a.hash.size b.hash.size
  for i in [:n] do
    let x := a.hash.get! i
    let y := b.hash.get! i
    if x != y then return x < y
  return a.hash.size < b.hash.size

private def natFromBytesLE (bs : ByteArray) : Nat := Id.run do
  let mut acc : Nat := 0
  let mut shift : Nat := 0
  for i in [:bs.size] do
    acc := acc ||| ((bs.get! i).toNat <<< shift)
    shift := shift + 8
  return acc

/-- Decode Section 4 (names) and Section 5 (named → §2 constant rank) directly from a named
`.ixe` envelope in memory (< 5ms, zero `ix addr-of` subprocess spawns). -/
private def extractNamedMap (bytes : ByteArray) : Except String (Std.HashMap String String) := do
  let env ← Ixon.V3.decodeAnonymousEnv bytes
  let constOrder : Array Ixon.Address :=
    (env.consts.toArray.map (·.1)).qsort addrBytesLt
  let parseMeta : _root_.Ixon.GetM (Std.HashMap String String) := do
    -- Section 4: Names
    let numNames := (← _root_.Ixon.getTagN 0).value.toNat
    let mut namesLookup : Std.HashMap ByteArray String := {}
    let mut nameRev : Array String := Array.mkEmpty numNames
    for _ in [:numNames] do
      let addrBytes ← _root_.Ixon.getBytes 32
      let tag ← _root_.Ixon.getU8
      let nm ← match tag with
        | 0 => pure ""
        | 1 =>
          let pBytes ← _root_.Ixon.getBytes 32
          let len := (← _root_.Ixon.getTagN 0).value.toNat
          let sBytes ← _root_.Ixon.getBytes len
          let some s := String.fromUTF8? sBytes | throw "§4 invalid UTF-8 name"
          let parent := namesLookup.getD pBytes ""
          pure (if parent.isEmpty then s else s!"{parent}.{s}")
        | 2 =>
          let pBytes ← _root_.Ixon.getBytes 32
          let len := (← _root_.Ixon.getTagN 0).value.toNat
          let nBytes ← _root_.Ixon.getBytes len
          let n := natFromBytesLE nBytes
          let parent := namesLookup.getD pBytes ""
          pure (if parent.isEmpty then toString n else s!"{parent}.{n}")
        | t => throw s!"§4 invalid name component tag {t}"
      nameRev := nameRev.push nm
      namesLookup := namesLookup.insert addrBytes nm
    -- Section 5: Named (nameIdx, constRank, fusedOptHint, len-prefixed metadata blob)
    let numNamed := (← _root_.Ixon.getTagN 0).value.toNat
    let mut out : Std.HashMap String String := Std.HashMap.emptyWithCapacity numNamed
    for _ in [:numNamed] do
      let nameIdx := (← _root_.Ixon.getTagN 0).value.toNat
      let constRank := (← _root_.Ixon.getTagN 0).value.toNat
      let _hint ← _root_.Ixon.getTagN 0
      let metaLen := (← _root_.Ixon.getTagN 0).value.toNat
      let _skip ← _root_.Ixon.getBytes metaLen
      if let (some nm, some addr) := (nameRev[nameIdx]?, constOrder[constRank]?) then
        out := out.insert nm (bytesToHex addr.hash)
    return out
  match parseMeta.run { bytes := env.metadata, idx := 0 } with
  | .ok m _ => .ok m
  | .error e _ => .error s!"extractNamedMap: {e}"

/-- Freeze a Lean file with `ix compile`, resolve `ix/compile-equations/2` names directly
from the `.ixe` §4/§5 tables, emit an `ixcc/k1-equations/1` sidecar, and run `Recheck.ingress`. -/
private def freezeToRecheckInput (ixBin : String) (leanFile : FilePath) (logs : FilePath)
    (stem rootConst : String) (extraEnv : Array (String × Option String) := #[]) :
    IO (Std.HashMap String String × Recheck.Input) := do
  let ixe := logs / s!"{stem}.ixe"
  let eqs := logs / s!"{stem}.eq.json"
  runIxCompile ixBin leanFile ixe eqs rootConst extraEnv
  let bytes ← IO.FS.readBinFile ixe
  let namedMap ← IO.ofExcept (extractNamedMap bytes)
  let rawJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let getStr (j : Lean.Json) (k : String) : IO String :=
    IO.ofExcept ((j.getObjValAs? String k).mapError fun e => s!"{stem}.eq.json missing {k}: {e}")
  let getArr (j : Lean.Json) (k : String) : IO (Array Lean.Json) :=
    IO.ofExcept ((j.getObjValAs? (Array Lean.Json) k).mapError fun e => s!"{stem}.eq.json missing {k}: {e}")
  let fmt ← getStr rawJson "format"
  if fmt != "ix/compile-equations/2" then
    throw (IO.userError s!"FAIL WireTests: {stem}: unexpected ix equations format {fmt}")
  let eqArr ← getArr rawJson "equations"
  let thmArr ← getArr rawJson "theorems"
  let resolve (nm : String) : IO String := do
    match namedMap[nm]? with
    | some a => pure a
    | none => throw (IO.userError s!"FAIL WireTests: {stem}: name `{nm}` absent from .ixe §5 table")
  let rootAddr ← resolve rootConst
  let mut eqRows : Array Lean.Json := #[]
  for p in eqArr do
    let d ← getStr p "definition"
    let e ← getStr p "equation"
    let da ← resolve d
    let ea ← resolve e
    eqRows := eqRows.push (Lean.Json.mkObj [
      ("definition", .str d), ("definition_address", .str da),
      ("equation", .str e), ("equation_address", .str ea)
    ])
  let mut thmRows : Array Lean.Json := #[]
  for t in thmArr do
    let k ← getStr t "kind"
    let s ← getStr t "subject"
    let n ← getStr t "theorem"
    let sa ← resolve s
    let na ← resolve n
    thmRows := thmRows.push (Lean.Json.mkObj [
      ("kind", .str k), ("subject", .str s), ("subject_address", .str sa),
      ("theorem", .str n), ("theorem_address", .str na)
    ])
  let fields : List (String × Lean.Json) :=
    [ ("format", .str "ixcc/k1-equations/1"),
      ("source", .str leanFile.toString),
      ("roots", .arr #[Lean.Json.mkObj [("name", .str rootConst), ("address", .str rootAddr)]]),
      ("equations", .arr eqRows) ] ++
    (if thmRows.isEmpty then [] else [("theorems", .arr thmRows)]) ++
    [ ("failures", .arr #[]) ]
  let sidecar := Lean.Json.mkObj fields
  let inp ← IO.ofExcept ((Recheck.ingress bytes sidecar [rootConst]).mapError (·.render))
  return (namedMap, inp)

/-! ## 6. K3 `rbmap_checkpoint`, K4 `array-qsort`, K4 `blake3` (vector `8193`), `BigNat`, Aliasing/COW -/

private def testK3RbmapCheckpoint (ixBin : String) (logs : FilePath) (cnt : IO.Ref Nat) : IO Unit := do
  let srcFile : FilePath := "benchmarks" / "fixtures" / "rbmap_checkpoint" / "RbmapCheckpoint.lean"
  let (_, inp) ← freezeToRecheckInput ixBin srcFile logs "rbmap_cp" "entry"
  let cw ← IO.ofExcept (compileWireFromInput inp (useRep := false))
  let mem : TestShell.Mem := { stack := 512 * 1024, region := 256 * 1024 * 1024 }
  let exe ← writeWireExe logs "k3-rbmap-checkpoint" cw mem
  Session.withSession exe (seconds := some 60) fun s => do
    let _ ← initSession s mem cnt "rbmap_checkpoint"
    let ptr ← callRoot s mem [100000, 10] cnt "rbmap_checkpoint(100000, 10)"
    let p := ptr.toNat
    require cnt (p % 8 == 0 && p ≥ mem.base) "rbmap_checkpoint returns Prod heap cell"
    let f0 := (← Session.readWord s (p + 8)).toNat
    let f1 := (← Session.readWord s (p + 16)).toNat
    require cnt (f0 % 2 == 1 && f1 % 2 == 1 && f0 / 2 == 10001 && f1 / 2 == 10000)
      s!"K3 rbmap_checkpoint(100000, 10) == (10001, 10000) (got ({f0 / 2}, {f1 / 2}))"
  IO.println "PASS WireTests: K3 rbmap_checkpoint(100000, 10) == (10001, 10000) natively on Xeon"

private def testK4ArrayQsort (ixBin : String) (logs : FilePath) (cnt : IO.Ref Nat) : IO Unit := do
  let srcFile : FilePath := "benchmarks" / "fixtures" / "array-qsort" / "ArrayQsort.lean"
  let (_, inp) ← freezeToRecheckInput ixBin srcFile logs "array_qsort" "entry"
  let cw ← IO.ofExcept (compileWireFromInput inp (useRep := true))
  require cnt cw.cert.hasArrays "array-qsort cert has native arrays enabled"
  let mem : TestShell.Mem := { stack := 512 * 1024, region := 64 * 1024 * 1024 }
  let exe ← writeWireExe logs "k4-array-qsort" cw mem
  Session.withSession exe (seconds := some 60) fun s => do
    let bump0 ← initSession s mem cnt "array-qsort(1000)"
    let w ← callRoot s mem [1000] cnt "array-qsort(1000)"
    let bump1 := (← Session.readWord s (mem.base + 24)).toNat
    let used := bump1 - bump0
    require cnt (w.toNat % 2 == 1 && w.toNat / 2 == 1000413603308)
      s!"K4 array-qsort(1000) == 1000413603308 (got {w.toNat / 2})"
    require cnt (used < 4 * 1024 * 1024)
      s!"K4 array-qsort(1000) in-place O(n) heap usage (used {used} bytes)"
    -- Small edge cases
    let _ ← initSession s mem cnt "array-qsort(0)"
    let w0 ← callRoot s mem [0] cnt "array-qsort(0)"
    require cnt (w0.toNat % 2 == 1 && w0.toNat / 2 == 0) s!"array-qsort(0) == 0 (got {w0.toNat / 2})"
  IO.println "PASS WireTests: K4 array-qsort(1000) == 1000413603308 (in-place O(n) heap) natively on Xeon"

private def testK4Blake3 (ixBin : String) (logs : FilePath) (cnt : IO.Ref Nat) : IO Unit := do
  let srcFile : FilePath := "benchmarks" / "fixtures" / "blake3" / "Blake3.lean"
  let (_, inp) ← freezeToRecheckInput ixBin srcFile logs "blake3" "entry"
  let cw ← IO.ofExcept (compileWireFromInput inp (useRep := true))
  require cnt cw.cert.hasArrays "blake3 cert has native arrays enabled"
  let mem : TestShell.Mem := { stack := 512 * 1024, region := 128 * 1024 * 1024 }
  let exe ← writeWireExe logs "k4-blake3" cw mem
  let vectors : List (Nat × String) := [
    (0,    "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"),
    (64,   "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98"),
    (1024, "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7"),
    (1025, "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444"),
    (8193, "bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3b")
  ]
  Session.withSession exe (seconds := some 60) fun s => do
    for (n, expectedHex) in vectors do
      let _ ← initSession s mem cnt s!"blake3({n})"
      let ptr ← callRoot s mem [n] cnt s!"blake3({n})"
      let p := ptr.toNat
      require cnt (p % 8 == 0 && p ≥ mem.base) s!"blake3({n}) returns ByteArray ptr"
      let hdr := (← Session.readWord s p).toNat
      let tag := (hdr >>> 16) &&& 0xFFFF
      let sz := (← Session.readWord s (p + 8)).toNat
      require cnt (tag == tagByteArray && sz == 32)
        s!"blake3({n}) tag={tag} (expect {tagByteArray}), size={sz} (expect 32)"
      let digest ← Session.read s (p + 24) 32
      let gotHex := bytesToHex digest
      require cnt (gotHex == expectedHex)
        s!"K4 blake3({n}) == {expectedHex} (got {gotHex})"
  IO.println "PASS WireTests: K4 blake3 official vectors (0, 64, 1024, 1025, 8193) natively on Xeon"

private def bigNatSmokeSource : String :=
"import IxCC.BigNat.Linear
import IxCC.BigNat.Mul
import IxCC.BigNat.Div

def aLimbs : Array UInt64 := #[0xFFFFFFFFFFFFFFFE, 0x8000000000000001, 0x0000000000000003]
def bLimbs : Array UInt64 := #[0x0000000000000005, 0x9000000000000002]

def entry (mode : Nat) : Array UInt64 :=
  if mode == 0 then IxCC.BigNat.add aLimbs bLimbs
  else if mode == 1 then IxCC.BigNat.mul aLimbs bLimbs
  else if mode == 2 then (IxCC.BigNat.divMod (IxCC.BigNat.mul aLimbs bLimbs) bLimbs).1
  else (IxCC.BigNat.divMod (IxCC.BigNat.add (IxCC.BigNat.mul aLimbs bLimbs) #[42]) bLimbs).2
"

private def testBigNatLimbArray (ixBin : String) (logs : FilePath) (cnt : IO.Ref Nat) : IO Unit := do
  let leanFile := logs / "BigNatWireSmoke.lean"
  IO.FS.writeFile leanFile bigNatSmokeSource
  let cwd ← IO.currentDir
  let buildLean := (cwd / ".lake" / "build" / "lib" / "lean").toString
  let curLp := (← IO.getEnv "LEAN_PATH").getD ""
  let lp := if curLp.isEmpty then buildLean else s!"{buildLean}:{curLp}"
  let (namedMap, inp) ← freezeToRecheckInput ixBin leanFile logs "bignat_smoke" "entry" #[("LEAN_PATH", some lp)]
  -- Resolve IxCC.BigNat.LimbOps + Prod.mk pins from the named `.ixe` §5 table
  let limbNames : List (String × Src.LimbOp) := [
    ("IxCC.BigNat.addCarry64", .addCarry64),
    ("IxCC.BigNat.subBorrow64", .subBorrow64),
    ("IxCC.BigNat.mulWide64", .mulWide64),
    ("IxCC.BigNat.divWide64", .divWide64),
    ("IxCC.BigNat.clz64", .clz64)
  ]
  let mut limbPins : List (Src.CId × Src.LimbOp) := []
  for (nm, op) in limbNames do
    if let some hex := namedMap[nm]? then
      if let some addr := parseHexAddr? hex then
        if let some cid := inp.program.lookup addr then
          limbPins := limbPins ++ [(cid, op)]
  let prodKey : Option Key.CtorKey :=
    (namedMap["Prod.mk"]?.bind parseHexAddr?).bind fun addr =>
      (inp.program.lookup addr).map Key.CtorKey.src
  let cw ← IO.ofExcept (compileWireFromInput inp limbPins prodKey (kindOverride := none) (useRep := true))
  require cnt (cw.info.arrayKind == .limbs) "BigNat smoke auto-detected ArrayRepKind.limbs"
  require cnt cw.cert.hasArrays "BigNat smoke cert has native arrays enabled"
  let aL : Array UInt64 := #[0xFFFFFFFFFFFFFFFE, 0x8000000000000001, 0x0000000000000003]
  let bL : Array UInt64 := #[0x0000000000000005, 0x9000000000000002]
  let expected : List (Nat × Array UInt64) := [
    (0, IxCC.BigNat.add aL bL),
    (1, IxCC.BigNat.mul aL bL),
    (2, (IxCC.BigNat.divMod (IxCC.BigNat.mul aL bL) bL).1),
    (3, (IxCC.BigNat.divMod (IxCC.BigNat.add (IxCC.BigNat.mul aL bL) #[42]) bL).2)
  ]
  let mem : TestShell.Mem := { stack := 262144, region := 32 * 1024 * 1024 }
  let exe ← writeWireExe logs "bignat-limb-smoke" cw mem
  Session.withSession exe (seconds := some 60) fun s => do
    for (mode, expArr) in expected do
      let _ ← initSession s mem cnt s!"BigNat mode {mode}"
      let ptr ← callRoot s mem [mode] cnt s!"BigNat mode {mode}"
      let p := ptr.toNat
      require cnt (p % 8 == 0 && p ≥ mem.base) s!"BigNat mode {mode} returns LimbArray ptr"
      let hdr := (← Session.readWord s p).toNat
      let tag := (hdr >>> 16) &&& 0xFFFF
      let sz := (← Session.readWord s (p + 8)).toNat
      require cnt (tag == tagLimbArray && sz == expArr.size)
        s!"BigNat mode {mode} tag={tag} (expect {tagLimbArray}), size={sz} (expect {expArr.size})"
      for (limb, idx) in expArr.toList.zipIdx do
        let got := ← Session.readWord s (p + 24 + 8 * idx)
        require cnt (got == limb)
          s!"BigNat mode {mode} limb[{idx}]: got {got}, expected {limb}"
  IO.println "PASS WireTests: IxCC.BigNat.{add, mul, divMod} on unboxed Array UInt64 (tag=0x7F03) natively on Xeon"

private def aliasingCowSource : String :=
"@[noinline] def idArr (a : Array Nat) : Array Nat := a

def entry (mode : Nat) : Nat :=
  if mode == 0 then
    -- Shared Array COW
    let a := #[10, 20, 30]
    let b := a.set! 1 99
    a[1]! * 1000 + b[1]!
  else if mode == 1 then
    -- Escaped alias via idArr + pop + extract + append
    let a := #[1, 2, 3, 4, 5]
    let b := idArr a
    let c := b.pop
    let d := a.extract 1 4
    let e := #[10] ++ d.extract 0 2 ++ #[40]
    a.size * 10000 + c.size * 1000 + d[2]! * 100 + e[1]! * 10 + e[2]!
  else if mode == 2 then
    -- Nested Array (Array Nat)
    let inner := #[7, 8]
    let outer := #[inner, inner.set! 0 42]
    outer[0]![0]! * 100 + outer[1]![0]!
  else if mode == 3 then
    -- ByteArray shared COW, set!, extract, copySlice
    let b0 := ByteArray.emptyWithCapacity 4 |>.push 1 |>.push 2 |>.push 3 |>.push 4
    let b1 := b0.set! 2 99
    let b2 := b1.extract 1 4
    let b3 := ByteArray.copySlice b0 0 b1 1 2 false
    (b0.get! 2).toNat * 10000 + (b1.get! 2).toNat * 100 + (b2.get! 1).toNat + (b3.get! 1).toNat
  else
    -- Multi-byte UTF-8 String literal byte size
    \"λx. café 🚀\".utf8ByteSize
"

private def testAliasingCow (ixBin : String) (logs : FilePath) (cnt : IO.Ref Nat) : IO Unit := do
  let leanFile := logs / "AliasCowWire.lean"
  IO.FS.writeFile leanFile aliasingCowSource
  let (_, inp) ← freezeToRecheckInput ixBin leanFile logs "alias_cow" "entry"
  let cw ← IO.ofExcept (compileWireFromInput inp (useRep := true))
  require cnt cw.lowered.rodata.isSome "alias-cow lowered with .rodata UTF-8 string"
  let mem : TestShell.Mem := { stack := 262144, region := 16 * 1024 * 1024 }
  let exe ← writeWireExe logs "alias-cow-wire" cw mem
  -- Expected:
  -- mode 0: 20 * 1000 + 99 = 20099
  -- mode 1: a.size=5, c.size=4, d=[2,3,4] so d[2]=4, e=[10,2,3,40] so e[1]=2, e[2]=3 -> 54423
  -- mode 2: 7 * 100 + 42 = 742
  -- mode 3: b0[2]=3, b1[2]=99, b2=[2,99,4] -> b2[1]=99, b3=[1,1,2,4] -> b3[1]=1 -> 30000 + 9900 + 99 + 1 = 40000
  -- mode 4: "λx. café 🚀".utf8ByteSize = 15 (2 + 1 + 1 + 1 + 1 + 1 + 1 + 2 + 1 + 4 = 15)
  let cases : List (Nat × Nat) := [(0, 20099), (1, 54423), (2, 742), (3, 40000), (4, 15)]
  Session.withSession exe (seconds := some 30) fun s => do
    for (mode, expected) in cases do
      let _ ← initSession s mem cnt s!"alias-cow({mode})"
      let w ← callRoot s mem [mode] cnt s!"alias-cow({mode})"
      require cnt (w.toNat % 2 == 1 && w.toNat / 2 == expected)
        s!"alias-cow({mode}) == {expected} (got {w.toNat / 2})"
  IO.println "PASS WireTests: Aliasing/COW, nested Array, ByteArray ops & UTF-8 String natively on Xeon"

/-! ## The array analyses run to their fixpoints (`Rt.LowerRep`)

Each program below needs more rounds than the fixed round counts the three analyses ran before
(liveness `min (blocks + 2) 32`, taint `min (blocks + 3) 12`, parameter flags
`min (functions + 1) 16`), whose results on them were partial (a protection missing): the
fixpoint is reached, complete and within the analysis's bound, the totals the lowerings call
return it, and a bound too small is refused (`rt.internal`), never answered with a partial
result. -/

private def psig : Own.PSig := Own.PSig.plain .obj

/-- `n + 1` blocks in a line: block 0 takes `x0`, block `i` jumps to `i + 1`, the last returns
`x0`; liveness carries `x0` back one block per round. -/
private def liveLine (n : Nat) : Cfg.Fun :=
  { key := .const 0 [], sig := default
    blocks := (List.range (n + 1)).map fun i =>
      { params := if i == 0 then [(0, psig)] else []
        term := if i == n then .ret (.var 0) else .jump { target := i + 1 } } }

/-- Block `i` binds `x (i + 1) := x i` and jumps on, the last returns `x n`; taint flows back one
block per round (a round folds the blocks in order). -/
private def taintLine (n : Nat) : Cfg.Fun :=
  { key := .const 0 [], sig := default
    blocks := (List.range (n + 1)).map fun i =>
      if i == n then { term := .ret (.var n) }
      else
        { params := if i == 0 then [(0, psig)] else []
          body := [.bind (i + 1) (.fir (.arg (.var i)))]
          term := .jump { target := i + 1 } } }

/-- `n + 1` functions: `f i x := f (i + 1) x` (a tail call), `f n x := x` (the parameter
escapes); the flag travels back one function per round. -/
private def chainFun (n i : Nat) : Cfg.Fun :=
  { key := .const i [], sig := default
    blocks := [{ params := [(0, psig)]
                 term := if i == n then .ret (.var 0) else .tcall (i + 1) [.var 0] }] }

private def mutChain (n : Nat) : Cfg.Program :=
  { funs := Src.NatMap.ofDense ((List.range (n + 1)).map (chainFun n)), size := n + 1
    exports := [0], ctors := [], known := default }

def testArrayAnalyses (cnt : IO.Ref Nat) : IO Unit := do
  let n := 40
  let fd := liveLine n
  match LowerRep.liveInFix 0 fd with
  | .ok (m, rounds) =>
    require cnt (rounds > min (fd.blocks.length + 2) 32)
      s!"liveness on {n + 1} blocks in a line: {rounds} rounds, not more than the old 32"
    require cnt (rounds ≤ LowerRep.liveInBound fd) s!"liveness: {rounds} rounds past its bound"
    require cnt ((List.range (n + 1)).all fun i => i == 0 || (m.getD i .leaf).contains 0)
      "liveness: x0 not live into every block after the first"
    require cnt (LowerRep.sameSetMap (LowerRep.computeLiveIn fd) m) "computeLiveIn is not the fixpoint"
  | .error e => require cnt false s!"liveness refused: {e.render}"
  match LowerRep.liveInFix 0 fd (fuel := 32) with
  | .error (.internal 0 _) => require cnt true ""
  | _ => require cnt false "liveness within 32 rounds on a line of 41 blocks was not refused"
  let td := taintLine 20
  match LowerRep.taintedFix 0 td .leaf with
  | .ok (t, rounds) =>
    require cnt (rounds > min (td.blocks.length + 3) 12)
      s!"taint along 21 blocks: {rounds} rounds, not more than the old 12"
    require cnt (rounds ≤ LowerRep.taintedBound td) s!"taint: {rounds} rounds past its bound"
    require cnt ((List.range 21).all t.contains) "taint: some x i does not flow to the result"
    require cnt (LowerRep.sameSet (LowerRep.computeTainted td .leaf) t) "computeTainted is not the fixpoint"
  | .error e => require cnt false s!"taint refused: {e.render}"
  match LowerRep.taintedFix 0 td .leaf (fuel := 12) with
  | .error (.internal 0 _) => require cnt true ""
  | _ => require cnt false "taint within 12 rounds along 21 blocks was not refused"
  let P := mutChain 20
  match LowerRep.paramMutFix P {} with
  | .ok (pm, rounds) =>
    require cnt (rounds > min (P.size + 1) 16)
      s!"parameter flags along 21 functions: {rounds} rounds, not more than the old 16"
    require cnt (rounds ≤ LowerRep.paramMutBound P {}) s!"parameter flags: {rounds} rounds past their bound"
    require cnt ((List.range 21).all fun f => pm.getD f [] == [true])
      "parameter flags: some function's escaping parameter is not flagged"
    require cnt (LowerRep.sameFlags (LowerRep.computeParamMutates P {}) pm)
      "computeParamMutates is not the fixpoint"
  | .error e => require cnt false s!"parameter flags refused: {e.render}"
  match LowerRep.paramMutFix P {} (fuel := 16) with
  | .error (.internal _ _) => require cnt true ""
  | _ => require cnt false "parameter flags within 16 rounds along 21 functions were not refused"
  -- the guard the lowerings' callers run: an array program, every analysis to its fixpoint
  let arrCert : Fir.Rep.Cert := { arrayMkKey := some (Key.CtorKey.src 0) }
  require cnt (LowerRep.checkArrayAnalyses arrCert P).isOk "checkArrayAnalyses refused converging analyses"
  let rounds := fun (r : Except Rt.Error Nat) => match r with | .ok k => toString k | .error _ => "-"
  IO.println s!"PASS WireTests: array analyses reach their fixpoints past the old round counts \
    (liveness {rounds ((·.2) <$> LowerRep.liveInFix 0 fd)} > 32, \
    taint {rounds ((·.2) <$> LowerRep.taintedFix 0 td .leaf)} > 12, \
    parameter flags {rounds ((·.2) <$> LowerRep.paramMutFix P {})} > 16) and refuse a bound too small"

/-! ## Entry Point -/

def run (logs : FilePath) (cliIx : Option String := none) (requireIx : Bool := false) : IO Nat := do
  IO.FS.createDirAll logs
  let cnt ← IO.mkRef 0
  testArrayAnalyses cnt
  testWireProcs logs cnt
  testRodataElf cnt
  testCommittedDeclines logs cnt
  match ← findIx cliIx with
  | some ixBin =>
    IO.println s!"WireTests: using ix binary {ixBin}"
    testK3RbmapCheckpoint ixBin logs cnt
    testK4ArrayQsort ixBin logs cnt
    testK4Blake3 ixBin logs cnt
    testBigNatLimbArray ixBin logs cnt
    testAliasingCow ixBin logs cnt
  | none =>
    if requireIx then
      throw (IO.userError "FAIL WireTests: --require-ix set but no `ix` binary found")
    IO.println "WireTests: skipping external `ix` K3/K4/BigNat freeze tests (`ix` not found; pass `--ix <path>` or `IX_BIN`)"
  cnt.get

end IxCCTests.Array.WireTests
