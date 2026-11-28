import IxCCTests.Exe.Session
import IxCCTests.Array.Emit
import IxCC.Rt.Rc.Array.Layout
import IxCC.BigNat.Basic

/-! # Native Xeon x86-64 Controls for Contiguous Arrays, ByteArrays, and LimbArrays

Runs the compiled array runtime ELF object (`Emit.compileObject`) natively on
the host x86-64 CPU inside `IxCCTests.Exe.TestShell` (seccomp-confined, zero C):
* 71-class `cx_arr_class_for` & `cx_arr_class_words` + heap error boundaries,
* Boxed `Array α` unique in-place mutation (same pointer, zero bump growth) vs
  shared copy-on-write, amortized 2x growth + old-shell recycling, `extract`,
  `copy_slice` (including self-aliasing & extension), and OOB trap (status 4),
* Unified iterative `cx_arr_dec` on nested `Array (Array Nat)`, mixed
  `Array (Ctor (ByteArray, LimbArray))`, O(1) `scan=0` free, and immortal
  static header (`rc = 0x80000000`) no-op,
* Packed `ByteArray` / UTF-8 `String` round-trips across word boundaries & 2x growth,
* Unboxed `Array UInt64` / `BigNat` (`≥ 2^63`, full 64-bit raw limbs including
  even limbs!) round-trips and O(1) reclamation. -/

set_option autoImplicit false

namespace IxCCTests.Array.NativeControls

open IxCC
open IxCC.Rt.Rc.Array
open IxCCTests.Exe

-- Export indices matching `IxCCTests.Array.Emit.exports`
def fnInit := 0
def fnInc := 1
def fnDec := 2
def fnClassFor := 3
def fnClassWords := 4
def fnAllocCell := 5
def fnEmptyBoxed := 6
def fnEmptyLimbs := 7
def fnByteEmpty := 8
def fnSize := 9
def fnCap := 10
def fnGet := 11
def fnByteGet := 12
def fnSetBoxed := 13
def fnSetLimbs := 14
def fnPushBoxed := 15
def fnPushLimbs := 16
def fnPopBoxed := 17
def fnPopLimbs := 18
def fnExtractBoxed := 19
def fnExtractLimbs := 20
def fnCopySliceBoxed := 21
def fnCopySliceLimbs := 22
def fnByteSet := 23
def fnBytePush := 24
def fnBytePop := 25
def fnByteExtract := 26
def fnByteCopySlice := 27
def fnAllocCtor2 := 28

def mem : TestShell.Mem := { stack := 65536, region := 262144 }
def regionSize : Nat := 262144
def testBudget : Nat := 65536 - 4096

structure Env where
  s : Session.Session
  base : Nat
  assertions : IO.Ref Nat
  out : IO.Ref (Array String)

def require (e : Env) (c : Bool) (label : String) : IO Unit := do
  e.assertions.modify (· + 1)
  unless c do throw (IO.userError s!"FAIL NativeControls: {label}")

def emit (e : Env) (line : String) : IO Unit := e.out.modify (·.push line)

def contextAt (e : Env) (offset : Int) : Nat := Int.toNat (e.base + 64 + offset)

def ctxField (e : Env) (offset : Int) : IO Nat :=
  return (← Session.readWord e.s (contextAt e offset)).toNat

def head (e : Env) (cls : Nat) : IO Nat := ctxField e (8 * cls)

def word (e : Env) (p : Nat) : IO Nat :=
  return (← Session.readWord e.s p).toNat

def putword (e : Env) (p v : Nat) : IO Unit :=
  Session.writeWord e.s p v

def invoke (e : Env) (fn : Nat) (args : List Nat) : IO (Nat × Nat) := do
  let (rax, rdx, ok) ← Session.call e.s fn (e.base :: args)
  require e ok "native callee-saved registers & rsp preserved"
  return (rax.toNat, rdx.toNat)

def ok (e : Env) (fn : Nat) (args : List Nat) : IO Nat := do
  let (rax, rdx) ← invoke e fn args
  require e (rax == 0) s!"native call fn={fn} succeeds (got status {rax})"
  return rdx

def expectStatus (e : Env) (fn : Nat) (args : List Nat) (expected : Nat) (label : String) : IO Unit := do
  let (rax, _) ← invoke e fn args
  require e (rax == expected) s!"{label} (expected status {expected}, got {rax})"

def freeList (e : Env) (c : Nat) (maxLen : Nat := 200) : IO (List Nat) := do
  let mut out := #[]
  let mut a ← head e c
  for _ in List.range maxLen do
    if a == 0 then break
    out := out.push a
    a ← word e a
  return out.toList

def fresh (e : Env) (capacity : Nat := 131072) : IO Nat := do
  putword e (contextAt e (-48)) testBudget
  let (rax, _) ← invoke e fnInit [regionSize, testBudget]
  require e (rax == 0) "cx_init succeeds"
  let start ← ctxField e (-40)
  require e (start % 64 == 0 && start + capacity ≤ e.base + regionSize) "arena aligned and in range"
  putword e (contextAt e (-32)) (start + capacity)
  for c in List.range' 1 71 do
    require e ((← head e c) == 0) s!"free head {c} initially 0"
  return start

/-- 1. Size classes 1..71 and heap failure boundaries natively on Xeon. -/
def testSizeClasses (e : Env) : IO Unit := do
  let _ ← fresh e
  for c in List.range' 1 71 do
    let cw := IxCC.Rt.Rc.classWords c
    let gotW ← ok e fnClassWords [c]
    require e (gotW == cw) s!"native arrClassWords({c}) == {cw}"
    let gotC ← ok e fnClassFor [cw]
    require e (gotC == c) s!"native arrClassFor({cw}) == {c}"
    if c > 1 then
      let prev := IxCC.Rt.Rc.classWords (c - 1)
      let gotLo ← ok e fnClassFor [prev + 1]
      require e (gotLo == c) s!"native arrClassFor({prev + 1}) == {c}"
  expectStatus e fnClassFor [0] 1 "arrClassFor(0) -> heap error (1)"
  expectStatus e fnClassFor [IxCC.Rt.Rc.maxCellWords + 1] 1 "arrClassFor(max+1) -> heap error (1)"
  emit e "PASS native size classes (1..71 + overflow boundaries)"

/-- 2. Boxed `Array α`: unique in-place mutation, shared COW, 2x growth, extract, copySlice, OOB trap. -/
def testBoxedArrays (e : Env) : IO Unit := do
  let _ ← fresh e
  -- Allocate empty boxed array with cap >= 4 (4 + 3 = 7 words -> class 7 -> cap 4)
  let a0 ← ok e fnEmptyBoxed [4]
  require e ((← ok e fnSize [a0]) == 0 && (← ok e fnCap [a0]) == 4) "empty boxed(4): size 0, cap 4"
  let bump0 ← ctxField e (-40)
  -- Push 4 immediates uniquely: MUST stay in-place at `a0` with ZERO bump advancement!
  let mut a := a0
  for j in List.range 4 do
    let a' ← ok e fnPushBoxed [a, 2 * (j + 10) + 1]
    require e (a' == a0) s!"unique boxed push #{j} stays in place"
    a := a'
  require e ((← ctxField e (-40)) == bump0) "unique boxed pushes within cap: zero bump growth"
  require e ((← ok e fnSize [a]) == 4) "boxed size == 4"
  -- Unique in-place set: stays at `a0`, zero allocation
  let aSet ← ok e fnSetBoxed [a, 2, 2 * 999 + 1]
  require e (aSet == a0 && (← ctxField e (-40)) == bump0) "unique boxed set in place"
  require e ((← ok e fnGet [aSet, 2]) == 2 * 999 + 1) "unique boxed set updated slot 2"
  -- OOB get traps with status 4
  expectStatus e fnGet [aSet, 4] 4 "boxed arrGet OOB traps (status 4)"
  -- Shared copy-on-write set: `inc` before `set` -> new cell, original untouched, original rc back to 0!
  discard <| ok e fnInc [aSet]
  let aCow ← ok e fnSetBoxed [aSet, 2, 2 * 777 + 1]
  require e (aCow != aSet) "shared boxed set allocates COW copy"
  require e ((← ok e fnGet [aSet, 2]) == 2 * 999 + 1) "original boxed array untouched after COW set"
  require e ((← ok e fnGet [aCow, 2]) == 2 * 777 + 1) "COW boxed array has new value"
  require e ((← ok e fnGet [aCow, 0]) == 2 * 10 + 1) "COW boxed array copied slot 0"
  -- Check original `aSet` is back to unique (rc == 0 in high 32 bits of header)
  let hdrOrig ← word e aSet
  require e ((hdrOrig / 2 ^ 32) == 0) "original boxed array RC decremented back to unique"
  -- Shared COW push & pop
  discard <| ok e fnInc [aCow]
  let aCowPush ← ok e fnPushBoxed [aCow, 2 * 55 + 1]
  require e (aCowPush != aCow && (← ok e fnSize [aCow]) == 4 && (← ok e fnSize [aCowPush]) == 5)
    "shared boxed push triggers COW and grows"
  require e ((← ok e fnGet [aCowPush, 4]) == 2 * 55 + 1) "COW push appended element"
  -- Unique pop in place
  let bumpPrePop ← ctxField e (-40)
  let aPop ← ok e fnPopBoxed [aCowPush]
  require e (aPop == aCowPush && (← ctxField e (-40)) == bumpPrePop && (← ok e fnSize [aPop]) == 4)
    "unique boxed pop in place"
  -- Amortized 2x growth: push 100 elements uniquely and verify old shells recycled onto free lists!
  let mut g ← ok e fnEmptyBoxed [0]
  for j in List.range 100 do
    g ← ok e fnPushBoxed [g, 2 * j + 1]
  require e ((← ok e fnSize [g]) == 100 && (← ok e fnCap [g]) ≥ 100) "boxed 2x growth to 100 elements"
  for j in List.range 100 do
    require e ((← ok e fnGet [g, j]) == 2 * j + 1) s!"boxed growth elem[{j}] exact"
  -- Old empty class-3 shell must have been recycled onto free list 3!
  require e (!(← freeList e 3).isEmpty) "boxed 2x growth recycled old class-3 shell"
  -- Extract slice [10, 25)
  let sub ← ok e fnExtractBoxed [g, 10, 25]
  require e ((← ok e fnSize [sub]) == 15) "boxed extract size 15"
  for j in List.range 15 do
    require e ((← ok e fnGet [sub, j]) == 2 * (10 + j) + 1) s!"boxed extract elem[{j}]"
  -- CopySlice: unique in-place overwrite, extending, and self-aliasing
  let dst0 ← ok e fnEmptyBoxed [20]
  let mut dst := dst0
  for j in List.range 5 do
    dst ← ok e fnPushBoxed [dst, 2 * (500 + j) + 1]
  let bumpPreCs ← ctxField e (-40)
  let dst1 ← ok e fnCopySliceBoxed [sub, 2, dst, 3, 6]
  require e (dst1 == dst0 && (← ctxField e (-40)) == bumpPreCs && (← ok e fnSize [dst1]) == 9)
    "unique boxed copySlice extends in place within cap"
  require e ((← ok e fnGet [dst1, 2]) == 2 * 502 + 1) "boxed copySlice preserves prefix"
  require e ((← ok e fnGet [dst1, 3]) == 2 * 12 + 1 && (← ok e fnGet [dst1, 8]) == 2 * 17 + 1)
    "boxed copySlice wrote slice [12..17]"
  -- Self-aliasing copySlice (src == dest, overlapping upward shift)
  let dstSelf ← ok e fnCopySliceBoxed [dst1, 0, dst1, 2, 4]
  require e ((← ok e fnGet [dstSelf, 2]) == 2 * 500 + 1 && (← ok e fnGet [dstSelf, 5]) == 2 * 12 + 1)
    "boxed self-aliasing copySlice matches snapshot semantics"
  -- Release all arrays
  for arr in [aSet, aCow, aPop, g, sub, dstSelf] do
    discard <| ok e fnDec [arr]
  emit e "PASS native boxed Array (in-place, COW, 2x growth, extract, copySlice, OOB trap)"

/-- 3. Nested iterative `arrDec` reclamation (boxed arrays of arrays + ctors + ByteArray + LimbArray)
and immortal static header no-op. -/
def testIterativeRelease (e : Env) : IO Unit := do
  let start ← fresh e
  -- Build outer boxed Array holding: [innerBoxedArray, ctor(byteArr, limbArr), sharedInner]
  let inner ← ok e fnEmptyBoxed [2]
  let inner ← ok e fnPushBoxed [inner, 101]
  let inner ← ok e fnPushBoxed [inner, 103]
  let ba ← ok e fnByteEmpty [8]
  let ba ← ok e fnBytePush [ba, 0x41]
  let ba ← ok e fnBytePush [ba, 0x42]
  let la ← ok e fnEmptyLimbs [2]
  -- Put an EVEN 64-bit raw limb (0x00000000deadbeef0 — low bit 0! Must NOT be dereferenced by arrDec!)
  let la ← ok e fnPushLimbs [la, 0xdeadbeef0]
  let la ← ok e fnPushLimbs [la, 0]
  let pair ← ok e fnAllocCtor2 []
  putword e (pair + 8) ba
  putword e (pair + 16) la
  let shared ← ok e fnEmptyBoxed [2]
  let shared ← ok e fnPushBoxed [shared, 77]
  discard <| ok e fnInc [shared] -- rc = 1 (2 refs)
  let outer ← ok e fnEmptyBoxed [4]
  let outer ← ok e fnPushBoxed [outer, inner]
  let outer ← ok e fnPushBoxed [outer, pair]
  let outer ← ok e fnPushBoxed [outer, shared]
  let bumpFull ← ctxField e (-40)
  -- Release `outer`: must iteratively reclaim `outer`, `inner`, `pair`, `ba`, `la`,
  -- and decrement `shared` from 2 -> 1 without freeing `shared`!
  discard <| ok e fnDec [outer]
  require e ((← word e shared) / 2 ^ 32 == 0) "shared child decremented from 2 -> 1"
  require e ((← ok e fnGet [shared, 0]) == 77) "shared child still live and intact"
  -- Verify recycled cells are reused with ZERO bump advancement!
  let reOuter ← ok e fnEmptyBoxed [4]
  let reInner ← ok e fnEmptyBoxed [2]
  let reLa ← ok e fnEmptyLimbs [2]
  let reBa ← ok e fnByteEmpty [8]
  let rePair ← ok e fnAllocCtor2 []
  putword e (rePair + 8) 1
  putword e (rePair + 16) 1
  require e ((← ctxField e (-40)) == bumpFull) "full nested graph reclaimed and reused with ZERO bump growth"
  -- Release everything including `shared`
  for p in [shared, reOuter, reInner, reLa, reBa, rePair] do
    discard <| ok e fnDec [p]
  -- Immortal static cell no-op check: craft a static boxed array header (rc = 0x80000000) in region
  let staticAddr := start + 65536
  let staticHdr : Nat := 0xFF + 65536 * 0x7F01 + 2 ^ 32 * 0x80000000
  putword e staticAddr staticHdr
  putword e (staticAddr + 8) 2
  putword e (staticAddr + 16) 2
  putword e (staticAddr + 24) 11
  putword e (staticAddr + 32) 13
  discard <| ok e fnDec [staticAddr]
  require e ((← word e staticAddr) == staticHdr) "arrDec leaves immortal static cell header unchanged"
  require e ((← ok e fnSize [staticAddr]) == 2 && (← ok e fnGet [staticAddr, 1]) == 13)
    "static cell readable after arrDec"
  emit e "PASS native iterative arrDec (nested arrays + ctors + scan=0 + immortal static no-op)"

/-- 4. Packed `ByteArray` & UTF-8 `String` round-trips natively on Xeon. -/
def testByteArraysAndStrings (e : Env) : IO Unit := do
  let _ ← fresh e
  let msg := "Hello, IxCC UTF-8: λ→∀! 0123456789abcdef"
  let utf8 := msg.toByteArray
  -- Start with tiny capacity 4 bytes so pushing triggers multiple 2x growths across word boundaries!
  let mut ba ← ok e fnByteEmpty [4]
  require e ((← ok e fnSize [ba]) == 0 && (← ok e fnCap [ba]) == 8) "byteArrEmpty(4) -> class 4 -> cap 8 bytes"
  let bump0 ← ctxField e (-40)
  for j in List.range 8 do
    let ba' ← ok e fnBytePush [ba, utf8[j]!.toNat]
    require e (ba' == ba) s!"unique byte push #{j} stays in place"
    ba := ba'
  require e ((← ctxField e (-40)) == bump0) "first 8 byte pushes: zero bump growth"
  for j in List.range' 8 (utf8.size - 8) do
    ba ← ok e fnBytePush [ba, utf8[j]!.toNat]
  require e ((← ok e fnSize [ba]) == utf8.size) "byte array exact UTF-8 byte length"
  -- Verify via `cx_byte_get` AND raw memory read + `String.fromUTF8?`
  for j in List.range utf8.size do
    require e ((← ok e fnByteGet [ba, j]) == utf8[j]!.toNat) s!"byteArrGet[{j}] matches UTF-8"
  let rawBytes ← Session.read e.s (ba + 24) utf8.size
  require e (String.fromUTF8? rawBytes == some msg) "raw ByteArray payload decodes to exact UTF-8 String"
  -- Shared COW `byteArrSet`
  discard <| ok e fnInc [ba]
  let baCow ← ok e fnByteSet [ba, 0, 'X'.toNat]
  require e (baCow != ba && (← ok e fnByteGet [ba, 0]) == 'H'.toNat && (← ok e fnByteGet [baCow, 0]) == 'X'.toNat)
    "shared byteArrSet COW preserves original and mutates copy"
  -- Unique in-place `byteArrSet` & `byteArrPop`
  let bumpPre ← ctxField e (-40)
  let baSet ← ok e fnByteSet [baCow, 1, 'Y'.toNat]
  require e (baSet == baCow && (← ctxField e (-40)) == bumpPre && (← ok e fnByteGet [baSet, 1]) == 'Y'.toNat)
    "unique byteArrSet in place"
  let baPop ← ok e fnBytePop [baSet]
  require e (baPop == baSet && (← ctxField e (-40)) == bumpPre && (← ok e fnSize [baPop]) == utf8.size - 1)
    "unique byteArrPop in place"
  -- `byteArrExtract` & `byteArrCopySlice`
  let sub ← ok e fnByteExtract [ba, 7, 11] -- "IxCC"
  let subRaw ← Session.read e.s (sub + 24) 4
  require e (String.fromUTF8? subRaw == some "IxCC") "byteArrExtract slice == \"IxCC\""
  let dst ← ok e fnByteEmpty [16]
  let mut d := dst
  for b in "----".toByteArray.toList do
    d ← ok e fnBytePush [d, b.toNat]
  let d1 ← ok e fnByteCopySlice [sub, 0, d, 2, 4] -- "--IxCC"
  require e (d1 == dst && (← ok e fnSize [d1]) == 6) "unique byteArrCopySlice extends in place"
  let dRaw ← Session.read e.s (d1 + 24) 6
  require e (String.fromUTF8? dRaw == some "--IxCC") "byteArrCopySlice payload == \"--IxCC\""
  -- OOB byteArrGet traps (status 4)
  expectStatus e fnByteGet [d1, 6] 4 "byteArrGet OOB traps (status 4)"
  for p in [ba, baPop, sub, d1] do
    discard <| ok e fnDec [p]
  emit e "PASS native ByteArray & UTF-8 String (packed .w8, growth, COW, extract, copySlice)"

/-- 5. Unboxed `Array UInt64` / `BigNat` limb buffer round-trips natively on Xeon. -/
def testLimbArraysAndBigNat (e : Env) : IO Unit := do
  let _ ← fresh e
  let cases : List Nat := [
    2 ^ 63,
    2 ^ 64 - 1,
    (1 <<< 128) + 42,
    (0xfedcba9876543210 <<< 192) + (0x0000000000000000 <<< 128) + (0x8000000000000000 <<< 64) + 2
  ]
  for n in cases do
    let bn := BigNat.ofNat n
    let mut la ← ok e fnEmptyLimbs [1]
    for limb in bn.toList do
      la ← ok e fnPushLimbs [la, limb.toNat]
    require e ((← ok e fnSize [la]) == bn.size) "LimbArray size matches BigNat limb count"
    -- Read back raw 64-bit limbs and reconstruct Nat via BigNat.toNat
    let mut back : Array UInt64 := #[]
    for j in List.range bn.size do
      let w ← ok e fnGet [la, j]
      back := back.push (UInt64.ofNat w)
    require e (BigNat.toNat back == n) "LimbArray -> BigNat.toNat exact round-trip"
    -- Shared COW set on limb 0 + unique in-place set + pop + extract + copySlice
    discard <| ok e fnInc [la]
    let laCow ← ok e fnSetLimbs [la, 0, 0x1122334455667788]
    require e (laCow != la && (← ok e fnGet [la, 0]) == bn[0]!.toNat &&
        (← ok e fnGet [laCow, 0]) == 0x1122334455667788) "LimbArray shared COW set"
    let bumpPre ← ctxField e (-40)
    let laSet ← ok e fnSetLimbs [laCow, 0, 0xabcdef0123456789]
    require e (laSet == laCow && (← ctxField e (-40)) == bumpPre &&
        (← ok e fnGet [laSet, 0]) == 0xabcdef0123456789) "LimbArray unique in-place set"
    let sub ← ok e fnExtractLimbs [la, 0, bn.size]
    require e ((← ok e fnSize [sub]) == bn.size && (← ok e fnGet [sub, 0]) == bn[0]!.toNat)
      "LimbArray extract round-trip"
    let cs ← ok e fnCopySliceLimbs [la, 0, laSet, 0, bn.size]
    require e ((← ok e fnGet [cs, 0]) == bn[0]!.toNat) "LimbArray copySlice restores limb 0"
    let laPop ← ok e fnPopLimbs [cs]
    require e ((← ok e fnSize [laPop]) == bn.size - 1) "LimbArray unique pop"
    -- O(1) scan=0 free on all cells (even limbs with low bit 0 must not crash!)
    for p in [la, laPop, sub] do
      discard <| ok e fnDec [p]
  emit e "PASS native LimbArray / BigNat >= 2^63 (raw 64-bit limbs, COW, growth, O(1) free)"

/-- Compile, build standalone seccomp ELF executable, and run all native Xeon controls. -/
def run (logs : System.FilePath) : IO Nat := do
  IO.FS.createDirAll logs
  let objBytes ← IO.ofExcept Emit.compileObject
  let objPath := logs / "array_rt.o"
  IO.FS.writeBinFile objPath objBytes
  let exePath := logs / "array-native-controls"
  match TestShell.writeExe mem Emit.exports objBytes with
  | .error err => throw (IO.userError s!"FAIL TestShell.writeExe(array_rt): {err}")
  | .ok exeBytes =>
    IO.FS.writeBinFile exePath exeBytes
    IO.setAccessRights exePath { user := { read := true, write := true, execution := true } }
  let (lines, n) ← Session.withSession exePath (seconds := some 30) fun s => do
    let e : Env := { s, base := mem.base, assertions := ← IO.mkRef 0, out := ← IO.mkRef #[] }
    require e mem.ok "guarded native stack & region"
    testSizeClasses e
    testBoxedArrays e
    testIterativeRelease e
    testByteArraysAndStrings e
    testLimbArraysAndBigNat e
    let n ← e.assertions.get
    emit e s!"PASS NativeControls (host x86-64 Xeon): {n} native assertions"
    return ((← e.out.get).toList, n)
  for l in lines do IO.println l
  return n

end IxCCTests.Array.NativeControls
