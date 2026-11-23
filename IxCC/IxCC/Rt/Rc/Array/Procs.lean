import IxCC.Rt.Rc.Array.Layout
import IxCC.Rt.Rc.Procs
import IxCC.Lir.SplitEdges
import IxCC.Lir.WellFormed

/-! # Lir Runtime Procedures for Contiguous Arrays, ByteArrays, and LimbArrays

Implements the complete native contiguous array runtime in Lir, sharing the
71-class allocator and RC header conventions of `IxCC.Rt.Rc.Gen` and handling
immortal read-only `.rodata` cells from `IxCC.X86.ELFRodata`:

* Unified iterative release (`arrDec`): O(1) auxiliary stack, zero recursion;
  handles immediates, immortal static `.rodata` cells (`rc < 0`), shared cells,
  O(1) recycling for `scan = 0` (`ByteArray`, `LimbArray`, scalar ctors) and
  empty boxed arrays, plus iterative pointer-reversal traversal for both boxed
  arrays (`scan = 0xFF`, count in `+8`, parent link in `+16`) and ordinary
  constructors (`1 ≤ scan ≤ 254`, count in `+4`, parent link in `+8`).
* O(1) size-class arithmetic (`arrClassFor` via `bsr64`, `arrClassWords`).
* Unified cell allocator (`arrAllocCell`) + typed constructors
  (`arrEmptyCapBoxed`, `arrEmptyCapLimbs`, `byteArrEmptyCap`).
* O(1) queries (`arrSize`, `arrCap`, `arrGet`, `byteArrGet`).
* Unique in-place / shared copy-on-write mutations:
  `arrSetBoxed`, `arrSetLimbs`, `arrPushBoxed`, `arrPushLimbs` (amortized 2x
  growth moving elements with zero inc/dec and O(1) old-shell recycling when
  unique!), `arrPopBoxed`, `arrPopLimbs`, `arrExtractBoxed`, `arrExtractLimbs`,
  `arrCopySliceBoxed`, `arrCopySliceLimbs`, and packed `.w8` `ByteArray`
  counterparts (`byteArrSet`, `byteArrPush`, `byteArrPop`, `byteArrExtract`,
  `byteArrCopySlice`). -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt (bumpOff limitOff)
open IxCC.Rt.Rc (maxClass classBytes maxCellWords)
open IxCC.Rt.Rc.Procs (v i to cellAddr ctx)

/-! ## Function table indices in `arrayRuntimeProgram` -/

def fnInc : FunId := 0
def fnDec : FunId := 1
def fnClassFor : FunId := 2
def fnClassWords : FunId := 3
def fnAllocCell : FunId := 4
def fnEmptyCapBoxed : FunId := 5
def fnEmptyCapLimbs : FunId := 6
def fnByteEmptyCap : FunId := 7
def fnSize : FunId := 8
def fnCap : FunId := 9
def fnGetWord : FunId := 10
def fnByteGet : FunId := 11
def fnSetBoxed : FunId := 12
def fnSetLimbs : FunId := 13
def fnPushBoxed : FunId := 14
def fnPushLimbs : FunId := 15
def fnPopBoxed : FunId := 16
def fnPopLimbs : FunId := 17
def fnExtractBoxed : FunId := 18
def fnExtractLimbs : FunId := 19
def fnCopySliceBoxed : FunId := 20
def fnCopySliceLimbs : FunId := 21
def fnByteSet : FunId := 22
def fnBytePush : FunId := 23
def fnBytePop : FunId := 24
def fnByteExtract : FunId := 25
def fnByteCopySlice : FunId := 26

/-- Fixed low-32-bit header template `scan + 65536 * tag` (class byte 0, rc 0). -/
def scanTagFixed (k : ArrayKind) : Word :=
  UInt64.ofNat (k.scan + 65536 * k.tag)

theorem scanTagFixed_or_cls {k : ArrayKind} {cls : Nat} (hcls : cls ≤ maxClass) :
    (scanTagFixed k ||| (UInt64.ofNat cls <<< 8)) = arrayHeader k cls 1 := by
  have all : ∀ cls < 72,
      (scanTagFixed k ||| (UInt64.ofNat cls <<< 8)) = arrayHeader k cls 1 := by
    cases k <;> decide
  exact all cls (by unfold maxClass at hcls; omega)

/-- Scaled word element address `[base + index*8 + 24]`. -/
def wordElemAddr (base idx : VReg) : Addr :=
  { base := some (.v base), index := some (idx, .eight), disp := 24 }

/-- Scaled byte element address `[base + index*1 + 24]`. -/
def byteElemAddr (base idx : VReg) : Addr :=
  { base := some (.v base), index := some (idx, .one), disp := 24 }

/-- Context free-list head slot `[ctx + cls*8]`. -/
def ctxHeadAddr (cls : VReg) : Addr :=
  { base := some .ctx, index := some (cls, .eight) }

/-! ## 1. Unified iterative RC release (`arrDec`) -/

/-- Unified iterative release handling immediates, static `.rodata` cells
(`rc < 0`), shared cells (`rc > 0`), `scan = 0` cells (`ByteArray`, `LimbArray`,
scalar ctors), boxed arrays (`scan = 0xFF`), and ordinary constructors
(`1 ≤ scan ≤ 254`) with O(1) stack and zero recursion. -/
def arrDec : Func where
  name := "rt_arr_dec"
  params := [0]
  results := 0
  blocks := #[
    -- 0: start with current = v0, parent = 0
    { term := .jump (to 1 [v 0, i 0]) },
    -- 1: dispatch current v1 with suspended parent chain v2
    { params := [1, 2]
      term := .br .tnz .w64 (v 1) (i 1) (to 6 [v 2]) (to 2) },
    -- 2: static .rodata cell (rc < 0 signed i32) needs no write
    { body := #[.assign 3 (.load .w32 .zero (cellAddr 1 4))]
      term := .br .slt .w32 (v 3) (i 0) (to 6 [v 2]) (to 3) },
    -- 3: dead (rc == 0) vs shared (rc > 0)
    { term := .br .eq .w32 (v 3) (i 0) (to 5) (to 4) },
    -- 4: shared dynamic cell: decrement rc in place
    { body := #[.assign 4 (.bin .sub .w32 (v 3) (i 1)),
        .store .w32 (cellAddr 1 4) (v 4)]
      term := .jump (to 6 [v 2]) },
    -- 5: dead cell: scan == 0 -> O(1) recycle (ByteArray, LimbArray, scalar ctor)
    { body := #[.assign 5 (.load .w8 .zero (cellAddr 1))]
      term := .br .eq .w64 (v 5) (i 0) (to 11) (to 12) },
    -- 6: continuation dispatch: parent == 0 -> done
    { params := [8]
      term := .br .eq .w64 (v 8) (i 0) (to 10) (to 7) },
    -- 7: resume suspended parent v8: boxed array (scan == 0xFF) vs ordinary ctor
    { body := #[.assign 10 (.load .w8 .zero (cellAddr 8))]
      term := .br .eq .w64 (v 10) (i 0xFF) (to 16) (to 17) },
    -- 8: ordinary ctor next field: idx = scan - rem
    { body := #[.assign 12 (.bin .sub .w64 (v 10) (v 9)),
        .assign 13 (.load .w64 .zero { base := some (.v 8), index := some (12, .eight), disp := 8 }),
        .assign 14 (.bin .sub .w64 (v 9) (i 1)),
        .store .w32 (cellAddr 8 4) (v 14)]
      term := .jump (to 1 [v 13, v 8]) },
    -- 9: recycle finished ordinary ctor parent v8; resume pred at [v8 + 8]
    { body := #[.assign 11 (.load .w8 .zero (cellAddr 8 1)),
        .assign 15 (.load .w64 .zero (cellAddr 8 8)),
        .assign 16 (.load .w64 .zero (ctxHeadAddr 11)),
        .store .w64 (cellAddr 8) (v 16),
        .store .w64 (ctxHeadAddr 11) (v 8)]
      term := .jump (to 6 [v 15]) },
    -- 10: done
    { term := .ret [] },
    -- 11: O(1) recycle of v1 (scan == 0 or empty boxed array); continue with v2
    { body := #[.assign 17 (.load .w8 .zero (cellAddr 1 1)),
        .assign 18 (.load .w64 .zero (ctxHeadAddr 17)),
        .store .w64 (cellAddr 1) (v 18),
        .store .w64 (ctxHeadAddr 17) (v 1)]
      term := .jump (to 6 [v 2]) },
    -- 12: scan != 0: boxed array (0xFF) vs ordinary ctor (1..254)
    { term := .br .eq .w64 (v 5) (i 0xFF) (to 13) (to 14) },
    -- 13: dead boxed array v1: load size; if 0 -> O(1) recycle (block 11)
    { body := #[.assign 19 (.load .w64 .zero (cellAddr 1 8))]
      term := .br .eq .w64 (v 19) (i 0) (to 11) (to 15) },
    -- 14: dead ordinary ctor v1 (exact Rt.Rc.Gen.dec logic)
    { body := #[.assign 6 (.load .w64 .zero (cellAddr 1 8)),
        .assign 7 (.bin .sub .w64 (v 5) (i 1)),
        .store .w64 (cellAddr 1 8) (v 2),
        .store .w32 (cellAddr 1 4) (v 7)]
      term := .jump (to 1 [v 6, v 1]) },
    -- 15: dead non-empty boxed array v1: rem = size - 1, store rem at +8, parent at +16, descend elem[rem]
    { body := #[.assign 20 (.bin .sub .w64 (v 19) (i 1)),
        .assign 21 (.load .w64 .zero (wordElemAddr 1 20)),
        .store .w64 (cellAddr 1 8) (v 20),
        .store .w64 (cellAddr 1 16) (v 2)]
      term := .jump (to 1 [v 21, v 1]) },
    -- 16: resume suspended boxed array v8: rem at +8
    { body := #[.assign 22 (.load .w64 .zero (cellAddr 8 8))]
      term := .br .eq .w64 (v 22) (i 0) (to 18) (to 19) },
    -- 17: resume suspended ordinary ctor v8: rem at +4
    { body := #[.assign 9 (.load .w32 .zero (cellAddr 8 4))]
      term := .br .eq .w64 (v 9) (i 0) (to 9) (to 8) },
    -- 18: recycle finished boxed array parent v8; resume pred at [v8 + 16]
    { body := #[.assign 23 (.load .w8 .zero (cellAddr 8 1)),
        .assign 24 (.load .w64 .zero (cellAddr 8 16)),
        .assign 25 (.load .w64 .zero (ctxHeadAddr 23)),
        .store .w64 (cellAddr 8) (v 25),
        .store .w64 (ctxHeadAddr 23) (v 8)]
      term := .jump (to 6 [v 24]) },
    -- 19: boxed array next element: rem1 = rem - 1, descend elem[rem1]
    { body := #[.assign 26 (.bin .sub .w64 (v 22) (i 1)),
        .assign 27 (.load .w64 .zero (wordElemAddr 8 26)),
        .store .w64 (cellAddr 8 8) (v 26)]
      term := .jump (to 1 [v 27, v 8]) }]

/-! ## 2. O(1) size-class arithmetic (`arrClassFor`, `arrClassWords`) -/

/-- O(1) `classFor` matching `Layout.classForFast` / `Rt.Rc.classFor`.
Fails `.heap` if `words = 0` or `words > maxCellWords` (`2^26`). -/
def arrClassFor : Func where
  name := "rt_arr_class_for"
  params := [0]
  results := 1
  blocks := #[
    -- 0: reject words == 0
    { term := .br .eq .w64 (v 0) (i 0) (to 6) (to 1) },
    -- 1: reject words > 2^26
    { term := .br .ugt .w64 (v 0) (i maxCellWords) (to 6) (to 2) },
    -- 2: small classes 1..32
    { term := .br .ule .w64 (v 0) (i 32) (to 3) (to 4) },
    -- 3: return words
    { term := .ret [v 0] },
    -- 4: compute x = words - 1, b = bsr64(x); branch on words ≤ 2048
    { body := #[.assign 1 (.bin .sub .w64 (v 0) (i 1)),
        .assign 2 (.bsr64 (v 1))]
      term := .br .ule .w64 (v 0) (i 2048) (to 5) (to 7) },
    -- 5: mid range 33..56: 33 + ((b - 5) << 2) + ((x >> (b - 2)) & 3)
    { body := #[.assign 3 (.bin .sub .w64 (v 2) (i 5)),
        .assign 4 (.bin .shl .w64 (v 3) (i 2)),
        .assign 5 (.bin .sub .w64 (v 2) (i 2)),
        .assign 6 (.bin .shr .w64 (v 1) (v 5)),
        .assign 7 (.bin .and .w64 (v 6) (i 3)),
        .assign 8 (.bin .add .w64 (v 4) (i 33)),
        .assign 9 (.bin .add .w64 (v 8) (v 7))]
      term := .ret [v 9] },
    -- 6: heap resource error
    { term := .fail .heap, cold := true },
    -- 7: high range 57..71: b + 46
    { body := #[.assign 10 (.bin .add .w64 (v 2) (i 46))]
      term := .ret [v 10] }]

/-- O(1) `classWords` matching `Layout.classWordsFast` / `Rt.Rc.classWords`. -/
def arrClassWords : Func where
  name := "rt_arr_class_words"
  params := [0]
  results := 1
  blocks := #[
    -- 0: c ≤ 32 -> c
    { term := .br .ule .w64 (v 0) (i 32) (to 1) (to 2) },
    -- 1: return c
    { term := .ret [v 0] },
    -- 2: c ≤ 56 vs c ≥ 57
    { term := .br .ule .w64 (v 0) (i 56) (to 3) (to 4) },
    -- 3: mid range: (32 + (((k & 3) + 1) << 3)) << (k >> 2)
    { body := #[.assign 1 (.bin .sub .w64 (v 0) (i 33)),
        .assign 2 (.bin .and .w64 (v 1) (i 3)),
        .assign 3 (.bin .add .w64 (v 2) (i 1)),
        .assign 4 (.bin .shl .w64 (v 3) (i 3)),
        .assign 5 (.bin .add .w64 (v 4) (i 32)),
        .assign 6 (.bin .shr .w64 (v 1) (i 2)),
        .assign 7 (.bin .shl .w64 (v 5) (v 6))]
      term := .ret [v 7] },
    -- 4: high range: 4096 << (c - 57)
    { body := #[.assign 8 (.bin .sub .w64 (v 0) (i 57)),
        .assign 9 (.bin .shl .w64 (i 4096) (v 8))]
      term := .ret [v 9] }]

/-! ## 3. Allocator & constructors -/

/-- Allocate an array cell of at least `words` 64-bit words (`words ≥ 3`) with
fixed header template `scanTagFixed` (`scan + 65536 * tag`). Initializes
`header` (`rc = 0`, unique), `size = 0`, and `cap = classWords cls - 3`. -/
def arrAllocCell : Func where
  name := "rt_arr_alloc_cell"
  params := [0, 1]
  results := 1
  blocks := #[
    -- 0: compute cls, cw, and inspect free list head [ctx + cls*8]
    { body := #[.call [2] fnClassFor [v 0],
        .call [3] fnClassWords [v 2],
        .assign 4 (.load .w64 .zero (ctxHeadAddr 2))]
      term := .br .eq .w64 (v 4) (i 0) (to 2) (to 1) },
    -- 1: pop free list head
    { body := #[.assign 5 (.load .w64 .zero (cellAddr 4)),
        .store .w64 (ctxHeadAddr 2) (v 5)]
      term := .jump (to 5 [v 4]) },
    -- 2: bump allocate cw * 8 bytes from [ctx + bumpOff]..[ctx + limitOff]
    { body := #[.assign 6 (.load .w64 .zero (ctx bumpOff)),
        .assign 7 (.load .w64 .zero (ctx limitOff)),
        .assign 8 (.bin .shl .w64 (v 3) (i 3))]
      term := .brOvf .addC 9 (v 6) (v 8) (to 3) (to 6) },
    -- 3: check newBump ≤ limit
    { term := .br .ule .w64 (v 9) (v 7) (to 4) (to 6) },
    -- 4: commit bump pointer
    { body := #[.store .w64 (ctx bumpOff) (v 9)]
      term := .jump (to 5 [v 6]) },
    -- 5: initialize header, size = 0, wordCap = cw - 3
    { params := [10]
      body := #[.assign 11 (.bin .shl .w64 (v 2) (i 8)),
        .assign 12 (.bin .or .w64 (v 1) (v 11)),
        .assign 13 (.bin .sub .w64 (v 3) (i 3)),
        .store .w64 (cellAddr 10 0) (v 12),
        .store .w64 (cellAddr 10 8) (i 0),
        .store .w64 (cellAddr 10 16) (v 13)]
      term := .ret [v 10] },
    -- 6: heap exhausted
    { term := .fail .heap, cold := true }]

/-- Allocate an empty word-backed array (`boxed` or `limbs`) with capacity at least `cap`. -/
def arrEmptyCapWord (kind : ArrayKind) (name : String) : Func where
  name := name
  params := [0]
  results := 1
  blocks := #[
    { term := .brOvf .addC 1 (v 0) (i 3) (to 1) (to 2) },
    { term := .tail fnAllocCell [v 1, .imm (scanTagFixed kind)] },
    { term := .fail .heap, cold := true }]

/-- Allocate an empty boxed `Array α` with capacity at least `cap`. -/
def arrEmptyCapBoxed : Func := arrEmptyCapWord .boxed "rt_arr_empty_cap_boxed"

/-- Allocate an empty unboxed `Array UInt64` / `BigNat` limb buffer with capacity at least `cap`. -/
def arrEmptyCapLimbs : Func := arrEmptyCapWord .limbs "rt_arr_empty_cap_limbs"

/-- Allocate an empty unboxed `ByteArray` (or UTF-8 `String` buffer) with byte
capacity at least `byteCap`. Sets `cap = byteCapOfClass cls = 8 * (cw - 3)`. -/
def byteArrEmptyCap : Func where
  name := "rt_byte_arr_empty_cap"
  params := [0]
  results := 1
  blocks := #[
    -- 0: byteCap + 7 (check overflow)
    { term := .brOvf .addC 1 (v 0) (i 7) (to 1) (to 3) },
    -- 1: words = 3 + ((byteCap + 7) >> 3)
    { body := #[.assign 2 (.bin .shr .w64 (v 1) (i 3))]
      term := .brOvf .addC 3 (v 2) (i 3) (to 2) (to 3) },
    -- 2: allocate cell and convert stored wordCap to byteCap = wordCap << 3
    { body := #[.call [4] fnAllocCell [v 3, .imm (scanTagFixed .bytes)],
        .assign 5 (.load .w64 .zero (cellAddr 4 16)),
        .assign 6 (.bin .shl .w64 (v 5) (i 3)),
        .store .w64 (cellAddr 4 16) (v 6)]
      term := .ret [v 4] },
    -- 3: overflow / heap error
    { term := .fail .heap, cold := true }]

/-! ## 4. O(1) queries (`arrSize`, `arrCap`, `arrGet`, `byteArrGet`) -/

/-- Return the element/byte count of any array cell (boxed, bytes, limbs, dynamic or static). -/
def arrSize : Func where
  name := "rt_arr_size"
  params := [0]
  results := 1
  blocks := #[
    { body := #[.assign 1 (.load .w64 .zero (cellAddr 0 8))]
      term := .ret [v 1] }]

/-- Return the element/byte capacity of any array cell. -/
def arrCap : Func where
  name := "rt_arr_cap"
  params := [0]
  results := 1
  blocks := #[
    { body := #[.assign 1 (.load .w64 .zero (cellAddr 0 16))]
      term := .ret [v 1] }]

/-- Bounds-checked word read `arr[idx]` for boxed `Array` or unboxed `LimbArray`.
Traps if `idx ≥ size`. -/
def arrGet : Func where
  name := "rt_arr_get"
  params := [0, 1]
  results := 1
  blocks := #[
    { body := #[.assign 2 (.load .w64 .zero (cellAddr 0 8))]
      term := .br .ult .w64 (v 1) (v 2) (to 1) (to 2) },
    { body := #[.assign 3 (.load .w64 .zero (wordElemAddr 0 1))]
      term := .ret [v 3] },
    { term := .trap, cold := true }]

/-- Bounds-checked byte read `arr[idx]` (zero-extended 0..255) for `ByteArray` / `String`.
Traps if `idx ≥ size`. -/
def byteArrGet : Func where
  name := "rt_byte_arr_get"
  params := [0, 1]
  results := 1
  blocks := #[
    { body := #[.assign 2 (.load .w64 .zero (cellAddr 0 8))]
      term := .br .ult .w64 (v 1) (v 2) (to 1) (to 2) },
    { body := #[.assign 3 (.load .w8 .zero (byteElemAddr 0 1))]
      term := .ret [v 3] },
    { term := .trap, cold := true }]

/-! ## 5. Word-backed mutations (`arrSet`, `arrPush`, `arrPop`, `arrExtract`, `arrCopySlice`) -/

/-- Helper: optional `inc` call statement when `isBoxed = true`. -/
private def optInc (isBoxed : Bool) (r : VReg) : Array Stmt :=
  if isBoxed then #[.call [] fnInc [v r]] else #[]

/-- Helper: optional `arrDec` call statement when `isBoxed = true`. -/
private def optDec (isBoxed : Bool) (r : VReg) : Array Stmt :=
  if isBoxed then #[.call [] fnDec [v r]] else #[]

/-- Word-array `set (arr, idx, val) -> arr'`:
* Out-of-bounds (`idx ≥ size`): no-op (releases `val` if boxed) and returns `arr`.
* Unique (`rc == 0`): O(1) in-place overwrite (releases old element if boxed).
* Shared or static `.rodata` (`rc != 0`): copy-on-write into a fresh array,
  incrementing retained boxed elements and releasing `arr`. -/
def arrSetWord (isBoxed : Bool) : Func :=
  let emptyFn := if isBoxed then fnEmptyCapBoxed else fnEmptyCapLimbs
  { name := if isBoxed then "rt_arr_set_boxed" else "rt_arr_set_limbs"
    params := [0, 1, 2]
    results := 1
    blocks := #[
      -- 0: bounds check idx < size
      { body := #[.assign 3 (.load .w64 .zero (cellAddr 0 8))]
        term := .br .ult .w64 (v 1) (v 3) (to 2) (to 1) },
      -- 1: out of bounds: dec val if boxed, return arr unchanged
      { body := optDec isBoxed 2
        term := .ret [v 0] },
      -- 2: check uniqueness (rc == 0)
      { body := #[.assign 4 (.load .w32 .zero (cellAddr 0 4))]
        term := .br .eq .w32 (v 4) (i 0) (to 3) (to 4) },
      -- 3: unique fast path (O(1) in-place)
      { body :=
          if isBoxed then
            #[.assign 5 (.load .w64 .zero (wordElemAddr 0 1)),
              .store .w64 (wordElemAddr 0 1) (v 2),
              .call [] fnDec [v 5]]
          else
            #[.store .w64 (wordElemAddr 0 1) (v 2)]
        term := .ret [v 0] },
      -- 4: shared / static COW path: allocate fresh cell of size v3
      { body := #[.call [6] emptyFn [v 3],
          .store .w64 (cellAddr 6 8) (v 3)]
        term := .jump (to 5 [i 0]) },
      -- 5: copy loop header: j = v7
      { params := [7]
        term := .br .ult .w64 (v 7) (v 3) (to 6) (to 9) },
      -- 6: check j == idx
      { term := .br .eq .w64 (v 7) (v 1) (to 7) (to 8) },
      -- 7: store new val at dst[idx]
      { body := #[.store .w64 (wordElemAddr 6 7) (v 2),
          .assign 8 (.bin .add .w64 (v 7) (i 1))]
        term := .jump (to 5 [v 8]) },
      -- 8: copy old elem (inc if boxed) at dst[j]
      { body := #[.assign 9 (.load .w64 .zero (wordElemAddr 0 7))] ++
          optInc isBoxed 9 ++
          #[.store .w64 (wordElemAddr 6 7) (v 9),
            .assign 10 (.bin .add .w64 (v 7) (i 1))]
        term := .jump (to 5 [v 10]) },
      -- 9: release old shared/static arr and return fresh dst
      { body := #[.call [] fnDec [v 0]]
        term := .ret [v 6] }] }

def arrSetBoxed : Func := arrSetWord true
def arrSetLimbs : Func := arrSetWord false

/-- Word-array `push (arr, val) -> arr'`:
* Unique + room (`rc == 0 ∧ size < cap`): O(1) in-place write + size increment.
* Unique + full (`rc == 0 ∧ size == cap`): amortized 2x growth moving elements
  with ZERO `inc`/`dec` and O(1) old-shell recycling onto `[ctx + oldCls*8]`.
* Shared / static `.rodata` (`rc != 0`): COW allocation + element `inc` (if
  boxed) + release of old array. -/
def arrPushWord (isBoxed : Bool) : Func :=
  let emptyFn := if isBoxed then fnEmptyCapBoxed else fnEmptyCapLimbs
  { name := if isBoxed then "rt_arr_push_boxed" else "rt_arr_push_limbs"
    params := [0, 1]
    results := 1
    blocks := #[
      -- 0: load size, cap, rc; branch on unique (rc == 0)
      { body := #[.assign 2 (.load .w64 .zero (cellAddr 0 8)),
          .assign 3 (.load .w64 .zero (cellAddr 0 16)),
          .assign 4 (.load .w32 .zero (cellAddr 0 4))]
        term := .br .eq .w32 (v 4) (i 0) (to 1) (to 8) },
      -- 1: unique: room (size < cap) vs full (grow 2x)
      { term := .br .ult .w64 (v 2) (v 3) (to 2) (to 3) },
      -- 2: unique + room (O(1) in-place)
      { body := #[.store .w64 (wordElemAddr 0 2) (v 1),
          .assign 5 (.bin .add .w64 (v 2) (i 1)),
          .store .w64 (cellAddr 0 8) (v 5)]
        term := .ret [v 0] },
      -- 3: unique + full: check size < maxWordCap
      { term := .br .ult .w64 (v 2) (i maxWordCap) (to 4) (to 13) },
      -- 4: compute newCap = min(maxWordCap, max(4, max(size + 1, cap * 2))) and alloc
      { body := #[.assign 6 (.bin .add .w64 (v 2) (i 1)),
          .assign 7 (.bin .shl .w64 (v 3) (i 1)),
          .assign 8 (.select .ugt .w64 (v 7) (v 6) (v 7) (v 6)),
          .assign 9 (.select .ult .w64 (v 8) (i initWordGrowCap) (i initWordGrowCap) (v 8)),
          .assign 10 (.select .ugt .w64 (v 9) (i maxWordCap) (i maxWordCap) (v 9)),
          .call [11] emptyFn [v 10]]
        term := .jump (to 5 [i 0]) },
      -- 5: unique move loop: j = v12 (ZERO inc/dec — ownership transfers directly!)
      { params := [12]
        term := .br .ult .w64 (v 12) (v 2) (to 6) (to 7) },
      -- 6: move one element
      { body := #[.assign 13 (.load .w64 .zero (wordElemAddr 0 12)),
          .store .w64 (wordElemAddr 11 12) (v 13),
          .assign 14 (.bin .add .w64 (v 12) (i 1))]
        term := .jump (to 5 [v 14]) },
      -- 7: write pushed val, size = size + 1, O(1) recycle old shell v0
      { body := #[.store .w64 (wordElemAddr 11 2) (v 1),
          .store .w64 (cellAddr 11 8) (v 6),
          .assign 15 (.load .w8 .zero (cellAddr 0 1)),
          .assign 16 (.load .w64 .zero (ctxHeadAddr 15)),
          .store .w64 (cellAddr 0 0) (v 16),
          .store .w64 (ctxHeadAddr 15) (v 0)]
        term := .ret [v 11] },
      -- 8: shared / static: check size < maxWordCap
      { term := .br .ult .w64 (v 2) (i maxWordCap) (to 9) (to 13) },
      -- 9: compute target capacity and allocate fresh array
      { body := #[.assign 17 (.bin .add .w64 (v 2) (i 1)),
          .assign 18 (.bin .shl .w64 (v 3) (i 1)),
          .assign 19 (.select .ugt .w64 (v 18) (v 17) (v 18) (v 17)),
          .assign 20 (.select .ult .w64 (v 19) (i initWordGrowCap) (i initWordGrowCap) (v 19)),
          .assign 21 (.select .ugt .w64 (v 20) (i maxWordCap) (i maxWordCap) (v 20)),
          .assign 22 (.select .ult .w64 (v 2) (v 3) (v 17) (v 21)),
          .call [23] emptyFn [v 22]]
        term := .jump (to 10 [i 0]) },
      -- 10: shared copy loop: j = v24
      { params := [24]
        term := .br .ult .w64 (v 24) (v 2) (to 11) (to 12) },
      -- 11: copy one element (inc if boxed)
      { body := #[.assign 25 (.load .w64 .zero (wordElemAddr 0 24))] ++
          optInc isBoxed 25 ++
          #[.store .w64 (wordElemAddr 23 24) (v 25),
            .assign 26 (.bin .add .w64 (v 24) (i 1))]
        term := .jump (to 10 [v 26]) },
      -- 12: write pushed val, size, release old arr v0
      { body := #[.store .w64 (wordElemAddr 23 2) (v 1),
          .store .w64 (cellAddr 23 8) (v 17),
          .call [] fnDec [v 0]]
        term := .ret [v 23] },
      -- 13: capacity limit exceeded
      { term := .fail .heap, cold := true }] }

def arrPushBoxed : Func := arrPushWord true
def arrPushLimbs : Func := arrPushWord false

/-- Word-array `pop (arr) -> arr'`:
* Empty (`size == 0`): returns `arr` unchanged.
* Unique (`rc == 0`): O(1) in-place size decrement (releases popped element if boxed).
* Shared / static (`rc != 0`): COW copy of prefix `0 ..< size - 1` + release old `arr`. -/
def arrPopWord (isBoxed : Bool) : Func :=
  let emptyFn := if isBoxed then fnEmptyCapBoxed else fnEmptyCapLimbs
  { name := if isBoxed then "rt_arr_pop_boxed" else "rt_arr_pop_limbs"
    params := [0]
    results := 1
    blocks := #[
      -- 0: empty check
      { body := #[.assign 1 (.load .w64 .zero (cellAddr 0 8))]
        term := .br .eq .w64 (v 1) (i 0) (to 1) (to 2) },
      -- 1: empty -> return arr unchanged
      { term := .ret [v 0] },
      -- 2: compute sz1 = size - 1; check unique
      { body := #[.assign 2 (.bin .sub .w64 (v 1) (i 1)),
          .assign 3 (.load .w32 .zero (cellAddr 0 4))]
        term := .br .eq .w32 (v 3) (i 0) (to 3) (to 4) },
      -- 3: unique fast path (O(1) in-place)
      { body :=
          if isBoxed then
            #[.store .w64 (cellAddr 0 8) (v 2),
              .assign 4 (.load .w64 .zero (wordElemAddr 0 2)),
              .call [] fnDec [v 4]]
          else
            #[.store .w64 (cellAddr 0 8) (v 2)]
        term := .ret [v 0] },
      -- 4: shared / static COW path
      { body := #[.call [5] emptyFn [v 2],
          .store .w64 (cellAddr 5 8) (v 2)]
        term := .jump (to 5 [i 0]) },
      -- 5: copy loop: j = v6
      { params := [6]
        term := .br .ult .w64 (v 6) (v 2) (to 6) (to 7) },
      -- 6: copy one element (inc if boxed)
      { body := #[.assign 7 (.load .w64 .zero (wordElemAddr 0 6))] ++
          optInc isBoxed 7 ++
          #[.store .w64 (wordElemAddr 5 6) (v 7),
            .assign 8 (.bin .add .w64 (v 6) (i 1))]
        term := .jump (to 5 [v 8]) },
      -- 7: release old shared/static arr and return fresh dst
      { body := #[.call [] fnDec [v 0]]
        term := .ret [v 5] }] }

def arrPopBoxed : Func := arrPopWord true
def arrPopLimbs : Func := arrPopWord false

/-- Word-array `extract (arr, start, stop) -> dst`: allocates a fresh slice
containing `arr[start ..< min stop arr.size]` (borrows `arr`). -/
def arrExtractWord (isBoxed : Bool) : Func :=
  let emptyFn := if isBoxed then fnEmptyCapBoxed else fnEmptyCapLimbs
  { name := if isBoxed then "rt_arr_extract_boxed" else "rt_arr_extract_limbs"
    params := [0, 1, 2]
    results := 1
    blocks := #[
      -- 0: stop' = min(stop, size), len = if start < stop' then stop' - start else 0
      { body := #[.assign 3 (.load .w64 .zero (cellAddr 0 8)),
          .assign 4 (.select .ult .w64 (v 2) (v 3) (v 2) (v 3)),
          .assign 5 (.bin .sub .w64 (v 4) (v 1)),
          .assign 6 (.select .ult .w64 (v 1) (v 4) (v 5) (i 0)),
          .call [7] emptyFn [v 6],
          .store .w64 (cellAddr 7 8) (v 6)]
        term := .jump (to 1 [i 0]) },
      -- 1: copy loop: j = v8
      { params := [8]
        term := .br .ult .w64 (v 8) (v 6) (to 2) (to 3) },
      -- 2: copy src[start + j] -> dst[j]
      { body := #[.assign 9 (.bin .add .w64 (v 1) (v 8)),
          .assign 10 (.load .w64 .zero (wordElemAddr 0 9))] ++
          optInc isBoxed 10 ++
          #[.store .w64 (wordElemAddr 7 8) (v 10),
            .assign 11 (.bin .add .w64 (v 8) (i 1))]
        term := .jump (to 1 [v 11]) },
      -- 3: return dst
      { term := .ret [v 7] }] }

def arrExtractBoxed : Func := arrExtractWord true
def arrExtractLimbs : Func := arrExtractWord false

/-- Word-array `copySlice (src, srcOff, dest, destOff, len) -> dest'`:
Matches `ArraySpec.copySliceList` exactly, with a unique in-place fast path when
`dest` is unique, has capacity `≥ newSize`, and `src ≠ dest`, and a safe COW /
growth / self-alias path otherwise. -/
def arrCopySliceWord (isBoxed : Bool) : Func :=
  let emptyFn := if isBoxed then fnEmptyCapBoxed else fnEmptyCapLimbs
  { name := if isBoxed then "rt_arr_copy_slice_boxed" else "rt_arr_copy_slice_limbs"
    params := [0, 1, 2, 3, 4]
    results := 1
    blocks := #[
      -- 0: if len == 0 -> return dest
      { body := #[.assign 5 (.load .w64 .zero (cellAddr 0 8)),
          .assign 6 (.load .w64 .zero (cellAddr 2 8))]
        term := .br .eq .w64 (v 4) (i 0) (to 1) (to 2) },
      -- 1: empty slice -> return dest unchanged
      { term := .ret [v 2] },
      -- 2: if srcOff ≥ srcSz -> return dest
      { term := .br .ult .w64 (v 1) (v 5) (to 3) (to 1) },
      -- 3: actualLen = min(len, srcSz - srcOff), destOff' = min(destOff, destSz)
      { body := #[.assign 7 (.bin .sub .w64 (v 5) (v 1)),
          .assign 8 (.select .ult .w64 (v 4) (v 7) (v 4) (v 7)),
          .assign 9 (.select .ult .w64 (v 3) (v 6) (v 3) (v 6))]
        term := .brOvf .addC 10 (v 9) (v 8) (to 4) (to 19) },
      -- 4: newSize = max(destSz, endPos); reject newSize > maxWordCap
      { body := #[.assign 11 (.select .ugt .w64 (v 10) (v 6) (v 10) (v 6))]
        term := .br .ule .w64 (v 11) (i maxWordCap) (to 5) (to 19) },
      -- 5: check unique dest (rc == 0)
      { body := #[.assign 12 (.load .w32 .zero (cellAddr 2 4)),
          .assign 13 (.load .w64 .zero (cellAddr 2 16))]
        term := .br .eq .w32 (v 12) (i 0) (to 6) (to 12) },
      -- 6: check destCap ≥ newSize
      { term := .br .ule .w64 (v 11) (v 13) (to 7) (to 12) },
      -- 7: check non-aliasing (src != dest)
      { term := .br .ne .w64 (v 0) (v 2) (to 8) (to 12) },
      -- 8: fast unique in-place entry
      { term := .jump (to 9 [i 0]) },
      -- 9: fast loop header: j = v14
      { params := [14]
        term := .br .ult .w64 (v 14) (v 8) (to 10) (to 11) },
      -- 10: copy one element into dest[destOff' + j]
      { body :=
          if isBoxed then
            #[.assign 15 (.bin .add .w64 (v 1) (v 14)),
              .assign 16 (.load .w64 .zero (wordElemAddr 0 15)),
              .call [] fnInc [v 16],
              .assign 17 (.bin .add .w64 (v 9) (v 14)),
              .assign 18 (.bin .add .w64 (v 14) (i 1))]
          else
            #[.assign 15 (.bin .add .w64 (v 1) (v 14)),
              .assign 16 (.load .w64 .zero (wordElemAddr 0 15)),
              .assign 17 (.bin .add .w64 (v 9) (v 14)),
              .store .w64 (wordElemAddr 2 17) (v 16),
              .assign 18 (.bin .add .w64 (v 14) (i 1))]
        term :=
          if isBoxed then .br .ult .w64 (v 17) (v 6) (to 20) (to 21)
          else .jump (to 9 [v 18]) },
      -- 11: finish fast in-place: update size and return dest
      { body := #[.store .w64 (cellAddr 2 8) (v 11)]
        term := .ret [v 2] },
      -- 12: general COW / growth / alias path: allocate fresh out[newSize]
      { body := #[.call [20] emptyFn [v 11],
          .store .w64 (cellAddr 20 8) (v 11)]
        term := .jump (to 13 [i 0]) },
      -- 13: loop 1 (prefix 0 ..< destOff'): j = v21
      { params := [21]
        term := .br .ult .w64 (v 21) (v 9) (to 14) (to 15) },
      -- 14: copy dest[j] -> out[j]
      { body := #[.assign 22 (.load .w64 .zero (wordElemAddr 2 21))] ++
          optInc isBoxed 22 ++
          #[.store .w64 (wordElemAddr 20 21) (v 22),
            .assign 23 (.bin .add .w64 (v 21) (i 1))]
        term := .jump (to 13 [v 23]) },
      -- 15: enter loop 2 (middle 0 ..< actualLen)
      { term := .jump (to 16 [i 0]) },
      -- 16: loop 2: j = v24
      { params := [24]
        term := .br .ult .w64 (v 24) (v 8) (to 17) (to 18) },
      -- 17: copy src[srcOff + j] -> out[destOff' + j]
      { body := #[.assign 25 (.bin .add .w64 (v 1) (v 24)),
          .assign 26 (.load .w64 .zero (wordElemAddr 0 25))] ++
          optInc isBoxed 26 ++
          #[.assign 27 (.bin .add .w64 (v 9) (v 24)),
            .store .w64 (wordElemAddr 20 27) (v 26),
            .assign 28 (.bin .add .w64 (v 24) (i 1))]
        term := .jump (to 16 [v 28]) },
      -- 18: enter loop 3 (suffix endPos ..< destSz)
      { term := .jump (to 22 [v 10]) },
      -- 19: heap overflow
      { term := .fail .heap, cold := true },
      -- 20: (boxed fast path) overwrite existing slot dest[v17] and dec old
      { body :=
          if isBoxed then
            #[.assign 19 (.load .w64 .zero (wordElemAddr 2 17)),
              .store .w64 (wordElemAddr 2 17) (v 16),
              .call [] fnDec [v 19]]
          else #[]
        term := .jump (to 9 [v 18]) },
      -- 21: (boxed fast path) write into newly extended slot dest[v17]
      { body :=
          if isBoxed then #[.store .w64 (wordElemAddr 2 17) (v 16)] else #[]
        term := .jump (to 9 [v 18]) },
      -- 22: loop 3 (suffix endPos ..< destSz): j = v29
      { params := [29]
        term := .br .ult .w64 (v 29) (v 6) (to 23) (to 24) },
      -- 23: copy dest[j] -> out[j]
      { body := #[.assign 30 (.load .w64 .zero (wordElemAddr 2 29))] ++
          optInc isBoxed 30 ++
          #[.store .w64 (wordElemAddr 20 29) (v 30),
            .assign 31 (.bin .add .w64 (v 29) (i 1))]
        term := .jump (to 22 [v 31]) },
      -- 24: release old dest and return out
      { body := #[.call [] fnDec [v 2]]
        term := .ret [v 20] }] }

/-- Specialized clean non-boxed `arrCopySliceLimbs` (no unreachable blocks 20/21). -/
def arrCopySliceLimbs : Func where
  name := "rt_arr_copy_slice_limbs"
  params := [0, 1, 2, 3, 4]
  results := 1
  blocks := #[
    { body := #[.assign 5 (.load .w64 .zero (cellAddr 0 8)),
        .assign 6 (.load .w64 .zero (cellAddr 2 8))]
      term := .br .eq .w64 (v 4) (i 0) (to 1) (to 2) },
    { term := .ret [v 2] },
    { term := .br .ult .w64 (v 1) (v 5) (to 3) (to 1) },
    { body := #[.assign 7 (.bin .sub .w64 (v 5) (v 1)),
        .assign 8 (.select .ult .w64 (v 4) (v 7) (v 4) (v 7)),
        .assign 9 (.select .ult .w64 (v 3) (v 6) (v 3) (v 6))]
      term := .brOvf .addC 10 (v 9) (v 8) (to 4) (to 19) },
    { body := #[.assign 11 (.select .ugt .w64 (v 10) (v 6) (v 10) (v 6))]
      term := .br .ule .w64 (v 11) (i maxWordCap) (to 5) (to 19) },
    { body := #[.assign 12 (.load .w32 .zero (cellAddr 2 4)),
        .assign 13 (.load .w64 .zero (cellAddr 2 16))]
      term := .br .eq .w32 (v 12) (i 0) (to 6) (to 12) },
    { term := .br .ule .w64 (v 11) (v 13) (to 7) (to 12) },
    { term := .br .ne .w64 (v 0) (v 2) (to 8) (to 12) },
    { term := .jump (to 9 [i 0]) },
    { params := [14]
      term := .br .ult .w64 (v 14) (v 8) (to 10) (to 11) },
    { body := #[.assign 15 (.bin .add .w64 (v 1) (v 14)),
        .assign 16 (.load .w64 .zero (wordElemAddr 0 15)),
        .assign 17 (.bin .add .w64 (v 9) (v 14)),
        .store .w64 (wordElemAddr 2 17) (v 16),
        .assign 18 (.bin .add .w64 (v 14) (i 1))]
      term := .jump (to 9 [v 18]) },
    { body := #[.store .w64 (cellAddr 2 8) (v 11)]
      term := .ret [v 2] },
    { body := #[.call [20] fnEmptyCapLimbs [v 11],
        .store .w64 (cellAddr 20 8) (v 11)]
      term := .jump (to 13 [i 0]) },
    { params := [21]
      term := .br .ult .w64 (v 21) (v 9) (to 14) (to 15) },
    { body := #[.assign 22 (.load .w64 .zero (wordElemAddr 2 21)),
        .store .w64 (wordElemAddr 20 21) (v 22),
        .assign 23 (.bin .add .w64 (v 21) (i 1))]
      term := .jump (to 13 [v 23]) },
    { term := .jump (to 16 [i 0]) },
    { params := [24]
      term := .br .ult .w64 (v 24) (v 8) (to 17) (to 18) },
    { body := #[.assign 25 (.bin .add .w64 (v 1) (v 24)),
        .assign 26 (.load .w64 .zero (wordElemAddr 0 25)),
        .assign 27 (.bin .add .w64 (v 9) (v 24)),
        .store .w64 (wordElemAddr 20 27) (v 26),
        .assign 28 (.bin .add .w64 (v 24) (i 1))]
      term := .jump (to 16 [v 28]) },
    { term := .jump (to 20 [v 10]) },
    { term := .fail .heap, cold := true },
    { params := [29]
      term := .br .ult .w64 (v 29) (v 6) (to 21) (to 22) },
    { body := #[.assign 30 (.load .w64 .zero (wordElemAddr 2 29)),
        .store .w64 (wordElemAddr 20 29) (v 30),
        .assign 31 (.bin .add .w64 (v 29) (i 1))]
      term := .jump (to 20 [v 31]) },
    { body := #[.call [] fnDec [v 2]]
      term := .ret [v 20] }]

def arrCopySliceBoxed : Func := arrCopySliceWord true

/-! ## 6. Packed `ByteArray` mutations (`byteArrSet`, `byteArrPush`, `byteArrPop`, `byteArrExtract`, `byteArrCopySlice`) -/

/-- Packed `ByteArray` `set (arr, idx, byte) -> arr'`: O(1) in-place `.w8` store
when unique, COW when shared or static `.rodata`, no-op when out-of-bounds. -/
def byteArrSet : Func where
  name := "rt_byte_arr_set"
  params := [0, 1, 2]
  results := 1
  blocks := #[
    { body := #[.assign 3 (.load .w64 .zero (cellAddr 0 8))]
      term := .br .ult .w64 (v 1) (v 3) (to 2) (to 1) },
    { term := .ret [v 0] },
    { body := #[.assign 4 (.load .w32 .zero (cellAddr 0 4))]
      term := .br .eq .w32 (v 4) (i 0) (to 3) (to 4) },
    -- 3: unique O(1) in-place .w8 store
    { body := #[.store .w8 (byteElemAddr 0 1) (v 2)]
      term := .ret [v 0] },
    -- 4: shared / static COW
    { body := #[.call [5] fnByteEmptyCap [v 3],
        .store .w64 (cellAddr 5 8) (v 3)]
      term := .jump (to 5 [i 0]) },
    { params := [6]
      term := .br .ult .w64 (v 6) (v 3) (to 6) (to 7) },
    { body := #[.assign 7 (.load .w8 .zero (byteElemAddr 0 6)),
        .store .w8 (byteElemAddr 5 6) (v 7),
        .assign 8 (.bin .add .w64 (v 6) (i 1))]
      term := .jump (to 5 [v 8]) },
    { body := #[.store .w8 (byteElemAddr 5 1) (v 2),
        .call [] fnDec [v 0]]
      term := .ret [v 5] }]

/-- Packed `ByteArray` `push (arr, byte) -> arr'`: O(1) in-place when unique
with room, amortized 2x growth + O(1) shell recycle when unique and full, COW
when shared or static `.rodata`. -/
def byteArrPush : Func where
  name := "rt_byte_arr_push"
  params := [0, 1]
  results := 1
  blocks := #[
    { body := #[.assign 2 (.load .w64 .zero (cellAddr 0 8)),
        .assign 3 (.load .w64 .zero (cellAddr 0 16)),
        .assign 4 (.load .w32 .zero (cellAddr 0 4))]
      term := .br .eq .w32 (v 4) (i 0) (to 1) (to 8) },
    { term := .br .ult .w64 (v 2) (v 3) (to 2) (to 3) },
    -- 2: unique + room (O(1) in-place .w8 store + size increment)
    { body := #[.store .w8 (byteElemAddr 0 2) (v 1),
        .assign 5 (.bin .add .w64 (v 2) (i 1)),
        .store .w64 (cellAddr 0 8) (v 5)]
      term := .ret [v 0] },
    -- 3: unique + full
    { term := .br .ult .w64 (v 2) (i maxByteCap) (to 4) (to 13) },
    { body := #[.assign 6 (.bin .add .w64 (v 2) (i 1)),
        .assign 7 (.bin .shl .w64 (v 3) (i 1)),
        .assign 8 (.select .ugt .w64 (v 7) (v 6) (v 7) (v 6)),
        .assign 9 (.select .ult .w64 (v 8) (i initByteGrowCap) (i initByteGrowCap) (v 8)),
        .assign 10 (.select .ugt .w64 (v 9) (i maxByteCap) (i maxByteCap) (v 9)),
        .call [11] fnByteEmptyCap [v 10]]
      term := .jump (to 5 [i 0]) },
    { params := [12]
      term := .br .ult .w64 (v 12) (v 2) (to 6) (to 7) },
    { body := #[.assign 13 (.load .w8 .zero (byteElemAddr 0 12)),
        .store .w8 (byteElemAddr 11 12) (v 13),
        .assign 14 (.bin .add .w64 (v 12) (i 1))]
      term := .jump (to 5 [v 14]) },
    -- 7: write pushed byte, size, O(1) recycle old shell
    { body := #[.store .w8 (byteElemAddr 11 2) (v 1),
        .store .w64 (cellAddr 11 8) (v 6),
        .assign 15 (.load .w8 .zero (cellAddr 0 1)),
        .assign 16 (.load .w64 .zero (ctxHeadAddr 15)),
        .store .w64 (cellAddr 0 0) (v 16),
        .store .w64 (ctxHeadAddr 15) (v 0)]
      term := .ret [v 11] },
    -- 8: shared / static
    { term := .br .ult .w64 (v 2) (i maxByteCap) (to 9) (to 13) },
    { body := #[.assign 17 (.bin .add .w64 (v 2) (i 1)),
        .assign 18 (.bin .shl .w64 (v 3) (i 1)),
        .assign 19 (.select .ugt .w64 (v 18) (v 17) (v 18) (v 17)),
        .assign 20 (.select .ult .w64 (v 19) (i initByteGrowCap) (i initByteGrowCap) (v 19)),
        .assign 21 (.select .ugt .w64 (v 20) (i maxByteCap) (i maxByteCap) (v 20)),
        .assign 22 (.select .ult .w64 (v 2) (v 3) (v 17) (v 21)),
        .call [23] fnByteEmptyCap [v 22]]
      term := .jump (to 10 [i 0]) },
    { params := [24]
      term := .br .ult .w64 (v 24) (v 2) (to 11) (to 12) },
    { body := #[.assign 25 (.load .w8 .zero (byteElemAddr 0 24)),
        .store .w8 (byteElemAddr 23 24) (v 25),
        .assign 26 (.bin .add .w64 (v 24) (i 1))]
      term := .jump (to 10 [v 26]) },
    { body := #[.store .w8 (byteElemAddr 23 2) (v 1),
        .store .w64 (cellAddr 23 8) (v 17),
        .call [] fnDec [v 0]]
      term := .ret [v 23] },
    { term := .fail .heap, cold := true }]

/-- Packed `ByteArray` `pop (arr) -> arr'`: O(1) in-place when unique, COW when shared/static. -/
def byteArrPop : Func where
  name := "rt_byte_arr_pop"
  params := [0]
  results := 1
  blocks := #[
    { body := #[.assign 1 (.load .w64 .zero (cellAddr 0 8))]
      term := .br .eq .w64 (v 1) (i 0) (to 1) (to 2) },
    { term := .ret [v 0] },
    { body := #[.assign 2 (.bin .sub .w64 (v 1) (i 1)),
        .assign 3 (.load .w32 .zero (cellAddr 0 4))]
      term := .br .eq .w32 (v 3) (i 0) (to 3) (to 4) },
    { body := #[.store .w64 (cellAddr 0 8) (v 2)]
      term := .ret [v 0] },
    { body := #[.call [4] fnByteEmptyCap [v 2],
        .store .w64 (cellAddr 4 8) (v 2)]
      term := .jump (to 5 [i 0]) },
    { params := [5]
      term := .br .ult .w64 (v 5) (v 2) (to 6) (to 7) },
    { body := #[.assign 6 (.load .w8 .zero (byteElemAddr 0 5)),
        .store .w8 (byteElemAddr 4 5) (v 6),
        .assign 7 (.bin .add .w64 (v 5) (i 1))]
      term := .jump (to 5 [v 7]) },
    { body := #[.call [] fnDec [v 0]]
      term := .ret [v 4] }]

/-- Packed `ByteArray` `extract (arr, start, stop) -> dst`. -/
def byteArrExtract : Func where
  name := "rt_byte_arr_extract"
  params := [0, 1, 2]
  results := 1
  blocks := #[
    { body := #[.assign 3 (.load .w64 .zero (cellAddr 0 8)),
        .assign 4 (.select .ult .w64 (v 2) (v 3) (v 2) (v 3)),
        .assign 5 (.bin .sub .w64 (v 4) (v 1)),
        .assign 6 (.select .ult .w64 (v 1) (v 4) (v 5) (i 0)),
        .call [7] fnByteEmptyCap [v 6],
        .store .w64 (cellAddr 7 8) (v 6)]
      term := .jump (to 1 [i 0]) },
    { params := [8]
      term := .br .ult .w64 (v 8) (v 6) (to 2) (to 3) },
    { body := #[.assign 9 (.bin .add .w64 (v 1) (v 8)),
        .assign 10 (.load .w8 .zero (byteElemAddr 0 9)),
        .store .w8 (byteElemAddr 7 8) (v 10),
        .assign 11 (.bin .add .w64 (v 8) (i 1))]
      term := .jump (to 1 [v 11]) },
    { term := .ret [v 7] }]

/-- Packed `ByteArray` `copySlice (src, srcOff, dest, destOff, len) -> dest'`. -/
def byteArrCopySlice : Func where
  name := "rt_byte_arr_copy_slice"
  params := [0, 1, 2, 3, 4]
  results := 1
  blocks := #[
    { body := #[.assign 5 (.load .w64 .zero (cellAddr 0 8)),
        .assign 6 (.load .w64 .zero (cellAddr 2 8))]
      term := .br .eq .w64 (v 4) (i 0) (to 1) (to 2) },
    { term := .ret [v 2] },
    { term := .br .ult .w64 (v 1) (v 5) (to 3) (to 1) },
    { body := #[.assign 7 (.bin .sub .w64 (v 5) (v 1)),
        .assign 8 (.select .ult .w64 (v 4) (v 7) (v 4) (v 7)),
        .assign 9 (.select .ult .w64 (v 3) (v 6) (v 3) (v 6))]
      term := .brOvf .addC 10 (v 9) (v 8) (to 4) (to 19) },
    { body := #[.assign 11 (.select .ugt .w64 (v 10) (v 6) (v 10) (v 6))]
      term := .br .ule .w64 (v 11) (i maxByteCap) (to 5) (to 19) },
    { body := #[.assign 12 (.load .w32 .zero (cellAddr 2 4)),
        .assign 13 (.load .w64 .zero (cellAddr 2 16))]
      term := .br .eq .w32 (v 12) (i 0) (to 6) (to 12) },
    { term := .br .ule .w64 (v 11) (v 13) (to 7) (to 12) },
    { term := .br .ne .w64 (v 0) (v 2) (to 8) (to 12) },
    { term := .jump (to 9 [i 0]) },
    { params := [14]
      term := .br .ult .w64 (v 14) (v 8) (to 10) (to 11) },
    { body := #[.assign 15 (.bin .add .w64 (v 1) (v 14)),
        .assign 16 (.load .w8 .zero (byteElemAddr 0 15)),
        .assign 17 (.bin .add .w64 (v 9) (v 14)),
        .store .w8 (byteElemAddr 2 17) (v 16),
        .assign 18 (.bin .add .w64 (v 14) (i 1))]
      term := .jump (to 9 [v 18]) },
    { body := #[.store .w64 (cellAddr 2 8) (v 11)]
      term := .ret [v 2] },
    { body := #[.call [20] fnByteEmptyCap [v 11],
        .store .w64 (cellAddr 20 8) (v 11)]
      term := .jump (to 13 [i 0]) },
    { params := [21]
      term := .br .ult .w64 (v 21) (v 9) (to 14) (to 15) },
    { body := #[.assign 22 (.load .w8 .zero (byteElemAddr 2 21)),
        .store .w8 (byteElemAddr 20 21) (v 22),
        .assign 23 (.bin .add .w64 (v 21) (i 1))]
      term := .jump (to 13 [v 23]) },
    { term := .jump (to 16 [i 0]) },
    { params := [24]
      term := .br .ult .w64 (v 24) (v 8) (to 17) (to 18) },
    { body := #[.assign 25 (.bin .add .w64 (v 1) (v 24)),
        .assign 26 (.load .w8 .zero (byteElemAddr 0 25)),
        .assign 27 (.bin .add .w64 (v 9) (v 24)),
        .store .w8 (byteElemAddr 20 27) (v 26),
        .assign 28 (.bin .add .w64 (v 24) (i 1))]
      term := .jump (to 16 [v 28]) },
    { term := .jump (to 20 [v 10]) },
    { term := .fail .heap, cold := true },
    { params := [29]
      term := .br .ult .w64 (v 29) (v 6) (to 21) (to 22) },
    { body := #[.assign 30 (.load .w8 .zero (byteElemAddr 2 29)),
        .store .w8 (byteElemAddr 20 29) (v 30),
        .assign 31 (.bin .add .w64 (v 29) (i 1))]
      term := .jump (to 20 [v 31]) },
    { body := #[.call [] fnDec [v 2]]
      term := .ret [v 20] }]

/-! ## 7. Complete runtime program bundle & well-formedness -/

/-- All 27 native array/bytearray/limbarray/RC procedures in exact `FunId` order. -/
def arrayRuntimeFuncs : Array Func := #[
  IxCC.Rt.Rc.Procs.inc, -- 0: fnInc
  arrDec,               -- 1: fnDec
  arrClassFor,          -- 2: fnClassFor
  arrClassWords,        -- 3: fnClassWords
  arrAllocCell,         -- 4: fnAllocCell
  arrEmptyCapBoxed,     -- 5: fnEmptyCapBoxed
  arrEmptyCapLimbs,     -- 6: fnEmptyCapLimbs
  byteArrEmptyCap,      -- 7: fnByteEmptyCap
  arrSize,              -- 8: fnSize
  arrCap,               -- 9: fnCap
  arrGet,               -- 10: fnGetWord
  byteArrGet,           -- 11: fnByteGet
  arrSetBoxed,          -- 12: fnSetBoxed
  arrSetLimbs,          -- 13: fnSetLimbs
  arrPushBoxed,         -- 14: fnPushBoxed
  arrPushLimbs,         -- 15: fnPushLimbs
  arrPopBoxed,          -- 16: fnPopBoxed
  arrPopLimbs,          -- 17: fnPopLimbs
  arrExtractBoxed,      -- 18: fnExtractBoxed
  arrExtractLimbs,      -- 19: fnExtractLimbs
  arrCopySliceBoxed,    -- 20: fnCopySliceBoxed
  arrCopySliceLimbs,    -- 21: fnCopySliceLimbs
  byteArrSet,           -- 22: fnByteSet
  byteArrPush,          -- 23: fnBytePush
  byteArrPop,           -- 24: fnBytePop
  byteArrExtract,       -- 25: fnByteExtract
  byteArrCopySlice      -- 26: fnByteCopySlice
]

/-- Bundle the runtime with entry point `mainFn`. -/
def arrayProgram (mainFn : FunId := fnEmptyCapBoxed) : Program :=
  { funcs := arrayRuntimeFuncs, main := mainFn }

-- Every array runtime procedure passes full Lir SSA, reachability, arity,
-- displacement, and protected-context validation after critical-edge splitting.
#guard (arrayProgram fnEmptyCapBoxed).splitCriticalEdges.wellFormed

end IxCC.Rt.Rc.Array
