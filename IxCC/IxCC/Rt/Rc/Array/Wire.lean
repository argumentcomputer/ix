import IxCC.Rt.Rc.Array.Procs
import IxCC.X86.ELFRodata

/-! # DR3 / DR4 Array Runtime Relocation, Bridges & Static String Materializers

Extends `IxCC.Rt.Rc.Array.Procs` with:
* `relocateFunc` / `relocateArrayRuntime`: shifts internal `FunId`s (`0..34`) in
  `arrayRuntimeFuncs` + bridge procs by `+ base` when embedding the native array
  runtime into a lowered `Lir.Program`;
* `arrSwapBoxed` / `arrSwapLimbs`: O(1) in-place swap when unique (COW when shared,
  no-op when out of bounds);
* `arrOfListBoxed` / `arrToListBoxed` / `arrOfListLimbs` / `arrToListLimbs`:
  representation bridges between Lean's `List` (`Array.mk` / `Array.toList`) and
  native contiguous `Array` / `Array UInt64` cells (unboxing both `< 2^63` odd tagged
  immediates and `≥ 2^63` 1-scalar-word boxed cells for `Array UInt64`);
* `byteArrOfArr` / `byteArrToArr`: representation bridges between boxed `Array UInt8`
  and packed `.w8` `ByteArray` (`ByteArray.mk` / `ByteArray.data`);
* `strLitProc`: position-independent static string literal materializer emitting the
  exact byte-for-byte `X86.ELFRodata.encodeStaticString s` layout (`staticHeader 0
  tagByteArray`, `rc = 0x80000000`, `size`, `cap`, UTF-8 bytes) as 64-bit stores.
-/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt (bumpOff limitOff immortalHeader ctor0Word)
open IxCC.Rt.Rc.Procs (v i to cellAddr ctx)
open IxCC.X86.ELFRodata (encodeStaticString encodeStaticStringK)

/-! ## Additional function indices in the extended array runtime table (`27..34`) -/

def fnSwapBoxed : FunId := 27
def fnSwapLimbs : FunId := 28
def fnArrOfListBoxed : FunId := 29
def fnArrToListBoxed : FunId := 30
def fnArrOfListLimbs : FunId := 31
def fnArrToListLimbs : FunId := 32
def fnByteArrOfArr : FunId := 33
def fnByteArrToArr : FunId := 34
def fnIncVal : FunId := 35

/-- Total count of functions in the extended native array runtime table (`0..35`). -/
def extendedArrayRuntimeCount : Nat := 36

/-! ## 1. O(1) Swap (`arrSwapBoxed`, `arrSwapLimbs`) -/

/-- O(1) boxed array swap `(arr, idx1, idx2) -> arr'`:
* Out-of-bounds `idx1 ≥ size ∨ idx2 ≥ size` or `idx1 == idx2`: returns `arr` unchanged.
* Unique (`rc == 0`): swaps `arr[idx1]` and `arr[idx2]` in place (zero allocation).
* Shared or static `.rodata` (`rc != 0`): allocates a fresh copy via `arrEmptyCapBoxed`,
  copies all elements with `fnInc`, writes the swapped pair, calls `fnDec arr`,
  and returns the copy. -/
def arrSwapBoxed : Func :=
  let emptyFn := fnEmptyCapBoxed
  { name := "rt_arr_swap_boxed"
    params := [0, 1, 2]
    results := 1
    blocks := #[
      -- 0: load size = [v0 + 8]; check v1 < size
      { body := #[.assign 3 (.load .w64 .zero (cellAddr 0 8))]
        term := .br .ult .w64 (v 1) (v 3) (to 1) (to 9) },
      -- 1: check v2 < size
      { term := .br .ult .w64 (v 2) (v 3) (to 2) (to 9) },
      -- 2: if v1 == v2 -> return v0
      { term := .br .eq .w64 (v 1) (v 2) (to 9) (to 3) },
      -- 3: load rc = [v0 + 4]; unique (rc == 0) vs shared
      { body := #[.assign 4 (.load .w32 .zero (cellAddr 0 4))]
        term := .br .eq .w32 (v 4) (i 0) (to 4) (to 5) },
      -- 4: unique fast path: swap in place
      { body := #[
          .assign 5 (.load .w64 .zero (wordElemAddr 0 1)),
          .assign 6 (.load .w64 .zero (wordElemAddr 0 2)),
          .store .w64 (wordElemAddr 0 1) (v 6),
          .store .w64 (wordElemAddr 0 2) (v 5)]
        term := .ret [v 0] },
      -- 5: shared/static COW path: allocate fresh cell of size v3
      { body := #[
          .call [7] emptyFn [v 3],
          .store .w64 (cellAddr 7 8) (v 3)]
        term := .jump (to 6 [i 0]) },
      -- 6: copy loop k = v8 < v3
      { params := [8]
        term := .br .ult .w64 (v 8) (v 3) (to 7) (to 8) },
      -- 7: copy v0[k] -> v7[k] with fnInc
      { body := #[
          .assign 9 (.load .w64 .zero (wordElemAddr 0 8)),
          .call [] fnInc [v 9],
          .store .w64 (wordElemAddr 7 8) (v 9),
          .assign 10 (.bin .add .w64 (v 8) (i 1))]
        term := .jump (to 6 [v 10]) },
      -- 8: swap v7[v1] and v7[v2], release old v0, return v7
      { body := #[
          .assign 11 (.load .w64 .zero (wordElemAddr 7 1)),
          .assign 12 (.load .w64 .zero (wordElemAddr 7 2)),
          .store .w64 (wordElemAddr 7 1) (v 12),
          .store .w64 (wordElemAddr 7 2) (v 11),
          .call [] fnDec [v 0]]
        term := .ret [v 7] },
      -- 9: out-of-bounds or i == j -> return v0
      { term := .ret [v 0] } ] }

def arrSwapLimbs : Func :=
  let emptyFn := fnEmptyCapLimbs
  { name := "rt_arr_swap_limbs"
    params := [0, 1, 2]
    results := 1
    blocks := #[
      -- 0: load size = [v0 + 8]; check v1 < size
      { body := #[.assign 3 (.load .w64 .zero (cellAddr 0 8))]
        term := .br .ult .w64 (v 1) (v 3) (to 1) (to 9) },
      -- 1: check v2 < size
      { term := .br .ult .w64 (v 2) (v 3) (to 2) (to 9) },
      -- 2: if v1 == v2 -> return v0
      { term := .br .eq .w64 (v 1) (v 2) (to 9) (to 3) },
      -- 3: load rc = [v0 + 4]; unique (rc == 0) vs shared
      { body := #[.assign 4 (.load .w32 .zero (cellAddr 0 4))]
        term := .br .eq .w32 (v 4) (i 0) (to 4) (to 5) },
      -- 4: unique fast path: swap in place
      { body := #[
          .assign 5 (.load .w64 .zero (wordElemAddr 0 1)),
          .assign 6 (.load .w64 .zero (wordElemAddr 0 2)),
          .store .w64 (wordElemAddr 0 1) (v 6),
          .store .w64 (wordElemAddr 0 2) (v 5)]
        term := .ret [v 0] },
      -- 5: shared/static COW path
      { body := #[
          .call [7] emptyFn [v 3],
          .store .w64 (cellAddr 7 8) (v 3)]
        term := .jump (to 6 [i 0]) },
      -- 6: copy loop k = v8 < v3
      { params := [8]
        term := .br .ult .w64 (v 8) (v 3) (to 7) (to 8) },
      -- 7: copy v0[k] -> v7[k]
      { body := #[
          .assign 9 (.load .w64 .zero (wordElemAddr 0 8)),
          .store .w64 (wordElemAddr 7 8) (v 9),
          .assign 10 (.bin .add .w64 (v 8) (i 1))]
        term := .jump (to 6 [v 10]) },
      -- 8: swap v7[v1] and v7[v2], release old v0, return v7
      { body := #[
          .assign 11 (.load .w64 .zero (wordElemAddr 7 1)),
          .assign 12 (.load .w64 .zero (wordElemAddr 7 2)),
          .store .w64 (wordElemAddr 7 1) (v 12),
          .store .w64 (wordElemAddr 7 2) (v 11),
          .call [] fnDec [v 0]]
        term := .ret [v 7] },
      -- 9: out-of-bounds or i == j -> return v0
      { term := .ret [v 0] } ] }

/-! ## 2. `List` ↔ `Array` Bridges (`arrOfListBoxed`, `arrToListBoxed`, `arrOfListLimbs`, `arrToListLimbs`) -/

/-- Convert a `List α` (`nil` = odd immediate, `cons` = even 2-field cell `[head@+8, tail@+16]`)
into a contiguous boxed `Array α` cell (`scan = 0xFF`, `tag = 0x7F01`). -/
def arrOfListBoxed : Func where
  name := "rt_arr_of_list_boxed"
  params := [0]
  results := 1
  blocks := #[
    -- 0: pass 1 — count length n = v2, cur = v1
    { term := .jump (to 1 [v 0, i 0]) },
    -- 1: while (cur & 1) == 0 (cons cell)
    { params := [1, 2]
      term := .br .tnz .w64 (v 1) (i 1) (to 3) (to 2) },
    -- 2: advance cur = [cur + 16], n = n + 1
    { body := #[
        .assign 3 (.load .w64 .zero (cellAddr 1 16)),
        .assign 4 (.bin .add .w64 (v 2) (i 1))]
      term := .jump (to 1 [v 3, v 4]) },
    -- 3: allocate boxed array of capacity v2, store size = v2
    { body := #[
        .call [5] fnEmptyCapBoxed [v 2],
        .store .w64 (cellAddr 5 8) (v 2)]
      term := .jump (to 4 [v 0, i 0]) },
    -- 4: pass 2 — fill arr[k] from list (cur = v6, k = v7)
    { params := [6, 7]
      term := .br .ult .w64 (v 7) (v 2) (to 5) (to 6) },
    -- 5: elem = [cur + 8]; fnInc(elem); arr[k] = elem; cur = [cur + 16]; k++
    { body := #[
        .assign 8 (.load .w64 .zero (cellAddr 6 8)),
        .call [] fnInc [v 8],
        .store .w64 (wordElemAddr 5 7) (v 8),
        .assign 9 (.load .w64 .zero (cellAddr 6 16)),
        .assign 10 (.bin .add .w64 (v 7) (i 1))]
      term := .jump (to 4 [v 9, v 10]) },
    -- 6: return arr
    { term := .ret [v 5] } ]

/-- Convert a contiguous boxed `Array α` cell into a `List α` (`nilTag`, `consTag`). -/
def arrToListBoxed (nilTag consTag : Nat) : Func :=
  let nilW : Word := ctor0Word nilTag
  let consHdr : Word := immortalHeader 2 consTag
  { name := "rt_arr_to_list_boxed"
    params := [0]
    results := 1
    blocks := #[
      -- 0: sz = [v0 + 8], acc = nilW
      { body := #[
          .assign 1 (.load .w64 .zero (cellAddr 0 8)),
          .assign 2 (.arg (.imm consHdr))]
        term := .jump (to 1 [v 1, .imm nilW]) },
      -- 1: loop idx = v3 (counts down to 0), acc = v4
      { params := [3, 4]
        term := .br .eq .w64 (v 3) (i 0) (to 5) (to 2) },
      -- 2: idx' = idx - 1; bump-allocate 24-byte List.cons cell
      { body := #[
          .assign 5 (.bin .sub .w64 (v 3) (i 1)),
          .assign 6 (.load .w64 .zero (wordElemAddr 0 5)),
          .call [] fnInc [v 6],
          .assign 7 (.load .w64 .zero (ctx bumpOff)),
          .assign 8 (.load .w64 .zero (ctx limitOff))]
        term := .brOvf .addC 9 (v 7) (i 24) (to 3) (to 6) },
      -- 3: check next <= limit
      { term := .br .ule .w64 (v 9) (v 8) (to 4) (to 6) },
      -- 4: commit bump, initialize cons cell [hdr, elem, acc]
      { body := #[
          .store .w64 (ctx bumpOff) (v 9),
          .store .w64 (cellAddr 7 0) (v 2),
          .store .w64 (cellAddr 7 8) (v 6),
          .store .w64 (cellAddr 7 16) (v 4)]
        term := .jump (to 1 [v 5, v 7]) },
      -- 5: done -> return acc
      { term := .ret [v 4] },
      -- 6: heap exhausted
      { term := .fail .heap, cold := true } ] }

/-- Convert a `List UInt64` into an unboxed `Array UInt64` (`LimbArray`, `scan = 0`, `tag = 0x7F03`),
unboxing both small odd tagged immediates (`< 2^63`) and even 1-scalar-word boxed cells (`≥ 2^63`). -/
def arrOfListLimbs : Func where
  name := "rt_arr_of_list_limbs"
  params := [0]
  results := 1
  blocks := #[
    -- 0: pass 1 — count length n = v2, cur = v1
    { term := .jump (to 1 [v 0, i 0]) },
    -- 1: while (cur & 1) == 0
    { params := [1, 2]
      term := .br .tnz .w64 (v 1) (i 1) (to 3) (to 2) },
    -- 2: advance cur = [cur + 16], n = n + 1
    { body := #[
        .assign 3 (.load .w64 .zero (cellAddr 1 16)),
        .assign 4 (.bin .add .w64 (v 2) (i 1))]
      term := .jump (to 1 [v 3, v 4]) },
    -- 3: allocate limb array of capacity v2, store size = v2
    { body := #[
        .call [5] fnEmptyCapLimbs [v 2],
        .store .w64 (cellAddr 5 8) (v 2)]
      term := .jump (to 4 [v 0, i 0]) },
    -- 4: pass 2 — fill arr[k] from list (cur = v6, k = v7)
    { params := [6, 7]
      term := .br .ult .w64 (v 7) (v 2) (to 5) (to 9) },
    -- 5: load boxed/tagged UInt64 elem = [cur + 8]; test low bit
    { body := #[.assign 8 (.load .w64 .zero (cellAddr 6 8))]
      term := .br .tnz .w64 (v 8) (i 1) (to 6) (to 7) },
    -- 6: odd tagged immediate (< 2^63) -> raw = elem >>> 1
    { body := #[.assign 9 (.bin .shr .w64 (v 8) (i 1))]
      term := .jump (to 8 [v 9]) },
    -- 7: even boxed 1-scalar-word cell (>= 2^63) -> raw = [elem + 8]
    { body := #[.assign 10 (.load .w64 .zero (cellAddr 8 8))]
      term := .jump (to 8 [v 10]) },
    -- 8: store raw limb v11 at arr[k], advance cur & k
    { params := [11]
      body := #[
        .store .w64 (wordElemAddr 5 7) (v 11),
        .assign 12 (.load .w64 .zero (cellAddr 6 16)),
        .assign 13 (.bin .add .w64 (v 7) (i 1))]
      term := .jump (to 4 [v 12, v 13]) },
    -- 9: return arr
    { term := .ret [v 5] } ]

/-- Convert an unboxed `Array UInt64` (`LimbArray`) into a `List UInt64` (`nilTag`, `consTag`),
tagging limbs `< 2^63` and boxing limbs `≥ 2^63` in 16-byte 1-scalar-word cells. -/
def arrToListLimbs (nilTag consTag : Nat) : Func :=
  let nilW : Word := ctor0Word nilTag
  let consHdr : Word := immortalHeader 2 consTag
  let boxHdr : Word := immortalHeader 0 0
  let natLim : Word := UInt64.ofNat IxCC.Rt.natLimit
  { name := "rt_arr_to_list_limbs"
    params := [0]
    results := 1
    blocks := #[
      -- 0: sz = [v0 + 8]
      { body := #[
          .assign 1 (.load .w64 .zero (cellAddr 0 8)),
          .assign 2 (.arg (.imm consHdr)),
          .assign 3 (.arg (.imm boxHdr)),
          .assign 4 (.arg (.imm natLim))]
        term := .jump (to 1 [v 1, .imm nilW]) },
      -- 1: loop idx = v5 (counts down), acc = v6
      { params := [5, 6]
        term := .br .eq .w64 (v 5) (i 0) (to 9) (to 2) },
      -- 2: load raw limb = arr[idx - 1]; check raw < 2^63
      { body := #[
          .assign 7 (.bin .sub .w64 (v 5) (i 1)),
          .assign 8 (.load .w64 .zero (wordElemAddr 0 7))]
        term := .br .ult .w64 (v 8) (v 4) (to 3) (to 4) },
      -- 3: small (< 2^63): tag = (raw <<< 1) ||| 1
      { body := #[
          .assign 9 (.bin .shl .w64 (v 8) (i 1)),
          .assign 10 (.bin .or .w64 (v 9) (i 1))]
        term := .jump (to 6 [v 10]) },
      -- 4: large (>= 2^63): bump-allocate 16-byte 1-scalar-word cell
      { body := #[
          .assign 11 (.load .w64 .zero (ctx bumpOff)),
          .assign 12 (.load .w64 .zero (ctx limitOff))]
        term := .brOvf .addC 13 (v 11) (i 16) (to 5) (to 10) },
      -- 5: check next <= limit and initialize boxed cell
      { term := .br .ule .w64 (v 13) (v 12) (to 11) (to 10) },
      -- 6: elem = v14; bump-allocate 24-byte List.cons cell
      { params := [14]
        body := #[
          .assign 15 (.load .w64 .zero (ctx bumpOff)),
          .assign 16 (.load .w64 .zero (ctx limitOff))]
        term := .brOvf .addC 17 (v 15) (i 24) (to 7) (to 10) },
      -- 7: check next <= limit
      { term := .br .ule .w64 (v 17) (v 16) (to 8) (to 10) },
      -- 8: commit bump, initialize cons cell
      { body := #[
          .store .w64 (ctx bumpOff) (v 17),
          .store .w64 (cellAddr 15 0) (v 2),
          .store .w64 (cellAddr 15 8) (v 14),
          .store .w64 (cellAddr 15 16) (v 6)]
        term := .jump (to 1 [v 7, v 15]) },
      -- 9: done -> return acc
      { term := .ret [v 6] },
      -- 10: heap exhausted
      { term := .fail .heap, cold := true },
      -- 11: commit boxed word cell [boxHdr, raw] and jump to 6
      { body := #[
          .store .w64 (ctx bumpOff) (v 13),
          .store .w64 (cellAddr 11 0) (v 3),
          .store .w64 (cellAddr 11 8) (v 8)]
        term := .jump (to 6 [v 11]) } ] }

/-! ## 3. `ByteArray` ↔ `Array UInt8` Bridges (`byteArrOfArr`, `byteArrToArr`) -/

/-- Pack a boxed `Array UInt8` (`tag = 0x7F01`, tagged `2*b + 1` elements) into a
packed `ByteArray` cell (`scan = 0`, `tag = 0x7F02`, `.w8` payload). -/
def byteArrOfArr : Func where
  name := "rt_byte_arr_of_arr"
  params := [0]
  results := 1
  blocks := #[
    -- 0: sz = [v0 + 8]; allocate packed ByteArray of cap sz, store size = sz
    { body := #[
        .assign 1 (.load .w64 .zero (cellAddr 0 8)),
        .call [2] fnByteEmptyCap [v 1],
        .store .w64 (cellAddr 2 8) (v 1)]
      term := .jump (to 1 [i 0]) },
    -- 1: loop k = v3 < v1
    { params := [3]
      term := .br .ult .w64 (v 3) (v 1) (to 2) (to 3) },
    -- 2: load tagged UInt8, untag >>> 1, store .w8 at b[k]
    { body := #[
        .assign 4 (.load .w64 .zero (wordElemAddr 0 3)),
        .assign 5 (.bin .shr .w64 (v 4) (i 1)),
        .store .w8 (byteElemAddr 2 3) (v 5),
        .assign 6 (.bin .add .w64 (v 3) (i 1))]
      term := .jump (to 1 [v 6]) },
    -- 3: return b
    { term := .ret [v 2] } ]

/-- Unpack a packed `ByteArray` cell (`tag = 0x7F02`) into a boxed `Array UInt8`
(`tag = 0x7F01`, tagged `2*b + 1` elements). -/
def byteArrToArr : Func where
  name := "rt_byte_arr_to_arr"
  params := [0]
  results := 1
  blocks := #[
    -- 0: sz = [v0 + 8]; allocate boxed Array of cap sz, store size = sz
    { body := #[
        .assign 1 (.load .w64 .zero (cellAddr 0 8)),
        .call [2] fnEmptyCapBoxed [v 1],
        .store .w64 (cellAddr 2 8) (v 1)]
      term := .jump (to 1 [i 0]) },
    -- 1: loop k = v3 < v1
    { params := [3]
      term := .br .ult .w64 (v 3) (v 1) (to 2) (to 3) },
    -- 2: load .w8 at b[k], retag (byte <<< 1) ||| 1, store .w64 at a[k]
    { body := #[
        .assign 4 (.load .w8 .zero (byteElemAddr 0 3)),
        .assign 5 (.bin .shl .w64 (v 4) (i 1)),
        .assign 6 (.bin .or .w64 (v 5) (i 1)),
        .store .w64 (wordElemAddr 2 3) (v 6),
        .assign 7 (.bin .add .w64 (v 3) (i 1))]
      term := .jump (to 1 [v 7]) },
    -- 3: return a
    { term := .ret [v 2] } ]

/-- Alias-safe value increment `(x)`:
* Immediate (odd): no-op.
* Dynamic cell (`rc ≥ 0`, e.g. `Array` / `ByteArray` / `LimbArray`): `rc := rc + 1`.
* Static `.rodata` (`rc < 0`, `scan = 0` or `0xFF`): no-op (zero writes to `.rodata`).
* Immortal constructor (`rc < 0`, `1 ≤ scan ≤ 254`): recursively increments its `scan`
  object fields so dynamic arrays stored inside shared immortal constructors safely COW. -/
def arrIncValue : Func where
  name := "rt_arr_inc_val"
  params := [0]
  results := 0
  blocks := #[
    -- 0: immediate check
    { term := .br .tnz .w64 (v 0) (i 1) (to 6) (to 1) },
    -- 1: load rc = [v0 + 4]; dynamic (rc >= 0) vs immortal/static (rc < 0)
    { body := #[.assign 1 (.load .w32 .zero (cellAddr 0 4))]
      term := .br .slt .w32 (v 1) (i 0) (to 3) (to 2) },
    -- 2: dynamic cell: increment rc in place
    { body := #[
        .assign 2 (.bin .add .w32 (v 1) (i 1)),
        .store .w32 (cellAddr 0 4) (v 2)]
      term := .ret [] },
    -- 3: immortal/static cell: check scan == 0 (ByteArray, LimbArray, scalar ctor)
    { body := #[.assign 3 (.load .w8 .zero (cellAddr 0 0))]
      term := .br .eq .w64 (v 3) (i 0) (to 6) (to 7) },
    -- 4: loop k = v4 < v3 over immortal ctor object fields
    { params := [4]
      term := .br .ult .w64 (v 4) (v 3) (to 5) (to 6) },
    -- 5: load field [v0 + 8 + k*8], recursively inc, k++
    { body := #[
        .assign 5 (.load .w64 .zero { base := some (.v 0), index := some (4, .eight), disp := 8 }),
        .call [] fnIncVal [v 5],
        .assign 6 (.bin .add .w64 (v 4) (i 1))]
      term := .jump (to 4 [v 6]) },
    -- 6: done
    { term := .ret [] },
    -- 7: check scan == 0xFF (static .rodata boxed array)
    { term := .br .eq .w64 (v 3) (i 0xFF) (to 6) (to 8) },
    -- 8: enter field loop for immortal ctor (1 <= scan <= 254)
    { term := .jump (to 4 [i 0]) } ]

/-! ## 4. Relocation (`relocateFunc`, `extendedArrayRuntimeFuncs`) -/

/-- Shift every internal callee `FunId` in a `Lir.Stmt` by `+ base`. -/
def relocateStmt (base : FunId) : Stmt → Stmt
  | .call rs f as => .call rs (f + base) as
  | s => s

/-- Shift every internal tail-callee `FunId` in a `Lir.Term` by `+ base`. -/
def relocateTerm (base : FunId) : Term → Term
  | .tail f as => .tail (f + base) as
  | t => t

/-- Shift every internal `FunId` in a `Lir.Block` by `+ base`. -/
def relocateBlock (base : FunId) (b : Block) : Block :=
  { b with
    body := b.body.map (relocateStmt base)
    term := relocateTerm base b.term }

/-- Shift every internal `FunId` in a `Lir.Func` by `+ base` and split critical edges. -/
def relocateFunc (base : FunId) (fn : Func) : Func :=
  Func.splitCriticalEdges { fn with blocks := fn.blocks.map (relocateBlock base) }

/-- The complete 36-proc native array runtime table (`0..26` from `arrayRuntimeFuncs` plus
`27..35` swap, `List`/`ByteArray` bridges, and `arrIncValue`), relocated to start at `FunId` `base`. -/
def extendedArrayRuntimeFuncs (base : FunId) (nilTag consTag : Nat) : List Func :=
  let extra : List Func :=
    [ arrSwapBoxed, arrSwapLimbs,
      arrOfListBoxed, arrToListBoxed nilTag consTag,
      arrOfListLimbs, arrToListLimbs nilTag consTag,
      byteArrOfArr, byteArrToArr,
      arrIncValue ]
  (arrayRuntimeFuncs.toList ++ extra).map (relocateFunc base)

theorem extendedArrayRuntimeFuncs_length (base : FunId) (nilTag consTag : Nat) :
    (extendedArrayRuntimeFuncs base nilTag consTag).length = extendedArrayRuntimeCount := by
  rfl

/-! ## 5. DR4 Static String Materializer (`strLitProc`) -/

/-- Pack an 8-byte-aligned `ByteArray` into its little-endian 64-bit words. -/
def bytesToWords64 (bs : ByteArray) : List Word :=
  let nWords := bs.size / 8
  (List.range nWords).map fun wIdx =>
    let base := 8 * wIdx
    let b := fun j => (bs.get! (base + j)).toUInt64
    b 0 ||| (b 1 <<< 8) ||| (b 2 <<< 16) ||| (b 3 <<< 24) |||
    (b 4 <<< 32) ||| (b 5 <<< 40) ||| (b 6 <<< 48) ||| (b 7 <<< 56)

theorem bytesToWords64_length (bs : ByteArray) :
    (bytesToWords64 bs).length = bs.size / 8 := by
  simp [bytesToWords64]

/-- Position-independent LIR materializer for a static UTF-8 string literal `s`:
allocates `24 + alignUp s.utf8ByteSize 8` bytes from the bump region and stores the
exact 64-bit words of `X86.ELFRodata.encodeStaticString s` (header with `rc = 0x80000000`,
`tag = 0x7F02`, `scan = 0`, `size`, `cap`, and padded UTF-8 payload).

Has zero critical edges by construction (separate cold `.fail .heap` blocks), and fails
immediately with `.heap` if `cell.size ≥ 2^31` (keeping every `disp32` and `imm32` in range). -/
def strLitProc (idx : Nat) (s : String) : Func :=
  let cell : ByteArray := ⟨⟨encodeStaticStringK s⟩⟩
  let nBytes := cell.size
  if nBytes ≥ 2 ^ 31 then
    { name := s!"rt_str_lit_{idx}"
      params := []
      results := 1
      blocks := #[{ term := .fail .heap, cold := true }] }
  else
    let words := bytesToWords64 cell
    let storeStmts : List Stmt :=
      words.zipIdx.flatMap fun (w, k) =>
        let reg := 3 + k
        [ .assign reg (.arg (.imm w)),
          .store .w64 (cellAddr 0 (8 * k)) (v reg) ]
    { name := s!"rt_str_lit_{idx}"
      params := []
      results := 1
      blocks := #[
        -- 0: bump = [ctx - 40], limit = [ctx - 32], next = bump + nBytes
        { body := #[
            .assign 0 (.load .w64 .zero (ctx bumpOff)),
            .assign 1 (.load .w64 .zero (ctx limitOff))]
          term := .brOvf .addC 2 (v 0) (i nBytes) (to 1) (to 3) },
        -- 1: check next <= limit
        { term := .br .ule .w64 (v 2) (v 1) (to 2) (to 4) },
        -- 2: commit bump, store exact encodeStaticString words, return bump
        { body := (#[.store .w64 (ctx bumpOff) (v 2)] ++ storeStmts.toArray)
          term := .ret [v 0] },
        -- 3: heap exhausted (overflow)
        { term := .fail .heap, cold := true },
        -- 4: heap exhausted (limit)
        { term := .fail .heap, cold := true } ] }

/-- Direct `.rodata` static string pointer getter (used when `rodataBase` is fixed):
returns the read-only `.rodata` address `addr` with zero allocation and zero writes. -/
def rodataStrProc (idx : Nat) (addr : Word) : Func where
  name := s!"rt_str_rodata_{idx}"
  params := []
  results := 1
  blocks := #[
    { body := #[.assign 0 (.arg (.imm addr))]
      term := .ret [v 0] } ]

end IxCC.Rt.Rc.Array
