import IxCC.Rt.Rc.Array.Kind
import IxCC.Rt.Rc.Array.Procs

/-! # The array procedures of the certified route

One text per operation, for every element kind (`ElemKind`), placed at any function index: every
callee is named by a table (`Fns`), never by a fixed index, so a program can hold the procedures
anywhere and the specifications (`Proof/Ops*.lean`) hold in every program that does.

Values cross the interface as machine words: an array is the address of its cell, an index, a
size or a capacity a raw word, an element a word of the kind's width (a boxed element a tagged
word). The procedures are:

| procedure | arguments | results | paths |
| --- | --- | --- | --- |
| `alloc k` | capacity | the cell | free list, bump, refused |
| `copy k` | source, offset, destination, offset, count | — | the loop |
| `incs` | array, from, to | — | the loop (boxed only) |
| `size` | array | size | |
| `get k` | array, index | element | in range, trap |
| `set k` | array, index, element | array (and the element to drop, boxed) | unique, copied, trap |
| `push k` | array, element | array | unique with room, unique grown, copied |
| `pop k` | array | array (and the element to drop, boxed) | empty, unique, copied |
| `extract k` | array, start, stop | fresh array | the copy |

* **Uniqueness** is the one-word test of `Gen.isUnique`: the count word `0`. A static cell's count
  is negative, so it is never written: it takes the copying path.
* **The copying path** (a shared or static array) increments the elements it keeps (boxed only,
  `incs`, by the one increment `Procs.inc`), allocates a cell of the kind, copies the elements
  (`copy`), and releases the old array by the one release (`Gen.decArr`), which on a shared or
  static cell only lowers the count or does nothing.
* **Growth** of a unique array moves its elements to a cell of at least twice the capacity, with
  no increment or release (the references move), and recycles the old cell at once.
* **The element to drop.** A boxed `set` or `pop` on a unique array removes a reference the array
  held; the procedure returns it as its second result and the caller releases it with the one
  release. (On the copying path the second result is the element as copied, which the copy's
  increment paid for.) So no array procedure releases an arbitrary value, and every path's
  specification closes over the array invariant.
* **Out of range** `get` and `set` trap (design D2). `pop` of an empty array returns it. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array.Ops

open Lir
open IxCC.Rt (bumpOff limitOff)
open IxCC.Rt.Rc.Procs (v i to cellAddr ctx)

/-- Where the procedures an array operation calls are. -/
structure Fns where
  /-- `Rt.Rc.Procs.inc` -/
  inc : FunId
  /-- `Rt.Rc.Gen.decArr` -/
  dec : FunId
  /-- `arrClassFor` -/
  classFor : FunId
  /-- `arrClassWords` -/
  classWords : FunId
  /-- `alloc k`, for the operation's kind -/
  alloc : FunId
  /-- `copy k`, for the operation's kind -/
  copy : FunId
  /-- `incs` -/
  incs : FunId
  deriving DecidableEq, Repr, Inhabited

/-- A short name of the kind, for symbol names. -/
def kindName : ElemKind → String
  | .boxed => "boxed"
  | .packed .w8 => "u8"
  | .packed .w16 => "u16"
  | .packed .w32 => "u32"
  | .packed .w64 => "u64"

/-- Element `idx` of the cell in `base`: `[base + idx · bytes + 24]`. -/
def elemAt (k : ElemKind) (base idx : VReg) : Addr :=
  { base := some (.v base), index := some (idx, k.scale), disp := 24 }

/-- The free-list head of the class in register `cls`: `[ctx + cls · 8]`. -/
def headAt (cls : VReg) : Addr := { base := some .ctx, index := some (cls, .eight) }

/-! ## Allocation and the two loops -/

/-- An empty cell of kind `k` with capacity at least `n`: the class of `3 + ⌈n · bytes / 8⌉`
words, from its free list or the bump pointer, with one reference, size `0` and the class's
capacity. A capacity above `k.maxCap`, or an exhausted arena, is a heap failure. -/
def alloc (t : Fns) (k : ElemKind) : Func where
  name := s!"rt_arr_alloc_{kindName k}"
  params := [0]
  results := 1
  blocks := #[
    -- 0: a capacity no class holds is refused
    { term := .br .ugt .w64 (v 0) (i k.maxCap) (to 7) (to 1) },
    -- 1: the words, the class, the class's words, the class's free list
    { body := #[.assign 1 (.bin .shl .w64 (v 0) (i k.shift)),
        .assign 2 (.bin .add .w64 (v 1) (i 7)),
        .assign 3 (.bin .shr .w64 (v 2) (i 3)),
        .assign 4 (.bin .add .w64 (v 3) (i 3)),
        .call [5] t.classFor [v 4],
        .call [6] t.classWords [v 5],
        .assign 7 (.load .w64 .zero (headAt 5))]
      term := .br .eq .w64 (v 7) (i 0) (to 3) (to 2) },
    -- 2: pop the free list
    { body := #[.assign 8 (.load .w64 .zero (cellAddr 7)),
        .store .w64 (headAt 5) (v 8)]
      term := .jump (to 6 [v 7]) },
    -- 3: the bump pointer and the class's bytes
    { body := #[.assign 9 (.load .w64 .zero (ctx bumpOff)),
        .assign 10 (.load .w64 .zero (ctx limitOff)),
        .assign 11 (.bin .shl .w64 (v 6) (i 3))]
      term := .brOvf .addC 12 (v 9) (v 11) (to 4) (to 7) },
    -- 4: below the limit
    { term := .br .ule .w64 (v 12) (v 10) (to 5) (to 7) },
    -- 5: commit the bump pointer
    { body := #[.store .w64 (ctx bumpOff) (v 12)]
      term := .jump (to 6 [v 9]) },
    -- 6: header (one reference), size 0, the class's capacity
    { params := [13]
      body := #[.assign 14 (.bin .shl .w64 (v 5) (i 8)),
        .assign 15 (.bin .or .w64 (.imm k.template) (v 14)),
        .assign 16 (.bin .sub .w64 (v 6) (i 3)),
        .assign 17 (.bin .shl .w64 (v 16) (i (3 - k.shift))),
        .store .w64 (cellAddr 13) (v 15),
        .store .w64 (cellAddr 13 8) (i 0),
        .store .w64 (cellAddr 13 16) (v 17)]
      term := .ret [v 13] },
    -- 7: refused, or the arena is exhausted
    { term := .fail .heap, cold := true }]

/-- Copy `n` elements of kind `k` from `src` at `srcOff` to `dst` at `dstOff`, first to last. -/
def copy (k : ElemKind) : Func where
  name := s!"rt_arr_copy_{kindName k}"
  params := [0, 1, 2, 3, 4]
  results := 0
  blocks := #[
    { term := .jump (to 1 [i 0]) },
    -- 1: j = v5
    { params := [5]
      term := .br .ult .w64 (v 5) (v 4) (to 2) (to 3) },
    -- 2: dst[dstOff + j] := src[srcOff + j]
    { body := #[.assign 6 (.bin .add .w64 (v 1) (v 5)),
        .assign 7 (.load k.width .zero (elemAt k 0 6)),
        .assign 8 (.bin .add .w64 (v 3) (v 5)),
        .store k.width (elemAt k 2 8) (v 7),
        .assign 9 (.bin .add .w64 (v 5) (i 1))]
      term := .jump (to 1 [v 9]) },
    { term := .ret [] }]

/-- Increment the elements `from ..< to` of a boxed array, by the one increment. -/
def incs (t : Fns) : Func where
  name := "rt_arr_incs"
  params := [0, 1, 2]
  results := 0
  blocks := #[
    { term := .jump (to 1 [v 1]) },
    -- 1: j = v3
    { params := [3]
      term := .br .ult .w64 (v 3) (v 2) (to 2) (to 3) },
    { body := #[.assign 4 (.load .w64 .zero (elemAt .boxed 0 3)),
        .call [] t.inc [v 4],
        .assign 5 (.bin .add .w64 (v 3) (i 1))]
      term := .jump (to 1 [v 5]) },
    { term := .ret [] }]

/-! ## Reads -/

/-- The size of an array (live or static, of any kind). -/
def size : Func where
  name := "rt_arr_size"
  params := [0]
  results := 1
  blocks := #[{ body := #[.assign 1 (.load .w64 .zero (cellAddr 0 8))], term := .ret [v 1] }]

/-- Element `i`; out of range traps. A boxed element is returned borrowed. -/
def get (k : ElemKind) : Func where
  name := s!"rt_arr_get_{kindName k}"
  params := [0, 1]
  results := 1
  blocks := #[
    { body := #[.assign 2 (.load .w64 .zero (cellAddr 0 8))]
      term := .br .ult .w64 (v 1) (v 2) (to 1) (to 2) },
    { body := #[.assign 3 (.load k.width .zero (elemAt k 0 1))]
      term := .ret [v 3] },
    { term := .trap, cold := true }]

/-! ## Updates -/

/-- The results of a `set` or `pop`: the array, and for a boxed kind the element to drop. -/
def results (k : ElemKind) (arr drop : Arg) : List Arg := if k.isBoxed then [arr, drop] else [arr]

/-- The increments of the copying path, for a boxed kind: elements `from ..< to` of `arr`. -/
def keepStmts (t : Fns) (k : ElemKind) (arr lo hi : Arg) : Array Stmt :=
  if k.isBoxed then #[.call [] t.incs [arr, lo, hi]] else #[]

/-- Element `i` replaced by `x`; out of range traps. Consumes the array and `x`. -/
def set (t : Fns) (k : ElemKind) : Func where
  name := s!"rt_arr_set_{kindName k}"
  params := [0, 1, 2]
  results := if k.isBoxed then 2 else 1
  blocks := #[
    -- 0: the size; out of range traps
    { body := #[.assign 3 (.load .w64 .zero (cellAddr 0 8))]
      term := .br .ult .w64 (v 1) (v 3) (to 1) (to 5) },
    -- 1: unique (count word 0)?
    { body := #[.assign 4 (.load .w32 .zero (cellAddr 0 4))]
      term := .br .eq .w32 (v 4) (i 0) (to 2) (to 3) },
    -- 2: in place: the old element is returned to drop
    { body := #[.assign 5 (.load k.width .zero (elemAt k 0 1)),
        .store k.width (elemAt k 0 1) (v 2)]
      term := .ret (results k (v 0) (v 5)) },
    -- 3: shared or static: keep the elements
    { body := keepStmts t k (v 0) (i 0) (v 3)
      term := .jump (to 4) },
    -- 4: a fresh cell, the copy, the new element; the old array released
    { body := #[.call [6] t.alloc [v 3],
        .call [] t.copy [v 0, i 0, v 6, i 0, v 3],
        .store .w64 (cellAddr 6 8) (v 3),
        .assign 7 (.load k.width .zero (elemAt k 6 1)),
        .store k.width (elemAt k 6 1) (v 2),
        .call [] t.dec [v 0]]
      term := .ret (results k (v 6) (v 7)) },
    -- 5: out of range
    { term := .trap, cold := true }]

/-- The capacity a unique full array grows to: twice its size, at least one more, at most the
largest. -/
def growCap (k : ElemKind) (size : Nat) : Nat :=
  if k.maxCap < 2 * size then size + 1 else max (2 * size) (size + 1)

/-- `x` appended. Consumes the array and `x`. -/
def push (t : Fns) (k : ElemKind) : Func where
  name := s!"rt_arr_push_{kindName k}"
  params := [0, 1]
  results := 1
  blocks := #[
    -- 0: size, capacity, count word; unique?
    { body := #[.assign 2 (.load .w64 .zero (cellAddr 0 8)),
        .assign 3 (.load .w64 .zero (cellAddr 0 16)),
        .assign 4 (.load .w32 .zero (cellAddr 0 4))]
      term := .br .eq .w32 (v 4) (i 0) (to 1) (to 4) },
    -- 1: room?
    { term := .br .ult .w64 (v 2) (v 3) (to 2) (to 3) },
    -- 2: in place
    { body := #[.store k.width (elemAt k 0 2) (v 1),
        .assign 5 (.bin .add .w64 (v 2) (i 1)),
        .store .w64 (cellAddr 0 8) (v 5)]
      term := .ret [v 0] },
    -- 3: grow: move the elements to a larger cell, recycle the old one
    { body := #[.assign 6 (.bin .add .w64 (v 2) (i 1)),
        .assign 7 (.bin .shl .w64 (v 2) (i 1)),
        .assign 8 (.select .ugt .w64 (v 7) (v 6) (v 7) (v 6)),
        .assign 9 (.select .ult .w64 (i k.maxCap) (v 7) (v 6) (v 8)),
        .call [10] t.alloc [v 9],
        .call [] t.copy [v 0, i 0, v 10, i 0, v 2],
        .store k.width (elemAt k 10 2) (v 1),
        .store .w64 (cellAddr 10 8) (v 6),
        .assign 11 (.load .w8 .zero (cellAddr 0 1)),
        .assign 12 (.load .w64 .zero (headAt 11)),
        .store .w64 (cellAddr 0) (v 12),
        .store .w64 (headAt 11) (v 0)]
      term := .ret [v 10] },
    -- 4: shared or static: keep the elements
    { body := keepStmts t k (v 0) (i 0) (v 2)
      term := .jump (to 5) },
    -- 5: a fresh cell of one more, the copy, the new element; the old array released
    { body := #[.assign 13 (.bin .add .w64 (v 2) (i 1)),
        .call [14] t.alloc [v 13],
        .call [] t.copy [v 0, i 0, v 14, i 0, v 2],
        .store k.width (elemAt k 14 2) (v 1),
        .store .w64 (cellAddr 14 8) (v 13),
        .call [] t.dec [v 0]]
      term := .ret [v 14] }]

/-- The last element removed (an empty array is returned as it is). Consumes the array. -/
def pop (t : Fns) (k : ElemKind) : Func where
  name := s!"rt_arr_pop_{kindName k}"
  params := [0]
  results := if k.isBoxed then 2 else 1
  blocks := #[
    -- 0: empty?
    { body := #[.assign 1 (.load .w64 .zero (cellAddr 0 8))]
      term := .br .eq .w64 (v 1) (i 0) (to 1) (to 2) },
    -- 1: empty: nothing to drop
    { term := .ret (results k (v 0) (i 1)) },
    -- 2: unique?
    { body := #[.assign 2 (.bin .sub .w64 (v 1) (i 1)),
        .assign 3 (.load .w32 .zero (cellAddr 0 4))]
      term := .br .eq .w32 (v 3) (i 0) (to 3) (to 4) },
    -- 3: in place: the last element is returned to drop
    { body := #[.assign 4 (.load k.width .zero (elemAt k 0 2)),
        .store .w64 (cellAddr 0 8) (v 2)]
      term := .ret (results k (v 0) (v 4)) },
    -- 4: shared or static: keep all but the last
    { body := keepStmts t k (v 0) (i 0) (v 2)
      term := .jump (to 5) },
    -- 5: a fresh cell, the copy; the old array released
    { body := #[.call [5] t.alloc [v 2],
        .call [] t.copy [v 0, i 0, v 5, i 0, v 2],
        .store .w64 (cellAddr 5 8) (v 2),
        .call [] t.dec [v 0]]
      term := .ret (results k (v 5) (i 1)) }]

/-- `ArraySpec.extractList a start stop` as a fresh array. Reads the array. -/
def extract (t : Fns) (k : ElemKind) : Func where
  name := s!"rt_arr_extract_{kindName k}"
  params := [0, 1, 2]
  results := 1
  blocks := #[
    -- 0: stop' = min stop size; len = stop' - start, or 0
    { body := #[.assign 3 (.load .w64 .zero (cellAddr 0 8)),
        .assign 4 (.select .ult .w64 (v 2) (v 3) (v 2) (v 3)),
        .assign 5 (.bin .sub .w64 (v 4) (v 1)),
        .assign 6 (.select .ult .w64 (v 1) (v 4) (v 5) (i 0)),
        .assign 7 (.bin .add .w64 (v 1) (v 6))]
      term := .jump (to 1) },
    -- 1: keep the elements copied
    { body := keepStmts t k (v 0) (v 1) (v 7)
      term := .jump (to 2) },
    -- 2: a fresh cell, the copy
    { body := #[.call [8] t.alloc [v 6],
        .call [] t.copy [v 0, v 1, v 8, i 0, v 6],
        .store .w64 (cellAddr 8 8) (v 6)]
      term := .ret [v 8] }]

end IxCC.Rt.Rc.Array.Ops
