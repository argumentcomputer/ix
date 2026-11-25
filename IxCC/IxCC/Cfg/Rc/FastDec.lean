import IxCC.Cfg.Rc.Layout

/-! # Fast Specialized Counted-Heap Decrement (`Cfg.Rc.FastDec`)

Replaces `Rt.Rc.Gen.dec` at `l.decProc` with a semantically identical
(byte-for-byte memory- and ctx-identical on every input state, including
arbitrary memory) specialized decrement loop:

1. Checks `rc == 0` first on `b2` (single-branch fast path for freeing unique
   trees in `binarytrees`, `const_fold`, `nqueens`, `list-qsort`).
2. Specializes `scan == 2` (`Node(l, r)`, `List.cons`, `Pair`, `Expr.add`) and
   `scan == 1` (`Expr.val`, `Option.some`):
   - When all children are immediates (`f0 & 1 != 0`, `f1 & 1 != 0`), recycles
     the cell immediately without storing/reloading `[v+4]` (eliminating 2
     store-forwarding stalls and 10 basic blocks per leaf).
   - When `f0` is immediate and `f1` is a pointer (or `scan == 1` with pointer
     `f0`), jumps straight to `b2(child, v)` without storing `[v+4] = 0`
     (already `0` on entry to `b5`!).
   - When a child is a known pointer (`f & 1 == 0`), jumps straight to `b2`
     bypassing the redundant `tnz` check in `b1`.
3. Moves `[v8+0]` (`scan`) load out of `b7` into `b8` (only needed when
   `rem != 0`), and when `b8` detaches an immediate field, jumps directly to
   `b9` (if `rem - 1 == 0`) or `b7` (otherwise), bypassing `b1 → b6`.

Every dispatch edge in `b5..b24` is strictly forward (`0` clock charges), and
every loop-back edge makes `1` charge matching `1..3` charges in `Gen.dec`.
Max live virtual registers is 4 (fitting in `decProc`'s exact 5 caller-saved
clobber registers `[.rax, .rcx, .rdx, .rsi, .rdi]` with zero spills).
Semantic preservation is proved in `IxCC.Cfg.Rc.Proof.FastDec`. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.FastDec

open IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Procs (v i to cellAddr)

def fastDec : Lir.Func where
  name := "rt_rc_dec"
  params := [0]
  results := 0
  blocks := #[
    -- 0: entry
    { term := .jump (to 1 [v 0, i 0]) },
    -- 1: dispatch v1 (cur), v2 (parent)
    { params := [1, 2]
      term := .br .tnz .w64 (v 1) (i 1) (to 6 [v 2]) (to 2 [v 1, v 2]) },
    -- 2: heap pointer v20, parent v21; load rc and check == 0 first
    { params := [20, 21]
      body := #[.assign 3 (.load .w32 .zero (cellAddr 20 4))]
      term := .br .eq .w32 (v 3) (i 0) (to 5) (to 3) },
    -- 3: non-zero count: static (<s 0) skips, else shared (> 0) decrements
    { term := .br .slt .w32 (v 3) (i 0) (to 6 [v 21]) (to 4) },
    -- 4: shared cell: rc -= 1
    { body := #[.assign 4 (.bin .sub .w32 (v 3) (i 1)),
        .store .w32 (cellAddr 20 4) (v 4)]
      term := .jump (to 6 [v 21]) },
    -- 5: dead cell (`[v20+4] == 0`): load scan count, specialize scan == 2
    { body := #[.assign 5 (.load .w8 .zero (cellAddr 20))]
      term := .br .eq .w64 (v 5) (i 2) (to 11) (to 14) },
    -- 6: advance parent chain v8, or finish
    { params := [8]
      term := .br .eq .w64 (v 8) (i 0) (to 10) (to 7) },
    -- 7: load ONLY remaining field count `[v8+4]` first
    { body := #[.assign 9 (.load .w32 .zero (cellAddr 8 4))]
      term := .br .eq .w64 (v 9) (i 0) (to 9) (to 8) },
    -- 8: parent has remaining fields: load scan `[v8+0]`, load next child, store `v9 - 1`
    { body := #[.assign 10 (.load .w8 .zero (cellAddr 8)),
        .assign 12 (.bin .sub .w64 (v 10) (v 9)),
        .assign 13 (.load .w64 .zero { base := some (.v 8), index := some (12, .eight), disp := 8 }),
        .assign 14 (.bin .sub .w64 (v 9) (i 1)),
        .store .w32 (cellAddr 8 4) (v 14)]
      term := .br .tnz .w64 (v 13) (i 1) (to 22) (to 23) },
    -- 9: recycle finished parent v8 onto its class's free list; resume predecessor
    { body := #[.assign 11 (.load .w8 .zero (cellAddr 8 1)),
        .assign 15 (.load .w64 .zero (cellAddr 8 8)),
        .assign 16 (.load .w64 .zero { base := some .ctx, index := some (11, .eight) }),
        .store .w64 (cellAddr 8) (v 16),
        .store .w64 { base := some .ctx, index := some (11, .eight) } (v 8)]
      term := .jump (to 6 [v 15]) },
    -- 10: done
    { term := .ret [] },
    -- 11: scan == 2 fast path: load f0
    { body := #[.assign 22 (.load .w64 .zero (cellAddr 20 8))]
      term := .br .tnz .w64 (v 22) (i 1) (to 12) (to 18) },
    -- 12: scan == 2 & f0 immediate: guard v20 == 0 (cold) before skipping b6(v20)
    { term := .br .eq .w64 (v 20) (i 0) (to 24) (to 13) },
    -- 13: scan == 2 & f0 immediate & v20 != 0: load f1
    { body := #[.assign 23 (.load .w64 .zero (cellAddr 20 16))]
      term := .br .tnz .w64 (v 23) (i 1) (to 19) (to 20 [v 23]) },
    -- 14: scan != 2: check scan == 0 -> b21 | b15
    { term := .br .eq .w64 (v 5) (i 0) (to 21) (to 15) },
    -- 15: scan ∉ {0, 2}: check scan == 1 -> b16 | b24
    { term := .br .eq .w64 (v 5) (i 1) (to 16) (to 24) },
    -- 16: scan == 1 fast path: load f0
    { body := #[.assign 27 (.load .w64 .zero (cellAddr 20 8))]
      term := .br .tnz .w64 (v 27) (i 1) (to 17) (to 20 [v 27]) },
    -- 17: scan == 1 & f0 immediate: guard v20 == 0 (cold) before skipping b6(v20)
    { term := .br .eq .w64 (v 20) (i 0) (to 24) (to 19) },
    -- 18: scan == 2 & f0 pointer: store parent & rem = 1, jump directly to b2(f0, v20)
    { body := #[.store .w64 (cellAddr 20 8) (v 21),
        .store .w32 (cellAddr 20 4) (i 1)]
      term := .jump (to 2 [v 22, v 20]) },
    -- 19: fast leaf recycle (scan == 2 imm/imm OR scan == 1 imm, v20 != 0)
    { body := #[.store .w64 (cellAddr 20 8) (v 21),
        .assign 24 (.load .w8 .zero (cellAddr 20 1)),
        .assign 25 (.load .w64 .zero { base := some .ctx, index := some (24, .eight) }),
        .store .w64 (cellAddr 20) (v 25),
        .store .w64 { base := some .ctx, index := some (24, .eight) } (v 20)]
      term := .jump (to 6 [v 21]) },
    -- 20: scan == 2 (f0 imm, f1 ptr) OR scan == 1 (f0 ptr): `[v20+4]` already 0!
    { params := [26]
      body := #[.store .w64 (cellAddr 20 8) (v 21)]
      term := .jump (to 2 [v 26, v 20]) },
    -- 21: recycle a cell without scanned fields; continue with parent chain
    { body := #[.assign 17 (.load .w8 .zero (cellAddr 20 1)),
        .assign 18 (.load .w64 .zero { base := some .ctx, index := some (17, .eight) }),
        .store .w64 (cellAddr 20) (v 18),
        .store .w64 { base := some .ctx, index := some (17, .eight) } (v 20)]
      term := .jump (to 6 [v 21]) },
    -- 22: from b8 when v13 is immediate: if v14 == 0 recycle v8 directly, else loop to b7
    { term := .br .eq .w32 (v 14) (i 0) (to 9) (to 7) },
    -- 23: from b8 when v13 is pointer: jump directly to b2(v13, v8)
    { term := .jump (to 2 [v 13, v 8]) },
    -- 24: general dead cell (scan ≥ 3, or cold v20 == 0 fallback)
    { body := #[.assign 6 (.load .w64 .zero (cellAddr 20 8)),
        .assign 7 (.bin .sub .w64 (v 5) (i 1)),
        .store .w64 (cellAddr 20 8) (v 21),
        .store .w32 (cellAddr 20 4) (v 7)]
      term := .jump (to 1 [v 6, v 20]) }]

/-- Install `fastDec` at `l.decProc` if that slot currently holds `Rt.Rc.Gen.dec`. -/
def install (l : Layout) (p : Lir.Program) : Lir.Program :=
  { p with
    funcs := p.funcs.mapIdx fun idx F =>
      if idx == l.decProc && F == Rt.Rc.Gen.dec then fastDec else F }

end IxCC.Cfg.Rc.FastDec
