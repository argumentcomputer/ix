import Compilatrix.Rt.Rc.Layout

set_option autoImplicit false
namespace Compilatrix.Rt.Rc.Procs
open Lir


def v (x : VReg) : Arg := .v x
def i (n : Nat) : Arg := .imm (UInt64.ofNat n)
def to (b : Label) (args : List Arg := []) : Edge := ⟨b, args⟩
def cellAddr (x : VReg) (off : Int := 0) : Addr := { base := some (.v x), disp := off }
def ctx (off : Int) : Addr := { base := some .ctx, disp := off }

/-- Reserve one class-sized cell, preferring recycled storage, with a fresh
unique header. Fields are still uninitialized: caller owns a reserved cell,
not a published live object, until every field store and token transfer.
One-cell bump refill is the bounded first implementation, not batch refill.
Invalid compile-time layouts produce a trapping function. -/
def alloc (fields tag : Nat) : Func :=
  if fields == 0 || fields ≥ 32 || tag > maxTag then
    { name := "rt_rc_alloc_declined", params := [], results := 1,
      blocks := #[{ term := .trap }] }
  else
    { name := s!"rt_rc_alloc_{fields}_{tag}", params := [], results := 1,
      blocks := #[
        { body := #[.assign 0 (.load .w64 .zero (ctx (Int.ofNat (8 * smallClass fields))))]
          term := .br .eq .w64 (v 0) (i 0) (to 2) (to 1) },
        { body := #[.assign 1 (.load .w64 .zero (cellAddr 0)),
            .store .w64 (ctx (Int.ofNat (8 * smallClass fields))) (v 1)]
          term := .jump (to 5 [v 0]) },
        { body := #[.assign 2 (.load .w64 .zero (ctx bumpOff)),
            .assign 3 (.load .w64 .zero (ctx limitOff))]
          term := .brOvf .addC 4 (v 2) (i (cellBytes fields)) (to 3) (to 6) },
        { term := .br .ule .w64 (v 4) (v 3) (to 4) (to 6) },
        { body := #[.store .w64 (ctx bumpOff) (v 4)]
          term := .jump (to 5 [v 2]) },
        { params := [5]
          body := #[.store .w64 (cellAddr 5) (.imm (dynamicHeader fields (smallClass fields) tag 1))]
          term := .ret [v 5] },
        { term := .fail .heap, cold := true }] }

/-- Increment one logical token. Immediate and static inputs are untouched.
Overflow fails before modifying the header; proof precondition excludes zero
and malformed pointers and establishes the live-cell memory predicate. -/
def inc : Func where
  name := "rt_rc_inc"
  params := [0]
  results := 0
  blocks := #[
    { term := .br .tnz .w64 (v 0) (i 1) (to 5) (to 1) },
    { body := #[.assign 1 (.load .w32 .zero (cellAddr 0 4))]
      term := .br .slt .w32 (v 1) (i 0) (to 5) (to 2) },
    { term := .br .eq .w32 (v 1) (i (maxCount - 1)) (to 4) (to 3) },
    { body := #[.assign 2 (.bin .add .w32 (v 1) (i 1)),
        .store .w32 (cellAddr 0 4) (v 2)]
      term := .jump (to 5) },
    { term := .fail .heap, cold := true },
    { term := .ret [] }]

/-- Drop one token using dead parents as a bounded-storage continuation.
Precondition: every reachable dynamic cell has 1..31 fully scanned fields,
class=fields+1, and the ownership balance invariant. No recursive calls.
The continuation relation is specified in INTERFACE.md; its proof is open. -/
def dec : Func where
  name := "rt_rc_dec"
  params := [0]
  results := 0
  blocks := #[
    -- 0: current value and no suspended parent
    { term := .jump (to 1 [v 0, i 0]) },
    -- 1: dispatch current; v2 is the parent chain
    { params := [1, 2]
      term := .br .tnz .w64 (v 1) (i 1) (to 6 [v 2]) (to 2) },
    -- 2: static needs no writes
    { body := #[.assign 3 (.load .w32 .zero (cellAddr 1 4))]
      term := .br .slt .w32 (v 3) (i 0) (to 6 [v 2]) (to 3) },
    { term := .br .eq .w32 (v 3) (i 0) (to 5) (to 4) },
    -- 4: a shared child's body remains live
    { body := #[.assign 4 (.bin .sub .w32 (v 3) (i 1)),
        .store .w32 (cellAddr 1 4) (v 4)]
      term := .jump (to 6 [v 2]) },
    -- 5: detach first edge before installing continuation link
    { body := #[.assign 5 (.load .w8 .zero (cellAddr 1)),
        .assign 6 (.load .w64 .zero (cellAddr 1 8)),
        .assign 7 (.bin .sub .w64 (v 5) (i 1)),
        .store .w64 (cellAddr 1 8) (v 2), .store .w8 (cellAddr 1) (v 7)]
      term := .jump (to 1 [v 6, v 1]) },
    -- 6: advance the continuation, or finish
    { params := [8]
      term := .br .eq .w64 (v 8) (i 0) (to 10) (to 7) },
    { body := #[.assign 9 (.load .w8 .zero (cellAddr 8)),
        .assign 10 (.load .w8 .zero (cellAddr 8 1))]
      term := .br .eq .w64 (v 9) (i 0) (to 9) (to 8) },
    -- 8: index=class-1-remaining, hence original field >=1
    { body := #[.assign 11 (.bin .sub .w64 (v 10) (i 1)),
        .assign 12 (.bin .sub .w64 (v 11) (v 9)),
        .assign 13 (.load .w64 .zero
          { base := some (.v 8), index := some (12, .eight), disp := 8 }),
        .assign 14 (.bin .sub .w64 (v 9) (i 1)), .store .w8 (cellAddr 8) (v 14)]
      term := .jump (to 1 [v 13, v 8]) },
    -- 9: save predecessor before recycling; class survives until this point
    { body := #[.assign 15 (.load .w64 .zero (cellAddr 8 8)),
        .assign 16 (.load .w64 .zero { base := some .ctx, index := some (10, .eight) }),
        .store .w64 (cellAddr 8) (v 16),
        .store .w64 { base := some .ctx, index := some (10, .eight) } (v 8)]
      term := .jump (to 6 [v 15]) },
    { term := .ret [] }]

end Compilatrix.Rt.Rc.Procs
