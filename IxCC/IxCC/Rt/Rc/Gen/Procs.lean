import IxCC.Rt.Rc.Classes
import IxCC.Rt.Rc.Procs

/-! # The counted heap's procedures for general cell layouts

Allocation by layout (`alloc`), release (`dec`) and the uniqueness test (`isUnique`) for cells of
any layout `CellLayout` describes: `nobj ≤ 254` scanned fields, then `nscalar` raw scalar words, in
any of the 71 size classes. On the layouts of `Rt.Rc.Procs` (1–31 scanned fields, no scalar word)
`alloc` is that module's `alloc` exactly (`alloc_ofFields`); `dec` differs from that module's `dec`
in where it keeps its countdown, so that the field index no longer depends on the class. -/

set_option autoImplicit false
namespace IxCC.Rt.Rc.Gen
open Lir
open IxCC.Rt.Rc.Procs (v i to cellAddr ctx)

/-- A trapping procedure for a layout the runtime does not allocate (as `Procs.alloc`'s). -/
def declined : Func :=
  { name := "rt_rc_alloc_declined", params := [], results := 1, blocks := #[{ term := .trap }] }

/-- The procedure's name: `Procs.alloc`'s for a scalar-free layout. -/
def allocName (L : CellLayout) : String :=
  if L.nscalar = 0 then s!"rt_rc_alloc_{L.nobj}_{L.tag}" else s!"rt_rc_alloc_{L.nobj}_{L.nscalar}_{L.tag}"

/-- Reserve one cell of the layout's class, preferring that class's free list, else the bump
pointer, with a fresh header (scan count, class, tag, one reference). The fields and scalar words
are stored by the caller (the allocation wrapper) before the cell is published. A layout the runtime
does not allocate gives a trapping procedure. -/
def allocFunc (L : CellLayout) (cls : Nat) : Func :=
  { name := allocName L, params := [], results := 1,
    blocks := #[
      { body := #[.assign 0 (.load .w64 .zero (ctx (Int.ofNat (8 * cls))))]
        term := .br .eq .w64 (v 0) (i 0) (to 2) (to 1) },
      { body := #[.assign 1 (.load .w64 .zero (cellAddr 0)),
          .store .w64 (ctx (Int.ofNat (8 * cls))) (v 1)]
        term := .jump (to 5 [v 0]) },
      { body := #[.assign 2 (.load .w64 .zero (ctx bumpOff)),
          .assign 3 (.load .w64 .zero (ctx limitOff))]
        term := .brOvf .addC 4 (v 2) (i (classBytes cls)) (to 3) (to 6) },
      { term := .br .ule .w64 (v 4) (v 3) (to 4) (to 6) },
      { body := #[.store .w64 (ctx bumpOff) (v 4)]
        term := .jump (to 5 [v 2]) },
      { params := [5]
        body := #[.store .w64 (cellAddr 5) (.imm (dynamicHeader L.nobj cls L.tag 1))]
        term := .ret [v 5] },
      { term := .fail .heap, cold := true }] }

/-- Allocation by layout: `allocFunc` at the layout's class, or a trapping procedure for a layout
the runtime does not allocate. -/
def alloc (L : CellLayout) : Func :=
  match L.cls? with
  | none => declined
  | some cls => if L.ok then allocFunc L cls else declined

theorem alloc_eq {L : CellLayout} {cls : Nat} (hL : L.ok = true) (hc : L.cls? = some cls) :
    alloc L = allocFunc L cls := by
  simp [alloc, hc, hL]

/-- Release one token. As `Procs.dec` (iterative, the parent chain threaded through the first field
of each dead cell being scanned, no recursion), with three changes:
* the countdown of fields still to visit is kept in the dead cell's 32-bit count word (free once the
  count reached zero), not in its scan byte, which keeps the scan count; the next field's index is
  `scan − remaining`, which does not depend on the class;
* a cell with no scanned field (scalar words only) is recycled at once (block 11): its first word is
  a raw scalar, never a child;
* recycling pushes onto the free list of the cell's class, whatever it is (`1 … 71`). -/
def dec : Func where
  name := "rt_rc_dec"
  params := [0]
  results := 0
  blocks := #[
    -- 0: the current value, and no suspended parent
    { term := .jump (to 1 [v 0, i 0]) },
    -- 1: dispatch the current value v1; v2 is the parent chain
    { params := [1, 2]
      term := .br .tnz .w64 (v 1) (i 1) (to 6 [v 2]) (to 2) },
    -- 2: a static cell needs no write
    { body := #[.assign 3 (.load .w32 .zero (cellAddr 1 4))]
      term := .br .slt .w32 (v 3) (i 0) (to 6 [v 2]) (to 3) },
    { term := .br .eq .w32 (v 3) (i 0) (to 5) (to 4) },
    -- 4: a shared cell stays live
    { body := #[.assign 4 (.bin .sub .w32 (v 3) (i 1)),
        .store .w32 (cellAddr 1 4) (v 4)]
      term := .jump (to 6 [v 2]) },
    -- 5: the last reference: a cell without scanned fields is recycled at once
    { body := #[.assign 5 (.load .w8 .zero (cellAddr 1))]
      term := .br .eq .w64 (v 5) (i 0) (to 11) (to 12) },
    -- 6: advance the continuation, or finish
    { params := [8]
      term := .br .eq .w64 (v 8) (i 0) (to 10) (to 7) },
    -- 7: the parent's remaining fields (count word) and scan count
    { body := #[.assign 9 (.load .w32 .zero (cellAddr 8 4)),
        .assign 10 (.load .w8 .zero (cellAddr 8))]
      term := .br .eq .w64 (v 9) (i 0) (to 9) (to 8) },
    -- 8: the next field is `scan − remaining`
    { body := #[.assign 12 (.bin .sub .w64 (v 10) (v 9)),
        .assign 13 (.load .w64 .zero { base := some (.v 8), index := some (12, .eight), disp := 8 }),
        .assign 14 (.bin .sub .w64 (v 9) (i 1)), .store .w32 (cellAddr 8 4) (v 14)]
      term := .jump (to 1 [v 13, v 8]) },
    -- 9: recycle the finished parent onto its class's list; resume its predecessor
    { body := #[.assign 11 (.load .w8 .zero (cellAddr 8 1)),
        .assign 15 (.load .w64 .zero (cellAddr 8 8)),
        .assign 16 (.load .w64 .zero { base := some .ctx, index := some (11, .eight) }),
        .store .w64 (cellAddr 8) (v 16),
        .store .w64 { base := some .ctx, index := some (11, .eight) } (v 8)]
      term := .jump (to 6 [v 15]) },
    -- 10: done
    { term := .ret [] },
    -- 11: recycle a cell without scanned fields; continue with the parent chain
    { body := #[.assign 17 (.load .w8 .zero (cellAddr 1 1)),
        .assign 18 (.load .w64 .zero { base := some .ctx, index := some (17, .eight) }),
        .store .w64 (cellAddr 1) (v 18),
        .store .w64 { base := some .ctx, index := some (17, .eight) } (v 1)]
      term := .jump (to 6 [v 2]) },
    -- 12: detach the first field; the parent link goes in its place, `scan − 1` in the count word
    { body := #[.assign 6 (.load .w64 .zero (cellAddr 1 8)),
        .assign 7 (.bin .sub .w64 (v 5) (i 1)),
        .store .w64 (cellAddr 1 8) (v 2), .store .w32 (cellAddr 1 4) (v 7)]
      term := .jump (to 1 [v 6, v 1]) }]

/-- The uniqueness test: `1` for a dynamic cell whose count word is `0` (one reference), `0` for an
immediate, a shared cell or a static cell (whose count word is negative). Reads one word; writes
nothing. -/
def isUnique : Func where
  name := "rt_rc_is_unique"
  params := [0]
  results := 1
  blocks := #[
    { term := .br .tnz .w64 (v 0) (i 1) (to 3) (to 1) },
    { body := #[.assign 1 (.load .w32 .zero (cellAddr 0 4))]
      term := .br .eq .w32 (v 1) (i 0) (to 2) (to 3) },
    { term := .ret [i 1] },
    { term := .ret [i 0] }]

/-- On the layouts of `Procs` (fewer than 32 scanned fields, no scalar word) allocation by layout is
`Procs.alloc`, name included. -/
theorem alloc_ofFields {n tag : Nat} (h : n < 32) :
    alloc (CellLayout.ofFields n tag) = Procs.alloc n tag := by
  have hc := CellLayout.ofFields_cls (tag := tag) h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold alloc
    split <;> simp [Procs.alloc, CellLayout.ok, CellLayout.ofFields, declined]
  · by_cases ht : tag ≤ maxTag
    · have hok := CellLayout.ofFields_ok hn h ht
      have h0 : (n == 0) = false := by simp; omega
      have h32 : ¬ 32 ≤ n := by omega
      have htag : ¬ maxTag < tag := by omega
      simp only [alloc, hc, hok, ite_true, Procs.alloc, h0, h32, htag, decide_false,
        Bool.or_false, Bool.false_eq_true, ite_false]
      simp [allocFunc, allocName, classBytes, CellLayout.ofFields, smallClass, classWords_small (show n + 1 ≤ 32 by omega),
        cellBytes, Nat.add_comm]
    · have hok : (CellLayout.ofFields n tag).ok = false := by
        cases hk : (CellLayout.ofFields n tag).ok
        · rfl
        · exact absurd (CellLayout.ok_bounds hk).2.2 ht
      have htag : maxTag < tag := by omega
      simp [alloc, hc, hok, Procs.alloc, htag, declined]

end IxCC.Rt.Rc.Gen
