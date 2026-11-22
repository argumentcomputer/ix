import IxCC.Rt.Layout

/-! # `cx_init`

The runtime's first procedure, a fixed Lir function exported as
`cx_result cx_init(void *region, uint64_t size, uint64_t stack_budget)`.
The export wrapper points `ctx` 64 bytes into the region, so
`ctx − 64` is the region's base. `cx_init` checks that

* the base is 8-aligned,
* the region has at least `minRegion` (4 KiB) bytes, and
* it does not wrap: `base + size < 2^63` (so the allocator's `lea` never
  wraps either),

failing with `fail heap` (status 1) otherwise. It then stores the stack
budget, the bump pointer (the first 64-byte boundary after the 640-byte
context block), the limit (`base + size`) and the region base, zeroes the
reserved words and the 71 free-list heads, and returns the bytes left for
objects (`limit − bump`).

It is straight-line apart from its checks, each a separate cold block, so it
is `Lir.WellFormed` as written and runs without charging the clock. Both
arguments are words (`ArgRep.word` at the wrapper). -/

namespace IxCC.Rt.Procs

open IxCC.Lir

private def v (x : VReg) : Arg := .v x
private def i (n : Nat) : Arg := .imm (UInt64.ofNat n)
private def to (l : Label) : Edge := ⟨l, []⟩
private def ctxAt (d : Int) : Addr := { base := some .ctx, disp := d }
private def zero (d : Int) : Stmt := .store .w64 (ctxAt d) (.imm 0)

/-- The symbol of `cx_init`. -/
def initSymbol : String := "cx_init"

/-- Registers: `v0` size, `v1` stack budget, `v2` base, `v3` misalignment,
`v4` limit, `v5`/`v6` the first object, `v7` the bytes left. -/
def cxInit : Func where
  name := initSymbol
  params := [0, 1]
  results := 1
  conv := .sysvExport initSymbol
  blocks := #[
    -- b0: base := ctx − 64, which must be 8-aligned
    { body := #[.assign 2 (.addr (ctxAt (-(ctxOffset : Int)))), .assign 3 (.bin .and .w64 (v 2) (i 7))]
      term := .br .ne .w64 (v 3) (i 0) (to 1) (to 2) },
    { term := .fail .heap, cold := true },
    -- b2: at least `minRegion` bytes
    { term := .br .ult .w64 (v 0) (i minRegion) (to 3) (to 4) },
    { term := .fail .heap, cold := true },
    -- b4: limit := base + size without a carry
    { term := .brOvf .addC 4 (v 2) (v 0) (to 5) (to 6) },
    -- b5: and below 2^63
    { term := .br .slt .w64 (v 4) (i 0) (to 7) (to 8) },
    { term := .fail .heap, cold := true },
    { term := .fail .heap, cold := true },
    -- b8: the fields, the reserved words and the heads
    { body := (#[
        .assign 5 (.addr { base := some (.v 2), disp := (ctxBlockBytes + objectAlign - 1 : Nat) }),
        .assign 6 (.bin .and .w64 (v 5) (.imm (0 - UInt64.ofNat objectAlign))),
        .store .w64 (ctxAt stackBudgetOff) (v 1),
        .store .w64 (ctxAt bumpOff) (v 6),
        .store .w64 (ctxAt limitOff) (v 4),
        .store .w64 (ctxAt regionBaseOff) (v 2)] ++
        (reservedOffs.map zero).toArray ++
        (headClasses.map fun c => zero (headOffset c)).toArray ++
        #[.assign 7 (.bin .sub .w64 (v 4) (v 6))])
      term := .ret [v 7] }]

end IxCC.Rt.Procs
