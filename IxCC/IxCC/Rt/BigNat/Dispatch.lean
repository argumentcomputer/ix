import IxCC.Rt.Lower
import IxCC.Rt.BigNat.Cell

/-! # Phase 4 Arbitrary-Precision `Nat` LIR Lowering & Slow-Path Dispatch (`IxCC.Rt.BigNat.Dispatch`)

Self-contained LIR lowering emit helpers (in `IxCC.Rt.Lower.M`) for every `Nat`
primitive, ready to plug directly into `IxCC.Rt.Lower` in Wave 3b:

* **Fast path preserved:** Every operation keeps its tagged fixnum fast path on
  odd immediates `2n + 1` (`n < 2^63`).
* **1-instruction tag test:** Binary operations compute `a & b` and branch on
  `br .tz (a & b) 1 slow fast` (`test reg, 1; jz slow`); unary `natPred` /
  `Nat.succ` peel branch directly on `br .tz a 1 slow fast`.
* **Zero `fail natOverflow`:** Every overflow exit (`natAdd` carry, `natMul`
  widening overflow, `natShl` bit-loss/shift-width overflow, `rt_nat_pow_big`
  and `rt_nat_gcd_big`) jumps to a cold slow-path call into the linked `BigNat`
  runtime library instead of failing `.natOverflow`.
* **Zero critical edges & strict SSA:** Every multi-predecessor join block is
  entered exclusively by unconditional `.jump` edges carrying the result word;
  every conditional branch targets a single-predecessor block. -/

set_option autoImplicit false

namespace IxCC.Rt.BigNat

open IxCC.Fir (FunId)
open IxCC.Lir (VReg Word)
open IxCC.Rt
open IxCC.Rt.Lower

/-! ## Linked Slow-Path Procedure Table -/

/-- Linked LIR `FunId`s for all arbitrary-precision `Nat` slow-path procedures.
* `pow` names `Rt.Procs.natPowBig slowPow` (which fast-paths small operands and
  tail-calls `slowPow` on big operands or overflow).
* `gcd` names `Rt.Procs.natGcdBig slowGcd` (which fast-paths small operands and
  tail-calls `slowGcd` on big operands).
* Every other field names the linked `BigNat` slow-path procedure directly. -/
structure BigNatProcs where
  add : Lir.FunId
  sub : Lir.FunId
  pred : Lir.FunId
  mul : Lir.FunId
  div : Lir.FunId
  mod : Lir.FunId
  pow : Lir.FunId
  gcd : Lir.FunId
  beq : Lir.FunId
  ble : Lir.FunId
  blt : Lir.FunId
  land : Lir.FunId
  lor : Lir.FunId
  xor : Lir.FunId
  shl : Lir.FunId
  shr : Lir.FunId
  deriving DecidableEq, Repr, Inhabited

/-- Lowering tables for Phase 4 arbitrary-precision `Nat` primitives. -/
structure BigNatTables where
  /-- Tagged words of `Bool.true` and `Bool.false`, when `Bool` is pinned. -/
  bools : Option (Word × Word)
  /-- Linked `BigNat` slow-path LIR procedures. -/
  procs : BigNatProcs
  deriving DecidableEq, Repr, Inhabited

/-! ## Generic Binary Fast/Slow Dispatch Helper -/

/-- Emit a binary `Nat` primitive whose fast fixnum path cannot overflow:
1. 1-instruction low-bit tag test `br .tz (a & b) 1 slowBlk fastBlk`;
2. `fastBlk`: executes `fastBody` and jumps to `joinBlk [fastRes tagAnd]`;
3. `slowBlk` (cold): calls `slowFn [a, b]` and jumps to `joinBlk [rSlow]`;
4. continues in `joinBlk [x]`. Zero critical edges, zero `natOverflow`. -/
def binFastSlow (slowFn : Lir.FunId) (x : VReg) (a b : Lir.Arg)
    (fastBody : List Lir.Stmt) (fastRes : Lir.Arg → Lir.Arg) : M Unit := do
  let tagAnd ← bin .and a b
  let fastBlk ← newLabel
  let slowBlk ← newLabel
  let joinBlk ← newLabel
  close (.br .tz tagAnd (.imm 1) (loc slowBlk) (loc fastBlk))
  let rSlow ← freshReg
  put fastBlk { body := fastBody, term := .jump ⟨.loc joinBlk, [fastRes tagAnd]⟩ }
  put slowBlk {
    body := [.call [rSlow] slowFn [a, b]]
    term := .jump ⟨.loc joinBlk, [.v rSlow]⟩
    cold := true
  }
  openAt joinBlk [x]

/-! ## Per-Primitive Emit Helpers (Zero `.natOverflow`) -/

/-- Arbitrary-precision `natAdd`: fast tagged `brOvf .addC` on `a + (b - 1)`,
with both tag-miss and carry-overflow calling `procs.add`. -/
def natAddBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit := do
  let tagAnd ← bin .and a b
  let fastBlk ← newLabel
  let fastOk ← newLabel
  let slowTag ← newLabel
  let slowOvf ← newLabel
  let joinBlk ← newLabel
  close (.br .tz tagAnd (.imm 1) (loc slowTag) (loc fastBlk))
  let b1 ← freshReg
  let rSum ← freshReg
  let rSlow1 ← freshReg
  let rSlow2 ← freshReg
  put fastBlk {
    body := [.assign b1 (.bin .sub .w64 b (.imm 1))]
    term := .brOvf .addC rSum a (.v b1) (loc fastOk) (loc slowOvf)
  }
  put fastOk { term := .jump ⟨.loc joinBlk, [.v rSum]⟩ }
  put slowTag {
    body := [.call [rSlow1] procs.add [a, b]]
    term := .jump ⟨.loc joinBlk, [.v rSlow1]⟩
    cold := true
  }
  put slowOvf {
    body := [.call [rSlow2] procs.add [a, b]]
    term := .jump ⟨.loc joinBlk, [.v rSlow2]⟩
    cold := true
  }
  openAt joinBlk [x]

/-- Arbitrary-precision truncating `natSub`: fast tagged subtract + `select`,
slow path calling `procs.sub` (with canonical demotion). -/
def natSubBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit := do
  let d ← freshReg
  let r ← freshReg
  let res ← freshReg
  binFastSlow procs.sub x a b
    [ .assign d (.bin .sub .w64 a b)
    , .assign r (.bin .or .w64 (.v d) (.imm 1))
    , .assign res (.select .ult .w64 a b (.imm 1) (.v r)) ]
    (fun _ => .v res)

/-- Arbitrary-precision truncating `natPred`: 1-instruction low-bit test on `a`,
fast tagged `a - 2` with zero guard, slow path calling `procs.pred` (demoting `2^63`). -/
def natPredBig (procs : BigNatProcs) (x : VReg) (a : Lir.Arg) : M Unit := do
  let fastBlk ← newLabel
  let slowBlk ← newLabel
  let joinBlk ← newLabel
  close (.br .tz a (.imm 1) (loc slowBlk) (loc fastBlk))
  let d ← freshReg
  let res ← freshReg
  let rSlow ← freshReg
  put fastBlk {
    body :=
      [ .assign d (.bin .sub .w64 a (.imm 2))
      , .assign res (.select .eq .w64 a (.imm 1) (.imm 1) (.v d)) ]
    term := .jump ⟨.loc joinBlk, [.v res]⟩
  }
  put slowBlk {
    body := [.call [rSlow] procs.pred [a]]
    term := .jump ⟨.loc joinBlk, [.v rSlow]⟩
    cold := true
  }
  openAt joinBlk [x]

/-- Arbitrary-precision `Nat.succ` projection peel (for `Cfg.Instr.proj` on `natSucc`):
identical to `natPredBig`, cleanly demoting `2^63` to tagged `2^63 - 1`. -/
def natSuccPeelBig (procs : BigNatProcs) (x y : VReg) : M Unit :=
  natPredBig procs x (.v y)

/-- Arbitrary-precision `natMul`: fast hardware widening `brOvf .mulOvf` on `(a >>> 1) * (b - 1)`,
with both tag-miss and widening overflow calling `procs.mul`. -/
def natMulBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit := do
  let tagAnd ← bin .and a b
  let fastBlk ← newLabel
  let fastOk ← newLabel
  let slowTag ← newLabel
  let slowOvf ← newLabel
  let joinBlk ← newLabel
  close (.br .tz tagAnd (.imm 1) (loc slowTag) (loc fastBlk))
  let u ← freshReg
  let t ← freshReg
  let p ← freshReg
  let rFast ← freshReg
  let rSlow1 ← freshReg
  let rSlow2 ← freshReg
  put fastBlk {
    body :=
      [ .assign u (.bin .shr .w64 a (.imm 1))
      , .assign t (.bin .sub .w64 b (.imm 1)) ]
    term := .brOvf .mulOvf p (.v u) (.v t) (loc fastOk) (loc slowOvf)
  }
  put fastOk {
    body := [.assign rFast (.bin .or .w64 (.v p) (.imm 1))]
    term := .jump ⟨.loc joinBlk, [.v rFast]⟩
  }
  put slowTag {
    body := [.call [rSlow1] procs.mul [a, b]]
    term := .jump ⟨.loc joinBlk, [.v rSlow1]⟩
    cold := true
  }
  put slowOvf {
    body := [.call [rSlow2] procs.mul [a, b]]
    term := .jump ⟨.loc joinBlk, [.v rSlow2]⟩
    cold := true
  }
  openAt joinBlk [x]

/-- Shared arbitrary-precision `div`/`mod` helper (`o = .udiv` or `.urem`, `zero a` for divisor 0):
fast tagged path checks `b == 1` (`0`) then untags, divides, and retags; any big operand
dispatches to `slowFn`. -/
def natDivModBig (o : Lir.BinOp) (zero : Lir.Arg → Lir.Arg) (slowFn : Lir.FunId)
    (x : VReg) (a b : Lir.Arg) : M Unit := do
  let tagAnd ← bin .and a b
  let fastCheckZ ← newLabel
  let fastZ ← newLabel
  let fastNz ← newLabel
  let slowBlk ← newLabel
  let joinBlk ← newLabel
  close (.br .tz tagAnd (.imm 1) (loc slowBlk) (loc fastCheckZ))
  let u ← freshReg
  let y ← freshReg
  let q ← freshReg
  let rFast ← freshReg
  let rSlow ← freshReg
  put fastCheckZ { term := .br .eq b (.imm 1) (loc fastZ) (loc fastNz) }
  put fastZ { term := .jump ⟨.loc joinBlk, [zero a]⟩, cold := true }
  put fastNz {
    body :=
      [ .assign u (.bin .shr .w64 a (.imm 1))
      , .assign y (.bin .shr .w64 b (.imm 1))
      , .assign q (.bin o .w64 (.v u) (.v y))
      , .assign rFast (retag (.v q)) ]
    term := .jump ⟨.loc joinBlk, [.v rFast]⟩
  }
  put slowBlk {
    body := [.call [rSlow] slowFn [a, b]]
    term := .jump ⟨.loc joinBlk, [.v rSlow]⟩
    cold := true
  }
  openAt joinBlk [x]

/-- Arbitrary-precision `natDiv` (`n / 0 = 0`, tagged `1`). -/
def natDivBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit :=
  natDivModBig .udiv (fun _ => .imm 1) procs.div x a b

/-- Arbitrary-precision `natMod` (`n % 0 = n`). -/
def natModBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit :=
  natDivModBig .urem id procs.mod x a b

/-- Shared arbitrary-precision comparison helper (`natBeq`, `natBle`, `natBlt`). -/
def natCmpBig (c : Lir.Cond) (slowFn : Lir.FunId) (tWord fWord : Word)
    (x : VReg) (a b : Lir.Arg) : M Unit := do
  let res ← freshReg
  binFastSlow slowFn x a b
    [.assign res (.select c .w64 a b (.imm tWord) (.imm fWord))]
    (fun _ => .v res)

/-- Arbitrary-precision `natBeq`. -/
def natBeqBig (procs : BigNatProcs) (tWord fWord : Word) (x : VReg) (a b : Lir.Arg) : M Unit :=
  natCmpBig .eq procs.beq tWord fWord x a b

/-- Arbitrary-precision `natBle`. -/
def natBleBig (procs : BigNatProcs) (tWord fWord : Word) (x : VReg) (a b : Lir.Arg) : M Unit :=
  natCmpBig .ule procs.ble tWord fWord x a b

/-- Arbitrary-precision `natBlt`. -/
def natBltBig (procs : BigNatProcs) (tWord fWord : Word) (x : VReg) (a b : Lir.Arg) : M Unit :=
  natCmpBig .ult procs.blt tWord fWord x a b

/-- Arbitrary-precision `natLand`: fast path reuses the tag-test word `a & b` directly
(zero extra ALU instructions!). -/
def natLandBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit :=
  binFastSlow procs.land x a b [] id

/-- Arbitrary-precision `natLor`. -/
def natLorBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit := do
  let res ← freshReg
  binFastSlow procs.lor x a b [.assign res (.bin .or .w64 a b)] (fun _ => .v res)

/-- Arbitrary-precision `natXor`. -/
def natXorBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit := do
  let d ← freshReg
  let res ← freshReg
  binFastSlow procs.xor x a b
    [ .assign d (.bin .xor .w64 a b)
    , .assign res (.bin .or .w64 (.v d) (.imm 1)) ]
    (fun _ => .v res)

/-- Arbitrary-precision `natShr` (never overflows on small operands; big operands call `procs.shr`). -/
def natShrBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit := do
  let y ← freshReg
  let s ← freshReg
  let r ← freshReg
  let res ← freshReg
  binFastSlow procs.shr x a b
    [ .assign y (.bin .shr .w64 b (.imm 1))
    , .assign s (.bin .shr .w64 a (.v y))
    , .assign r (.bin .or .w64 (.v s) (.imm 1))
    , .assign res (.select .ugt .w64 (.v y) (.imm 63) (.imm 1) (.v r)) ]
    (fun _ => .v res)

/-- Arbitrary-precision `natShl`: keeps the exact tagged shift-and-check fast path,
dispatching both tag-miss and shift-overflow to `procs.shl`. -/
def natShlBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit := do
  let tagAnd ← bin .and a b
  let fastBlk ← newLabel
  let fastOk ← newLabel
  let slowTag ← newLabel
  let slowOvf ← newLabel
  let joinBlk ← newLabel
  close (.br .tz tagAnd (.imm 1) (loc slowTag) (loc fastBlk))
  let y ← freshReg
  let t ← freshReg
  let s ← freshReg
  let back ← freshReg
  let c1 ← freshReg
  let c2 ← freshReg
  let c3 ← freshReg
  let c4 ← freshReg
  let c ← freshReg
  let rFast ← freshReg
  let rSlow1 ← freshReg
  let rSlow2 ← freshReg
  put fastBlk {
    body :=
      [ .assign y (.bin .shr .w64 b (.imm 1))
      , .assign t (.bin .sub .w64 a (.imm 1))
      , .assign s (.bin .shl .w64 (.v t) (.v y))
      , .assign back (.bin .shr .w64 (.v s) (.v y))
      , .assign c1 (.test .ne .w64 (.v back) (.v t))
      , .assign c2 (.test .ugt .w64 (.v y) (.imm 63))
      , .assign c3 (.bin .or .w64 (.v c1) (.v c2))
      , .assign c4 (.test .ne .w64 (.v t) (.imm 0))
      , .assign c (.bin .and .w64 (.v c3) (.v c4)) ]
    term := .br .ne (.v c) (.imm 0) (loc slowOvf) (loc fastOk)
  }
  put fastOk {
    body := [.assign rFast (.bin .or .w64 (.v s) (.imm 1))]
    term := .jump ⟨.loc joinBlk, [.v rFast]⟩
  }
  put slowTag {
    body := [.call [rSlow1] procs.shl [a, b]]
    term := .jump ⟨.loc joinBlk, [.v rSlow1]⟩
    cold := true
  }
  put slowOvf {
    body := [.call [rSlow2] procs.shl [a, b]]
    term := .jump ⟨.loc joinBlk, [.v rSlow2]⟩
    cold := true
  }
  openAt joinBlk [x]

/-- Arbitrary-precision `natPow`: calls `rt_nat_pow_big` (`procs.pow`). -/
def natPowBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit :=
  emit (.call [x] procs.pow [a, b])

/-- Arbitrary-precision `natGcd`: calls `rt_nat_gcd_big` (`procs.gcd`). -/
def natGcdBig (procs : BigNatProcs) (x : VReg) (a b : Lir.Arg) : M Unit :=
  emit (.call [x] procs.gcd [a, b])

/-! ## Unified Phase 4 `Nat` Primitive Dispatcher -/

/-- Drop-in Phase 4 dispatcher for all 16 `Nat` primitives of `Lam.Prim`.
Ready to replace `Rt.Lower.primitive`'s `Nat` arms in Wave 3b with zero `.natOverflow`. -/
def primitiveBig (f : FunId) (T : BigNatTables) (x : VReg) (op : Lam.Prim)
    (as : List Lir.Arg) : M Unit :=
  match op, as with
  | .natAdd, [a, b] => natAddBig T.procs x a b
  | .natSub, [a, b] => natSubBig T.procs x a b
  | .natPred, [a] => natPredBig T.procs x a
  | .natMul, [a, b] => natMulBig T.procs x a b
  | .natDiv, [a, b] => natDivBig T.procs x a b
  | .natMod, [a, b] => natModBig T.procs x a b
  | .natPow, [a, b] => natPowBig T.procs x a b
  | .natGcd, [a, b] => natGcdBig T.procs x a b
  | .natBeq, [a, b] => do
    let some (tW, fW) := T.bools | throw (.noBool f)
    natBeqBig T.procs tW fW x a b
  | .natBle, [a, b] => do
    let some (tW, fW) := T.bools | throw (.noBool f)
    natBleBig T.procs tW fW x a b
  | .natBlt, [a, b] => do
    let some (tW, fW) := T.bools | throw (.noBool f)
    natBltBig T.procs tW fW x a b
  | .natLand, [a, b] => natLandBig T.procs x a b
  | .natLor, [a, b] => natLorBig T.procs x a b
  | .natXor, [a, b] => natXorBig T.procs x a b
  | .natShl, [a, b] => natShlBig T.procs x a b
  | .natShr, [a, b] => natShrBig T.procs x a b
  | op, _ => throw (.prim f op)

end IxCC.Rt.BigNat
