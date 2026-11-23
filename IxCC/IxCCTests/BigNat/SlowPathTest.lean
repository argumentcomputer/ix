import IxCC.BigNat.Entry
import IxCC.BigNat.Bootstrap
import IxCC.Rt.BigNat.Cell
import IxCC.Rt.BigNat.Dispatch
import IxCC.Rt.Procs.Nat
import IxCC.Rt.Rc.Array.Procs
import IxCC.Rt.Readback.Array
import IxCC.Lir.Semantics
import IxCC.Lir.WellFormed
import IxCC.X86.ELFRodata
import IxCC.X86.ELFWriteK
import IxCC.X86.ELFValidate
import IxCC.X86.ELFCheckK

/-! # Phase 4 Arbitrary-Precision `Nat` Slow-Path & LIR Dispatch Tests (`IxCCTests.BigNat.SlowPathTest`)

Executable native test suite exercising:
1. **`IxCC.BigNat.Entry` boundary & mixed-width matrix:** all 19 slow-path entrypoints across
   `0, 1, 2, 3, 7, 63, 64, 2^32 - 1, 2^32, 2^62, 2^63 - 2, 2^63 - 1, 2^63, 2^63 + 1, 2^64 - 1,
   2^64, 2^64 + 1, 10^19, 2^128 - 1, 2^128, 2^256 - 1, 2^256` (small-small, small-big,
   big-small, big-big), verifying exact `Nat` agreement, canonical promotion/demotion, and
   `pow?`/`shiftLeft?` OOM boundary guards.
2. **`IxCC.BigNat.Bootstrap` verifier & JSON codec:** `verifyInternalIndices`, `compileAnonArgs`,
   `compileNamedArgs`, `limbEquationSpecs`, `FrozenLibrary` JSON round-trip, and static
   `checkSrcNoBigNatLit` acceptance/rejection.
3. **Immortal static `.rodata` `≥ 2^63` literal cells:** `addBigNatLiteral` → `ELF.writeCheckedK`
   → `ELF.check`/`ELF.checkK` → `ELFRodata.mapRodata` → `readbackBigNat` + read-only `arrDec`
   immortal no-op across `2^63, 2^63 + 1, 2^64 - 1, 2^64, 2^128 - 1, 2^128, 2^256 - 1, 2^256`.
4. **Live `Lir.eval` + `Lir.Program.check` + zero-`natOverflow` across every `Rt.BigNat.Dispatch`
   primitive and `Rt.Procs.natPowBig`/`natGcdBig`:**
   - Verifies `Lir.Program.check` (zero critical edges, strict SSA, matching arities) and
     `Bootstrap.checkLirHasNoNatOverflow` (zero `.fail .natOverflow` blocks) on every lowered program.
   - Verifies fast paths return exact tagged fixnum words with untouched slow-path canary.
   - Verifies overflow paths (`(2^63-1)+1`, `(2^63-1)*2`, `1<<<63`, `2^63`, `3^40`, ...) AND
     big-operand paths (real `.rodata`-mapped `2^63, 2^64, 2^128, 2^256` pointers) dispatch cleanly
     to the exact slow-path procedure with exact unmodified arguments and NEVER return
     `.resource .natOverflow`, then validates end-to-end readback + `BigNat.Entry` agreement. -/

set_option autoImplicit false

namespace IxCCTests.BigNat.SlowPathTest

open IxCC
open IxCC.BigNat
open IxCC.BigNat.Entry
open IxCC.BigNat.Bootstrap
open IxCC.Rt
open IxCC.Rt.BigNat
open IxCC.Rt.Readback
open IxCC.Rt.Rc.Array
open IxCC.X86
open IxCC.X86.ELF
open IxCC.X86.ELFRodata

private def renderOutcome : Lir.Outcome → String
  | .ok (ws, _) => s!"ok({ws.length} words)"
  | .resource r => s!"resource({reprStr r})"
  | .timeout => "timeout"
  | .stuck => "stuck"
  | .trap => "trap"

private def assertCheck (cond : Bool) (label : String) (cnt : IO.Ref Nat) : IO Unit := do
  cnt.modify (· + 1)
  unless cond do
    throw (IO.userError s!"FAIL SlowPathTest: {label}")

private def tagNat (n : Nat) : Word :=
  UInt64.ofNat (2 * n + 1)

private def boolTrueWord : Word := 3
private def boolFalseWord : Word := 1

private def slowSentinel (opIdx : Nat) : Word :=
  0x5100_0000_0000_0000 ||| UInt64.ofNat (opIdx * 2)

/-! ## Part 1: `IxCC.BigNat.Entry` Boundary & Mixed-Width Matrix -/

private def boundaryValues : List Nat :=
  [ 0, 1, 2, 3, 7, 63, 64
  , 2 ^ 32 - 1, 2 ^ 32
  , 2 ^ 62
  , 2 ^ 63 - 2, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1
  , 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1
  , 10 ^ 19
  , 2 ^ 128 - 1, 2 ^ 128
  , 2 ^ 256 - 1, 2 ^ 256 ]

private def checkSlowNat (label : String) (r : SlowNat) (expected : Nat) (cnt : IO.Ref Nat) : IO Unit := do
  assertCheck (isCanonical r) s!"{label}: canonical" cnt
  assertCheck (r.val == expected) s!"{label}: val {r.val} == {expected}" cnt
  if expected < Rt.natLimit then
    match r with
    | .small v => assertCheck (v.toNat == expected) s!"{label}: demoted .small" cnt
    | .big _ => throw (IO.userError s!"FAIL SlowPathTest: {label}: expected .small for {expected}")
  else
    match r with
    | .big _ => assertCheck true s!"{label}: promoted .big" cnt
    | .small _ => throw (IO.userError s!"FAIL SlowPathTest: {label}: expected .big for {expected}")

def testEntryMatrix (cnt : IO.Ref Nat) : IO Unit := do
  let n2_63 := Rt.natLimit
  -- Explicit promotion & demotion boundary transitions
  checkSlowNat "promote add (2^63-1)+1" (Entry.add (SlowNat.ofNat (n2_63 - 1)) (SlowNat.ofNat 1)) n2_63 cnt
  checkSlowNat "promote mul (2^63-1)*2" (Entry.mul (SlowNat.ofNat (n2_63 - 1)) (SlowNat.ofNat 2)) (2 * (n2_63 - 1)) cnt
  checkSlowNat "promote shl 1<<<63" (Entry.shiftLeft (SlowNat.ofNat 1) 63) n2_63 cnt
  checkSlowNat "promote pow 2^63" (Entry.pow (SlowNat.ofNat 2) 63) n2_63 cnt
  checkSlowNat "demote pred 2^63" (Entry.pred (SlowNat.ofNat n2_63)) (n2_63 - 1) cnt
  checkSlowNat "demote sub 2^63-1" (Entry.sub (SlowNat.ofNat n2_63) (SlowNat.ofNat 1)) (n2_63 - 1) cnt
  checkSlowNat "demote sub 2^128-2^128" (Entry.sub (SlowNat.ofNat (2 ^ 128)) (SlowNat.ofNat (2 ^ 128))) 0 cnt
  checkSlowNat "demote div 2^63/2" (Entry.div (SlowNat.ofNat n2_63) (SlowNat.ofNat 2)) (2 ^ 62) cnt
  checkSlowNat "demote mod 2^63%7" (Entry.mod (SlowNat.ofNat n2_63) (SlowNat.ofNat 7)) (n2_63 % 7) cnt
  checkSlowNat "demote shr 2^63>>>1" (Entry.shiftRight (SlowNat.ofNat n2_63) 1) (2 ^ 62) cnt
  checkSlowNat "demote land (2^63+5)&&&7" (Entry.land (SlowNat.ofNat (n2_63 + 5)) (SlowNat.ofNat 7)) 5 cnt
  checkSlowNat "demote xor 2^63^^^2^63" (Entry.xor (SlowNat.ofNat n2_63) (SlowNat.ofNat n2_63)) 0 cnt
  checkSlowNat "demote gcd 2^128 (2^63-1)" (Entry.gcd (SlowNat.ofNat (2 ^ 128)) (SlowNat.ofNat (n2_63 - 1))) 1 cnt

  -- `pow?` and `shiftLeft?` OOM boundary semantics
  let bigExp := SlowNat.ofNat (2 ^ 64)
  let hugeExp := SlowNat.ofNat (2 ^ 128)
  match Entry.pow? (SlowNat.ofNat 0) bigExp with
  | some r => checkSlowNat "pow? 0^(2^64)" r 0 cnt
  | none => throw (IO.userError "FAIL SlowPathTest: pow? 0^(2^64) returned none")
  match Entry.pow? (SlowNat.ofNat 1) hugeExp with
  | some r => checkSlowNat "pow? 1^(2^128)" r 1 cnt
  | none => throw (IO.userError "FAIL SlowPathTest: pow? 1^(2^128) returned none")
  assertCheck (Entry.pow? (SlowNat.ofNat 2) (SlowNat.ofNat n2_63) == none)
    "pow? 2^(2^63) returns none (OOM)" cnt
  assertCheck (Entry.pow? (SlowNat.ofNat (2 ^ 64)) bigExp == none)
    "pow? (2^64)^(2^64) returns none (OOM)" cnt
  match Entry.shiftLeft? (SlowNat.ofNat 0) hugeExp with
  | some r => checkSlowNat "shiftLeft? 0<<<(2^128)" r 0 cnt
  | none => throw (IO.userError "FAIL SlowPathTest: shiftLeft? 0<<<(2^128) returned none")
  assertCheck (Entry.shiftLeft? (SlowNat.ofNat 1) (SlowNat.ofNat n2_63) == none)
    "shiftLeft? 1<<<(2^63) returns none (OOM)" cnt

  -- Full boundary matrix across small-small, small-big, big-small, big-big
  for a in boundaryValues do
    let sa := SlowNat.ofNat a
    assertCheck (isCanonical sa) s!"ofNat {a} canonical" cnt
    checkSlowNat s!"pred {a}" (Entry.pred sa) (a - 1) cnt
    assertCheck (Entry.log2 sa == Nat.log2 a) s!"log2 {a}" cnt
    checkSlowNat s!"log2Slow {a}" (Entry.log2Slow sa) (Nat.log2 a) cnt
    let dec := Entry.toDecimal sa
    match Entry.ofDecimal dec with
    | some parsed => checkSlowNat s!"decimal round-trip {a}" parsed a cnt
    | none => throw (IO.userError s!"FAIL SlowPathTest: ofDecimal failed on {dec}")
    match toTaggedWord? sa with
    | some w =>
      assertCheck (a < n2_63 && w == tagNat a && ofTaggedWord w == sa)
        s!"toTaggedWord? round-trip {a}" cnt
    | none =>
      assertCheck (a ≥ n2_63) s!"toTaggedWord? none iff ≥ 2^63 ({a})" cnt
    for b in boundaryValues do
      let sb := SlowNat.ofNat b
      checkSlowNat s!"add {a} {b}" (Entry.add sa sb) (a + b) cnt
      checkSlowNat s!"sub {a} {b}" (Entry.sub sa sb) (a - b) cnt
      checkSlowNat s!"mul {a} {b}" (Entry.mul sa sb) (a * b) cnt
      checkSlowNat s!"div {a} {b}" (Entry.div sa sb) (a / b) cnt
      checkSlowNat s!"mod {a} {b}" (Entry.mod sa sb) (a % b) cnt
      checkSlowNat s!"gcd {a} {b}" (Entry.gcd sa sb) (Nat.gcd a b) cnt
      checkSlowNat s!"land {a} {b}" (Entry.land sa sb) (a &&& b) cnt
      checkSlowNat s!"lor {a} {b}" (Entry.lor sa sb) (a ||| b) cnt
      checkSlowNat s!"xor {a} {b}" (Entry.xor sa sb) (a ^^^ b) cnt
      checkSlowNat s!"shrSlow {a} {b}" (Entry.shiftRightSlow sa sb) (if b ≥ 512 then 0 else a / 2 ^ b) cnt
      assertCheck (Entry.cmp sa sb == compare a b) s!"cmp {a} {b}" cnt
      assertCheck (Entry.beq sa sb == (a == b)) s!"beq {a} {b}" cnt
      assertCheck (Entry.ble sa sb == decide (a ≤ b)) s!"ble {a} {b}" cnt
      assertCheck (Entry.blt sa sb == decide (a < b)) s!"blt {a} {b}" cnt
    for s in [0, 1, 7, 63, 64, 65, 128] do
      checkSlowNat s!"shl {a} {s}" (Entry.shiftLeft sa s) (a * 2 ^ s) cnt
    for e in [0, 1, 2, 3, 4] do
      checkSlowNat s!"pow {a} {e}" (Entry.pow sa e) (a ^ e) cnt

/-! ## Part 2: `IxCC.BigNat.Bootstrap` Verification & Serialization -/

def testBootstrap (cnt : IO.Ref Nat) : IO Unit := do
  -- Pure-Lean internal index verifier
  match Bootstrap.verifyInternalIndices with
  | .error e => throw (IO.userError s!"FAIL SlowPathTest: verifyInternalIndices: {e}")
  | .ok n => assertCheck (n > 5000) s!"verifyInternalIndices ran {n} checks" cnt

  -- Manifest completeness
  assertCheck (Bootstrap.SlowPathOp.all.length == 19) "SlowPathOp.all has 19 entries" cnt
  assertCheck (Bootstrap.limbEquationSpecs.length == 5) "limbEquationSpecs has 5 LimbOps" cnt
  assertCheck ((Bootstrap.allFreezeConsts true).length == 19 + 10) "allFreezeConsts includes entries + 5 ops + 5 eqns" cnt

  -- CLI arg builders
  let fcfg : FreezeConfig :=
    { ix := "ix", outDir := "/tmp/bignat-bootstrap-test" }
  let anonArgs := compileAnonArgs fcfg "/tmp/a.ixe" "/tmp/a.json"
  let namedArgs := compileNamedArgs fcfg "/tmp/n.ixe" "/tmp/n.json"
  assertCheck (anonArgs.contains "--anon" && anonArgs.contains "--consts" && anonArgs.contains "--equations")
    "compileAnonArgs flags" cnt
  assertCheck (!namedArgs.contains "--anon" && namedArgs.contains "--consts" && namedArgs.contains "--equations")
    "compileNamedArgs flags" cnt

  -- FrozenLibrary JSON round-trip
  let mkAddr (b : UInt8) : Ixon.Address := Ixon.Address.replicate b
  let synPins : Src.Pinned.LimbPins :=
    { ops := Src.LimbOp.all.zipIdx.map fun (op, i) => (op, Src.Pinned.addrNat (mkAddr (UInt8.ofNat (i + 1))))
    , prodType := some (Src.Pinned.addrNat (mkAddr 0x10))
    , prodMk := some (Src.Pinned.addrNat (mkAddr 0x11))
    , natLog2 := some (Src.Pinned.addrNat (mkAddr 0x12))
    , boolToNat := some (Src.Pinned.addrNat (mkAddr 0x13))
    , cond := some (Src.Pinned.addrNat (mkAddr 0x14)) }
  let synLib : FrozenLibrary :=
    { closureBytes := ByteArray.mk #[0x49, 0x58, 0x45, 0x01, 0xAB, 0xCD]
    , equationsJson := Lean.Json.mkObj [("equations", Lean.Json.arr #[])]
    , limbPins := synPins
    , entryAddrs := SlowPathOp.all.zipIdx.map fun (op, i) => (op, mkAddr (UInt8.ofNat (0x20 + i)))
    , limbEqnAddrs := Src.LimbOp.all.zipIdx.map fun (op, i) => (op, mkAddr (UInt8.ofNat (0x40 + i)))
    , ixVersion := "ix-test-0.1" }
  let j := synLib.toJson
  match FrozenLibrary.ofJson j with
  | .error e => throw (IO.userError s!"FAIL SlowPathTest: FrozenLibrary.ofJson: {e}")
  | .ok decoded =>
    assertCheck (decoded.closureBytes == synLib.closureBytes) "FrozenLibrary closureBytes round-trip" cnt
    assertCheck (decoded.ixVersion == synLib.ixVersion) "FrozenLibrary ixVersion round-trip" cnt
    assertCheck (decoded.entryAddrs.length == 19) "FrozenLibrary entryAddrs round-trip" cnt
    assertCheck (decoded.limbEqnAddrs.length == 5) "FrozenLibrary limbEqnAddrs round-trip" cnt
    assertCheck (decoded.limbPins.ops.length == 5) "FrozenLibrary limbPins.ops round-trip" cnt

  -- Static `checkSrcNoBigNatLit` acceptance & rejection
  let aGood := mkAddr 0xA1
  let aBad := mkAddr 0xA2
  let aLimb := mkAddr 0xA3
  let okConsts : Src.NatMap Src.ConstEntry :=
    (Src.NatMap.leaf.insert 0
      { ref := default, addr := aGood, decl := .defn .defn .safe 0 (.sort (.succ .zero)) (.natLit (2 ^ 63 - 1)) })
    |>.insert 1
      { ref := default, addr := aLimb, decl := .defn .defn .safe 0 (.sort (.succ .zero)) (.natLit (2 ^ 64)) }
  let okProg : Src.Program := { consts := okConsts, size := 2 }
  let pinsWithLimb : Src.Pinned.LimbPins :=
    { ops := [(.mulWide64, Src.Pinned.addrNat aLimb)] }
  match Bootstrap.checkSrcNoBigNatLit okProg pinsWithLimb with
  | .ok () => assertCheck true "checkSrcNoBigNatLit accepts < 2^63 + LimbOp body" cnt
  | .error e => throw (IO.userError s!"FAIL SlowPathTest: checkSrcNoBigNatLit false positive: {e}")

  let badConsts : Src.NatMap Src.ConstEntry :=
    Src.NatMap.leaf.insert 0
      { ref := default, addr := aBad, decl := .defn .defn .safe 0 (.sort (.succ .zero)) (.natLit (2 ^ 63)) }
  let badProg : Src.Program := { consts := badConsts, size := 1 }
  match Bootstrap.checkSrcNoBigNatLit badProg {} with
  | .error _ => assertCheck true "checkSrcNoBigNatLit rejects ≥ 2^63 literal outside LimbOps" cnt
  | .ok () => throw (IO.userError "FAIL SlowPathTest: checkSrcNoBigNatLit missed 2^63 literal")

/-! ## Part 3: Static `.rodata` `≥ 2^63` Literal Cells + Readback + Immortal `arrDec` -/

private structure MappedRodataBigs where
  mem : Memory
  addrs : List (Nat × Word)

private def buildRodataBigs (cnt : IO.Ref Nat) : IO MappedRodataBigs := do
  let bigVals : List Nat :=
    [ 2 ^ 63
    , 2 ^ 63 + 1
    , 2 ^ 64 - 1
    , 2 ^ 64
    , 2 ^ 128 - 1
    , 2 ^ 128
    , 2 ^ 256 - 1
    , 2 ^ 256 ]
  let mut tbl := RodataTable.empty
  let mut offs : List (Nat × Nat) := []
  let mut idx := 0
  for v in bigVals do
    let (tbl', off) := addBigNatLiteral tbl s!"cx_bignat_lit_{idx}" v
    tbl := tbl'
    offs := offs ++ [(v, off)]
    idx := idx + 1
  -- Emit ELF64 object and verify with both ELF.check and ELF.checkK
  let input : ELF.Input :=
    { encoded := { text := ByteArray.mk #[0xC3], blockOffsets := #[0], relocations := #[] }
    , entryBlock := 0
    , exportName := "cx_bignat_rodata_smoke"
    , provenance := .ixir2 (Ixon.Address.replicate 0x77)
    , rodata := some tbl.bytes
    , rodataExports := tbl.symbols }
  match ELF.writeCheckedK input with
  | .error e => throw (IO.userError s!"FAIL SlowPathTest: writeCheckedK: {reprStr e}")
  | .ok cert =>
    assertCheck (ELF.check input cert.bytes) "ELF.check accepts BigNat .rodata object" cnt
    assertCheck (ELF.checkK input cert.bytes) "ELF.checkK accepts BigNat .rodata object" cnt
  let base : Word := 0x400000
  let mem := mapRodata Memory.unmapped base tbl.bytes
  let mut addrs : List (Nat × Word) := []
  for (v, off) in offs do
    let w := base + UInt64.ofNat off
    assertCheck ((w &&& 1) == 0 && w.toNat % 8 == 0 && w != 0)
      s!"static BigNat pointer aligned & even ({v})" cnt
    assertCheck (readbackBigNat mem w == some v)
      s!"readbackBigNat static .rodata cell ({v})" cnt
    -- Immortal read-only `arrDec` must be a zero-write no-op on read-only `.rodata`
    match Lir.eval (arrayProgram fnDec) 20 [w] mem 0 with
    | .ok ([], _) => assertCheck true s!"arrDec immortal no-op on static BigNat ({v})" cnt
    | res => throw (IO.userError s!"FAIL SlowPathTest: arrDec on static BigNat ({v}): {renderOutcome res}")
    addrs := addrs ++ [(v, w)]
  pure { mem, addrs }

/-! ## Part 4: Live `Lir.eval` + `Lir.Program.check` + Zero-`natOverflow` Dispatch Tests -/

private def addScratchRegion (mem : Memory) (ctx : Word) : Memory :=
  { mem with
    readable := fun a => mem.readable a || (ctx ≤ a && a < ctx + 64)
    writable := fun a => mem.writable a || (ctx ≤ a && a < ctx + 64) }

/-- Unary slow-path stub: records `(v0, 1)` at `ctx + 0 / ctx + 16` and returns `slowSentinel opIdx`. -/
private def slowStub1 (opIdx : Nat) (name : String) : Lir.Func where
  name := s!"slow_{name}"
  params := [0]
  results := 1
  blocks := #[{
    body :=
      #[ .store .w64 { base := some .ctx, disp := 0 } (.v 0)
       , .store .w64 { base := some .ctx, disp := 16 } (.imm 1) ]
    term := .ret [.imm (slowSentinel opIdx)]
  }]

/-- Binary slow-path stub: records `(v0, v1, 2)` at `ctx + 0 / 8 / 16` and returns `slowSentinel opIdx`. -/
private def slowStub2 (opIdx : Nat) (name : String) : Lir.Func where
  name := s!"slow_{name}"
  params := [0, 1]
  results := 1
  blocks := #[{
    body :=
      #[ .store .w64 { base := some .ctx, disp := 0 } (.v 0)
       , .store .w64 { base := some .ctx, disp := 8 } (.v 1)
       , .store .w64 { base := some .ctx, disp := 16 } (.imm 2) ]
    term := .ret [.imm (slowSentinel opIdx)]
  }]

/-- Lower a single `Rt.Lower.M` action into a standalone `Lir.Func`. -/
private def lowerHarnessFunc (name : String) (params : List Lir.VReg) (resReg : Lir.VReg)
    (freshStart : Lir.VReg) (act : Rt.Lower.M Unit) : Except String Lir.Func := do
  let runAct : Rt.Lower.M Unit := do
    act
    Rt.Lower.close (.ret (.v resReg))
  match runAct.run { fresh := freshStart } with
  | .error e => throw s!"lowerHarnessFunc ({name}): {e}"
  | .ok ((), st) =>
    let mut blks : Array Lir.Block := #[]
    for l in List.range st.next do
      let some pb := st.done.get? l
        | throw s!"lowerHarnessFunc ({name}): missing block {l}"
      match Rt.Lower.resolveBlock 0 0 .leaf pb with
      | .error e => throw s!"lowerHarnessFunc ({name}) block {l}: {e}"
      | .ok b => blks := blks.push b
    pure { name, params, results := 1, blocks := blks }

/-- Concrete `BigNatProcs` layout used by the LIR dispatch test harness:
- `0`: wrapper main function (replaced per test op)
- `1..14`: direct slow-path stubs (`add, sub, pred, mul, div, mod, beq, ble, blt, land, lor, xor, shl, shr`)
- `15`: `slowStub2 15 "pow"` (slow target of `natPowBig`)
- `16`: `slowStub2 16 "gcd"` (slow target of `natGcdBig`)
- `17`: `Rt.Procs.natPowBig 15`
- `18`: `Rt.Procs.natGcdBig 16` -/
private def harnessProcs : BigNatProcs :=
  { add := 1, sub := 2, pred := 3, mul := 4, div := 5, mod := 6
  , beq := 7, ble := 8, blt := 9
  , land := 10, lor := 11, xor := 12, shl := 13, shr := 14
  , pow := 17, gcd := 18 }

private def harnessTables : BigNatTables :=
  { bools := some (boolTrueWord, boolFalseWord), procs := harnessProcs }

private def harnessCalleeFuncs : Array Lir.Func :=
  #[ slowStub2 1 "add"
   , slowStub2 2 "sub"
   , slowStub1 3 "pred"
   , slowStub2 4 "mul"
   , slowStub2 5 "div"
   , slowStub2 6 "mod"
   , slowStub2 7 "beq"
   , slowStub2 8 "ble"
   , slowStub2 9 "blt"
   , slowStub2 10 "land"
   , slowStub2 11 "lor"
   , slowStub2 12 "xor"
   , slowStub2 13 "shl"
   , slowStub2 14 "shr"
   , slowStub2 15 "pow"
   , slowStub2 16 "gcd"
   , Rt.Procs.natPowBig 15
   , Rt.Procs.natGcdBig 16 ]

private def mkHarnessProgram (mainFn : Lir.Func) : Lir.Program :=
  { funcs := #[mainFn] ++ harnessCalleeFuncs, main := 0 }

private def checkProgramWFAndNoOvf (label : String) (prog : Lir.Program) (cnt : IO.Ref Nat) : IO Unit := do
  match Lir.Program.check prog with
  | .ok () => assertCheck true s!"{label}: Lir.Program.check WF" cnt
  | .error e => throw (IO.userError s!"FAIL SlowPathTest: {label} Program.check failed: {e}")
  let ovfs := Bootstrap.checkLirHasNoNatOverflow prog
  assertCheck ovfs.isEmpty s!"{label}: zero .fail .natOverflow blocks (found {ovfs})" cnt

private def evalBinOp (label : String) (prog : Lir.Program) (opIdx : Nat)
    (mem : Memory) (ctx wa wb : Word) (expectSlow : Bool) (expectFastWord : Word)
    (cnt : IO.Ref Nat) : IO Unit := do
  match Lir.eval prog 500 [wa, wb] mem ctx with
  | .resource .natOverflow =>
    throw (IO.userError s!"FAIL SlowPathTest: {label}: returned .resource .natOverflow!")
  | .ok ([res], mem') =>
    let canary := mem'.read64 (ctx + 16)
    if expectSlow then
      assertCheck (res == slowSentinel opIdx) s!"{label}: returned slow sentinel" cnt
      assertCheck (canary == 2) s!"{label}: slow stub invoked (canary == 2)" cnt
      assertCheck (mem'.read64 ctx == wa && mem'.read64 (ctx + 8) == wb)
        s!"{label}: slow stub received exact unmodified (wa, wb)" cnt
    else
      assertCheck (canary == 0) s!"{label}: fast path bypassed slow stub (canary == 0)" cnt
      assertCheck (res == expectFastWord) s!"{label}: fast result {res} == {expectFastWord}" cnt
  | other =>
    throw (IO.userError s!"FAIL SlowPathTest: {label}: unexpected Lir.eval outcome {renderOutcome other}")

private def evalUnOp (label : String) (prog : Lir.Program) (opIdx : Nat)
    (mem : Memory) (ctx wa : Word) (expectSlow : Bool) (expectFastWord : Word)
    (cnt : IO.Ref Nat) : IO Unit := do
  match Lir.eval prog 200 [wa] mem ctx with
  | .resource .natOverflow =>
    throw (IO.userError s!"FAIL SlowPathTest: {label}: returned .resource .natOverflow!")
  | .ok ([res], mem') =>
    let canary := mem'.read64 (ctx + 16)
    if expectSlow then
      assertCheck (res == slowSentinel opIdx) s!"{label}: returned slow sentinel" cnt
      assertCheck (canary == 1) s!"{label}: slow stub invoked (canary == 1)" cnt
      assertCheck (mem'.read64 ctx == wa) s!"{label}: slow stub received exact unmodified wa" cnt
    else
      assertCheck (canary == 0) s!"{label}: fast path bypassed slow stub (canary == 0)" cnt
      assertCheck (res == expectFastWord) s!"{label}: fast result {res} == {expectFastWord}" cnt
  | other =>
    throw (IO.userError s!"FAIL SlowPathTest: {label}: unexpected Lir.eval outcome {renderOutcome other}")

def testLirDispatch (ro : MappedRodataBigs) (cnt : IO.Ref Nat) : IO Unit := do
  let ctx : Word := 0x800000
  let mem := addScratchRegion ro.mem ctx
  let maxSmall := Rt.natLimit - 1 -- 2^63 - 1
  let wBig63 := (ro.addrs.find? (·.1 == 2 ^ 63)).get!.2
  let wBig64 := (ro.addrs.find? (·.1 == 2 ^ 64)).get!.2
  let wBig128 := (ro.addrs.find? (·.1 == 2 ^ 128)).get!.2
  let wBig256 := (ro.addrs.find? (·.1 == 2 ^ 256)).get!.2
  let bigPairs : List (String × Word × Word) :=
    [ ("small-big63", tagNat 42, wBig63)
    , ("big63-small", wBig63, tagNat 7)
    , ("small0-big64", tagNat 0, wBig64)
    , ("big128-small0", wBig128, tagNat 0)
    , ("big63-big256", wBig63, wBig256)
    , ("big256-big128", wBig256, wBig128) ]

  -- Helper to lower any binary `Lam.Prim` via `primitiveBig`
  let lowerBin := fun (op : Lam.Prim) => do
    let fn ← IO.ofExcept <| lowerHarnessFunc op.name [0, 1] 2 3
      (primitiveBig 0 harnessTables 2 op [.v 0, .v 1])
    let prog := mkHarnessProgram fn
    checkProgramWFAndNoOvf op.name prog cnt
    pure prog

  -- 1. natAdd: fast + carry overflow + big operands
  let pAdd ← lowerBin .natAdd
  for (a, b) in [(0, 0), (0, 1), (1, 0), (42, 99), (maxSmall, 0), (2 ^ 62, 2 ^ 62 - 1)] do
    evalBinOp s!"natAdd fast {a}+{b}" pAdd 1 mem ctx (tagNat a) (tagNat b) false (tagNat (a + b)) cnt
  for (a, b) in [(maxSmall, 1), (1, maxSmall), (maxSmall, maxSmall), (2 ^ 62, 2 ^ 62)] do
    evalBinOp s!"natAdd ovf {a}+{b}" pAdd 1 mem ctx (tagNat a) (tagNat b) true 0 cnt
  for (lbl, wa, wb) in bigPairs do
    evalBinOp s!"natAdd {lbl}" pAdd 1 mem ctx wa wb true 0 cnt

  -- 2. natSub: fast + big operands
  let pSub ← lowerBin .natSub
  for (a, b) in [(0, 0), (0, 1), (1, 0), (5, 9), (9, 5), (maxSmall, 1), (maxSmall, maxSmall)] do
    evalBinOp s!"natSub fast {a}-{b}" pSub 2 mem ctx (tagNat a) (tagNat b) false (tagNat (a - b)) cnt
  for (lbl, wa, wb) in bigPairs do
    evalBinOp s!"natSub {lbl}" pSub 2 mem ctx wa wb true 0 cnt

  -- 3. natPred & natSuccPeel: fast + big operands
  let fnPred ← IO.ofExcept <| lowerHarnessFunc "natPred" [0] 1 2
    (primitiveBig 0 harnessTables 1 .natPred [.v 0])
  let pPred := mkHarnessProgram fnPred
  checkProgramWFAndNoOvf "natPred" pPred cnt
  let fnPeel ← IO.ofExcept <| lowerHarnessFunc "natSuccPeel" [0] 1 2
    (natSuccPeelBig harnessProcs 1 0)
  let pPeel := mkHarnessProgram fnPeel
  checkProgramWFAndNoOvf "natSuccPeel" pPeel cnt
  for a in [0, 1, 2, 42, maxSmall] do
    evalUnOp s!"natPred fast {a}" pPred 3 mem ctx (tagNat a) false (tagNat (a - 1)) cnt
    evalUnOp s!"natSuccPeel fast {a}" pPeel 3 mem ctx (tagNat a) false (tagNat (a - 1)) cnt
  for (v, w) in ro.addrs do
    evalUnOp s!"natPred big {v}" pPred 3 mem ctx w true 0 cnt
    evalUnOp s!"natSuccPeel big {v}" pPeel 3 mem ctx w true 0 cnt

  -- 4. natMul: fast + widening overflow + big operands
  let pMul ← lowerBin .natMul
  for (a, b) in [(0, 0), (0, maxSmall), (maxSmall, 0), (1, maxSmall), (7, 9), (2 ^ 31, 2 ^ 31), (2 ^ 31, 2 ^ 32 - 1)] do
    evalBinOp s!"natMul fast {a}*{b}" pMul 4 mem ctx (tagNat a) (tagNat b) false (tagNat (a * b)) cnt
  for (a, b) in [(maxSmall, 2), (2, maxSmall), (2 ^ 32, 2 ^ 31), (2 ^ 32, 2 ^ 32), (maxSmall, maxSmall)] do
    evalBinOp s!"natMul ovf {a}*{b}" pMul 4 mem ctx (tagNat a) (tagNat b) true 0 cnt
  for (lbl, wa, wb) in bigPairs do
    evalBinOp s!"natMul {lbl}" pMul 4 mem ctx wa wb true 0 cnt

  -- 5. natDiv & natMod: fast (including div/mod by 0) + big operands
  let pDiv ← lowerBin .natDiv
  let pMod ← lowerBin .natMod
  for (a, b) in [(0, 0), (42, 0), (maxSmall, 0), (0, 7), (42, 1), (42, 5), (maxSmall, 2), (maxSmall, maxSmall)] do
    evalBinOp s!"natDiv fast {a}/{b}" pDiv 5 mem ctx (tagNat a) (tagNat b) false (tagNat (a / b)) cnt
    evalBinOp s!"natMod fast {a}%{b}" pMod 6 mem ctx (tagNat a) (tagNat b) false (tagNat (a % b)) cnt
  for (lbl, wa, wb) in bigPairs do
    evalBinOp s!"natDiv {lbl}" pDiv 5 mem ctx wa wb true 0 cnt
    evalBinOp s!"natMod {lbl}" pMod 6 mem ctx wa wb true 0 cnt

  -- 6. Comparisons: natBeq, natBle, natBlt
  let pBeq ← lowerBin .natBeq
  let pBle ← lowerBin .natBle
  let pBlt ← lowerBin .natBlt
  let bWord := fun b => if b then boolTrueWord else boolFalseWord
  for (a, b) in [(0, 0), (0, 1), (1, 0), (42, 42), (42, 43), (maxSmall - 1, maxSmall), (maxSmall, maxSmall)] do
    evalBinOp s!"natBeq fast {a}=={b}" pBeq 7 mem ctx (tagNat a) (tagNat b) false (bWord (a == b)) cnt
    evalBinOp s!"natBle fast {a}<={b}" pBle 8 mem ctx (tagNat a) (tagNat b) false (bWord (decide (a ≤ b))) cnt
    evalBinOp s!"natBlt fast {a}<{b}" pBlt 9 mem ctx (tagNat a) (tagNat b) false (bWord (decide (a < b))) cnt
  for (lbl, wa, wb) in bigPairs do
    evalBinOp s!"natBeq {lbl}" pBeq 7 mem ctx wa wb true 0 cnt
    evalBinOp s!"natBle {lbl}" pBle 8 mem ctx wa wb true 0 cnt
    evalBinOp s!"natBlt {lbl}" pBlt 9 mem ctx wa wb true 0 cnt

  -- 7. Bitwise: natLand, natLor, natXor
  let pLand ← lowerBin .natLand
  let pLor ← lowerBin .natLor
  let pXor ← lowerBin .natXor
  for (a, b) in [(0, 0), (0, maxSmall), (0x5555, 0x3333), (maxSmall, 0xFF00FF), (maxSmall, maxSmall)] do
    evalBinOp s!"natLand fast {a}&&&{b}" pLand 10 mem ctx (tagNat a) (tagNat b) false (tagNat (a &&& b)) cnt
    evalBinOp s!"natLor fast {a}|||{b}" pLor 11 mem ctx (tagNat a) (tagNat b) false (tagNat (a ||| b)) cnt
    evalBinOp s!"natXor fast {a}^^^{b}" pXor 12 mem ctx (tagNat a) (tagNat b) false (tagNat (a ^^^ b)) cnt
  for (lbl, wa, wb) in bigPairs do
    evalBinOp s!"natLand {lbl}" pLand 10 mem ctx wa wb true 0 cnt
    evalBinOp s!"natLor {lbl}" pLor 11 mem ctx wa wb true 0 cnt
    evalBinOp s!"natXor {lbl}" pXor 12 mem ctx wa wb true 0 cnt

  -- 8. Shifts: natShl (fast + overflow + big) and natShr (fast + big)
  let pShl ← lowerBin .natShl
  let pShr ← lowerBin .natShr
  for (a, s) in [(0, 0), (0, 64), (0, maxSmall), (1, 0), (1, 62), (7, 10), (maxSmall, 0)] do
    let expShl := if a == 0 then 0 else a * 2 ^ s
    evalBinOp s!"natShl fast {a}<<<{s}" pShl 13 mem ctx (tagNat a) (tagNat s) false (tagNat expShl) cnt
  for (a, s) in [(1, 63), (1, 64), (1, 100), (2, 62), (maxSmall, 1), (3, 62)] do
    evalBinOp s!"natShl ovf {a}<<<{s}" pShl 13 mem ctx (tagNat a) (tagNat s) true 0 cnt
  for (a, s) in [(0, 0), (0, 100), (maxSmall, 0), (maxSmall, 1), (maxSmall, 62), (maxSmall, 63), (maxSmall, 64), (maxSmall, maxSmall)] do
    let expShr := if s ≥ 64 then 0 else a / 2 ^ s
    evalBinOp s!"natShr fast {a}>>>{s}" pShr 14 mem ctx (tagNat a) (tagNat s) false (tagNat expShr) cnt
  for (lbl, wa, wb) in bigPairs do
    evalBinOp s!"natShl {lbl}" pShl 13 mem ctx wa wb true 0 cnt
    evalBinOp s!"natShr {lbl}" pShr 14 mem ctx wa wb true 0 cnt

  -- 9. natPow (via `Rt.Procs.natPowBig 15`): fast + exponent/product overflow + big operands
  let pPow ← lowerBin .natPow
  for (a, e) in [(0, 0), (0, 1), (0, maxSmall), (1, 0), (1, maxSmall), (2, 0), (2, 1), (2, 62), (3, 39), (maxSmall, 0), (maxSmall, 1)] do
    let expPow := if e == 0 then 1 else if a ≤ 1 then a else a ^ e
    evalBinOp s!"natPow fast {a}^{e}" pPow 15 mem ctx (tagNat a) (tagNat e) false (tagNat expPow) cnt
  for (a, e) in [(2, 63), (2, 64), (3, 40), (2 ^ 32, 2), (maxSmall, 2), (2, maxSmall)] do
    evalBinOp s!"natPow ovf {a}^{e}" pPow 15 mem ctx (tagNat a) (tagNat e) true 0 cnt
  for (lbl, wa, wb) in bigPairs do
    evalBinOp s!"natPow {lbl}" pPow 15 mem ctx wa wb true 0 cnt

  -- 10. natGcd (via `Rt.Procs.natGcdBig 16`): fast + big operands
  let pGcd ← lowerBin .natGcd
  for (a, b) in [(0, 0), (0, 42), (42, 0), (48, 18), (1071, 462), (maxSmall, maxSmall), (maxSmall, 7)] do
    evalBinOp s!"natGcd fast gcd({a},{b})" pGcd 16 mem ctx (tagNat a) (tagNat b) false (tagNat (Nat.gcd a b)) cnt
  for (lbl, wa, wb) in bigPairs do
    evalBinOp s!"natGcd {lbl}" pGcd 16 mem ctx wa wb true 0 cnt

  -- 11. End-to-end slow-path readback + `BigNat.Entry` semantic bridge check:
  -- For captured slow-path arguments `(wa, wb)`, decode via `readbackBigNat` and check `BigNat.Entry`
  for (lbl, wa, wb) in bigPairs do
    match Lir.eval pAdd 200 [wa, wb] mem ctx with
    | .ok ([res], mem') =>
      assertCheck (res == slowSentinel 1) s!"bridge add {lbl}: dispatched" cnt
      let some na := readbackBigNat mem' (mem'.read64 ctx)
        | throw (IO.userError s!"FAIL SlowPathTest: bridge readback wa failed ({lbl})")
      let some nb := readbackBigNat mem' (mem'.read64 (ctx + 8))
        | throw (IO.userError s!"FAIL SlowPathTest: bridge readback wb failed ({lbl})")
      let rAdd := Entry.add (SlowNat.ofNat na) (SlowNat.ofNat nb)
      let rMul := Entry.mul (SlowNat.ofNat na) (SlowNat.ofNat nb)
      let rGcd := Entry.gcd (SlowNat.ofNat na) (SlowNat.ofNat nb)
      assertCheck (isCanonical rAdd && rAdd.val == na + nb) s!"bridge add exact ({lbl})" cnt
      assertCheck (isCanonical rMul && rMul.val == na * nb) s!"bridge mul exact ({lbl})" cnt
      assertCheck (isCanonical rGcd && rGcd.val == Nat.gcd na nb) s!"bridge gcd exact ({lbl})" cnt
    | other => throw (IO.userError s!"FAIL SlowPathTest: bridge {lbl}: {renderOutcome other}")

def run : IO Nat := do
  let cnt ← IO.mkRef 0
  testEntryMatrix cnt
  testBootstrap cnt
  let ro ← buildRodataBigs cnt
  testLirDispatch ro cnt
  cnt.get

end IxCCTests.BigNat.SlowPathTest

def main : IO Unit := do
  let n ← IxCCTests.BigNat.SlowPathTest.run
  IO.println s!"SlowPathTest: PASS ({n} checks)"
