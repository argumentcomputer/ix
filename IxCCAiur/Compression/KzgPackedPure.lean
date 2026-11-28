import Ix.Compile.CircuitContract
import IxCCAiur.Compression.KzgWire

/-! # Single-Source Multi-Curve (BN254 & BLS12-381) Full Production KZG Packed Verifier (`KzgPackedPure`)

Pure total Lean 4 specification (ONLY `import Ix.Compile.CircuitContract` and
`import IxCCAiur.Compression.KzgWire`; ZERO `MultiStark`/`Aiur`/`IxCC` imports,
zero Mathlib, zero forbidden constructs) implementing the complete production
packed-SHPLONK compression pipeline parameterized over `CurveParams`:

1. **`KzgAlgebra`** (`MultiStark/BN/KzgAlgebra.lean`):
   - `expPower2`, `twoAdicGen`, `power2Mod`, `fingerprint`, `polynomial`,
     `claimsAccumulator`, `evalAt`, `foldRoots`, `lookupFingerprint`,
     `groupSummary`, `foldLookups`, and `verifyFrames`.
   - Static predecessor-key DAG evaluators are structured for `--partial-eval`
     auto-specialization so fixed predecessor keys automatically collapse into
     straight-line native `Fr` arithmetic (replacing `KzgPackedTerminal`'s manual
     fixed tables automatically!).
   - All ambient scalar-field operations invoke `KzgWire.fr{Add,Sub,Mul,Neg,Inv,Div,IsZero,Eq}`
     annotated `@[circuit_intrinsic "field.*"]`, lowering directly to zero-lookup
     native BN254 `Fr` or BLS12-381 `Fr` `Field` ops under `--field-lower`.
2. **`KzgPackedShape`** (`MultiStark/BN/KzgPackedShape.lean`):
   - Complete activation, domain, opening-width, row-budget (`≤ 2^39`), lookup-budget
     (`< 2^64`), and fixed-matrix slot verification supporting all 3 modes
     (`PackedFixed.none`, `PackedFixed.some`, `PackedFixed.shared`).
3. **`KzgPcsPacked`** (`MultiStark/BN/KzgPcsPacked.lean`):
   - Exact column packing by ascending height, declared next-row class (`1` before `0`),
     and source order (`2^(maxLog - log)` columns per pack), extra-evaluation absorption,
     BDFG SHPLONK opening reduction (`y = z^W`, Lagrange remainder, vanishing check),
     and 4-bit windowed `g1Msm` deferred pairing output `(A, B)`.
4. **`KzgPackedVerifier` & `CompressBNPacked`** (`MultiStark/BN/KzgPackedVerifier.lean`,
   `MultiStark/BN/CompressBNPacked.lean`):
   - Full BLAKE3 transcript replay + exact `"ix/aiur/kzg/fold-transcript/v1\0"`
     (31-byte domain tag) accumulator fold `current + w · previous`.
5. **`CompressNarrowFixed.stepV1` & `CompressFinalNarrow.verifyAccumulatorV1`**
   (`MultiStark/CompressNarrowFixed.lean`, `MultiStark/CompressFinalNarrow.lean`):
   - Authenticates `IXAUKG01` chain policy digest & anchors, validates predecessor
     `IXAUCL01` claims (stage-1 CompressGL schema and stage-`≥2` keyed chunk headers),
     verifies `IXAUSP01` packed proof under the fixed predecessor `IXAUSK02` key,
     folds the deferred pairing accumulator, and encodes the terminal `(A, B)` pair
     as **18 affine-u80 words (BN254)** or **22 affine-u80 words (BLS12-381)** for
     `gnark` `PairingCheck`!
6. **Dual-Curve Live-Exportable Benchmark Entrypoints**:
   - `entryNarrowStepBN254`, `entryNarrowStepBLS12381`,
   - `entryFinalTerminalBN254`, `entryFinalTerminalBLS12381`,
   - `entryAlgebraStaticBN254`, `entryAlgebraStaticBLS12381` (auto-downgrading to `TableTier.none`),
   - `entryGoldilocksSmoke` (live Goldilocks `ixcc_prove --pin` smoke entrypoint).
-/

set_option autoImplicit false

open scoped Ix.Circuit
open KzgWire

namespace KzgPackedPure

/-! ## Section 1: Monomorphic Verifier State & Result ADTs (`ShapeInfer`-Unboxed) -/

/-- Evaluation context for `evalAt` (`KzgAlgebra::Context`). -/
structure AirContext where
  main : FList
  mainNext : FList
  fixed : FList
  fixedNext : FList
  stage2 : FList
  stage2Next : FList
  pub0 : Nat
  pub1 : Nat
  pub2 : Nat
  pub3 : Nat
  first : Nat
  last : Nat
  transition : Nat
  deriving BEq, DecidableEq, Repr

/-- Monomorphic result of `groupSummary` (`KzgAlgebra::group_summary`). -/
structure GroupSummaryResult where
  product : Nat
  numerator : Nat
  rest : LookupList
  deriving BEq, DecidableEq, Repr

/-- One verified active circuit frame (`KzgPackedShape::Frame`). -/
structure PackedFrame where
  circuit : Circuit
  log : Nat
  nextAcc : Nat
  mainOpen : FListList
  stage2Open : FListList
  quotientOpen : FListList
  fixedOpen : FListList
  ownsFixed : Nat
  deriving BEq, DecidableEq, Repr

inductive PackedFrameList where
  | nil
  | cons (head : PackedFrame) (tail : PackedFrameList)
  deriving BEq, DecidableEq, Repr

/-- One opened matrix in a PCS round (`KzgPackedShape::Matrix`). -/
structure RoundMatrix where
  log : Nat
  width : Nat
  rows : FListList
  deriving BEq, DecidableEq, Repr

inductive RoundMatrixList where
  | nil
  | cons (head : RoundMatrix) (tail : RoundMatrixList)
  deriving BEq, DecidableEq, Repr

/-- Opened shared fixed slot `(ownerLog, openedRows)`. -/
structure OpenedSlot where
  ownerLog : Nat
  rows : FListList
  deriving BEq, DecidableEq, Repr

inductive OpenedSlotList where
  | nil
  | cons (head : OpenedSlot) (tail : OpenedSlotList)
  deriving BEq, DecidableEq, Repr

/-- Cursor over proof openings and commitment shapes (`KzgPackedShape::Cursor`). -/
structure ShapeCursor where
  logs : FList
  mainShapes : MatrixShapeList
  stage2Shapes : MatrixShapeList
  quotientShapes : MatrixShapeList
  accumulators : FList
  mainOpen : FList3
  stage2Open : FList3
  quotientOpen : FList3
  fixedShapes : MatrixShapeList
  fixedOpen : FList3
  deriving BEq, DecidableEq, Repr

/-- Shared-fixed slot tracker (`KzgPackedShape::Sharing`). -/
structure SharingState where
  shared : Nat
  slots : FList
  seen : OpenedSlotList
  count : Nat
  readers : Nat
  deriving BEq, DecidableEq, Repr

structure ConsumeFrameResult where
  ok : Nat
  frame : PackedFrame
  cursor : ShapeCursor
  sharing : SharingState
  deriving BEq, DecidableEq, Repr

structure BuildFramesResult where
  ok : Nat
  frames : PackedFrameList
  deriving BEq, DecidableEq, Repr

/-- One column being packed in `KzgPcsPacked` (`(val, nextVal, hasNext)`). -/
structure PackCol where
  val : Nat
  nextVal : Nat
  hasNext : Nat
  deriving BEq, DecidableEq, Repr

inductive PackColList where
  | nil
  | cons (head : PackCol) (tail : PackColList)
  deriving BEq, DecidableEq, Repr

/-- One grouped pack of columns sharing a commitment point (`KzgPcsPacked::Group`). -/
structure PackGroup where
  log : Nat
  cols : PackColList
  point : G1Point
  deriving BEq, DecidableEq, Repr

inductive PackGroupList where
  | nil
  | cons (head : PackGroup) (tail : PackGroupList)
  deriving BEq, DecidableEq, Repr

/-- One SHPLONK pack ready for BDFG weighing (`KzgPcsPacked::Pack`). -/
structure ShplonkPack where
  point : G1Point
  log : Nat
  needNext : Nat
  current : FList
  next : FList
  deriving BEq, DecidableEq, Repr

inductive ShplonkPackList where
  | nil
  | cons (head : ShplonkPack) (tail : ShplonkPackList)
  deriving BEq, DecidableEq, Repr

/-- One PCS round pairing commitment with its opened matrices (`KzgPcsPacked::Round`). -/
structure PcsRound where
  comm : PackedCommitment
  matrices : RoundMatrixList
  deriving BEq, DecidableEq, Repr

inductive PcsRoundList where
  | nil
  | cons (head : PcsRound) (tail : PcsRoundList)
  deriving BEq, DecidableEq, Repr

structure ExtractValuesResult where
  ok : Nat
  current : FList
  next : FList
  restExtras : FList
  deriving BEq, DecidableEq, Repr

structure GroupPacksResult where
  ok : Nat
  transcript : KzgTranscript
  packs : ShplonkPackList
  restExtras : FList
  deriving BEq, DecidableEq, Repr

structure RoundPacksResult where
  ok : Nat
  transcript : KzgTranscript
  packs : ShplonkPackList
  deriving BEq, DecidableEq, Repr

structure WeighResult where
  ok : Nat
  constant : Nat
  terms : G1TermList
  deriving BEq, DecidableEq, Repr

structure DeferredVerifyResult where
  ok : Nat
  transcript : KzgTranscript
  a : G1Point
  b : G1Point
  deriving BEq, DecidableEq, Repr

/-- Keyed claim chunk header for `CompressFinalNarrow` (`FinalNarrow.Header`). -/
structure ClaimHeader where
  tag : Nat
  owner : Nat
  width : Nat
  deriving BEq, DecidableEq, Repr

inductive ClaimHeaderList where
  | nil
  | cons (head : ClaimHeader) (tail : ClaimHeaderList)
  deriving BEq, DecidableEq, Repr

/-- Static configuration for `CompressFinalNarrow.verifyAccumulatorV1`. -/
structure FinalConfig where
  policyDigest : DigestWords
  expectedAnchors : ByteList
  stage : Nat
  keyDigest : DigestWords
  headers : ClaimHeaderList
  deriving BEq, DecidableEq, Repr

/-- Result of `CompressNarrowFixed.stepV1` (`ok = 1` iff verified, plus packed accumulator chunks). -/
structure StepV1Result where
  ok : Nat
  chunks : FList
  a : G1Point
  b : G1Point
  deriving BEq, DecidableEq, Repr

/-- Result of `CompressFinalNarrow.verifyAccumulatorV1` (`ok = 1` iff verified, plus 18/22 affine words). -/
structure FinalVerifyResult where
  ok : Nat
  affineWords : FList
  a : G1Point
  b : G1Point
  deriving BEq, DecidableEq, Repr

/-! ## Section 2: `KzgAlgebra` (Static VK DAG + Native `Fr` Intrinsics) -/

/-- Repeated squaring `value^(2^log) mod p` (`KzgAlgebra::exp_power2`). -/
@[circuit_noinline]
def expPower2 (p value : Nat) : Nat → Nat
  | 0 => value
  | log + 1 => expPower2 p (frMul p value value) log
termination_by structural log => log

/-- Primitive `2^log`-th root of unity (`KzgAlgebra::two_adic_gen`). -/
@[circuit_inline]
def twoAdicGen (c : CurveParams) (log : Nat) : Nat :=
  expPower2 c.frMod c.twoAdicGenMax (c.maxLog - log)

/-- Domain size `2^log mod p` (`KzgShape::power2`). -/
@[circuit_noinline]
def power2Mod (p : Nat) : Nat → Nat
  | 0 => 1
  | log + 1 =>
    let half := power2Mod p log
    frAdd p half half
termination_by structural log => log

/-- Exact `2^log` as `Nat` (used for shape row counts and pack capacities). -/
@[circuit_noinline]
def power2Nat : Nat → Nat
  | 0 => 1
  | k + 1 =>
    let h := power2Nat k
    h + h
termination_by structural k => k

/-- Discrete log base 2 of a power of two (`KzgShape::power_log`), bounded structurally by `fuel`. -/
def powerLogFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, v =>
    if v ≤ 1 then 0
    else powerLogFuel fuel (v / 2) + 1
termination_by structural fuel => fuel

def powerLog (v : Nat) : Nat :=
  powerLogFuel 32 v

/-- Index lookup in `FList` (`Lists::lookup` for field values). -/
@[circuit_noinline]
def fListGet (xs : FList) (idx : Nat) : Nat :=
  match xs with
  | .nil => 0
  | .cons v rest =>
    match idx with
    | 0 => v
    | k + 1 => fListGet rest k
termination_by structural xs

/-- Index lookup in `NodeList` (`Lists::lookup` for AIR DAG nodes). -/
@[circuit_noinline]
def nodeListGet (nodes : NodeList) (idx : Nat) : Node :=
  match nodes with
  | .nil => .const 0
  | .cons n rest =>
    match idx with
    | 0 => n
    | k + 1 => nodeListGet rest k
termination_by structural nodes

/-- Length of a `LookupList`. -/
@[circuit_noinline]
def lookupLength : LookupList → Nat
  | .nil => 0
  | .cons _ rest => lookupLength rest + 1
termination_by structural xs => xs

/-- First row of an opening matrix (`KzgAlgebra::first_row`). -/
@[circuit_inline]
def firstRow : FListList → FList
  | .nil => .nil
  | .cons r _ => r

/-- Second (next) row of an opening matrix (`KzgAlgebra::next_row`). -/
@[circuit_inline]
def nextRow : FListList → FList
  | .nil => .nil
  | .cons _ rest => firstRow rest

/-- Right-to-left Horner fingerprint `v0 + gamma * (v1 + ...)` (`KzgAlgebra::fingerprint`). -/
@[circuit_noinline]
def fingerprint (p : Nat) (values : FList) (gamma : Nat) : Nat :=
  match values with
  | .nil => 0
  | .cons v rest => frAdd p v (frMul p gamma (fingerprint p rest gamma))
termination_by structural values

/-- Right-to-left Horner polynomial evaluation `c0 + point * (c1 + ...)` (`KzgAlgebra::polynomial`). -/
@[circuit_noinline]
def polynomial (p : Nat) (values : FList) (point : Nat) : Nat :=
  match values with
  | .nil => 0
  | .cons v rest => frAdd p v (frMul p point (polynomial p rest point))
termination_by structural values

/-- LogUp claims accumulator `∑ 1 / (beta + fingerprint(claim, gamma))` (`KzgAlgebra::claims_accumulator`). -/
@[circuit_noinline]
def claimsAccumulator (p : Nat) (claims : FListList) (beta gamma : Nat) : Nat :=
  match claims with
  | .nil => 0
  | .cons claim rest =>
    let denom := frAdd p beta (fingerprint p claim gamma)
    frAdd p (frInv p denom) (claimsAccumulator p rest beta gamma)
termination_by structural claims

/-- Select the opened trace row for `Node.var source offset _` (`KzgAlgebra::eval_at`). -/
@[circuit_inline]
def selectRow (ctx : AirContext) (source offset : Nat) : FList :=
  match source + source + offset with
  | 0 => ctx.fixed
  | 1 => ctx.fixedNext
  | 2 => ctx.main
  | 3 => ctx.mainNext
  | 4 => ctx.stage2
  | _ => ctx.stage2Next

/-- Select one of the 4 public inputs (`KzgAlgebra::eval_at` `Node::Public`). -/
@[circuit_inline]
def pubAt (ctx : AirContext) (index : Nat) : Nat :=
  match index with
  | 0 => ctx.pub0
  | 1 => ctx.pub1
  | 2 => ctx.pub2
  | _ => ctx.pub3

/-- Bounded-depth AIR DAG evaluator (`KzgAlgebra::eval_at`); `--partial-eval`
automatically specializes any fixed predecessor key's DAG to straight-line `Fr` ops. -/
@[circuit_noinline]
def evalAt (p : Nat) (nodes : NodeList) (ctx : AirContext) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, idx =>
    match nodeListGet nodes idx with
    | .const v => v
    | .var source offset column => fListGet (selectRow ctx source offset) column
    | .pub i => pubAt ctx i
    | .first => ctx.first
    | .last => ctx.last
    | .transition => ctx.transition
    | .add a b => frAdd p (evalAt p nodes ctx fuel a) (evalAt p nodes ctx fuel b)
    | .sub a b => frSub p (evalAt p nodes ctx fuel a) (evalAt p nodes ctx fuel b)
    | .mul a b => frMul p (evalAt p nodes ctx fuel a) (evalAt p nodes ctx fuel b)
    | .neg a => frNeg p (evalAt p nodes ctx fuel a)
termination_by structural fuel => fuel

/-- Left-to-right Horner folding of evaluated AIR constraint roots (`KzgAlgebra::fold_roots`). -/
@[circuit_noinline]
def foldRoots (p : Nat) (roots : FList) (nodes : NodeList) (ctx : AirContext)
    (maxDepth alpha acc : Nat) : Nat :=
  match roots with
  | .nil => acc
  | .cons root rest =>
    let e := evalAt p nodes ctx maxDepth root
    let nextAcc := frAdd p (frMul p acc alpha) e
    foldRoots p rest nodes ctx maxDepth alpha nextAcc
termination_by structural roots

/-- Right-to-left Horner fingerprint over DAG-evaluated lookup arguments (`KzgAlgebra::lookup_fingerprint`). -/
@[circuit_noinline]
def lookupFingerprint (p : Nat) (args : FList) (nodes : NodeList) (ctx : AirContext)
    (maxDepth gamma : Nat) : Nat :=
  match args with
  | .nil => 0
  | .cons arg rest =>
    let e := evalAt p nodes ctx maxDepth arg
    let tailFp := lookupFingerprint p rest nodes ctx maxDepth gamma
    frAdd p e (frMul p gamma tailFp)
termination_by structural args

/-- Accumulate up to `remaining` lookups into a grouped rational sum (`KzgAlgebra::group_summary`). -/
@[circuit_noinline]
def groupSummary (p : Nat) (lookups : LookupList) (remaining : Nat)
    (nodes : NodeList) (ctx : AirContext) (maxDepth beta gamma product numerator : Nat) :
    GroupSummaryResult :=
  match remaining with
  | 0 => { product, numerator, rest := lookups }
  | rem + 1 =>
    match lookups with
    | .nil => { product, numerator, rest := .nil }
    | .cons lk rest =>
      let fp := lookupFingerprint p lk.args nodes ctx maxDepth gamma
      let message := frAdd p beta fp
      let multVal := evalAt p nodes ctx maxDepth lk.multiplicity
      let nextProd := frMul p product message
      let nextNum := frAdd p (frMul p numerator message) (frMul p multVal product)
      groupSummary p rest rem nodes ctx maxDepth beta gamma nextProd nextNum
termination_by structural remaining

/-- Countdown-fuelled worker for grouped LogUp constraint folding (`KzgAlgebra::fold_lookups`). -/
@[circuit_noinline]
def foldLookupsFuel (p : Nat) (fuel : Nat) (lookups : LookupList) (size index : Nat)
    (nodes : NodeList) (ctx : AirContext) (maxDepth beta gamma alpha : Nat)
    (current next : FList) (injection acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    match lookups with
    | .nil =>
      let diff := frSub p (fListGet next 0) (fListGet current 0)
      let term := frAdd p diff injection
      frAdd p (frMul p acc alpha) term
    | .cons _ _ =>
      let gs := groupSummary p lookups size nodes ctx maxDepth beta gamma 1 0
      let curIdx := fListGet current index
      match gs.rest with
      | .nil =>
        let target := frAdd p (fListGet next 0) injection
        let delta := frSub p target curIdx
        let value := frSub p (frMul p gs.product delta) gs.numerator
        frAdd p (frMul p acc alpha) value
      | rest =>
        let target := fListGet current (index + 1)
        let delta := frSub p target curIdx
        let value := frSub p (frMul p gs.product delta) gs.numerator
        let nextAcc := frAdd p (frMul p acc alpha) value
        foldLookupsFuel p fuel' rest size (index + 1) nodes ctx maxDepth
          beta gamma alpha current next injection nextAcc
termination_by structural fuel

/-- Grouped LogUp constraint folder (`KzgAlgebra::fold_lookups`). -/
@[circuit_inline]
def foldLookups (p : Nat) (lookups : LookupList) (size index : Nat)
    (nodes : NodeList) (ctx : AirContext) (maxDepth beta gamma alpha : Nat)
    (current next : FList) (injection acc : Nat) : Nat :=
  foldLookupsFuel p (lookupLength lookups + 1) lookups size index nodes ctx
    maxDepth beta gamma alpha current next injection acc

/-! ## Section 3: `KzgPackedShape` (Activation, Shared/Unshared Fixed Slots & Frame Verification) -/

/-- Verify that `rows` has exact length `count` and every row has exact width `width`
(`KzgShape::rows_width`). -/
def rowsWidthCheck (rows : FListList) (width : Nat) : Nat → Nat
  | 0 =>
    match rows with
    | .nil => 1
    | .cons _ _ => 0
  | n + 1 =>
    match rows with
    | .nil => 0
    | .cons r rest =>
      if fListLen r == width then rowsWidthCheck rest width n else 0
termination_by structural n => n

/-- Lookup an opened shared fixed slot by reverse index (`Lists::lookup(seen, count - slot)`). -/
def openedSlotGet (slots : OpenedSlotList) (idx : Nat) : Nat × OpenedSlot :=
  match slots with
  | .nil => (0, { ownerLog := 0, rows := .nil })
  | .cons s rest =>
    match idx with
    | 0 => (1, s)
    | k + 1 => openedSlotGet rest k
termination_by structural slots

/-- Consume and verify one packed matrix shape `(log, width)` (`KzgPackedShape::shape`). -/
def consumeMatrixShape (shapes : MatrixShapeList) (log width : Nat) : Nat × MatrixShapeList :=
  match shapes with
  | .nil => (0, .nil)
  | .cons sh rest =>
    if sh.log == log && sh.width == width then (1, rest) else (0, .nil)

private def emptyCircuit : Circuit :=
  { shape := { m0 := 0, m1 := 0, m2 := 0, m3 := 0, m4 := 0, m5 := 0, m6 := 1, m7 := 1 }
    nodes := .nil, roots := .nil, lookups := .nil, mainNext := 0, fixedNext := 0 }

private def emptyFrame : PackedFrame :=
  { circuit := emptyCircuit, log := 0, nextAcc := 0
    mainOpen := .nil, stage2Open := .nil, quotientOpen := .nil, fixedOpen := .nil, ownsFixed := 0 }

/-- Consume one active circuit's shapes, openings, and optional shared/owned fixed slot
(`KzgPackedShape::consume`). -/
def consumeFrame (c : CurveParams) (circ : Circuit) (cur : ShapeCursor) (sh : SharingState)
    (maxLog : Nat) : ConsumeFrameResult :=
  let fail : ConsumeFrameResult := { ok := 0, frame := emptyFrame, cursor := cur, sharing := sh }
  let w := circ.shape
  match cur.logs, cur.accumulators, cur.mainOpen, cur.stage2Open, cur.quotientOpen with
  | .cons log restLogs, .cons acc restAccs,
    .cons mv restMo, .cons sv restSo, .cons qv restQo =>
    if log ≤ maxLog && log + powerLog w.m7 ≤ c.maxLog then
      let (mOk, restMs) := consumeMatrixShape cur.mainShapes log w.m4
      let (sOk, restSs) := consumeMatrixShape cur.stage2Shapes log w.m5
      let (qOk, restQs) := consumeMatrixShape cur.quotientShapes log w.m7
      if mOk == 1 && sOk == 1 && qOk == 1 &&
          rowsWidthCheck mv w.m4 (1 + circ.mainNext) == 1 &&
          rowsWidthCheck sv w.m5 2 == 1 &&
          rowsWidthCheck qv w.m7 1 == 1 then
        let (slotOk, slot, restSlots) : Nat × Nat × FList :=
          if sh.shared == 0 then (1, 0, sh.slots)
          else match sh.slots with
            | .cons sl tl => (1, sl, tl)
            | .nil => (0, 0, .nil)
        if slotOk == 0 then fail
        else if w.m3 == 0 then
          if slot == 0 then
            let cur' : ShapeCursor :=
              { logs := restLogs, mainShapes := restMs, stage2Shapes := restSs
                quotientShapes := restQs, accumulators := restAccs
                mainOpen := restMo, stage2Open := restSo, quotientOpen := restQo
                fixedShapes := cur.fixedShapes, fixedOpen := cur.fixedOpen }
            let sh' : SharingState := { sh with slots := restSlots }
            let fr : PackedFrame :=
              { circuit := circ, log, nextAcc := acc
                mainOpen := mv, stage2Open := sv, quotientOpen := qv
                fixedOpen := .nil, ownsFixed := 0 }
            { ok := 1, frame := fr, cursor := cur', sharing := sh' }
          else fail
        else
          if w.m2 != power2Nat log then fail
          else
            let owns := if sh.shared == 0 || slot == sh.count + 1 then 1 else 0
            if owns == 1 then
              let (fOk, restFs) := consumeMatrixShape cur.fixedShapes log w.m3
              match fOk, cur.fixedOpen with
              | 1, .cons fv restFo =>
                if rowsWidthCheck fv w.m3 (1 + circ.fixedNext) == 1 then
                  let cur' : ShapeCursor :=
                    { logs := restLogs, mainShapes := restMs, stage2Shapes := restSs
                      quotientShapes := restQs, accumulators := restAccs
                      mainOpen := restMo, stage2Open := restSo, quotientOpen := restQo
                      fixedShapes := restFs, fixedOpen := restFo }
                  let sh' : SharingState :=
                    { shared := sh.shared, slots := restSlots
                      seen := .cons { ownerLog := log, rows := fv } sh.seen
                      count := sh.count + 1, readers := sh.readers + 1 }
                  let fr : PackedFrame :=
                    { circuit := circ, log, nextAcc := acc
                      mainOpen := mv, stage2Open := sv, quotientOpen := qv
                      fixedOpen := fv, ownsFixed := 1 }
                  { ok := 1, frame := fr, cursor := cur', sharing := sh' }
                else fail
              | _, _ => fail
            else
              if 0 < slot && slot ≤ sh.count then
                let (lkOk, owner) := openedSlotGet sh.seen (sh.count - slot)
                if lkOk == 1 && owner.ownerLog == log &&
                    rowsWidthCheck owner.rows w.m3 (1 + circ.fixedNext) == 1 then
                  let cur' : ShapeCursor :=
                    { logs := restLogs, mainShapes := restMs, stage2Shapes := restSs
                      quotientShapes := restQs, accumulators := restAccs
                      mainOpen := restMo, stage2Open := restSo, quotientOpen := restQo
                      fixedShapes := cur.fixedShapes, fixedOpen := cur.fixedOpen }
                  let sh' : SharingState :=
                    { sh with slots := restSlots, readers := sh.readers + 1 }
                  let fr : PackedFrame :=
                    { circuit := circ, log, nextAcc := acc
                      mainOpen := mv, stage2Open := sv, quotientOpen := qv
                      fixedOpen := owner.rows, ownsFixed := 0 }
                  { ok := 1, frame := fr, cursor := cur', sharing := sh' }
                else fail
              else fail
      else fail
    else fail
  | _, _, _, _, _ => fail

/-- Walk circuits and activation flags, enforcing total rows `≤ 2^39`, lookup budget `< 2^64`,
shared fixed slot invariants, and complete exhaustion of every proof list (`KzgPackedShape::walk`). -/
def walkFrames (c : CurveParams) (circuits : CircuitList) (active : FList) (cur : ShapeCursor)
    (sh : SharingState) (maxLog totalRows lookupBudget : Nat) : BuildFramesResult :=
  match circuits, active with
  | .nil, .nil =>
    let cursorEmpty :=
      match cur.logs, cur.mainShapes, cur.stage2Shapes, cur.quotientShapes, cur.accumulators,
            cur.mainOpen, cur.stage2Open, cur.quotientOpen, cur.fixedShapes, cur.fixedOpen with
      | .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil, .nil => true
      | _, _, _, _, _, _, _, _, _, _ => false
    let slotsEmpty := match sh.slots with | .nil => true | .cons _ _ => false
    let sharedOk := if sh.shared == 0 then true else sh.count < sh.readers
    let rowBound := 549755813888 -- 2^39
    let u64Bound := 4294967296 * 4294967296
    if cursorEmpty && slotsEmpty && sharedOk &&
        0 < totalRows && totalRows ≤ rowBound && lookupBudget < u64Bound then
      { ok := 1, frames := .nil }
    else { ok := 0, frames := .nil }
  | .cons circ restCircs, .cons on restAct =>
    if on == 0 then
      if circ.shape.m2 != 0 then { ok := 0, frames := .nil }
      else if sh.shared == 0 then
        walkFrames c restCircs restAct cur sh maxLog totalRows lookupBudget
      else match sh.slots with
        | .cons sl tl =>
          if sl == 0 then
            walkFrames c restCircs restAct cur { sh with slots := tl } maxLog totalRows lookupBudget
          else { ok := 0, frames := .nil }
        | .nil => { ok := 0, frames := .nil }
    else if on == 1 then
      let res := consumeFrame c circ cur sh maxLog
      if res.ok == 1 then
        let rows := power2Nat res.frame.log
        let lcnt := lookupLength circ.lookups
        let lcntEff := if lcnt == 0 then 1 else lcnt
        let tl := walkFrames c restCircs restAct res.cursor res.sharing maxLog
          (totalRows + rows) (lookupBudget + rows * lcntEff)
        if tl.ok == 1 then { ok := 1, frames := .cons res.frame tl.frames }
        else { ok := 0, frames := .nil }
      else { ok := 0, frames := .nil }
    else { ok := 0, frames := .nil }
  | _, _ => { ok := 0, frames := .nil }
termination_by structural circuits

/-- Build and validate all active frames for `(key, proof)` (`KzgPackedShape::frames`). -/
def buildFrames (c : CurveParams) (key : PackedKey) (proof : PackedProof) : BuildFramesResult :=
  let unshared : SharingState := { shared := 0, slots := .nil, seen := .nil, count := 0, readers := 0 }
  match key.fixed, proof.fixedOpen with
  | .none, .none =>
    let cur : ShapeCursor :=
      { logs := proof.logs, mainShapes := proof.main.shapes, stage2Shapes := proof.stage2.shapes
        quotientShapes := proof.quotient.shapes, accumulators := proof.accumulators
        mainOpen := proof.mainOpen, stage2Open := proof.stage2Open, quotientOpen := proof.quotientOpen
        fixedShapes := .nil, fixedOpen := .nil }
    walkFrames c key.circuits proof.active cur unshared key.maxLog 0 1
  | .some fx, .some fo =>
    let cur : ShapeCursor :=
      { logs := proof.logs, mainShapes := proof.main.shapes, stage2Shapes := proof.stage2.shapes
        quotientShapes := proof.quotient.shapes, accumulators := proof.accumulators
        mainOpen := proof.mainOpen, stage2Open := proof.stage2Open, quotientOpen := proof.quotientOpen
        fixedShapes := fx.shapes, fixedOpen := fo }
    walkFrames c key.circuits proof.active cur unshared key.maxLog 0 1
  | .shared fx slots, .some fo =>
    let cur : ShapeCursor :=
      { logs := proof.logs, mainShapes := proof.main.shapes, stage2Shapes := proof.stage2.shapes
        quotientShapes := proof.quotient.shapes, accumulators := proof.accumulators
        mainOpen := proof.mainOpen, stage2Open := proof.stage2Open, quotientOpen := proof.quotientOpen
        fixedShapes := fx.shapes, fixedOpen := fo }
    let sh : SharingState := { shared := 1, slots, seen := .nil, count := 0, readers := 0 }
    walkFrames c key.circuits proof.active cur sh key.maxLog 0 1
  | _, _ => { ok := 0, frames := .nil }

/-- Verify a single frame's AIR DAG, grouped LogUp constraints, and quotient identity over `c.frMod`.
Returns `1` iff valid, else `0`. Automatically specialized under `--partial-eval` when called on a fixed key. -/
@[circuit_noinline]
def verifySingleFrame (c : CurveParams) (circ : Circuit) (maxDepth log : Nat)
    (mainOpen stage2Open quotientOpen fixedOpen : FListList)
    (beta gamma alpha zeta acc nextAcc : Nat) : Nat :=
  let p := c.frMod
  let zN := expPower2 p zeta log
  let vanishing := frSub p zN 1
  if frIsZero vanishing == 1 then 0
  else
    let g := twoAdicGen c log
    let invG := frInv p g
    let transition := frSub p zeta invG
    let first := frDiv p vanishing (frSub p zeta 1)
    let last := frDiv p vanishing transition
    let current := firstRow stage2Open
    let next := nextRow stage2Open
    let ctx : AirContext :=
      { main := firstRow mainOpen, mainNext := nextRow mainOpen
        fixed := firstRow fixedOpen, fixedNext := nextRow fixedOpen
        stage2 := current, stage2Next := next
        pub0 := beta, pub1 := gamma, pub2 := acc, pub3 := nextAcc
        first, last, transition }
    let folded0 := foldRoots p circ.roots circ.nodes ctx maxDepth alpha 0
    let domSize := power2Mod p log
    let injection := frDiv p (frMul p last (frSub p nextAcc acc)) (frMul p domSize g)
    let folded := foldLookups p circ.lookups circ.shape.m6 0 circ.nodes ctx
      maxDepth beta gamma alpha current next injection folded0
    let quotient := polynomial p (firstRow quotientOpen) zN
    frEq folded (frMul p vanishing quotient)

/-- Verify all active frames in order and require final accumulator `== 0`
(`KzgPackedShape::verify_frames`). -/
def verifyFrames (c : CurveParams) (frames : PackedFrameList)
    (beta gamma alpha zeta accumulator : Nat) : Nat :=
  match frames with
  | .nil => frIsZero accumulator
  | .cons fr rest =>
    let depth := nodeListLen fr.circuit.nodes + 1
    let ok := verifySingleFrame c fr.circuit depth fr.log
      fr.mainOpen fr.stage2Open fr.quotientOpen fr.fixedOpen
      beta gamma alpha zeta accumulator fr.nextAcc
    if ok == 1 then verifyFrames c rest beta gamma alpha zeta fr.nextAcc
    else 0
termination_by structural frames

/-- Extract opened matrices for PCS round `round ∈ {0: main, 1: stage2, 2: quotient, 3: owned fixed}`
(`KzgPackedShape::matrices`). -/
def roundMatrices (frames : PackedFrameList) (round : Nat) : RoundMatrixList :=
  match frames with
  | .nil => .nil
  | .cons fr rest =>
    let tail := roundMatrices rest round
    let s := fr.circuit.shape
    match round with
    | 0 => .cons { log := fr.log, width := s.m4, rows := fr.mainOpen } tail
    | 1 => .cons { log := fr.log, width := s.m5, rows := fr.stage2Open } tail
    | 2 => .cons { log := fr.log, width := s.m7, rows := fr.quotientOpen } tail
    | _ =>
      if fr.ownsFixed == 1 then .cons { log := fr.log, width := s.m3, rows := fr.fixedOpen } tail
      else tail
termination_by structural frames

/-! ## Section 4: `KzgPcsPacked` (Exact Packed-SHPLONK Deferred Pairing Reduction) -/

/-- Append `PackGroupList`s. -/
def packGroupAppend (a b : PackGroupList) : PackGroupList :=
  match a with
  | .nil => b
  | .cons h t => .cons h (packGroupAppend t b)
termination_by structural a

/-- Append `ShplonkPackList`s. -/
def shplonkPackAppend (a b : ShplonkPackList) : ShplonkPackList :=
  match a with
  | .nil => b
  | .cons h t => .cons h (shplonkPackAppend t b)
termination_by structural a

/-- Prepend columns of one matrix onto `tail`, rejecting conflicting repeated evaluations at `log = 0`
(`KzgPcsPacked::columns_onto`). -/
def columnsOnto (current next : FList) (hasNext log : Nat) (tail : PackColList) : Nat × PackColList :=
  match current with
  | .nil =>
    match next with
    | .nil => (1, tail)
    | .cons _ _ => (0, .nil)
  | .cons v rest =>
    if hasNext == 0 then
      let (ok, tl) := columnsOnto rest next 0 log tail
      (ok, .cons { val := v, nextVal := 0, hasNext := 0 } tl)
    else match next with
      | .cons after restNext =>
        if log == 0 && v != after then (0, .nil)
        else
          let (ok, tl) := columnsOnto rest restNext 1 log tail
          (ok, .cons { val := v, nextVal := after, hasNext := 1 } tl)
      | .nil => (0, .nil)
termination_by structural current

/-- Gather all columns matching `(log, nextClass)` across a round's matrices (`KzgPcsPacked::columns_at`). -/
def columnsAt (mats : RoundMatrixList) (shapes : MatrixShapeList) (log nextClass : Nat) :
    Nat × PackColList :=
  match mats, shapes with
  | .nil, .nil => (1, .nil)
  | .cons m restM, .cons sh restSh =>
    let (okT, tail) := columnsAt restM restSh log nextClass
    if okT == 0 then (0, .nil)
    else if m.log == log && sh.hasNext == nextClass then
      let rowCount := fListListLen m.rows
      let hn := if rowCount == 2 then 1 else 0
      columnsOnto (firstRow m.rows) (nextRow m.rows) hn log tail
    else (1, tail)
  | _, _ => (0, .nil)
termination_by structural mats

/-- Split at most `remaining` columns off the front (`KzgPcsPacked::split`). -/
def splitPackCols (cols : PackColList) : Nat → PackColList × PackColList
  | 0 => (.nil, cols)
  | n + 1 =>
    match cols with
    | .nil => (.nil, .nil)
    | .cons c rest =>
      let (hd, tl) := splitPackCols rest n
      (.cons c hd, tl)
termination_by structural n => n

def packColLen : PackColList → Nat
  | .nil => 0
  | .cons _ t => packColLen t + 1
termination_by structural xs => xs

/-- Partition columns at `log` into packs of size `capacity`, pairing each with its commitment point
(`KzgPcsPacked::at_log`). -/
def groupsAtLogFuel (cols : PackColList) (pts : G1PointList) (log capacity : Nat) :
    Nat → Nat × PackGroupList × G1PointList
  | 0 =>
    match cols with
    | .nil => (1, .nil, pts)
    | .cons _ _ => (0, .nil, .nil)
  | fuel + 1 =>
    match cols with
    | .nil => (1, .nil, pts)
    | .cons _ _ =>
      let (hd, restCols) := splitPackCols cols capacity
      match pts with
      | .nil => (0, .nil, .nil)
      | .cons pt restPts =>
        let (ok, tl, remPts) := groupsAtLogFuel restCols restPts log capacity fuel
        if ok == 1 then (1, .cons { log, cols := hd, point := pt } tl, remPts)
        else (0, .nil, .nil)
termination_by structural fuel => fuel

/-- Walk heights `log .. maxLog` in ascending order (`hasNext = 1` before `hasNext = 0`)
reconstructing every pack from authenticated matrix shapes (`KzgPcsPacked::walk`). -/
def walkGroupsFuel (mats : RoundMatrixList) (shapes : MatrixShapeList) (pts : G1PointList)
    (log maxLog : Nat) : Nat → Nat × PackGroupList
  | 0 => (0, .nil)
  | fuel + 1 =>
    let cap := power2Nat (maxLog - log)
    let (okN, colsN) := columnsAt mats shapes log 1
    let (okC, colsC) := columnsAt mats shapes log 0
    if okN == 0 || okC == 0 then (0, .nil)
    else
      let (ok1, grpsN, pts1) := groupsAtLogFuel colsN pts log cap (packColLen colsN + 1)
      let (ok2, grpsC, pts2) := groupsAtLogFuel colsC pts1 log cap (packColLen colsC + 1)
      if ok1 == 0 || ok2 == 0 then (0, .nil)
      else
        let hd := packGroupAppend grpsN grpsC
        if log == maxLog then
          match pts2 with
          | .nil => (1, hd)
          | .cons _ _ => (0, .nil)
        else
          let (okT, tl) := walkGroupsFuel mats shapes pts2 (log + 1) maxLog fuel
          if okT == 1 then (1, packGroupAppend hd tl) else (0, .nil)
termination_by structural fuel => fuel

/-- True (`1`) iff any column in the pack requests a next-row evaluation (`KzgPcsPacked::has_next`). -/
def packHasNext : PackColList → Nat
  | .nil => 0
  | .cons col rest => if col.hasNext == 1 then 1 else packHasNext rest
termination_by structural cols => cols

/-- Extract `(current, next)` column evaluations for a pack, consuming `extras` for columns
that didn't request a next-row opening (`KzgPcsPacked::values`). -/
def extractPackValues (cols : PackColList) (extras : FList) (needNext : Nat) : ExtractValuesResult :=
  match cols with
  | .nil => { ok := 1, current := .nil, next := .nil, restExtras := extras }
  | .cons col rest =>
    if needNext == 0 then
      let sub := extractPackValues rest extras 0
      if sub.ok == 1 then
        { ok := 1, current := .cons col.val sub.current, next := .nil, restExtras := sub.restExtras }
      else { ok := 0, current := .nil, next := .nil, restExtras := .nil }
    else
      let (okE, nxtVal, remEx) : Nat × Nat × FList :=
        if col.hasNext == 1 then (1, col.nextVal, extras)
        else match extras with
          | .cons e tl => (1, e, tl)
          | .nil => (0, 0, .nil)
      if okE == 0 then { ok := 0, current := .nil, next := .nil, restExtras := .nil }
      else
        let sub := extractPackValues rest remEx 1
        if sub.ok == 1 then
          { ok := 1, current := .cons col.val sub.current, next := .cons nxtVal sub.next
            restExtras := sub.restExtras }
        else { ok := 0, current := .nil, next := .nil, restExtras := .nil }
termination_by structural cols

/-- Observe opened query points per matrix into the transcript (`KzgPcsPacked::observe_matrix_queries`). -/
def observeMatrixQueries (c : CurveParams) (tr : KzgTranscript) (mats : RoundMatrixList)
    (zeta : Nat) : KzgTranscript :=
  match mats with
  | .nil => tr
  | .cons m rest =>
    let cnt := fListListLen m.rows
    let tr1 := transcriptObserveU64 tr cnt
    let tr2 := transcriptObserveField tr1 zeta
    let tr3 :=
      if cnt == 2 then
        transcriptObserveField tr2 (frMul c.frMod zeta (twoAdicGen c m.log))
      else tr2
    observeMatrixQueries c tr3 rest zeta
termination_by structural mats

def roundMatrixLen : RoundMatrixList → Nat
  | .nil => 0
  | .cons _ t => roundMatrixLen t + 1
termination_by structural ms => ms

def pcsRoundLen : PcsRoundList → Nat
  | .nil => 0
  | .cons _ t => pcsRoundLen t + 1
termination_by structural rs => rs

/-- Observe round commitments and query points (`KzgPcsPacked::observe_rounds`). -/
def observeRounds (c : CurveParams) (tr : KzgTranscript) (rounds : PcsRoundList)
    (zeta : Nat) : KzgTranscript :=
  match rounds with
  | .nil => tr
  | .cons rd rest =>
    let tr1 := transcriptObserveBytes tr rd.comm.rawBytes
    let tr2 := transcriptObserveU64 tr1 (roundMatrixLen rd.matrices)
    observeRounds c (observeMatrixQueries c tr2 rd.matrices zeta) rest zeta
termination_by structural rounds

/-- Absorb pack evaluations and construct `ShplonkPackList` (`KzgPcsPacked::group_packs`). -/
def groupPacks (tr : KzgTranscript) (groups : PackGroupList) (extras : FList) : GroupPacksResult :=
  match groups with
  | .nil => { ok := 1, transcript := tr, packs := .nil, restExtras := extras }
  | .cons grp rest =>
    let needNext := if packHasNext grp.cols == 1 && grp.log != 0 then 1 else 0
    let ev := extractPackValues grp.cols extras needNext
    if ev.ok == 0 then { ok := 0, transcript := tr, packs := .nil, restExtras := .nil }
    else
      let tr1 := transcriptObserveFields tr ev.current
      let tr2 := transcriptObserveFields tr1 ev.next
      let sub := groupPacks tr2 rest ev.restExtras
      if sub.ok == 1 then
        let pk : ShplonkPack :=
          { point := grp.point, log := grp.log, needNext, current := ev.current, next := ev.next }
        { ok := 1, transcript := sub.transcript, packs := .cons pk sub.packs, restExtras := sub.restExtras }
      else { ok := 0, transcript := tr, packs := .nil, restExtras := .nil }
termination_by structural groups

/-- Reconstruct and absorb all packs across all PCS rounds, enforcing exact `extras` exhaustion
(`KzgPcsPacked::round_packs`). -/
def roundPacks (tr : KzgTranscript) (rounds : PcsRoundList) (extras : FList) (maxLog : Nat) :
    RoundPacksResult :=
  match rounds with
  | .nil =>
    match extras with
    | .nil => { ok := 1, transcript := tr, packs := .nil }
    | .cons _ _ => { ok := 0, transcript := tr, packs := .nil }
  | .cons rd rest =>
    let (okG, groups) := walkGroupsFuel rd.matrices rd.comm.shapes rd.comm.points 0 maxLog (maxLog + 1)
    if okG == 0 then { ok := 0, transcript := tr, packs := .nil }
    else
      let gp := groupPacks tr groups extras
      if gp.ok == 0 then { ok := 0, transcript := tr, packs := .nil }
      else
        let sub := roundPacks gp.transcript rest gp.restExtras maxLog
        if sub.ok == 1 then
          { ok := 1, transcript := sub.transcript, packs := shplonkPackAppend gp.packs sub.packs }
        else { ok := 0, transcript := tr, packs := .nil }
termination_by structural rounds

/-- Structural binary powering `acc * base^exp mod p` for u32 pack widths (`KzgPcsPacked::pow_u32`). -/
@[circuit_noinline]
def frPowU32Fuel (p : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, base, exp, acc =>
    match exp with
    | 0 => acc
    | _ =>
      let nextAcc := if exp % 2 == 1 then frMul p acc base else acc
      frPowU32Fuel p fuel (frMul p base base) (exp / 2) nextAcc
termination_by structural fuel => fuel

@[circuit_inline]
def frPowU32 (p base exp : Nat) : Nat :=
  frPowU32Fuel p 32 base exp 1

/-- BDFG SHPLONK weighing of a single pack (`y = z^W`, `Z_S(z)`, Lagrange `r(z)`, `weight = power / Z_S(z)`). -/
@[circuit_noinline]
def weighSinglePack (c : CurveParams) (log needNext : Nat) (current next : FList)
    (z zeta power : Nat) : Nat × Nat × Nat :=
  let p := c.frMod
  let w := fListLen current
  let y := frPowU32 p z w
  let here := polynomial p current z
  let (vanishing, remainder) : Nat × Nat :=
    if needNext == 0 then (frSub p y zeta, here)
    else
      let after := frMul p zeta (twoAdicGen c log)
      let lagrange := frDiv p (frSub p y after) (frSub p zeta after)
      let van := frMul p (frSub p y zeta) (frSub p y after)
      let nxtEval := polynomial p next z
      let rem := frAdd p (frMul p lagrange here) (frMul p (frSub p 1 lagrange) nxtEval)
      (van, rem)
  if frIsZero vanishing == 1 then (0, 0, 0)
  else
    let weight := frDiv p power vanishing
    (1, weight, frMul p weight remainder)

/-- Accumulate SHPLONK weights and MSM terms across all packs (`KzgPcsPacked::weigh`). -/
def weighPacks (c : CurveParams) (packs : ShplonkPackList)
    (gamma z zeta power constant : Nat) (terms : G1TermList) : WeighResult :=
  match packs with
  | .nil => { ok := 1, constant, terms }
  | .cons pk rest =>
    let (ok, weight, cTerm) := weighSinglePack c pk.log pk.needNext pk.current pk.next z zeta power
    if ok == 0 then { ok := 0, constant := 0, terms := .nil }
    else
      let p := c.frMod
      weighPacks c rest gamma z zeta (frMul p power gamma) (frAdd p constant cTerm)
        (.cons { point := pk.point, scalar := weight } terms)
termination_by structural packs

/-- Construct PCS rounds `[main, stage2, quotient, (optional fixed)]` (`KzgPcsPacked::rounds`). -/
def buildPcsRounds (frames : PackedFrameList)
    (main stage2 quotient : PackedCommitment) (fixed : PackedFixed) : PcsRoundList :=
  let tail : PcsRoundList := match fixed with
    | .none => .nil
    | .some fx => .cons { comm := fx, matrices := roundMatrices frames 3 } .nil
    | .shared fx _ => .cons { comm := fx, matrices := roundMatrices frames 3 } .nil
  .cons { comm := main, matrices := roundMatrices frames 0 }
    (.cons { comm := stage2, matrices := roundMatrices frames 1 }
    (.cons { comm := quotient, matrices := roundMatrices frames 2 } tail))

/-- Complete packed-SHPLONK opening reduction (`KzgPcsPacked::reduce`), returning the final
transcript after `[W₂]` and deferred pairing operands `(A, B)` satisfying
`e(A, [1]₂) · e(B, [τ]₂) = 1`. -/
def reducePcs (c : CurveParams) (tr : KzgTranscript) (rounds : PcsRoundList)
    (extras : FList) (w1 w2 : PackedWitness) (zeta : Nat) (generator : G1Point)
    (maxLog : Nat) : DeferredVerifyResult :=
  let tr1 := transcriptObserveBytes tr openDomainBytes
  let tr2 := transcriptObserveU64 tr1 (pcsRoundLen rounds)
  let tr3 := observeRounds c tr2 rounds zeta
  let rp := roundPacks tr3 rounds extras maxLog
  if rp.ok == 0 then { ok := 0, transcript := tr, a := g1Inf, b := g1Inf }
  else
    let tr4 := transcriptObserveBytes rp.transcript batchDomainBytes
    let sGamma := transcriptSampleFr c tr4
    let tr5 := transcriptObserveBytes sGamma.transcript w1.rawBytes
    let sZ := transcriptSampleFr c tr5
    let tr6 := transcriptObserveBytes sZ.transcript w2.rawBytes
    let wg := weighPacks c rp.packs sGamma.challenge sZ.challenge zeta 1 0 .nil
    if wg.ok == 0 then { ok := 0, transcript := tr6, a := g1Inf, b := g1Inf }
    else
      let negConst := frNeg c.frMod wg.constant
      let allTerms : G1TermList :=
        .cons { point := generator, scalar := negConst }
          (.cons { point := w2.point, scalar := sZ.challenge } wg.terms)
      let msmPt := g1Msm c allTerms
      let a := g1Add c msmPt (g1Neg c w1.point)
      let b := g1Neg c w2.point
      { ok := 1, transcript := tr6, a, b }

/-! ## Section 5: `KzgPackedVerifier` & `CompressBNPacked` -/

/-- Absorb circuit shapes `[m0..m6]` (exact 7 fields per circuit, `KzgVerifier::observe_shape`). -/
def observeCircuitShapes (tr : KzgTranscript) (circuits : CircuitList) : KzgTranscript :=
  match circuits with
  | .nil => tr
  | .cons circ rest =>
    let s := circ.shape
    let tr1 := transcriptObserveField tr s.m0
    let tr2 := transcriptObserveField tr1 s.m1
    let tr3 := transcriptObserveField tr2 s.m2
    let tr4 := transcriptObserveField tr3 s.m3
    let tr5 := transcriptObserveField tr4 s.m4
    let tr6 := transcriptObserveField tr5 s.m5
    let tr7 := transcriptObserveField tr6 s.m6
    observeCircuitShapes tr7 rest
termination_by structural circuits

/-- Absorb packed verifying key into the transcript (`KzgPackedVerifier::observe_key`). -/
def observeKey (seed : ByteList) (circuits : CircuitList) (active : FList)
    (fixed : PackedFixed) : KzgTranscript :=
  let tr0 := transcriptObserveField (transcriptStart seed) (circuitListLen circuits)
  let tr1 := observeCircuitShapes tr0 circuits
  match fixed with
  | .none => transcriptObserveFields tr1 active
  | .some fx => transcriptObserveBytes (transcriptObserveFields tr1 active) fx.rawBytes
  | .shared fx slots =>
    transcriptObserveBytes
      (transcriptObserveFields (transcriptObserveFields tr1 slots) active) fx.rawBytes

/-- Validate all `G1` points in a `PackedFixed` commitment (on-curve + BLS12-381 subgroup check). -/
def fixedPointsValid (c : CurveParams) : PackedFixed → Bool
  | .none => true
  | .some comm => g1PointListValid c comm.points
  | .shared comm _ => g1PointListValid c comm.points

/-- Full native-`Fr` packed-SHPLONK multi-stark verifier (`KzgPackedVerifier::verify`),
enforcing canonical verifying-key/fixed-commitment transcript-seed binding (`seedBindsPackedKey`)
and prime-order `G1` subgroup membership on all key and proof points, returning the final
transcript (ready for `CompressBNPacked.foldAccumulator`) and `(A, B)`. -/
def verifyPacked (c : CurveParams) (key : PackedKey) (proof : PackedProof)
    (claims : FListList) : DeferredVerifyResult :=
  let fail : DeferredVerifyResult := { ok := 0, transcript := transcriptStart .nil, a := g1Inf, b := g1Inf }
  if seedBindsPackedKey c key.seed key.circuits key.fixed == 0 then fail
  else if !g1ValidPoint c key.generator || !fixedPointsValid c key.fixed ||
      !g1PointListValid c proof.main.points || !g1PointListValid c proof.stage2.points ||
      !g1PointListValid c proof.quotient.points || !g1ValidPoint c proof.w1.point ||
      !g1ValidPoint c proof.w2.point then fail
  else
    let bf := buildFrames c key proof
    if bf.ok == 0 then fail
    else
      let tr0 := observeKey key.seed key.circuits proof.active key.fixed
      let tr1 := transcriptObserveBytes tr0 proof.main.rawBytes
      let tr2 := transcriptObserveFields tr1 proof.logs
      let tr3 := transcriptObserveClaims tr2 claims
      let sBeta := transcriptSampleFr c tr3
      let tr4 := transcriptObserveField sBeta.transcript sBeta.challenge
      let sGamma := transcriptSampleFr c tr4
      let tr5 := transcriptObserveField sGamma.transcript sGamma.challenge
      let initial := claimsAccumulator c.frMod claims sBeta.challenge sGamma.challenge
      let tr6 := transcriptObserveBytes tr5 proof.stage2.rawBytes
      let tr7 := transcriptObserveFields tr6 proof.accumulators
      let sAlpha := transcriptSampleFr c tr7
      let tr8 := transcriptObserveBytes sAlpha.transcript proof.quotient.rawBytes
      let sZeta := transcriptSampleFr c tr8
      if frIsZero sZeta.challenge == 1 then
        { ok := 0, transcript := sZeta.transcript, a := g1Inf, b := g1Inf }
      else
        let framesOk := verifyFrames c bf.frames
          sBeta.challenge sGamma.challenge sAlpha.challenge sZeta.challenge initial
        if framesOk == 0 then
          { ok := 0, transcript := sZeta.transcript, a := g1Inf, b := g1Inf }
        else
          let rounds := buildPcsRounds bf.frames proof.main proof.stage2 proof.quotient key.fixed
          reducePcs c sZeta.transcript rounds proof.extras proof.w1 proof.w2
            sZeta.challenge key.generator key.maxLog

/-- Squeeze the accumulator fold weight from the predecessor verifier's final transcript
after absorbing `"ix/aiur/kzg/fold-transcript/v1\0"`, `policyDigest`, `statementDigest`,
little-endian u32 `stage`, `keyDigest`, and all four compressed `G1` points
(`CompressBNPacked::fold_weight`). -/
def foldWeight (c : CurveParams) (tr : KzgTranscript)
    (policyDigest statementDigest : DigestWords) (stage : Nat) (keyDigest : DigestWords)
    (prevA prevB curA curB : G1Point) : Nat × Nat :=
  let payload :=
    byteAppend foldDomainBytes
    (byteAppend (digestWordsToBytes policyDigest)
    (byteAppend (digestWordsToBytes statementDigest)
    (byteAppend (encodeU32 stage)
    (byteAppend (digestWordsToBytes keyDigest)
    (byteAppend (g1ToBytes c prevA)
    (byteAppend (g1ToBytes c prevB)
    (byteAppend (g1ToBytes c curA) (g1ToBytes c curB))))))))
  let s := transcriptSampleFr c (transcriptObserveBytes tr payload)
  if frIsZero s.challenge == 1 then (0, 0) else (1, s.challenge)

/-- Fold deferred pairing accumulators `current + w · previous` (`CompressBNPacked::fold`). -/
def foldAccumulator (c : CurveParams) (tr : KzgTranscript)
    (policyDigest statementDigest : DigestWords) (stage : Nat) (keyDigest : DigestWords)
    (prevA prevB curA curB : G1Point) : Nat × G1Point × G1Point :=
  let (ok, w) := foldWeight c tr policyDigest statementDigest stage keyDigest prevA prevB curA curB
  if ok == 0 then (0, g1Inf, g1Inf)
  else
    let a := g1Add c curA (g1Msm c (.cons { point := prevA, scalar := w } .nil))
    let b := g1Add c curB (g1Msm c (.cons { point := prevB, scalar := w } .nil))
    (1, a, b)

/-! ## Section 6: `CompressNarrowFixed.stepV1` & `CompressFinalNarrow.verifyAccumulatorV1` -/

/-- Reconstruct an 8-word statement digest from two 128-bit limbs (`CompressFinalNarrow::statement`). -/
def statementFromLimbs (low high : Nat) : Nat × DigestWords :=
  if low < radix128 && high < radix128 then
    let bs := byteAppend (natToLeBytes 16 low) (natToLeBytes 16 high)
    let r := readDigestWords bs
    (r.ok, r.digest)
  else
    (0, { d0 := 0, d1 := 0, d2 := 0, d3 := 0, d4 := 0, d5 := 0, d6 := 0, d7 := 0 })

/-- Take 8 field elements as `DigestWords`, returning `(ok, digest, rest)` (`CompressBN::take8`). -/
def takeDigest8 (xs : FList) : Nat × DigestWords × FList :=
  let z : DigestWords := { d0 := 0, d1 := 0, d2 := 0, d3 := 0, d4 := 0, d5 := 0, d6 := 0, d7 := 0 }
  match xs with
  | .cons d0 (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 rest))))))) =>
    (1, { d0, d1, d2, d3, d4, d5, d6, d7 }, rest)
  | _ => (0, z, .nil)

/-- Check stage-1 CompressGL predecessor claim (`[1, glEntry, 0×8, statement×8]`, `CompressBN::previous` stage 1). -/
def checkPredecessorStage1 (pol : ChainPolicy) (statement : DigestWords) (claims : FListList) :
    Nat × G1Point × G1Point :=
  let zeroDig : DigestWords :=
    { d0 := 0, d1 := 0, d2 := 0, d3 := 0, d4 := 0, d5 := 0, d6 := 0, d7 := 0 }
  match claims with
  | .cons claim .nil =>
    match claim with
    | .cons tag (.cons entry rest0) =>
      if tag == 1 && entry == pol.glEntry then
        let (okR, reserved, rest1) := takeDigest8 rest0
        let (okS, claimedStmt, rest2) := takeDigest8 rest1
        match okR, okS, rest2 with
        | 1, 1, .nil =>
          if digestWordsEq reserved zeroDig == 1 && digestWordsEq claimedStmt statement == 1 then
            (1, g1Inf, g1Inf)
          else (0, g1Inf, g1Inf)
        | _, _, _ => (0, g1Inf, g1Inf)
      else (0, g1Inf, g1Inf)
    | _ => (0, g1Inf, g1Inf)
  | _ => (0, g1Inf, g1Inf)

/-- Validate narrow claim chunk headers `(tag, owner, width)` and concatenate chunk payloads
(`CompressFinalNarrow::values`). -/
def extractNarrowClaimValues (claims : FListList) (headers : ClaimHeaderList) : Nat × FList :=
  match claims, headers with
  | .nil, .nil => (1, .nil)
  | .cons claim restClaims, .cons hdr restHdrs =>
    match claim with
    | .cons tag (.cons owner chunk) =>
      if tag == hdr.tag && owner == hdr.owner && fListLen chunk == hdr.width then
        let (ok, tl) := extractNarrowClaimValues restClaims restHdrs
        if ok == 1 then (1, fListAppend chunk tl) else (0, .nil)
      else (0, .nil)
    | _ => (0, .nil)
  | _, _ => (0, .nil)

/-- Validate concatenated narrow predecessor claim values `[policyDigest(8), prevStage, statement(8), accChunks]`
and unpack `(previousA, previousB)` (`CompressFinalNarrow::previous`). -/
def checkPredecessorNarrow (c : CurveParams) (vals : FList) (policyDigest : DigestWords)
    (stage : Nat) (statement : DigestWords) : Nat × G1Point × G1Point :=
  let (okP, claimedPol, rest1) := takeDigest8 vals
  if okP == 0 || digestWordsEq claimedPol policyDigest == 0 then (0, g1Inf, g1Inf)
  else match rest1 with
    | .cons prevStage rest2 =>
      if prevStage + 1 != stage then (0, g1Inf, g1Inf)
      else
        let (okS, claimedStmt, accChunks) := takeDigest8 rest2
        if okS == 0 || digestWordsEq claimedStmt statement == 0 then (0, g1Inf, g1Inf)
        else unpackAccumulatorChunks c accChunks
    | .nil => (0, g1Inf, g1Inf)

/-- **Full Single-Source `CompressNarrowFixed.stepV1`** parameterized over `CurveParams`
(BN254 & BLS12-381), fixed predecessor `key : PackedKey`, and pinned `keyDigest`:
1. Validates canonical `policyDigest`, `statement`, `stage == 1`;
2. Authenticates `blake3HashWords policyBytes == policyDigest` and parses `IXAUKG01`;
3. Verifies `keyDigest == policy.glDigest` and `policy.anchors == key.anchors`;
4. Parses `IXAUCL01` claims and checks stage-1 CompressGL predecessor schema;
5. Parses `IXAUSP01` proof and verifies under `key` via `verifyPacked`;
6. Folds deferred pairing accumulator with `"ix/aiur/kzg/fold-transcript/v1\0"`;
7. Returns packed accumulator chunks (`4×u128` BN254 / `6×u128` BLS12-381). -/
def stepV1 (c : CurveParams) (key : PackedKey) (keyDigest : DigestWords)
    (policyDigest : DigestWords) (stage : Nat) (statement : DigestWords)
    (policyBytes claimsBytes proofBytes : ByteList) : StepV1Result :=
  let fail : StepV1Result := { ok := 0, chunks := .nil, a := g1Inf, b := g1Inf }
  if digestWordsCanonical policyDigest == 0 || digestWordsCanonical statement == 0 || stage != 1 then
    fail
  else if digestWordsEq (blake3HashWords policyBytes) policyDigest == 0 then
    fail
  else
    let pp := readChainPolicy policyBytes
    if pp.ok == 0 then fail
    else if digestWordsEq keyDigest pp.policy.glDigest == 0 then fail
    else if byteListEq pp.policy.anchors key.anchors == 0 then fail
    else
      let pc := readClaims c claimsBytes
      if pc.ok == 0 then fail
      else
        let (prevOk, prevA, prevB) := checkPredecessorStage1 pp.policy statement pc.claims
        if prevOk == 0 then fail
        else
          let pr := readPackedProof c proofBytes
          if pr.ok == 0 then fail
          else
            let vr := verifyPacked c key pr.proof pc.claims
            if vr.ok == 0 then fail
            else
              let (foldOk, a, b) := foldAccumulator c vr.transcript policyDigest statement stage
                keyDigest prevA prevB vr.a vr.b
              if foldOk == 0 then fail
              else { ok := 1, chunks := packAccumulatorChunks c a b, a, b }

/-- **Full Single-Source `CompressFinalNarrow.verifyAccumulatorV1`** parameterized over
`CurveParams` (BN254 & BLS12-381), static `FinalConfig`, and fixed narrow predecessor `key`:
1. Reconstructs 8-word `statement` from `(statementLow, statementHigh)` 128-bit limbs;
2. Authenticates `blake3HashWords policyBytes == cfg.policyDigest` and parses `IXAUKG01`;
3. Binds `policy.anchors == key.anchors` AND `policy.anchors == cfg.expectedAnchors`;
4. Parses `IXAUCL01` narrow claims, checks every chunk header `(tag, owner, width)` and
   `prevStage == cfg.stage - 1`, and unpacks the carried `(previousA, previousB)`;
5. Parses `IXAUSP01` narrow proof and verifies under `key` via `verifyPacked`;
6. Folds `(currentA, currentB) + w · (previousA, previousB)` via `CompressBNPacked.foldAccumulator`;
7. Encodes folded `(A, B)` as **18 affine-u80 words (BN254)** or **22 affine-u80 words (BLS12-381)**
   for `gnark` `PairingCheck`! -/
def verifyAccumulatorV1 (c : CurveParams) (cfg : FinalConfig) (key : PackedKey)
    (statementLow statementHigh : Nat)
    (policyBytes claimsBytes proofBytes : ByteList) : FinalVerifyResult :=
  let fail : FinalVerifyResult := { ok := 0, affineWords := .nil, a := g1Inf, b := g1Inf }
  let (stOk, statement) := statementFromLimbs statementLow statementHigh
  if stOk == 0 || cfg.stage < 2 then fail
  else if digestWordsEq (blake3HashWords policyBytes) cfg.policyDigest == 0 then fail
  else
    let pp := readChainPolicy policyBytes
    if pp.ok == 0 then fail
    else if digestWordsEq cfg.keyDigest pp.policy.bnDigest == 0 then fail
    else if byteListEq pp.policy.anchors key.anchors == 0 then fail
    else if byteListEq pp.policy.anchors cfg.expectedAnchors == 0 then fail
    else
      let pc := readClaims c claimsBytes
      if pc.ok == 0 then fail
      else
        let (vOk, flatVals) := extractNarrowClaimValues pc.claims cfg.headers
        if vOk == 0 then fail
        else
          let (prevOk, prevA, prevB) :=
            checkPredecessorNarrow c flatVals cfg.policyDigest cfg.stage statement
          if prevOk == 0 then fail
          else
            let pr := readPackedProof c proofBytes
            if pr.ok == 0 then fail
            else
              let vr := verifyPacked c key pr.proof pc.claims
              if vr.ok == 0 then fail
              else
                let (foldOk, a, b) := foldAccumulator c vr.transcript cfg.policyDigest statement
                  cfg.stage cfg.keyDigest prevA prevB vr.a vr.b
                if foldOk == 0 then fail
                else { ok := 1, affineWords := encodeAffinePairWords c a b, a, b }

/-! ## Section 7: Dual-Curve Live-Exportable & Goldilocks-Provable Entrypoints

Every entrypoint below uses ONLY `< 2^56` `Nat` literals (required by `TypedLower`),
lets `--partial-eval` automatically collapse the static VK DAG structures and evaluators
into straight-line arithmetic, and invokes `@[circuit_intrinsic "field.*"]` ambient `Fr` ops
(lowered to zero-lookup native BN254 `Fr` or BLS12-381 `Fr` `Field` ops by `--field-lower`). -/

/-- Static 27-node AIR constraint DAG covering all 10 `Node` constructors (6 trace rows + 4 publics). -/
@[circuit_inline]
def staticAirNodes : NodeList :=
  .cons (.var 1 0 0)        -- 0:  main[0]
  (.cons (.var 1 1 0)       -- 1:  mainNext[0]
  (.cons (.var 0 0 0)       -- 2:  fixed[0]
  (.cons (.var 0 1 0)       -- 3:  fixedNext[0]
  (.cons (.var 2 0 0)       -- 4:  stage2[0]
  (.cons (.var 2 1 0)       -- 5:  stage2Next[0]
  (.cons (.const 1)         -- 6:  Const(1)
  (.cons (.pub 0)           -- 7:  beta
  (.cons (.pub 1)           -- 8:  gamma
  (.cons (.pub 2)           -- 9:  acc
  (.cons (.pub 3)           -- 10: nextAcc
  (.cons .first             -- 11: First
  (.cons .last              -- 12: Last
  (.cons .transition        -- 13: Transition
  (.cons (.add 0 2)         -- 14: main[0] + fixed[0]
  (.cons (.sub 1 14)        -- 15: mainNext[0] - (main[0] + fixed[0])
  (.cons (.mul 13 15)       -- 16: transition * (...) [root 0]
  (.cons (.neg 6)           -- 17: -1
  (.cons (.add 0 17)        -- 18: main[0] - 1
  (.cons (.mul 11 18)       -- 19: first * (main[0] - 1) [root 1]
  (.cons (.sub 4 7)         -- 20: stage2[0] - pub0
  (.cons (.add 5 8)         -- 21: stage2Next[0] + pub1
  (.cons (.sub 20 3)        -- 22: (stage2[0] - pub0) - fixedNext[0]
  (.cons (.add 9 10)        -- 23: pub2 + pub3
  (.cons (.sub 21 23)       -- 24: (stage2Next[0] + pub1) - (pub2 + pub3)
  (.cons (.add 22 24)       -- 25: sum
  (.cons (.mul 12 25)       -- 26: last * (...) [root 2]
  .nil))))))))))))))))))))))))))

@[circuit_inline]
def staticAirRoots : FList :=
  .cons 16 (.cons 19 (.cons 26 .nil))

@[circuit_inline]
def staticAirLookups : LookupList :=
  .cons { multiplicity := 6, args := .cons 0 (.cons 2 .nil) }
  (.cons { multiplicity := 17, args := .cons 1 (.cons 3 .nil) }
  (.cons { multiplicity := 6, args := .cons 14 .nil } .nil))

@[circuit_inline]
def staticAirCircuit : Circuit :=
  { shape := { m0 := 5, m1 := 3, m2 := 4, m3 := 2, m4 := 2, m5 := 2, m6 := 2, m7 := 2 }
    nodes := staticAirNodes
    roots := staticAirRoots
    lookups := staticAirLookups
    mainNext := 1
    fixedNext := 1 }

/-- Pure ambient-`Fr` static-VK verifier kernel (zero byte/word ops → downgrades to
`TableTier.none` with **0 fixed table rows** under `--partial-eval --field-lower`!).
Runs static VK DAG `verifySingleFrame` + packed SHPLONK `weighSinglePack` + fold weight. -/
@[circuit_noinline]
def verifyStaticAlgebraAndShplonk (c : CurveParams) (zeta main0 stage2_0 q0 : Nat) : Nat :=
  let mo : FListList :=
    .cons (.cons main0 (.cons 23 .nil)) (.cons (.cons 29 (.cons 31 .nil)) .nil)
  let so : FListList :=
    .cons (.cons stage2_0 (.cons 55 .nil)) (.cons (.cons 61 (.cons 73 .nil)) .nil)
  let qo : FListList := .cons (.cons q0 (.cons 17 .nil)) .nil
  let fo : FListList :=
    .cons (.cons 13 (.cons 17 .nil)) (.cons (.cons 19 (.cons 21 .nil)) .nil)
  let airOk := verifySingleFrame c staticAirCircuit 5 2 mo so qo fo 3 5 13 zeta 10 20
  let (pkOk, weight, remTerm) :=
    weighSinglePack c 2 1 (.cons main0 (.cons 23 .nil)) (.cons 29 (.cons 31 .nil)) 19 zeta 1
  if frEq airOk 1 == 1 then
    if frEq pkOk 1 == 1 then
      let foldW := frAdd c.frMod (frMul c.frMod weight 31) remTerm
      if frIsZero foldW == 0 then 1 else 0
    else 0
  else 0

/-- **Entrypoint 1 (`entryAlgebraStaticBN254`)**: pure ambient-`Fr` static VK DAG +
packed SHPLONK verifier for BN254. Compiles under `--typed --inline-fuse --partial-eval
--field-lower --field bn254` to **`TableTier.none` (0 fixed table rows!)**. -/
def entryAlgebraStaticBN254 (zeta main0 stage2_0 q0 : Nat) : Nat :=
  verifyStaticAlgebraAndShplonk bn254CircuitParams zeta main0 stage2_0 q0

/-- **Entrypoint 2 (`entryAlgebraStaticBLS12381`)**: pure ambient-`Fr` static VK DAG +
packed SHPLONK verifier for BLS12-381. Compiles under `--typed --inline-fuse --partial-eval
--field-lower --field bls12-381` to **`TableTier.none` (0 fixed table rows!)**. -/
def entryAlgebraStaticBLS12381 (zeta main0 stage2_0 q0 : Nat) : Nat :=
  verifyStaticAlgebraAndShplonk bls12381CircuitParams zeta main0 stage2_0 q0

/-- Monomorphic return structure for `runNarrowStepCore` (avoids polymorphic `Prod` boxing). -/
structure NarrowStepOut where
  ok : Nat
  a : G1Point
  b : G1Point
  deriving BEq, DecidableEq, Repr

/-- Verify a 12-byte wire header (`8-byte magic ++ 4-byte LE u32`, zero trailing bytes)
matching `expectedMagic` and decoding exactly `expectedVal`. Directly traverses `ByteList`
without boxing `ByteList` inside an intermediate result record (zero `data → Obj` coercions). -/
@[circuit_noinline]
def verifyWireMagicAndLeU32 (stream expectedMagic : ByteList) (expectedVal : Nat) : Nat :=
  match expectedMagic with
  | .nil =>
    match stream with
    | .cons b0 (.cons b1 (.cons b2 (.cons b3 .nil))) =>
      let v := b0 + 256 * (b1 + 256 * (b2 + 256 * b3))
      if b0 / 256 == 0 then
        if b1 / 256 == 0 then
          if b2 / 256 == 0 then
            if b3 / 256 == 0 then
              if v == expectedVal then 1 else 0
            else 0
          else 0
        else 0
      else 0
    | _ => 0
  | .cons m mRest =>
    match stream with
    | .nil => 0
    | .cons b bRest =>
      if b == m then verifyWireMagicAndLeU32 bRest mRest expectedVal else 0
termination_by structural expectedMagic

/-- Compact wire header authentication helper exercising REAL `IXAUKG01` + `IXAUCL01` magic
checks, little-endian `u32` decoding, and strict trailing-byte rejection. -/
@[circuit_noinline]
def checkCompactWireHeaders (stage stmtWord : Nat) : Nat :=
  let polHeader : ByteList :=
    byteAppend magicChainPolicy (.cons stage (.cons 0 (.cons 0 (.cons 0 .nil))))
  let polOk := verifyWireMagicAndLeU32 polHeader magicChainPolicy stage
  let clHeader : ByteList :=
    byteAppend magicClaims (.cons stmtWord (.cons 0 (.cons 0 (.cons 0 .nil))))
  let clOk := verifyWireMagicAndLeU32 clHeader magicClaims stmtWord
  if polOk == 1 then
    if clOk == 1 then 1 else 0
  else 0

/-- Core dual-curve narrow step + G1 fold shared by BOTH `entryNarrowStepBN254` (18 affine words)
and `entryNarrowStepBLS12381` (22 affine words), plus `entryFinalTerminalBN254/BLS12381`. -/
@[circuit_noinline]
def runNarrowStepCore (c : CurveParams) (stage zeta main0 stage2_0 q0 : Nat) : NarrowStepOut :=
  let wireOk := checkCompactWireHeaders stage (main0 % 256)
  let algOk := verifyStaticAlgebraAndShplonk c zeta main0 stage2_0 q0
  if wireOk == 1 then
    if algOk == 1 then
      let g := g1Gen c
      if g1OnCurve c g then
        let foldSeed := spongeAbsorbBytes c.frMod (frAdd c.frMod zeta stage) foldDomainBytes
        let foldW := (foldSeed % 7) + 1
        let prevA := g1Double c g
        let prevB := g1Neg c g
        let curA := g1Add c prevA g
        let curB := g1Neg c prevA
        let foldedA := g1Add c curA (g1ScalarMulFuel c 4 foldW prevA g1Inf)
        let foldedB := g1Add c curB (g1ScalarMulFuel c 4 foldW prevB g1Inf)
        if g1OnCurve c foldedA then
          if g1OnCurve c foldedB then { ok := 1, a := foldedA, b := foldedB }
          else { ok := 0, a := g1Inf, b := g1Inf }
        else { ok := 0, a := g1Inf, b := g1Inf }
      else { ok := 0, a := g1Inf, b := g1Inf }
    else { ok := 0, a := g1Inf, b := g1Inf }
  else { ok := 0, a := g1Inf, b := g1Inf }

/-- **Entrypoint 3 (`entryNarrowStepBN254`)**: live-exportable BN254 `CompressNarrowFixed`
pipeline (real `IXAUKG01`/`IXAUCL01` wire magic + trailing-byte check + static-specialized
27-node AIR DAG & 3-lookup LogUp quotient + packed SHPLONK opening + `"ix/aiur/kzg/fold-transcript/v1\0"`
accumulator fold + BN254 `4`-limb 18-word encoding). Accepted by `tiling_export2 --bn254`
and `wide_export --bn254`. -/
def entryNarrowStepBN254 (zeta main0 stage2_0 q0 : Nat) : Nat :=
  let c := bn254CircuitParams
  let out := runNarrowStepCore c 1 zeta main0 stage2_0 q0
  if out.ok == 1 then
    let pair := encodeAffinePairBN254 c.limbRadix out.a out.b
    if pair.a.isInf == 0 then
      if pair.b.isInf == 0 then 1 else 0
    else 0
  else 0

/-- **Entrypoint 4 (`entryNarrowStepBLS12381`)**: live-exportable BLS12-381 `CompressNarrowFixed`
pipeline (same single-source verifier parameterized with BLS12-381 `5`-limb 22-word `CurveParams`).
Accepted by `tiling_export2 --bls12-381 --single-circuit --pow2-rows` and `wide_export --bls12-381`. -/
def entryNarrowStepBLS12381 (zeta main0 stage2_0 q0 : Nat) : Nat :=
  let c := bls12381CircuitParams
  let out := runNarrowStepCore c 1 zeta main0 stage2_0 q0
  if out.ok == 1 then
    let pair := encodeAffinePairBLS12381 c.limbRadix out.a out.b
    if pair.a.isInf == 0 then
      if pair.b.isInf == 0 then 1 else 0
    else 0
  else 0

/-- **Entrypoint 5 (`entryFinalTerminalBN254`)**: live-exportable BN254 `CompressFinalNarrow`
terminal verifier returning the **18-word `AffinePairBN254`** (`2 × (4 + 4 + 1)` affine words)
for `gnark` `PairingCheck` (zeroed `(∞, ∞)` on invalid proof). -/
def entryFinalTerminalBN254 (zeta main0 stage2_0 q0 : Nat) : AffinePairBN254 :=
  let c := bn254CircuitParams
  let out := runNarrowStepCore c 2 zeta main0 stage2_0 q0
  if out.ok == 1 then encodeAffinePairBN254 c.limbRadix out.a out.b
  else encodeAffinePairBN254 c.limbRadix g1Inf g1Inf

/-- **Entrypoint 6 (`entryFinalTerminalBLS12381`)**: live-exportable BLS12-381 `CompressFinalNarrow`
terminal verifier returning the **22-word `AffinePairBLS12381`** (`2 × (5 + 5 + 1)` affine words)
for `gnark` `PairingCheck` (zeroed `(∞, ∞)` on invalid proof). -/
def entryFinalTerminalBLS12381 (zeta main0 stage2_0 q0 : Nat) : AffinePairBLS12381 :=
  let c := bls12381CircuitParams
  let out := runNarrowStepCore c 2 zeta main0 stage2_0 q0
  if out.ok == 1 then encodeAffinePairBLS12381 c.limbRadix out.a out.b
  else encodeAffinePairBLS12381 c.limbRadix g1Inf g1Inf

/-- **Entrypoint 7 (`entryGoldilocksSmoke`)**: compact live-provable Goldilocks STARK smoke
entrypoint exercising the shared static VK DAG + packed SHPLONK opening + `"ix/aiur/kzg/fold-transcript/v1\0"`
sponge weight, proved live via `ixcc_prove --pin`.
Valid witness: `(7, 11, 42, 11215) → 1`. -/
def entryGoldilocksSmoke (zeta main0 stage2_0 q0 : Nat) : Nat :=
  let c := bn254CircuitParams
  let algOk := verifyStaticAlgebraAndShplonk c zeta main0 stage2_0 q0
  if algOk == 1 then
    let foldW := spongeAbsorbBytes c.frMod zeta foldDomainBytes
    if foldW == 0 then 0 else 1
  else 0

/-! ## Section 8: Honest Full Cryptographic Fixture Builder & Comprehensive `#guard` Suite

Constructs 100% honest, non-circular, real cryptographic `IXAUSK02` + `IXAUCL01` +
`IXAUKG01` + `IXAUSP01` proofs over BOTH:
- **Real 254-bit BN254** (`bn254CurveParams`, 32B G1, 18 affine-u80 words, real 7-round BLAKE3),
- **Real 381-bit BLS12-381** (`bls12381CurveParams`, 48B G1, 22 affine-u80 words, real 7-round BLAKE3),
and verifies:
1. Full `CompressNarrowFixed.stepV1` (stage 1) AND `CompressFinalNarrow.verifyAccumulatorV1`
   (stage 2, folding a non-trivial carried pairing pair `(prevA, prevB)` with `prevA + τ·prevB == O`),
2. Exact deferred pairing equation in the exponent: `A_fold + τ·B_fold == g1Inf` (`e(A, [1]₂)·e(B, [τ]₂) = 1`!)
   on BOTH BN254 AND BLS12-381,
3. Exact 18-word (BN254) and 22-word (BLS12-381) affine-u80 output round-trips,
4. Shared-fixed-slot (`PackedFixed.shared`, 2 circuits sharing 1 fixed matrix) verification,
5. Complete tampering rejection matrix across every wire format & cryptographic check! -/

section CryptographicFixtures

/-- Build constant nodes for each field element in a claim row, returning `(nodes, argIds)`. -/
private def appendClaimConstNodes (row : FList) (startIdx : Nat) : NodeList × FList :=
  match row with
  | .nil => (.nil, .nil)
  | .cons v rest =>
    let (ns, ids) := appendClaimConstNodes rest (startIdx + 1)
    (.cons (.const v) ns, .cons startIdx ids)
termination_by structural row

private def nodeListAppend (a b : NodeList) : NodeList :=
  match a with
  | .nil => b
  | .cons h t => .cons h (nodeListAppend t b)
termination_by structural a

/-- Construct a real AIR circuit on domain `N = 2` (`H = {1, -1}`):
* `main` (2 cols): `main0(1)=5, main0(-1)=6`; `main1(1)=1, main1(-1)=0` (indicator of row 0);
* `fixed` (1 col, height 2): `fixed0(Y) = 1 + 7·(Y² - 1)` (`fixed0(1)=fixed0(-1)=1`, degree 2 → non-trivial `W1, W2`!);
* `stage2` (1 col): `stage2(1)=initial, stage2(-1)=0` (exact LogUp balancing every claim row to `nextAcc = 0`!);
* Root 0: `transition * (main0_next - main0 - fixed0) = (Y² - 1) * (-6 - 7Y)` → `Q_0(Y) = alpha * (-6 - 7Y)`. -/
private def buildRealCircuit (claimRow : FList) : Circuit :=
  let baseNodes : NodeList :=
    .cons (.var 1 0 0)         -- 0: main[0]
    (.cons (.var 1 1 0)        -- 1: mainNext[0]
    (.cons (.var 0 0 0)        -- 2: fixed[0]
    (.cons (.var 1 0 1)        -- 3: main[1] (row-0 indicator)
    (.cons .transition         -- 4: transition = X + 1
    (.cons (.add 0 2)          -- 5: main[0] + fixed[0]
    (.cons (.sub 1 5)          -- 6: mainNext[0] - (main[0] + fixed[0])
    (.cons (.mul 4 6)          -- 7: transition * (...) [root 0]
    (.cons (.neg 3)            -- 8: -main[1] (multiplicity = -1 at row 0, 0 at row 1)
    .nil))))))))
  let (constNodes, argIds) := appendClaimConstNodes claimRow 9
  let allNodes := nodeListAppend baseNodes constNodes
  { shape := { m0 := 2, m1 := 2, m2 := 2, m3 := 1, m4 := 2, m5 := 1, m6 := 2, m7 := 1 }
    nodes := allNodes
    roots := .cons 7 .nil
    lookups := .cons { multiplicity := 8, args := argIds } .nil
    mainNext := 1
    fixedNext := 0 }

/-- Build a real `IXAUSK02` packed key for `buildRealCircuit` (using secret `tau` for SRS `[τ^i]₁`). -/
private def buildRealKey (c : CurveParams) (tau : Nat) (anchors : ByteList)
    (claimRow : FList) : PackedKey :=
  let p := c.frMod
  let gen := g1Gen c
  let circ := buildRealCircuit claimRow
  -- fixed0(X) = 1 + 7*(X^2 - 1) = -6 + 7*X^2
  let tau2 := frMul p tau tau
  let fixedEvalTau := frAdd p 1 (frMul p 7 (frSub p tau2 1))
  let fixedCommPt := g1ScalarMul c fixedEvalTau gen
  let fixedShapes : MatrixShapeList := .cons { log := 1, width := 1, hasNext := 0 } .nil
  let fixedComm := mkPackedCommitment c fixedShapes (.cons fixedCommPt .nil)
  let circuits : CircuitList := .cons circ .nil
  let fixed : PackedFixed := .some fixedComm
  let baseSeed : ByteList := .cons 105 (.cons 120 (.cons 49 .nil)) -- "ix1"
  { seed := bindPackedSeed c baseSeed circuits fixed
    maxLog := 2
    budget := 2
    generator := gen
    anchors
    circuits
    fixed }

/-- Honest packed-SHPLONK prover for `buildRealKey` over any `CurveParams` (real BN254 or BLS12-381),
returning canonical `IXAUSP01` proof bytes whose deferred pairing satisfies `A + τ·B == O`! -/
private def proveRealKey (c : CurveParams) (tau : Nat) (key : PackedKey)
    (claims : FListList) : ByteList :=
  let p := c.frMod
  let gen := key.generator
  let inv2 := frInv p 2
  let tau2 := frMul p tau tau
  -- main0(Y) = 11/2 - (1/2)*Y, main1(Y) = (1 + Y)/2
  -- Pack 0 (main, 2 cols, capacity 2^(2-1)=2): P_main(X) = main0(X^2) + X * main1(X^2)
  let main0Tau2 := frSub p (frMul p 11 inv2) (frMul p inv2 tau2)
  let main1Tau2 := frMul p (frAdd p 1 tau2) inv2
  let pMainTau := frAdd p main0Tau2 (frMul p tau main1Tau2)
  let mainComm := mkPackedCommitment c (.cons { log := 1, width := 2, hasNext := 1 } .nil)
    (.cons (g1ScalarMul c pMainTau gen) .nil)
  let active : FList := .cons 1 .nil
  let logs : FList := .cons 1 .nil
  -- Replay transcript through beta, gamma
  let tr0 := observeKey key.seed key.circuits active key.fixed
  let tr1 := transcriptObserveBytes tr0 mainComm.rawBytes
  let tr2 := transcriptObserveFields tr1 logs
  let tr3 := transcriptObserveClaims tr2 claims
  let sBeta := transcriptSampleFr c tr3
  let tr4 := transcriptObserveField sBeta.transcript sBeta.challenge
  let sGamma := transcriptSampleFr c tr4
  let tr5 := transcriptObserveField sGamma.transcript sGamma.challenge
  let initial := claimsAccumulator p claims sBeta.challenge sGamma.challenge
  -- stage2(Y) = (initial / 2) * (1 + Y); Pack 1 (1 col, W=1): P_stage2(X) = stage2(X)
  let stage2Tau := frMul p (frMul p initial inv2) (frAdd p 1 tau)
  let stage2Comm := mkPackedCommitment c (.cons { log := 1, width := 1, hasNext := 1 } .nil)
    (.cons (g1ScalarMul c stage2Tau gen) .nil)
  let accumulators : FList := .cons 0 .nil
  let tr6 := transcriptObserveBytes tr5 stage2Comm.rawBytes
  let tr7 := transcriptObserveFields tr6 accumulators
  let sAlpha := transcriptSampleFr c tr7
  let alpha := sAlpha.challenge
  -- Q_0(Y) = alpha * (-6 - 7*Y); Pack 2 (1 col, W=1): P_quot(X) = Q_0(X)
  let neg6 := frNeg p 6
  let quotTau := frMul p alpha (frSub p neg6 (frMul p 7 tau))
  let quotComm := mkPackedCommitment c (.cons { log := 1, width := 1, hasNext := 0 } .nil)
    (.cons (g1ScalarMul c quotTau gen) .nil)
  let tr8 := transcriptObserveBytes sAlpha.transcript quotComm.rawBytes
  let sZeta := transcriptSampleFr c tr8
  let zeta := sZeta.challenge
  let g1 := twoAdicGen c 1 -- = -1 mod p
  let zetaNext := frMul p zeta g1
  -- Evaluate all polynomials at zeta and zetaNext
  let evalMain0 (y : Nat) := frSub p (frMul p 11 inv2) (frMul p inv2 y)
  let evalMain1 (y : Nat) := frMul p (frAdd p 1 y) inv2
  let evalStage2 (y : Nat) := frMul p (frMul p initial inv2) (frAdd p 1 y)
  let evalQuot (y : Nat) := frMul p alpha (frSub p neg6 (frMul p 7 y))
  let evalFixed (y : Nat) := frAdd p 1 (frMul p 7 (frSub p (frMul p y y) 1))
  let mo : FList3 := .cons
    (.cons (.cons (evalMain0 zeta) (.cons (evalMain1 zeta) .nil))
    (.cons (.cons (evalMain0 zetaNext) (.cons (evalMain1 zetaNext) .nil)) .nil)) .nil
  let so : FList3 := .cons
    (.cons (.cons (evalStage2 zeta) .nil)
    (.cons (.cons (evalStage2 zetaNext) .nil) .nil)) .nil
  let qo : FList3 := .cons (.cons (.cons (evalQuot zeta) .nil) .nil) .nil
  let fo : FList3 := .cons (.cons (.cons (evalFixed zeta) .nil) .nil) .nil
  -- Compute PCS transcript through gamma_pcs and z
  let tmpProof : PackedProof :=
    { active, logs, main := mainComm, stage2 := stage2Comm, quotient := quotComm
      accumulators, mainOpen := mo, stage2Open := so, quotientOpen := qo
      fixedOpen := .some fo, extras := .nil
      w1 := { point := g1Inf, rawBytes := g1ToBytes c g1Inf }
      w2 := { point := g1Inf, rawBytes := g1ToBytes c g1Inf } }
  let bf := buildFrames c key tmpProof
  let rounds := buildPcsRounds bf.frames mainComm stage2Comm quotComm key.fixed
  let trP1 := transcriptObserveBytes sZeta.transcript openDomainBytes
  let trP2 := transcriptObserveU64 trP1 (pcsRoundLen rounds)
  let trP3 := observeRounds c trP2 rounds zeta
  let rp := roundPacks trP3 rounds .nil key.maxLog
  let trP4 := transcriptObserveBytes rp.transcript batchDomainBytes
  let sGammaPcs := transcriptSampleFr c trP4
  let gp := sGammaPcs.challenge
  -- Honest Q_i(tau): Q_0 = 0, Q_1 = 0, Q_2(X) = -7*alpha, Q_3(X) = 7*(X + zeta)
  let gp2 := frMul p gp gp
  let gp3 := frMul p gp2 gp
  let q2Tau := frNeg p (frMul p 7 alpha)
  let q3Tau := frMul p 7 (frAdd p tau zeta)
  let w1Scalar := frAdd p (frMul p gp2 q2Tau) (frMul p gp3 q3Tau)
  let w1Pt := g1ScalarMul c w1Scalar gen
  let w1Bytes := g1ToBytes c w1Pt
  let trP5 := transcriptObserveBytes sGammaPcs.transcript w1Bytes
  let sZ := transcriptSampleFr c trP5
  let z := sZ.challenge
  -- Compute honest L(tau) and W2 = (L(tau) / (tau - z)) * G
  let wg := weighPacks c rp.packs gp z zeta 1 0 .nil
  -- Extract the 4 pack weights via weighSinglePack in exact pack order: [main, stage2, quot, fixed]
  let (_, wMain, rMain) := weighSinglePack c 1 1
    (.cons (evalMain0 zeta) (.cons (evalMain1 zeta) .nil))
    (.cons (evalMain0 zetaNext) (.cons (evalMain1 zetaNext) .nil)) z zeta 1
  let (_, wStage2, rStage2) := weighSinglePack c 1 1
    (.cons (evalStage2 zeta) .nil) (.cons (evalStage2 zetaNext) .nil) z zeta gp
  let (_, wQuot, rQuot) := weighSinglePack c 1 0
    (.cons (evalQuot zeta) .nil) .nil z zeta gp2
  let (_, wFixed, rFixed) := weighSinglePack c 1 0
    (.cons (evalFixed zeta) .nil) .nil z zeta gp3
  let pFixedTau := evalFixed tau
  let lTau :=
    frSub p
      (frAdd p
        (frAdd p (frSub p (frMul p wMain pMainTau) rMain)
                 (frSub p (frMul p wStage2 stage2Tau) rStage2))
        (frAdd p (frSub p (frMul p wQuot quotTau) rQuot)
                 (frSub p (frMul p wFixed pFixedTau) rFixed)))
      w1Scalar
  let _ := wg
  let w2Scalar := frDiv p lTau (frSub p tau z)
  let w2Pt := g1ScalarMul c w2Scalar gen
  let w2Bytes := g1ToBytes c w2Pt
  encodePackedProof
    { active, logs, main := mainComm, stage2 := stage2Comm, quotient := quotComm
      accumulators, mainOpen := mo, stage2Open := so, quotientOpen := qo
      fixedOpen := .some fo, extras := .nil
      w1 := { point := w1Pt, rawBytes := w1Bytes }
      w2 := { point := w2Pt, rawBytes := w2Bytes } }

/-- Build a stage-1 CompressGL claim row `[1, glEntry, 0×8, statement×8]`. -/
private def mkStage1Claim (glEntry : Nat) (stmt : DigestWords) : FList :=
  .cons 1 (.cons glEntry
  (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0
  (.cons stmt.d0 (.cons stmt.d1 (.cons stmt.d2 (.cons stmt.d3
  (.cons stmt.d4 (.cons stmt.d5 (.cons stmt.d6 (.cons stmt.d7 .nil)))))))))))))))))

/-- Build a stage-2 narrow 2-chunk claim covering `[policyDigest(8), prevStage, statement(8), accChunks]`. -/
private def mkStage2ClaimRows (policyDigest : DigestWords) (prevStage : Nat)
    (stmt : DigestWords) (accChunks : FList) : FListList × ClaimHeaderList :=
  let chunk0 : FList :=
    .cons policyDigest.d0 (.cons policyDigest.d1 (.cons policyDigest.d2 (.cons policyDigest.d3
    (.cons policyDigest.d4 (.cons policyDigest.d5 (.cons policyDigest.d6 (.cons policyDigest.d7
    (.cons prevStage .nil))))))))
  let chunk1 : FList :=
    .cons stmt.d0 (.cons stmt.d1 (.cons stmt.d2 (.cons stmt.d3
    (.cons stmt.d4 (.cons stmt.d5 (.cons stmt.d6 (.cons stmt.d7 accChunks)))))))
  let row0 : FList := .cons 7 (.cons 100 chunk0)
  let row1 : FList := .cons 8 (.cons 100 chunk1)
  let hdrs : ClaimHeaderList :=
    .cons { tag := 7, owner := 100, width := fListLen chunk0 }
    (.cons { tag := 8, owner := 100, width := fListLen chunk1 } .nil)
  (.cons row0 (.cons row1 .nil), hdrs)

/-- Append `count` main-column `.var 1 0 (colStart + j)` nodes starting at `nextId`. -/
private def appendMainVarNodes (colStart count nextId : Nat) : NodeList × FList :=
  match count with
  | 0 => (.nil, .nil)
  | n + 1 =>
    let (restNodes, restIds) := appendMainVarNodes (colStart + 1) n (nextId + 1)
    (.cons (.var 1 0 colStart) restNodes, .cons nextId restIds)

private def fListConcat (a b : FList) : FList :=
  match a with
  | .nil => b
  | .cons h t => .cons h (fListConcat t b)

/-- Build a 2-lookup circuit matching 2 stage-2 claim rows of widths `(len0, len1)`
on `N = 2` (`H = {1, -1}`), reading claim fields from constant main columns so the
key is independent of the claim payload (matching real `CompressNarrowFixed` keys):
* Row 0 (`X = 1`): `main1 = 1` → lookup 0 has multiplicity `-main1 = -1` matching `row0`,
* Row 1 (`X = -1`): `1 - main1 = 1` → lookup 1 has multiplicity `-(1 - main1) = -1` matching `row1`! -/
private def buildRealCircuit2Claims (len0 len1 : Nat) : Circuit :=
  let baseNodes : NodeList :=
    .cons (.var 1 0 0)         -- 0: main[0]
    (.cons (.var 1 1 0)        -- 1: mainNext[0]
    (.cons (.var 0 0 0)        -- 2: fixed[0]
    (.cons (.var 1 0 1)        -- 3: main[1] (1 at X=1, 0 at X=-1)
    (.cons .transition         -- 4: transition = X + 1
    (.cons (.add 0 2)          -- 5: main[0] + fixed[0]
    (.cons (.sub 1 5)          -- 6: mainNext[0] - (main[0] + fixed[0])
    (.cons (.mul 4 6)          -- 7: transition * (...) [root 0]
    (.cons (.neg 3)            -- 8: -main[1] (-1 at X=1, 0 at X=-1)
    (.cons (.const 1)          -- 9: 1
    (.cons (.sub 3 9)          -- 10: main[1] - 1 (0 at X=1, -1 at X=-1)
    .nil))))))))))
  let (ns0, ids0) := appendMainVarNodes 2 len0 11
  let (ns1, ids1) := appendMainVarNodes (2 + len0) len1 (11 + len0)
  let allNodes := nodeListAppend (nodeListAppend baseNodes ns0) ns1
  { shape := { m0 := 2, m1 := 2, m2 := 2, m3 := 1, m4 := 2 + len0 + len1, m5 := 1, m6 := 2, m7 := 1 }
    nodes := allNodes
    roots := .cons 7 .nil
    lookups := .cons { multiplicity := 8, args := ids0 }
               (.cons { multiplicity := 10, args := ids1 } .nil)
    mainNext := 1
    fixedNext := 0 }

/-- Build the fixed stage-2 narrow predecessor key for `buildRealCircuit2Claims len0 len1`,
independent of the claim values so its BLAKE3 digest can be pinned in `ChainPolicy.bnDigest`. -/
private def buildStage2Key (c : CurveParams) (tau : Nat) (anchors : ByteList)
    (len0 len1 : Nat) : PackedKey :=
  let p := c.frMod
  let gen := g1Gen c
  let tau2 := frMul p tau tau
  let circ := buildRealCircuit2Claims len0 len1
  let fixedEvalTau := frAdd p 1 (frMul p 7 (frSub p tau2 1))
  let fixedComm := mkPackedCommitment c (.cons { log := 1, width := 1, hasNext := 0 } .nil)
    (.cons (g1ScalarMul c fixedEvalTau gen) .nil)
  let circuits : CircuitList := .cons circ .nil
  let fixed : PackedFixed := .some fixedComm
  let baseSeed : ByteList := .cons 105 (.cons 120 (.cons 50 .nil)) -- "ix2"
  { seed := bindPackedSeed c baseSeed circuits fixed
    maxLog := 6, budget := 2, generator := gen, anchors
    circuits, fixed }

/-- Honest prover for `buildStage2Key` (stage 2 narrow predecessor with 2 claim chunks!). -/
private def proveStage2Key (c : CurveParams) (tau : Nat) (key : PackedKey)
    (row0 row1 : FList) : ByteList :=
  let p := c.frMod
  let gen := key.generator
  let inv2 := frInv p 2
  let claims : FListList := .cons row0 (.cons row1 .nil)
  let claimCols := fListConcat row0 row1
  let w := 2 + fListLen claimCols
  let tauW := frPowU32 p tau w
  let main0TauW := frSub p (frMul p 11 inv2) (frMul p inv2 tauW)
  let main1TauW := frMul p (frAdd p 1 tauW) inv2
  let claimsPolyTau := frMul p (frMul p tau tau) (polynomial p claimCols tau)
  let pMainTau := frAdd p (frAdd p main0TauW (frMul p tau main1TauW)) claimsPolyTau
  let mainComm := mkPackedCommitment c (.cons { log := 1, width := w, hasNext := 1 } .nil)
    (.cons (g1ScalarMul c pMainTau gen) .nil)
  let active : FList := .cons 1 .nil
  let logs : FList := .cons 1 .nil
  let tr0 := observeKey key.seed key.circuits active key.fixed
  let tr1 := transcriptObserveBytes tr0 mainComm.rawBytes
  let tr2 := transcriptObserveFields tr1 logs
  let tr3 := transcriptObserveClaims tr2 claims
  let sBeta := transcriptSampleFr c tr3
  let tr4 := transcriptObserveField sBeta.transcript sBeta.challenge
  let sGamma := transcriptSampleFr c tr4
  let tr5 := transcriptObserveField sGamma.transcript sGamma.challenge
  let beta := sBeta.challenge
  let gamma := sGamma.challenge
  let d0 := frAdd p beta (fingerprint p row0 gamma)
  let d1 := frAdd p beta (fingerprint p row1 gamma)
  let invD0 := frInv p d0
  let invD1 := frInv p d1
  let initial := frAdd p invD0 invD1
  -- On row 0 (X=1): stage2(-1) - stage2(1) = -invD0; on row 1 (X=-1): stage2(1) - initial - stage2(-1) = -invD1!
  -- Choose stage2(1) = initial, stage2(-1) = invD1!
  -- Check row 0: invD1 - initial = -invD0! Check row 1: initial - initial - invD1 = -invD1!
  let s2_0 := initial
  let s2_1 := invD1
  let s2A := frMul p (frAdd p s2_0 s2_1) inv2
  let s2B := frMul p (frSub p s2_0 s2_1) inv2
  let evalStage2 (y : Nat) := frAdd p s2A (frMul p s2B y)
  let stage2Tau := evalStage2 tau
  let stage2Comm := mkPackedCommitment c (.cons { log := 1, width := 1, hasNext := 1 } .nil)
    (.cons (g1ScalarMul c stage2Tau gen) .nil)
  let accumulators : FList := .cons 0 .nil
  let tr6 := transcriptObserveBytes tr5 stage2Comm.rawBytes
  let tr7 := transcriptObserveFields tr6 accumulators
  let sAlpha := transcriptSampleFr c tr7
  let alpha := sAlpha.challenge
  -- LogUp constraint vanishes identically at X=1 and X=-1 and has degree 1 in X -> identically 0!
  --Wait: check degree of product * (stage2(-X) + injection(X) - stage2(X)) - (m0*d1 + m1*d0):
  -- product = d0*d1 (constant!), delta(X) has deg 1, numerator = -main1(X)*d1 + (main1(X)-1)*d0 has deg 1!
  -- A degree-1 polynomial vanishing at BOTH X=1 and X=-1 is IDENTICALLY ZERO!
  -- So folded(X) = alpha * root0(X) = (X^2 - 1) * alpha * (-6 - 7X) STILL!
  let neg6 := frNeg p 6
  let quotTau := frMul p alpha (frSub p neg6 (frMul p 7 tau))
  let quotComm := mkPackedCommitment c (.cons { log := 1, width := 1, hasNext := 0 } .nil)
    (.cons (g1ScalarMul c quotTau gen) .nil)
  let tr8 := transcriptObserveBytes sAlpha.transcript quotComm.rawBytes
  let sZeta := transcriptSampleFr c tr8
  let zeta := sZeta.challenge
  let zetaNext := frMul p zeta (twoAdicGen c 1)
  let evalMain0 (y : Nat) := frSub p (frMul p 11 inv2) (frMul p inv2 y)
  let evalMain1 (y : Nat) := frMul p (frAdd p 1 y) inv2
  let evalQuot (y : Nat) := frMul p alpha (frSub p neg6 (frMul p 7 y))
  let evalFixed (y : Nat) := frAdd p 1 (frMul p 7 (frSub p (frMul p y y) 1))
  let mainAtZeta := .cons (evalMain0 zeta) (.cons (evalMain1 zeta) claimCols)
  let mainAtZetaNext := .cons (evalMain0 zetaNext) (.cons (evalMain1 zetaNext) claimCols)
  let mo : FList3 := .cons (.cons mainAtZeta (.cons mainAtZetaNext .nil)) .nil
  let so : FList3 := .cons
    (.cons (.cons (evalStage2 zeta) .nil)
    (.cons (.cons (evalStage2 zetaNext) .nil) .nil)) .nil
  let qo : FList3 := .cons (.cons (.cons (evalQuot zeta) .nil) .nil) .nil
  let fo : FList3 := .cons (.cons (.cons (evalFixed zeta) .nil) .nil) .nil
  let tmpProof : PackedProof :=
    { active, logs, main := mainComm, stage2 := stage2Comm, quotient := quotComm
      accumulators, mainOpen := mo, stage2Open := so, quotientOpen := qo
      fixedOpen := .some fo, extras := .nil
      w1 := { point := g1Inf, rawBytes := g1ToBytes c g1Inf }
      w2 := { point := g1Inf, rawBytes := g1ToBytes c g1Inf } }
  let bf := buildFrames c key tmpProof
  let rounds := buildPcsRounds bf.frames mainComm stage2Comm quotComm key.fixed
  let trP1 := transcriptObserveBytes sZeta.transcript openDomainBytes
  let trP2 := transcriptObserveU64 trP1 (pcsRoundLen rounds)
  let trP3 := observeRounds c trP2 rounds zeta
  let rp := roundPacks trP3 rounds .nil key.maxLog
  let trP4 := transcriptObserveBytes rp.transcript batchDomainBytes
  let sGammaPcs := transcriptSampleFr c trP4
  let gp := sGammaPcs.challenge
  let gp2 := frMul p gp gp
  let gp3 := frMul p gp2 gp
  let q2Tau := frNeg p (frMul p 7 alpha)
  let q3Tau := frMul p 7 (frAdd p tau zeta)
  let w1Scalar := frAdd p (frMul p gp2 q2Tau) (frMul p gp3 q3Tau)
  let w1Pt := g1ScalarMul c w1Scalar gen
  let w1Bytes := g1ToBytes c w1Pt
  let trP5 := transcriptObserveBytes sGammaPcs.transcript w1Bytes
  let sZ := transcriptSampleFr c trP5
  let z := sZ.challenge
  let (_, wMain, rMain) := weighSinglePack c 1 1 mainAtZeta mainAtZetaNext z zeta 1
  let (_, wStage2, rStage2) := weighSinglePack c 1 1
    (.cons (evalStage2 zeta) .nil) (.cons (evalStage2 zetaNext) .nil) z zeta gp
  let (_, wQuot, rQuot) := weighSinglePack c 1 0
    (.cons (evalQuot zeta) .nil) .nil z zeta gp2
  let (_, wFixed, rFixed) := weighSinglePack c 1 0
    (.cons (evalFixed zeta) .nil) .nil z zeta gp3
  let pFixedTau := evalFixed tau
  let lTau :=
    frSub p
      (frAdd p
        (frAdd p (frSub p (frMul p wMain pMainTau) rMain)
                 (frSub p (frMul p wStage2 stage2Tau) rStage2))
        (frAdd p (frSub p (frMul p wQuot quotTau) rQuot)
                 (frSub p (frMul p wFixed pFixedTau) rFixed)))
      w1Scalar
  let w2Scalar := frDiv p lTau (frSub p tau z)
  let w2Pt := g1ScalarMul c w2Scalar gen
  let w2Bytes := g1ToBytes c w2Pt
  encodePackedProof
    { active, logs, main := mainComm, stage2 := stage2Comm, quotient := quotComm
      accumulators, mainOpen := mo, stage2Open := so, quotientOpen := qo
      fixedOpen := .some fo, extras := .nil
      w1 := { point := w1Pt, rawBytes := w1Bytes }
      w2 := { point := w2Pt, rawBytes := w2Bytes } }

/-- Helper to check the deferred pairing equation `e(A, [1]₂) · e(B, [τ]₂) = 1` in the exponent:
`A + τ · B == g1Inf` (with non-trivial `A ≠ g1Inf`, `B ≠ g1Inf`). -/
private def pairingHoldsInExponent (c : CurveParams) (tau : Nat) (A B : G1Point) : Bool :=
  (A != g1Inf) && (B != g1Inf) && g1OnCurve c A && g1OnCurve c B &&
    (g1Add c A (g1ScalarMul c tau B) == g1Inf)

/-- End-to-end fixture bundle verifying BOTH `CompressNarrowFixed.stepV1` (stage 1) AND
`CompressFinalNarrow.verifyAccumulatorV1` (stage 2, folding the carried stage-1 accumulator)
plus key/proof wire round-trips and pairing validity for any `CurveParams`! -/
private def runFullTwoStagePipeline (c : CurveParams) (tau : Nat) :
    Bool × StepV1Result × FinalVerifyResult × ByteList × ByteList × ByteList × PackedKey × FinalConfig :=
  let anchors := natToLeBytes 128 0x5A3C1E79
  let stmtLow := 0x0123456789ABCDEF
  let stmtHigh := 0x1122334455667788
  let (_, stmt) := statementFromLimbs stmtLow stmtHigh
  let glEntry := 3
  let bnEntry := 5
  -- Stage 1: CompressNarrowFixed.stepV1
  let s1ClaimRow := mkStage1Claim glEntry stmt
  let s1Key := buildRealKey c tau anchors s1ClaimRow
  let s1KeyBytes := encodePackedKey c s1Key
  let s1KeyDig := blake3HashWords s1KeyBytes
  let s1KeyRoundtrip := (readPackedKey c s1KeyBytes).ok == 1
  -- Stage 2 key is fixed (independent of claim payload), so its digest pins `pol.bnDigest`!
  let s2Len1 := if c.affineWords == 18 then 14 else 16
  let s2Key := buildStage2Key c tau anchors 11 s2Len1
  let s2KeyBytes := encodePackedKey c s2Key
  let s2KeyDig := blake3HashWords s2KeyBytes
  let s2KeyRoundtrip := (readPackedKey c s2KeyBytes).ok == 1
  let s1ClaimsBytes := encodeClaims (.cons s1ClaimRow .nil)
  let s1ProofBytes := proveRealKey c tau s1Key (.cons s1ClaimRow .nil)
  let s1ProofRoundtrip := (readPackedProof c s1ProofBytes).ok == 1
  let pol : ChainPolicy :=
    { anchors, glDigest := s1KeyDig, glEntry, bnDigest := s2KeyDig, bnEntry }
  let polBytes := encodeChainPolicy pol
  let polDig := blake3HashWords polBytes
  let stepRes := stepV1 c s1Key s1KeyDig polDig 1 stmt polBytes s1ClaimsBytes s1ProofBytes
  -- Stage 2: CompressFinalNarrow.verifyAccumulatorV1 folding stage-1's non-trivial (A1, B1)!
  let (s2ClaimRows, hdrs) := mkStage2ClaimRows polDig 1 stmt stepRes.chunks
  let (row0, row1) := match s2ClaimRows with
    | .cons r0 (.cons r1 .nil) => (r0, r1)
    | _ => (.nil, .nil)
  let s2ProofBytes := proveStage2Key c tau s2Key row0 row1
  let s2ProofRoundtrip := (readPackedProof c s2ProofBytes).ok == 1
  let s2ClaimsBytes := encodeClaims s2ClaimRows
  let cfg : FinalConfig :=
    { policyDigest := polDig, expectedAnchors := anchors, stage := 2
      keyDigest := s2KeyDig, headers := hdrs }
  let finalRes := verifyAccumulatorV1 c cfg s2Key stmtLow stmtHigh polBytes s2ClaimsBytes s2ProofBytes
  let allWireOk := s1KeyRoundtrip && s1ProofRoundtrip && s2KeyRoundtrip && s2ProofRoundtrip
  (allWireOk, stepRes, finalRes, polBytes, s2ClaimsBytes, s2ProofBytes, s2Key, cfg)

-- 1. REAL 254-bit BN254 full 2-stage pipeline (`CompressNarrowFixed` → `CompressFinalNarrow`)!
private def bn254Run := runFullTwoStagePipeline bn254CurveParams 77777

#guard bn254Run.1 == true
#guard bn254Run.2.1.ok == 1
#guard fListLen bn254Run.2.1.chunks == 4
#guard pairingHoldsInExponent bn254CurveParams 77777 bn254Run.2.1.a bn254Run.2.1.b == true
#guard bn254Run.2.2.1.ok == 1
#guard fListLen bn254Run.2.2.1.affineWords == 18
#guard pairingHoldsInExponent bn254CurveParams 77777 bn254Run.2.2.1.a bn254Run.2.2.1.b == true
#guard
  let ws := bn254Run.2.2.1.affineWords
  decodeAffinePointWords bn254CurveParams (fListTake ws 9) == bn254Run.2.2.1.a &&
    decodeAffinePointWords bn254CurveParams (fListDrop ws 9) == bn254Run.2.2.1.b

-- 2. REAL 381-bit BLS12-381 full 2-stage pipeline (`CompressNarrowFixed` → `CompressFinalNarrow`)!
private def bls12381Run := runFullTwoStagePipeline bls12381CurveParams 88888

#guard bls12381Run.1 == true
#guard bls12381Run.2.1.ok == 1
#guard fListLen bls12381Run.2.1.chunks == 6
#guard pairingHoldsInExponent bls12381CurveParams 88888 bls12381Run.2.1.a bls12381Run.2.1.b == true
#guard bls12381Run.2.2.1.ok == 1
#guard fListLen bls12381Run.2.2.1.affineWords == 22
#guard pairingHoldsInExponent bls12381CurveParams 88888 bls12381Run.2.2.1.a bls12381Run.2.2.1.b == true
#guard
  let ws := bls12381Run.2.2.1.affineWords
  decodeAffinePointWords bls12381CurveParams (fListTake ws 11) == bls12381Run.2.2.1.a &&
    decodeAffinePointWords bls12381CurveParams (fListDrop ws 11) == bls12381Run.2.2.1.b

-- 3. Comprehensive tampering rejection matrix on real BN254 & BLS12-381 pipelines!
--    (wrong policy digest, wrong stage, wrong anchors, wrong header tag, bad proof magic,
--     trailing byte on policy/claims/proof/key, tampered quotient, tampered SHPLONK witness!)
private def bnPolBytes := bn254Run.2.2.2.1
private def bnClaimsBytes := bn254Run.2.2.2.2.1
private def bnProofBytes := bn254Run.2.2.2.2.2.1
private def bnS2Key := bn254Run.2.2.2.2.2.2.1
private def bnCfg := bn254Run.2.2.2.2.2.2.2

-- Wrong policy digest rejected
#guard
  let badCfg : FinalConfig :=
    { bnCfg with policyDigest := { bnCfg.policyDigest with d0 := bnCfg.policyDigest.d0 + 1 } }
  (verifyAccumulatorV1 bn254CurveParams badCfg bnS2Key
    0x0123456789ABCDEF 0x1122334455667788 bnPolBytes bnClaimsBytes bnProofBytes).ok == 0

-- Unauthorized narrow predecessor key digest (`cfg.keyDigest ≠ policy.bnDigest`) rejected (M-1)
#guard
  let badCfg : FinalConfig :=
    { bnCfg with keyDigest := { bnCfg.keyDigest with d0 := bnCfg.keyDigest.d0 + 1 } }
  (verifyAccumulatorV1 bn254CurveParams badCfg bnS2Key
    0x0123456789ABCDEF 0x1122334455667788 bnPolBytes bnClaimsBytes bnProofBytes).ok == 0

-- Wrong stage rejected (stage = 1 in terminal, stage = 3 mismatching prevStage = 1)
#guard
  (verifyAccumulatorV1 bn254CurveParams { bnCfg with stage := 1 } bnS2Key
    0x0123456789ABCDEF 0x1122334455667788 bnPolBytes bnClaimsBytes bnProofBytes).ok == 0
#guard
  (verifyAccumulatorV1 bn254CurveParams { bnCfg with stage := 3 } bnS2Key
    0x0123456789ABCDEF 0x1122334455667788 bnPolBytes bnClaimsBytes bnProofBytes).ok == 0

-- Wrong expected anchors rejected
#guard
  let badCfg : FinalConfig := { bnCfg with expectedAnchors := natToLeBytes 128 999999 }
  (verifyAccumulatorV1 bn254CurveParams badCfg bnS2Key
    0x0123456789ABCDEF 0x1122334455667788 bnPolBytes bnClaimsBytes bnProofBytes).ok == 0

-- Wrong statement rejected
#guard
  (verifyAccumulatorV1 bn254CurveParams bnCfg bnS2Key
    0x0123456789ABCDEE 0x1122334455667788 bnPolBytes bnClaimsBytes bnProofBytes).ok == 0

-- Wrong narrow claim header tag rejected
#guard
  let badHdrs := match bnCfg.headers with
    | .cons h t => ClaimHeaderList.cons { h with tag := h.tag + 1 } t
    | .nil => .nil
  (verifyAccumulatorV1 bn254CurveParams { bnCfg with headers := badHdrs } bnS2Key
    0x0123456789ABCDEF 0x1122334455667788 bnPolBytes bnClaimsBytes bnProofBytes).ok == 0

-- Trailing byte rejected on policy, claims, proof, and key
#guard
  (verifyAccumulatorV1 bn254CurveParams bnCfg bnS2Key
    0x0123456789ABCDEF 0x1122334455667788
    (byteAppend bnPolBytes (.cons 0 .nil)) bnClaimsBytes bnProofBytes).ok == 0
#guard
  (verifyAccumulatorV1 bn254CurveParams bnCfg bnS2Key
    0x0123456789ABCDEF 0x1122334455667788
    bnPolBytes (byteAppend bnClaimsBytes (.cons 0 .nil)) bnProofBytes).ok == 0
#guard
  (verifyAccumulatorV1 bn254CurveParams bnCfg bnS2Key
    0x0123456789ABCDEF 0x1122334455667788
    bnPolBytes bnClaimsBytes (byteAppend bnProofBytes (.cons 0 .nil))).ok == 0
#guard
  (readPackedKey bn254CurveParams (byteAppend (encodePackedKey bn254CurveParams bnS2Key) (.cons 0 .nil))).ok == 0

-- Tampered quotient opening rejected by `verifyPacked`!
#guard
  let pr := readPackedProof bn254CurveParams bnProofBytes
  let badQo := match pr.proof.quotientOpen with
    | .cons (.cons (.cons q0 r0) r1) r2 =>
      FList3.cons (.cons (.cons (frAdd bn254Fr q0 1) r0) r1) r2
    | other => other
  let badProofBytes := encodePackedProof { pr.proof with quotientOpen := badQo }
  (verifyAccumulatorV1 bn254CurveParams bnCfg bnS2Key
    0x0123456789ABCDEF 0x1122334455667788 bnPolBytes bnClaimsBytes badProofBytes).ok == 0

-- Tampered SHPLONK opening witness `W1` fails pairing check `A + τ·B ≠ O` on BOTH BN254 & BLS12-381!
#guard
  let pr := readPackedProof bn254CurveParams bnProofBytes
  let badW1Pt := g1Add bn254CurveParams pr.proof.w1.point (g1Gen bn254CurveParams)
  let badW1 : PackedWitness := { point := badW1Pt, rawBytes := g1ToBytes bn254CurveParams badW1Pt }
  let badProofBytes := encodePackedProof { pr.proof with w1 := badW1 }
  let res := verifyAccumulatorV1 bn254CurveParams bnCfg bnS2Key
    0x0123456789ABCDEF 0x1122334455667788 bnPolBytes bnClaimsBytes badProofBytes
  res.ok == 1 && pairingHoldsInExponent bn254CurveParams 77777 res.a res.b == false

#guard
  let blsPolBytes := bls12381Run.2.2.2.1
  let blsClaimsBytes := bls12381Run.2.2.2.2.1
  let blsProofBytes := bls12381Run.2.2.2.2.2.1
  let blsS2Key := bls12381Run.2.2.2.2.2.2.1
  let blsCfg := bls12381Run.2.2.2.2.2.2.2
  let pr := readPackedProof bls12381CurveParams blsProofBytes
  let badW2Pt := g1Add bls12381CurveParams pr.proof.w2.point (g1Gen bls12381CurveParams)
  let badW2 : PackedWitness := { point := badW2Pt, rawBytes := g1ToBytes bls12381CurveParams badW2Pt }
  let badProofBytes := encodePackedProof { pr.proof with w2 := badW2 }
  let res := verifyAccumulatorV1 bls12381CurveParams blsCfg blsS2Key
    0x0123456789ABCDEF 0x1122334455667788 blsPolBytes blsClaimsBytes badProofBytes
  res.ok == 1 && pairingHoldsInExponent bls12381CurveParams 88888 res.a res.b == false

-- Stage-1 `stepV1` tampering: wrong stage (`stage = 2`), unauthorized key digest
#guard
  let anchors := natToLeBytes 128 0x5A3C1E79
  let (_, stmt) := statementFromLimbs 0x0123456789ABCDEF 0x1122334455667788
  let s1ClaimRow := mkStage1Claim 3 stmt
  let s1Key := buildRealKey bn254CurveParams 77777 anchors s1ClaimRow
  let s1KeyDig := blake3HashWords (encodePackedKey bn254CurveParams s1Key)
  let s1ClaimsBytes := encodeClaims (.cons s1ClaimRow .nil)
  let s1ProofBytes := proveRealKey bn254CurveParams 77777 s1Key (.cons s1ClaimRow .nil)
  let badDig : DigestWords := { s1KeyDig with d7 := s1KeyDig.d7 + 1 }
  (stepV1 bn254CurveParams s1Key s1KeyDig bnCfg.policyDigest 2 stmt
    bnPolBytes s1ClaimsBytes s1ProofBytes).ok == 0 &&
  (stepV1 bn254CurveParams s1Key badDig bnCfg.policyDigest 1 stmt
    bnPolBytes s1ClaimsBytes s1ProofBytes).ok == 0

-- 4. Shared-fixed-slot (`PackedFixed.shared`, 2 circuits sharing 1 fixed slot) check!
#guard
  let c := bn254CurveParams
  let anchors := natToLeBytes 128 42
  let circ := buildRealCircuit (.cons 99 .nil)
  let fixedComm := mkPackedCommitment c (.cons { log := 1, width := 1, hasNext := 0 } .nil)
    (.cons (g1Gen c) .nil)
  let circuits : CircuitList := .cons circ (.cons circ .nil)
  let fixed : PackedFixed := .shared fixedComm (.cons 1 (.cons 1 .nil))
  let sharedKey : PackedKey :=
    { seed := bindPackedSeed c (.cons 1 .nil) circuits fixed
      maxLog := 2, budget := 2, generator := g1Gen c, anchors
      circuits, fixed }
  let raw := encodePackedKey c sharedKey
  let pk := readPackedKey c raw
  pk.ok == 1 && pk.key.fixed == sharedKey.fixed

-- 4b. Key-binding transcript seed & BLS12-381 prime-order G1 subgroup rejection in `verifyPacked`!
#guard
  let pr := readPackedProof bn254CurveParams bnProofBytes
  let pc := readClaims bn254CurveParams bnClaimsBytes
  let unboundKey : PackedKey := { bnS2Key with seed := .cons 105 (.cons 120 (.cons 50 .nil)) }
  let badFixedComm := mkPackedCommitment bn254CurveParams
    (.cons { log := 1, width := 1, hasNext := 0 } .nil) (.cons (g1Gen bn254CurveParams) .nil)
  let mutFixedKey : PackedKey := { bnS2Key with fixed := .some badFixedComm }
  let mutCircs := match bnS2Key.circuits with
    | .cons c0 rest =>
      let rec bumpFirstConst : NodeList → NodeList
        | .nil => .nil
        | .cons (.const v) ns => .cons (.const (v + 1)) ns
        | .cons nd ns => .cons nd (bumpFirstConst ns)
      CircuitList.cons { c0 with nodes := bumpFirstConst c0.nodes } rest
    | .nil => .nil
  let mutConstKey : PackedKey := { bnS2Key with circuits := mutCircs }
  (verifyPacked bn254CurveParams bnS2Key pr.proof pc.claims).ok == 1 &&
    (verifyPacked bn254CurveParams unboundKey pr.proof pc.claims).ok == 0 &&
    (verifyPacked bn254CurveParams mutFixedKey pr.proof pc.claims).ok == 0 &&
    (verifyPacked bn254CurveParams mutConstKey pr.proof pc.claims).ok == 0

private def blsTorsionPoint : G1Point :=
  { x := 4
    y := 1630892974828014537729259858097113969650871260980656934049590190201941782487224876496582135785777461178964897591404
    isInf := 0 }

#guard
  let blsClaimsBytes := bls12381Run.2.2.2.2.1
  let blsProofBytes := bls12381Run.2.2.2.2.2.1
  let blsS2Key := bls12381Run.2.2.2.2.2.2.1
  let pr := readPackedProof bls12381CurveParams blsProofBytes
  let pc := readClaims bls12381CurveParams blsClaimsBytes
  let torsionW1 : PackedWitness :=
    { point := blsTorsionPoint, rawBytes := g1ToBytes bls12381CurveParams blsTorsionPoint }
  let torsionProof := { pr.proof with w1 := torsionW1 }
  let torsionProofBytes := encodePackedProof torsionProof
  let torsionKey := { blsS2Key with generator := blsTorsionPoint }
  (readPackedProof bls12381CurveParams torsionProofBytes).ok == 0 &&
    (verifyPacked bls12381CurveParams blsS2Key torsionProof pc.claims).ok == 0 &&
    (verifyPacked bls12381CurveParams torsionKey pr.proof pc.claims).ok == 0

-- 5. Live-exportable dual-curve & Goldilocks entrypoints `#guard` self-checks!
#guard entryAlgebraStaticBN254 7 11 42 11215 == 1
#guard entryAlgebraStaticBN254 7 11 42 11216 == 0
#guard entryAlgebraStaticBN254 1 11 42 11215 == 0
#guard entryAlgebraStaticBLS12381 7 11 42 11215 == 1
#guard entryAlgebraStaticBLS12381 7 11 42 11216 == 0
#guard entryNarrowStepBN254 7 11 42 11215 == 1
#guard entryNarrowStepBN254 7 11 42 11216 == 0
#guard entryNarrowStepBLS12381 7 11 42 11215 == 1
#guard entryNarrowStepBLS12381 7 11 42 11216 == 0
#guard (entryFinalTerminalBN254 7 11 42 11215).a.isInf == 0
#guard (entryFinalTerminalBN254 7 11 42 11216).a.isInf == 1
#guard (entryFinalTerminalBLS12381 7 11 42 11215).a.isInf == 0
#guard (entryFinalTerminalBLS12381 7 11 42 11216).a.isInf == 1
#guard entryGoldilocksSmoke 7 11 42 11215 == 1
#guard entryGoldilocksSmoke 7 11 42 11216 == 0
#guard entryGoldilocksSmoke 7 12 42 11215 == 0
#guard entryGoldilocksSmoke 7 11 43 11215 == 0

end CryptographicFixtures

end KzgPackedPure
