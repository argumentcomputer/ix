import Ix.Cert.MultiStark.Types
import CertiFriP3.GoldilocksExt

/-! # Out-of-Circuit Multi-STARK AIR & LogUp OOD Evaluator (`Ix.Cert.MultiStark.Air`)

Mathlib-free evaluator matching `multi-stark/src/{verifier.rs,lookup.rs,graph.rs}` and
`MultiStark/MultiStark/Modules/StarkVerifier.lean:140-430`:
- Trace vanishing & unnormalized Lagrange selectors (`is_first_row`, `is_last_row`, `is_transition`)
- Compiled `ConstraintGraph` DAG sweep in `EF = GoldilocksExt`
- Grouped chained LogUp constraint evaluation over `EF × EF` (`K[u]/(u^2 - 7)`)
- Quotient slice recombination and `comp * inv_vanishing == quot` verification
- Claims and batch-messages LogUp accumulators (`Σ mult · (β + fp(γ, args))⁻¹`).
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3

/-- Repeated squaring: `x ^ (2 ^ k)` in `EF`. -/
def efPow2 (x : EF) : Nat → EF
  | 0 => x
  | k + 1 => efPow2 (x.mul x) k

/-- Trace selectors at OOD point `ζ` for domain of size `2^logDeg`, matching
`StarkVerifier.lean:140-148` and `p3_commit::TwoAdicMultiplicativeCoset::selectors_at_point`.
Returns `none` if `ζ = 0` or `ζ^(2^logDeg) = 1` (degenerate / on-domain OOD point). -/
def traceSelectors? (zeta : EF) (logDeg : Nat) : Option (EF × EF × EF × EF) := do
  if zeta == GoldilocksExt.zero || logDeg > 32 then none
  let zPowN := efPow2 zeta logDeg
  let zh := zPowN.sub GoldilocksExt.one
  if zh == GoldilocksExt.zero then none
  let g : F := TwoAdicOps.twoAdicGenerator logDeg
  let gInv : F := g.inv
  let denomFirst := zeta.sub GoldilocksExt.one
  let denomLast := zeta.sub (GoldilocksExt.embed gInv)
  if denomFirst == GoldilocksExt.zero || denomLast == GoldilocksExt.zero then none
  let isFirst := zh.mul denomFirst.inv
  let isLast := zh.mul denomLast.inv
  let isTrans := denomLast
  let invVan := zh.inv
  pure (isFirst, isLast, isTrans, invVan)

/-- Multiplication in `EF[u] / (u^2 - 7)` (`StarkVerifier.lean:216-219`), used when
evaluating base-field-flattened extension columns at OOD point `ζ ∈ EF`. -/
def pairMul (a0 a1 b0 b1 : EF) : EF × EF :=
  let w7 := GoldilocksExt.embed GoldilocksExt.nonResidue
  ((a0.mul b0).add (w7.mul (a1.mul b1)), (a0.mul b1).add (a1.mul b0))

/-- Horner fingerprint `Σ_i args[i] · γ^i` (`StarkVerifier.lean:413-419`). -/
def fingerprintVals (gamma : EF) (args : Array F) : EF :=
  args.foldr (init := GoldilocksExt.zero) fun v acc =>
    (GoldilocksExt.embed v).add (gamma.mul acc)

/-- Claims accumulator `Σ_c (β + fp(γ, c))⁻¹`, failing closed on zero denominator. -/
def claimsAccumulator? (beta gamma : EF) (claims : Array (Array F)) : Option EF :=
  claims.foldlM (init := GoldilocksExt.zero) fun acc c => do
    let denom := beta.add (fingerprintVals gamma c)
    if denom == GoldilocksExt.zero then none
    pure (acc.add denom.inv)

/-- Messages accumulator `Σ_m mult_m · (β + fp(γ, args_m))⁻¹`, failing closed on zero denominator. -/
def messagesAccumulator? (beta gamma : EF) (messages : Array BatchMessage) : Option EF :=
  messages.foldlM (init := GoldilocksExt.zero) fun acc m => do
    let denom := beta.add (fingerprintVals gamma m.args)
    if denom == GoldilocksExt.zero then none
    let term := (GoldilocksExt.embed m.multiplicity).mul denom.inv
    pure (acc.add term)

/-- Evaluate all nodes of a compiled `ConstraintGraph` in topological order (`0..nodes.size-1`).
Returns `none` if any node references an out-of-range child, column, or public input. -/
def sweepGraph? (nodes : Array GraphNode)
    (prepCur prepNext mainCur mainNext s2Cur s2Next publics : Array EF)
    (isFirst isLast isTrans : EF) : Option (Array EF) := do
  let mut vals := Array.mkEmpty nodes.size
  for node in nodes do
    let v ← match node with
      | .const c => some (GoldilocksExt.embed c)
      | .var src off col =>
        let row := match src, off with
          | .preprocessed, .current => prepCur
          | .preprocessed, .next => prepNext
          | .main, .current => mainCur
          | .main, .next => mainNext
          | .stage2, .current => s2Cur
          | .stage2, .next => s2Next
        row[col]?
      | .publicInput idx => publics[idx]?
      | .isFirstRow => some isFirst
      | .isLastRow => some isLast
      | .isTransition => some isTrans
      | .add a b => do
        let va ← vals[a]?
        let vb ← vals[b]?
        pure (va.add vb)
      | .sub a b => do
        let va ← vals[a]?
        let vb ← vals[b]?
        pure (va.sub vb)
      | .mul a b => do
        let va ← vals[a]?
        let vb ← vals[b]?
        pure (va.mul vb)
      | .neg a => do
        let va ← vals[a]?
        pure va.neg
    vals := vals.push v
  pure vals

/-- Fold a constraint value `x` into `acc` via Horner in `α`: `acc * α + x`. -/
@[inline] def oodFold (acc alpha x : EF) : EF :=
  (acc.mul alpha).add x

/-- Evaluate lookup fingerprint in `EF[u]/(u^2 - 7)` from swept node values
(`StarkVerifier.lean:221-235`). -/
def logupFingerprint? (vals : Array EF) (g0 g1 : EF) (args : Array Nat) : Option (EF × EF) :=
  args.foldrM (init := (GoldilocksExt.zero, GoldilocksExt.zero)) fun nodeId (f0, f1) => do
    let av ← vals[nodeId]?
    let (m0, m1) := pairMul f0 f1 g0 g1
    pure (m0.add av, m1)

/-- Evaluate and fold all user constraints followed by all grouped LogUp constraints
into the OOD composition value (`StarkVerifier.lean:293-322`, `multi-stark/src/lookup.rs`). -/
def oodComposition? (circuit : SysCircuit) (vals : Array EF)
    (s2Cur s2Next : Array EF) (beta gamma accPrev accNext isLast alpha : EF)
    (injNorm : F) : Option EF := do
  -- 1. Fold user constraint roots in order
  let mut comp := GoldilocksExt.zero
  for z in circuit.zeros do
    let v ← vals[z]?
    comp := oodFold comp alpha v

  -- 2. Prepare LogUp parameters in EF[u]/(u^2 - 7)
  let b0 := GoldilocksExt.embed beta.c0
  let b1 := GoldilocksExt.embed beta.c1
  let g0 := GoldilocksExt.embed gamma.c0
  let g1 := GoldilocksExt.embed gamma.c1
  let a0 := GoldilocksExt.embed accPrev.c0
  let a1 := GoldilocksExt.embed accPrev.c1
  let na0 := GoldilocksExt.embed accNext.c0
  let na1 := GoldilocksExt.embed accNext.c1
  let inormEF := GoldilocksExt.embed injNorm
  let inj0 := isLast.mul ((na0.sub a0).mul inormEF)
  let inj1 := isLast.mul ((na1.sub a1).mul inormEF)

  -- 3. Fold grouped LogUp constraints
  let lcount := circuit.lookups.size
  if lcount == 0 then
    let s0 ← s2Cur[0]?
    let s1 ← s2Cur[1]?
    let t0 ← s2Next[0]?
    let t1 ← s2Next[1]?
    comp := oodFold comp alpha ((t0.sub s0).add inj0)
    comp := oodFold comp alpha ((t1.sub s1).add inj1)
    pure comp
  else
    let k := max 1 circuit.lookupGroupSize
    let mut groupIdx := 0
    let mut rem := k
    let mut p0 := GoldilocksExt.one
    let mut p1 := GoldilocksExt.zero
    let mut r0 := GoldilocksExt.zero
    let mut r1 := GoldilocksExt.zero
    for j in [0:lcount] do
      let lk ← circuit.lookups[j]?
      let (f0, f1) ← logupFingerprint? vals g0 g1 lk.args
      let m0 := f0.add b0
      let m1 := f1.add b1
      let mv ← vals[lk.multiplicity]?
      let (rm0, rm1) := pairMul r0 r1 m0 m1
      let nr0 := rm0.add (mv.mul p0)
      let nr1 := rm1.add (mv.mul p1)
      let (np0, np1) := pairMul p0 p1 m0 m1
      if j + 1 == lcount then
        let s0 ← s2Cur[2 * groupIdx]?
        let s1 ← s2Cur[2 * groupIdx + 1]?
        let t0 := (← s2Next[0]?).add inj0
        let t1 := (← s2Next[1]?).add inj1
        let (c0, c1) := pairMul np0 np1 (t0.sub s0) (t1.sub s1)
        comp := oodFold (oodFold comp alpha (c0.sub nr0)) alpha (c1.sub nr1)
      else if rem == 1 then
        let s0 ← s2Cur[2 * groupIdx]?
        let s1 ← s2Cur[2 * groupIdx + 1]?
        let t0 ← s2Cur[2 * groupIdx + 2]?
        let t1 ← s2Cur[2 * groupIdx + 3]?
        let (c0, c1) := pairMul np0 np1 (t0.sub s0) (t1.sub s1)
        comp := oodFold (oodFold comp alpha (c0.sub nr0)) alpha (c1.sub nr1)
        groupIdx := groupIdx + 1
        rem := k
        p0 := GoldilocksExt.one
        p1 := GoldilocksExt.zero
        r0 := GoldilocksExt.zero
        r1 := GoldilocksExt.zero
      else
        rem := rem - 1
        p0 := np0
        p1 := np1
        r0 := nr0
        r1 := nr1
    pure comp

/-- Recombine base-flattened quotient slice evaluations at `ζ` (`StarkVerifier.lean:158-165, 332-338`):
each pair `(c0, c1)` reconstructs `c0 + c1 · u`, then evaluates `Σ_r slice_r · (ζ^N)^r`. -/
def recombineQuotient? (rawRow : Array EF) (expectedSlices : Nat) (zetaPowN : EF) : Option EF := do
  if rawRow.size != 2 * expectedSlices then none
  let unitX : EF := ⟨Goldilocks.zero, Goldilocks.one⟩
  let mut acc := GoldilocksExt.zero
  let mut pow := GoldilocksExt.one
  for r in [0:expectedSlices] do
    let c0 ← rawRow[2 * r]?
    let c1 ← rawRow[2 * r + 1]?
    let slice := c0.add (c1.mul unitX)
    acc := acc.add (pow.mul slice)
    pow := pow.mul zetaPowN
  pure acc

/-- Verify the OOD AIR + LogUp identity for one active circuit in a shard
(`multi-stark/src/verifier.rs:468-545`, `StarkVerifier.lean:364-411`). -/
def checkCircuitOod (circuit : SysCircuit) (logDeg : Nat)
    (prepCur prepNext mainCur mainNext s2Cur s2Next quotRow : Array EF)
    (beta gamma accPrev accNext alpha zeta : EF) : Bool :=
  let height := 1 <<< logDeg
  if logDeg ≥ 32 then false
  else if circuit.preprocessedHeight != 0 && height != circuit.preprocessedHeight then false
  else if mainCur.size != circuit.mainWidth || mainNext.size != circuit.mainWidth then false
  else if s2Cur.size != circuit.stage2Width || s2Next.size != circuit.stage2Width then false
  else if prepCur.size != circuit.preprocessedWidth || prepNext.size != circuit.preprocessedWidth then false
  else
    match traceSelectors? zeta logDeg with
    | none => false
    | some (isFirst, isLast, isTrans, invVan) =>
      let publics : Array EF := #[
        GoldilocksExt.embed beta.c0, GoldilocksExt.embed beta.c1,
        GoldilocksExt.embed gamma.c0, GoldilocksExt.embed gamma.c1,
        GoldilocksExt.embed accPrev.c0, GoldilocksExt.embed accPrev.c1,
        GoldilocksExt.embed accNext.c0, GoldilocksExt.embed accNext.c1
      ]
      let g : F := TwoAdicOps.twoAdicGenerator logDeg
      let injNorm : F := ((Goldilocks.ofNat height).mul g).inv
      match sweepGraph? circuit.nodes prepCur prepNext mainCur mainNext s2Cur s2Next publics
          isFirst isLast isTrans with
      | none => false
      | some vals =>
        match oodComposition? circuit vals s2Cur s2Next beta gamma accPrev accNext isLast alpha injNorm with
        | none => false
        | some comp =>
          let zetaPowN := efPow2 zeta logDeg
          match recombineQuotient? quotRow circuit.quotientDegree zetaPowN with
          | none => false
          | some quot => comp.mul invVan == quot

end Ix.Cert.MultiStark
