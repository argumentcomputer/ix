import Ix.Cert.MultiStark.Types
import CertiFriP3.GoldilocksExt3

/-! # Out-of-Circuit Multi-STARK Protocol `v6` AIR & LogUp OOD Evaluator (`Ix.Cert.MultiStark.Air`)

Mathlib-free evaluator matching Protocol `v6` (`multi-stark/src/{verifier.rs,lookup.rs,graph.rs}`
and `MultiStark/MultiStark/Modules/StarkVerifier.lean:140-430`) over `EF = GoldilocksExt3`
(`Fp^3 = Fp[X] / (X^3 - X - 1)`):
- Trace vanishing & unnormalized Lagrange selectors (`is_first_row`, `is_last_row`, `is_transition`)
- Compiled `ConstraintGraph` DAG sweep in `EF = GoldilocksExt3`
- Grouped chained LogUp constraint evaluation over `EF × EF × EF` (`K[Y] / (Y^3 - Y - 1)`)
- Quotient slice recombination (`c0 + c1·X + c2·X^2`) and `comp * inv_vanishing == quot`
- Claims and batch-messages LogUp accumulators (`Σ mult · (β + fp(γ, args))⁻¹`).
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3

/-- Repeated squaring: `x ^ (2 ^ k)` in `EF`. -/
def efPow2 (x : EF) : Nat → EF
  | 0 => x
  | k + 1 => efPow2 (x.mul x) k

/-- Trace selectors at OOD point `ζ` for domain of size `2^logDeg`, matching
`StarkVerifier.lean:147-157` and `p3_commit::TwoAdicMultiplicativeCoset::selectors_at_point`.
Returns `none` if `ζ = 0` or `ζ^(2^logDeg) = 1` (degenerate / on-domain OOD point). -/
def traceSelectors? (zeta : EF) (logDeg : Nat) : Option (EF × EF × EF × EF) := do
  if zeta == GoldilocksExt3.zero || logDeg > 32 then none
  let zPowN := efPow2 zeta logDeg
  let zh := zPowN.sub GoldilocksExt3.one
  if zh == GoldilocksExt3.zero then none
  let g : F := TwoAdicOps.twoAdicGenerator logDeg
  let gInv : F := g.inv
  let denomFirst := zeta.sub GoldilocksExt3.one
  let denomLast := zeta.sub (GoldilocksExt3.embed gInv)
  if denomFirst == GoldilocksExt3.zero || denomLast == GoldilocksExt3.zero then none
  let isFirst := zh.mul denomFirst.inv
  let isLast := zh.mul denomLast.inv
  let isTrans := denomLast
  let invVan := zh.inv
  pure (isFirst, isLast, isTrans, invVan)

/-- Coordinate-wise Karatsuba multiplication in `EF[Y] / (Y^3 - Y - 1)`
(`StarkVerifier.lean:230-242`), used when evaluating base-field-flattened cubic extension
columns at OOD point `ζ ∈ EF`. -/
def tripleMul (a0 a1 a2 b0 b1 b2 : EF) : EF × EF × EF :=
  let v0 := a0.mul b0
  let v1 := a1.mul b1
  let v2 := a2.mul b2
  let m01 := (((a0.add a1).mul (b0.add b1)).sub v0).sub v1
  let m02 := (((a0.add a2).mul (b0.add b2)).sub v0).sub v2
  let m12 := (((a1.add a2).mul (b1.add b2)).sub v1).sub v2
  (v0.add m12, (m01.add m12).add v2, (m02.add v1).add v2)

/-- Horner fingerprint `Σ_i args[i] · γ^i` (`StarkVerifier.lean`). -/
def fingerprintVals (gamma : EF) (args : Array F) : EF :=
  args.foldr (init := GoldilocksExt3.zero) fun v acc =>
    (GoldilocksExt3.embed v).add (gamma.mul acc)

/-- Claims accumulator `Σ_c (β + fp(γ, c))⁻¹`, failing closed on zero denominator. -/
def claimsAccumulator? (beta gamma : EF) (claims : Array (Array F)) : Option EF :=
  claims.foldlM (init := GoldilocksExt3.zero) fun acc c => do
    let denom := beta.add (fingerprintVals gamma c)
    if denom == GoldilocksExt3.zero then none
    pure (acc.add denom.inv)

/-- Messages accumulator `Σ_m mult_m · (β + fp(γ, args_m))⁻¹`, failing closed on zero denominator. -/
def messagesAccumulator? (beta gamma : EF) (messages : Array BatchMessage) : Option EF :=
  messages.foldlM (init := GoldilocksExt3.zero) fun acc m => do
    let denom := beta.add (fingerprintVals gamma m.args)
    if denom == GoldilocksExt3.zero then none
    let term := (GoldilocksExt3.embed m.multiplicity).mul denom.inv
    pure (acc.add term)

/-- Evaluate all nodes of a compiled `ConstraintGraph` in topological order (`0..nodes.size-1`).
Returns `none` if any node references an out-of-range child, column, or public input. -/
def sweepGraph? (nodes : Array GraphNode)
    (prepCur prepNext mainCur mainNext s2Cur s2Next publics : Array EF)
    (isFirst isLast isTrans : EF) : Option (Array EF) := do
  let mut vals := Array.mkEmpty nodes.size
  for node in nodes do
    let v ← match node with
      | .const c => some (GoldilocksExt3.embed c)
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

/-- Evaluate lookup fingerprint in `EF[Y] / (Y^3 - Y - 1)` from swept node values
(`StarkVerifier.lean:244-258`). -/
def logupFingerprint? (vals : Array EF) (g0 g1 g2 : EF) (args : Array Nat) :
    Option (EF × EF × EF) :=
  args.foldrM (init := (GoldilocksExt3.zero, GoldilocksExt3.zero, GoldilocksExt3.zero))
    fun nodeId (f0, f1, f2) => do
      let av ← vals[nodeId]?
      let (m0, m1, m2) := tripleMul f0 f1 f2 g0 g1 g2
      pure (m0.add av, m1, m2)

/-- Evaluate and fold all user constraints followed by all grouped LogUp constraints
into the OOD composition value (`StarkVerifier.lean:260-357`, `multi-stark/src/lookup.rs`). -/
def oodComposition? (circuit : SysCircuit) (vals : Array EF)
    (s2Cur s2Next : Array EF) (beta gamma accPrev accNext isLast alpha : EF)
    (injNorm : F) : Option EF := do
  -- 1. Fold user constraint roots in order
  let mut comp := GoldilocksExt3.zero
  for z in circuit.zeros do
    let v ← vals[z]?
    comp := oodFold comp alpha v

  -- 2. Prepare LogUp parameters in EF[Y] / (Y^3 - Y - 1)
  let b0 := GoldilocksExt3.embed beta.c0
  let b1 := GoldilocksExt3.embed beta.c1
  let b2 := GoldilocksExt3.embed beta.c2
  let g0 := GoldilocksExt3.embed gamma.c0
  let g1 := GoldilocksExt3.embed gamma.c1
  let g2 := GoldilocksExt3.embed gamma.c2
  let a0 := GoldilocksExt3.embed accPrev.c0
  let a1 := GoldilocksExt3.embed accPrev.c1
  let a2 := GoldilocksExt3.embed accPrev.c2
  let na0 := GoldilocksExt3.embed accNext.c0
  let na1 := GoldilocksExt3.embed accNext.c1
  let na2 := GoldilocksExt3.embed accNext.c2
  let inormEF := GoldilocksExt3.embed injNorm
  let inj0 := isLast.mul ((na0.sub a0).mul inormEF)
  let inj1 := isLast.mul ((na1.sub a1).mul inormEF)
  let inj2 := isLast.mul ((na2.sub a2).mul inormEF)

  -- 3. Fold grouped LogUp constraints
  let lcount := circuit.lookups.size
  if lcount == 0 then
    let s0 ← s2Cur[0]?
    let s1 ← s2Cur[1]?
    let s2 ← s2Cur[2]?
    let t0 ← s2Next[0]?
    let t1 ← s2Next[1]?
    let t2 ← s2Next[2]?
    comp := oodFold comp alpha ((t0.sub s0).add inj0)
    comp := oodFold comp alpha ((t1.sub s1).add inj1)
    comp := oodFold comp alpha ((t2.sub s2).add inj2)
    pure comp
  else
    let k := max 1 circuit.lookupGroupSize
    let mut groupIdx := 0
    let mut rem := k
    let mut p0 := GoldilocksExt3.one
    let mut p1 := GoldilocksExt3.zero
    let mut p2 := GoldilocksExt3.zero
    let mut r0 := GoldilocksExt3.zero
    let mut r1 := GoldilocksExt3.zero
    let mut r2 := GoldilocksExt3.zero
    for j in [0:lcount] do
      let lk ← circuit.lookups[j]?
      let (f0, f1, f2) ← logupFingerprint? vals g0 g1 g2 lk.args
      let m0 := f0.add b0
      let m1 := f1.add b1
      let m2 := f2.add b2
      let mv ← vals[lk.multiplicity]?
      let (rm0, rm1, rm2) := tripleMul r0 r1 r2 m0 m1 m2
      let nr0 := rm0.add (mv.mul p0)
      let nr1 := rm1.add (mv.mul p1)
      let nr2 := rm2.add (mv.mul p2)
      let (np0, np1, np2) := tripleMul p0 p1 p2 m0 m1 m2
      if j + 1 == lcount then
        let g3 := 3 * groupIdx
        let s0 ← s2Cur[g3]?
        let s1 ← s2Cur[g3 + 1]?
        let s2 ← s2Cur[g3 + 2]?
        let t0 := (← s2Next[0]?).add inj0
        let t1 := (← s2Next[1]?).add inj1
        let t2 := (← s2Next[2]?).add inj2
        let (c0, c1, c2) := tripleMul np0 np1 np2 (t0.sub s0) (t1.sub s1) (t2.sub s2)
        comp := oodFold (oodFold (oodFold comp alpha (c0.sub nr0)) alpha (c1.sub nr1)) alpha (c2.sub nr2)
      else if rem == 1 then
        let g3 := 3 * groupIdx
        let s0 ← s2Cur[g3]?
        let s1 ← s2Cur[g3 + 1]?
        let s2 ← s2Cur[g3 + 2]?
        let t0 ← s2Cur[g3 + 3]?
        let t1 ← s2Cur[g3 + 4]?
        let t2 ← s2Cur[g3 + 5]?
        let (c0, c1, c2) := tripleMul np0 np1 np2 (t0.sub s0) (t1.sub s1) (t2.sub s2)
        comp := oodFold (oodFold (oodFold comp alpha (c0.sub nr0)) alpha (c1.sub nr1)) alpha (c2.sub nr2)
        groupIdx := groupIdx + 1
        rem := k
        p0 := GoldilocksExt3.one
        p1 := GoldilocksExt3.zero
        p2 := GoldilocksExt3.zero
        r0 := GoldilocksExt3.zero
        r1 := GoldilocksExt3.zero
        r2 := GoldilocksExt3.zero
      else
        rem := rem - 1
        p0 := np0
        p1 := np1
        p2 := np2
        r0 := nr0
        r1 := nr1
        r2 := nr2
    pure comp

/-- Recombine base-flattened cubic quotient slice evaluations at `ζ`
(`StarkVerifier.lean:164-178, 367-373`):
each triple `(c0, c1, c2)` reconstructs `c0 + c1·X + c2·X^2` in `Fp[X]/(X^3 - X - 1)`,
then evaluates `Σ_r slice_r · (ζ^N)^r`. -/
def recombineQuotient? (rawRow : Array EF) (expectedSlices : Nat) (zetaPowN : EF) : Option EF := do
  if rawRow.size != 3 * expectedSlices then none
  let unitX : EF := ⟨Goldilocks.zero, Goldilocks.one, Goldilocks.zero⟩
  let unitX2 : EF := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.one⟩
  let mut acc := GoldilocksExt3.zero
  let mut pow := GoldilocksExt3.one
  for r in [0:expectedSlices] do
    let c0 ← rawRow[3 * r]?
    let c1 ← rawRow[3 * r + 1]?
    let c2 ← rawRow[3 * r + 2]?
    let slice := (c0.add (c1.mul unitX)).add (c2.mul unitX2)
    acc := acc.add (pow.mul slice)
    pow := pow.mul zetaPowN
  pure acc

/-- Verify the OOD AIR + LogUp identity for one active circuit in a shard
(`multi-stark/src/verifier.rs`, `StarkVerifier.lean:359-450`). -/
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
        GoldilocksExt3.embed beta.c0, GoldilocksExt3.embed beta.c1, GoldilocksExt3.embed beta.c2,
        GoldilocksExt3.embed gamma.c0, GoldilocksExt3.embed gamma.c1, GoldilocksExt3.embed gamma.c2,
        GoldilocksExt3.embed accPrev.c0, GoldilocksExt3.embed accPrev.c1, GoldilocksExt3.embed accPrev.c2,
        GoldilocksExt3.embed accNext.c0, GoldilocksExt3.embed accNext.c1, GoldilocksExt3.embed accNext.c2
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
