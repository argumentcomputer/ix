import Ix.Cert.MultiStark.Types
import Ix.Cert.MultiStark.Wire
import Ix.Cert.MultiStark.Transcript
import Ix.Cert.MultiStark.Air
import Ix.Cert.MultiStark.Preamble
import CertiFriP3.DomainSep
import CertiFriP3.Pruned
import CertiFri.TensorBatching
import CertiFri.Verifier

/-! # Executable Out-of-Circuit Certified Protocol `v6` Multi-STARK Verifier (`Ix.Cert.MultiStark.Verifier`)

Mathlib-free executable verifier for `multi-stark` Protocol `v6` (`310c5a3f`, `Fp^3`,
`FriBatching::Tensor`, native BLAKE3 `derive_key` domain separation) batch proofs built
directly on `CertiFri.Fri.{shapeOk, inputChecks, commitChecks, foldChain, tensorOpeningTerm}`
and `CertiFri.P3.{prunedMmcs, baseHasherSep, ext3HasherSep}`.

Entrypoints:
- `verifyFriTensorWith`: tensor-batched FRI verification (`FriBatching::Tensor`).
- `verifyShard`: verifies one shard proof under the shared batch challenger and `(β, γ)`,
  returning the shard's LogUp residual (`intermediateAccumulators.back!`).
- `verifyBatch`: verifies a full `BatchProof` against `StarkSystem`, checking preamble
  bounds, `MEMSEG` closure pairs, every shard's AIR/LogUp OOD & FRI opening proof,
  global LogUp vanishing (`total == 0`), and returning the concatenated batch claims.
- `verifyBatchBytes`: end-to-end byte verifier `(vkBytes, claimsBytes, proofBytes) → Bool`.
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3

/-- Extract the indices of active circuits in canonical order. -/
def activeCircuitIndices (active : Array Bool) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:active.size] do
    if active[i]?.getD false then out := out.push i
  return out

/-- Flatten an `OpenedRound` (`[matrix][point][col]`) into the linear `values` array
expected by `CertiFri.Fri` and observed into the PCS transcript. -/
private def pushOpenedRound (vals : Array EF) (round : OpenedRound) : Array EF :=
  round.foldl (init := vals) fun acc mat =>
    mat.foldl (init := acc) fun acc' pt =>
      pt.foldl (init := acc') fun acc'' v => acc''.push v

/-- Annotate each `PointRef` in `Fri.pointRefs logBlowup shape` with its `pointIdx`
and starting `valueOffset` in the flat `values` array. -/
private def pointRefEntries (logBlowup : Nat) (shape : Fri.ClaimShape) :
    List (Fri.PointRef × Nat × Nat) := Id.run do
  let mut out : List (Fri.PointRef × Nat × Nat) := []
  let mut ptIdx : Nat := 0
  let mut valOff : Nat := 0
  for p in Fri.pointRefs logBlowup shape do
    out := out ++ [(p, ptIdx, valOff)]
    ptIdx := ptIdx + 1
    valOff := valOff + p.width
  return out

/-- Reduced opening for one height level under `FriBatching::Tensor`, accumulating
`openWeights[oIdx] * tensorColAcc colWeights claimed opened * (z - x)⁻¹` in canonical
`pointRefs` order (`Pcs.lean:442-498`, `CertiFri.Fri.tensorOpeningTerm`). -/
private def reducedOpeningTensorLevel (sched : Fri.TensorSchedule EF) (x : EF)
    (points values : Array EF) (rows : Array (Array (Array F)))
    (levelPts : List (Fri.PointRef × Nat × Nat)) : EF :=
  (levelPts.zipIdx).foldl (init := 0) fun acc ((p, pointIdx, valOff), oIdx) =>
    let z := points.getD pointIdx 0
    let claimed := values.extract valOff (valOff + p.width)
    let opened := (rows.getD p.batch #[]).getD p.matrix #[]
    let openW := sched.openWeights.getD oIdx 0
    acc + Fri.tensorOpeningTerm sched.colWeights openW z x claimed opened

/-- Per-query checks under `FriBatching::Tensor` (parity with `CertiFri.Fri.checkQuery`
and `Pcs.lean:667-689`). -/
private def checkQueryTensor (params : FriParams) (shape : Fri.ClaimShape)
    (levelPts : Nat → List (Fri.PointRef × Nat × Nat))
    (points values : Array EF)
    (proof : FriProof F EF D (PrunedPaths D) (PrunedPaths D))
    (ch : TensorFriChallenges EF) (t index : Nat) : Fri.QueryResult EF :=
  let n := Fri.logMaxHeight params.logBlowup shape
  let rounds := Fri.numRounds params shape
  let rows := Fri.queryRows proof t
  let ros := Array.ofFn (n := rounds + 1) fun j =>
    reducedOpeningTensorLevel ch.schedule
      (Fri.cosetPoint (F := F) n j.val (index >>> j.val))
      points values rows (levelPts j.val)
  let chain := Fri.foldChain (F := F) n ros (fun i => Fri.sibling proof i t) ch.betas index rounds
  let distinct := (Fri.pointRefs params.logBlowup shape).zipIdx.all fun (p, pointIdx) =>
    !(points.getD pointIdx 0 -
      Fri.cosetPoint (F := F) n (n - p.logHeight) (index >>> (n - p.logHeight)) == 0)
  let constOk := params.logFinalPolyLen != 0 || ros.getD rounds 0 == 0
  let finalOk := chain.1 ==
    CertiFri.horner proof.finalPoly
      (ExtensionOps.embed (Fri.domainPoint (F := F) n rounds (index >>> rounds)))
  { ok := distinct && constOk && finalOk, rows := chain.2 }

/-- Full `FriBatching::Tensor` FRI verification given pre-derived `TensorFriChallenges`,
reusing `CertiFri.Fri.{inputChecks, commitChecks, foldChain}` with domain-separated
`prunedMmcs` (`baseHasherSep .v6Batch`, `ext3HasherSep .v6Batch`). -/
def verifyFriTensorWith (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D)
    (params : FriParams) (shape : Fri.ClaimShape) (commitments : Array D)
    (points values : Array EF)
    (proof : FriProof F EF D inputMmcs.MultiProof friMmcs.MultiProof)
    (ch : TensorFriChallenges EF) : Bool :=
  let n := Fri.logMaxHeight params.logBlowup shape
  let rounds := Fri.numRounds params shape
  let entries := pointRefEntries params.logBlowup shape
  let levelArr := Array.ofFn (n := rounds + 1) fun j =>
    entries.filter fun (p, _, _) => p.logHeight + j.val == n
  let results := Array.ofFn (n := params.numQueries) fun t =>
    let idx := ch.indices.getD t.val 0
    let rows := Fri.queryRows proof t.val
    let ros := Array.ofFn (n := rounds + 1) fun j =>
      reducedOpeningTensorLevel ch.schedule
        (Fri.cosetPoint (F := F) n j.val (idx >>> j.val))
        points values rows (levelArr.getD j.val [])
    let chain := Fri.foldChain (F := F) n ros (fun i => Fri.sibling proof i t.val) ch.betas idx rounds
    let distinct := (Fri.pointRefs params.logBlowup shape).zipIdx.all fun (p, pointIdx) =>
      !(points.getD pointIdx 0 -
        Fri.cosetPoint (F := F) n (n - p.logHeight) (idx >>> (n - p.logHeight)) == 0)
    let constOk := params.logFinalPolyLen != 0 || ros.getD rounds 0 == 0
    let finalOk := chain.1 ==
      CertiFri.horner proof.finalPoly
        (ExtensionOps.embed (Fri.domainPoint (F := F) n rounds (idx >>> rounds)))
    ({ ok := distinct && constOk && finalOk, rows := chain.2 } : Fri.QueryResult EF)
  ch.powOk && ch.indices.size == params.numQueries
    && (List.range params.numQueries).all (fun t => decide (ch.indices.getD t 0 < 2 ^ n))
    && Fri.inputChecks inputMmcs params shape commitments proof.inputOpenings ch.indices
    && results.all (·.ok)
    && Fri.commitChecks friMmcs params.numQueries n rounds proof.commitPhaseCommits
        proof.commitPhaseOpenings ch.indices (results.map (·.rows))

/-- Build the `ClaimShape`, `commitments`, `points`, and `values` arrays matching
`multi-stark/src/verifier.rs` (`stage1`, `stage2`, `quotient`, optional `preprocessed`).
All array accesses are bounds-checked via `arr[i]?` (no panicking `[i]!`).
When `allowInactivePrep = false` (production default), inactive preprocessed circuits are
rejected (matching `StarkVerifier.lean` and `batch.rs`). -/
def buildPcsInputsWithOpts? (sys : StarkSystem) (activeIndices : Array Nat) (proof : ShardProof)
    (zeta : EF) (allowInactivePrep : Bool := false) :
    Option (Fri.ClaimShape × Array D × Array EF × Array EF) := do
  let numActive := activeIndices.size
  if proof.active.size != sys.circuits.size
      || sys.preprocessedIndices.size != sys.circuits.size then
    none
  if proof.stage1OpenedValues.size != numActive
      || proof.stage2OpenedValues.size != numActive
      || proof.quotientOpenedValues.size != numActive
      || proof.logDegrees.size != numActive then
    none
  if proof.commitments.stage1Trace.size != 1
      || proof.commitments.stage2Trace.size != 1
      || proof.commitments.quotientChunks.size != 1 then
    none

  let mut s1Shape : List Fri.MatrixShape := []
  let mut s2Shape : List Fri.MatrixShape := []
  let mut qShape : List Fri.MatrixShape := []
  let mut points : Array EF := #[]

  -- Round 0: Stage 1 (each active circuit opened at [ζ, ζ·g])
  for pos in [0:numActive] do
    let ci ← activeIndices[pos]?
    let c ← sys.circuits[ci]?
    let ld ← proof.logDegrees[pos]?
    let g : F := TwoAdicOps.twoAdicGenerator ld
    let zetaNext := zeta.mul (GoldilocksExt3.embed g)
    let pts ← proof.stage1OpenedValues[pos]?
    if pts.size != 2 then none
    let p0 ← pts[0]?
    let p1 ← pts[1]?
    if p0.size != c.mainWidth || p1.size != c.mainWidth then none
    s1Shape := s1Shape ++ [{ logDegree := ld, width := c.mainWidth, numPoints := 2 }]
    points := points.push zeta |>.push zetaNext

  -- Round 1: Stage 2 (each active circuit opened at [ζ, ζ·g])
  for pos in [0:numActive] do
    let ci ← activeIndices[pos]?
    let c ← sys.circuits[ci]?
    let ld ← proof.logDegrees[pos]?
    let g : F := TwoAdicOps.twoAdicGenerator ld
    let zetaNext := zeta.mul (GoldilocksExt3.embed g)
    let pts ← proof.stage2OpenedValues[pos]?
    if pts.size != 2 then none
    let p0 ← pts[0]?
    let p1 ← pts[1]?
    if p0.size != c.stage2Width || p1.size != c.stage2Width then none
    s2Shape := s2Shape ++ [{ logDegree := ld, width := c.stage2Width, numPoints := 2 }]
    points := points.push zeta |>.push zetaNext

  -- Round 2: Quotient chunks (each active circuit opened at [ζ], width = 3 * quotientDegree for Fp^3)
  for pos in [0:numActive] do
    let ci ← activeIndices[pos]?
    let c ← sys.circuits[ci]?
    let ld ← proof.logDegrees[pos]?
    let qWidth := 3 * c.quotientDegree
    let pts ← proof.quotientOpenedValues[pos]?
    if pts.size != 1 then none
    let p0 ← pts[0]?
    if p0.size != qWidth then none
    qShape := qShape ++ [{ logDegree := ld, width := qWidth, numPoints := 1 }]
    points := points.push zeta

  let s1Root ← proof.commitments.stage1Trace[0]?
  let s2Root ← proof.commitments.stage2Trace[0]?
  let qRoot ← proof.commitments.quotientChunks[0]?
  let mut shape : Fri.ClaimShape := [s1Shape, s2Shape, qShape]
  let mut commits : Array D := #[s1Root, s2Root, qRoot]
  let mut values : Array EF := #[]
  values := pushOpenedRound values proof.stage1OpenedValues
  values := pushOpenedRound values proof.stage2OpenedValues
  values := pushOpenedRound values proof.quotientOpenedValues

  -- Round 3 (optional): Preprocessed traces in canonical slot order
  match sys.preprocessedCommit, proof.preprocessedOpenedValues with
  | none, none => pure ()
  | some prepCap, some prepOpened =>
    if prepCap.size != 1 then none
    let prepRoot ← prepCap[0]?
    let mut activePos : Array (Option Nat) := Array.replicate sys.circuits.size none
    for pos in [0:numActive] do
      let ci ← activeIndices[pos]?
      if ci ≥ activePos.size then none
      activePos := activePos.setIfInBounds ci (some pos)
    let mut prepShape : List Fri.MatrixShape := []
    let mut expectedSlot := 0
    for ci in [0:sys.circuits.size] do
      let slotOpt ← sys.preprocessedIndices[ci]?
      if let some slot := slotOpt then
        if slot != expectedSlot then none
        expectedSlot := expectedSlot + 1
        let c ← sys.circuits[ci]?
        if c.preprocessedHeight == 0 then none
        let prepLogDeg := Nat.log2 c.preprocessedHeight
        if (1 <<< prepLogDeg) != c.preprocessedHeight then none
        let pts ← prepOpened[slot]?
        let posOpt ← activePos[ci]?
        match posOpt with
        | some pos =>
          let ld ← proof.logDegrees[pos]?
          if ld != prepLogDeg then none
          if pts.size != 2 then none
          let p0 ← pts[0]?
          let p1 ← pts[1]?
          if p0.size != c.preprocessedWidth || p1.size != c.preprocessedWidth then none
          let g : F := TwoAdicOps.twoAdicGenerator ld
          let zetaNext := zeta.mul (GoldilocksExt3.embed g)
          prepShape := prepShape ++ [{ logDegree := ld, width := c.preprocessedWidth, numPoints := 2 }]
          points := points.push zeta |>.push zetaNext
        | none =>
          if !allowInactivePrep then none
          if pts.size != 1 then none
          let p0 ← pts[0]?
          if p0.size != c.preprocessedWidth then none
          prepShape := prepShape ++ [{ logDegree := prepLogDeg, width := c.preprocessedWidth, numPoints := 1 }]
          points := points.push zeta
    if prepOpened.size != expectedSlot then none
    shape := shape ++ [prepShape]
    commits := commits.push prepRoot
    values := pushOpenedRound values prepOpened
  | _, _ => none

  pure (shape, commits, points, values)

/-- Production PCS input builder (strictly rejecting inactive preprocessed circuits). -/
def buildPcsInputs? (sys : StarkSystem) (activeIndices : Array Nat) (proof : ShardProof)
    (zeta : EF) : Option (Fri.ClaimShape × Array D × Array EF × Array EF) :=
  buildPcsInputsWithOpts? sys activeIndices proof zeta false

/-- Verify one shard of a Protocol `v6` batch proof under the shared batch challenger state
and `(β, γ)`. Returns the shard's final LogUp residual accumulator on acceptance.
When `allowInactivePrep = false` (production default), inactive preprocessed circuits are rejected. -/
def verifyShardWithOpts (sys : StarkSystem) (header : ShardHeader) (shardIdx : Nat)
    (proof : ShardProof) (batchState : ChallengerState) (beta gamma : EF)
    (allowInactivePrep : Bool := false) : Option EF := do
  if header.active != proof.active
      || header.stage1Trace != proof.commitments.stage1Trace
      || header.logDegrees != proof.logDegrees then
    none
  let activeIndices := activeCircuitIndices proof.active
  let numActive := activeIndices.size
  if numActive == 0 || proof.intermediateAccumulators.size != numActive then none

  -- Per-shard Fiat–Shamir (`α_air`, `ζ`)
  let (alphaAir, zeta, postZeta) ← shardAirChallenges batchState shardIdx proof
  if zeta == GoldilocksExt3.zero then none

  -- Build PCS inputs and run `verifyFriTensorWith` with `v6Batch` domain-separated `prunedMmcs`
  let (shape, commits, points, values) ←
    buildPcsInputsWithOpts? sys activeIndices proof zeta allowInactivePrep
  let friParams := sys.params.toFriParams
  if !Fri.shapeOk (F := F) friParams shape commits points values proof.openingProof then none
  let friCh ← shardFriChallenges postZeta friParams shape values proof.openingProof
  let inputMmcs := prunedMmcs (baseHasherSep .v6Batch)
  let friMmcs := prunedMmcs (ext3HasherSep .v6Batch)
  if !verifyFriTensorWith inputMmcs friMmcs friParams shape commits points values proof.openingProof friCh then
    none

  -- OOD AIR + LogUp constraint verification across all active circuits (all accesses bounds-checked)
  let mut accPrev ← claimsAccumulator? beta gamma header.claims
  for pos in [0:numActive] do
    let ci ← activeIndices[pos]?
    let c ← sys.circuits[ci]?
    let ld ← proof.logDegrees[pos]?
    let accNext ← proof.intermediateAccumulators[pos]?
    let s1 ← proof.stage1OpenedValues[pos]?
    let s1Cur ← s1[0]?
    let s1Next ← s1[1]?
    let s2 ← proof.stage2OpenedValues[pos]?
    let s2Cur ← s2[0]?
    let s2Next ← s2[1]?
    let qPts ← proof.quotientOpenedValues[pos]?
    let qRow ← qPts[0]?
    let prepSlot ← sys.preprocessedIndices[ci]?
    let (prepCur, prepNext) ← match prepSlot, proof.preprocessedOpenedValues with
      | some slot, some prepOpened =>
        let pts ← prepOpened[slot]?
        let p0 ← pts[0]?
        let p1 ← pts[1]?
        pure (p0, p1)
      | none, _ => pure (#[], #[])
      | some _, none => none
    if !checkCircuitOod c ld prepCur prepNext s1Cur s1Next s2Cur s2Next qRow
        beta gamma accPrev accNext alphaAir zeta then
      none
    accPrev := accNext

  pure accPrev

/-- Production single-shard verifier (strictly rejecting inactive preprocessed circuits). -/
def verifyShard (sys : StarkSystem) (header : ShardHeader) (shardIdx : Nat)
    (proof : ShardProof) (batchState : ChallengerState) (beta gamma : EF) : Option EF :=
  verifyShardWithOpts sys header shardIdx proof batchState beta gamma false

/-- Verify a full `BatchProof` against `sys`, returning the concatenated public claims
on acceptance. When `allowBelowFloor = false` and `allowInactivePrep = false`
(production defaults), enforces both the full Aiur 128-bit security floor and
active-preprocessed-circuit parity; the waivers are strictly for test-harness fixtures. -/
def verifyBatchWithFloor (sys : StarkSystem) (batch : BatchProof)
    (maxLogDeg : Nat := 32 - sys.params.logBlowup)
    (allowBelowFloor : Bool := false)
    (allowInactivePrep : Bool := false) : Option (Array (Array F)) := do
  if !validatePreambleWithFloor sys batch maxLogDeg allowBelowFloor allowInactivePrep then none
  let (batchState, beta, gamma) ← batchChallenger sys batch.preamble
  let mut total ← messagesAccumulator? beta gamma batch.preamble.messages
  let mut allClaims : Array (Array F) := #[]
  for s in [0:batch.preamble.headers.size] do
    let some h := batch.preamble.headers[s]? | none
    let some p := batch.proofs[s]? | none
    let residual ← verifyShardWithOpts sys h s p batchState beta gamma allowInactivePrep
    total := total.add residual
    allClaims := allClaims ++ h.claims
  if total != GoldilocksExt3.zero then none
  pure allClaims

/-- Verify a full `BatchProof` against `sys` under production security-floor and
active-preprocessed enforcement, returning the concatenated public claims on acceptance. -/
def verifyBatch (sys : StarkSystem) (batch : BatchProof)
    (maxLogDeg : Nat := 32 - sys.params.logBlowup) : Option (Array (Array F)) :=
  verifyBatchWithFloor sys batch maxLogDeg false false

/-- Byte-level Multi-STARK batch verifier with explicit test-harness waivers. -/
def verifyBatchBytesWithFloor (vkBytes claimsBytes proofBytes : ByteArray)
    (maxLogDeg? : Option Nat := none)
    (allowBelowFloor : Bool := false)
    (allowInactivePrep : Bool := false) : Bool :=
  match StarkSystem.fromBytes vkBytes, decodeClaims claimsBytes, BatchProof.fromBytes proofBytes with
  | .ok sys, .ok expectedClaims, .ok batch =>
    let maxLog := maxLogDeg?.getD (32 - sys.params.logBlowup)
    match verifyBatchWithFloor sys batch maxLog allowBelowFloor allowInactivePrep with
    | some foundClaims => foundClaims == expectedClaims
    | none => false
  | _, _, _ => false

/-- End-to-end production byte-level Multi-STARK batch verifier (`vkBytes`, `claimsBytes`, `proofBytes`),
strictly enforcing the Aiur 128-bit security floor and rejecting inactive preprocessed circuits. -/
def verifyBatchBytes (vkBytes claimsBytes proofBytes : ByteArray)
    (maxLogDeg? : Option Nat := none) : Bool :=
  verifyBatchBytesWithFloor vkBytes claimsBytes proofBytes maxLogDeg? false false

end Ix.Cert.MultiStark
