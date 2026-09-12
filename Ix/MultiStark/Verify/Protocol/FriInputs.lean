module
public import Ix.MultiStark.Verify.Fri.Inputs
public import Ix.MultiStark.Verify.Protocol.FriFold
public import Ix.MultiStark.Verify.Protocol.Mmcs

/-! Input PCS authentication and the literal ordered quotient reduction.
Each height bucket holds its next alpha power and accumulated value. Matrix
widths/points and query indices are verifier inputs, never inferred from a
proof row. Bucket updates preserve all other heights, and the output lists
every present bucket in descending height order. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

def AuthenticatedBatches (params : Parameters) (challenges : Fri.Challenges)
    (openings : Array BatchOpening) : List Pcs.Round → Nat → Prop
  | [], _ => True
  | round :: rounds, batch =>
    let dimensions := round.matrices.map (fun matrix =>
      Mmcs.Dimension.mk (matrix.logDegree + params.logBlowup) matrix.width)
    let logBatch := dimensions.foldl (fun height dimension => max height dimension.logHeight) 0
    round.matrices ≠ #[] ∧ logBatch ≤ challenges.logGlobal ∧
      ∃ opening, openings[batch]? = some opening ∧
        MmcsAccepted params.capHeight dimensions round.commitment
          (challenges.indices.map (· / 2 ^ (challenges.logGlobal - logBatch))) opening ∧
        AuthenticatedBatches params challenges openings rounds (batch + 1)

def InputAuthenticated (params : Parameters) (challenges : Fri.Challenges)
    (rounds : Array Pcs.Round) (openings : Array BatchOpening) : Prop :=
  openings.size = rounds.size ∧ challenges.logGlobal ≤ 32 ∧ params.logBlowup ≤ 32 ∧
    challenges.indices.size = params.numQueries ∧
    (∀ index ∈ challenges.indices, index < 2 ^ challenges.logGlobal) ∧
    AuthenticatedBatches params challenges openings rounds.toList 0

def InputQueryPoint (index logGlobal logHeight : Nat) (result : Ext) : Prop :=
  logHeight ≤ logGlobal ∧ logGlobal ≤ 32 ∧ index < 2 ^ logGlobal ∧
    ∃ group, TwoAdicGenerator logHeight group ∧
      Arithmetic.embed ((7 : Field).mul
        (group.pow (bitReverse (index / 2 ^ (logGlobal - logHeight)) logHeight))) = result

/-- A literal left-to-right sum, with one alpha factor per coordinate.
The surrounding relation checks BOTH lengths before forming these pairs. -/
def CoordinateSum (alpha reciprocal : Ext) (coordinates : List (Field × Ext)) (initial : Ext × Ext) : Ext × Ext :=
  coordinates.foldl (fun (power, value) (atX, atZ) =>
    (power.mul alpha, value.add (power.mul ((atZ.sub (Arithmetic.embed atX)).mul reciprocal)))) initial

def CoordinateReduction (alpha reciprocal : Ext) (row : List Field) (opened : List Ext)
    (power value : Ext) (result : Ext × Ext) : Prop :=
  row.length = opened.length ∧ CoordinateSum alpha reciprocal (row.zip opened) (power, value) = result

def PointReduction (alpha x : Ext) (width : Nat) (row : Array Field) :
    List Pcs.PointOpening → Ext → Ext → Ext × Ext → Prop
  | [], power, value, result => (power, value) = result
  | opening :: openings, power, value, result =>
    row.size = width ∧ row.size = opening.values.size ∧
      ∃ reciprocal nextPower nextValue, ExtensionInverse (opening.point.sub x) reciprocal ∧
        CoordinateReduction alpha reciprocal row.toList opening.values.toList power value (nextPower, nextValue) ∧
        PointReduction alpha x width row openings nextPower nextValue result

def MatrixReduction (params : Parameters) (challenges : Fri.Challenges) (index : Nat)
    (matrix : Pcs.Matrix) (row : Array Field) (before after : Fri.ReductionBuckets) : Prop :=
  let height := matrix.logDegree + params.logBlowup
  ∃ x cell reduced, InputQueryPoint index challenges.logGlobal height x ∧
    before[height]? = some cell ∧ matrix.points ≠ #[] ∧
    PointReduction challenges.alpha x matrix.width row matrix.points.toList
      (cell.getD (Arithmetic.one, Arithmetic.zero)).1 (cell.getD (Arithmetic.one, Arithmetic.zero)).2 reduced ∧
    before.set! height (some reduced) = after

def MatrixReductions (params : Parameters) (challenges : Fri.Challenges) (index : Nat) :
    List Pcs.Matrix → List (Array Field) → Fri.ReductionBuckets → Fri.ReductionBuckets → Prop
  | [], [], before, after => before = after
  | matrix :: matrices, row :: rows, before, after =>
    ∃ middle, MatrixReduction params challenges index matrix row before middle ∧
      MatrixReductions params challenges index matrices rows middle after
  | _, _, _, _ => False

def BatchReductions (params : Parameters) (challenges : Fri.Challenges) (index query : Nat)
    (openings : Array BatchOpening) : List Pcs.Round → Nat → Fri.ReductionBuckets → Fri.ReductionBuckets → Prop
  | [], _, before, after => before = after
  | round :: rounds, batch, before, after =>
    ∃ opening rows middle, openings[batch]? = some opening ∧ opening.values[query]? = some rows ∧
      rows.size = round.matrices.size ∧ MatrixReductions params challenges index round.matrices.toList rows.toList before middle ∧
      BatchReductions params challenges index query openings rounds (batch + 1) middle after

def ConstantBucket (buckets : Fri.ReductionBuckets) (height : Nat) : Prop :=
  ∃ cell, buckets[height]? = some cell ∧
    match cell with
    | none => True
    | some (_, value) => value = Arithmetic.zero

def ReducedHeights (buckets : Fri.ReductionBuckets) : List Nat → List Fri.ReducedOpening → Prop
  | [], result => [] = result
  | height :: heights, result =>
    ∃ cell rest, buckets[height]? = some cell ∧ ReducedHeights buckets heights rest ∧
      (match cell with | none => rest | some (_, value) => ⟨height, value⟩ :: rest) = result

def ReducedQuery (params : Parameters) (challenges : Fri.Challenges) (rounds : Array Pcs.Round)
    (openings : Array BatchOpening) (query : Nat) (result : Array Fri.ReducedOpening) : Prop :=
  ∃ index buckets, challenges.indices[query]? = some index ∧
    BatchReductions params challenges index query openings rounds.toList 0 (Array.replicate 33 none) buckets ∧
    ConstantBucket buckets params.logBlowup ∧
    ReducedHeights buckets ((List.range 33).map (32 - ·)) result.toList

def ReducedQueries (params : Parameters) (challenges : Fri.Challenges) (rounds : Array Pcs.Round)
    (openings : Array BatchOpening) : Nat → Nat → List (Array Fri.ReducedOpening) → Prop
  | _, 0, result => [] = result
  | query, remaining + 1, result =>
    ∃ first rest, ReducedQuery params challenges rounds openings query first ∧
      ReducedQueries params challenges rounds openings (query + 1) remaining rest ∧ first :: rest = result

def InputsOpened (params : Parameters) (challenges : Fri.Challenges) (rounds : Array Pcs.Round)
    (openings : Array BatchOpening) (result : Array (Array Fri.ReducedOpening)) : Prop :=
  InputAuthenticated params challenges rounds openings ∧
    ReducedQueries params challenges rounds openings 0 challenges.indices.size result.toList

end MultiStark.Verify.Protocol
