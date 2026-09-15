module
public import Ix.MultiStark.Verify.Fri.Basic

public section
@[expose] section

namespace MultiStark.Verify.Fri

structure ReducedOpening where
  logHeight : Nat
  value : Ext
  deriving BEq, DecidableEq, Repr

def authenticateInputBatches (params : Parameters) (challenges : Challenges)
    (openings : Array BatchOpening) : List Pcs.Round → Nat → Except Error Unit
  | [], _ => .ok ()
  | round :: rounds, batch => do
    ensure (!round.matrices.isEmpty) .empty
    let dimensions := round.matrices.map fun matrix =>
      Mmcs.Dimension.mk (matrix.logDegree + params.logBlowup) matrix.width
    let logBatch := Mmcs.maxLogHeight dimensions
    ensure (logBatch ≤ challenges.logGlobal) .height
    let indices := challenges.indices.map (· / 2 ^ (challenges.logGlobal - logBatch))
    let opening ← getAt openings batch
    (Mmcs.check params.capHeight dimensions round.commitment indices opening).mapError (.inputMmcs batch)
    authenticateInputBatches params challenges openings rounds (batch + 1)

def authenticateInputs (params : Parameters) (challenges : Challenges)
    (rounds : Array Pcs.Round) (openings : Array BatchOpening) : Except Error Unit := do
  ensure (openings.size == rounds.size) .count
  ensure (challenges.logGlobal ≤ 32 && params.logBlowup ≤ 32) .height
  ensure (challenges.indices.size == params.numQueries) .query
  ensure (challenges.indices.all (· < 2 ^ challenges.logGlobal)) .query
  authenticateInputBatches params challenges openings rounds.toList 0

/-- The exact coset point for a bit-reversed matrix query. Input LDEs use
the native multiplicative generator 7; FRI folding rows use unshifted groups. -/
def queryPoint (index logGlobal logHeight : Nat) : Except Error Ext := do
  ensure (logHeight ≤ logGlobal && logGlobal ≤ 32 && index < 2 ^ logGlobal) .height
  let g ← (Arithmetic.twoAdicGenerator logHeight).mapError Error.arithmetic
  let reduced := index / 2 ^ (logGlobal - logHeight)
  return Arithmetic.embed ((7 : Field).mul (g.pow (reverseBits reduced logHeight)))

abbrev ReductionBuckets := Array (Option (Ext × Ext))

def coordinateStep (alpha reciprocal : Ext) (state : Ext × Ext) (coordinate : Field × Ext) : Ext × Ext :=
  (state.1.mul alpha, state.2.add (state.1.mul ((coordinate.2.sub (Arithmetic.embed coordinate.1)).mul reciprocal)))

def reduceCoordinatePairs (alpha reciprocal : Ext) : List (Field × Ext) → (Ext × Ext) → Ext × Ext
  | [], state => state
  | coordinate :: coordinates, state =>
    reduceCoordinatePairs alpha reciprocal coordinates (coordinateStep alpha reciprocal state coordinate)

def reduceCoordinates (alpha reciprocal : Ext) (row : List Field) (opened : List Ext)
    (power value : Ext) : Except Error (Ext × Ext) := do
  ensure (row.length == opened.length) .width
  return reduceCoordinatePairs alpha reciprocal (row.zip opened) (power, value)

def reducePoints (alpha x : Ext) (width : Nat) (row : Array Field) :
    List Pcs.PointOpening → Ext → Ext → Except Error (Ext × Ext)
  | [], power, value => .ok (power, value)
  | opening :: openings, power, value => do
    ensure (row.size == width && row.size == opening.values.size) .width
    let reciprocal ← (Arithmetic.inverse (opening.point.sub x)).mapError Error.arithmetic
    let (power, value) ← reduceCoordinates alpha reciprocal row.toList opening.values.toList power value
    reducePoints alpha x width row openings power value

def reduceMatrix (params : Parameters) (challenges : Challenges) (index : Nat)
    (matrix : Pcs.Matrix) (row : Array Field) (byHeight : ReductionBuckets) : Except Error ReductionBuckets := do
  let height := matrix.logDegree + params.logBlowup
  let x ← queryPoint index challenges.logGlobal height
  let (power, value) := (← getAt byHeight height).getD (Arithmetic.one, Arithmetic.zero)
  ensure (!matrix.points.isEmpty) .point
  let reduced ← reducePoints challenges.alpha x matrix.width row matrix.points.toList power value
  return byHeight.set! height (some reduced)

def reduceMatrices (params : Parameters) (challenges : Challenges) (index : Nat) :
    List Pcs.Matrix → List (Array Field) → ReductionBuckets → Except Error ReductionBuckets
  | [], [], byHeight => .ok byHeight
  | matrix :: matrices, row :: rows, byHeight => do
    let byHeight ← reduceMatrix params challenges index matrix row byHeight
    reduceMatrices params challenges index matrices rows byHeight
  | _, _, _ => .error .count

def reduceBatches (params : Parameters) (challenges : Challenges) (index query : Nat)
    (openings : Array BatchOpening) : List Pcs.Round → Nat → ReductionBuckets → Except Error ReductionBuckets
  | [], _, byHeight => .ok byHeight
  | round :: rounds, batch, byHeight => do
    let rows ← getAt (← getAt openings batch).values query
    ensure (rows.size == round.matrices.size) .count
    let byHeight ← reduceMatrices params challenges index round.matrices.toList rows.toList byHeight
    reduceBatches params challenges index query openings rounds (batch + 1) byHeight

def checkConstant (byHeight : ReductionBuckets) (height : Nat) : Except Error Unit := do
  match ← getAt byHeight height with
  | some (_, value) => ensure (value == Arithmetic.zero) .constant
  | none => pure ()

def collectReduced (byHeight : ReductionBuckets) : List Nat → Except Error (List ReducedOpening)
  | [] => .ok []
  | height :: heights => do
    let value ← getAt byHeight height
    let rest ← collectReduced byHeight heights
    return match value with
      | some (_, value) => ⟨height, value⟩ :: rest
      | none => rest

def reduceQuery (params : Parameters) (challenges : Challenges) (rounds : Array Pcs.Round)
    (openings : Array BatchOpening) (query : Nat) : Except Error (Array ReducedOpening) := do
  let index ← getAt challenges.indices query
  let byHeight ← reduceBatches params challenges index query openings rounds.toList 0 (Array.replicate 33 none)
  checkConstant byHeight params.logBlowup
  return (← collectReduced byHeight ((List.range 33).map (32 - ·))).toArray

def reduceQueries (params : Parameters) (challenges : Challenges) (rounds : Array Pcs.Round)
    (openings : Array BatchOpening) : Nat → Nat → Except Error (List (Array ReducedOpening))
  | _, 0 => .ok []
  | query, remaining + 1 => do
    let reduced ← reduceQuery params challenges rounds openings query
    let rest ← reduceQueries params challenges rounds openings (query + 1) remaining
    return reduced :: rest

/-- Authenticate every input batch before any reduced opening is used by a
FRI fold. Alpha powers continue across all matrices/points at a given height. -/
def openInputs (params : Parameters) (challenges : Challenges)
    (rounds : Array Pcs.Round) (openings : Array BatchOpening) :
    Except Error (Array (Array ReducedOpening)) := do
  authenticateInputs params challenges rounds openings
  return (← reduceQueries params challenges rounds openings 0 challenges.indices.size).toArray

end MultiStark.Verify.Fri
