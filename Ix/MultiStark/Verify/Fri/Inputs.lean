module
public import Ix.MultiStark.Verify.Fri.Basic

public section
@[expose] section

namespace MultiStark.Verify.Fri

structure ReducedOpening where
  logHeight : Nat
  value : Ext
  deriving BEq, DecidableEq, Repr

def authenticateInputs (params : Parameters) (challenges : Challenges)
    (rounds : Array Pcs.Round) (openings : Array BatchOpening) : Except Error Unit := do
  unless openings.size == rounds.size do throw .count
  unless challenges.logGlobal ≤ 32 && params.logBlowup ≤ 32 do throw .height
  unless challenges.indices.size == params.numQueries do throw .query
  unless challenges.indices.all (· < 2 ^ challenges.logGlobal) do throw .query
  for batch in [0:rounds.size] do
    let round ← getAt rounds batch
    if round.matrices.isEmpty then throw .empty
    let dimensions := round.matrices.map fun matrix =>
      Mmcs.Dimension.mk (matrix.logDegree + params.logBlowup) matrix.width
    let logBatch := Mmcs.maxLogHeight dimensions
    unless logBatch ≤ challenges.logGlobal do throw .height
    let indices := challenges.indices.map (· / 2 ^ (challenges.logGlobal - logBatch))
    let opening ← getAt openings batch
    (Mmcs.check params.capHeight dimensions round.commitment indices opening).mapError (.inputMmcs batch)

/-- The exact coset point for a bit-reversed matrix query. Input LDEs use
the native multiplicative generator 7; FRI folding rows use unshifted groups. -/
def queryPoint (index logGlobal logHeight : Nat) : Except Error Ext := do
  unless logHeight ≤ logGlobal && logGlobal ≤ 32 && index < 2 ^ logGlobal do throw .height
  let g ← (Arithmetic.twoAdicGenerator logHeight).mapError Error.arithmetic
  let reduced := index / 2 ^ (logGlobal - logHeight)
  return Arithmetic.embed ((7 : Field).mul (g.pow (reverseBits reduced logHeight)))

def reduceQuery (params : Parameters) (challenges : Challenges) (rounds : Array Pcs.Round)
    (openings : Array BatchOpening) (query : Nat) : Except Error (Array ReducedOpening) := do
  let index ← getAt challenges.indices query
  let mut byHeight : Array (Option (Ext × Ext)) := Array.replicate 33 none
  for batch in [0:rounds.size] do
    let round ← getAt rounds batch
    let rows ← getAt (← getAt openings batch).values query
    unless rows.size == round.matrices.size do throw .count
    for matrixIndex in [0:round.matrices.size] do
      let matrix ← getAt round.matrices matrixIndex
      let row ← getAt rows matrixIndex
      let height := matrix.logDegree + params.logBlowup
      let x ← queryPoint index challenges.logGlobal height
      let (initialPower, initialValue) := (← getAt byHeight height).getD (Arithmetic.one, Arithmetic.zero)
      let mut alphaPower := initialPower
      let mut value := initialValue
      if matrix.points.isEmpty then throw .point
      for opening in matrix.points do
        unless row.size == matrix.width && row.size == opening.values.size do throw .width
        let denominator ← (Arithmetic.inverse (opening.point.sub x)).mapError Error.arithmetic
        for column in [0:row.size] do
          let atX := Arithmetic.embed (← getAt row column)
          let atZ ← getAt opening.values column
          value := value.add (alphaPower.mul ((atZ.sub atX).mul denominator))
          alphaPower := alphaPower.mul challenges.alpha
      byHeight := byHeight.set! height (some (alphaPower, value))
  match ← getAt byHeight params.logBlowup with
  | some (_, value) => unless value == Arithmetic.zero do throw .constant
  | none => pure ()
  let mut reduced := #[]
  for offset in [0:33] do
    let height := 32 - offset
    match ← getAt byHeight height with
    | some (_, value) => reduced := reduced.push ⟨height, value⟩
    | none => pure ()
  return reduced

/-- Authenticate every input batch before any reduced opening is used by a
FRI fold. Alpha powers continue across all matrices/points at a given height. -/
def openInputs (params : Parameters) (challenges : Challenges)
    (rounds : Array Pcs.Round) (openings : Array BatchOpening) :
    Except Error (Array (Array ReducedOpening)) := do
  authenticateInputs params challenges rounds openings
  let mut reduced := #[]
  for query in [0:challenges.indices.size] do
    reduced := reduced.push (← reduceQuery params challenges rounds openings query)
  return reduced

end MultiStark.Verify.Fri
