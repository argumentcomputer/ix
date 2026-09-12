module
public import Ix.MultiStark.Verify.Key.Basic

/-! Total structural admission for canonical keys. This is not an approval
policy or a cryptographic verification step. PCS cap geometry and proof shape
are checked in their own phases. All graph reads are checked, including roots
and lookup arguments; native decoder panics are not part of this interface. -/

public section
@[expose] section

namespace MultiStark.Verify

inductive KeyError where
  | parameters | circuits | width | lookupGroup | reference | column | publicIndex
  | degree | preprocessing
  deriving BEq, DecidableEq, Repr, Inhabited

def Parameters.admissible (params : Parameters) : Bool :=
  params.words.all (· < 65536) && params.logBlowup ≤ 32 && params.capHeight ≤ 32 &&
    params.logFinalPolyLen + params.logBlowup ≤ 32 &&
    0 < params.maxLogArity && params.maxLogArity ≤ 32 && 0 < params.numQueries &&
    params.commitPowBits < 64 && params.queryPowBits < 64

namespace KeyValidation

def getDegree (degrees : Array Nat) (index : Nat) : Except KeyError Nat :=
  match degrees[index]? with | some degree => .ok degree | none => .error .reference

/-- The order check follows from reading only the degrees already accumulated
for earlier nodes. Forward references, cycles and self references all fail. -/
def nodeDegree (circuit : Circuit) (degrees : Array Nat) : Node → Except KeyError Nat
  | .const _ | .transition => .ok 0
  | .first | .last => .ok 1
  | .public index => if index < Circuit.numPublics then .ok 0 else .error .publicIndex
  | .var source _ column =>
    let width := match source with
      | .preprocessed => circuit.preprocessedWidth
      | .main => circuit.mainWidth
      | .stage2 => circuit.stage2Width
    if column < width then .ok 1 else .error .column
  | .add left right | .sub left right => do
    return max (← getDegree degrees left) (← getDegree degrees right)
  | .mul left right => do return (← getDegree degrees left) + (← getDegree degrees right)
  | .neg child => getDegree degrees child

def degrees (circuit : Circuit) : Except KeyError (Array Nat) := do
  let mut result := #[]
  for node in circuit.nodes do
    let degree ← nodeDegree circuit result node
    -- The supported v5 class bounds every intermediate degree as well as
    -- the serialized maximum, preventing adversarial exponential integers.
    if degree ≥ 65536 then throw .degree
    result := result.push degree
  return result

def maxRoots (degrees : Array Nat) (roots : Array Nat) : Except KeyError Nat := do
  let mut result := 0
  for root in roots do result := max result (← getDegree degrees root)
  return result

/-- Native analytic logUp degree: product of grouped messages times the
accumulator difference, minus each multiplicity times the other messages. -/
def groupDegree (degrees : Array Nat) (group : Array Lookup) : Except KeyError Nat := do
  let mut messageDegrees := #[]
  let mut multiplicityDegrees := #[]
  let mut sum := 0
  for lookup in group do
    let message ← maxRoots degrees lookup.args
    let multiplicity ← getDegree degrees lookup.multiplicity
    messageDegrees := messageDegrees.push message
    multiplicityDegrees := multiplicityDegrees.push multiplicity
    sum := sum + message
  let mut result := sum + 1
  for (message, multiplicity) in messageDegrees.zip multiplicityDegrees do
    result := max result (multiplicity + sum - message)
  return result

def logupDegree (circuit : Circuit) (degrees : Array Nat) : Except KeyError Nat := do
  let groupSize := max 1 circuit.lookupGroupSize
  let mut result := 1
  for group in [0:circuit.lookupGroups] do
    let chunk := circuit.lookups.extract (group * groupSize) ((group + 1) * groupSize)
    result := max result (← groupDegree degrees chunk)
  return result

def circuit (params : Parameters) (circuit : Circuit) : Except KeyError Unit := do
  unless circuit.mainWidth < 65536 && circuit.preprocessedWidth < 65536 &&
      circuit.preprocessedHeight < 2 ^ 32 && circuit.nodes.size < 65536 &&
      circuit.zeros.size < 65536 && circuit.lookups.size < 65536 &&
      circuit.lookups.all (·.args.size < 65536) do throw .width
  unless 1 ≤ circuit.lookupGroupSize && circuit.lookupGroupSize ≤ 8 do throw .lookupGroup
  if circuit.preprocessedWidth == 0 then
    unless circuit.preprocessedHeight == 0 do throw .preprocessing
  else
    unless circuit.preprocessedHeight > 0 &&
        2 ^ circuit.preprocessedHeight.log2 == circuit.preprocessedHeight &&
        circuit.preprocessedHeight.log2 + params.logBlowup ≤ 32 do throw .preprocessing
  let degrees ← degrees circuit
  let userDegree ← maxRoots degrees circuit.zeros
  let lookupDegree ← logupDegree circuit degrees
  unless circuit.maxConstraintDegree == max userDegree lookupDegree &&
      circuit.maxConstraintDegree < 65536 &&
      circuit.maxConstraintDegree ≤ 2 ^ params.logBlowup + 1 do throw .degree

end KeyValidation

def validateKey (key : Key) : Except KeyError Unit := do
  unless key.params.admissible do throw .parameters
  unless key.circuits.size > 0 && key.circuits.size < 65536 &&
      key.preprocessedIndices.size == key.circuits.size do throw .circuits
  let count := (key.preprocessedIndices.filter Option.isSome).size
  match key.preprocessed with
  | none => unless count == 0 do throw .preprocessing
  | some cap => unless count > 0 && cap.size > 0 do throw .preprocessing
  let mut nextSlot := 0
  for (circuit, index) in key.circuits.zip key.preprocessedIndices do
    KeyValidation.circuit key.params circuit
    match index with
    | none => unless circuit.preprocessedWidth == 0 do throw .preprocessing
    | some index =>
      -- Native PCS round reconstruction enumerates preprocessed circuits in
      -- circuit order. Require that exact builder map, not a permutation.
      unless circuit.preprocessedWidth > 0 && index < count && index == nextSlot do
        throw .preprocessing
      nextSlot := nextSlot + 1

/-- Checked admission evidence, not a statement that the key is approved. -/
structure AdmittedKey (key : Key) : Type where
  validated : validateKey key = .ok ()

def admitKey (key : Key) : Except KeyError (AdmittedKey key) :=
  match validated : validateKey key with
  | .error error => .error error
  | .ok () => .ok ⟨validated⟩

end MultiStark.Verify
