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
  | .public index => do
    ensure (index < Circuit.numPublics) .publicIndex
    return 0
  | .var source _ column => do
    let width := match source with
      | .preprocessed => circuit.preprocessedWidth
      | .main => circuit.mainWidth
      | .stage2 => circuit.stage2Width
    ensure (column < width) .column
    return 1
  | .add left right | .sub left right => do
    return max (← getDegree degrees left) (← getDegree degrees right)
  | .mul left right => do return (← getDegree degrees left) + (← getDegree degrees right)
  | .neg child => getDegree degrees child

def degreesFrom (circuit : Circuit) : List Node → Array Nat → Except KeyError (Array Nat)
  | [], result => .ok result
  | node :: nodes, result => do
    let degree ← nodeDegree circuit result node
    -- The supported v5 class bounds every intermediate degree as well as
    -- the serialized maximum, preventing adversarial exponential integers.
    ensure (degree < 65536) .degree
    degreesFrom circuit nodes (result.push degree)

def degrees (circuit : Circuit) : Except KeyError (Array Nat) :=
  degreesFrom circuit circuit.nodes.toList #[]

def maxRootsFrom (degrees : Array Nat) : List Nat → Nat → Except KeyError Nat
  | [], result => .ok result
  | root :: roots, result => do
    let degree ← getDegree degrees root
    maxRootsFrom degrees roots (max result degree)

def maxRoots (degrees : Array Nat) (roots : Array Nat) : Except KeyError Nat :=
  maxRootsFrom degrees roots.toList 0

def lookupDegrees (degrees : Array Nat) : List Lookup → Except KeyError (List (Nat × Nat))
  | [] => .ok []
  | lookup :: lookups => do
    let message ← maxRoots degrees lookup.args
    let multiplicity ← getDegree degrees lookup.multiplicity
    let rest ← lookupDegrees degrees lookups
    return (message, multiplicity) :: rest

/-- Native analytic logUp degree: product of grouped messages times the
accumulator difference, minus each multiplicity times the other messages. -/
def groupDegree (degrees : Array Nat) (group : Array Lookup) : Except KeyError Nat := do
  let pairs ← lookupDegrees degrees group.toList
  let sum := (pairs.map Prod.fst).sum
  return pairs.foldl (fun result (message, multiplicity) => max result (multiplicity + sum - message)) (sum + 1)

def logupDegreeFrom (circuit : Circuit) (degrees : Array Nat) (groupSize : Nat) :
    Nat → Nat → Nat → Except KeyError Nat
  | _, 0, result => .ok result
  | group, remaining + 1, result => do
    let chunk := circuit.lookups.extract (group * groupSize) ((group + 1) * groupSize)
    let degree ← groupDegree degrees chunk
    logupDegreeFrom circuit degrees groupSize (group + 1) remaining (max result degree)

def logupDegree (circuit : Circuit) (degrees : Array Nat) : Except KeyError Nat :=
  logupDegreeFrom circuit degrees (max 1 circuit.lookupGroupSize) 0 circuit.lookupGroups 1

def circuit (params : Parameters) (circuit : Circuit) : Except KeyError Unit := do
  ensure (circuit.mainWidth < 65536 && circuit.preprocessedWidth < 65536 &&
      circuit.preprocessedHeight < 2 ^ 32 && circuit.nodes.size < 65536 &&
      circuit.zeros.size < 65536 && circuit.lookups.size < 65536 &&
      circuit.lookups.all (·.args.size < 65536)) .width
  ensure (1 ≤ circuit.lookupGroupSize && circuit.lookupGroupSize ≤ 8) .lookupGroup
  if circuit.preprocessedWidth == 0 then
    ensure (circuit.preprocessedHeight == 0) .preprocessing
  else
    ensure (circuit.preprocessedHeight > 0 &&
        2 ^ circuit.preprocessedHeight.log2 == circuit.preprocessedHeight &&
        circuit.preprocessedHeight.log2 + params.logBlowup ≤ 32) .preprocessing
  let degrees ← degrees circuit
  let userDegree ← maxRoots degrees circuit.zeros
  let lookupDegree ← logupDegree circuit degrees
  ensure (circuit.maxConstraintDegree == max userDegree lookupDegree &&
      circuit.maxConstraintDegree < 65536 &&
      circuit.maxConstraintDegree ≤ 2 ^ params.logBlowup + 1) .degree

def circuits (params : Parameters) (count : Nat) : List Circuit → List (Option Nat) → Nat → Except KeyError Unit
  | [], [], _ => .ok ()
  | value :: values, index :: indices, nextSlot => do
    circuit params value
    match index with
    | none =>
      ensure (value.preprocessedWidth == 0) .preprocessing
      circuits params count values indices nextSlot
    | some index =>
      -- The canonical preprocessing map enumerates table circuits in order.
      ensure (value.preprocessedWidth > 0 && index < count && index == nextSlot) .preprocessing
      circuits params count values indices (nextSlot + 1)
  | _, _, _ => .error .circuits

end KeyValidation

def validateKey (key : Key) : Except KeyError Unit := do
  ensure key.params.admissible .parameters
  ensure (key.circuits.size > 0 && key.circuits.size < 65536 &&
      key.preprocessedIndices.size == key.circuits.size) .circuits
  let count := (key.preprocessedIndices.filter Option.isSome).size
  match key.preprocessed with
  | none => ensure (count == 0) .preprocessing
  | some cap => ensure (count > 0 && cap.size > 0) .preprocessing
  KeyValidation.circuits key.params count key.circuits.toList key.preprocessedIndices.toList 0

/-- Checked admission evidence, not a statement that the key is approved. -/
structure AdmittedKey (key : Key) : Type where
  validated : validateKey key = .ok ()

def admitKey (key : Key) : Except KeyError (AdmittedKey key) :=
  match validated : validateKey key with
  | .error error => .error error
  | .ok () => .ok ⟨validated⟩

end MultiStark.Verify
