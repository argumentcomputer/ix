module
public import Ix.MultiStark.Verify.Key

/-! Structural admission for the supported dense-v5 key class. Degrees are
equations over earlier graph positions; the analytic lookup degree and the
canonical preprocessing-slot map are part of the relation, not trusted
redundant metadata. Admissibility does not approve a key or its application. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

def ParametersAdmissible (params : Parameters) : Prop :=
  (∀ word ∈ params.words, word < 65536) ∧ params.logBlowup ≤ 32 ∧ params.capHeight ≤ 32 ∧
    params.logFinalPolyLen + params.logBlowup ≤ 32 ∧
    0 < params.maxLogArity ∧ params.maxLogArity ≤ 32 ∧ 0 < params.numQueries ∧
    params.commitPowBits < 64 ∧ params.queryPowBits < 64

def KeyNodeDegree (circuit : Circuit) (degrees : Array Nat) : Node → Nat → Prop
  | .const _, result | .transition, result => 0 = result
  | .first, result | .last, result => 1 = result
  | .public index, result => index < Circuit.numPublics ∧ 0 = result
  | .var source _ column, result =>
    let width := match source with
      | .preprocessed => circuit.preprocessedWidth
      | .main => circuit.mainWidth
      | .stage2 => circuit.stage2Width
    column < width ∧ 1 = result
  | .add left right, result | .sub left right, result =>
    ∃ l r, degrees[left]? = some l ∧ degrees[right]? = some r ∧ max l r = result
  | .mul left right, result =>
    ∃ l r, degrees[left]? = some l ∧ degrees[right]? = some r ∧ l + r = result
  | .neg child, result => degrees[child]? = some result

def KeyDegrees (circuit : Circuit) : List Node → Array Nat → Array Nat → Prop
  | [], before, after => before = after
  | node :: nodes, before, after =>
    ∃ degree, KeyNodeDegree circuit before node degree ∧ degree < 65536 ∧
      KeyDegrees circuit nodes (before.push degree) after

def RootDegree (degrees : Array Nat) : List Nat → Nat → Nat → Prop
  | [], initial, result => initial = result
  | root :: roots, initial, result =>
    ∃ degree, degrees[root]? = some degree ∧ RootDegree degrees roots (max initial degree) result

def LookupDegrees (degrees : Array Nat) : List Lookup → List (Nat × Nat) → Prop
  | [], [] => True
  | lookup :: lookups, (message, multiplicity) :: pairs =>
    RootDegree degrees lookup.args.toList 0 message ∧ degrees[lookup.multiplicity]? = some multiplicity ∧
      LookupDegrees degrees lookups pairs
  | _, _ => False

def GroupDegree (degrees : Array Nat) (group : Array Lookup) (result : Nat) : Prop :=
  ∃ pairs, LookupDegrees degrees group.toList pairs ∧
    let sum := (pairs.map Prod.fst).sum
    pairs.foldl (fun degree (message, multiplicity) => max degree (multiplicity + sum - message)) (sum + 1) = result

def LogupDegree (circuit : Circuit) (degrees : Array Nat) (groupSize : Nat) : Nat → Nat → Nat → Nat → Prop
  | _, 0, initial, result => initial = result
  | group, remaining + 1, initial, result =>
    ∃ degree, GroupDegree degrees (circuit.lookups.extract (group * groupSize) ((group + 1) * groupSize)) degree ∧
      LogupDegree circuit degrees groupSize (group + 1) remaining (max initial degree) result

def CircuitBounds (circuit : Circuit) : Prop :=
  circuit.mainWidth < 65536 ∧ circuit.preprocessedWidth < 65536 ∧
    circuit.preprocessedHeight < 2 ^ 32 ∧ circuit.nodes.size < 65536 ∧
    circuit.zeros.size < 65536 ∧ circuit.lookups.size < 65536 ∧
    (∀ lookup ∈ circuit.lookups, lookup.args.size < 65536)

def CircuitPreprocessing (params : Parameters) (circuit : Circuit) : Prop :=
  if circuit.preprocessedWidth = 0 then circuit.preprocessedHeight = 0 else
    0 < circuit.preprocessedHeight ∧ 2 ^ circuit.preprocessedHeight.log2 = circuit.preprocessedHeight ∧
      circuit.preprocessedHeight.log2 + params.logBlowup ≤ 32

def CircuitAdmissible (params : Parameters) (circuit : Circuit) : Prop :=
  CircuitBounds circuit ∧ (1 ≤ circuit.lookupGroupSize ∧ circuit.lookupGroupSize ≤ 8) ∧
    CircuitPreprocessing params circuit ∧
    ∃ degrees userDegree lookupDegree,
      KeyDegrees circuit circuit.nodes.toList #[] degrees ∧ RootDegree degrees circuit.zeros.toList 0 userDegree ∧
      LogupDegree circuit degrees (max 1 circuit.lookupGroupSize) 0 circuit.lookupGroups 1 lookupDegree ∧
      circuit.maxConstraintDegree = max userDegree lookupDegree ∧ circuit.maxConstraintDegree < 65536 ∧
      circuit.maxConstraintDegree ≤ 2 ^ params.logBlowup + 1

def KeyCircuits (params : Parameters) (count : Nat) : List Circuit → List (Option Nat) → Nat → Prop
  | [], [], _ => True
  | circuit :: circuits, index :: indices, nextSlot =>
    CircuitAdmissible params circuit ∧
      match index with
      | none => circuit.preprocessedWidth = 0 ∧ KeyCircuits params count circuits indices nextSlot
      | some index =>
        (0 < circuit.preprocessedWidth ∧ index < count ∧ index = nextSlot) ∧
          KeyCircuits params count circuits indices (nextSlot + 1)
  | _, _, _ => False

def KeyAdmissible (key : Key) : Prop :=
  let count := (key.preprocessedIndices.filter Option.isSome).size
  ParametersAdmissible key.params ∧
    (0 < key.circuits.size ∧ key.circuits.size < 65536 ∧ key.preprocessedIndices.size = key.circuits.size) ∧
    (match key.preprocessed with
      | none => count = 0
      | some cap => 0 < count ∧ 0 < cap.size) ∧
    KeyCircuits key.params count key.circuits.toList key.preprocessedIndices.toList 0

end MultiStark.Verify.Protocol
