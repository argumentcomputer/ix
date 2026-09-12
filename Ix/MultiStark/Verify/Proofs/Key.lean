module
public import Ix.MultiStark.Verify.Protocol.Key
public import Ix.MultiStark.Verify.Proofs.Basic

public section

namespace MultiStark.Verify.Proofs

theorem parameters_admissible_refines (params : Parameters) :
    params.admissible = true ↔ Protocol.ParametersAdmissible params := by
  simp only [Parameters.admissible, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true',
    Protocol.ParametersAdmissible, and_assoc]

theorem getDegree_refines (degrees : Array Nat) (index result : Nat) :
    KeyValidation.getDegree degrees index = .ok result ↔ degrees[index]? = some result := by
  unfold KeyValidation.getDegree
  cases degrees[index]? <;> simp

theorem nodeDegree_refines (circuit : Circuit) (degrees : Array Nat) (node : Node) (result : Nat) :
    KeyValidation.nodeDegree circuit degrees node = .ok result ↔ Protocol.KeyNodeDegree circuit degrees node result := by
  cases node <;>
    simp [KeyValidation.nodeDegree, Protocol.KeyNodeDegree, bind_ok_iff, map_ok_iff,
      unit_exists_iff, ensure_ok_iff, getDegree_refines, exists_and_left]
  intro _
  rfl

theorem degreesFrom_refines (circuit : Circuit) (nodes : List Node) (before after : Array Nat) :
    KeyValidation.degreesFrom circuit nodes before = .ok after ↔ Protocol.KeyDegrees circuit nodes before after := by
  induction nodes generalizing before with
  | nil => simp [KeyValidation.degreesFrom, Protocol.KeyDegrees]
  | cons node nodes ih =>
    simp only [KeyValidation.degreesFrom, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
      decide_eq_true_eq, nodeDegree_refines, ih, Protocol.KeyDegrees]

theorem degrees_refines (circuit : Circuit) (result : Array Nat) :
    KeyValidation.degrees circuit = .ok result ↔ Protocol.KeyDegrees circuit circuit.nodes.toList #[] result :=
  degreesFrom_refines circuit circuit.nodes.toList #[] result

theorem maxRootsFrom_refines (degrees : Array Nat) (roots : List Nat) (initial result : Nat) :
    KeyValidation.maxRootsFrom degrees roots initial = .ok result ↔ Protocol.RootDegree degrees roots initial result := by
  induction roots generalizing initial with
  | nil => simp [KeyValidation.maxRootsFrom, Protocol.RootDegree]
  | cons root roots ih =>
    simp only [KeyValidation.maxRootsFrom, bind_ok_iff, getDegree_refines, ih, Protocol.RootDegree]

theorem maxRoots_refines (degrees : Array Nat) (roots : Array Nat) (result : Nat) :
    KeyValidation.maxRoots degrees roots = .ok result ↔ Protocol.RootDegree degrees roots.toList 0 result :=
  maxRootsFrom_refines degrees roots.toList 0 result

theorem lookupDegrees_refines (degrees : Array Nat) (lookups : List Lookup) (pairs : List (Nat × Nat)) :
    KeyValidation.lookupDegrees degrees lookups = .ok pairs ↔ Protocol.LookupDegrees degrees lookups pairs := by
  induction lookups generalizing pairs with
  | nil => cases pairs <;> simp [KeyValidation.lookupDegrees, Protocol.LookupDegrees]
  | cons lookup lookups ih =>
    cases pairs with
    | nil => simp [KeyValidation.lookupDegrees, bind_ok_iff, map_ok_iff, Protocol.LookupDegrees]
    | cons pair pairs =>
      cases pair
      simp [KeyValidation.lookupDegrees, bind_ok_iff, map_ok_iff, maxRoots_refines, getDegree_refines,
        ih, Protocol.LookupDegrees]
      constructor
      · rintro ⟨message, hm, multiplicity, hw, rest, rfl, rfl⟩
        exact ⟨hm, hw, rest⟩
      · rintro ⟨hm, hw, rest⟩
        exact ⟨_, hm, _, hw, rest, rfl, rfl⟩

theorem groupDegree_refines (degrees : Array Nat) (group : Array Lookup) (result : Nat) :
    KeyValidation.groupDegree degrees group = .ok result ↔ Protocol.GroupDegree degrees group result := by
  simp only [KeyValidation.groupDegree, bind_ok_iff, lookupDegrees_refines, pure_ok_iff, Protocol.GroupDegree]

theorem logupDegreeFrom_refines (circuit : Circuit) (degrees : Array Nat) (groupSize group remaining initial result : Nat) :
    KeyValidation.logupDegreeFrom circuit degrees groupSize group remaining initial = .ok result ↔
      Protocol.LogupDegree circuit degrees groupSize group remaining initial result := by
  induction remaining generalizing group initial with
  | zero => simp [KeyValidation.logupDegreeFrom, Protocol.LogupDegree]
  | succ remaining ih =>
    simp only [KeyValidation.logupDegreeFrom, bind_ok_iff, groupDegree_refines, ih, Protocol.LogupDegree]

theorem logupDegree_refines (circuit : Circuit) (degrees : Array Nat) (result : Nat) :
    KeyValidation.logupDegree circuit degrees = .ok result ↔
      Protocol.LogupDegree circuit degrees (max 1 circuit.lookupGroupSize) 0 circuit.lookupGroups 1 result :=
  logupDegreeFrom_refines circuit degrees (max 1 circuit.lookupGroupSize) 0 circuit.lookupGroups 1 result

theorem circuit_refines (params : Parameters) (circuit : Circuit) :
    KeyValidation.circuit params circuit = .ok () ↔ Protocol.CircuitAdmissible params circuit := by
  by_cases zero : circuit.preprocessedWidth = 0 <;>
    simp only [KeyValidation.circuit, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.all_eq_true', degrees_refines,
      maxRoots_refines, logupDegree_refines, Protocol.CircuitAdmissible, Protocol.CircuitBounds,
      Protocol.CircuitPreprocessing, zero, ↓reduceIte, exists_and_left, and_assoc]

theorem circuits_refines (params : Parameters) (count : Nat) (circuits : List Circuit)
    (indices : List (Option Nat)) (nextSlot : Nat) :
    KeyValidation.circuits params count circuits indices nextSlot = .ok () ↔
      Protocol.KeyCircuits params count circuits indices nextSlot := by
  induction circuits generalizing indices nextSlot with
  | nil => cases indices <;> simp [KeyValidation.circuits, Protocol.KeyCircuits]
  | cons circuit circuits ih =>
    cases indices with
    | nil => simp [KeyValidation.circuits, Protocol.KeyCircuits]
    | cons index indices =>
      cases index <;>
        simp only [KeyValidation.circuits, bind_ok_iff, unit_exists_iff, ensure_ok_iff, beq_iff_eq,
          Bool.and_eq_true, decide_eq_true_eq, circuit_refines, ih, Protocol.KeyCircuits, and_assoc]

theorem validateKey_refines (key : Key) : validateKey key = .ok () ↔ Protocol.KeyAdmissible key := by
  unfold validateKey Protocol.KeyAdmissible
  cases key.preprocessed <;>
    simp only [bind_ok_iff, unit_exists_iff, ensure_ok_iff, parameters_admissible_refines,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, circuits_refines, and_assoc]

end MultiStark.Verify.Proofs
