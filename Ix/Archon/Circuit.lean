import Ix.Archon.ArithExpr
import Ix.Archon.Transparent
import Ix.Archon.Witness

namespace Archon

open Binius

private opaque GenericNonempty : NonemptyType
def CircuitModule : Type := GenericNonempty.type
instance : Nonempty CircuitModule := GenericNonempty.property

inductive ShiftVariant
  | circularLeft | logicalLeft | logicalRight

namespace CircuitModule

@[never_extract, extern "c_rs_circuit_module_new"]
opaque new : USize → CircuitModule

abbrev selector : CircuitModule → OracleId := fun _ => ⟨0⟩

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_freeze_oracles"]
opaque freezeOracles : CircuitModule → CircuitModule

@[extern "c_rs_circuit_module_init_witness_module"]
opaque initWitnessModule : @& CircuitModule → WitnessModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_flush"]
opaque flush : CircuitModule → FlushDirection → ChannelId → @& Array OracleId →
  (multiplicity : UInt64) → CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_assert_zero"]
opaque assertZero : CircuitModule → @& String → @& Array OracleId →
  @& ArithExpr → CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_assert_not_zero"]
opaque assertNotZero : CircuitModule → OracleId → CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_committed"]
opaque addCommitted : CircuitModule → @& String → TowerField → OracleId × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_transparent"]
opaque addTransparent : CircuitModule → @& String → @& Transparent → OracleId × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_linear_combination"]
opaque addLinearCombination : CircuitModule → @& String → (offset : @& UInt128) →
  (inner : @& Array (OracleId × UInt128)) → OracleId × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_packed"]
opaque addPacked : CircuitModule → @& String → OracleId →
  (logDegree : USize) → OracleId × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_shifted"]
opaque addShifted : CircuitModule → @& String → OracleId → (shiftOffset : UInt32) →
  (blockBits : USize) → @& ShiftVariant → OracleId × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_projected"]
opaque addProjected : CircuitModule → @& String → OracleId → (mask : UInt64) →
  (unprojectedSize startIndex : USize) → OracleId × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_push_namespace"]
opaque pushNamespace : CircuitModule → @& String → CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_pop_namespace"]
opaque popNamespace : CircuitModule → CircuitModule

end CircuitModule

end Archon
