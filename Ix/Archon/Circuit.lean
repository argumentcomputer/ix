import Blake3
import Ix.Archon.ArithExpr
import Ix.Archon.OracleIdx
import Ix.Archon.Transparent
import Ix.Archon.Witness
import Ix.Binius.Common

namespace Archon

private opaque GenericNonempty : NonemptyType
def CircuitModule : Type := GenericNonempty.type
instance : Nonempty CircuitModule := GenericNonempty.property

inductive ShiftVariant
  | circularLeft | logicalLeft | logicalRight

namespace CircuitModule

@[never_extract, extern "c_rs_circuit_module_new"]
opaque new : USize → CircuitModule

abbrev selector : OracleIdx := ⟨0⟩

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_freeze_oracles"]
opaque freezeOracles : CircuitModule → CircuitModule

@[extern "c_rs_circuit_module_init_witness_module"]
opaque initWitnessModule : @& CircuitModule → WitnessModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_flush"]
opaque flush : CircuitModule → Binius.FlushDirection → Binius.ChannelId →
  (selector : OracleIdx) → @& Array OracleIdx → (multiplicity : UInt64) → CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_assert_zero"]
opaque assertZero : CircuitModule → @& String → @& Array OracleIdx →
  @& ArithExpr → CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_assert_not_zero"]
opaque assertNotZero : CircuitModule → OracleIdx → CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_assert_dynamic_exp"]
opaque assertDynamicExp : CircuitModule → (expBits : @& Array OracleIdx) →
  (result : OracleIdx) → (base : OracleIdx) → CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_assert_static_exp"]
opaque assertStaticExp : CircuitModule → (expBits : @& Array OracleIdx) →
  (result : OracleIdx) → (base : @& UInt128) → (baseTF : TowerField) → CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_committed"]
opaque addCommitted : CircuitModule → @& String → TowerField → OracleIdx × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_transparent"]
opaque addTransparent : CircuitModule → @& String → @& Transparent → OracleIdx × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_linear_combination"]
opaque addLinearCombination : CircuitModule → @& String → (offset : @& UInt128) →
  (inner : @& Array (OracleIdx × UInt128)) → OracleIdx × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_packed"]
opaque addPacked : CircuitModule → @& String → OracleIdx →
  (logDegree : USize) → OracleIdx × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_shifted"]
opaque addShifted : CircuitModule → @& String → OracleIdx → (shiftOffset : UInt32) →
  (blockBits : USize) → @& ShiftVariant → OracleIdx × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_add_projected"]
opaque addProjected : CircuitModule → @& String → OracleIdx → (mask : UInt64) →
  (unprojectedSize : USize) → OracleIdx × CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_push_namespace"]
opaque pushNamespace : CircuitModule → @& String → CircuitModule

/-- **Invalidates** the input `CircuitModule` -/
@[never_extract, extern "c_rs_circuit_module_pop_namespace"]
opaque popNamespace : CircuitModule → CircuitModule

@[extern "c_rs_circuit_module_canonical_bytes"]
opaque canonicalBytes : @& CircuitModule → ByteArray

end CircuitModule

def version (modules : Array CircuitModule) : Blake3.Blake3Hash :=
  let bytes := modules.foldl (fun acc mod => acc ++ mod.canonicalBytes) default
  Blake3.hash bytes

end Archon
