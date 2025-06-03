import Ix.Archon.OracleIdx
import Ix.Archon.TowerField
import Ix.Unsigned

namespace Archon

private opaque GenericNonempty : NonemptyType
def WitnessModule : Type := GenericNonempty.type
instance : Nonempty WitnessModule := GenericNonempty.property

private opaque GenericNonempty' : NonemptyType
def Witness : Type := GenericNonempty'.type
instance : Nonempty Witness := GenericNonempty'.property

structure EntryId where
  toUSize : USize
  deriving Inhabited

namespace WitnessModule

/-- **Invalidates** the input `WitnessModule` -/
@[never_extract, extern "c_rs_witness_module_add_entry"]
opaque addEntry : WitnessModule → EntryId × WitnessModule

/-- **Invalidates** the input `WitnessModule` -/
@[never_extract, extern "c_rs_witness_module_add_entry_with_capacity"]
opaque addEntryWithCapacity : WitnessModule → (logBits : UInt8) → EntryId × WitnessModule

/-- **Invalidates** the input `WitnessModule` -/
@[never_extract, extern "c_rs_witness_module_bind_oracle_to"]
opaque bindOracleTo : WitnessModule → OracleIdx → EntryId → TowerField → WitnessModule

/-- **Invalidates** the input `WitnessModule` -/
@[never_extract, extern "c_rs_witness_module_push_u8s_to"]
opaque pushUInt8sTo : WitnessModule → @& Array UInt8 → EntryId → WitnessModule

/-- **Invalidates** the input `WitnessModule` -/
@[never_extract, extern "c_rs_witness_module_push_u16s_to"]
opaque pushUInt16sTo : WitnessModule → @& Array UInt16 → EntryId → WitnessModule

/-- **Invalidates** the input `WitnessModule` -/
@[never_extract, extern "c_rs_witness_module_push_u32s_to"]
opaque pushUInt32sTo : WitnessModule → @& Array UInt32 → EntryId → WitnessModule

/-- **Invalidates** the input `WitnessModule` -/
@[never_extract, extern "c_rs_witness_module_push_u64s_to"]
opaque pushUInt64sTo : WitnessModule → @& Array UInt64 → EntryId → WitnessModule

/-- **Invalidates** the input `WitnessModule` -/
@[never_extract, extern "c_rs_witness_module_push_u128s_to"]
opaque pushUInt128sTo : WitnessModule → @& Array UInt128 → EntryId → WitnessModule

/-- **Invalidates** the input `WitnessModule` -/
@[never_extract, extern "c_rs_witness_module_populate"]
opaque populate : WitnessModule → (height : UInt64) → WitnessModule

end WitnessModule

/-- **Invalidates** the elements of the input `Array WitnessModule` -/
@[never_extract, extern "c_rs_compile_witness_modules"]
opaque compileWitnessModules : Array WitnessModule → (heights : @& Array UInt64) → Witness

end Archon
