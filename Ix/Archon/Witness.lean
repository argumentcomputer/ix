import Ix.Archon.OracleIdx
import Ix.Unsigned

namespace Archon

inductive TowerField
  | b1 | b2 | b4 | b8 | b16 | b32 | b64 | b128

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
@[never_extract, extern "c_rs_witness_module_push_u128_to"]
opaque pushUInt128To : WitnessModule → @& UInt128 → EntryId → WitnessModule

/-- **Invalidates** the input `WitnessModule` -/
@[never_extract, extern "c_rs_witness_module_populate"]
opaque populate : WitnessModule → (height : UInt64) → WitnessModule

end WitnessModule

/-- **Invalidates** the elements of the input `Array WitnessModule` -/
@[never_extract, extern "c_rs_compile_witness_modules"]
opaque compileWitnessModules : Array WitnessModule → (heights : @& Array UInt64) → Witness

end Archon
