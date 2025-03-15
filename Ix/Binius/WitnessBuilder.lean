import Ix.Binius.ConstraintSystem

namespace Binius

private opaque GenericNonempty : NonemptyType

def WitnessBuilder : Type := GenericNonempty.type

instance : Nonempty WitnessBuilder := GenericNonempty.property

namespace WitnessBuilder

@[never_extract, extern "c_rs_witness_builder_new"]
opaque new : @& ConstraintSystem → WitnessBuilder

inductive ColumnData
  | raw : ByteArray → ColumnData
  | u8 : Array UInt8 → ColumnData
  | u16 : Array UInt16 → ColumnData
  | u32 : Array UInt32 → ColumnData
  | u64 : Array UInt64 → ColumnData
  | u128 : Array UInt128 → ColumnData

instance : Coe ByteArray ColumnData := ⟨.raw⟩
instance : Coe (Array UInt8) ColumnData := ⟨.u8⟩
instance : Coe (Array UInt16) ColumnData := ⟨.u16⟩
instance : Coe (Array UInt32) ColumnData := ⟨.u32⟩
instance : Coe (Array UInt64) ColumnData := ⟨.u64⟩
instance : Coe (Array UInt128) ColumnData := ⟨.u128⟩

/-- **Invalidates** the input `WitnessBuilder` -/
@[never_extract, extern "c_rs_witness_builder_with_column"]
opaque withColumn : WitnessBuilder → OracleId → @& ColumnData → WitnessBuilder

/-- **Invalidates** the input `WitnessBuilder` -/
@[never_extract, extern "c_rs_witness_builder_build"]
opaque build : WitnessBuilder → Witness

end WitnessBuilder

end Binius
