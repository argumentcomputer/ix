import Ix.Binius.ConstraintSystem

namespace Binius

private opaque GenericNonempty : NonemptyType

def WitnessBuilder : Type := GenericNonempty.type

instance : Nonempty WitnessBuilder := GenericNonempty.property

namespace WitnessBuilder

@[never_extract, extern "c_rs_witness_builder_new"]
opaque new : @& ConstraintSystem → WitnessBuilder

/-- **Invalidates** the input `WitnessBuilder` -/
@[never_extract, extern "c_rs_witness_builder_with_column"]
private opaque withColumn' : WitnessBuilder → OracleId → @& ByteArray → WitnessBuilder

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
@[never_extract]
def withColumn [Coe α ColumnData] (builder : WitnessBuilder) (oracleId : OracleId)
    (data : α) : WitnessBuilder :=
  let bytes := match (data : ColumnData) with
    | .raw bs => bs
    | .u8 xs => xs.foldl (init := .mkEmpty xs.size) fun acc x => acc.push x
    | .u16 xs => xs.foldl (init := .mkEmpty (2 * xs.size)) fun acc x => acc ++ x.toLEBytes
    | .u32 xs => xs.foldl (init := .mkEmpty (4 * xs.size)) fun acc x => acc ++ x.toLEBytes
    | .u64 xs => xs.foldl (init := .mkEmpty (8 * xs.size)) fun acc x => acc ++ x.toLEBytes
    | .u128 xs => xs.foldl (init := .mkEmpty (16 * xs.size)) fun acc x => acc ++ x.toLEBytes
  builder.withColumn' oracleId bytes

/-- **Invalidates** the input `WitnessBuilder` -/
@[never_extract, extern "c_rs_witness_builder_build"]
opaque build : WitnessBuilder → Witness

end WitnessBuilder

end Binius
