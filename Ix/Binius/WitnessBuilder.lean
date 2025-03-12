-- import Ix.Rust
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
opaque withColumn : WitnessBuilder → OracleId → (data : @& ByteArray) → WitnessBuilder

/-- **Invalidates** the input `WitnessBuilder` -/
@[never_extract, extern "c_rs_witness_builder_build"]
opaque build : WitnessBuilder → Witness

end WitnessBuilder

end Binius
