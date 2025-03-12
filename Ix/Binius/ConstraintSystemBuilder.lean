import Ix.Binius.ArithExpr
import Ix.Binius.Common
import Ix.Binius.ConstraintSystem

namespace Binius

private opaque GenericNonempty : NonemptyType

def ConstraintSystemBuilder : Type := GenericNonempty.type

instance : Nonempty ConstraintSystemBuilder := GenericNonempty.property

namespace ConstraintSystemBuilder

@[never_extract, extern "c_rs_constraint_system_builder_new"]
opaque new : Unit → ConstraintSystemBuilder

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_build"]
opaque build : ConstraintSystemBuilder → ConstraintSystem

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_flush_with_multiplicity"]
opaque flushWithMultiplicity :
  ConstraintSystemBuilder → FlushDirection → ChannelId → (count : USize) →
    @& Array OracleId → (multiplicity : UInt64) → ConstraintSystemBuilder

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
def flush (builder : ConstraintSystemBuilder) (direction : FlushDirection)
    (channelId : ChannelId) (count : USize) (oracleIds : @& Array OracleId) :
      ConstraintSystemBuilder :=
  builder.flushWithMultiplicity direction channelId count oracleIds 1

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_flush_custom"]
opaque flushCustom :
  ConstraintSystemBuilder → FlushDirection → ChannelId → (selector : OracleId) →
    @& Array OracleId → (multiplicity : UInt64) → ConstraintSystemBuilder

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
def send (builder : ConstraintSystemBuilder)
    (channelId : ChannelId) (count : USize) (oracleIds : @& Array OracleId) :
      ConstraintSystemBuilder :=
  builder.flush .push channelId count oracleIds

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
def receive (builder : ConstraintSystemBuilder)
    (channelId : ChannelId) (count : USize) (oracleIds : @& Array OracleId) :
      ConstraintSystemBuilder :=
  builder.flush .pull channelId count oracleIds

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_assert_zero"]
opaque assertZero : ConstraintSystemBuilder → @& String → @& Array OracleId →
  @& ArithExpr → ConstraintSystemBuilder

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_assert_not_zero"]
opaque assertNotZero : ConstraintSystemBuilder → OracleId → ConstraintSystemBuilder

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_add_channel"]
opaque addChannel : ConstraintSystemBuilder → ChannelId × ConstraintSystemBuilder

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_add_committed"]
opaque addCommitted : ConstraintSystemBuilder → @& String →
  (nVars towerLevel : USize) → OracleId × ConstraintSystemBuilder

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_add_linear_combination"]
opaque addLinearCombination : ConstraintSystemBuilder → @& String →
  (nVars : USize) → (inner : @& Array (OracleId × UInt128)) → OracleId × ConstraintSystemBuilder

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_add_linear_combination_with_offset"]
opaque addLinearCombinationWithOffset : ConstraintSystemBuilder → @& String →
  (nVars : USize) → (offset : @& UInt128) → (inner : @& Array (OracleId × UInt128)) →
    OracleId × ConstraintSystemBuilder

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_add_packed"]
opaque addPacked : ConstraintSystemBuilder → @& String → OracleId →
  (logDegree : USize) → OracleId × ConstraintSystemBuilder

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_push_namespace"]
opaque pushNamespace : ConstraintSystemBuilder → @& String → ConstraintSystemBuilder

/-- **Invalidates** the input `ConstraintSystemBuilder` -/
@[never_extract, extern "c_rs_constraint_system_builder_pop_namespace"]
opaque popNamespace : ConstraintSystemBuilder → ConstraintSystemBuilder

@[extern "c_rs_constraint_system_builder_log_rows"]
opaque logRows : @& ConstraintSystemBuilder → @& Array OracleId → USize

end ConstraintSystemBuilder

end Binius
