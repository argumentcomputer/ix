import Ix.Rust
import Ix.Binius.ArithExpr
import Ix.Binius.ConstraintSystem

/-!
This module provides Lean bindings for the Binius Rust crate.

Be extra careful with functions that mutate the input. Attempting to reuse mutated
objects will cause a runtime panic.
-/

namespace Binius

private opaque GenericNonempty : NonemptyType

def ConstraintSystemBuilder : Type := GenericNonempty.type

instance : Nonempty ConstraintSystemBuilder := GenericNonempty.property

structure ChannelId where
  toUSize : USize
  deriving Inhabited

structure OracleId where
  toUSize : USize
  deriving Inhabited

inductive FlushDirection
  | push | pull

namespace ConstraintSystemBuilder

@[extern "c_rs_constraint_system_builder_init"]
opaque init : Unit → ConstraintSystemBuilder

/-- **Mutates** the input `ConstraintSystemBuilder` -/
@[extern "c_rs_constraint_system_builder_build"]
opaque build : ConstraintSystemBuilder → ConstraintSystem

/-- **Mutates** the input `ConstraintSystemBuilder` -/
@[extern "c_rs_constraint_system_builder_flush_custom"]
opaque flushCustom :
  ConstraintSystemBuilder → FlushDirection → ChannelId → (selector : OracleId) →
    @& Array OracleId → (multiplicity : UInt64) → ConstraintSystemBuilder

/-- **Mutates** the input `ConstraintSystemBuilder` -/
@[extern "c_rs_constraint_system_builder_assert_zero"]
opaque assertZero : ConstraintSystemBuilder → @& String → @& Array OracleId →
  @& ArithExpr → ConstraintSystemBuilder

/-- **Mutates** the input `ConstraintSystemBuilder` -/
@[extern "c_rs_constraint_system_builder_assert_not_zero"]
opaque assertNotZero : ConstraintSystemBuilder → OracleId → ConstraintSystemBuilder

/-- **Mutates** the input `ConstraintSystemBuilder` -/
@[extern "c_rs_constraint_system_builder_add_channel"]
opaque addChannel : ConstraintSystemBuilder → ChannelId × ConstraintSystemBuilder

/-- **Mutates** the input `ConstraintSystemBuilder` -/
@[extern "c_rs_constraint_system_builder_add_committed"]
opaque addCommitted : ConstraintSystemBuilder → @& String →
  (nVars towerLevel : USize) → OracleId × ConstraintSystemBuilder

/-- **Mutates** the input `ConstraintSystemBuilder` -/
@[extern "c_rs_constraint_system_builder_push_namespace"]
opaque pushNamespace : ConstraintSystemBuilder → @& String → ConstraintSystemBuilder

/-- **Mutates** the input `ConstraintSystemBuilder` -/
@[extern "c_rs_constraint_system_builder_pop_namespace"]
opaque popNamespace : ConstraintSystemBuilder → ConstraintSystemBuilder

@[extern "c_rs_constraint_system_builder_log_rows"]
opaque logRows : @& ConstraintSystemBuilder → @& Array OracleId → USize

end ConstraintSystemBuilder

end Binius
