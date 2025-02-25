import Ix.Rust
import Ix.Binius.ConstraintSystem

namespace Binius

private opaque GenericNonempty : NonemptyType

def ConstraintSystemBuilder : Type := GenericNonempty.type

instance : Nonempty ConstraintSystemBuilder := GenericNonempty.property

abbrev ChannelId := USize

namespace ConstraintSystemBuilder

@[extern "c_constraint_system_builder_init"]
opaque init : Unit → ConstraintSystemBuilder

/--
**Mutates** the `ConstraintSystemBuilder` and returns a `ChannelId` and the
mutated `ConstraintSystemBuilder`.

**Warning**: trying to reuse the input `ConstraintSystemBuilder` will cause a
runtime panic.
-/
@[extern "c_constraint_system_builder_add_channel"]
opaque addChannel : ConstraintSystemBuilder → ChannelId × ConstraintSystemBuilder

/--
**Mutates** the `ConstraintSystemBuilder` (via `std::mem::take`) and returns the
built `ConstraintSystem`.

**Warning**: trying to reuse the input `ConstraintSystemBuilder` will cause a
runtime panic. -/
@[extern "c_constraint_system_builder_build"]
opaque build : ConstraintSystemBuilder → ConstraintSystem

end ConstraintSystemBuilder

end Binius
