import Ix.Rust

namespace Binius

private opaque GenericNonempty : NonemptyType

def ConstraintSystemBuilder : Type := GenericNonempty.type

instance : Nonempty ConstraintSystemBuilder := GenericNonempty.property

abbrev ChannelId := USize

namespace ConstraintSystemBuilder

@[extern "c_constraint_system_builder_init"]
opaque init : Unit → ConstraintSystemBuilder

/-- **Mutates** the `ConstraintSystemBuilder` and returns a `ChannelId` -/
@[extern "c_constraint_system_builder_add_channel"]
private opaque addChannel : ConstraintSystemBuilder → ChannelId

end ConstraintSystemBuilder

abbrev CSBuildM := StateM ConstraintSystemBuilder

opaque addChannel : CSBuildM ChannelId :=
  ConstraintSystemBuilder.addChannel <$> get

@[always_inline, inline]
def CSBuildM.run (f : CSBuildM α) (builder : ConstraintSystemBuilder) : α × ConstraintSystemBuilder :=
  f builder

end Binius
