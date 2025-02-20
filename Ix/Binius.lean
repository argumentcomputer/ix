@[extern "rs_constraint_system_builder_init"]
private opaque rs_constraint_system_builder_init [Inhabited α] : Unit → α
@[extern "rs_constraint_system_builder_free"]
private opaque rs_constraint_system_builder_free [Inhabited α] : Unit → α
@[extern "rs_constraint_system_builder_add_channel"]
private opaque rs_constraint_system_builder_add_channel [Inhabited α] : Unit → α

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
private opaque addChannel_ : ConstraintSystemBuilder → ChannelId

end ConstraintSystemBuilder

abbrev CSBuildM := StateM ConstraintSystemBuilder

opaque addChannel : CSBuildM ChannelId :=
  ConstraintSystemBuilder.addChannel_ <$> get

@[always_inline, inline]
def CSBuildM.run (f : CSBuildM α) (builder : ConstraintSystemBuilder) : α × ConstraintSystemBuilder :=
  f builder

end Binius
