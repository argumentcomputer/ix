import Ix.Rust

namespace Binius

private opaque GenericNonempty : NonemptyType

/--
Corresponds to Binius' type, which works via mutation, and must be treated as a
linear type. Otherwise, it will panic at runtime.
-/
def ConstraintSystemBuilder : Type := GenericNonempty.type

instance : Nonempty ConstraintSystemBuilder := GenericNonempty.property

abbrev ChannelId := USize

namespace ConstraintSystemBuilder

@[extern "c_constraint_system_builder_init"]
opaque init : Unit → ConstraintSystemBuilder

/--
**Mutates** the `ConstraintSystemBuilder` and returns a `ChannelId` and the
mutated `ConstraintSystemBuilder`.
-/
@[extern "c_constraint_system_builder_add_channel"]
private opaque addChannel : ConstraintSystemBuilder → ChannelId × ConstraintSystemBuilder

/-- Simulates inplace mutation with a syntactical overwrite. -/
macro "let" ch:ident "≪" "add_channel" csb:ident ";"? rst:term : term =>
  `(let ($ch, $csb) := addChannel $csb; $rst)

/--
Simulates inplace mutation with a syntactical overwrite and then clears the
constraint system builder from context to satisfy the unused variable linter.
-/
macro "let" ch:ident "≪" "add_channel" csb:ident "." ";"? rst:term : term =>
  `(let ($ch, $csb) := addChannel $csb;
    by
      repeat clear $csb;
      exact $rst)

end ConstraintSystemBuilder

end Binius
