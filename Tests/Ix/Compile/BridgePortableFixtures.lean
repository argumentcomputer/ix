/-! Runtime-only, actually checked Source inputs for the portable bridge.
The controls deliberately collide query address maps, never these records. -/
namespace Tests.Ix.Compile.BridgePortableFixtures

inductive NatAlias where
  | zero
  | succ : NatAlias → NatAlias

opaque Left : Type := Nat
opaque Right : Type := Nat
opaque Ambient : Type := Nat

def Poly.{u} (A : Sort u) : Sort u := A

end Tests.Ix.Compile.BridgePortableFixtures
