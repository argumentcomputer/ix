import Ix.AuxGen.Oracle

namespace Tests.Ix.AuxGen.GenerationOnlyOpaqueFixtures

-- The exported partial wrapper's supplied logical body is `default`;
-- its separately supplied operational companion recurs. Tests inspect the
-- records and never execute this function.
partial def hidden (x : Ix.AuxGen.OracleScope) : Nat := hidden x
def bodyOnly (_x : Ix.AuxGen.OracleScope) : Nat := 41
opaque usesBody (x : Ix.AuxGen.OracleScope) : Nat := bodyOnly x

inductive Owner (x : Ix.AuxGen.OracleScope) : Nat → Prop where
  | first : Owner x (hidden x)
  | second : Owner x (usesBody x)

end Tests.Ix.AuxGen.GenerationOnlyOpaqueFixtures
