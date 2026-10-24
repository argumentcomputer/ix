import Lean

namespace Tests.AuxGen.PortableFixtures

def Pred (A : Type) : Type := (x : A) → Prop
inductive Two : Prop | a | b
inductive One : Prop | mk
inductive T : Type | mk
inductive Loop : Prop | step : Loop → Loop
inductive S : Pred T | mk : S T.mk
inductive NestedProp : Prop | node : Nonempty NestedProp → NestedProp
inductive NestedType : Type | node : List NestedType → NestedType

-- Kernel-accepted Sort-u declarations, as in the existing SortUDecl fixture.
-- Their actual supplied records must also be Source-accepted by the test.
open Lean Meta Elab Command in
run_meta do
  for (name, count) in [(`Tests.AuxGen.PortableFixtures.PolyTwo, 2),
      (`Tests.AuxGen.PortableFixtures.PolyOne, 1), (`Tests.AuxGen.PortableFixtures.PolyAux, 1)] do
    let u : Lean.Level := .param `u
    let ctors := (List.range count).map fun i =>
      Lean.Constructor.mk (name.str s!"mk{i}") (Lean.mkConst name [u])
    let type := Lean.InductiveType.mk name (.sort u) ctors
    Lean.addDecl (.inductDecl [`u] 0 [type] false)

end Tests.AuxGen.PortableFixtures
