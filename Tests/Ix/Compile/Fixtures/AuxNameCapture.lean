import Init

/- Regression fixture. Both presentations use ordinary checked declarations.
The first deliberately puts one original member at the spelling used by
Ix for the first List auxiliary; the neighbour changes only that name. -/

namespace Tests.Ix.Compile.Fixtures.AuxNameCapture.Collision

mutual
  inductive Root : Type where
    | nil : Root
    | mk : List Root → Root._nested.List_1 → Root
  inductive Root._nested.List_1 : Type where
    | nil : Root._nested.List_1
    | mk : Root → Root._nested.List_1
end

end Tests.Ix.Compile.Fixtures.AuxNameCapture.Collision

namespace Tests.Ix.Compile.Fixtures.AuxNameCapture.Neighbour

mutual
  inductive Root : Type where
    | nil : Root
    | mk : List Root → Node → Root
  inductive Node : Type where
    | nil : Node
    | mk : Root → Node
end

end Tests.Ix.Compile.Fixtures.AuxNameCapture.Neighbour
