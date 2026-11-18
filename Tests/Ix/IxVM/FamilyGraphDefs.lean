/-! # Lean sources of the family graph records

A family nested through a user container, checked by Lean's kernel, that
`ixvm-family-graph-records` (`Tests.Ix.IxVM.FamilyGraphRecords`) reads from the test binary's
environment and compiles with Ix's compiler. The container's constructor is a constant address
of the container's block; the recursors of the nested family name it, and the family's own
block does not. -/

namespace Tests.Ix.IxVM.FamilyGraphDefs

/-- A user container with one constructor. -/
inductive Box (α : Type) where
  | mk : α → Box α

/-- A tree nested through the user container. -/
inductive BT where
  | node : Box BT → BT

/-- A tree nested through two containers: two auxiliary members. -/
inductive PT where
  | node : List PT → Option PT → PT

end Tests.Ix.IxVM.FamilyGraphDefs
