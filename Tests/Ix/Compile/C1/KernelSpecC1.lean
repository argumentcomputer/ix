/- Ordinary-source C1 fixtures supplementing the original KernelSpec file
   and the existing accounting units. -/
namespace KernelSpecC1

-- Exact source shape of KernelSpec.P, isolated from the independent T case.
inductive P : Prop
  | mk : And P P → P

inductive Box (p : Prop) : Prop
  | mk : p → Box p

-- The existing nested-Prop Rust fixture has two constructors. This one
-- exercises the single-constructor field probe that can fail before C1.
inductive W : Prop
  | node : Box W → W

-- Valid nonnested neighbours: empty, K, and proof-only singleton.
inductive EmptyP : Prop
inductive K : Prop
  | mk
inductive Drec : Prop
  | mk : Drec → Drec

-- Valid nested Type neighbour; no Prop-only C1 branch is permitted.
inductive T
  | leaf
  | node : List T → T

end KernelSpecC1
