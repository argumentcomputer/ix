import IxCC.Aiur.AIR.Rank.Model

/-! A fixed-size ingress for supplied ordered-edge witnesses. It retains
the checked range and physical rank equality; it does not accept a proof
that the natural ranks increase and does not identify a STARK assignment. -/

namespace IxCC.Aiur.AIR.Rank

structure Edge where
  parent : Limbs
  gap : Limbs
  child : Limbs
  deriving DecidableEq, Repr

def Edge.check (edge : Edge) : Bool :=
  decide edge.parent.Bounded && decide edge.gap.Bounded && decide edge.child.Bounded &&
  decide (ordered edge.parent edge.gap = edge.child.packed)

inductive Error where
  | parentRange | gapRange | childRange | binding
  deriving DecidableEq, Repr

structure Checked (edge : Edge) : Type where
  checked : edge.check = true

def validate (edge : Edge) : Except Error (Checked edge) :=
  if checked : edge.check = true then .ok ⟨checked⟩
  else if !decide edge.parent.Bounded then .error .parentRange
  else if !decide edge.gap.Bounded then .error .gapRange
  else if !decide edge.child.Bounded then .error .childRange
  else .error .binding

end IxCC.Aiur.AIR.Rank
