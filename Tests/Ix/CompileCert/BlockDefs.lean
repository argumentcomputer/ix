namespace Tests.Ix.CompileCert.BlockDefs

inductive Void : Prop

def first {α : Sort u} (a _b : α) : α := a
def firstAlias {α : Sort u} (a _b : α) : α := a
theorem first_eq {α : Sort u} (a b : α) : first a b = a := rfl

structure Pair (α : Type u) where
  fst : α
  snd : α

def getFst {α : Type u} (p : Pair α) : α := p.fst

/-- Unlike an ordinary structure, this nested structure goes through the
reader's modeller and exercises its projection-to-recursor normalization. -/
structure Node where
  val : Nat
  kids : List Node

/-- Explicit constructor keeps this alternative's dependencies inside the
already checked Node/Nat cone; overloaded numeral elaboration adds OfNat. -/
def Node.zero (_n : Node) : Nat := Nat.zero

/-- Universe/parameter-sensitive source lowering control. -/
structure PolyNode (α : Type u) where
  val : α
  kids : List (PolyNode α)

end Tests.Ix.CompileCert.BlockDefs
