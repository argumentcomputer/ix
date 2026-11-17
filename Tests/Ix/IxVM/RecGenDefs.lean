import Lean

/-! # Inductive families for the native recursor generator suite (fixtures)

Ordinary, kernel-checked Lean declarations, each a one-type, non-nested family, crossing the
shapes the native recursor generator distinguishes: the Π-depth of a reflexive field
(0 to 3), the number of indices (0 to 2), parameters and universe levels, a `let` and an
annotation wrapper in a field domain, several recursive fields, a recursive field before an
ordinary one, small and large elimination, K-like families, families without constructors.
`Tests.Ix.IxVM.RecGen` checks their recursor records. -/

namespace Tests.Ix.IxVM.RecGenDefs

universe u v w

/-! ## Reflexive depth 0 to 3, no index -/

inductive D0I0 where
  | leaf : D0I0
  | node : D0I0 → D0I0

inductive D1I0 where
  | leaf : D1I0
  | node : (Nat → D1I0) → D1I0

inductive D2I0 where
  | leaf : D2I0
  | node : (Nat → Bool → D2I0) → D2I0

inductive D3I0 where
  | leaf : D3I0
  | node : (Nat → Bool → Unit → D3I0) → D3I0

/-! ## One index -/

inductive D0I1 : Nat → Type where
  | leaf : D0I1 0
  | node : (n : Nat) → D0I1 n → D0I1 (n + 1)

inductive D1I1 : Nat → Type where
  | leaf : D1I1 0
  | node : (n : Nat) → ((k : Nat) → D1I1 (n + k)) → D1I1 (n + 1)

inductive D2I1 : Nat → Type where
  | leaf : D2I1 0
  | node : (n : Nat) → ((k : Nat) → (b : Bool) → D2I1 (if b then n else k)) → D2I1 n

inductive D3I1 : Nat → Type where
  | leaf : D3I1 0
  | node : (n : Nat) → ((k : Nat) → (b : Bool) → (x : Unit) → D3I1 (k + n)) → D3I1 n

/-! ## Two indices -/

inductive D0I2 : Nat → Bool → Type where
  | leaf : D0I2 0 true
  | node : (n : Nat) → (b : Bool) → D0I2 n b → D0I2 (n + 1) (!b)

inductive D1I2 : Nat → Bool → Type where
  | leaf : D1I2 0 false
  | node : (n : Nat) → ((k : Nat) → D1I2 k (k == n)) → D1I2 n true

inductive D2I2 : Nat → Bool → Type where
  | leaf : D2I2 0 false
  | node : (n : Nat) → ((k : Nat) → (b : Bool) → D2I2 (n + k) b) → D2I2 n false

inductive D3I2 : Nat → Bool → Type where
  | leaf : D3I2 0 false
  | node : (n : Nat) → (c : Bool) → ((k : Nat) → (b : Bool) → (x : Unit) → D3I2 k (b && c)) →
      D3I2 (n + 1) c

/-! ## Parameters and universe levels with reflexive and indexed fields -/

inductive PW (α : Type u) (β : α → Type v) : Type (max u v) where
  | sup (a : α) (f : β a → PW α β) : PW α β

inductive PD1I1 (α : Type u) (β : α → Type v) : α → Type (max u v) where
  | leaf (a : α) : PD1I1 α β a
  | node (a : α) (f : (b : β a) → PD1I1 α β a) (g : (c : α) → (b : β c) → PD1I1 α β c) :
      PD1I1 α β a

inductive PVec (α : Type u) : Nat → Type u where
  | nil : PVec α 0
  | cons {n : Nat} (a : α) (v : PVec α n) : PVec α (n + 1)

inductive PFinFn where
  | mk (n : Nat) (f : Fin n → PFinFn) : PFinFn

inductive PSig {α : Sort u} (β : α → Sort v) : Sort (max 1 u v) where
  | mk (a : α) (b : β a) : PSig β

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnitLike : Sort u where
  | unit : PUnitLike

/-! ## Several recursive fields, and a recursive field before an ordinary one -/

inductive Tree2 where
  | leaf : Tree2
  | node : Tree2 → Tree2 → Tree2

inductive TreeA (α : Type u) where
  | leaf : TreeA α
  | node (l : TreeA α) (a : α) (r : TreeA α) (n : Nat) : TreeA α

inductive RecFirst where
  | base : Nat → RecFirst
  | step : RecFirst → Nat → Bool → RecFirst

inductive Mixed (α : Type) : Nat → Type where
  | z : Mixed α 0
  | s (n : Nat) (m : Mixed α n) (a : α) (f : Nat → Mixed α n) (b : Bool) (m' : Mixed α (n + 1)) :
      Mixed α (n + 2)

/-! ## A `let` in a field domain -/

inductive LetField where
  | mk : (n : Nat) → (let m := n + 1; Fin m) → LetField

structure LetStruct where
  n : Nat
  h : let m := n + 1; m = m

inductive LetIdx : Nat → Type where
  | mk : (n : Nat) → (let m := n + 2; Fin m → Bool) → LetIdx n → LetIdx (n + 1)
  | z : LetIdx 0

/-! ## Annotation wrappers at field and parameter domains -/

inductive WrapCtor where
  | mk (x : Nat) (flag : Bool := false) : WrapCtor
  | node (child : WrapCtor) (n : Nat := 3) : WrapCtor

structure WrapAuto where
  n : Nat
  h : n = n := by rfl

class WrapOut (α : outParam Type) (β : Type) where
  f : β → α
  g : α → β

inductive WrapIdx : Nat → Type where
  | mk (n : Nat) (k : Nat := n) (prev : WrapIdx k) : WrapIdx (n + 1)
  | z : WrapIdx 0

/-! ## Small and large elimination, K-like families, no constructor -/

inductive SmallOr (p q : Prop) : Prop where
  | inl : p → SmallOr p q
  | inr : q → SmallOr p q

inductive SmallEx {α : Type} (p : α → Prop) : Prop where
  | intro (x : α) (h : p x) : SmallEx p

inductive SmallRec : Nat → Prop where
  | base : SmallRec 0
  | step (n : Nat) : SmallRec n → SmallRec (n + 1)

inductive SmallRefl (r : Nat → Nat → Prop) : Nat → Prop where
  | base : SmallRefl r 0
  | step (n : Nat) (h : (k : Nat) → r k n → SmallRefl r k) (h' : SmallRefl r n) : SmallRefl r (n + 1)

inductive LargeAnd (p q : Prop) : Prop where
  | intro : p → q → LargeAnd p q

inductive AccLike {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → AccLike r y) : AccLike r x

inductive KUnit : Prop where
  | intro : KUnit

inductive KEq {α : Sort u} (a : α) : α → Prop where
  | refl : KEq a a

inductive KHEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | refl {α : Sort u} (a : α) : KHEq a a

inductive Empty0 : Type

inductive Empty1 : Nat → Type

inductive EmptyP : Prop

inductive EmptyPI (α : Type u) : α → Prop

/-! ## Structures and enumerations -/

structure S3 (α : Type u) where
  a : α
  b : Nat
  c : a = a

structure SDep where
  n : Nat
  v : Fin n
  h : v.val = v.val

inductive Color where
  | r | g | b

inductive Wide where
  | a (x : Nat) (y : Bool)
  | b
  | c (x : Wide) (y : Wide) (z : Nat → Wide)
  | d (f : Nat → Bool → Wide) (g : Wide)

/-! ## Reduction through a recursor -/

theorem d0i0_iota :
    @D0I0.rec (fun _ => Bool) true (fun _ (ih : Bool) => !ih) (D0I0.node D0I0.leaf) = false := rfl

theorem tree2_iota :
    @Tree2.rec (fun _ => Bool) true (fun _ _ (a b : Bool) => a && !b)
      (Tree2.node Tree2.leaf (Tree2.node Tree2.leaf Tree2.leaf)) = true := rfl

/-- The names of the families whose recursor records the suite checks. -/
def families : List Lean.Name := [
  ``D0I0, ``D1I0, ``D2I0, ``D3I0, ``D0I1, ``D1I1, ``D2I1, ``D3I1, ``D0I2, ``D1I2, ``D2I2, ``D3I2,
  ``PW, ``PD1I1, ``PVec, ``PFinFn, ``PSig, ``PUnitLike, ``Tree2, ``TreeA, ``RecFirst, ``Mixed,
  ``LetField, ``LetStruct, ``LetIdx, ``WrapCtor, ``WrapAuto, ``WrapOut, ``WrapIdx,
  ``SmallOr, ``SmallEx, ``SmallRec, ``SmallRefl, ``LargeAnd, ``AccLike, ``KUnit, ``KEq, ``KHEq,
  ``Empty0, ``Empty1, ``EmptyP, ``EmptyPI, ``S3, ``SDep, ``Color, ``Wide]

/-- Theorems whose proofs reduce through a recursor of the families. -/
def reductions : List Lean.Name := [``d0i0_iota, ``tree2_iota]

end Tests.Ix.IxVM.RecGenDefs
