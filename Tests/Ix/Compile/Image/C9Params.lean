/- image-gen fixture (`Tests/Ix/Compile/Image.lean`), elaborated at run time and in no Lake library:
   the prototype's `exp-prototype/CertProto/Cases/C9Params.lean` without its commands. -/
/-! Case 9 (extra): universe-polymorphic, parametrised blocks with reflexive (function-typed) fields.
9a: split with a cross field; 9b: collapse. -/
set_option Elab.async false

universe u

namespace C9
namespace Src
mutual
inductive A (α : Type u) where
  | nil : A α
  | a : B α → (Nat → A α) → A α
inductive B (α : Type u) where
  | leaf : α → B α
end
def A.depth {α : Type u} : A α → Nat
  | .nil => 0
  | .a _ f => (f 0).depth + 1
def A.isNil {α : Type u} : A α → Bool
  | .nil => true
  | .a _ _ => false
theorem depth_ex : (A.a (.leaf 3) (fun _ => .nil) : A Nat).depth = 1 := rfl
end Src
namespace Can
inductive B (α : Type u) where
  | leaf : α → B α
inductive A (α : Type u) where
  | nil : A α
  | a : B α → (Nat → A α) → A α
def A.depth {α : Type u} : A α → Nat
  | .nil => 0
  | .a _ f => (f 0).depth + 1
def A.isNil {α : Type u} : A α → Bool
  | .nil => true
  | .a _ _ => false
end Can
end C9

namespace C9b
namespace Src
mutual
inductive A (α : Type u) where
  | nil : α → A α
  | a : (Nat → B α) → A α
inductive B (α : Type u) where
  | nil : α → B α
  | b : (Nat → A α) → B α
end
mutual
def A.f {α : Type u} : A α → Nat
  | .nil _ => 1
  | .a g => (g 0).g + 10
def B.g {α : Type u} : B α → Nat
  | .nil _ => 2
  | .b g => (g 0).f * 3
end
theorem f_ex : (A.a (fun _ => .b (fun _ => .nil ())) : A Unit).f = 13 := rfl
noncomputable def viaRec {α : Type u} : A α → Nat :=
  @A.rec α (fun _ => Nat) (fun _ => Nat) (fun _ => 1) (fun _ ih => ih 0 + 10) (fun _ => 2) (fun _ ih => ih 0 * 3)
end Src
namespace Can
inductive X (α : Type u) where
  | nil : α → X α
  | a : (Nat → X α) → X α
end Can
end C9b

