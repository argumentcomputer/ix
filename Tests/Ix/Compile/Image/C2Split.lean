/- image-gen fixture (`Tests/Ix/Compile/Image.lean`), elaborated at run time and in no Lake library:
   the prototype's `exp-prototype/CertProto/Cases/C2Split.lean` without its commands. -/
/-! Case 2: split with a cross field (SurgSplit) + mutual functions recursing into B. -/
set_option Elab.async false

namespace C2
namespace Src
mutual
inductive A
  | nil : A
  | a : B → A → A
inductive B
  | nil : B
end

def A.len : A → Nat
  | .nil => 0
  | .a _ x => x.len + 1

theorem len2 : A.len (.a .nil (.a .nil .nil)) = 2 := rfl

mutual
def A.cnt : A → Nat
  | .nil => 0
  | .a b x => B.cnt b + A.cnt x + 1
def B.cnt : B → Nat
  | .nil => 10
end

theorem cnt1 : A.cnt (.a .nil .nil) = 11 := rfl

def A.isNil : A → Bool
  | .nil => true
  | .a _ _ => false

noncomputable def A.viaRec : A → Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ _ ihb iha => ihb + iha + 1) 7
end Src

namespace Can
inductive B
  | nil : B
inductive A
  | nil : A
  | a : B → A → A

def A.len : A → Nat
  | .nil => 0
  | .a _ x => x.len + 1

mutual
def A.cnt : A → Nat
  | .nil => 0
  | .a b x => B.cnt b + A.cnt x + 1
def B.cnt : B → Nat
  | .nil => 10
end

def A.isNil : A → Bool
  | .nil => true
  | .a _ _ => false

noncomputable def A.viaRec : A → Nat :=
  @A.rec (fun _ => Nat) 0 (fun b _ iha => @B.rec (fun _ => Nat) 7 b + iha + 1)
end Can
end C2

/-! C2b: split WITHOUT a cross field (A does not mention B): structural recursion claimed rfl. -/
namespace C2b
namespace Src
mutual
inductive A
  | nil : A
  | cons : A → A
inductive B
  | leaf : B
  | two : B → B → B
end
def A.len : A → Nat
  | .nil => 0
  | .cons x => x.len + 1
def B.size : B → Nat
  | .leaf => 1
  | .two x y => x.size + y.size
end Src
namespace Can
inductive A
  | nil : A
  | cons : A → A
inductive B
  | leaf : B
  | two : B → B → B
def A.len : A → Nat
  | .nil => 0
  | .cons x => x.len + 1
def B.size : B → Nat
  | .leaf => 1
  | .two x y => x.size + y.size
end Can
end C2b
