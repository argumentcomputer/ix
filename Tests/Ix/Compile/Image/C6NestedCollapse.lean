/- image-gen fixture (`Tests/Ix/Compile/Image.lean`), elaborated at run time and in no Lake library:
   the prototype's `exp-prototype/CertProto/Cases/C6NestedCollapse.lean` without its commands. -/
/-! Case 6: collapse with nesting and bare occurrences (F4_NestedAlphaUsers). -/
set_option Elab.async false

namespace C6
namespace Src
mutual
inductive A : Type where
  | leaf
  | node : List B → A
inductive B : Type where
  | leaf
  | node : List A → B
end
noncomputable def r := @A.rec
noncomputable def rb := @A.brecOn
noncomputable def r1 := @A.rec_1
theorem t (a : A) : True :=
  A.rec (motive_1 := fun _ => True) (motive_2 := fun _ => True) (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    trivial (fun _ _ => trivial) trivial (fun _ _ => trivial) trivial (fun _ _ _ _ => trivial) trivial (fun _ _ _ _ => trivial) a
mutual
def A.size : A → Nat
  | .leaf => 1
  | .node bs => sizeL bs + 1
def B.size : B → Nat
  | .leaf => 1
  | .node as => sizeLA as + 1
def sizeL : List B → Nat
  | [] => 0
  | b :: bs => b.size + sizeL bs
def sizeLA : List A → Nat
  | [] => 0
  | a :: as => a.size + sizeLA as
end

mutual
def A.w : A → Nat
  | .leaf => 1
  | .node bs => wL bs + 10
def B.w : B → Nat
  | .leaf => 2
  | .node as => wLA as + 20
def wL : List B → Nat
  | [] => 0
  | b :: bs => b.w + wL bs
def wLA : List A → Nat
  | [] => 0
  | a :: as => a.w + wLA as
end
theorem size_ex : A.size (.node [.leaf, .node [.leaf]]) = 4 := rfl
theorem w_ex : A.w (.node [.leaf, .node [.leaf]]) = 33 := rfl
end Src

namespace Can
inductive X : Type where
  | leaf
  | node : List X → X
mutual
def X.size : X → Nat
  | .leaf => 1
  | .node xs => sizeL xs + 1
def sizeL : List X → Nat
  | [] => 0
  | x :: xs => x.size + sizeL xs
end
end Can
end C6

