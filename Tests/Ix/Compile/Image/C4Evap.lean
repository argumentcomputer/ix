/- image-gen fixture (`Tests/Ix/Compile/Image.lean`), elaborated at run time and in no Lake library:
   the prototype's `exp-prototype/CertProto/Cases/C4Evap.lean` without its commands. -/
/-! Case 4: evaporated nested auxiliary (EvapClosure / F2_SplitNestedClosure) and the Rose
container variant (NestRoseSplit / F3). -/
set_option Elab.async false

namespace C4
namespace Src
mutual
inductive A
  | mk : List B → A
inductive B
  | leaf : B
end

noncomputable def useRec : A → Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 5 0 (fun _ _ ihb ihl => ihb + ihl)
noncomputable def useRec1 : List B → Nat :=
  @A.rec_1 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 5 0 (fun _ _ ihb ihl => ihb + ihl)
noncomputable def rawRec1 := @A.rec_1
def useBelow1 (l : List B) : Type := @A.below_1 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) l
noncomputable def useBrecOn1 (l : List B) : Nat :=
  @A.brecOn_1 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) l (fun _ _ => 1) (fun _ _ => 2) (fun _ _ => 3)

mutual
def A.size : A → Nat
  | .mk bs => sizeL bs + 1
def sizeL : List B → Nat
  | [] => 0
  | b :: bs => B.size b + sizeL bs
def B.size : B → Nat
  | .leaf => 1
end

theorem size_ex : A.size (.mk [.leaf, .leaf]) = 3 := rfl
theorem useRec_ex : useRec (.mk [.leaf, .leaf]) = 11 := rfl

def A.isMk : A → Bool
  | .mk _ => true
end Src

namespace Can
inductive B
  | leaf : B
inductive A
  | mk : List B → A

noncomputable def useRec : A → Nat :=
  @A.rec (fun _ => Nat) (fun l => @List.rec B (fun _ => Nat) 0 (fun b _ ihl => @B.rec (fun _ => Nat) 5 b + ihl) l + 1)
noncomputable def useRec1 : List B → Nat :=
  @List.rec B (fun _ => Nat) 0 (fun b _ ihl => @B.rec (fun _ => Nat) 5 b + ihl)

mutual
def A.size : A → Nat
  | .mk bs => sizeL bs + 1
def sizeL : List B → Nat
  | [] => 0
  | b :: bs => B.size b + sizeL bs
def B.size : B → Nat
  | .leaf => 1
end

def A.isMk : A → Bool
  | .mk _ => true
end Can
end C4

namespace C4b
inductive Rose (α : Type)
  | node : α → List (Rose α) → Rose α

namespace Src
mutual
inductive A2
  | mk : Rose B2 → A2
inductive B2
  | leaf
end

def A2.isMk : A2 → Bool
  | .mk _ => true

mutual
def A2.cnt : A2 → Nat
  | .mk r => roseCnt r + 1
def roseCnt : Rose B2 → Nat
  | .node b rs => B2.cnt b + listCnt rs
def listCnt : List (Rose B2) → Nat
  | [] => 0
  | r :: rs => roseCnt r + listCnt rs
def B2.cnt : B2 → Nat
  | .leaf => 1
end

theorem cnt_ex : A2.cnt (.mk (.node .leaf [.node .leaf []])) = 3 := rfl
noncomputable def rawRec := @A2.rec
noncomputable def rawRec2 := @A2.rec_2
end Src

namespace Can
inductive B2
  | leaf
inductive A2
  | mk : Rose B2 → A2

def A2.isMk : A2 → Bool
  | .mk _ => true

mutual
def A2.cnt : A2 → Nat
  | .mk r => roseCnt r + 1
def roseCnt : Rose B2 → Nat
  | .node b rs => B2.cnt b + listCnt rs
def listCnt : List (Rose B2) → Nat
  | [] => 0
  | r :: rs => roseCnt r + listCnt rs
def B2.cnt : B2 → Nat
  | .leaf => 1
end
end Can
end C4b

