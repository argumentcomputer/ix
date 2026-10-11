/- image-gen fixture (`Tests/Ix/Compile/Image.lean`), elaborated at run time and in no Lake library:
   the prototype's `exp-prototype/CertProto/Cases/C5Collapse.lean` without its commands. -/
/-! Case 5: collapse (SurgCollapse): A ≅ B ↦ X. Functions with different arms (A.f/B.g, explicit
`@A.rec`), with equal arms (A.h/B.k), and match-only users. -/
set_option Elab.async false

namespace C5
namespace Src
mutual
inductive A
  | nil : A
  | a : B → A
inductive B
  | nil : B
  | b : A → B
end

noncomputable def f : A → Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) 100 (fun _ ih => ih * 2)

theorem f_ab : f (.a .nil) = 101 := rfl

mutual
def A.f : A → Nat
  | .nil => 0
  | .a b => b.g + 1
def B.g : B → Nat
  | .nil => 100
  | .b a => a.f * 2
end

theorem fg_ab : A.f (.a .nil) = 101 := rfl
theorem fg_bab : B.g (.b (.a .nil)) = 202 := rfl

mutual
def A.h : A → Nat
  | .nil => 0
  | .a b => b.k + 1
def B.k : B → Nat
  | .nil => 0
  | .b a => a.h + 1
end

def A.isNil : A → Bool
  | .nil => true
  | .a _ => false
def B.isNil : B → Bool
  | .nil => true
  | .b _ => false
end Src

namespace Can
inductive X
  | nil : X
  | a : X → X

def X.h : X → Nat
  | .nil => 0
  | .a x => x.h + 1

def X.isNil : X → Bool
  | .nil => true
  | .a _ => false

/-- the paired canonical form of A.f/B.g -/
def X.fg : X → Nat × Nat
  | .nil => (0, 100)
  | .a x => (x.fg.2 + 1, x.fg.1 * 2)
end Can
end C5

