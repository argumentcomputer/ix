/-! Surgery H1a: an alpha-collapsed mutual pair (A ≅ B) whose user code gives
the two members DIFFERENT minors/bodies. The canonical block keeps one class,
and call-site surgery drops the non-representative member's motive and minors
(surgery.rs ~501-536), reusing the kept member's minors at the other's nodes. -/
namespace SurgCollapse
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
end SurgCollapse
