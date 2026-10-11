/-! A0 (WB-B4), the equal-arms neighbour of `SurgCollapse`: the same
alpha-collapsed mutual pair, but the two members' minors, bodies and
structural-recursion handlers are equal after compilation, so every dropped
argument equals the kept one at its canonical slot and the call sites compile.
The value pins are `rfl` theorems the kernels must accept. -/
namespace SurgCollapseEq
mutual
inductive A
  | nil : A
  | a : B → A
inductive B
  | nil : B
  | b : A → B
end

noncomputable def f : A → Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1)

theorem f_ab : f (.a .nil) = 1 := rfl
theorem f_aba : f (.a (.b (.a .nil))) = 3 := rfl

mutual
def A.f : A → Nat
  | .nil => 0
  | .a b => b.g + 1
def B.g : B → Nat
  | .nil => 0
  | .b a => a.f + 1
end

theorem fg_ab : A.f (.a .nil) = 1 := rfl
theorem gf_bab : B.g (.b (.a (.b .nil))) = 3 := rfl
end SurgCollapseEq
