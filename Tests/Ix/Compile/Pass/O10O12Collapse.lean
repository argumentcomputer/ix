/- A6p per-pass fixture (`pass3` suite), elaborated at run time and in no Lake library.
O10 and O12, structural recursion over a collapsed block (the prototype's C5 and C8).
`Src.A`, `Src.B` are alpha-equivalent (one class). `A.h`/`B.k` have equal arms: O10 compiles both to
the twin's single function (`Can.X.h`, `Can` declaring the class once). `A.f`/`B.g` have different
arms: O12 compiles both through the shared pair-valued helper `fg` (`A.f := λ t. (fg t).1`);
`Perm` declares the same block and functions in the other order, and `fg`, `A.f`, `B.g` are
byte-equal between `Src` and `Perm` (the pair's order is by content). `C8.Src` is a collapsed pair
`A`, `B` next to a lifted member `C`: `A.h`/`B.h`/`C.h` have equal arms per class, O10 compiles
them to `C8.Can`'s `X.h`/`C.h`; `A.f`/`B.f`/`C.f` (different arms over two slots) decline. Value pins
by `rfl`. -/
set_option Elab.async false

namespace PassO10
namespace Src
mutual
inductive A
  | nil : A
  | a : B → A
inductive B
  | nil : B
  | b : A → B
end

mutual
def A.h : A → Nat
  | .nil => 0
  | .a b => b.k + 1
def B.k : B → Nat
  | .nil => 0
  | .b a => a.h + 1
end

mutual
def A.f : A → Nat
  | .nil => 0
  | .a b => b.g + 1
def B.g : B → Nat
  | .nil => 100
  | .b a => a.f * 2
end

theorem h_two : A.h (.a (.b .nil)) = 2 := rfl
theorem k_one : B.k (.b .nil) = 1 := rfl
theorem fg_ab : A.f (.a .nil) = 101 := rfl
theorem fg_bab : B.g (.b (.a .nil)) = 202 := rfl
end Src

namespace Perm
mutual
inductive B
  | nil : B
  | b : A → B
inductive A
  | nil : A
  | a : B → A
end

mutual
def B.g : B → Nat
  | .nil => 100
  | .b a => a.f * 2
def A.f : A → Nat
  | .nil => 0
  | .a b => b.g + 1
end

theorem fg_ab : A.f (.a .nil) = 101 := rfl
theorem fg_bab : B.g (.b (.a .nil)) = 202 := rfl
end Perm

namespace Can
inductive X
  | nil : X
  | a : X → X

def X.h : X → Nat
  | .nil => 0
  | .a x => x.h + 1

theorem h_two : X.h (.a (.a .nil)) = 2 := rfl
end Can

namespace C8
namespace Src
mutual
inductive A
  | z : A
  | s : C → A
inductive B
  | z : B
  | s : C → B
inductive C
  | n : A → B → C
  | e : C
end

mutual
def A.h : A → Nat
  | .z => 0
  | .s c => c.h + 1
def B.h : B → Nat
  | .z => 0
  | .s c => c.h + 1
def C.h : C → Nat
  | .n a b => a.h + b.h
  | .e => 5
end

mutual
def A.f : A → Nat
  | .z => 0
  | .s c => c.f + 1
def B.f : B → Nat
  | .z => 10
  | .s c => c.f + 2
def C.f : C → Nat
  | .n a b => a.f + b.f
  | .e => 5
end

theorem h_ex : C.h (.n (.s .e) (.s .e)) = 12 := rfl
theorem f_ex : C.f (.n (.s .e) (.s .e)) = 13 := rfl
end Src

namespace Can
mutual
inductive X
  | z : X
  | s : C → X
inductive C
  | n : X → X → C
  | e : C
end

mutual
def X.h : X → Nat
  | .z => 0
  | .s c => c.h + 1
def C.h : C → Nat
  | .n a b => a.h + b.h
  | .e => 5
end

theorem h_ex : C.h (.n (.s .e) (.s .e)) = 12 := rfl
end Can
end C8
end PassO10
