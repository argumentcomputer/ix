/- A6p per-pass fixture (`pass3` suite), elaborated at run time and in no Lake library.
O9, structural recursion over a split block with a cross field. In `Src`, `B` does not mention
`A`, so Pass 1 splits the block into `{B}` and `{A}`; `A.a` and `A.t` have fields of type `B` (cross
fields). Lean's `A.below` has a leaf for each `B` field, the Ix `below` of `{A}` does not, so the
handlers' paths shift (`x_1.2.1 ↦ x_1.1`, `x_1.2.2.1 ↦ x_1.2.1`). O9 rewrites `A.len`, `A.sum` (the
`DQSplit`/`SurgSplit`/C2 `len`) onto the Ix `brecOn` with the canonical handler `A.len._ix._f`
re-typed and re-pathed. Decision 5 (D1): the rewrites go to the canonical forms `A.len._ix`,
`A.sum._ix`, `A.cnt._ix`, which are the bytes of `Can`, where `B` and `A` are declared separately;
the Lean names keep their baselines (recorded `PJ-FORM-O9`, their callers `INHERITED`).
`len_succ` is an open unfolding of `A.len` by `rfl` against the unchanged Lean name. `A.cnt` with `B.cnt` (C2's `cnt`): Lean compiles `B.cnt b` as a call (`B.cnt` does not recurse
through `A`), so `A.cnt`'s handler reads no cross field and O9 fires too. Value pins by `rfl`. -/
set_option Elab.async false

namespace PassO9
namespace Src
mutual
inductive A
  | nil : A
  | a : B → A → A
  | t : A → B → A → A
inductive B
  | nil : B
  | b : Nat → B
end

def A.len : A → Nat
  | .nil => 0
  | .a _ x => x.len + 1
  | .t x _ y => x.len + y.len

def B.val : B → Nat
  | .nil => 7
  | .b n => n

def A.sum : A → Nat
  | .nil => 0
  | .a b x => b.val + x.sum
  | .t x b y => x.sum + b.val + y.sum

theorem len2 : A.len (.a .nil (.a .nil .nil)) = 2 := rfl
theorem len3 : A.len (.t (.a .nil .nil) (.b 4) (.a .nil .nil)) = 2 := rfl
theorem sum1 : A.sum (.a .nil .nil) = 7 := rfl
theorem sum2 : A.sum (.t (.a (.b 1) .nil) (.b 4) .nil) = 5 := rfl
theorem len_succ (x : A) (b : B) : (A.a b x).len = x.len + 1 := rfl

mutual
def A.cnt : A → Nat
  | .nil => 0
  | .a b x => B.cnt b + A.cnt x + 1
  | .t x b y => A.cnt x + B.cnt b + A.cnt y
def B.cnt : B → Nat
  | .nil => 10
  | .b n => n
end

theorem cnt1 : A.cnt (.a .nil .nil) = 11 := rfl
end Src

namespace Can
inductive B
  | nil : B
  | b : Nat → B
inductive A
  | nil : A
  | a : B → A → A
  | t : A → B → A → A

def A.len : A → Nat
  | .nil => 0
  | .a _ x => x.len + 1
  | .t x _ y => x.len + y.len

def B.val : B → Nat
  | .nil => 7
  | .b n => n

def A.sum : A → Nat
  | .nil => 0
  | .a b x => b.val + x.sum
  | .t x b y => x.sum + b.val + y.sum

theorem len2 : A.len (.a .nil (.a .nil .nil)) = 2 := rfl
theorem len3 : A.len (.t (.a .nil .nil) (.b 4) (.a .nil .nil)) = 2 := rfl
theorem sum1 : A.sum (.a .nil .nil) = 7 := rfl
theorem sum2 : A.sum (.t (.a (.b 1) .nil) (.b 4) .nil) = 5 := rfl
theorem len_succ (x : A) (b : B) : (A.a b x).len = x.len + 1 := rfl

mutual
def A.cnt : A → Nat
  | .nil => 0
  | .a b x => B.cnt b + A.cnt x + 1
  | .t x b y => A.cnt x + B.cnt b + A.cnt y
def B.cnt : B → Nat
  | .nil => 10
  | .b n => n
end

theorem cnt1 : A.cnt (.a .nil .nil) = 11 := rfl
end Can
end PassO9
