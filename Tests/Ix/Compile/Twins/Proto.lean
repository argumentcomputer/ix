/-
  Twin families from the image prototype (`plans/review/auxgen-certify/
  exp-prototype/CertProto/Cases/*.lean`, PRO): each case declares a source
  block `Src` and a hand-written canonical block `Can` (permuted, split,
  evaporated, collapsed, Prop, parameters), with the same user functions.
  The `namespace Cx … end Cx` sections are verbatim; the prototype's own
  commands (`#lean_view`, `#bridge_*`, `#dump_seeds`) and its bridge
  theorems over the generated `View` namespace are left out. Case C4b
  (evaporation through the nested `Rose`) is left out: its source block
  fails to compile at this head (as `NestRoseSplit`, `Repro.lean`).
-/

namespace Tests.Ix.Compile.Twins.Proto

-- ===== C1Perm.lean =====
namespace C1
namespace Src
mutual
inductive Even
  | zero : Even
  | s : Odd → Even
inductive Odd
  | s : Even → Odd
end

mutual
def Odd.toNat : Odd → Nat
  | .s e => e.toNat + 1
def Even.toNat : Even → Nat
  | .zero => 0
  | .s o => o.toNat + 1
end

theorem three : Odd.toNat (.s (.s (.s .zero))) = 3 := rfl

def Even.isZero : Even → Bool
  | .zero => true
  | .s _ => false

noncomputable def Even.viaRec : Even → Nat :=
  @Even.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) (fun _ ih => ih + 1)
end Src

namespace Can
mutual
inductive Odd
  | s : Even → Odd
inductive Even
  | zero : Even
  | s : Odd → Even
end

mutual
def Odd.toNat : Odd → Nat
  | .s e => e.toNat + 1
def Even.toNat : Even → Nat
  | .zero => 0
  | .s o => o.toNat + 1
end

def Even.isZero : Even → Bool
  | .zero => true
  | .s _ => false

noncomputable def Even.viaRec : Even → Nat :=
  @Even.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1)
end Can
end C1


-- ===== C2Split.lean =====
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


-- ===== C3PropSplit.lean =====
namespace C3
namespace Src
mutual
inductive P1 : Prop
  | mk : True → P1
inductive P2 : Prop
  | mk : True → True → P2
end

theorem p1 (h : P1) : True := by
  cases h
  trivial

theorem p2 (h : P2) : True :=
  @P2.rec (fun _ => True) (fun _ => True) (fun _ => trivial) (fun _ _ => trivial) h
end Src

namespace Can
inductive P1 : Prop
  | mk : True → P1
inductive P2 : Prop
  | mk : True → True → P2
theorem p1 (h : P1) : True := by
  cases h
  trivial
theorem p2 (h : P2) : True :=
  @P2.rec (fun _ => True) (fun _ _ => trivial) h
end Can
end C3

namespace C3b
namespace Src
mutual
inductive Q1 : Prop
  | mk : True → Q1
inductive Q2 : Prop
  | mk : True → Q2
end

theorem q1 (h : Q1) : True := by
  cases h
  trivial

theorem q2 (h : Q2) : True :=
  @Q2.rec (fun _ => True) (fun _ => True) (fun _ => trivial) (fun _ => trivial) h
end Src

namespace Can
inductive X : Prop
  | mk : True → X
theorem q (h : X) : True := by
  cases h
  trivial
end Can
end C3b


-- ===== C4Evap.lean =====
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


-- ===== C5Collapse.lean =====
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


-- ===== C6NestedCollapse.lean =====
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


-- ===== C7IndPred.lean =====
namespace C7
namespace Src
mutual
inductive P : Nat → Prop
  | base : P 0
  | step : ∀ n, Q n → P n
inductive Q : Nat → Prop
  | base : Q 0
  | step : ∀ n, P n → Q n
end

theorem p_cases (h : P 0) : True := by
  cases h with
  | base => trivial
  | step q => trivial

mutual
theorem P.toQ : ∀ {n}, P n → Q n
  | _, .base => .base
  | _, .step n q => .step n (Q.toP q)
theorem Q.toP : ∀ {n}, Q n → P n
  | _, .base => .base
  | _, .step n p => .step n (P.toQ p)
end
end Src

namespace Can
inductive X : Nat → Prop
  | base : X 0
  | step : ∀ n, X n → X n
theorem X.self : ∀ {n}, X n → X n
  | _, .base => .base
  | _, .step n x => .step n (X.self x)
end Can
end C7

namespace C7b
namespace Src
mutual
inductive EvenP : Nat → Prop
  | zero : R → EvenP 0
  | succ : OddP n → EvenP (n+1)
inductive OddP : Nat → Prop
  | succ : EvenP n → OddP (n+1)
inductive R : Prop
  | mk : R
end

mutual
theorem EvenP.toR : EvenP n → R
  | .zero r => r
  | .succ h => OddP.toR h
theorem OddP.toR : OddP n → R
  | .succ h => EvenP.toR h
end

theorem EvenP.two : EvenP 2 := .succ (.succ (.zero .mk))
end Src

namespace Can
inductive R : Prop
  | mk : R
-- Ix canonical order (OddP, EvenP)
mutual
inductive OddP : Nat → Prop
  | succ : EvenP n → OddP (n+1)
inductive EvenP : Nat → Prop
  | zero : R → EvenP 0
  | succ : OddP n → EvenP (n+1)
end
mutual
theorem EvenP.toR : EvenP n → R
  | .zero r => r
  | .succ h => OddP.toR h
theorem OddP.toR : OddP n → R
  | .succ h => EvenP.toR h
end
end Can
end C7b


-- ===== C8Collapse3.lean =====
namespace C8
namespace Src
mutual
inductive A where
  | z
  | s : C → A
inductive B where
  | z
  | s : C → B
inductive C where
  | n : A → B → C
  | e
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
theorem f_ex : C.f (.n (.s .e) (.s .e)) = 13 := rfl

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

noncomputable def viaRec : C → Nat :=
  @C.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) 10 (fun _ ih => ih + 2)
    (fun _ _ iha ihb => iha + ihb) 5
theorem viaRec_ex : viaRec (.n (.s .e) (.s .e)) = 13 := rfl

def C.isE : C → Bool
  | .e => true
  | _ => false
end Src

namespace Can
mutual
inductive X where
  | z
  | s : C → X
inductive C where
  | n : X → X → C
  | e
end
mutual
def X.h : X → Nat
  | .z => 0
  | .s c => c.h + 1
def C.h : C → Nat
  | .n a b => a.h + b.h
  | .e => 5
end
def C.isE : C → Bool
  | .e => true
  | _ => false
end Can
end C8

namespace C8b
namespace Src
mutual
inductive A where
  | z
  | s : B → A
inductive B where
  | z
  | s : C → B
inductive C where
  | z
  | s : A → C
end
mutual
def A.f : A → Nat
  | .z => 1
  | .s b => b.f * 2
def B.f : B → Nat
  | .z => 3
  | .s c => c.f * 5
def C.f : C → Nat
  | .z => 7
  | .s a => a.f * 11
end
theorem f_ex : A.f (.s (.s (.s .z))) = 2 * 5 * 11 * 1 := rfl
noncomputable def viaRec : B → Nat :=
  @B.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) 1 (fun _ ih => ih * 2) 3 (fun _ ih => ih * 5) 7 (fun _ ih => ih * 11)
theorem viaRec_ex : viaRec (.s (.s (.s .z))) = 5 * 11 * 2 * 3 := rfl
def B.isZ : B → Bool
  | .z => true
  | .s _ => false
end Src
namespace Can
inductive X where
  | z
  | s : X → X
def X.isZ : X → Bool
  | .z => true
  | .s _ => false
end Can
end C8b


-- ===== C9Params.lean =====
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


/-- The cases: the name map from `Src` into `Can` (the prototype's
    `#lean_view` maps; a collapsed member and an equal-armed function map
    onto the representative), and the `Src` constants `Can` has no
    counterpart for (value theorems, functions with different arms over a
    collapsed pair, raw recursor users), which are not compared. -/
def cases : List (String × List (Lean.Name × Lean.Name) × List Lean.Name) := [
  ("C1", [], [`three]),
  ("C2", [], [`len2, `cnt1]),
  ("C2b", [], []),
  ("C3", [], []),
  ("C3b", [(`Q1, `X), (`Q2, `X), (`q1, `q), (`q2, `q)], []),
  ("C4", [], [`useRec1, `rawRec1, `useBelow1, `useBrecOn1, `size_ex, `useRec_ex]),
  ("C5", [(`A, `X), (`B, `X), (`B.b, `X.a), (`A.h, `X.h), (`B.k, `X.h),
      (`A.isNil, `X.isNil), (`B.isNil, `X.isNil)],
    [`f, `f_ab, `A.f, `B.g, `fg_ab, `fg_bab, `X.fg]),
  ("C6", [(`A, `X), (`B, `X), (`sizeLA, `sizeL), (`A.rec_2, `X.rec_1), (`A.below_2, `X.below_1),
      (`A.brecOn_2, `X.brecOn_1)],
    [`r, `rb, `r1, `t, `A.w, `B.w, `wL, `wLA, `size_ex, `w_ex]),
  ("C7", [(`P, `X), (`Q, `X), (`P.toQ, `X.self), (`Q.toP, `X.self)], [`p_cases]),
  ("C7b", [], [`EvenP.two]),
  ("C8", [(`A, `X), (`B, `X), (`A.h, `X.h), (`B.h, `X.h)],
    [`A.f, `B.f, `C.f, `f_ex, `viaRec, `viaRec_ex]),
  ("C8b", [(`A, `X), (`B, `X), (`C, `X)],
    [`A.f, `B.f, `C.f, `f_ex, `viaRec, `viaRec_ex]),
  ("C9", [], [`depth_ex]),
  ("C9b", [(`A, `X), (`B, `X), (`B.b, `X.a)], [`A.f, `B.g, `f_ex, `viaRec])
]

end Tests.Ix.Compile.Twins.Proto
