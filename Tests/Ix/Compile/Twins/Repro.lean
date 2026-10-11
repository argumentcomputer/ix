/-
  Retained twin families from the oracle experiment (ORA): each original
  block and its
  hand-written twin in Ix's canonical form (reordered, split into
  separately declared components with the block's universes and
  parameters, or collapsed). The sources are verbatim, wrapped in
  `Orig`/`Twin` namespaces; the blackbox reproducers F1, F2 and F4 (no
  namespace of their own) are wrapped in `F1`, `F2`, `F4`. The name maps
  are the experiment's `Maps/*.map`, transcribed in
  `Tests.Ix.Compile.Twins` (`reproFamilies`).

  Historical exclusions at fixture import (not new current-run verdicts):
  - `F3_SplitRoseRace`: the compile races (BB F3; refused deterministically
    after A0's evaporation fix);
  - `AliasIdx`: `T` fails in both presentations (`missingConstant`, WB H5);
  - `NestMutExtT`: the Rust compiler rejects the whole environment
    (`non-canonical inductive flags`, numNested 2 vs 4; WB-A1, fixed by A0);
  - `NestRoseSplit`: `A2.brecOn_1.go` fails (`missingConstant A2.below_2`;
    refused deterministically after A0's evaporation fix).
  `UnivSplit` is declared but not a twins family: its twin gives the
  split-off member fewer universes, which Def 4.3 does not count as a
  presentation (design document §4.7 (a)); the oracle leg uses it.
  `SurgIdx.B.size` (and its users) fails in the original (the eta call-site
  adapter, WB SurgIdx, retired with surgery in A3); the family skips it.
-/

namespace Tests.Ix.Compile.Twins.Repro.Orig

-- ===== Ctl =====
/-! Control group: blocks that should arrive canonical. -/
namespace Ctl
inductive N
  | z : N
  | s : N → N

def N.toNat : N → Nat
  | .z => 0
  | .s n => n.toNat + 1

theorem one : N.toNat (.s .z) = 1 := rfl

inductive Tree
  | node : List Tree → Tree

mutual
def Tree.size : Tree → Nat
  | .node ts => 1 + Tree.sizes ts
def Tree.sizes : List Tree → Nat
  | [] => 0
  | t :: ts => t.size + Tree.sizes ts
end

theorem tsz : Tree.size (.node [.node []]) = 2 := rfl

inductive Ev : Nat → Prop
  | z : Ev 0
  | ss {n : Nat} : Ev n → Ev (n + 2)

theorem Ev.triv {n : Nat} (h : Ev n) : True := by
  induction h <;> trivial

theorem Ev.two_le : ∀ {n : Nat}, Ev (n + 2) → Ev n
  | _, .ss h => h

structure Pt where
  x : Nat
  y : Nat
  deriving DecidableEq, BEq, Hashable

def Pt.swap (p : Pt) : Pt := ⟨p.y, p.x⟩

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

def Vec.toList {α : Type u} : {n : Nat} → Vec α n → List α
  | _, .nil => []
  | _, .cons a v => a :: v.toList
end Ctl

-- ===== DQMut =====
/-! Disputed question, case 2: a split block ({B} below {A}) with a MUTUAL pair of
structurally recursive functions that recurse across the two types. -/
namespace DQMut
mutual
inductive A
  | nil : A
  | a : B → A → A
inductive B
  | nil : B
  | s : B → B
end

mutual
def A.size : A → Nat
  | .nil => 0
  | .a b x => B.size b + A.size x + 1
def B.size : B → Nat
  | .nil => 0
  | .s b => B.size b + 1
end

theorem size2 : A.size (.a (.s .nil) .nil) = 2 := rfl
end DQMut

-- ===== DQReord =====
/-! Reorder with user functions: a genuinely mutual pair declared in the order Ix
does NOT keep (Ix's canonical order is Odd, Even; measured on the twin). -/
namespace DQReord
mutual
inductive Even
  | z : Even
  | s : Odd → Even
inductive Odd
  | s : Even → Odd
end

mutual
def Even.toNat : Even → Nat
  | .z => 0
  | .s o => o.toNat + 1
def Odd.toNat : Odd → Nat
  | .s e => e.toNat + 1
end

theorem two : Even.toNat (.s (.s .z)) = 2 := rfl
end DQReord

-- ===== DQSplit =====
/-! Disputed question, case 1: a split block (B is not recursive through A) with a
field of the split-off member's type, and functions by structural recursion over A. -/
namespace DQSplit
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

def B.val : B → Nat
  | .nil => 7

def A.sum : A → Nat
  | .nil => 0
  | .a b x => b.val + x.sum

theorem len2 : A.len (.a .nil (.a .nil .nil)) = 2 := rfl
theorem sum1 : A.sum (.a .nil .nil) = 7 := rfl
theorem len_succ (x : A) (b : B) : (A.a b x).len = x.len + 1 := rfl
end DQSplit

-- ===== EvapClosure =====
/-! SCC split with an evaporated nested aux (`List B`, B split away), in a
closure compile: `Ix.EnvScope.collectDeps` may not bring in `List.rec`, the
evaporation alias target (aux_gen.rs:1273-1277). -/
namespace EvapClosure
mutual
inductive A where
  | mk : List B → A
inductive B where
  | leaf : B
end
end EvapClosure

-- ===== F1_Collapse2p1 =====
namespace F1
/-! F1 (class B, meta ingress): two members alpha-equivalent through a third.
`ix compile F1_Collapse2p1.lean --no-build --consts A,B,C --out c.ixe`
`ix check-rs c.ixe` -> `A: ctor return type: head is not the inductive` (0/9)
`ix check-rs --anon c.ixe` 6/6; `ix check-lean c.ixe` -> `C.n: unknown constant 2f6342baee0d`;
`ix check-lean --anon` 6/6; kernel-check-ixe accepts every record.
Neighbours that pass: the 2-member pair alone (A ↔ B), the 3-ring, the alpha triple. -/
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
end F1

-- ===== F2_SplitNestedClosure =====
namespace F2
/-! F2 (classes A, B, C; closure mode only): SCC split, nested occurrence evaporates.
Whole file: compiles, check-rs 40/40.
`ix compile F2_SplitNestedClosure.lean --no-build --consts A` -> block FAILED A (2 members):
  invalid mutual block: conflicting call-site plans for 'A.rec_1' — two blocks claim one source-indexed aux name
`--consts A.rec` (also A.casesOn, A.below, B.rec, A.rec_1): compiles; A.rec_1 address differs from the
whole compile (efcb43e4… vs 41369b84…) and `ix check-rs` rejects it:
  populate_recursor_rules_from_block: canonical header mismatch at peer 0
Same with Tri/Rose/E1 (any container) in place of List. -/
mutual
inductive A
  | mk : List B → A
inductive B
  | leaf
end
end F2

-- ===== F4_NestedAlphaUsers =====
namespace F4
/-! F4 (class B, both kernels): a nested alpha-collapsing pair; constants that USE the
collapsed recursor without its full argument list are ill-typed after compilation.
`ix compile F4_NestedAlphaUsers.lean --no-build --out na.ixe`
`ix check-rs na.ixe --ns A,B,r,t,sizeL,sizeLA` -> 79/84:
  ✗ r: AppTypeMismatch            (unapplied `@A.rec`; also `@A.brecOn`, `@A.rec_1`)
  ✗ A.size._unsafe_rec, B.size._unsafe_rec, sizeL._unsafe_rec, sizeLA._unsafe_rec: AppTypeMismatch
kernel-check-ixe (certified) rejects `r`, `@A.brecOn`, `@A.rec_1` users with "application type mismatch"
(the `_unsafe_rec` ones are unsafe and declined there).
Passes: `t` (fully applied A.rec), A.size/B.size themselves, and the same users on a NON-nested
alpha pair (A | z | s : B → A, B | z | s : A → B). -/
mutual
inductive A : Type where
  | leaf
  | node : List B → A
inductive B : Type where
  | leaf
  | node : List A → B
end
noncomputable def r := @A.rec
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
end F4

-- ===== FieldBelow =====
/-! H3: a constant named `X.below` / `X.brecOn` that is not an auxiliary.
Lean generates `.below`/`.brecOn` only for recursive inductives, so for a
non-recursive inductive (or a structure) the names are free for user code.
aux-gen gates `.below` generation on the name being present with a type that
ends in `Sort _` (`is_below_shaped`, aux_gen.rs:1317), not on recursiveness. -/
namespace FieldBelow
structure S where
  below : Nat → Type

def useS (s : S) : Type := s.below 0

def sNat : S := ⟨fun _ => Nat⟩
theorem useS_nat : useS sNat = Nat := rfl

inductive T
  | a
  | b

def T.below (_ : T) : Type := Nat
def T.brecOn (_ : T) : Nat := 7

theorem t_below : T.below T.a = Nat := rfl
theorem t_brecOn : T.brecOn T.b = 7 := rfl

structure SP where
  below : Prop

theorem sp (s : SP) (h : s.below) : s.below := h
end FieldBelow

-- ===== PropCollapse =====
/-! Collapsed Prop mutual pair (the Canonicity.lean PropCollapseA fixture
shape): the non-representative's `.below.casesOn` (seam audit H1; the
nestedprop fix says it fixes this) plus a user `cases` (recursor universe). -/
namespace PropCollapse
mutual
inductive P : Nat → Prop
  | step : ∀ n, Q n → P n
inductive Q : Nat → Prop
  | step : ∀ n, P n → Q n
end

theorem p_cases (h : P 0) : Q 0 := by
  cases h with
  | step q => exact q
end PropCollapse

-- ===== PropSplit =====
/-! A Lean mutual block of Prop inductives whose members do not reference
each other. In Lean's (2-type) block the recursors eliminate only into Prop.
aux-gen splits the block into SCC singletons, and a singleton one-constructor
Prop inductive whose fields are proofs gets LARGE elimination, so the
regenerated `.rec`/`.casesOn` gain a universe parameter. -/
namespace PropSplit
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

-- Alpha-equivalent pair (collapse instead of split).
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
end PropSplit

-- ===== RecAlias =====
/-! Recursive fields hidden behind a reducible alias (the kernel whnf's field
types when it finds recursive arguments; IndPredBelow builds the Prop `.below`
from the recursor's minors). ix's non-nested Prop `.below` path builds from the
constructor types and recognises recursive fields by their head constant. -/
namespace RecAlias
abbrev Id' (p : Prop) : Prop := p

inductive PA : Nat → Prop
  | base : PA 0
  | step {n : Nat} : Id' (PA n) → PA (n + 1)

theorem PA.triv : ∀ {n : Nat}, PA n → True
  | _, .base => trivial
  | _, .step h => PA.triv h

abbrev IdT (α : Type) : Type := α

inductive TA
  | leaf
  | node : IdT TA → TA

def TA.size : TA → Nat
  | .leaf => 0
  | .node t => TA.size t + 1

theorem ta2 : TA.size (.node (.node .leaf)) = 2 := rfl
end RecAlias

-- ===== SurgCollapse =====
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

-- ===== SurgIdx =====
/-! Surgery H2: block-wide `n_indices` (taken from the first `X.rec`) used to
slice `.brecOn` call sites of a member with a different index count. -/
namespace SurgIdx
mutual
inductive A : Nat → Type
  | mk : A 0
inductive B : Type
  | leaf : B
  | node : B → B
end

def B.size : B → Nat
  | .leaf => 0
  | .node b => b.size + 1

theorem bsize : B.size (.node .leaf) = 1 := rfl
end SurgIdx

namespace SurgIdx2
mutual
inductive A : Type
  | mk : A
inductive B : Nat → Type
  | leaf : B 0
  | node {n : Nat} : B n → B (n + 1)
end

def B.size : {n : Nat} → B n → Nat
  | _, .leaf => 0
  | _, .node b => b.size + 1

theorem bsize : B.size (.node .leaf) = 1 := rfl
end SurgIdx2

-- ===== SurgSplit =====
/-! Surgery H1b: an SCC split ({B}, {A}) of a mutual block, with structural
recursion on A. Lean's `A.below` has an entry for the B field; the canonical
{A} below does not, so the handler's PProd projections shift. -/
namespace SurgSplit
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
end SurgSplit

-- ===== UnivSplit =====
/-! Universe pruning on a split: the block's universe `v` occurs only in PA's constructor;
the split-off PB, declared alone, has no universe parameter. -/
namespace UnivSplit
universe v
mutual
inductive PA : Prop
  | a : PB → (α : Sort v) → α → PA
inductive PB : Prop
  | b : PB → PB
  | z : PB
end

theorem pb_triv (h : PB) : True := by
  cases h <;> trivial
end UnivSplit

end Tests.Ix.Compile.Twins.Repro.Orig

namespace Tests.Ix.Compile.Twins.Repro.Twin

-- ===== Ctl =====
/-! Control group: blocks that should arrive canonical. -/
namespace Tw.Ctl
inductive N
  | z : N
  | s : N → N

def N.toNat : N → Nat
  | .z => 0
  | .s n => n.toNat + 1

theorem one : N.toNat (.s .z) = 1 := rfl

inductive Tree
  | node : List Tree → Tree

mutual
def Tree.size : Tree → Nat
  | .node ts => 1 + Tree.sizes ts
def Tree.sizes : List Tree → Nat
  | [] => 0
  | t :: ts => t.size + Tree.sizes ts
end

theorem tsz : Tree.size (.node [.node []]) = 2 := rfl

inductive Ev : Nat → Prop
  | z : Ev 0
  | ss {n : Nat} : Ev n → Ev (n + 2)

theorem Ev.triv {n : Nat} (h : Ev n) : True := by
  induction h <;> trivial

theorem Ev.two_le : ∀ {n : Nat}, Ev (n + 2) → Ev n
  | _, .ss h => h

structure Pt where
  x : Nat
  y : Nat
  deriving DecidableEq, BEq, Hashable

def Pt.swap (p : Pt) : Pt := ⟨p.y, p.x⟩

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

def Vec.toList {α : Type u} : {n : Nat} → Vec α n → List α
  | _, .nil => []
  | _, .cons a v => a :: v.toList
end Tw.Ctl

-- ===== DQMut =====
/-! Twin of DQMut: {B} then {A}; the functions are split along the SCCs too
(B.size first, then A.size calling it), which is what Lean elaborates for separately
declared types. -/
namespace Tw.DQMut
inductive B
  | nil : B
  | s : B → B
inductive A
  | nil : A
  | a : B → A → A

def B.size : B → Nat
  | .nil => 0
  | .s b => B.size b + 1

def A.size : A → Nat
  | .nil => 0
  | .a b x => B.size b + A.size x + 1

theorem size2 : A.size (.a (.s .nil) .nil) = 2 := rfl
end Tw.DQMut

-- ===== DQReord =====
/-! Twin of DQReord: the same block in Ix's canonical order (Odd, Even). -/
namespace Tw.DQReord
mutual
inductive Odd
  | s : Even → Odd
inductive Even
  | z : Even
  | s : Odd → Even
end

mutual
def Odd.toNat : Odd → Nat
  | .s e => e.toNat + 1
def Even.toNat : Even → Nat
  | .z => 0
  | .s o => o.toNat + 1
end

theorem two : Even.toNat (.s (.s .z)) = 2 := rfl
end Tw.DQReord

-- ===== DQSplit =====
namespace Tw.DQSplit
inductive B
  | nil : B
inductive A
  | nil : A
  | a : B → A → A

def A.len : A → Nat
  | .nil => 0
  | .a _ x => x.len + 1

def B.val : B → Nat
  | .nil => 7

def A.sum : A → Nat
  | .nil => 0
  | .a b x => b.val + x.sum

theorem len2 : A.len (.a .nil (.a .nil .nil)) = 2 := rfl
theorem sum1 : A.sum (.a .nil .nil) = 7 := rfl
theorem len_succ (x : A) (b : B) : (A.a b x).len = x.len + 1 := rfl
end Tw.DQSplit

-- ===== EvapClosure =====
/-! Twin of EvapClosure: {B}, then {A}; `List B` is no longer a nested occurrence. -/
namespace Tw.EvapClosure
inductive B where
  | leaf : B
inductive A where
  | mk : List B → A
end Tw.EvapClosure

-- ===== F1_Collapse2p1 =====
/-! Twin of F1: classes [{A,B}, {C}] in Ix's canonical order (A-class at idx 0, C at idx 1). -/
namespace Tw.F1
mutual
inductive A where
  | z
  | s : C → A
inductive C where
  | n : A → A → C
  | e
end
end Tw.F1

-- ===== F2_SplitNestedClosure =====
namespace Tw.F2
inductive B
  | leaf
inductive A
  | mk : List B → A
end Tw.F2

-- ===== F4_NestedAlphaUsers =====
/-! Twin of F4: the class {A, B} has one representative, A; aux `List B` and `List A`
collapse into one `List A`. -/
namespace Tw.F4
inductive A : Type where
  | leaf
  | node : List A → A
noncomputable def r := @A.rec
theorem t (a : A) : True :=
  A.rec (motive_1 := fun _ => True) (motive_2 := fun _ => True)
    trivial (fun _ _ => trivial) trivial (fun _ _ _ _ => trivial) a
mutual
def A.size : A → Nat
  | .leaf => 1
  | .node bs => sizeL bs + 1
def sizeL : List A → Nat
  | [] => 0
  | b :: bs => b.size + sizeL bs
end
end Tw.F4

-- ===== FieldBelow =====
/-! H3: a constant named `X.below` / `X.brecOn` that is not an auxiliary.
Lean generates `.below`/`.brecOn` only for recursive inductives, so for a
non-recursive inductive (or a structure) the names are free for user code.
aux-gen gates `.below` generation on the name being present with a type that
ends in `Sort _` (`is_below_shaped`, aux_gen.rs:1317), not on recursiveness. -/
namespace Tw.FieldBelow
structure S where
  below : Nat → Type

def useS (s : S) : Type := s.below 0

def sNat : S := ⟨fun _ => Nat⟩
theorem useS_nat : useS sNat = Nat := rfl

inductive T
  | a
  | b

def T.below (_ : T) : Type := Nat
def T.brecOn (_ : T) : Nat := 7

theorem t_below : T.below T.a = Nat := rfl
theorem t_brecOn : T.brecOn T.b = 7 := rfl

structure SP where
  below : Prop

theorem sp (s : SP) (h : s.below) : s.below := h
end Tw.FieldBelow

-- ===== PropCollapse =====
/-! Twin of PropCollapse: the class {P, Q} has one representative, P. -/
namespace Tw.PropCollapse
inductive P : Nat → Prop
  | step : ∀ n, P n → P n

theorem p_cases (h : P 0) : P 0 := by
  cases h with
  | step q => exact q
end Tw.PropCollapse

-- ===== PropSplit =====
/-! Twin of PropSplit: every member is its own SCC. -/
namespace Tw.PropSplit
inductive P1 : Prop
  | mk : True → P1
inductive P2 : Prop
  | mk : True → True → P2

theorem p1 (h : P1) : True := by
  cases h
  trivial

theorem p2 (h : P2) : True :=
  @P2.rec (fun _ => True) (fun _ _ => trivial) h

inductive Q1 : Prop
  | mk : True → Q1
inductive Q2 : Prop
  | mk : True → Q2

theorem q1 (h : Q1) : True := by
  cases h
  trivial

theorem q2 (h : Q2) : True :=
  @Q2.rec (fun _ => True) (fun _ => trivial) h
end Tw.PropSplit

-- ===== RecAlias =====
/-! Recursive fields hidden behind a reducible alias (the kernel whnf's field
types when it finds recursive arguments; IndPredBelow builds the Prop `.below`
from the recursor's minors). ix's non-nested Prop `.below` path builds from the
constructor types and recognises recursive fields by their head constant. -/
namespace Tw.RecAlias
abbrev Id' (p : Prop) : Prop := p

inductive PA : Nat → Prop
  | base : PA 0
  | step {n : Nat} : Id' (PA n) → PA (n + 1)

theorem PA.triv : ∀ {n : Nat}, PA n → True
  | _, .base => trivial
  | _, .step h => PA.triv h

abbrev IdT (α : Type) : Type := α

inductive TA
  | leaf
  | node : IdT TA → TA

def TA.size : TA → Nat
  | .leaf => 0
  | .node t => TA.size t + 1

theorem ta2 : TA.size (.node (.node .leaf)) = 2 := rfl
end Tw.RecAlias

-- ===== SurgCollapse =====
/-! Twin of SurgCollapse: the class {A, B} has one representative, A (Ix's
representative; B's names are absent). `f` is the source text with B's motive and
minors dropped (what surgery is described to do); `f_ab` is not twinned (it is
false for the twin's `f`). The mutual structural pair is twinned as two functions
over the one type. -/
namespace Tw.SurgCollapse
inductive A
  | nil : A
  | a : A → A

noncomputable def f : A → Nat :=
  @A.rec (fun _ => Nat) 0 (fun _ ih => ih + 1)

mutual
def A.f : A → Nat
  | .nil => 0
  | .a b => B.g b + 1
def B.g : A → Nat
  | .nil => 100
  | .a a => a.f * 2
end

theorem fg_ab : A.f (.a .nil) = 101 := rfl
end Tw.SurgCollapse

-- ===== SurgIdx =====
/-! Twin of SurgIdx / SurgIdx2: each member its own SCC. -/
namespace Tw.SurgIdx
inductive A : Nat → Type
  | mk : A 0
inductive B : Type
  | leaf : B
  | node : B → B

def B.size : B → Nat
  | .leaf => 0
  | .node b => b.size + 1

theorem bsize : B.size (.node .leaf) = 1 := rfl
end Tw.SurgIdx

namespace Tw.SurgIdx2
inductive A : Type
  | mk : A
inductive B : Nat → Type
  | leaf : B 0
  | node {n : Nat} : B n → B (n + 1)

def B.size : {n : Nat} → B n → Nat
  | _, .leaf => 0
  | _, .node b => b.size + 1

theorem bsize : B.size (.node .leaf) = 1 := rfl
end Tw.SurgIdx2

-- ===== SurgSplit =====
/-! Twin of SurgSplit: SCCs {B}, {A} declared separately, in dependency order. -/
namespace Tw.SurgSplit
inductive B
  | nil : B
inductive A
  | nil : A
  | a : B → A → A

def A.len : A → Nat
  | .nil => 0
  | .a _ x => x.len + 1

theorem len2 : A.len (.a .nil (.a .nil .nil)) = 2 := rfl
end Tw.SurgSplit

-- ===== UnivSplit =====
namespace Tw.UnivSplit
universe v
inductive PB : Prop
  | b : PB → PB
  | z : PB
inductive PA : Prop
  | a : PB → (α : Sort v) → α → PA

theorem pb_triv (h : PB) : True := by
  cases h <;> trivial
end Tw.UnivSplit

end Tests.Ix.Compile.Twins.Repro.Twin
