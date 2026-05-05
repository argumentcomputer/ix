module
public import Lean

namespace Tests.Ix.Compile.Mutual

-- Alpha-equivalent pair (A ≅ B under renaming)
namespace AlphaCollapse
mutual
  public inductive A | a : B → A
  public inductive B | b : A → B
end

--set_option pp.all true
--#print A.brecOn
--#eval show Lean.MetaM Unit from do
--  let ci ← Lean.getConstInfo ``A.below.a
--  let .ctorInfo cv := ci | return
--  IO.println s!"{repr cv.type}"


-- Over-merged variant: A2≅B2, C2 references B2 (C2 is external SCC)
mutual
  public inductive A2 | a : B2 → A2
  public inductive B2 | b : A2 → B2
  public inductive C2 | c : B2 → C2
end

-- Self-referential: collapses to same compiled form as A and B
mutual
  public inductive A' | a' : A' → A'
  --public inductive B' | a' : B' → B'
end


end AlphaCollapse


-- Over-merged: A/B form one SCC, C references both but not vice versa.
-- A and B are NOT alpha-equivalent (B has 2 A fields).
namespace OverMerge
mutual
  public inductive A | a : B → A
  public inductive B | b : A → A → B
  public inductive C | c : A → B → C
end
-- Reordered: B2,C2,A2 (same structure, different declaration order)
mutual
  public inductive B2 | b : A2 → A2 → B2
  public inductive C2 | c : A2 → B2 → C2
  public inductive A2 | a : B2 → A2
end
-- Split: C3 separate (it's in a different SCC than A3/B3)
mutual
  public inductive B3 | b : A3 → A3 → B3
  public inductive A3 | a : B3 → A3
end
public inductive C3 where | c : A3 → B3 → C3
end OverMerge

--#print OverMerge.A3.below.rec
--#eval show Lean.MetaM Unit from do
--  let ci ← Lean.getConstInfo ``OverMerge.C3.c
--  let .ctorInfo cv := ci | return
--  IO.println s!"{repr cv.type}"

namespace OverMergeSplit
mutual
  public inductive A | a : B → A
  public inductive B | b : A → A → B
end
mutual
  public inductive C | c : A → B → C
end
end OverMergeSplit

namespace OverMerge2
mutual
  public inductive A | a : B → A
  public inductive B | b : A → A → B
  public inductive C | c : A -> D -> C
  public inductive D | c : B -> C -> D
end
-- Reordered: D2,C2,B2,A2
mutual
  public inductive D2 | c : B2 → C2 → D2
  public inductive C2 | c : A2 → D2 → C2
  public inductive B2 | b : A2 → A2 → B2
  public inductive A2 | a : B2 → A2
end
-- Split into two minimal SCCs
mutual
  public inductive B3 | b : A3 → A3 → B3
  public inductive A3 | a : B3 → A3
end
mutual
  public inductive C3 | c : A3 → D3 → C3
  public inductive D3 | c : B3 → C3 → D3
end
end OverMerge2

namespace OverMerge2Split
mutual
  public inductive A | a : B → A
  public inductive B | b : A → A → B
end
mutual
  public inductive C | c : A -> D -> C
  public inductive D | c : B -> C -> D
end
end OverMerge2Split

-- Over-merged + alpha-collapse: A ≅ B, C is external. Equivalent to BLE/BLI/BLO.
namespace OverMergeAlphaCollapse
mutual
  public inductive A | a : B → A
  public inductive B | b : A → B
  public inductive C | c : A → B → C
end
-- Reordered: C2,B2,A2
mutual
  public inductive C2 | c : A2 → B2 → C2
  public inductive B2 | b : A2 → B2
  public inductive A2 | a : B2 → A2
end
-- Split: A3≅B3 in mutual, C3 separate
mutual
  public inductive A3 | a : B3 → A3
  public inductive B3 | b : A3 → B3
end
public inductive C3 where | c : A3 → B3 → C3
end OverMergeAlphaCollapse

-- Alpha-collapse n=3: A→B→C→A cycle, all collapse to one.
namespace AlphaCollapse3
mutual
  public inductive A | a : B → A
  public inductive B | b : C → B
  public inductive C | c : A → C
end

-- Reordered: C2,A2,B2
mutual
  public inductive C2 | c : A2 → C2
  public inductive A2 | a : B2 → A2
  public inductive B2 | b : C2 → B2
end
end AlphaCollapse3

-- Alpha-collapse n=4: W→X→Y→Z→W cycle, all collapse to one.
namespace AlphaCollapse4
mutual
  public inductive W | w : X → W
  public inductive X | x : Y → X
  public inductive Y | y : Z → Y
  public inductive Z | z : W → Z
end
-- Reordered: Z2,Y2,X2,W2
mutual
  public inductive Z2 | z : W2 → Z2
  public inductive Y2 | y : Z2 → Y2
  public inductive X2 | x : Y2 → X2
  public inductive W2 | w : X2 → W2
end
end AlphaCollapse4

-- Over-merged with structures: 5 types, 2 SCCs.
-- EqC/EqP form one SCC, IneqC/IneqP/UnsatP form another.
-- IneqP references EqC (cross-SCC dependency).
namespace OverMergedStructs
mutual
  public structure EqC where
    val : Nat
    proof : EqP
  public inductive EqP where
    | base : Nat → EqP
    | combine : EqC → EqC → EqP
  public structure IneqC where
    val : Nat
    strict : Bool
    proof : IneqP
  public inductive IneqP where
    | base : Nat → IneqP
    | fromEq : EqC → IneqP
    | combine : IneqC → IneqC → IneqP
  public inductive UnsatP where
    | ineq : IneqC → UnsatP
end
end OverMergedStructs

namespace OverMergedStructs2
mutual
  public structure EqC where
    val : Nat
    proof : EqP
  public inductive EqP where
    | base : Nat → EqP
    | combine : EqC → EqC → EqP
  public structure IneqC where
    val : Nat
    strict : Bool
    proof : IneqP
  public inductive IneqP where
    | base : Nat → IneqP
    | fromEq : EqC → IneqP
    | ofDiseqSplit : UnsatP -> IneqP
    | combine : IneqC → IneqC → IneqP
  public inductive UnsatP where
    | ineq : IneqC → UnsatP
end
end OverMergedStructs2


-- Nested inductive: single type nesting through List.
-- No alpha-collapse (single inductive), so aux_gen doesn't run.
-- Serves as a baseline: Lean's original nested auxiliaries (.rec_1, .below_1,
-- .brecOn_1) compile without interference from our pipeline.
namespace NestedSimple
public inductive Tree where
  | leaf : Nat → Tree
  | node : List Tree → Tree

end NestedSimple

-- Nested + alpha-collapse: TreeA ≅ TreeB (identical structure under renaming),
-- both nesting through List. Mutual references (fromB/fromA) ensure they form
-- a single SCC so sort_consts can collapse them.
-- Exercises:
--   1. Alpha-collapse merges {TreeA, TreeB} into one equivalence class
--   2. build_compile_flat_block detects List as a nested auxiliary
--   3. generate_canonical_recursors builds a recursor with auxiliary rules for List
--   4. TreeB's auxiliaries are aliased to TreeA's
namespace NestedAlphaCollapse
mutual
  public inductive TreeA where
    | leaf : TreeA
    | fromB : TreeB → TreeA
    | node : List TreeA → TreeA
  public inductive TreeB where
    | leaf : TreeB
    | fromA : TreeA → TreeB
    | node : List TreeB → TreeB
end
end NestedAlphaCollapse

-- Nested + alpha-collapse with a parameter: Rose α nests through List.
-- Mutual references ensure SCC formation. Tests that spec_params (containing
-- the block parameter α) are correctly detected, hashed for dedup, and
-- abstracted back to BVars.
namespace NestedParam
mutual
  public inductive RoseA (α : Type) where
    | leaf : α → RoseA α
    | fromB : RoseB α → RoseA α
    | node : List (RoseA α) → RoseA α
  public inductive RoseB (α : Type) where
    | leaf : α → RoseB α
    | fromA : RoseA α → RoseB α
    | node : List (RoseB α) → RoseB α
end
end NestedParam

-- Nested + over-merge: A/B form one SCC (not alpha-equivalent: B has extra
-- field), C references both but not vice versa (external SCC). All three
-- nest through List.
-- Exercises nested detection in a multi-SCC block where the inner SCC {A,B}
-- has a non-trivial flat block (List appears as auxiliary for both A and B).
namespace NestedOverMerge
mutual
  public inductive A where
    | a : B → List A → A
  public inductive B where
    | b : A → A → List B → B
  public inductive C where
    | c : A → B → List C → C
end
end NestedOverMerge

-- Nested aux ordering: verify that auxiliary recursors generated for
-- nested inductive occurrences are ordered canonically (by content hash)
-- rather than by Lean's source-walk discovery order. Two semantically
-- equivalent blocks declared in different orders should compile to the
-- SAME canonical Ixon form.
--
-- The fixture declares three types {A, B, C} each with three nested
-- occurrences `Array`, `Option`, `List`, then re-declares the same block
-- with the types in a permuted order (C2, A2, B2). Without hash-sort of
-- aux recs, the source-walk order of `_nested.Array/Option/List_N`
-- differs between the two blocks, and so do the resulting aux recursor
-- numberings — which leaks into addresses and breaks content-addressing.
namespace NestedAuxOrdering
mutual
  public inductive A where | mk : Array B → Option C → List A → A
  public inductive B where | mk : Array C → Option A → List B → B
  public inductive C where | mk : Array A → Option B → List C → C
end

mutual
  public inductive C2 where | mk : Array A2 → Option B2 → List C2 → C2
  public inductive A2 where | mk : Array B2 → Option C2 → List A2 → A2
  public inductive B2 where | mk : Array C2 → Option A2 → List B2 → B2
end
end NestedAuxOrdering

-- Nested aux ordering with alpha-collapse: A and B have identical
-- semantic structure under renaming (A ≅ B), nesting through two
-- different containers (`Array`, `Option`). The block is declared
-- unreordered, then reordered.
namespace NestedAuxOrderingAlpha
mutual
  public inductive A where | mk : Array B → Option A → A
  public inductive B where | mk : Array A → Option B → B
end

mutual
  public inductive B2 where | mk : Array A2 → Option B2 → B2
  public inductive A2 where | mk : Array B2 → Option A2 → A2
end
end NestedAuxOrderingAlpha

-- Nested aux ordering with a binary nesting container (`Prod`). Exercises
-- spec_params with multiple arguments, so the hash-based ordering
-- depends on more than a single type argument. Declared twice with
-- different source orderings.
namespace NestedAuxOrderingProd
mutual
  public inductive A where | mk : Prod A B → Prod B C → Prod C A → A
  public inductive B where | mk : Prod A B → Prod B C → Prod C A → B
  public inductive C where | mk : Prod A B → Prod B C → Prod C A → C
end

mutual
  public inductive C2 where | mk : Prod A2 B2 → Prod B2 C2 → Prod C2 A2 → C2
  public inductive B2 where | mk : Prod A2 B2 → Prod B2 C2 → Prod C2 A2 → B2
  public inductive A2 where | mk : Prod A2 B2 → Prod B2 C2 → Prod C2 A2 → A2
end
end NestedAuxOrderingProd

-- Nested + over-merge + alpha-collapse: A ≅ B (identical structure under
-- renaming), C is in a separate SCC referencing both. All nest through List.
-- Exercises the combination of alpha-collapse AND nested detection in the
-- same block — the canonical recursor for {A,B} needs auxiliary List rules.
namespace NestedOverMergeAlphaCollapse
mutual
  public inductive A where
    | a : B → List A → A
  public inductive B where
    | b : A → List B → B
  public inductive C where
    | c : A → B → List C → C
end
--
--#eval show Lean.MetaM Unit from do
--  let ci ← Lean.getConstInfo ``A.rec_3
--  let .recInfo cv := ci | return
--  IO.println s!"{repr cv.all}"
--
mutual
  public inductive A2 where
    | a : B2 → List A2 → A2
  public inductive B2 where
    | b : A2 → List B2 → B2
end
mutual
  public inductive C2 where
    | c : A2 → B2 → List C2 → C2
end
--#print C2.rec_1

end NestedOverMergeAlphaCollapse

-- Higher-order recursive fields: constructors with `(A → I) → I` pattern.
-- Exercises the `build_below_minor` path for IH fields whose domain has
-- inner foralls. The `.below` minor must distribute PProd inside the forall:
--   `∀ (a : A), PProd(motive (f a), ih a)`
-- NOT flatten it outside:
--   `PProd(∀ (a : A), motive (f a), ih)`
namespace HigherOrderRec

-- Single inductive with a higher-order recursive field.
-- `.below` minor for `sup` should be:
--   `λ (f : Nat → WTree) (ih : ∀ (a : Nat), Sort rlvl),
--      ∀ (a : Nat), PProd (motive (f a)) (ih a)`
public inductive WTree where
  | leaf : Nat → WTree
  | sup : (Nat → WTree) → WTree

-- Multiple higher-order fields: both simple and function-typed recursion.
-- `.below` minor for `branch` should handle `t` as simple IH and `f` as
-- higher-order IH in the same PProd chain.
public inductive MTree where
  | leaf : Nat → MTree
  | branch : MTree → (Nat → MTree) → MTree

-- Alpha-collapse with higher-order recursive fields: FA ≅ FB under renaming.
-- Tests that collapsed aliases inherit the correct `.below` structure.
mutual
  public inductive FA where
    | leaf : FA
    | sup : (Nat → FB) → FA
  public inductive FB where
    | leaf : FB
    | sup : (Nat → FA) → FB
end

-- Multi-argument higher-order field: `(Nat → Bool → I) → I`.
-- `.below` minor should produce:
--   `λ (f : Nat → Bool → HOTree2) (ih : ∀ (a : Nat) (b : Bool), Sort rlvl),
--      ∀ (a : Nat) (b : Bool), PProd (motive (f a b)) (ih a b)`
public inductive HOTree2 where
  | leaf : HOTree2
  | sup : (Nat → Bool → HOTree2) → HOTree2

end HigherOrderRec

-- Inductives whose target type is a reducible alias. Minimal reproducers
-- (no Mathlib dependency) for the `build_below_def` mismatch on Mathlib's
-- `FiniteInter.finiteInterClosure` and `εNFA.εClosure`.
--
-- Context: Lean computes `num_indices` by walking the target type with
-- `whnf` — unfolding reducible aliases like `MySet α = α → Prop`. So the
-- target `MySet α` exposes one Pi after unfolding, and Lean stores
-- `num_indices = 1`. The recursor type is then built from `info.m_indices`
-- via the kernel's `mk_pi`, which should produce a matching physical
-- forall. But in practice the physical forall count sometimes disagrees
-- with `num_indices` — either because of how the motive is elaborated in
-- the presence of the reducible alias, or because the motive's argument
-- count vs binder count itself depends on how Lean resolves `motive t`
-- where `t`'s type reduces to a Pi.
--
-- These fixtures exist so validate-aux can reproduce the failure in
-- isolation while we work out the right fix. The aux_gen pipeline must
-- generate `.rec` / `.below` / `.brecOn` that typecheck against Lean's
-- originals — no shortcuts.
-- Inductives whose target type is a reducible alias. Minimal reproducers
-- (no Mathlib dependency) for the `build_below_def` mismatch on Mathlib's
-- `εNFA.εClosure` and `FiniteInter.finiteInterClosure`.
--
-- Context: Lean computes `num_indices` by walking the target type with
-- `whnf` — unfolding reducible aliases like `MySet α = α → Prop`. The
-- recursor type is then built from `info.m_indices` via the kernel's
-- `mk_pi`. In practice the physical forall count of the stored recursor
-- type can disagree with the stored `num_indices` by the number of
-- arrows hidden inside reducible aliases, because the motive's binder
-- arity is determined syntactically (the motive binds `t : MySet α S`)
-- while `num_indices` counts post-reduction arrows. Our arity-based
-- binder-chain peeling in `build_below_def` trips on this mismatch.
--
-- These fixtures exist so validate-aux can reproduce the failure in
-- isolation. The aux_gen pipeline must generate `.rec` / `.below` /
-- `.brecOn` that typecheck against Lean's originals — no shortcuts.
namespace ReducibleAliasTarget

public abbrev MySet (α : Type) := α → Prop

-- Single-level reducible target (εClosure shape).
-- Target `MySet α` ≡ `α → Prop` — one index `a : α` after WHNF.
public inductive SClosure (α : Type) (S : MySet α) : MySet α
  | base (a : α) : S a → SClosure α S a

-- Two-level reducible target (finiteInterClosure shape).
-- Target `MySet (MySet α)` ≡ `MySet α → Prop` — one "index" `s : MySet α`
-- after WHNF, but the index is itself a predicate (function type).
public inductive DClosure (α : Type) (S : MySet (MySet α)) : MySet (MySet α)
  | base (s : MySet α) : S s → DClosure α S s

end ReducibleAliasTarget

end Tests.Ix.Compile.Mutual
