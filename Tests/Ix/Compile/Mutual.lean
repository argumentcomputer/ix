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

namespace AuxDedup1

mutual
  inductive A : Type where | mk : List B → List C → A
  inductive B : Type where | leaf : B
  inductive C : Type where | leaf : C
end

end AuxDedup1

namespace AuxDedup2

  inductive C : Type where | leaf : C
mutual
  inductive A : Type where | mk : List B → List C → A
  inductive B : Type where | leaf : B
end

end AuxDedup2

-- Mixed nested auxiliaries: `List M` stays a genuine nested occurrence of
-- M's split SCC (M is recursive through it), while `List B` evaporates
-- (B splits into its own SCC). Exercises the expand/restore path with a
-- perm mixing a canonical slot and PERM_OUT_OF_SCC for the same owner:
-- `M.rec_1` is a canonical aux patch, `M.rec_2` aliases `List.rec`.
namespace AuxDedupMixed

mutual
  inductive M : Type where | mk : List M → List B → M
  inductive B : Type where | leaf : B
end

end AuxDedupMixed

-- Cross-SCC ownership of source-indexed auxiliary names
-- (plans/aux-recursor-alias-collision.md, TruthMines handoff repro).
--
-- Lean hangs every nested-aux name off `InductiveVal.all[0]` of the
-- ORIGINAL mutual block. When the block splits into SCCs, the spec
-- inductive's SCC can compile a position as a canonical aux (claiming
-- `all0.rec_N`) while the owner's SCC independently decides the same
-- position "evaporated" and aliases the same name to the external
-- container's generic recursor. Two claimants, one name:
--   invalid mutual block: aux_gen alias 'O.rec_1' already resolves to
--   <canonical patch>, expected <NE.rec> via 'NE.rec'
namespace AuxOwnership

-- External single-motive container (the HaskellSpec `NonEmpty` shape).
-- Declared OUTSIDE the mutuals: its own generic 1-motive `NE.rec` is the
-- evaporation target.
public structure NE (α : Type) where
  head : α
  tail : List α

-- A: minimal conflict. all = [O, X] so aux names hang off `O`; the walk
-- discovers `NE X` first from O.mk (owner = O), but X's OWN ctor also
-- mentions `NE X`, so {X}'s canonical block contains the aux and claims
-- `O.rec_1` (and `O.rec_2` for the inner `List X`). {O} then tries to
-- evaporate the same names to `NE.rec` / `List.rec`.
namespace ConflictMin
mutual
  public inductive O where
    | mk : NE X → O
  public inductive X where
    | node : NE X → X
    | leaf : X
end
end ConflictMin

-- B: two distinct specs in two different spec SCCs (the rec_2/rec_3
-- analog). {Q} claims P.rec_1/P.rec_2, {R} claims P.rec_3/P.rec_4,
-- {P} tries to evaporate all four. R differs from Q structurally so the
-- two spec SCCs aren't cross-block alpha-twins.
namespace TwoSpecs
mutual
  public inductive P where
    | mk : NE Q → NE R → P
  public inductive Q where
    | node : NE Q → Q
    | leaf : Q
  public inductive R where
    | node : NE R → R
    | leaf : R
    | stop : R
end
end TwoSpecs

-- C: legitimate evaporation regression guard. {B} never discovers
-- `NE B` (B.leaf mentions nothing), so nobody claims `M.rec_1`/`M.rec_2`
-- canonically and {M}'s evaporation to `NE.rec`/`List.rec` is correct.
-- Unlike AuxDedupMixed, {M}'s own expansion has NO nested occurrence at
-- all (`NE B` doesn't mention M), exercising the metadata-only
-- disagreement path (aux_gen.rs "metadata-only" branch).
namespace Evap
mutual
  public inductive M where
    | mk : NE B → M → M
  public inductive B where
    | leaf : B
end
end Evap

-- D: DQ2 probe — spec params spanning two SCCs. `List (S × T)` and the
-- inner `Prod S T` mention S (⇒ {S}'s canonical expansion contains both
-- auxes) but also T, an original member outside {S} (⇒ compute_aux_perm's
-- in_scc pre-filter skips every source position). Predicted to hard-error
-- with "canonical aux #0 has no source mapping" — an adjacent latent bug
-- in the same ownership family, scoped by plan §3 DQ2.
namespace SplitSpecs
mutual
  public inductive S where
    | mk : List (S × T) → S
  public inductive T where
    | leaf : T
end
end SplitSpecs

-- F: alpha-twin claim routing. X1 ≅ X2 (alpha-identical, one content
-- address) sit in DIFFERENT SCCs; W mentions only `NE X2`. Ownership
-- matching must compare other-SCC original members NAME-strictly:
-- with the address fallback, {X1} would match W's `NE X2` position
-- against its own `NE X1` signature and both twin SCCs would claim
-- `W.rec_1`. Expected claims: {X2} → W.rec_1/W.rec_2,
-- {X1} → W.rec_3/W.rec_4, {W} → nothing (canonical-elsewhere).
namespace TwinClaim
mutual
  public inductive W where
    | mk : NE X2 → W
  public inductive X1 where
    | node : NE X1 → X1
    | leaf : X1
  public inductive X2 where
    | node : NE X2 → X2
    | leaf : X2
end
end TwinClaim

-- E: the real block shape — a 3-member owner SCC (O1→O2→O3→O1) whose
-- perm mixes a canonical slot (`List O2`, specs in-SCC → claims O1.rec_3)
-- with conflicting evaporations (`NE X3` / `List X3` claimed canonically
-- by {X3} as O1.rec_1/O1.rec_2). Mirrors the failing
-- `HaskellSpec.Source.Binding (3 members)` block.
namespace ThreeMember
mutual
  public inductive O1 where
    | mk : NE X3 → O2 → O1
  public inductive O2 where
    | mk : O3 → List O2 → O2
    | leaf : O2
  public inductive O3 where
    | mk : O1 → O3
  public inductive X3 where
    | node : NE X3 → X3
    | leaf : X3
end
end ThreeMember

end AuxOwnership

-- Prop-valued mutual inductive predicates whose `.below` auxiliaries form
-- a generated mutual-inductive family (IndPredBelow) — the HaskellSpec
-- `dict`/`pat`/`type` shape. The mutual theorems by structural
-- pattern-matching force Lean to generate `EvenP.below`/`OddP.below`
-- (plus `.below.casesOn`, defined via `.below.rec`), exercising:
-- (a) the below-rec block's class-order key — its storage order must
--     follow the below inductive block (canonicity §6.2), and
-- (b) the `.below.casesOn` regeneration against the canonical below-rec
--     (compile + decompile Phase 3b; Lean's authored wrapper applies
--     motives in Lean's member order and would be ill-typed against the
--     canonical rec).
namespace BelowPredicate
mutual
  public inductive EvenP : Nat → Prop where
    | zero : EvenP 0
    | succ : {n : Nat} → OddP n → EvenP (n + 1)
  public inductive OddP : Nat → Prop where
    | succ : {n : Nat} → EvenP n → OddP (n + 1)
end

mutual
  public theorem evenp_nonneg : {n : Nat} → EvenP n → 0 ≤ n
    | _, .zero => Nat.le_refl 0
    | _, .succ h => Nat.le_trans (oddp_nonneg h) (Nat.le_succ _)
  public theorem oddp_nonneg : {n : Nat} → OddP n → 0 ≤ n
    | _, .succ h => Nat.le_trans (evenp_nonneg h) (Nat.le_succ _)
end

-- Tier A for `.below`: both motive arguments form the complete permuted
-- band, while the implicit major remains unapplied (3 of 4 source args).
public def evenpBelowPartial (n : Nat) :=
  @EvenP.below
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True) n
end BelowPredicate

-- Mirrored source order for the `.below` Tier-A fixture. Exactly one of
-- this block and `BelowPredicate` disagrees with canonical class order.
namespace BelowPredicate2
mutual
  public inductive OddP2 : Nat → Prop where
    | succ : {n : Nat} → EvenP2 n → OddP2 (n + 1)
  public inductive EvenP2 : Nat → Prop where
    | zero : EvenP2 0
    | succ : {n : Nat} → OddP2 n → EvenP2 (n + 1)
end

mutual
  public theorem oddp2_nonneg : {n : Nat} → OddP2 n → 0 ≤ n
    | _, .succ h => Nat.le_trans (evenp2_nonneg h) (Nat.le_succ _)
  public theorem evenp2_nonneg : {n : Nat} → EvenP2 n → 0 ≤ n
    | _, .zero => Nat.le_refl 0
    | _, .succ h => Nat.le_trans (oddp2_nonneg h) (Nat.le_succ _)
end

public def evenp2BelowPartial (n : Nat) :=
  @EvenP2.below
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True) n
end BelowPredicate2

-- Type-level mutual indexed inductives + mutual structural recursion +
-- forced `.eq_def` equation lemmas (the TorchLean `NN.GraphSpec.DAG`
-- `Term`/`Args` shape, torchlean.ixe check-rs failure of 2026-08-22).
--
-- The mutual defs compile through `X.brecOn`, and when the canonical
-- (`sort_consts`) class order differs from Lean's source order the
-- regenerated `.brecOn`/`.brecOn.go`/`.brecOn.eq` carry canonical motive
-- and handler order. User references to `X.brecOn` are permuted by
-- `brec_on_call_site_plans` — but the auto-generated `.eq_def` proofs
-- reference `X.brecOn.go` and `X.brecOn.eq` DIRECTLY, and those heads
-- need the same call-site permutation. The block is declared twice with
-- opposite source orders so exactly one twin disagrees with the
-- canonical order regardless of content-hash values.
namespace TypeBrecOnEqDef

-- Two ctors, deliberately NOT unit-like: with a 0-field single-ctor `Sh`,
-- Lean's elaborator-level `isDefEq` (unit-like structure eta) makes the
-- generalized major's types defeq inside `mkEqAndProof`, so Lean's
-- `.brecOn.eq` uses a homogeneous `Eq` for the major where ix's
-- kernel-level defeq (no unit-like rule) generates `HEq` — a separate,
-- pre-existing `.eq` fidelity divergence. `NN.Tensor.Shape` (the shape
-- this fixture mirrors) is not unit-like, so keep `Sh` non-unit-like.
public inductive Sh where
  | a : Sh
  | b : Sh

mutual
  public inductive Tm : List Sh → Sh → Type where
    | var {Γ : List Sh} {s : Sh} : Tm Γ s
    | op {Γ : List Sh} {ins : List Sh} {t : Sh} : Ar Γ ins → Tm Γ t
  public inductive Ar : List Sh → List Sh → Type where
    | nil {Γ : List Sh} : Ar Γ []
    | cons {Γ : List Sh} {s : Sh} {ss : List Sh} :
        Tm Γ s → Ar Γ ss → Ar Γ (s :: ss)
end

-- The Ar-first def order mirrors TorchLean's `Args.rename`/`Term.rename`.
mutual
  public def Ar.wk {Γ : List Sh} {ss : List Sh} : Ar Γ ss → Ar Γ ss
    | .nil => .nil
    | .cons t rest => .cons t.wk rest.wk
  public def Tm.wk {Γ : List Sh} {s : Sh} : Tm Γ s → Tm Γ s
    | .var => .var
    | .op args => .op args.wk
end

-- Force realization of the `.eq_def` lemmas into the env; their proofs
-- are what reference `.brecOn.go` / `.brecOn.eq` with explicit motives.
set_option linter.defProp false in
def arWkEqDef := @Ar.wk.eq_def
set_option linter.defProp false in
def tmWkEqDef := @Tm.wk.eq_def

-- Mirrored source order (Ar2 before Tm2).
mutual
  public inductive Ar2 : List Sh → List Sh → Type where
    | nil {Γ : List Sh} : Ar2 Γ []
    | cons {Γ : List Sh} {s : Sh} {ss : List Sh} :
        Tm2 Γ s → Ar2 Γ ss → Ar2 Γ (s :: ss)
  public inductive Tm2 : List Sh → Sh → Type where
    | var {Γ : List Sh} {s : Sh} : Tm2 Γ s
    | op {Γ : List Sh} {ins : List Sh} {t : Sh} : Ar2 Γ ins → Tm2 Γ t
end

mutual
  public def Ar2.wk {Γ : List Sh} {ss : List Sh} : Ar2 Γ ss → Ar2 Γ ss
    | .nil => .nil
    | .cons t rest => .cons t.wk rest.wk
  public def Tm2.wk {Γ : List Sh} {s : Sh} : Tm2 Γ s → Tm2 Γ s
    | .var => .var
    | .op args => .op args.wk
end

set_option linter.defProp false in
def ar2WkEqDef := @Ar2.wk.eq_def
set_option linter.defProp false in
def tm2WkEqDef := @Tm2.wk.eq_def

-- Tier B for `.brecOn`: the handler band trails the major, so a bare
-- reference or a prefix ending at the major needs a source-interface
-- eta adapter. The two inductive blocks above have opposite source order.
public noncomputable def arBrecAlias := @Ar.brecOn
public noncomputable def ar2BrecAlias := @Ar2.brecOn

set_option linter.defProp false in
public def arBrecPartial {Gamma ss} (a : Ar Gamma ss) :=
  @Ar.brecOn
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True) Gamma ss a

set_option linter.defProp false in
public def ar2BrecPartial {Gamma ss} (a : Ar2 Gamma ss) :=
  @Ar2.brecOn
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True) Gamma ss a

end TypeBrecOnEqDef

-- Unit-like index type. `Un` has a single 0-field constructor, so Lean's
-- elaborator-level defeq (`isDefEqUnitLike`, Meta/ExprDefEq.lean) treats
-- any two `Un` terms as defeq. Inside the `cases`-tactic construction of
-- `.brecOn.eq`, `mkEqAndProof` then sees the generalized major's types
-- `Tm Γ a₁` / `Tm Γ a₂` as defeq and generalizes the major with a
-- homogeneous `Eq` at the OUTER type (generically ill-typed inside the
-- motive lambda, but valid under the kernel's infer-only proof checking),
-- discharged by `Eq.refl` and consumed by `Eq.ndrec`+`Eq.symm` in the
-- minors — where the non-unit-like shape uses `HEq`/`HEq.refl`/
-- `eq_of_heq`. The regenerated `.brecOn.eq` must reproduce Lean's choice
-- (validate-aux Phase 2 congruence + roundtrip). `Ar`'s major stays `HEq`
-- (`List Un` is not unit-like), so this block exercises both kinds at
-- once. Order-independent (no mirrored twin needed).
namespace TypeBrecOnEqDefUnit

public inductive Un where
  | mk : Un

mutual
  -- `lit` returns at a CONCRETE unit-like index (`Un.mk`, an expression
  -- rather than a bound fvar), so its minor exercises the Eq-major kind
  -- combined with the expression-ret-index substCore path (index
  -- `Eq.ndrec` abstracting the outer index, forward-dep revert of the
  -- major, then the homogeneous major `Eq.ndrec`).
  public inductive Tm : List Un → Un → Type where
    | var {Γ : List Un} {s : Un} : Tm Γ s
    | lit {Γ : List Un} : Tm Γ .mk
    | op {Γ : List Un} {ins : List Un} {t : Un} : Ar Γ ins → Tm Γ t
  public inductive Ar : List Un → List Un → Type where
    | nil {Γ : List Un} : Ar Γ []
    | cons {Γ : List Un} {s : Un} {ss : List Un} :
        Tm Γ s → Ar Γ ss → Ar Γ (s :: ss)
end

mutual
  public def Ar.wk {Γ : List Un} {ss : List Un} : Ar Γ ss → Ar Γ ss
    | .nil => .nil
    | .cons t rest => .cons t.wk rest.wk
  public def Tm.wk {Γ : List Un} {s : Un} : Tm Γ s → Tm Γ s
    | .var => .var
    | .lit => .lit
    | .op args => .op args.wk
end

set_option linter.defProp false in
def arWkEqDef := @Ar.wk.eq_def
-- No `Tm.wk.eq_def` forcing: `lit`'s concrete return index makes the
-- match dependent and Lean fails to realize the equation lemma for it.
-- The `.brecOn.eq` coverage doesn't need it — aux_gen regenerates the
-- brecOn family for the block regardless; eq_def surgery is covered by
-- `TypeBrecOnEqDef` and by `arWkEqDef` above.

end TypeBrecOnEqDefUnit

-- Indexed `.brecOn.eq` with constructor fields whose dependency sets overlap
-- only after an earlier index substitution. Lean's `substCore` reverts each
-- forward dependency and re-introduces it at the end of the surviving local
-- context. Thus, in `recThenPayload`, substituting `i` first moves the
-- recursive field behind the unaffected `Payload j` field; the subsequent
-- substitution of `j` must see `Payload` before `Indexed`. Preserving the
-- fields' original positions instead produced the Plfl failures
-- `Compositional.Holed.brecOn.eq` and `Inference.TyS.brecOn.eq`.
namespace TypeBrecOnForwardDepOrder

public inductive Payload : Nat → Type where
  | mk {j : Nat} : Payload j

public inductive Indexed : Nat → Nat → Type where
  | base {i : Nat} : Indexed i i
  | recThenPayload {i j : Nat} : Indexed i j → Payload j → Indexed i j
  | payloadThenRec {i j : Nat} : Payload j → Indexed i j → Indexed i j

end TypeBrecOnForwardDepOrder

-- Mutual Prop-valued inductive predicates consumed through the raw mutual
-- recursor with explicit motives (the PhiConfluence `Par`/`ParB` shape;
-- phiconfluence.ixe check-rs failures of 2026-08-22: `parB_domain`,
-- `parB_preserves`, `par_to_red`, `WF.par`, `par_triangle`, …).
--
-- `induction h using Pb.rec (motive_1 := fun _ _ _ => True)` elaborates to a
-- DIRECT `Pb.rec` application whose motive/minor arguments follow Lean's
-- source order (`all = [Pa, Pb]`). When the canonical (`sort_consts`) class
-- order differs from source order, the regenerated `.rec` carries canonical
-- motive/minor order, so the user proof's call site needs the
-- `call_site_plans` permutation. The block is declared twice with opposite
-- source orders so exactly one twin disagrees with the canonical order
-- regardless of content-hash values.
namespace PropRecMotives

mutual
  public inductive Pa : Nat → Nat → Prop where
    | refl (n : Nat) : Pa n n
    | zero {ns ns' : List Nat} : Pb ns ns' → Pa 0 0
  public inductive Pb : List Nat → List Nat → Prop where
    | nil : Pb [] []
    | cons {n n' : Nat} {ns ns' : List Nat} :
        Pa n n' → Pb ns ns' → Pb (n :: ns) (n' :: ns')
end

-- The `parB_domain` pattern: self motive inferred from the goal, the other
-- member's motive explicitly trivial.
public theorem pb_length {ns ns' : List Nat} (h : Pb ns ns') :
    ns.length = ns'.length := by
  induction h using Pb.rec (motive_1 := fun _ _ _ => True) with
  | refl => trivial
  | zero => trivial
  | nil => rfl
  | cons hpa hpb ihpa ihpb => exact congrArg (· + 1) ihpb

-- The `par_to_red`/`WF.par` pattern: the companion motive carries content.
public theorem pa_eq {a b : Nat} (h : Pa a b) : a = b := by
  induction h using Pa.rec
    (motive_2 := fun ns ns' _ => ns.length = ns'.length) with
  | refl n => rfl
  | zero hb ihb => rfl
  | nil => rfl
  | cons hpa hpb ihpa ihpb => exact congrArg (· + 1) ihpb

-- Call-site shape coverage for the OTHER apply paths (see
-- plans/callsite-adapter-generalization.md §fixture-catalog). All three
-- are handled by shipped code; they pin the paths a tactic proof never
-- produces. Telescope order for `@Pb.rec` (all = [Pa, Pb]): motive_1 =
-- Pa's motive, motive_2 = Pb's; minors refl, zero, nil, cons; indices
-- and major explicit under `@`.
--
-- Full application written directly at the Const head (taxonomy #1 in a
-- USER term — normally only Lean-generated auxiliaries exercise it).
public theorem pb_len_direct {ns ns' : List Nat} (h : Pb ns ns') :
    ns.length = ns'.length :=
  @Pb.rec (fun _ _ _ => True) (fun a b _ => a.length = b.length)
    (fun _ => trivial) (fun _ _ => trivial)
    rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)
    ns ns' h

-- Inner-FULL redex (taxonomy #3 / finding F1): the lambda-abstracted
-- major with a complete spine inside the body. Phase 3 leaves the source
-- lambda intact and applies ordinary in-body Const-head surgery.
public theorem pb_len_lam {ns ns' : List Nat} (h : Pb ns ns') :
    ns.length = ns'.length :=
  (fun (p : Pb ns ns') =>
    @Pb.rec (fun _ _ _ => True) (fun a b _ => a.length = b.length)
      (fun _ => trivial) (fun _ _ => trivial)
      rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)
      ns ns' p) h

-- Dead-binder SPLIT redex: the binder value is unused. Phase 3 preserves
-- the outer redex verbatim while Tier B adapts the inner motives-only
-- spine (args=2 of 9); the elaborator inserts the implicit indices into
-- the outer spine.
public theorem pb_len_dead {ns ns' : List Nat} (h : Pb ns ns') :
    ns.length = ns'.length :=
  (fun (_ : Nat) =>
    @Pb.rec (fun _ _ _ => True) (fun a b _ => a.length = b.length)) 0
    (fun _ => trivial) (fun _ _ => trivial)
    rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)
    h

-- Tier A: motives+minors are present, while the identity indices/major
-- suffix remains unapplied (stored source spine: 6 of 9 args).
set_option linter.defProp false in
public def pbLenFn : ∀ (ns ns' : List Nat),
    Pb ns ns' → ns.length = ns'.length :=
  @Pb.rec (fun _ _ _ => True) (fun a b _ => a.length = b.length)
    (fun _ => trivial) (fun _ _ => trivial)
    rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)

public theorem pb_len_let {ns ns' : List Nat} (h : Pb ns ns') :
    ns.length = ns'.length :=
  let g := @Pb.rec (fun _ _ _ => True)
    (fun a b _ => a.length = b.length)
    (fun _ => trivial) (fun _ _ => trivial)
    rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)
  g h

set_option linter.defProp false in
public def useRec (f : ∀ (a b : List Nat),
    Pb a b → a.length = b.length) {ns ns' : List Nat}
    (h : Pb ns ns') : ns.length = ns'.length := f ns ns' h

public theorem pb_len_arg {ns ns' : List Nat} (h : Pb ns ns') :
    ns.length = ns'.length :=
  useRec (@Pb.rec (fun _ _ _ => True)
    (fun a b _ => a.length = b.length)
    (fun _ => trivial) (fun _ _ => trivial)
    rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)) h

-- Tier B: the permuted minor band is still unapplied (2 of 9 args).
set_option linter.defProp false in
public def pbCases :
    (∀ (_ : Nat), True) →
    (∀ {ns ns' : List Nat}, Pb ns ns' →
      ns.length = ns'.length → True) →
    (List.length ([] : List Nat) = List.length ([] : List Nat)) →
    (∀ {n n' : Nat} {ns ns' : List Nat}, Pa n n' → Pb ns ns' →
      True → ns.length = ns'.length →
      (n :: ns).length = (n' :: ns').length) →
    ∀ (ns ns' : List Nat), Pb ns ns' → ns.length = ns'.length :=
  @Pb.rec (fun _ _ _ => True) (fun a b _ => a.length = b.length)

set_option linter.defProp false in
public def pbRecAlias := @Pb.rec

public theorem pbRec_eq_self : @Pb.rec = @Pb.rec := rfl

-- Mirrored source order (Pb2 before Pa2).
mutual
  public inductive Pb2 : List Nat → List Nat → Prop where
    | nil : Pb2 [] []
    | cons {n n' : Nat} {ns ns' : List Nat} :
        Pa2 n n' → Pb2 ns ns' → Pb2 (n :: ns) (n' :: ns')
  public inductive Pa2 : Nat → Nat → Prop where
    | refl (n : Nat) : Pa2 n n
    | zero {ns ns' : List Nat} : Pb2 ns ns' → Pa2 0 0
end

public theorem pb2_length {ns ns' : List Nat} (h : Pb2 ns ns') :
    ns.length = ns'.length := by
  induction h using Pb2.rec (motive_2 := fun _ _ _ => True) with
  | nil => rfl
  | cons hpa hpb ihpa ihpb => exact congrArg (· + 1) ihpb
  | refl => trivial
  | zero => trivial

public theorem pa2_eq {a b : Nat} (h : Pa2 a b) : a = b := by
  induction h using Pa2.rec
    (motive_1 := fun ns ns' _ => ns.length = ns'.length) with
  | nil => rfl
  | cons hpa hpb ihpa ihpb => exact congrArg (· + 1) ihpb
  | refl n => rfl
  | zero hb ihb => rfl

-- Mirrored-order twins of the shape-coverage theorems above. For
-- `@Pb2.rec` (all = [Pb2, Pa2]): motive_1 = Pb2's motive, motive_2 =
-- Pa2's; minors nil, cons, refl, zero.
public theorem pb2_len_direct {ns ns' : List Nat} (h : Pb2 ns ns') :
    ns.length = ns'.length :=
  @Pb2.rec (fun a b _ => a.length = b.length) (fun _ _ _ => True)
    rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)
    (fun _ => trivial) (fun _ _ => trivial)
    ns ns' h

public theorem pb2_len_lam {ns ns' : List Nat} (h : Pb2 ns ns') :
    ns.length = ns'.length :=
  (fun (p : Pb2 ns ns') =>
    @Pb2.rec (fun a b _ => a.length = b.length) (fun _ _ _ => True)
      rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)
      (fun _ => trivial) (fun _ _ => trivial)
      ns ns' p) h

public theorem pb2_len_dead {ns ns' : List Nat} (h : Pb2 ns ns') :
    ns.length = ns'.length :=
  (fun (_ : Nat) =>
    @Pb2.rec (fun a b _ => a.length = b.length) (fun _ _ _ => True)) 0
    rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)
    (fun _ => trivial) (fun _ _ => trivial)
    h

set_option linter.defProp false in
public def pb2LenFn : ∀ (ns ns' : List Nat),
    Pb2 ns ns' → ns.length = ns'.length :=
  @Pb2.rec (fun a b _ => a.length = b.length) (fun _ _ _ => True)
    rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)
    (fun _ => trivial) (fun _ _ => trivial)

public theorem pb2_len_let {ns ns' : List Nat} (h : Pb2 ns ns') :
    ns.length = ns'.length :=
  let g := @Pb2.rec (fun a b _ => a.length = b.length)
    (fun _ _ _ => True)
    rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)
    (fun _ => trivial) (fun _ _ => trivial)
  g h

set_option linter.defProp false in
public def useRec2 (f : ∀ (a b : List Nat),
    Pb2 a b → a.length = b.length) {ns ns' : List Nat}
    (h : Pb2 ns ns') : ns.length = ns'.length := f ns ns' h

public theorem pb2_len_arg {ns ns' : List Nat} (h : Pb2 ns ns') :
    ns.length = ns'.length :=
  useRec2 (@Pb2.rec (fun a b _ => a.length = b.length)
    (fun _ _ _ => True)
    rfl (fun _ _ _ ihpb => congrArg (· + 1) ihpb)
    (fun _ => trivial) (fun _ _ => trivial)) h

set_option linter.defProp false in
public def pb2Cases :
    (List.length ([] : List Nat) = List.length ([] : List Nat)) →
    (∀ {n n' : Nat} {ns ns' : List Nat}, Pa2 n n' → Pb2 ns ns' →
      True → ns.length = ns'.length →
      (n :: ns).length = (n' :: ns').length) →
    (∀ (_ : Nat), True) →
    (∀ {ns ns' : List Nat}, Pb2 ns ns' →
      ns.length = ns'.length → True) →
    ∀ (ns ns' : List Nat), Pb2 ns ns' → ns.length = ns'.length :=
  @Pb2.rec (fun a b _ => a.length = b.length) (fun _ _ _ => True)

set_option linter.defProp false in
public def pb2RecAlias := @Pb2.rec

public theorem pb2Rec_eq_self : @Pb2.rec = @Pb2.rec := rfl

end PropRecMotives

-- Type-valued nested mutual consumed through the raw recursor with explicit
-- motives, including the nested-aux motive (the PhiConfluence
-- `Term`/`Binding` shape — `Term.form` nests `Binding` through `List` — and
-- its `nf_devel`/`nf_false_reducible` check-rs failures of 2026-08-22).
-- `Tm.rec` has three motives: Tm, Bd, and the `List Bd` nested auxiliary;
-- a user `induction … using Tm.rec (motive_2 := …) (motive_3 := …)` passes
-- all three in source order. Twins in both source orders, as above.
namespace NestedMutualRecMotives

mutual
  public inductive Tm where
    | leaf
    | node (kids : List Bd)
  public inductive Bd where
    | wrap (t : Tm)
end

public theorem tm_eq_self (t : Tm) : t = t := by
  induction t using Tm.rec
    (motive_2 := fun b => b = b)
    (motive_3 := fun bs => bs = bs) with
  | leaf => rfl
  | node kids ih => rfl
  | wrap t ih => rfl
  | nil => rfl
  | cons b bs ihb ihbs => rfl

-- Mirrored source order (Bd2 before Tm2): `Tm2.rec`'s user motives arrive
-- as [Bd2, Tm2] with the aux `List Bd2` motive third.
mutual
  public inductive Bd2 where
    | wrap (t : Tm2)
  public inductive Tm2 where
    | leaf
    | node (kids : List Bd2)
end

public theorem tm2_eq_self (t : Tm2) : t = t := by
  induction t using Tm2.rec
    (motive_1 := fun b => b = b)
    (motive_3 := fun bs => bs = bs) with
  | leaf => rfl
  | node kids ih => rfl
  | wrap t ih => rfl
  | nil => rfl
  | cons b bs ihb ihbs => rfl

end NestedMutualRecMotives

end Tests.Ix.Compile.Mutual
