/-
  Cross-namespace canonicity twin fixtures.

  Each twin pair declares structurally identical Lean types in different
  namespaces with different names.  The validate-aux Phase 4b asserts that
  corresponding constants compile to the **same** content address.

  See `docs/ix_canonicity.md` for the theory and testing plan.
-/
module
public import Lean

namespace Tests.Ix.Compile.Canonicity

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 1: Simple alpha-collapse
-- ═══════════════════════════════════════════════════════════════════════
-- Structurally identical declarations in different namespaces should
-- compile to the same canonical addresses.
namespace CrossNamespaceTwin1
mutual
  public inductive A | a : B → A
  public inductive B | b : A → B
end
end CrossNamespaceTwin1

namespace CrossNamespaceTwin2
mutual
  public inductive X | a : Y → X
  public inductive Y | b : X → Y
end
end CrossNamespaceTwin2

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 2: Nested alpha-collapse (List + Option)
-- ═══════════════════════════════════════════════════════════════════════
-- Same cross-namespace shape, but with nested references that force
-- generated auxiliary recursors.
namespace CrossNamespaceNestedTwin1
mutual
  public inductive A | node : B → List A → A
  public inductive B | node : A → Option B → B
end
end CrossNamespaceNestedTwin1

namespace CrossNamespaceNestedTwin2
mutual
  public inductive X | node : Y → List X → X
  public inductive Y | node : X → Option Y → Y
end
end CrossNamespaceNestedTwin2

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 3: OverMerge (non-alpha-equivalent mutuals)
-- ═══════════════════════════════════════════════════════════════════════
-- A and B are structurally distinct (B has 2 A fields) but should hash
-- consistently when renamed to X/Y in a different namespace.
namespace CrossNamespaceOverMergeTwin1
mutual
  public inductive A | a : B → A
  public inductive B | b : A → A → B
end
end CrossNamespaceOverMergeTwin1

namespace CrossNamespaceOverMergeTwin2
mutual
  public inductive X | a : Y → X
  public inductive Y | b : X → X → Y
end
end CrossNamespaceOverMergeTwin2

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 4: 3-way alpha-collapse cycle
-- ═══════════════════════════════════════════════════════════════════════
-- All three types are alpha-equivalent (A→B→C→A cycle); all should
-- share the same address as their counterparts X→Y→Z→X.
namespace CrossNamespaceAlpha3Twin1
mutual
  public inductive A | a : B → A
  public inductive B | b : C → B
  public inductive C | c : A → C
end
end CrossNamespaceAlpha3Twin1

namespace CrossNamespaceAlpha3Twin2
mutual
  public inductive X | a : Y → X
  public inductive Y | b : Z → Y
  public inductive Z | c : X → Z
end
end CrossNamespaceAlpha3Twin2

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 5: Parameter binder rename (alpha vs beta) + nested
-- ═══════════════════════════════════════════════════════════════════════
-- Tests that binder names on type parameters don't affect hashing.
-- Explicitly listed as missing in section 16.4 of the canonicity spec.
namespace CrossNamespaceParamTwin1
mutual
  public inductive A (α : Type)
    | leaf : α → A α
    | fromB : B α → A α
    | node : List (A α) → A α
  public inductive B (α : Type)
    | leaf : α → B α
    | fromA : A α → B α
    | node : List (B α) → B α
end
end CrossNamespaceParamTwin1

namespace CrossNamespaceParamTwin2
mutual
  public inductive X (β : Type)
    | leaf : β → X β
    | fromB : Y β → X β
    | node : List (X β) → X β
  public inductive Y (β : Type)
    | leaf : β → Y β
    | fromA : X β → Y β
    | node : List (Y β) → Y β
end
end CrossNamespaceParamTwin2

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 6: 3 types x 3 containers (nested aux ordering)
-- ═══════════════════════════════════════════════════════════════════════
-- Tests that content-hash-sorted aux ordering is canonical across
-- namespaces.  Hardest canonical ordering case: 9 nested aux
-- occurrences that must sort identically whether named A/B/C or X/Y/Z.
namespace CrossNamespaceNestedOrderTwin1
mutual
  public inductive A where | mk : Array B → Option C → List A → A
  public inductive B where | mk : Array C → Option A → List B → B
  public inductive C where | mk : Array A → Option B → List C → C
end
end CrossNamespaceNestedOrderTwin1

namespace CrossNamespaceNestedOrderTwin2
mutual
  public inductive X where | mk : Array Y → Option Z → List X → X
  public inductive Y where | mk : Array Z → Option X → List Y → Y
  public inductive Z where | mk : Array X → Option Y → List Z → Z
end
end CrossNamespaceNestedOrderTwin2

namespace CrossNamespaceNestedOrderTwin3
mutual
  public inductive A where | mk : Array B → Option C → List A → A
  public inductive B where | mk : Option A → List B → B
  public inductive C where | mk : List C → C
end
end CrossNamespaceNestedOrderTwin3

namespace CrossNamespaceNestedOrderTwin4
mutual
  public inductive Z where | mk : List Z → Z
  public inductive Y where | mk : Option X → List Y → Y
  public inductive X where | mk : Array Y → Option Z → List X → X
end
end CrossNamespaceNestedOrderTwin4

namespace CrossNamespaceNestedOrderTwin5
public inductive C where | mk : List C → C
mutual
  public inductive A where | mk : Array B → Option C → List A → A
  public inductive B where | mk : Option A → List B → B
end
end CrossNamespaceNestedOrderTwin5

namespace CrossNamespaceNestedOrderTwin6
public inductive Z where | mk : List Z → Z
mutual
  public inductive Y where | mk : Option X → List Y → Y
  public inductive X where | mk : Array Y → Option Z → List X → X
end
end CrossNamespaceNestedOrderTwin6

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 7: Higher-order recursive field
-- ═══════════════════════════════════════════════════════════════════════
-- Single inductive with function-typed recursive field.
-- No mutual block, no nesting.
namespace CrossNamespaceHOTwin1
public inductive A where
  | leaf : Nat → A
  | sup : (Nat → A) → A
end CrossNamespaceHOTwin1

namespace CrossNamespaceHOTwin2
public inductive X where
  | leaf : Nat → X
  | sup : (Nat → X) → X
end CrossNamespaceHOTwin2

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 8: Self-referential collapse
-- ═══════════════════════════════════════════════════════════════════════
-- A single self-referential inductive `A | a : A -> A` should compile to
-- the same canonical form as a mutual pair that alpha-collapses (e.g.
-- CrossNamespaceTwin1.{A,B} above).
--
-- We also declare a fresh mutual pair (X <-> Y) in a second namespace to
-- verify the self-ref and mutual-pair forms agree.

namespace SelfRefTwin1
public inductive A | a : A → A
end SelfRefTwin1

namespace SelfRefTwin2
mutual
  public inductive X | a : Y → X
  public inductive Y | b : X → Y
end
end SelfRefTwin2

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 9: OverMerge + alpha-collapse (partial collapse)
-- ═══════════════════════════════════════════════════════════════════════
-- A and B alpha-collapse (A ≅ B), but C is structurally different (it
-- references both A and B without being referenced by them).  Tests that
-- partial collapse works consistently across namespaces.

namespace OverMergeAlphaCollapseTwin1
mutual
  public inductive A | a : B → A
  public inductive B | b : A → B
  public inductive C | c : A → B → C
end
end OverMergeAlphaCollapseTwin1

namespace OverMergeAlphaCollapseTwin2
mutual
  public inductive X | a : Y → X
  public inductive Y | b : X → Y
  public inductive Z | c : X → Y → Z
end
end OverMergeAlphaCollapseTwin2

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 10: Nested + non-alpha-equivalent mutuals
-- ═══════════════════════════════════════════════════════════════════════
-- A and B are NOT alpha-equivalent (B has an extra A field), but both
-- nest through List.  Tests aux ordering for nested containers when the
-- block members are structurally distinct.

namespace NestedOverMergeTwin1
mutual
  public inductive A where
    | a : B → List A → A
  public inductive B where
    | b : A → A → List B → B
end
end NestedOverMergeTwin1

namespace NestedOverMergeTwin2
mutual
  public inductive X where
    | a : Y → List X → X
  public inductive Y where
    | b : X → X → List Y → Y
end
end NestedOverMergeTwin2

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 11: Binary container nesting (Prod)
-- ═══════════════════════════════════════════════════════════════════════
-- Nesting through `Prod` (2-argument container), unlike the unary
-- `List`/`Option`/`Array` containers in other twins.  Tests that
-- spec_params with arity > 1 hash correctly.
-- All 3 types alpha-collapse (A ≅ B ≅ C).

namespace ProdNestedTwin1
mutual
  public inductive A where | mk : Prod A B → Prod B C → Prod C A → A
  public inductive B where | mk : Prod A B → Prod B C → Prod C A → B
  public inductive C where | mk : Prod A B → Prod B C → Prod C A → C
end
end ProdNestedTwin1

namespace ProdNestedTwin2
mutual
  public inductive X where | mk : Prod X Y → Prod Y Z → Prod Z X → X
  public inductive Y where | mk : Prod X Y → Prod Y Z → Prod Z X → Y
  public inductive Z where | mk : Prod X Y → Prod Y Z → Prod Z X → Z
end
end ProdNestedTwin2

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 12: Simple nested (single inductive + List)
-- ═══════════════════════════════════════════════════════════════════════
-- Simplest nested case: a single (non-mutual) inductive nesting through
-- List.  No alpha-collapse.

namespace SimpleNestedTwin1
public inductive A where
  | leaf : Nat → A
  | node : List A → A
end SimpleNestedTwin1

namespace SimpleNestedTwin2
public inductive X where
  | leaf : Nat → X
  | node : List X → X
end SimpleNestedTwin2

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 13: Structures
-- ═══════════════════════════════════════════════════════════════════════
-- Structures generate projection constants — a different compilation
-- path from plain inductives.  Tests that structure machinery is
-- namespace-independent.

namespace StructureTwin1
mutual
  public structure SC where
    val : Nat
    proof : SP
  public inductive SP where
    | base : Nat → SP
    | combine : SC → SC → SP
end
end StructureTwin1

namespace StructureTwin2
mutual
  public structure XC where
    val : Nat
    proof : XP
  public inductive XP where
    | base : Nat → XP
    | combine : XC → XC → XP
end
end StructureTwin2

end Tests.Ix.Compile.Canonicity
