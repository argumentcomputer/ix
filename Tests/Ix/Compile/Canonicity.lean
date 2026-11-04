/-
  Cross-namespace canonicity twin fixtures.

  Renamed families and source-layout variants feed `validateAuxClosure` for
  compiler parity, schedule independence and reconstruction checks. Those
  suites compare the same input under different implementations or schedules;
  this file does not assert address equality between different declarations.
  Every mutual member retains its source slot, including symmetric members.

  See `docs/ix_canonicity.md` for the current representation contract.
-/
module
public import Lean

namespace Tests.Ix.Compile.Canonicity

-- ═══════════════════════════════════════════════════════════════════════
-- Twin 1: Symmetric mutual pair
-- ═══════════════════════════════════════════════════════════════════════
-- Structurally identical declarations in different namespaces, with the
-- same member order and two separate slots in each block.
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
-- Twin 2: Nested mutual pair (List + Option)
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
-- Twin 4: Three-member cycle
-- ═══════════════════════════════════════════════════════════════════════
-- Symmetric A→B→C→A and X→Y→Z→X cycles. Each retains three members;
-- symmetry does not identify their projection indices.
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
-- Renamed type parameters keep the same anonymous binder positions.
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
-- Nine nested occurrences across three members, with renamed, reordered
-- and separately declared variants below. Each compiles its own source
-- layout and Lean-generated auxiliaries without hash-sorting their order.
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
-- Twin 8: Self-reference and a mutual pair
-- ═══════════════════════════════════════════════════════════════════════
-- A self-referential singleton and a two-member cycle exercise different
-- block layouts. The pair keeps both slots; it does not collapse to the
-- singleton's encoding.

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
-- Twin 9: Symmetric pair with a dependent member
-- ═══════════════════════════════════════════════════════════════════════
-- A and B have symmetric shapes. C references both without being referenced
-- by them. All source members and their corresponding projections remain.

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
-- Nesting through the two-argument `Prod` container. The constructor fields
-- refer to all three members, which retain separate slots in source order.

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
-- Simplest nested case: a single inductive nesting through List.

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

namespace ZFA
/- Mathlib `SetTheory/Lists` shape, transcribed self-contained: a
   Prop-level MUTUAL pair (`Lists.Equiv` / `Lists'.Subset`) indexed by a
   sigma over a Bool-indexed inductive, with a ctor argument applying an
   external recursive function (`toList`). Reproduces the Mathlib-scale
   `.below.rec` divergence found during benchmarking (the only 2
   diverging constants in the 3.15 GB Mathlib env were
   `Lists.Equiv.below.rec` / `Lists'.Subset.below.rec`). -/

inductive Lists' (α : Type u) : Bool → Type u
  | atom : α → Lists' α false
  | nil : Lists' α true
  | cons' {b} : Lists' α b → Lists' α true → Lists' α true

def Lists (α : Type u) := Σ b, Lists' α b

variable {α : Type u}

namespace Lists'

def cons : Lists α → Lists' α true → Lists' α true
  | ⟨_, a⟩, l => cons' a l

def toList : ∀ {b}, Lists' α b → List (Lists α)
  | _, atom _ => []
  | _, nil => []
  | _, cons' a l => ⟨_, a⟩ :: l.toList

end Lists'

mutual
  inductive Lists.Equiv : Lists α → Lists α → Prop
    | refl (l) : Lists.Equiv l l
    | antisymm {l₁ l₂ : Lists' α true} :
      Lists'.Subset l₁ l₂ → Lists'.Subset l₂ l₁ → Lists.Equiv ⟨_, l₁⟩ ⟨_, l₂⟩

  inductive Lists'.Subset : Lists' α true → Lists' α true → Prop
    | nil {l} : Lists'.Subset Lists'.nil l
    | cons {a a' l l'} :
      Lists.Equiv a a' →
        a' ∈ Lists'.toList l' → Lists'.Subset l l' →
          Lists'.Subset (Lists'.cons a l) l'
end

end ZFA

namespace ZFA2
/- Mathlib `SetTheory/Lists` shape, transcribed self-contained: a
   Prop-level MUTUAL pair (`Lists.Equiv` / `Lists'.Subset`) indexed by a
   sigma over a Bool-indexed inductive, with a ctor argument applying an
   external recursive function (`toList`). Reproduces the Mathlib-scale
   `.below.rec` divergence found during benchmarking (the only 2
   diverging constants in the 3.15 GB Mathlib env were
   `Lists.Equiv.below.rec` / `Lists'.Subset.below.rec`). -/

inductive Lists' (α : Type u) : Bool → Type u
  | atom : α → Lists' α false
  | nil : Lists' α true
  | cons' {b} : Lists' α b → Lists' α true → Lists' α true

def Lists (α : Type u) := Σ b, Lists' α b

variable {α : Type u}

namespace Lists'

def cons : Lists α → Lists' α true → Lists' α true
  | ⟨_, a⟩, l => cons' a l

def toList : ∀ {b}, Lists' α b → List (Lists α)
  | _, atom _ => []
  | _, nil => []
  | _, cons' a l => ⟨_, a⟩ :: l.toList

end Lists'

mutual
  inductive Lists.Equiv : Lists α → Lists α → Prop
    | refl (l) : Lists.Equiv l l
    | antisymm {l₁ l₂ : Lists' α true} :
      Lists'.Subset l₁ l₂ → Lists'.Subset l₂ l₁ → Lists.Equiv ⟨_, l₁⟩ ⟨_, l₂⟩

  inductive Lists'.Subset : Lists' α true → Lists' α true → Prop
    | nil {l} : Lists'.Subset Lists'.nil l
    | cons {a a' l l'} :
      Lists.Equiv a a' →
        a' ∈ Lists'.toList l' → Lists'.Subset l l' →
          Lists'.Subset (Lists'.cons a l) l'
end

end ZFA2
namespace ZFA3
/- Mathlib `SetTheory/Lists` shape, transcribed self-contained: a
   Prop-level MUTUAL pair (`Lists.Equiv` / `Lists'.Subset`) indexed by a
   sigma over a Bool-indexed inductive, with a ctor argument applying an
   external recursive function (`toList`). Reproduces the Mathlib-scale
   `.below.rec` divergence found during benchmarking (the only 2
   diverging constants in the 3.15 GB Mathlib env were
   `Lists.Equiv.below.rec` / `Lists'.Subset.below.rec`). -/

inductive Lists' (α : Type u) : Bool → Type u
  | atom : α → Lists' α false
  | nil : Lists' α true
  | cons' {b} : Lists' α b → Lists' α true → Lists' α true

def Lists (α : Type u) := Σ b, Lists' α b

variable {α : Type u}

namespace Lists'

def cons : Lists α → Lists' α true → Lists' α true
  | ⟨_, a⟩, l => cons' a l

def toList : ∀ {b}, Lists' α b → List (Lists α)
  | _, atom _ => []
  | _, nil => []
  | _, cons' a l => ⟨_, a⟩ :: l.toList

end Lists'

mutual
  inductive Lists.Equiv : Lists α → Lists α → Prop
    | refl (l) : Lists.Equiv l l
    | antisymm {l₁ l₂ : Lists' α true} :
      Lists'.Subset l₁ l₂ → Lists'.Subset l₂ l₁ → Lists.Equiv ⟨_, l₁⟩ ⟨_, l₂⟩

  inductive Lists'.Subset : Lists' α true → Lists' α true → Prop
    | nil {l} : Lists'.Subset Lists'.nil l
    | cons {a a' l l'} :
      Lists.Equiv a a' →
        a' ∈ Lists'.toList l' → Lists'.Subset l l' →
          Lists'.Subset (Lists'.cons a l) l'
end

end ZFA3
namespace ZFA4
/- Mathlib `SetTheory/Lists` shape, transcribed self-contained: a
   Prop-level MUTUAL pair (`Lists.Equiv` / `Lists'.Subset`) indexed by a
   sigma over a Bool-indexed inductive, with a ctor argument applying an
   external recursive function (`toList`). Reproduces the Mathlib-scale
   `.below.rec` divergence found during benchmarking (the only 2
   diverging constants in the 3.15 GB Mathlib env were
   `Lists.Equiv.below.rec` / `Lists'.Subset.below.rec`). -/

inductive Lists' (α : Type u) : Bool → Type u
  | atom : α → Lists' α false
  | nil : Lists' α true
  | cons' {b} : Lists' α b → Lists' α true → Lists' α true

def Lists (α : Type u) := Σ b, Lists' α b

variable {α : Type u}

namespace Lists'

def cons : Lists α → Lists' α true → Lists' α true
  | ⟨_, a⟩, l => cons' a l

def toList : ∀ {b}, Lists' α b → List (Lists α)
  | _, atom _ => []
  | _, nil => []
  | _, cons' a l => ⟨_, a⟩ :: l.toList

end Lists'

mutual
  inductive Lists.Equiv : Lists α → Lists α → Prop
    | refl (l) : Lists.Equiv l l
    | antisymm {l₁ l₂ : Lists' α true} :
      Lists'.Subset l₁ l₂ → Lists'.Subset l₂ l₁ → Lists.Equiv ⟨_, l₁⟩ ⟨_, l₂⟩

  inductive Lists'.Subset : Lists' α true → Lists' α true → Prop
    | nil {l} : Lists'.Subset Lists'.nil l
    | cons {a a' l l'} :
      Lists.Equiv a a' →
        a' ∈ Lists'.toList l' → Lists'.Subset l l' →
          Lists'.Subset (Lists'.cons a l) l'
end

end ZFA4
namespace ZFA5
/- Mathlib `SetTheory/Lists` shape, transcribed self-contained: a
   Prop-level MUTUAL pair (`Lists.Equiv` / `Lists'.Subset`) indexed by a
   sigma over a Bool-indexed inductive, with a ctor argument applying an
   external recursive function (`toList`). Reproduces the Mathlib-scale
   `.below.rec` divergence found during benchmarking (the only 2
   diverging constants in the 3.15 GB Mathlib env were
   `Lists.Equiv.below.rec` / `Lists'.Subset.below.rec`). -/

inductive Lists' (α : Type u) : Bool → Type u
  | atom : α → Lists' α false
  | nil : Lists' α true
  | cons' {b} : Lists' α b → Lists' α true → Lists' α true

def Lists (α : Type u) := Σ b, Lists' α b

variable {α : Type u}

namespace Lists'

def cons : Lists α → Lists' α true → Lists' α true
  | ⟨_, a⟩, l => cons' a l

def toList : ∀ {b}, Lists' α b → List (Lists α)
  | _, atom _ => []
  | _, nil => []
  | _, cons' a l => ⟨_, a⟩ :: l.toList

end Lists'

mutual
  inductive Lists.Equiv : Lists α → Lists α → Prop
    | refl (l) : Lists.Equiv l l
    | antisymm {l₁ l₂ : Lists' α true} :
      Lists'.Subset l₁ l₂ → Lists'.Subset l₂ l₁ → Lists.Equiv ⟨_, l₁⟩ ⟨_, l₂⟩

  inductive Lists'.Subset : Lists' α true → Lists' α true → Prop
    | nil {l} : Lists'.Subset Lists'.nil l
    | cons {a a' l l'} :
      Lists.Equiv a a' →
        a' ∈ Lists'.toList l' → Lists'.Subset l l' →
          Lists'.Subset (Lists'.cons a l) l'
end

end ZFA5

/-!
Symmetric mutual Prop pairs and their source auxiliaries.

`P` and `Q` have symmetric mutual references but retain distinct member
slots. The two namespaces provide the same source shape, including Lean's
original `.below` and `.below.rec` declarations, for the shared corpus.
-/

namespace PropCollapseA

mutual
  inductive P : Nat → Prop
    | step : ∀ n, Q n → P n
  inductive Q : Nat → Prop
    | step : ∀ n, P n → Q n
end

end PropCollapseA

namespace PropCollapseB

mutual
  inductive P : Nat → Prop
    | step : ∀ n, Q n → P n
  inductive Q : Nat → Prop
    | step : ∀ n, P n → Q n
end

end PropCollapseB

/-!
Cross-block alias-occurrence provenance.

`WrapA` and `WrapB` are alpha-identical wrapper definitions in separate
blocks, so they share a content address. Each inductive below uses both
source names in one expression. Compilation and reconstruction must retain
the spelling of each occurrence, including those in Lean's auxiliaries.

Coverage axes:
- `StepAB`/`StepBA`: both orientations through a reducible index
  wrapper (`RelOn`, the `HomRel (Paths (Symmetrify V))` shape of the
  Mathlib motivating instance). Reducing `RelOn (WrapA (WrapB V))`
  exposes the index telescope and both alias occurrences. The mirrored
  orientation distinguishes occurrence metadata from a first-seen or
  least-name policy.
- `DirectAB`: the same double occurrence as a plain index telescope
  (syntactic peel, no reduction).
- `Pair`: both spellings as sibling constructor fields — the
  hint-collision shape (`WrapA V` and `WrapB V` are content-identical
  subterms of one constructor type).
-/

namespace AliasProvenance

universe u

-- `@[expose]`: the inductives below take these as (reducible) index
-- types; without exposed bodies the compiler infers a different
-- compilation type locally than importers would and refuses to compile.
@[expose] public def WrapA (V : Type u) : Type u := V
@[expose] public def WrapB (V : Type u) : Type u := V

public abbrev RelOn (C : Type u) : Type u := C → C → Prop

public inductive StepAB (V : Type u) : RelOn (WrapA (WrapB V)) where
  | refl : (x : WrapA (WrapB V)) → StepAB V x x

public inductive StepBA (V : Type u) : RelOn (WrapB (WrapA V)) where
  | refl : (x : WrapB (WrapA V)) → StepBA V x x

public inductive DirectAB (V : Type u) :
    WrapA (WrapB V) → WrapA (WrapB V) → Prop where
  | refl : (x : WrapA (WrapB V)) → DirectAB V x x

public inductive Pair (V : Type u) : Type u where
  | mk : WrapA V → WrapB V → Pair V

end AliasProvenance

end Tests.Ix.Compile.Canonicity
