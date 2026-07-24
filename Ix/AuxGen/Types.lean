/-
  Ix.AuxGen.Types: data shapes for the auxiliary-generation subsystem.

  Mirrors the Rust aux_gen data model. Layout note: Rust keeps `BelowDef`/
  `BelowIndc`/`BelowCtor` in `aux_gen/below.rs:56-98` and `BRecOnDef` in
  `aux_gen/brecon.rs:47-55`, next to their generators; the Lean port
  centralizes the plain data here so `PatchedConstant` (aux_gen.rs:98) and
  the generator modules can all import one leaf module. Field-for-field
  identical to the Rust structs.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public section

namespace Ix.AuxGen

/-- A simple auxiliary definition (type + value + level params).

    `isUnsafe` mirrors the parent inductive's flag: Lean's
    `mkDefinitionValInferringUnsafe` flips to unsafe whenever type or value
    mentions an unsafe constant, and every auxiliary references its parent
    inductive. Mirrors Rust `AuxDef` (aux_gen.rs:121). -/
structure AuxDef where
  name : Name
  levelParams : Array Name
  typ : Expr
  value : Expr
  isUnsafe : Bool
  deriving Repr, Nonempty, Inhabited

/-- A generated `.below` definition (Type-level case).
    Mirrors Rust `BelowDef` (aux_gen/below.rs:56). -/
structure BelowDef where
  name : Name
  levelParams : Array Name
  typ : Expr
  value : Expr
  isUnsafe : Bool
  deriving Repr, Nonempty, Inhabited

/-- A constructor for a Prop-level `.below` inductive.
    Mirrors Rust `BelowCtor` (aux_gen/below.rs:90). -/
structure BelowCtor where
  name : Name
  typ : Expr
  nParams : Nat
  nFields : Nat
  deriving Repr, Nonempty, Inhabited

/-- A generated `.below` inductive (Prop-level case).

    `nIndices` = original inductive's indices + 1 (major premise).
    `isReflexive` iff the parent is reflexive (a higher-order recursive IH
    field translates to a higher-order `.below` IH, making `.below` itself
    reflexive — the flag keeps the content hash aligned with Lean's
    `IndPredBelow` output). Mirrors Rust `BelowIndc` (aux_gen/below.rs:65). -/
structure BelowIndc where
  name : Name
  levelParams : Array Name
  nParams : Nat
  nIndices : Nat
  isReflexive : Bool
  isUnsafe : Bool
  typ : Expr
  ctors : Array BelowCtor
  deriving Repr, Nonempty, Inhabited

/-- A generated `.below` constant — Type-level definition or Prop-level
    inductive. Mirrors Rust `BelowConstant` (aux_gen/below.rs:42). -/
inductive BelowConstant where
  | defn : BelowDef → BelowConstant
  | indc : BelowIndc → BelowConstant
  deriving Repr, Nonempty, Inhabited

/-- A generated `.brecOn` (or `.brecOn.go` / `.brecOn.eq`) definition.

    `isProp` selects the generation path: Prop-level (`IndPredBelow.lean`
    analogue — single `.brecOn` theorem, never `.go`/`.eq`) vs Type-level
    (`BRecOn.lean` analogue — `.go` + `.brecOn` as Defn, `.eq` as
    Thm/opaque-hint unsafe Defn). Mirrors Rust `BRecOnDef`
    (aux_gen/brecon.rs:47). -/
structure BRecOnDef where
  name : Name
  levelParams : Array Name
  typ : Expr
  value : Expr
  isUnsafe : Bool
  isProp : Bool
  deriving Repr, Nonempty, Inhabited

/-- A regenerated constant ready for compilation.
    Mirrors Rust `PatchedConstant` (aux_gen.rs:98). Constructor names carry
    a `Def`/`recr` twist because the natural ones (`rec`, `recOn`,
    `casesOn`, `brecOn`) collide with Lean's auto-generated auxiliaries of
    this very inductive. -/
inductive PatchedConstant where
  /-- A regenerated `.rec` recursor. -/
  | recr : RecursorVal → PatchedConstant
  /-- A regenerated `.recOn` definition (arg-reordered `.rec` wrapper). -/
  | recOnDef : AuxDef → PatchedConstant
  /-- A regenerated `.casesOn` definition (`.rec` wrapper without IHs). -/
  | casesOnDef : AuxDef → PatchedConstant
  /-- A regenerated `.below` definition (Type-level case). -/
  | belowDef : BelowDef → PatchedConstant
  /-- A regenerated `.below` inductive (Prop-level case). -/
  | belowIndc : BelowIndc → PatchedConstant
  /-- A regenerated `.brecOn` (or `.brecOn.go`, `.brecOn.eq`) definition. -/
  | brecOnDef : BRecOnDef → PatchedConstant
  deriving Repr, Nonempty, Inhabited

/-- Output of `generateAuxPatches`.

    `perm` is the canonical hash-sort permutation for the aux section of the
    expanded block: `perm[sourceJ] = canonicalI` per source-walk aux
    position, with `PERM_OUT_OF_SCC` (see `Ix.AuxGen.Nested`) for auxes
    whose spec-params live in other SCCs; `none` when the block has no
    nested auxiliaries. Mirrors Rust `AuxPatchesOutput` (aux_gen.rs:137). -/
structure AuxPatchesOutput where
  /-- Regenerated canonical-layout constants, keyed by their Lean-visible
      source-indexed name (e.g. `A.rec`, `A.below_2`). -/
  patches : Std.HashMap Name PatchedConstant := {}
  /-- Lean-visible aux names that resolve to an already-compiled canonical
      patch instead of compiling a renamed copy (source name → patch name). -/
  aliases : Std.HashMap Name Name := {}
  perm : Option (Array Nat) := none
  /-- Number of equivalence classes (primary members) in the canonical block. -/
  nClasses : Nat := 0
  /-- Number of canonical aux members (length of the hash-sorted aux section). -/
  nCanonicalAux : Nat := 0
  /-- Number of source-walk aux positions (≥ `nCanonicalAux` under collapse). -/
  nSourceAux : Nat := 0
  deriving Inhabited

end Ix.AuxGen
