module

@[expose] public section

/-!
# Unpack specifications for modeled structure projections

When a 1-constructor, 0-index member of a modeled (mutual or nested) inductive
block stores a field inside its native auxiliary inductive `aux`, projecting
that field may need to unpack mimic-container subtrees back into the container's
real constructors.  `UnpackSpec` is the finite, level-independent recipe
describing how each `aux` constructor tag unpacks in the set model.
-/

namespace Ix.Kernel.Term

/-- How a mimic container constructor builds its set-model value from its
field values. -/
inductive UnpackCtorKind where
  /-- Native 1-constructor non-recursive structure (positive sort): `mkTower args`. -/
  | structMk
  /-- Native sum or recursive inductive constructor `ctorTag` (positive sort):
      `inj ctorTag (mkTower (args ++ [pt]))`. -/
  | sumMk (ctorTag : Nat)
  /-- Basis `PSigma'.mk` (positive sort): `spair a b`. -/
  | psigmaMk
  /-- `Prop`-level (sort 0) container constructor: `pt`. -/
  | propMk
  deriving Repr, DecidableEq, Inhabited

/-- Per-constructor rule for unpacking an `aux` value, indexed by `aux`'s
constructor tag. -/
inductive UnpackRule where
  /-- Real member constructor (or non-mimic value): pass through unchanged. -/
  | passthrough
  /-- Mimic container constructor: read `recFlags.length` fields from the `aux`
      payload, recursively unpack each field whose flag is `true`, and rebuild
      with `kind`. -/
  | rebuild (kind : UnpackCtorKind) (recFlags : List Bool)
  deriving Repr, DecidableEq, Inhabited

/-- Table of unpack rules indexed by `aux`'s constructor tag.  An empty list
acts as the identity function. -/
abbrev UnpackSpec := List UnpackRule

end Ix.Kernel.Term
