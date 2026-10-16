/-
  Ix.Compile.Image.MotiveEq: the image generator's motive/slot comparison.

  It is `exprEqWith` (`Ix.Compile.Image.Expr`) with universes compared in
  their canonical wire form: names stay exact and metadata must still be
  paired, so only the level test differs from `alphaEq`. The comparison does
  not rewrite the source types or their universe metadata.
-/
module
public import Ix.Compile.Image.Expr
public import Ix.IxonUniv
public section

namespace Ix.Compile.Image

/-- Positional universes for motive matching. Parameter lookup confirms the
complete raw name; a cached hash alone cannot identify two parameters. -/
def motiveUniv (params : Array Ix.Name) : Ix.Level → Option Ixon.Univ
  | .zero _ => some .zero
  | .succ u _ => .succ <$> motiveUniv params u
  | .max u v _ => .max <$> motiveUniv params u <*> motiveUniv params v
  | .imax u v _ => .imax <$> motiveUniv params u <*> motiveUniv params v
  | .param name _ => do
    let index ← params.findIdx? (RawExact.nameEq name ·)
    if index < UInt64.size then some (.var index.toUInt64) else none
  | .mvar .. => none

/-- Match universe spellings using the same canonical wire form as nested
occurrence keys and serialization. Exact raw matches remain accepted even
outside the supplied parameter context; unknown unequal levels never match. -/
def motiveLevelEq (params : Array Ix.Name) (left right : Ix.Level) : Bool :=
  RawExact.levelEq left right ||
    match motiveUniv params left, motiveUniv params right with
    | some left, some right => Ixon.canonUniv left == Ixon.canonUniv right
    | _, _ => false

/-- The motive/slot comparison: `exprEqWith` with `motiveLevelEq`. -/
def motiveEq (params : Array Ix.Name) (a b : Ix.Expr) : Bool :=
  exprEqWith (motiveLevelEq params) a b

end Ix.Compile.Image

end
