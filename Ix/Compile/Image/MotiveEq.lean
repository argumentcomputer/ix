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

def motiveLevelsEq (params : Array Ix.Name) (left right : Array Ix.Level) : Bool :=
  left.size == right.size && (left.zip right).all (fun (u, v) => motiveLevelEq params u v)

/-- The image generator's motive/slot comparison. Only universe comparison
differs from `alphaEq`: names stay exact, and metadata must still be paired.
This comparison does not rewrite the source types or their universe metadata. -/
def motiveEq (params : Array Ix.Name) : Ix.Expr → Ix.Expr → Bool
  | .bvar i _, .bvar j _ => i == j
  | .fvar a _, .fvar b _ => RawExact.nameEq a b
  | .mvar a _, .mvar b _ => RawExact.nameEq a b
  | .sort u _, .sort v _ => motiveLevelEq params u v
  | .const a us _, .const b vs _ => RawExact.nameEq a b && motiveLevelsEq params us vs
  | .app f a _, .app g b _ => motiveEq params f g && motiveEq params a b
  | .lam _ t b _ _, .lam _ t' b' _ _ => motiveEq params t t' && motiveEq params b b'
  | .forallE _ t b _ _, .forallE _ t' b' _ _ => motiveEq params t t' && motiveEq params b b'
  | .letE _ t v b _ _, .letE _ t' v' b' _ _ =>
    motiveEq params t t' && motiveEq params v v' && motiveEq params b b'
  | .lit a _, .lit b _ => a == b
  | .mdata _ a _, .mdata _ b _ => motiveEq params a b
  | .proj s i a _, .proj s' i' b _ => RawExact.nameEq s s' && i == i' && motiveEq params a b
  | _, _ => false

end Ix.Compile.Image
