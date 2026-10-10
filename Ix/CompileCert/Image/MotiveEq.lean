module
public import Ix.Compile.Image.MotiveEq
import all Ix.Compile.Image.MotiveEq
import all Ix.Compile.Image.Expr
import all IxC.Ixon.Types
public section

/-!
The motive comparator preserves every raw-alpha match and identifies additional
universe spellings only through successful positional conversion and equal
canonical wire universes. Semantic preservation of `canonUniv` remains the
shared universe-normalization obligation; it is not assumed as a new axiom.
-/

namespace Ix.CompileCert.Img.MotiveMatch

open Ix (Name Level Expr)
open Ix.Compile.Image

theorem univ_beq_iff (left right : Ixon.Univ) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Ixon.instBEqUniv.beq]

theorem levelEq_spec (params : Array Name) (left right : Level) :
    motiveLevelEq params left right = true ↔ left = right ∨
      ∃ u v, motiveUniv params left = some u ∧ motiveUniv params right = some v ∧
        Ixon.canonUniv u = Ixon.canonUniv v := by
  unfold motiveLevelEq
  rw [Bool.or_eq_true, RawExact.levelEq_eq_true]
  cases motiveUniv params left <;> cases motiveUniv params right <;>
    simp [univ_beq_iff]

theorem levelEq_refl (params : Array Name) (level : Level) :
    motiveLevelEq params level level = true :=
  (levelEq_spec params level level).mpr (.inl rfl)

theorem levelEq_of_raw (params : Array Name) {left right : Level}
    (same : RawExact.levelEq left right = true) : motiveLevelEq params left right = true := by
  simp only [motiveLevelEq, same, Bool.true_or]

theorem levelsEq_of_raw (params : Array Name) {left right : Array Level}
    (same : RawExact.levelsEq left right = true) : motiveLevelsEq params left right = true := by
  have same := (RawExact.levelsEq_eq_true left right).mp same
  subst right
  simp only [motiveLevelsEq, beq_self_eq_true, Bool.true_and, Array.all_eq_true]
  intro i hi
  simp only [Array.getElem_zip]
  exact levelEq_refl params _

/-- No input previously matched by the raw alpha comparator is lost, including
arbitrary cached fields, metadata and levels outside the parameter context. -/
theorem motiveEq_of_alphaEq (params : Array Name) (left right : Expr)
    (same : alphaEq left right = true) : motiveEq params left right = true := by
  induction left generalizing right <;> cases right <;>
    simp_all only [alphaEq, motiveEq, Bool.and_eq_true, Bool.false_eq_true]
  all_goals grind only [levelEq_of_raw, levelsEq_of_raw]

theorem motiveEq_constant_name {params : Array Name} {left right : Name}
    {ls rs : Array Level} {lh rh : Address}
    (same : motiveEq params (.const left ls lh) (.const right rs rh) = true) :
    left = right := by
  exact (RawExact.nameEq_eq_true left right).mp (Bool.and_eq_true_iff.mp same).1

end Ix.CompileCert.Img.MotiveMatch
