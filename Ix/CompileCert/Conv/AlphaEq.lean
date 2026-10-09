import Ix.CompileCert.Conv.Tm

/-!
The image comparator implies the existing erasure equality on all raw expressions.
No hash faithfulness, freshness, source well-formedness or callback restriction is
assumed. The converse is intentionally absent: `er` erases one-sided metadata,
whereas the image comparator only compares two metadata constructors together.
-/

namespace Ix.CompileCert.Conv

open Ix (Expr Name Level)
open Ix.Compile.Image (alphaEq)
open Ix.Compile.Image.RawExact (nameEq_eq_true levelEq_eq_true levelsEq_eq_true)

private theorem literal_eq_of_beq {a b : Lean.Literal} (h : (a == b) = true) : a = b := by
  cases a <;> cases b
  case natVal.natVal a b =>
    change (a == b) = true at h
    exact congrArg Lean.Literal.natVal (beq_iff_eq.mp h)
  case strVal.strVal a b =>
    change (a == b) = true at h
    exact congrArg Lean.Literal.strVal (beq_iff_eq.mp h)
  all_goals exact False.elim (Bool.noConfusion h)

/-- Success of the actual image comparator gives equality of the unchanged
erasure, for arbitrary raw names, levels, expressions and cached addresses. -/
theorem alphaEq_er (a b : Expr) (h : alphaEq a b = true) : er a = er b := by
  induction a generalizing b <;> cases b
  all_goals try exact False.elim (Bool.noConfusion h)
  case bvar.bvar i _ j _ =>
    exact congrArg Tm.bvar (beq_iff_eq.mp h)
  case fvar.fvar a _ b _ =>
    exact congrArg Tm.fvar ((nameEq_eq_true a b).mp h)
  case mvar.mvar a _ b _ =>
    exact congrArg Tm.mvar ((nameEq_eq_true a b).mp h)
  case sort.sort u _ v _ =>
    exact congrArg Tm.sort ((levelEq_eq_true u v).mp h)
  case const.const a us _ b vs _ =>
    obtain ⟨hn, hu⟩ := Bool.and_eq_true.mp h
    have sameName := (nameEq_eq_true a b).mp hn
    have sameLevels := (levelsEq_eq_true us vs).mp hu
    cases sameName
    cases sameLevels
    rfl
  case app.app f x _ ihf ihx g y _ =>
    obtain ⟨hf, hx⟩ := Bool.and_eq_true.mp h
    change Tm.app (er f) (er x) = Tm.app (er g) (er y)
    rw [ihf g hf, ihx y hx]
  case lam.lam _ t x _ _ iht ihx _ u y _ _ =>
    obtain ⟨ht, hx⟩ := Bool.and_eq_true.mp h
    change Tm.lam (er t) (er x) = Tm.lam (er u) (er y)
    rw [iht u ht, ihx y hx]
  case forallE.forallE _ t x _ _ iht ihx _ u y _ _ =>
    obtain ⟨ht, hx⟩ := Bool.and_eq_true.mp h
    change Tm.pi (er t) (er x) = Tm.pi (er u) (er y)
    rw [iht u ht, ihx y hx]
  case letE.letE _ t v x _ _ iht ihv ihx _ u w y _ _ =>
    obtain ⟨htv, hx⟩ := Bool.and_eq_true.mp h
    obtain ⟨ht, hv⟩ := Bool.and_eq_true.mp htv
    change Tm.letE (er t) (er v) (er x) = Tm.letE (er u) (er w) (er y)
    rw [iht u ht, ihv w hv, ihx y hx]
  case lit.lit a _ b _ =>
    exact congrArg Tm.lit (literal_eq_of_beq h)
  case mdata.mdata _ a _ ih _ b _ =>
    exact ih b h
  case proj.proj s i a _ ih t j b _ =>
    obtain ⟨hsi, hab⟩ := Bool.and_eq_true.mp h
    obtain ⟨hs, hi⟩ := Bool.and_eq_true.mp hsi
    have sameName := (nameEq_eq_true s t).mp hs
    have sameIndex : i = j := beq_iff_eq.mp hi
    cases sameName
    cases sameIndex
    change Tm.proj s i (er a) = Tm.proj s i (er b)
    rw [ih b hab]

/-- The original same-address/different-name witness is now refused. -/
theorem alphaEq_name_collision_refused (h : Address) :
    alphaEq (.fvar (.anonymous h) h)
      (.fvar (.str (.anonymous h) "different" h) h) = false := by
  rfl

/-- Level constructor collisions are refused independently of names. -/
theorem alphaEq_level_collision_refused (h : Address) :
    alphaEq (.sort (.zero h) h) (.sort (.succ (.zero h) h) h) = false := by
  rfl

/-- Equal raw leaves remain accepted even when expression caches differ. -/
theorem alphaEq_fvar_neighbour (n : Name) (h k : Address) :
    alphaEq (.fvar n h) (.fvar n k) = true :=
  (nameEq_eq_true n n).mpr rfl

/-- Expression hash equality does not identify distinct bound variables. -/
theorem alphaEq_bvar_collision_refused (h : Address) :
    alphaEq (.bvar 0 h) (.bvar 1 h) = false := by
  rfl

/-- The image comparator preserves its original two-sided metadata policy. -/
theorem alphaEq_one_sided_mdata_refused (md : Array (Name × Ix.DataValue)) (h k : Address) :
    alphaEq (.mdata md (.bvar 0 h) k) (.bvar 0 h) = false := by
  rfl

end Ix.CompileCert.Conv
