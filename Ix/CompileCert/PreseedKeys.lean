import Ix.CompileM
import Std.Data.HashMap.Lemmas

/-! Exact visited keys for table collection. Unequal expressions and positional
contexts remain distinct even when all bucket hints collide. The coverage
cutoff supports pending ancestors in the preorder walk; it is not yet a proof
of complete reference/universe collection. -/

namespace Ix.CompileCert.PreseedKeys

open Ix.Compile.ExactKey
open Ix.CompileM

abbrev Seen := Std.HashMap PreseedKey Unit

theorem insert_other (seen : Seen) (stored queried : PreseedKey) (different : stored ≠ queried) :
    (seen.insert stored ()).contains queried = seen.contains queried := by
  rw [Std.HashMap.contains_insert]
  have miss : (stored == queried) = false := beq_eq_false_iff_ne.mpr different
  simp only [miss, Bool.false_or]

theorem insert_expression_collision (seen : Seen) (stored queried : PreseedKey)
    (different : stored.expr ≠ queried.expr) :
    (seen.insert stored ()).contains queried = seen.contains queried :=
  insert_other seen stored queried (fun same => different (congrArg PreseedKey.expr same))

theorem insert_context_collision (seen : Seen) (stored queried : PreseedKey)
    (different : stored.params ≠ queried.params) :
    (seen.insert stored ()).contains queried = seen.contains queried :=
  insert_other seen stored queried (fun same => different (congrArg PreseedKey.params same))

theorem insert_retains (seen : Seen) (stored queried : PreseedKey) (found : seen.contains queried = true) :
    (seen.insert stored ()).contains queried = true := by
  rw [Std.HashMap.contains_insert, found, Bool.or_true]

/-- The collector marks a parent before visiting its children. Restricting
coverage to smaller expressions permits these pending ancestors without
mistaking them for completed descendants. Bounds occur only in proofs. -/
def CoveredBelow (bound : Nat) (covered : PreseedKey → Prop) (seen : Seen) : Prop :=
  ∀ key, sizeOf key.expr < bound → seen.contains key = true → covered key

theorem CoveredBelow.empty (bound : Nat) (covered : PreseedKey → Prop) : CoveredBelow bound covered {} := by
  intro key _ found
  simp at found

theorem CoveredBelow.mono {bound : Nat} {first next : PreseedKey → Prop} {seen : Seen}
    (valid : CoveredBelow bound first seen) (growth : ∀ key, first key → next key) : CoveredBelow bound next seen :=
  fun key small found => growth key (valid key small found)

theorem CoveredBelow.restrict {before after : Nat} {covered : PreseedKey → Prop} {seen : Seen}
    (valid : CoveredBelow before covered seen) (bound : after ≤ before) : CoveredBelow after covered seen :=
  fun key small found => valid key (by omega) found

theorem CoveredBelow.insert {bound : Nat} {covered : PreseedKey → Prop} {seen : Seen}
    (valid : CoveredBelow bound covered seen) (key : PreseedKey)
    (ready : sizeOf key.expr < bound → covered key) : CoveredBelow bound covered (seen.insert key ()) := by
  intro query small found
  rw [Std.HashMap.contains_insert, Bool.or_eq_true] at found
  rcases found with same | prior
  · have same : key = query := eq_of_beq same
    subst query
    exact ready small
  · exact valid query small prior

theorem CoveredBelow.insert_above {bound : Nat} {covered : PreseedKey → Prop} {seen : Seen}
    (valid : CoveredBelow bound covered seen) (key : PreseedKey) (above : bound ≤ sizeOf key.expr) :
    CoveredBelow bound covered (seen.insert key ()) :=
  valid.insert key (fun small => by omega)

theorem CoveredBelow.lookup {covered : PreseedKey → Prop} {seen : Seen} (key : PreseedKey)
    (valid : CoveredBelow (sizeOf key.expr + 1) covered seen) (found : seen.contains key = true) : covered key :=
  valid key (by omega) found

theorem collect_hit (hint : Address) (mutualContext : Ix.MutCtx) (params : List Ix.Name) (source : Ix.Expr)
    (refs : Array Address) (univs : Array Ixon.Univ) (seen : Seen)
    (found : seen.contains ⟨source, params, hint⟩ = true) :
    collectExprTablesStructural hint mutualContext params source (refs, univs, seen) = pure (refs, univs, seen) := by
  rw [collectExprTablesStructural]
  simp only [found, ↓reduceIte]

end Ix.CompileCert.PreseedKeys
