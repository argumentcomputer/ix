import Ix.Compile.ExactKey
import Std.Data.HashMap.Lemmas

/-! Storage laws for the production expression-cache key. These hold for an
arbitrary meaning predicate, without identifying terms by their digest.
The compiler's expression proof must establish each inserted value's meaning;
table-growth proofs must justify transporting that meaning to a larger state. -/

namespace Ix.CompileCert.ExpressionCache

open Ix.Compile.ExactKey

abbrev Cache (α : Type) := Std.HashMap ExprKey α

def Sound (meaning : Ix.Expr → α → Prop) (cache : Cache α) : Prop :=
  ∀ expr value, cache.get? ⟨expr⟩ = some value → meaning expr value

theorem lookup_insert (cache : Cache α) (source query : Ix.Expr) (value : α) :
    (cache.insert ⟨source⟩ value).get? ⟨query⟩ =
      if source = query then some value else cache.get? ⟨query⟩ := by
  change (cache.insert ⟨source⟩ value)[ExprKey.mk query]? = _
  simp only [Std.HashMap.getElem?_insert, beq_iff_eq, ExprKey.mk.injEq]
  rfl

theorem sound_empty (meaning : Ix.Expr → α → Prop) : Sound meaning {} := by
  intro expr value found
  simp at found

theorem Sound.insert {meaning : Ix.Expr → α → Prop} {cache : Cache α}
    (prior : Sound meaning cache) (expr : Ix.Expr) (value : α)
    (correct : meaning expr value) : Sound meaning (cache.insert ⟨expr⟩ value) := by
  intro query result found
  rw [lookup_insert] at found
  split at found
  · rename_i same
    subst query
    cases Option.some.inj found
    exact correct
  · exact prior query result found

theorem lookup_insert_other (cache : Cache α) {source query : Ix.Expr}
    (different : source ≠ query) (value : α) :
    (cache.insert ⟨source⟩ value).get? ⟨query⟩ = cache.get? ⟨query⟩ := by
  simp only [lookup_insert, different, ↓reduceIte]

theorem lookup_distinct_singleton {source query : Ix.Expr}
    (different : source ≠ query) (value : α) :
    (({} : Cache α).insert ⟨source⟩ value).get? ⟨query⟩ = none := by
  rw [lookup_insert_other _ different]
  simp

theorem Sound.mono {first second : Ix.Expr → α → Prop} {cache : Cache α}
    (prior : Sound first cache) (preserves : ∀ expr value, first expr value → second expr value) :
    Sound second cache := by
  intro expr value found
  exact preserves expr value (prior expr value found)

end Ix.CompileCert.ExpressionCache
