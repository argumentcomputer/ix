import Std.Data.HashMap.Lemmas

/-! # Sound memo tables

`CacheSound meaning cache`: every entry of a hash-map memo means what its
key says (`meaning key value`). It is the one invariant behind the
compiler's memos in the proofs: the expression cache read back by the
certified reader (`Ix.CompileCert.ExpressionRead`), and, with lawful keys,
the canonical and raw universe memos.

Insertion keeps it only where the map's key comparison is lawful
(`CacheSound.insert`), or where `meaning` cannot tell apart keys the map
identifies (`CacheSound.insert_of_respects`). The compiler's `Ix.Expr` and
`Ix.Level` keys compare stored hash fields only, so for them insertion
needs exact keys (compiler queue CQ2.8); transport along a stronger
meaning (`CacheSound.mono`) needs nothing about the keys. -/

namespace Ix.CompileCert

/-- Every entry of `cache` satisfies `meaning`. -/
def CacheSound [BEq κ] [Hashable κ] (meaning : κ → α → Prop) (cache : Std.HashMap κ α) : Prop :=
  ∀ key value, cache.get? key = some value → meaning key value

theorem CacheSound.empty [BEq κ] [Hashable κ] (meaning : κ → α → Prop) :
    CacheSound meaning ({} : Std.HashMap κ α) := by
  intro key value found
  simp at found

theorem CacheSound.mono [BEq κ] [Hashable κ] {first second : κ → α → Prop}
    {cache : Std.HashMap κ α} (prior : CacheSound first cache)
    (preserves : ∀ key value, first key value → second key value) : CacheSound second cache :=
  fun key value found => preserves key value (prior key value found)

/-- Insertion under a key comparison that is an equivalence, of a value whose
meaning holds at every key the map identifies with the inserted one. -/
theorem CacheSound.insert_of_respects [BEq κ] [Hashable κ] [EquivBEq κ] [LawfulHashable κ]
    {meaning : κ → α → Prop} {cache : Std.HashMap κ α} (prior : CacheSound meaning cache)
    (key : κ) (value : α) (correct : ∀ query, (key == query) = true → meaning query value) :
    CacheSound meaning (cache.insert key value) := by
  intro query result found
  change (cache.insert key value)[query]? = some result at found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · rename_i same
    cases Option.some.inj found
    exact correct query same
  · exact prior query result found

/-- Insertion under lawful keys. -/
theorem CacheSound.insert [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
    {meaning : κ → α → Prop} {cache : Std.HashMap κ α} (prior : CacheSound meaning cache)
    (key : κ) (value : α) (correct : meaning key value) :
    CacheSound meaning (cache.insert key value) :=
  prior.insert_of_respects key value fun query same => by
    cases beq_iff_eq.mp same
    exact correct

end Ix.CompileCert
