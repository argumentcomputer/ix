import Ix.Sharing.Exact.Dag

/-! Pointer-selected cache hits require exact source equality. These facts
hold for arbitrary address hints, including collisions. They supply the cache
boundary of ingestion; interner and whole-ingestion correctness remain separate. -/

namespace Ix.Sharing.Verify.ExprCache

open Ix.Sharing.Exact

def Sound (meaning : Ixon.Expr → α → Prop) (cache : ExprCache α) : Prop :=
  ∀ address source value, cache.entries.get? address = some (source, value) → meaning source value

theorem sound_empty (meaning : Ixon.Expr → α → Prop) : Sound meaning {} := by
  intro address source value found
  simp at found

theorem sound_insert {meaning : Ixon.Expr → α → Prop} {cache : ExprCache α} (sound : Sound meaning cache)
    (key : ExprCache.Key) (value : α) (correct : meaning key.source value) :
    Sound meaning (cache.insert key value) := by
  intro address source result found
  change (cache.entries.insert key.address (key.source, value))[address]? = some (source, result) at found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · cases Option.some.inj found
    exact correct
  · exact sound address source result found

theorem lookup_entry (cache : ExprCache α) (key : ExprCache.Key) (value : α)
    (found : cache.get? key = some value) : cache.entries.get? key.address = some (key.source, value) := by
  unfold Ix.Sharing.Exact.ExprCache.get? at found
  cases got : cache.entries.get? key.address with
  | none => simp only [got] at found; cases found
  | some entry =>
    rcases entry with ⟨source, actual⟩
    simp only [got] at found
    split at found
    · rename_i same
      cases Option.some.inj found
      rw [same]
    · cases found

theorem lookup_sound {meaning : Ixon.Expr → α → Prop} {cache : ExprCache α} (sound : Sound meaning cache)
    (key : ExprCache.Key) (value : α) (found : cache.get? key = some value) : meaning key.source value :=
  sound key.address key.source value (lookup_entry cache key value found)

theorem lookup_insert (cache : ExprCache α) (key : ExprCache.Key) (value : α) :
    (cache.insert key value).get? key = some value := by
  simp [Ix.Sharing.Exact.ExprCache.insert, Ix.Sharing.Exact.ExprCache.get?]

theorem collision_miss (cache : ExprCache α) (stored query : Ixon.Expr) (address : USize) (value : α)
    (different : query ≠ stored) :
    (cache.insert ⟨address, stored⟩ value).get? ⟨address, query⟩ = none := by
  simp [Ix.Sharing.Exact.ExprCache.insert, Ix.Sharing.Exact.ExprCache.get?, different]

theorem Sound.mono {first second : Ixon.Expr → α → Prop} {cache : ExprCache α}
    (sound : Sound first cache) (grows : ∀ source value, first source value → second source value) :
    Sound second cache := fun address source value found => grows source value (sound address source value found)

theorem ingestExpr_hit (limits : Limits) (context : ShareCtx) (depth : Nat) (source : Ixon.Expr)
    (before : IngestState) (id : Nat) (found : before.ptrCache.get? (exprKey source) = some id) :
    (ingestExpr limits context depth source).run before = .ok (id, before) := by
  rw [ingestExpr]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [found]
  rfl

theorem ingestExpr_hit_meaning (meaning : Ixon.Expr → Nat → Prop)
    (limits : Limits) (context : ShareCtx) (depth : Nat) (source : Ixon.Expr)
    (before : IngestState) (sound : Sound meaning before.ptrCache) (id : Nat)
    (found : before.ptrCache.get? (exprKey source) = some id) :
    (ingestExpr limits context depth source).run before = .ok (id, before) ∧ meaning source id :=
  ⟨ingestExpr_hit limits context depth source before id found, lookup_sound sound (exprKey source) id found⟩

end Ix.Sharing.Verify.ExprCache
