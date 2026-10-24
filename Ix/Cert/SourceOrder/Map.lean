module
public import Ix.Environment
import all Std.Data.HashMap.Basic
import all Std.Data.DHashMap.Basic
import all Std.Data.DHashMap.Raw
import all Std.Data.DHashMap.Internal.Defs
import all Std.Data.DHashMap.Internal.WF
import Batteries.Tactic.OpenPrivate

open private Std.DHashMap.Internal.Raw₀.expand.go from Std.Data.DHashMap.Internal.Defs

/-! Exact order for the concrete shared insertion trace. This intentionally
uses the pinned bucket/resize implementation, not HashMap.map or Equiv. -/
public section
namespace Ix.Cert.SourceOrder.Map
open Ix (Name ConstantInfo)
open Std.DHashMap.Internal

universe u
private abbrev Bucket (α : Type u) := AssocList Name (fun _ => α)
private abbrev Data (α : Type u) := { a : Array (Bucket α) // 0 < a.size }

private def forgetBucket : Bucket α → Bucket Unit
  | .nil => .nil
  | .cons k _ tail => .cons k () (forgetBucket tail)
private abbrev forgetData (a : Data α) : Data Unit :=
  ⟨a.1.map forgetBucket, by simpa using a.2⟩
private abbrev forget (m : Raw₀ Name (fun _ => α)) : Raw₀ Name (fun _ => Unit) :=
  ⟨⟨m.1.size, m.1.buckets.map forgetBucket⟩, by simpa using m.2⟩

private theorem contains_forget (b : Bucket α) (n : Name) :
    (forgetBucket b).contains n = b.contains n := by
  induction b with
  | nil => rfl
  | cons k v tail ih => simp only [forgetBucket, AssocList.contains, ih]

private theorem forget_replace (b : Bucket α) (n : Name) (v : α) :
    forgetBucket (b.replace n v) = (forgetBucket b).replace n () := by
  induction b with
  | nil => rfl
  | cons k x tail ih =>
    cases h : k == n <;> simp [AssocList.replace, forgetBucket, h, ih]

private theorem index_map (a : Array (Bucket α)) (h : 0 < a.size) (d : UInt64) :
    mkIdx (a.map forgetBucket).size (by simpa using h) d =
      ⟨(mkIdx a.size h d).1, by simpa using (mkIdx a.size h d).2⟩ := by
  apply Subtype.ext
  unfold mkIdx
  simp only [Array.size_map]

private theorem forget_reinsert (a : Data α) (n : Name) (v : α) :
    forgetData (Raw₀.reinsertAux hash a n v) = Raw₀.reinsertAux hash (forgetData a) n () := by
  obtain ⟨a, ha⟩ := a
  apply Subtype.ext
  simp only [Raw₀.reinsertAux, Array.uset_eq_set, Array.map_set, forgetBucket]
  rw [index_map a ha (hash n)]
  simp

private theorem forget_fold (b : Bucket α) (a : Data α) :
    forgetData (b.foldl (Raw₀.reinsertAux hash) a) =
      (forgetBucket b).foldl (Raw₀.reinsertAux hash) (forgetData a) := by
  induction b generalizing a with
  | nil => rfl
  | cons k v tail ih =>
    change forgetData (tail.foldl _ (Raw₀.reinsertAux hash a k v)) =
      (forgetBucket tail).foldl _ (Raw₀.reinsertAux hash (forgetData a) k ())
    rw [ih, forget_reinsert]

private theorem forget_expand_go (i : Nat) (source : Array (Bucket α)) (target : Data α) :
    forgetData (Raw₀.expand.go i source target) =
      Raw₀.expand.go i (source.map forgetBucket) (forgetData target) := by
  conv => lhs; rw [Raw₀.expand.go]
  conv => rhs; rw [Raw₀.expand.go]
  by_cases h : i < source.size
  · simp only [Array.size_map, h, dite_true, Array.getElem_map]
    have ih := forget_expand_go (i + 1) (source.set i .nil) (source[i].foldl (Raw₀.reinsertAux hash) target)
    simpa only [Array.map_set, forgetBucket, forget_fold] using ih
  · simp [h, Array.size_map]
termination_by source.size - i
decreasing_by simp_wf; omega

private theorem forget_expand (a : Data α) :
    forgetData (Raw₀.expand a) = Raw₀.expand (forgetData a) := by
  obtain ⟨a, ha⟩ := a
  simpa only [Raw₀.expand, forgetData, Array.size_map, Array.map_replicate, forgetBucket] using
    forget_expand_go 0 a ⟨Array.replicate (a.size * 2) .nil, by simpa using Nat.mul_pos ha Nat.two_pos⟩

private theorem forget_expandIf (m : Raw₀ Name (fun _ => α)) :
    forget (Raw₀.expandIfNecessary m) = Raw₀.expandIfNecessary (forget m) := by
  obtain ⟨⟨size, buckets⟩, positive⟩ := m
  unfold Raw₀.expandIfNecessary
  simp only [forget, Array.size_map]
  split
  · rfl
  · apply Subtype.ext
    have h := congrArg Subtype.val (forget_expand ⟨buckets, positive⟩)
    exact congrArg (fun b => Std.DHashMap.Raw.mk size b) h

private theorem forget_insert (m : Raw₀ Name (fun _ => α)) (n : Name) (v : α) :
    forget (Raw₀.insert m n v) = Raw₀.insert (forget m) n () := by
  obtain ⟨⟨size, buckets⟩, positive⟩ := m
  unfold Raw₀.insert
  simp only [forget]
  rw [index_map buckets positive (hash n)]
  simp only [Array.ugetElem_eq_getElem, Array.getElem_map, contains_forget]
  split
  · apply Subtype.ext
    simp [Array.uset_eq_set, forget_replace]
  · let i := mkIdx buckets.size positive (hash n)
    let updated : Raw₀ Name (fun _ => α) :=
      ⟨⟨size + 1, buckets.set i.1.toNat (.cons n v buckets[i.1.toNat])⟩, by simpa using positive⟩
    simpa only [updated, i, forget, Array.uset_eq_set, Array.map_set, forgetBucket] using
      forget_expandIf updated

private abbrev forgetMap (m : Std.HashMap Name α) : Raw₀ Name (fun _ => Unit) :=
  forget ⟨m.1.1, m.1.2.size_buckets_pos⟩

private theorem forgetMap_empty : forgetMap ({} : Std.HashMap Name α) = Raw₀.emptyWithCapacity := by
  change forget (Raw₀.emptyWithCapacity (β := fun _ : Name => α)) = _
  apply Subtype.ext
  simp [Raw₀.emptyWithCapacity, forgetBucket]

private theorem forgetMap_insert (m : Std.HashMap Name α) (n : Name) (v : α) :
    forgetMap (m.insert n v) = Raw₀.insert (forgetMap m) n () :=
  forget_insert ⟨m.1.1, m.1.2.size_buckets_pos⟩ n v

private theorem forgetBucket_keys (b : Bucket α) :
    (forgetBucket b).toList.map (·.1) = b.toList.map (·.1) := by
  induction b with
  | nil => rfl
  | cons k v tail ih => simp only [forgetBucket, AssocList.toList, List.map_cons, ih]

private theorem model_keys (bs : Array (Bucket α)) :
    (toListModel (bs.map forgetBucket)).map (·.1) = (toListModel bs).map (·.1) := by
  simp only [toListModel, Array.toList_map, List.flatMap_map, List.map_flatMap,
    forgetBucket_keys]

private theorem forgetMap_keys (m : Std.HashMap Name α) :
    (forgetMap m).1.toList.map (·.1) = m.toList.map (·.1) := by
  simp only [Std.HashMap.toList, Std.DHashMap.Const.toList,
    Std.DHashMap.Internal.Raw.Const.toList_eq_toListModel_map,
    Std.DHashMap.Internal.Raw.toList_eq_toListModel, List.map_map]
  exact model_keys m.1.1.buckets

private theorem forget_folded (xs : List (Name × α)) (f : α → β) :
    forgetMap (xs.foldl (fun m p => m.insert p.1 (f p.2)) ({} : Std.HashMap Name β)) =
      xs.foldl (fun m p => Raw₀.insert m p.1 ()) Raw₀.emptyWithCapacity := by
  rw [← List.foldl_hom forgetMap (g₂ := fun m (p : Name × α) => Raw₀.insert m p.1 ())
    (fun m p => (forgetMap_insert m p.1 (f p.2)).symm), forgetMap_empty]

/-- Same concrete insertion trace, including replacement and resize. This
is not an order statement for arbitrary equivalent maps or HashMap.map. -/
theorem inserted_keys (xs : List (Name × α)) (f : α → β) :
    (xs.foldl (fun m p => m.insert p.1 (f p.2)) ({} : Std.HashMap Name β)).toList.map (·.1) =
      (xs.foldl (fun m p => m.insert p.1 p.2) ({} : Std.HashMap Name α)).toList.map (·.1) := by
  rw [← forgetMap_keys, ← forgetMap_keys, forget_folded xs f]
  change _ = (forgetMap (xs.foldl (fun m p => m.insert p.1 (id p.2)) {})).1.toList.map (·.1)
  rw [forget_folded xs id]

end Ix.Cert.SourceOrder.Map
