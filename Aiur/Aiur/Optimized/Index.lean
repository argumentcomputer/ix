import Std.Data.HashMap.Lemmas

namespace Aiur.Optimized.Index

/-- Preserve source order within each natural-number key. Keys describe
compiler metadata, so indexing requires no hashing or ordering on the field. -/
def build (key : α → Nat) (items : List α) : Std.HashMap Nat (List α) :=
  items.foldr (fun item buckets =>
    buckets.insert (key item) (item :: buckets.getD (key item) [])) {}

/-- An index lookup returns exactly the corresponding subsequence. -/
theorem getD_build (key : α → Nat) (items : List α) (id : Nat) :
    (build key items).getD id [] = items.filter (fun item => key item == id) := by
  induction items with
  | nil => simp [build]
  | cons item items ih =>
    simp only [build] at ih
    simp only [build, List.foldr_cons, Std.HashMap.getD_insert]
    by_cases same : key item = id
    · simp [same, ih]
    · simp [same, ih]

@[simp] theorem mem_build (key : α → Nat) (items : List α) (item : α) :
    item ∈ (build key items).getD (key item) [] ↔ item ∈ items := by
  simp [getD_build]

end Aiur.Optimized.Index
