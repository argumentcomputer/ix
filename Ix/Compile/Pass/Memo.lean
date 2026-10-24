/- # Pass 3: memo tables (one shape)

## Contract
A memo table maps a key to the value a pure computation gives it
(`compute : κ → Except String V`). `memoLookup` reads the table: a stored
value is returned (in check mode it is computed again and compared, and a
difference is an error), a missing one is computed. `memoMerge` admits new
entries, the first entry of a key winning.

## Shape (for the statements)
One invariant, `MemoSound table compute`: every stored value is the
computation's. Under it `memoLookup` is the computation (`memoLookup_eq`,
`memoLookup_eq_of_check`), and merging entries the computation agrees with
keeps it (`MemoSound.merge`). The keys are lawful (`LawfulBEq`, e.g.
`ExactKey.ExactName`), so a hit is the request itself, never a key that only
shares a digest.

## Faithfulness
A sound table changes no result: every lookup returns what the computation
returns.
-/
module
public import Std.Data.HashMap
public section

namespace Ix.Compile.Pass

variable {κ V : Type} [BEq κ] [Hashable κ]

/-- The value of `k`: the table's entry, else `compute ()`. With `check`, an
entry is computed again and must be `==` to the stored one; a difference is
an error prefixed by `what`. -/
def memoLookup [BEq V] (table : Std.HashMap κ V) (check : Bool) (what : String) (k : κ)
    (compute : Unit → Except String V) : Except String V :=
  match table[k]? with
  | some v =>
    if check then do
      let v' ← compute ()
      if v == v' then pure v else throw s!"{what}: the recomputed value differs from the table's"
    else pure v
  | none => compute ()

/-- Admit `entries` into `table`, the first entry of a key winning. -/
def memoMerge (table : Std.HashMap κ V) (entries : Array (κ × V)) : Std.HashMap κ V :=
  entries.foldl (fun t (k, v) => t.insertIfNew k v) table

/-- Every value the table stores is the computation's. -/
def MemoSound (table : Std.HashMap κ V) (compute : κ → Except String V) : Prop :=
  ∀ k v, table[k]? = some v → compute k = .ok v

theorem MemoSound.empty (compute : κ → Except String V) :
    MemoSound ({} : Std.HashMap κ V) compute := by
  intro k v h
  simp at h

/-- Outside check mode, a lookup in a sound table is the computation. -/
theorem memoLookup_eq [BEq V] {table : Std.HashMap κ V} {compute : κ → Except String V}
    (sound : MemoSound table compute) (what : String) (k : κ) :
    memoLookup table false what k (fun _ => compute k) = compute k := by
  unfold memoLookup
  split
  · next v hit => exact (sound k v hit).symm
  · rfl

/-- In check mode, a lookup in a sound table is the computation, for a
reflexive `==`. -/
theorem memoLookup_eq_of_check [BEq V] [ReflBEq V] {table : Std.HashMap κ V}
    {compute : κ → Except String V} (sound : MemoSound table compute) (what : String) (k : κ) :
    memoLookup table true what k (fun _ => compute k) = compute k := by
  unfold memoLookup
  split
  · next v hit =>
    rw [sound k v hit]
    simp [bind, Except.bind, pure, Except.pure]
  · rfl

theorem MemoSound.insertIfNew [LawfulBEq κ] [LawfulHashable κ] {table : Std.HashMap κ V}
    {compute : κ → Except String V} (sound : MemoSound table compute) {k : κ} {v : V}
    (agrees : compute k = .ok v) : MemoSound (table.insertIfNew k v) compute := by
  intro a w h
  rw [Std.HashMap.getElem?_insertIfNew] at h
  split at h
  · next cond =>
    obtain ⟨same, -⟩ := cond
    have equal : k = a := eq_of_beq same
    subst equal
    cases h
    exact agrees
  · exact sound a w h

/-- Merging entries the computation agrees with keeps the table sound. -/
theorem MemoSound.merge [LawfulBEq κ] [LawfulHashable κ] {table : Std.HashMap κ V}
    {compute : κ → Except String V} (sound : MemoSound table compute) (entries : Array (κ × V))
    (agree : ∀ e ∈ entries, compute e.1 = .ok e.2) :
    MemoSound (memoMerge table entries) compute := by
  unfold memoMerge
  rw [← Array.foldl_toList]
  have agree' : ∀ e ∈ entries.toList, compute e.1 = .ok e.2 := fun e he =>
    agree e (Array.mem_toList_iff.mp he)
  clear agree
  generalize entries.toList = es at agree'
  induction es generalizing table with
  | nil => exact sound
  | cons e rest ih =>
    simp only [List.foldl_cons]
    apply ih (sound.insertIfNew (agree' e List.mem_cons_self))
    intro x hx
    exact agree' x (List.mem_cons_of_mem _ hx)

end Ix.Compile.Pass

end
