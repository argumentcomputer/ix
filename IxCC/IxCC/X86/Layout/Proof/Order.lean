import IxCC.X86.Layout.Order

/-!
# What `Order.check` guarantees (05 §7, step 2)

`Order.check` accepts an order exactly when its flattening is a
duplicate-free list of blocks of the program that contains the entry and
every reachable block, is closed under block targets (`placedClosed`), and
respects the groups (each group's list names only its blocks, a reachable
group entry first). `Order.check_sound` states these as propositions over
the flattened list, which is what linearisation renumbers by.
-/

namespace IxCC.X86.Layout.Proof

open IxCC.X86

/-! ## Sets built from lists -/

/-- The set of a list's elements. -/
def setOf (l : List Nat) : NatSet := l.foldl (fun acc b => acc.insert b) {}

theorem contains_foldl_insert :
    ∀ (l : List Nat) (acc : NatSet) (b : Nat),
      (l.foldl (fun acc b => acc.insert b) acc).contains b = true ↔ b ∈ l ∨ acc.contains b = true
  | [], acc, b => by simp
  | x :: xs, acc, b => by
      simp only [List.foldl_cons, List.mem_cons]
      rw [contains_foldl_insert xs (acc.insert x) b, Std.TreeSet.contains_insert]
      simp only [Bool.or_eq_true, beq_iff_eq, Nat.compare_eq_eq]
      constructor
      · rintro (h | h | h)
        · exact .inl (.inr h)
        · exact .inl (.inl h.symm)
        · exact .inr h
      · rintro ((h | h) | h)
        · exact .inr (.inl h.symm)
        · exact .inl h
        · exact .inr (.inr h)

theorem contains_setOf {l : List Nat} {b : Nat} : (setOf l).contains b = true ↔ b ∈ l := by
  rw [setOf, contains_foldl_insert]
  simp

theorem size_foldl_insert :
    ∀ (l : List Nat) (acc : NatSet),
      (l.foldl (fun acc b => acc.insert b) acc).size ≤ acc.size + l.length ∧
        ((l.foldl (fun acc b => acc.insert b) acc).size = acc.size + l.length →
          l.Nodup ∧ ∀ x ∈ l, acc.contains x = false)
  | [], acc => by simp
  | x :: xs, acc => by
      simp only [List.foldl_cons, List.length_cons, List.nodup_cons, List.mem_cons]
      obtain ⟨le, eq⟩ := size_foldl_insert xs (acc.insert x)
      have hsize := Std.TreeSet.size_insert (t := acc) (k := x)
      refine ⟨?_, ?_⟩
      · split at hsize <;> omega
      · intro equal
        have inserted : (acc.insert x).size = acc.size + 1 := by split at hsize <;> omega
        have fresh : acc.contains x = false := by
          cases hc : acc.contains x
          · rfl
          · rw [hc] at hsize
            simp only [ite_true] at hsize
            omega
        obtain ⟨nodup, disjoint⟩ := eq (by omega)
        have notIn : x ∉ xs := fun mem => by
          have := disjoint x mem
          rw [Std.TreeSet.contains_insert] at this
          simp at this
        refine ⟨⟨notIn, nodup⟩, ?_⟩
        rintro y (rfl | mem)
        · exact fresh
        · have := disjoint y mem
          rw [Std.TreeSet.contains_insert] at this
          simp only [Bool.or_eq_false_iff] at this
          exact this.2

theorem nodup_of_setOf_size {l : List Nat} (h : (setOf l).size = l.length) : l.Nodup :=
  ((size_foldl_insert l {}).2 (by simpa [setOf] using h)).1

/-! ## Soundness -/

/-- What an accepted order guarantees, over its flattening. -/
structure OrderSound (p : Program) (s : Shape) (o : Order) : Prop where
  groups : o.length = s.groups.length
  nodup : o.flatten.Nodup
  inRange : ∀ b ∈ o.flatten, b < p.blocks.size
  groupBlocks : ∀ g bs, (g, bs) ∈ s.groups.zip o → ∀ b ∈ bs, g.contains b = true
  groupEntry : ∀ g bs e, (g, bs) ∈ s.groups.zip o → g.entry = some e →
    (reachable p s.roots).contains e = true → bs.head? = some e
  reachable : ∀ b, (reachable p s.roots).contains b = true → b ∈ o.flatten
  entry : p.entry.toNat ∈ o.flatten
  closed : ∀ b ∈ o.flatten, ∀ blk, p.blocks[b]? = some blk → ∀ t ∈ blk.targets, t.toNat ∈ o.flatten

theorem Order.check_sound {p : Program} {s : Shape} {o : Order} (h : Order.check p s o = true) :
    OrderSound p s o := by
  simp only [Order.check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hgroups, hsize⟩, hrange⟩, hgroup⟩, hreach⟩, hentry⟩, hclosed⟩ := h
  have placed : ∀ b, (o.flatten.foldl (fun acc b => acc.insert b) ({} : NatSet)).contains b = true ↔
      b ∈ o.flatten := fun b => contains_setOf
  refine ⟨hgroups, nodup_of_setOf_size hsize, hrange, ?_, ?_, ?_, (placed _).1 hentry, ?_⟩
  · intro g bs member b hb
    exact (hgroup (g, bs) member).1 b hb
  · intro g bs e member he hseen
    have := (hgroup (g, bs) member).2
    simp only [he, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    rcases this with h | h
    · rw [hseen] at h
      cases h
    · exact h
  · intro b hb
    refine (placed b).1 (hreach b ?_)
    rw [Std.TreeSet.mem_toList]
    exact Std.TreeSet.mem_iff_contains.2 hb
  · intro b hb blk found t ht
    simp only [placedClosed, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hclosed
    have mem : (blk, b) ∈ p.blocks.toList.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      simpa using found
    rcases hclosed (blk, b) mem with h | h
    · rw [(placed b).2 hb] at h
      cases h
    · exact (placed _).1 (h t ht)

end IxCC.X86.Layout.Proof
