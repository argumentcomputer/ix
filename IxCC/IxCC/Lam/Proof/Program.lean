import IxCC.Lam.Syntax

/-! # A Lam program's globals in order

`Program.globalList` lists each global `g < size` once, with its body. -/

set_option autoImplicit false

namespace IxCC.Lam.Program

theorem mem_globalList {P : Program} {g : GlobalId} {gl : Global} :
    (g, gl) ∈ P.globalList ↔ g < P.size ∧ P.global? g = some gl := by
  unfold globalList
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨g', hg', gl', hgl, rfl, rfl⟩
    exact ⟨hg', hgl⟩
  · rintro ⟨hg, hgl⟩
    exact ⟨g, hg, gl, hgl, rfl, rfl⟩

theorem globalList_pairwise (P : Program) : P.globalList.Pairwise fun p p' => p.1 < p'.1 := by
  unfold globalList
  refine List.Pairwise.filterMap _ (fun a a' h b hb b' hb' => ?_) List.pairwise_lt_range
  simp only [Option.map_eq_some_iff] at hb hb'
  obtain ⟨_, _, rfl⟩ := hb
  obtain ⟨_, _, rfl⟩ := hb'
  exact h

theorem globalList_keys_nodup (P : Program) : (P.globalList.map (·.1)).Nodup :=
  (List.pairwise_map.2 (globalList_pairwise P)).imp Nat.ne_of_lt

end IxCC.Lam.Program
