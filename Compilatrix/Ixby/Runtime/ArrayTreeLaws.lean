import Compilatrix.Ixby.Runtime.ArrayTreeRepresentation

/-! Source array laws for slot replacement, prefix extension, and capacity
growth. These lift exact tree values to arbitrary source element relations. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees

open Ix.Ixby Representation

theorem Prefix.set {numbers : NumberLayout} {element : α → Value → Prop}
    {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix numbers element source height tree size)
    (index : Nat) (bounded : index < source.size) (item : α) (value : Value)
    (itemRep : element item value) :
    Prefix numbers element (source.set! index item) height (tree.set height index value) size := by
  refine ⟨by simpa [Array.size_set!] using represented.capacity,
    by simpa [Array.size_set!] using represented.sizeRep, ?_⟩
  intro query queryBound
  have queryBound' : query < source.size := by simpa [Array.size_set!] using queryBound
  rw [Tree.get_set height tree index query value (by have := represented.capacity; omega)
    (by have := represented.capacity; omega)]
  by_cases same : query = index
  · subst query
    exact ⟨value, by simp, by simpa [Array.set!_eq_setIfInBounds,
      Array.getElem_setIfInBounds, bounded] using itemRep⟩
  · obtain ⟨old, found, related⟩ := represented.elements query queryBound'
    have changed : (source.set! index item)[query]'queryBound = source[query] := by
      simpa only [Array.set!_eq_setIfInBounds] using
        (Array.getElem_setIfInBounds_ne (xs := source) (a := item) queryBound' (Ne.symm same))
    exact ⟨old, by simpa [same] using found, changed.symm ▸ related⟩

theorem Prefix.grow {numbers : NumberLayout} {element : α → Value → Prop}
    {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix numbers element source height tree size) :
    Prefix numbers element source (height + 1) (.node tree (.empty height)) size := by
  refine ⟨?_, represented.sizeRep, ?_⟩
  · have := represented.capacity
    rw [Nat.pow_succ]; omega
  · intro index bounded
    have inside : index < 2 ^ height := by have := represented.capacity; omega
    simpa [Tree.get, inside] using represented.elements index bounded

theorem Prefix.push {numbers : NumberLayout} {element : α → Value → Prop}
    {source : Array α} {height : Nat} {tree : Tree height} {size : Value}
    (represented : Prefix numbers element source height tree size)
    (space : source.size < 2 ^ height) (item : α) (value nextSize : Value)
    (itemRep : element item value) (nextRep : Number numbers (source.size + 1) nextSize) :
    Prefix numbers element (source.push item) height (tree.set height source.size value) nextSize := by
  refine ⟨by simp; omega, by simpa using nextRep, ?_⟩
  intro query bounded
  have queryBound : query < source.size + 1 := by simpa using bounded
  rw [Tree.get_set height tree source.size query value space (by omega)]
  by_cases last : query = source.size
  · subst query
    exact ⟨value, by simp, by simpa using itemRep⟩
  · have before : query < source.size := by omega
    obtain ⟨old, found, related⟩ := represented.elements query before
    exact ⟨old, by simpa [last] using found, by simpa [Array.getElem_push, before] using related⟩

end Compilatrix.Ixby.Runtime.ArrayTrees
