import IxVMRefinement.L1.ConvertExpr

/-! # Exact binder-tree contents and lookup

The tree records the serialized keys and node lists. Its lookup models the source comparison
exactly, including the source's kind-field branch. No sorting or unique-key premise is needed
to establish the result of a successful lookup in this particular tree.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Deserialize
open IxVM.Refinement.Obs

abbrev BinderKey := F × F × F

def binderKeyCompare (a b : BinderKey) : F :=
  if a.1 = b.1 then
    if a.2.1 = b.2.1 then (if a.2.2.val < b.2.2.val then 1 else 0)
    else (if a.2.1.val < b.2.1.val then 1 else 0)
  else b.1

/-- The comparison result, as well as heap preservation, is determined by the input keys. -/
theorem binder_key_lt_exact_spec {a b : BinderKey} {r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "Convert::binder_key_lt"
      [.field a.1, .field a.2.1, .field a.2.2, .field b.1, .field b.2.1, .field b.2.2]
      h r h' calls) : h' = h ∧ r = .field (binderKeyCompare a b) := by
  rcases «Convert::binder_key_lt».obs ev with
    ⟨_, op17, op40, ev52, _⟩ | ⟨v24, _, op17, op40, hne70, ev79, _⟩ |
    ⟨v1, op17, hne97, hr, hh, _⟩
  · have he : a.1 = b.1 := sub_eq_zero.mp (by
      simpa only [evalBinOp, Except.ok.injEq, Value.field.injEq] using op17)
    have hi : a.2.1 = b.2.1 := sub_eq_zero.mp (by
      simpa only [evalBinOp, Except.ok.injEq, Value.field.injEq] using op40)
    obtain ⟨va, vb, hva, hvb, _, _, result, heap⟩ := Lib.less_than_fields_spec ev52
    have hva' := Value.field.inj hva
    have hvb' := Value.field.inj hvb
    subst va vb
    exact ⟨heap, by simpa only [binderKeyCompare, he, hi, ↓reduceIte] using result⟩
  · have he : a.1 = b.1 := sub_eq_zero.mp (by
      simpa only [evalBinOp, Except.ok.injEq, Value.field.injEq] using op17)
    have hi : a.2.1 ≠ b.2.1 := by
      intro equal
      apply hne70
      simpa only [equal, evalBinOp, sub_self, Except.ok.injEq] using op40.symm
    obtain ⟨va, vb, hva, hvb, _, _, result, heap⟩ := Lib.less_than_fields_spec ev79
    have hva' := Value.field.inj hva
    have hvb' := Value.field.inj hvb
    subst va vb
    exact ⟨heap, by simpa only [binderKeyCompare, he, hi, ↓reduceIte] using result⟩
  · have he : a.1 ≠ b.1 := by
      intro equal
      apply hne97
      simpa only [equal, evalBinOp, sub_self, Except.ok.injEq] using op17.symm
    exact ⟨hh, by simpa only [binderKeyCompare, he, ↓reduceIte] using hr⟩

inductive BinderTreeData where
  | empty
  | leaf (key : BinderKey) (nodes : List Ixon.BinderNode)
  | node (key : BinderKey) (left right : BinderTreeData)

def BinderTreeData.lookup : BinderTreeData → BinderKey → Option (List Ixon.BinderNode)
  | .empty, _ => none
  | .leaf key nodes, query => if query = key then some nodes else none
  | .node key left right, query =>
    let compared := binderKeyCompare query key
    if compared = 1 then left.lookup query
    else if compared = 0 then right.lookup query else none

/-- Exact key and node-list contents of a heap binder tree. -/
inductive RepBinderTreeData (h : Heap F) : BinderTreeData → SourceValue F → Prop where
  | empty {addr : Nat} (cell : h[addr]? = some (.construct binderTreeEnum "Empty" [])) :
      RepBinderTreeData h .empty (.ptr (.enum binderTreeEnum) addr)
  | leaf {addr : Nat} {key : BinderKey} {nodes : List Ixon.BinderNode} {ptr : SourceValue F}
      (cell : h[addr]? = some (.construct binderTreeEnum "Leaf"
        [.field key.1, .field key.2.1, .field key.2.2, ptr]))
      (values : RepList binderNodeListEnum RepBinderNode h nodes ptr) :
      RepBinderTreeData h (.leaf key nodes) (.ptr (.enum binderTreeEnum) addr)
  | node {addr : Nat} {key : BinderKey} {left right : BinderTreeData}
      {leftPtr rightPtr : SourceValue F}
      (cell : h[addr]? = some (.construct binderTreeEnum "Node"
        [.field key.1, .field key.2.1, .field key.2.2, leftPtr, rightPtr]))
      (leftRep : RepBinderTreeData h left leftPtr) (rightRep : RepBinderTreeData h right rightPtr) :
      RepBinderTreeData h (.node key left right) (.ptr (.enum binderTreeEnum) addr)

theorem RepBinderTreeData.mono {h h' : Heap F} {tree : BinderTreeData} {ptr : SourceValue F}
    (extended : Heap.Extends h h') (rep : RepBinderTreeData h tree ptr) :
    RepBinderTreeData h' tree ptr := by
  induction rep with
  | empty cell => exact .empty (extended.getElem?_eq cell)
  | leaf cell values => exact .leaf (extended.getElem?_eq cell)
      (repList_heapMono₂ _ repBinderNode_heapMono₂ extended values)
  | node cell _ _ left right => exact .node (extended.getElem?_eq cell) left right

/-- A successful lookup returns the exact node list specified by the represented tree. -/
theorem binder_nodes_exact_spec {tree : BinderTreeData} {ptr : SourceValue F} {h : Heap F}
    (rep : RepBinderTreeData h tree ptr) :
    ∀ {query : BinderKey} {result : SourceValue F} {h' : Heap F} {calls : List (Call F)},
      ObsFn W "Convert::binder_nodes"
        [ptr, .field query.1, .field query.2.1, .field query.2.2] h result h' calls →
      h' = h ∧ ∃ nodes, tree.lookup query = some nodes ∧
        RepList binderNodeListEnum RepBinderNode h nodes result := by
  induction rep with
  | empty cell =>
    intro query result h' calls ev
    rcases «Convert::binder_nodes».obs ev with
      ⟨_, _, _, _, loaded, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, loaded, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, loaded, _, _, _⟩
    all_goals exact (Core.load_cell_ne cell loaded (by decide)).elim
  | @leaf addr key nodes nodePtr cell values =>
    intro query result h' calls ev
    rcases «Convert::binder_nodes».obs ev with
      ⟨_, _, _, _, loaded, he, hi, hv, resultEq, heapEq, _⟩ |
      ⟨_, _, _, _, _, _, _, _, loaded, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, loaded, _, _, _⟩
    · have fields := (Core.load_cell cell loaded).2
      simp only [List.cons.injEq, and_true] at fields
      obtain ⟨rfl, rfl, rfl, rfl⟩ := fields
      subst resultEq
      have same : query = key := Prod.ext (Value.field.inj he).symm
        (Prod.ext (Value.field.inj hi).symm (Value.field.inj hv).symm)
      exact ⟨heapEq, nodes, by simp only [BinderTreeData.lookup, same, ↓reduceIte], values⟩
    all_goals exact (Core.load_cell_ne cell loaded (by decide)).elim
  | @node addr key left right leftPtr rightPtr cell _ _ ihLeft ihRight =>
    intro query result h' calls ev
    rcases «Convert::binder_nodes».obs ev with
      ⟨_, _, _, _, loaded, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, middle, _, _, loaded, comparison, rest, _⟩ |
      ⟨_, _, _, _, _, middle, _, _, loaded, comparison, rest, _⟩
    · exact (Core.load_cell_ne cell loaded (by decide)).elim
    · have fields := (Core.load_cell cell loaded).2
      simp only [List.cons.injEq, and_true] at fields
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := fields
      obtain ⟨heapEq, compared⟩ := binder_key_lt_exact_spec comparison
      subst middle
      have compared : binderKeyCompare query key = 1 := (Value.field.inj compared).symm
      obtain ⟨heapEq, nodes, found, values⟩ := ihLeft rest
      exact ⟨heapEq, nodes, by simpa only [BinderTreeData.lookup, compared, ↓reduceIte] using found, values⟩
    · have fields := (Core.load_cell cell loaded).2
      simp only [List.cons.injEq, and_true] at fields
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := fields
      obtain ⟨heapEq, compared⟩ := binder_key_lt_exact_spec comparison
      subst middle
      have compared : binderKeyCompare query key = 0 := (Value.field.inj compared).symm
      obtain ⟨heapEq, nodes, found, values⟩ := ihRight rest
      exact ⟨heapEq, nodes, by simpa only [BinderTreeData.lookup, compared, zero_ne_one, ↓reduceIte] using found, values⟩

end IxVM.Refinement.L1
