import IxVMRefinement.L1.BinderData

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

/-- A mode's serialized field identifies its exact mode. -/
theorem allMode_field_inj {left right : Ixon.AllMode}
    (same : (left.toCode.toNat : F) = (right.toCode.toNat : F)) : left = right := by
  have leftBound := left.toCode.toNat_lt
  have rightBound := right.toCode.toNat_lt
  have codes : left.toCode = right.toCode := UInt8.ext
    ((natCast_eq_iff (by omega) (by omega)).mp same)
  have decoded := congrArg Ixon.AllMode.ofCode? codes
  simpa using decoded

/-- Decoding a represented binder node is independent of its derivation. -/
theorem repBinderNode_unique {h : Heap F} {left right : Ixon.BinderNode}
    {leftValue rightValue : SourceValue F}
    (first : RepBinderNode h left leftValue) (second : RepBinderNode h right rightValue)
    (same : leftValue = rightValue) : left = right := by
  cases first with
  | never mode =>
    cases second with
    | never other =>
      exact congrArg Ixon.BinderNode.never (allMode_field_inj (by simpa using same))
    | zero _ | ifAllZero _ _ | share _ | undecided _ => simp at same
  | zero mode =>
    cases second with
    | zero other =>
      exact congrArg Ixon.BinderNode.zero (allMode_field_inj (by simpa using same))
    | never _ | ifAllZero _ _ | share _ | undecided _ => simp at same
  | ifAllZero mode params =>
    cases second with
    | ifAllZero other otherParams =>
      have fields := same
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at fields
      obtain ⟨rfl, modeEq⟩ := fields
      have modes := allMode_field_inj (Value.field.inj modeEq)
      cases modes
      have lists := repList_u64_unique params otherParams
      cases lists
      rfl
    | never _ | zero _ | share _ | undecided _ => simp at same
  | share variant =>
    cases second with
    | share other =>
      apply congrArg Ixon.BinderNode.share
      apply u64Value_inj
      simpa only [Value.construct.injEq, List.cons.injEq, true_and, and_true] using same
    | never _ | zero _ | ifAllZero _ _ | undecided _ => simp at same
  | undecided mode =>
    cases second with
    | undecided other =>
      exact congrArg Ixon.BinderNode.undecided (allMode_field_inj (by simpa using same))
    | never _ | zero _ | ifAllZero _ _ | share _ => simp at same

theorem repBinderNodes_unique {h : Heap F} {left right : List Ixon.BinderNode}
    {ptr : SourceValue F}
    (first : RepList binderNodeListEnum RepBinderNode h left ptr)
    (second : RepList binderNodeListEnum RepBinderNode h right ptr) : left = right :=
  repList_inj (fun a b => repBinderNode_unique a b rfl) first second

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
  | leaf cell values =>
      exact .leaf (extended.getElem?_eq cell)
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

abbrev BinderTreeEntryData := BinderKey × BinderTreeData

def binderBlockKey (block : Ixon.BinderBlock) : BinderKey :=
  (((if block.shared then 1 else 0 : Nat) : F), (block.index.toNat : F), (block.variant.toNat : F))

def binderLeavesData (blocks : List Ixon.BinderBlock) : List BinderTreeEntryData :=
  blocks.map fun block => (binderBlockKey block, .leaf (binderBlockKey block) block.nodes.toList)

def binderPairsData : List BinderTreeEntryData → List BinderTreeEntryData
  | [] => []
  | [entry] => [entry]
  | first :: second :: rest =>
    (first.1, .node second.1 first.2 second.2) :: binderPairsData rest

/-- The source's repeated adjacent pairing, expressed without a fuel-dependent output. -/
inductive BinderTreeBuilt : List BinderTreeEntryData → BinderTreeData → Prop where
  | empty : BinderTreeBuilt [] .empty
  | single (entry : BinderTreeEntryData) : BinderTreeBuilt [entry] entry.2
  | pair {first second : BinderTreeEntryData} {rest : List BinderTreeEntryData}
      {tree : BinderTreeData}
      (built : BinderTreeBuilt (binderPairsData (first :: second :: rest)) tree) :
      BinderTreeBuilt (first :: second :: rest) tree

theorem BinderTreeBuilt.unique {entries : List BinderTreeEntryData} {left right : BinderTreeData}
    (first : BinderTreeBuilt entries left) (second : BinderTreeBuilt entries right) : left = right := by
  induction first generalizing right with
  | empty => cases second; rfl
  | single entry => cases second; rfl
  | pair built ih => cases second with | pair other => exact ih other

def RepBinderTreeDataEntry (h : Heap F) (entry : BinderTreeEntryData) (value : SourceValue F) : Prop :=
  ∃ ptr, value = .tuple [.field entry.1.1, .field entry.1.2.1, .field entry.1.2.2, ptr] ∧
    RepBinderTreeData h entry.2 ptr

theorem repBinderTreeDataEntry_heapMono₂ : HeapMono₂ RepBinderTreeDataEntry := by
  intro h h' entry value extended rep
  obtain ⟨ptr, same, tree⟩ := rep
  exact ⟨ptr, same, tree.mono extended⟩

/-- Leaf construction preserves the complete ordered list of serialized keys and nodes. -/
theorem binder_leaves_data_spec {blocks : List Ixon.BinderBlock} :
    ∀ {blocksPtr result : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      RepList binderBlockListEnum RepBinderBlock h blocks blocksPtr →
      ObsFn W "Convert::binder_leaves" [blocksPtr] h result h' calls →
      Heap.Extends h h' ∧
        RepList binderPairListEnum RepBinderTreeDataEntry h' (binderLeavesData blocks) result := by
  induction blocks with
  | nil =>
    intro blocksPtr result h h' calls blocksRep ev
    rw [binderBlockListEnum_eq] at blocksRep
    rcases «Convert::binder_leaves».obs ev with
      ⟨_, he24, hm23, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, Lib.rep_store_nil _⟩
    · exact absurd rfl (repList_ne_nil_of_load_cons blocksRep ld12)
  | cons block rest ih =>
    intro blocksPtr result h h' calls blocksRep ev
    rw [binderBlockListEnum_eq] at blocksRep
    rcases «Convert::binder_leaves».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨x_rest, x_ekind, x_eidx, x_variant, x_nodes, v78, m79, _, v100, m101, _, v131, m166,
        m211, _, ld12, ev91, ev113, he126, hm125, hm174, ev221, _⟩
    · have empty := repList_nil_of_load blocksRep ld12
      simp at empty
    · obtain ⟨block', rest', same, blockRep, restRep⟩ := Core.RepList.cons_of_load blocksRep ld12
      cases same
      obtain ⟨nodesPtr, blockEq, nodesRep⟩ := blockRep
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at blockEq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := blockEq
      obtain ⟨_, hv78, hm79⟩ := Lib.u64_to_field_spec
        (Deserialize.repU64_u64Value h block.index) ev91
      subst v78 m79
      obtain ⟨_, hv100, hm101⟩ := Lib.u64_to_field_spec
        (Deserialize.repU64_u64Value h block.variant) ev113
      subst v100 m101
      have extLeaf : Heap.Extends h m166 := by rw [hm174]; exact Heap.Extends.snoc _ _
      have leaf : RepBinderTreeData m166 (.leaf (binderBlockKey block) block.nodes.toList)
          (.ptr (.enum binderTreeEnum) h.length) := by
        rw [hm174]
        exact .leaf (by simp [binderBlockKey])
          (repList_heapMono₂ _ repBinderNode_heapMono₂ (Heap.Extends.snoc _ _) nodesRep)
      rw [← binderBlockListEnum_eq] at restRep
      obtain ⟨extRest, tailRep⟩ := ih
        (repList_heapMono₂ _ repBinderBlock_heapMono₂ extLeaf restRep) ev221
      subst result h'
      have extCons := Heap.Extends.snoc m211
        (.construct binderPairListEnum "Cons"
          [.tuple [.field ((if block.shared then 1 else 0 : Nat) : F),
              .field (block.index.toNat : F), .field (block.variant.toNat : F),
              .ptr (.enum binderTreeEnum) h.length], v131])
      refine ⟨(extLeaf.trans extRest).trans extCons, ?_⟩
      exact Lib.rep_store_cons repBinderTreeDataEntry_heapMono₂
        ⟨_, rfl, leaf.mono extRest⟩ tailRep

private theorem binder_pairs_data_go (fuel : Nat) :
    ∀ {entries : List BinderTreeEntryData} {ptr result : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      entries.length ≤ fuel →
      RepList binderPairListEnum RepBinderTreeDataEntry h entries ptr →
      ObsFn W "Convert::binder_pairs" [ptr] h result h' calls →
      Heap.Extends h h' ∧
        RepList binderPairListEnum RepBinderTreeDataEntry h' (binderPairsData entries) result := by
  induction fuel with
  | zero =>
    intro entries ptr result h h' calls lengthBound entriesRep ev
    have empty : entries = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst empty
    rcases «Convert::binder_pairs».obs ev with
      ⟨_, he24, hm23, _⟩ | ⟨_, _, loaded, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, loaded, _, _, _, _, _, _⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, Lib.rep_store_nil _⟩
    all_goals exact absurd rfl (repList_ne_nil_of_load_cons entriesRep loaded)
  | succ fuel ih =>
    intro entries ptr result h h' calls lengthBound entriesRep ev
    rcases «Convert::binder_pairs».obs ev with
      ⟨loaded, he24, hm23, _⟩ |
      ⟨x_x, x_rest, loaded, restLoaded, he66, he67, _⟩ |
      ⟨x_rest, x_rest2, x_e1, x_i1, x_v1, x_t1, x_e2, x_i2, x_v2, x_t2, v159, m194, m247, _,
        ld12, ld57, he154, hm153, hm202, ev257, _⟩
    · have empty := Lib.rep_nil_of_load entriesRep loaded
      subst empty
      subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, Lib.rep_store_nil _⟩
    · obtain ⟨entry, rest, same, _, restRep⟩ := Core.RepList.cons_of_load entriesRep loaded
      cases same
      have empty := Lib.rep_nil_of_load restRep restLoaded
      subst empty
      subst he66 he67
      exact ⟨Heap.Extends.refl _, entriesRep⟩
    · obtain ⟨first, rest, rfl, firstRep, restRep⟩ := Core.RepList.cons_of_load entriesRep ld12
      obtain ⟨second, tail, rfl, secondRep, tailRep⟩ := Core.RepList.cons_of_load restRep ld57
      obtain ⟨_, firstEq, firstTree⟩ := firstRep
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at firstEq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := firstEq
      obtain ⟨_, secondEq, secondTree⟩ := secondRep
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at secondEq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := secondEq
      have extNode : Heap.Extends h m194 := by rw [hm202]; exact Heap.Extends.snoc _ _
      have node : RepBinderTreeData m194 (.node second.1 first.2 second.2)
          (.ptr (.enum binderTreeEnum) h.length) := by
        rw [hm202]
        exact .node (by simp)
          (firstTree.mono (Heap.Extends.snoc _ _)) (secondTree.mono (Heap.Extends.snoc _ _))
      simp only [List.length_cons] at lengthBound
      obtain ⟨extRest, tailResult⟩ := ih (by omega)
        (repList_heapMono₂ _ repBinderTreeDataEntry_heapMono₂ extNode tailRep) ev257
      subst result h'
      have extCons := Heap.Extends.snoc m247
        (.construct binderPairListEnum "Cons"
          [.tuple [.field first.1.1, .field first.1.2.1, .field first.1.2.2,
            .ptr (.enum binderTreeEnum) h.length], v159])
      refine ⟨(extNode.trans extRest).trans extCons, ?_⟩
      exact Lib.rep_store_cons repBinderTreeDataEntry_heapMono₂
        ⟨_, rfl, node.mono extRest⟩ tailResult

/-- Adjacent pairing preserves the exact data carried by every subtree. -/
theorem binder_pairs_data_spec {entries : List BinderTreeEntryData} {ptr result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (entriesRep : RepList binderPairListEnum RepBinderTreeDataEntry h entries ptr)
    (ev : ObsFn W "Convert::binder_pairs" [ptr] h result h' calls) :
    Heap.Extends h h' ∧
      RepList binderPairListEnum RepBinderTreeDataEntry h' (binderPairsData entries) result :=
  binder_pairs_data_go entries.length (Nat.le_refl _) entriesRep ev

private theorem binder_tree_of_data_go (fuel : Nat) :
    ∀ {entries : List BinderTreeEntryData} {ptr result : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ fuel →
      RepList binderPairListEnum RepBinderTreeDataEntry h entries ptr →
      ObsFn W "Convert::binder_tree_of" [ptr] h result h' calls →
      Heap.Extends h h' ∧ ∃ tree, BinderTreeBuilt entries tree ∧ RepBinderTreeData h' tree result := by
  induction fuel with
  | zero =>
    intro entries ptr result h h' calls lengthBound entriesRep ev
    rcases «Convert::binder_tree_of».obs ev with
      ⟨loaded, he24, hm23, _⟩ |
      ⟨_, _, _, _, x_t, loaded, restLoaded, he101, he102, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc135⟩
    · have empty := Lib.rep_nil_of_load entriesRep loaded
      subst empty
      subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, .empty, .empty, .empty (by simp)⟩
    · obtain ⟨entry, rest, same, headRep, restRep⟩ := Core.RepList.cons_of_load entriesRep loaded
      cases same
      have empty := Lib.rep_nil_of_load restRep restLoaded
      subst empty
      obtain ⟨_, tupleEq, treeRep⟩ := headRep
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at tupleEq
      obtain ⟨_, _, _, rfl⟩ := tupleEq
      subst he101 he102
      exact ⟨Heap.Extends.refl _, entry.2, .single entry, treeRep⟩
    · rw [hc135] at lengthBound
      simp at lengthBound
  | succ fuel ih =>
    intro entries ptr result h h' calls lengthBound entriesRep ev
    rcases «Convert::binder_tree_of».obs ev with
      ⟨loaded, he24, hm23, _⟩ |
      ⟨_, _, _, _, x_t, loaded, restLoaded, he101, he102, _⟩ |
      ⟨x_x, x_rest, v45, cs111, v114, m116, cs124, loaded, restLoaded, nonempty, ev126, ev113, hc135⟩
    · have empty := Lib.rep_nil_of_load entriesRep loaded
      subst empty
      subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, .empty, .empty, .empty (by simp)⟩
    · obtain ⟨entry, rest, same, headRep, restRep⟩ := Core.RepList.cons_of_load entriesRep loaded
      cases same
      have empty := Lib.rep_nil_of_load restRep restLoaded
      subst empty
      obtain ⟨_, tupleEq, treeRep⟩ := headRep
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at tupleEq
      obtain ⟨_, _, _, rfl⟩ := tupleEq
      subst he101 he102
      exact ⟨Heap.Extends.refl _, entry.2, .single entry, treeRep⟩
    · obtain ⟨entry, rest, same, _, restRep⟩ := Core.RepList.cons_of_load entriesRep loaded
      cases same
      cases rest with
      | nil =>
        cases restRep with
        | nil cell =>
          have valueEq := Except.ok.inj ((Lib.load_enum_cell cell).symm.trans restLoaded)
          exact False.elim (nonempty [] rfl valueEq.symm)
      | cons next tail =>
        obtain ⟨extPairs, paired⟩ := binder_pairs_data_spec entriesRep ev126
        have shorter : cs111.length ≤ fuel := by
          rw [hc135] at lengthBound
          simp only [List.length_cons, List.length_append] at lengthBound
          omega
        obtain ⟨extTree, tree, built, represented⟩ := ih shorter paired ev113
        exact ⟨extPairs.trans extTree, tree, .pair built, represented⟩

/-- The complete table construction retains a pure tree built from the actual serialized blocks. -/
theorem binder_table_data_spec {blocks : List Ixon.BinderBlock} {ptr result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (blocksRep : RepList binderBlockListEnum RepBinderBlock h blocks ptr)
    (ev : ObsFn W "Convert::binder_table" [ptr] h result h' calls) :
    Heap.Extends h h' ∧ ∃ tree, BinderTreeBuilt (binderLeavesData blocks) tree ∧
      RepBinderTreeData h' tree result := by
  obtain ⟨cs4, v7, m9, _, leavesRun, treeRun, _⟩ := «Convert::binder_table».obs ev
  obtain ⟨extLeaves, leaves⟩ := binder_leaves_data_spec blocksRep leavesRun
  obtain ⟨extTree, tree, built, treeRep⟩ :=
    binder_tree_of_data_go cs4.length (Nat.le_refl _) leaves treeRun
  exact ⟨extLeaves.trans extTree, tree, built, treeRep⟩

/-- Two successful lookups in tables built from the same serialized blocks read the same
node list, even when their heap addresses differ. -/
theorem binder_nodes_same_blocks {blocks : List Ixon.BinderBlock} {query : BinderKey}
    {blocks₁ blocks₂ tree₁ tree₂ nodes₁ nodes₂ : SourceValue F}
    {h₁ h₂ h₁' h₂' h₁'' h₂'' : Heap F} {calls₁ calls₂ lookups₁ lookups₂ : List (Call F)}
    (blocksRep₁ : RepList binderBlockListEnum RepBinderBlock h₁ blocks blocks₁)
    (blocksRep₂ : RepList binderBlockListEnum RepBinderBlock h₂ blocks blocks₂)
    (built₁ : ObsFn W "Convert::binder_table" [blocks₁] h₁ tree₁ h₁' calls₁)
    (built₂ : ObsFn W "Convert::binder_table" [blocks₂] h₂ tree₂ h₂' calls₂)
    (lookup₁ : ObsFn W "Convert::binder_nodes"
      [tree₁, .field query.1, .field query.2.1, .field query.2.2] h₁' nodes₁ h₁'' lookups₁)
    (lookup₂ : ObsFn W "Convert::binder_nodes"
      [tree₂, .field query.1, .field query.2.1, .field query.2.2] h₂' nodes₂ h₂'' lookups₂) :
    ∃ nodes, RepList binderNodeListEnum RepBinderNode h₁'' nodes nodes₁ ∧
      RepList binderNodeListEnum RepBinderNode h₂'' nodes nodes₂ := by
  obtain ⟨_, treeA, dataA, repA⟩ := binder_table_data_spec blocksRep₁ built₁
  obtain ⟨_, treeB, dataB, repB⟩ := binder_table_data_spec blocksRep₂ built₂
  obtain rfl := dataA.unique dataB
  obtain ⟨rfl, nodesA, foundA, valuesA⟩ := binder_nodes_exact_spec repA lookup₁
  obtain ⟨rfl, nodesB, foundB, valuesB⟩ := binder_nodes_exact_spec repB lookup₂
  rw [foundA] at foundB
  injection foundB with same
  subst nodesB
  exact ⟨nodesA, valuesA, valuesB⟩

/-- A property of every serialized node retained by a tree. -/
def BinderTreeData.AllNodes (property : Ixon.BinderNode → Prop) : BinderTreeData → Prop
  | .empty => True
  | .leaf _ nodes => ∀ node ∈ nodes, property node
  | .node _ left right => left.AllNodes property ∧ right.AllNodes property

theorem BinderTreeData.lookup_all {property : Ixon.BinderNode → Prop}
    {tree : BinderTreeData} {query : BinderKey} {nodes : List Ixon.BinderNode}
    (all : tree.AllNodes property) (found : tree.lookup query = some nodes) :
    ∀ node ∈ nodes, property node := by
  induction tree with
  | empty => cases found
  | leaf key values =>
    simp only [lookup] at found
    split at found
    · injection found with same
      subst nodes
      exact all
    · cases found
  | node key left right ihLeft ihRight =>
    simp only [lookup] at found
    split at found
    · exact ihLeft all.1 found
    · split at found
      · exact ihRight all.2 found
      · cases found

private theorem binderPairsData_all (property : Ixon.BinderNode → Prop) :
    ∀ entries : List BinderTreeEntryData,
      (∀ entry ∈ entries, entry.2.AllNodes property) →
      ∀ entry ∈ binderPairsData entries, entry.2.AllNodes property
  | [], _, _, member => nomatch member
  | [first], all, entry, member => all entry member
  | first :: second :: rest, all, entry, member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨all first List.mem_cons_self, all second (by simp)⟩
    · exact binderPairsData_all property rest
        (fun entry member => all entry (by simp [member])) entry member

theorem BinderTreeBuilt.all_nodes {property : Ixon.BinderNode → Prop}
    {entries : List BinderTreeEntryData} {tree : BinderTreeData}
    (built : BinderTreeBuilt entries tree) (all : ∀ entry ∈ entries, entry.2.AllNodes property) :
    tree.AllNodes property := by
  induction built with
  | empty => trivial
  | single entry => exact all entry List.mem_cons_self
  | pair built ih => exact ih (binderPairsData_all property _ all)

theorem RepBinderTreeData.toBounded {bound : Nat} {h : Heap F} {tree : BinderTreeData}
    {ptr : SourceValue F} (rep : RepBinderTreeData h tree ptr)
    (all : tree.AllNodes (BinderNodeParamsLt bound)) : RepBinderTree bound h ptr := by
  induction rep with
  | empty cell => exact .empty cell
  | leaf cell values => exact .leaf cell values all
  | node cell _ _ ihLeft ihRight => exact .node cell (ihLeft all.1) (ihRight all.2)

/-- Exact table contents preserve the decoder's existing parameter bounds. -/
theorem binder_table_data_bounded_spec {bound : Nat} {blocks : List Ixon.BinderBlock}
    {ptr result : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (blocksRep : RepList binderBlockListEnum RepBinderBlock h blocks ptr)
    (bounds : ∀ block ∈ blocks, ∀ node ∈ block.nodes.toList, BinderNodeParamsLt bound node)
    (ev : ObsFn W "Convert::binder_table" [ptr] h result h' calls) :
    Heap.Extends h h' ∧ ∃ tree, BinderTreeBuilt (binderLeavesData blocks) tree ∧
      RepBinderTreeData h' tree result ∧ tree.AllNodes (BinderNodeParamsLt bound) ∧
      RepBinderTree bound h' result := by
  obtain ⟨extended, tree, built, rep⟩ := binder_table_data_spec blocksRep ev
  have all : tree.AllNodes (BinderNodeParamsLt bound) := built.all_nodes (by
    intro entry member
    change entry ∈ blocks.map (fun block =>
      (binderBlockKey block, BinderTreeData.leaf (binderBlockKey block) block.nodes.toList)) at member
    obtain ⟨block, blockMember, equal⟩ := List.mem_map.mp member
    cases equal
    exact bounds block blockMember)
  exact ⟨extended, tree, built, rep, all, rep.toBounded all⟩

/-- The first binder reached by two equal table queries has the same exact level in both
conversions. Bounds come from the serialized blocks' existing decoder invariant. -/
theorem binder_head_level_same_blocks {blocks : List Ixon.BinderBlock} {query : BinderKey}
    {blocks₁ blocks₂ tree₁ tree₂ nodes₁ nodes₂ node₁ node₂ tail₁ tail₂ level₁ level₂ : SourceValue F}
    {h₁ h₂ h₁' h₂' h₁'' h₂'' h₁''' h₂''' : Heap F}
    {calls₁ calls₂ lookups₁ lookups₂ levels₁ levels₂ : List (Call F)}
    (blocksRep₁ : RepList binderBlockListEnum RepBinderBlock h₁ blocks blocks₁)
    (blocksRep₂ : RepList binderBlockListEnum RepBinderBlock h₂ blocks blocks₂)
    (bounds : ∀ block ∈ blocks, ∀ node ∈ block.nodes.toList, BinderNodeParamsLt 4294967296 node)
    (built₁ : ObsFn W "Convert::binder_table" [blocks₁] h₁ tree₁ h₁' calls₁)
    (built₂ : ObsFn W "Convert::binder_table" [blocks₂] h₂ tree₂ h₂' calls₂)
    (lookup₁ : ObsFn W "Convert::binder_nodes"
      [tree₁, .field query.1, .field query.2.1, .field query.2.2] h₁' nodes₁ h₁'' lookups₁)
    (lookup₂ : ObsFn W "Convert::binder_nodes"
      [tree₂, .field query.1, .field query.2.1, .field query.2.2] h₂' nodes₂ h₂'' lookups₂)
    (head₁ : loadValue h₁'' nodes₁ = .ok (.construct binderNodeListEnum "Cons" [node₁, tail₁]))
    (head₂ : loadValue h₂'' nodes₂ = .ok (.construct binderNodeListEnum "Cons" [node₂, tail₂]))
    (levelRead₁ : ObsFn W "Convert::binder_level" [node₁] h₁'' level₁ h₁''' levels₁)
    (levelRead₂ : ObsFn W "Convert::binder_level" [node₂] h₂'' level₂ h₂''' levels₂) :
    ∃ level : Core.KLevel, KernelLevels.RepKLevel h₁''' level level₁ ∧
      KernelLevels.RepKLevel h₂''' level level₂ := by
  obtain ⟨_, treeA, dataA, repA, allA, _⟩ := binder_table_data_bounded_spec blocksRep₁ bounds built₁
  obtain ⟨_, treeB, dataB, repB⟩ := binder_table_data_spec blocksRep₂ built₂
  obtain rfl := dataA.unique dataB
  obtain ⟨rfl, nodesA, foundA, valuesA⟩ := binder_nodes_exact_spec repA lookup₁
  obtain ⟨rfl, nodesB, foundB, valuesB⟩ := binder_nodes_exact_spec repB lookup₂
  rw [foundA] at foundB
  injection foundB with same
  subst nodesB
  have nodeBounds := BinderTreeData.lookup_all allA foundA
  obtain ⟨node, rest, shape, nodeRep₁, _⟩ := Core.RepList.cons_of_load valuesA head₁
  cases shape
  obtain ⟨node', rest', shape, nodeRep₂, _⟩ := Core.RepList.cons_of_load valuesB head₂
  injection shape with sameNode sameRest
  subst node' rest'
  have bound := nodeBounds node List.mem_cons_self
  exact ⟨binderLevel node, (binder_level_exact_spec nodeRep₁ bound levelRead₁).2,
    (binder_level_exact_spec nodeRep₂ bound levelRead₂).2⟩

end IxVM.Refinement.L1
