import IxVMRefinement.Ingress.Decode
import IxVMRefinement.Obs.Convert
import IxVMRefinement.Lib.Words

/-! # Serialized binder data and its heap operations

The bounded tree interface and exact level conversion are shared by expression conversion
and the exact tree-content refinement. Their existing public names are preserved.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library Aiur.Library.List

namespace IxVM.Refinement.Ingress

open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Refinement.TagN
open IxVM.Refinement.Deserialize

local notation "W" => IxVM.Refinement.Obs.W

/-! ## Binder search tree (`binder_table`, `binder_nodes`) and `binder_level` -/

abbrev binderTreeEnum : String := "Convert::BinderTreeNode"
abbrev binderPairListEnum : String :=
  Names.«Lists::Node<(Field, Field, Field, &Convert::BinderTreeNode)>»

/-- Heap invariant for a `Convert::BinderTree`: every leaf stores a `RepList` of `RepBinderNode`
whose parameter indices are below `bound`. -/
inductive RepBinderTree (bound : Nat) (h : Heap F) : SourceValue F → Prop where
  | empty {addr : Nat}
      (cell : h[addr]? = some (.construct binderTreeEnum "Empty" [])) :
      RepBinderTree bound h (.ptr (.enum binderTreeEnum) addr)
  | leaf {addr : Nat} {e i v nodesPtr : SourceValue F} {ns : List Ixon.BinderNode}
      (cell : h[addr]? = some (.construct binderTreeEnum "Leaf" [e, i, v, nodesPtr]))
      (hrep : RepList binderNodeListEnum RepBinderNode h ns nodesPtr)
      (hplt : ∀ nd ∈ ns, BinderNodeParamsLt bound nd) :
      RepBinderTree bound h (.ptr (.enum binderTreeEnum) addr)
  | node {addr : Nat} {e i v left right : SourceValue F}
      (cell : h[addr]? = some (.construct binderTreeEnum "Node" [e, i, v, left, right]))
      (hleft : RepBinderTree bound h left)
      (hright : RepBinderTree bound h right) :
      RepBinderTree bound h (.ptr (.enum binderTreeEnum) addr)

theorem RepBinderTree.mono {bound : Nat} {h₁ h₂ : Heap F} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepBinderTree bound h₁ p) :
    RepBinderTree bound h₂ p := by
  induction rep with
  | empty cell => exact .empty (ext.getElem?_eq cell)
  | leaf cell hrep hplt =>
    exact .leaf (ext.getElem?_eq cell)
      (repList_heapMono₂ _ repBinderNode_heapMono₂ ext hrep) hplt
  | node cell _ _ ihl ihr => exact .node (ext.getElem?_eq cell) ihl ihr

/-- Element representation for `(Field, Field, Field, Convert::BinderTree)` list entries. -/
def RepBinderTreeEntry (bound : Nat) (h : Heap F) (_u : Unit) (v : SourceValue F) : Prop :=
  ∃ e i var t, v = .tuple [e, i, var, t] ∧ RepBinderTree bound h t

theorem repBinderTreeEntry_heapMono₂ (bound : Nat) : HeapMono₂ (RepBinderTreeEntry bound) :=
  fun _ _ _ _ ext ⟨e, i, var, t, hv, ht⟩ => ⟨e, i, var, t, hv, ht.mono ext⟩

/-- `Convert::binder_key_lt` allocates nothing (`h' = h`). -/
theorem binder_key_lt_spec {e1 i1 v1 e2 i2 v2 r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "Convert::binder_key_lt" [e1, i1, v1, e2, i2, v2] h r h' cs) :
    h' = h := by
  rcases «Convert::binder_key_lt».obs ev with
    ⟨_, _, _, ev52, _⟩ | ⟨_, _, _, _, _, ev79, _⟩ | ⟨_, _, _, _, he103, _⟩
  · obtain ⟨_, _, _, _, _, _, _, hh⟩ := Lib.less_than_fields_spec ev52
    exact hh
  · obtain ⟨_, _, _, _, _, _, _, hh⟩ := Lib.less_than_fields_spec ev79
    exact hh
  · exact he103

/-- `Convert::binder_leaves` builds a list of leaf `BinderTree` entries preserving parameter bounds. -/
theorem binder_leaves_spec {bound : Nat} {blocks : List Ixon.BinderBlock} :
    ∀ {blocksPtr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList binderBlockListEnum RepBinderBlock h blocks blocksPtr →
      (∀ b ∈ blocks, ∀ nd ∈ b.nodes.toList, BinderNodeParamsLt bound nd) →
      ObsFn W "Convert::binder_leaves" [blocksPtr] h r h' cs →
      Heap.Extends h h' ∧ ∃ us : List Unit,
        RepList binderPairListEnum (RepBinderTreeEntry bound) h' us r := by
  induction blocks with
  | nil =>
    intro blocksPtr r h h' cs hblks _ ev
    rw [binderBlockListEnum_eq] at hblks
    rcases «Convert::binder_leaves».obs ev with
      ⟨_, he24, hm23, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, [], Lib.rep_store_nil _⟩
    · exact absurd rfl (repList_ne_nil_of_load_cons hblks ld12)
  | cons blk rest ih =>
    intro blocksPtr r h h' cs hblks hplt ev
    rw [binderBlockListEnum_eq] at hblks
    rcases «Convert::binder_leaves».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨x_rest, x_ekind, x_eidx, x_variant, x_nodes, v78, m79, _, v100, m101, _, v131, m166,
        m211, _, ld12, ev91, ev113, he126, hm125, hm174, ev221, _⟩
    · have hnil := repList_nil_of_load hblks ld12
      simp at hnil
    · obtain ⟨blk', rest', heq, hblk, hrest⟩ := Core.RepList.cons_of_load hblks ld12
      cases heq
      obtain ⟨nodesPtr, hmk, hnodes⟩ := hblk
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hmk
      rcases hmk with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨_, hv78, hm79⟩ :=
        Lib.u64_to_field_spec (Deserialize.repU64_u64Value h blk.index) ev91
      subst v78 m79
      obtain ⟨_, hv100, hm101⟩ :=
        Lib.u64_to_field_spec (Deserialize.repU64_u64Value h blk.variant) ev113
      subst v100 m101
      have ext_leaf : Heap.Extends h m166 := by
        rw [hm174]; exact Heap.Extends.snoc _ _
      have hleaf : RepBinderTree bound m166 (.ptr (.enum binderTreeEnum) h.length) := by
        rw [hm174]
        exact .leaf (by simp; exact ⟨rfl, rfl, rfl⟩)
          (repList_heapMono₂ _ repBinderNode_heapMono₂ (Heap.Extends.snoc _ _) hnodes)
          (fun nd hnd => hplt blk (by simp) nd hnd)
      rw [← binderBlockListEnum_eq] at hrest
      obtain ⟨ext_rest, us, hus⟩ :=
        ih (repList_heapMono₂ _ repBinderBlock_heapMono₂ ext_leaf hrest)
          (fun b hb nd hnd => hplt b (List.mem_cons_of_mem _ hb) nd hnd) ev221
      subst r h'
      have ext_cons := Heap.Extends.snoc m211
        (.construct binderPairListEnum "Cons"
          [.tuple [.field ((if blk.shared then 1 else 0 : Nat) : F),
              .field (blk.index.toNat : F), .field (blk.variant.toNat : F),
              .ptr (.enum binderTreeEnum) h.length], v131])
      exact ⟨(ext_leaf.trans ext_rest).trans ext_cons, () :: us,
        Lib.rep_store_cons (repBinderTreeEntry_heapMono₂ bound)
          ⟨_, _, _, _, rfl, hleaf.mono ext_rest⟩ hus⟩

private theorem binder_pairs_go (n : Nat) :
    ∀ {us : List Unit} {lvlPtr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      us.length ≤ n →
      RepList binderPairListEnum (RepBinderTreeEntry bound) h us lvlPtr →
      ObsFn W "Convert::binder_pairs" [lvlPtr] h r h' cs →
      Heap.Extends h h' ∧ ∃ us' : List Unit,
        RepList binderPairListEnum (RepBinderTreeEntry bound) h' us' r := by
  induction n with
  | zero =>
    intro us lvlPtr r h h' cs hlen hlvl ev
    have hus_nil : us = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hus_nil
    rcases «Convert::binder_pairs».obs ev with
      ⟨_, he24, hm23, _⟩ | ⟨_, _, ld12, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, [], Lib.rep_store_nil _⟩
    all_goals exact absurd rfl (repList_ne_nil_of_load_cons hlvl ld12)
  | succ n ih =>
    intro us lvlPtr r h h' cs hlen hlvl ev
    rcases «Convert::binder_pairs».obs ev with
      ⟨_, he24, hm23, _⟩ |
      ⟨x_x, x_rest, _, _, he66, he67, _⟩ |
      ⟨x_rest, x_rest2, x_e1, x_i1, x_v1, x_t1, x_e2, x_i2, x_v2, x_t2, v159, m194, m247, _,
        ld12, ld57, he154, hm153, hm202, ev257, _⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, [], Lib.rep_store_nil _⟩
    · subst he66 he67
      exact ⟨Heap.Extends.refl _, us, hlvl⟩
    · obtain ⟨u1, rest1, rfl, hu1, hrest1⟩ := Core.RepList.cons_of_load hlvl ld12
      obtain ⟨u2, rest2, rfl, hu2, hrest2⟩ := Core.RepList.cons_of_load hrest1 ld57
      obtain ⟨_, _, _, _, heq1, ht1⟩ := hu1
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
      rcases heq1 with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨_, _, _, _, heq2, ht2⟩ := hu2
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
      rcases heq2 with ⟨rfl, rfl, rfl, rfl⟩
      have ext_node : Heap.Extends h m194 := by rw [hm202]; exact Heap.Extends.snoc _ _
      have hnode : RepBinderTree bound m194 (.ptr (.enum binderTreeEnum) h.length) := by
        rw [hm202]
        exact .node (by simp; exact ⟨rfl, rfl, rfl⟩) (ht1.mono (Heap.Extends.snoc _ _))
          (ht2.mono (Heap.Extends.snoc _ _))
      simp only [List.length_cons] at hlen
      obtain ⟨ext_rec, us2, hus2⟩ :=
        ih (by omega) (repList_heapMono₂ _ (repBinderTreeEntry_heapMono₂ bound) ext_node hrest2)
          ev257
      subst r h'
      have ext_cons := Heap.Extends.snoc m247
        (.construct binderPairListEnum "Cons"
          [.tuple [x_e1, x_i1, x_v1, .ptr (.enum binderTreeEnum) h.length], v159])
      exact ⟨(ext_node.trans ext_rec).trans ext_cons, () :: us2,
        Lib.rep_store_cons (repBinderTreeEntry_heapMono₂ bound)
          ⟨_, _, _, _, rfl, hnode.mono ext_rec⟩ hus2⟩

private theorem binder_tree_of_go (fuel : Nat) :
    ∀ {us : List Unit} {lvlPtr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ fuel →
      RepList binderPairListEnum (RepBinderTreeEntry bound) h us lvlPtr →
      ObsFn W "Convert::binder_tree_of" [lvlPtr] h r h' calls →
      Heap.Extends h h' ∧ RepBinderTree bound h' r := by
  induction fuel with
  | zero =>
    intro us lvlPtr r h h' calls hfuel hlvl ev
    rcases «Convert::binder_tree_of».obs ev with
      ⟨_, he24, hm23, _⟩ |
      ⟨_, _, _, _, x_t, ld12, _, he101, he102, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc135⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, .empty (by simp)⟩
    · obtain ⟨_, _, _, hu, _⟩ := Core.RepList.cons_of_load hlvl ld12
      obtain ⟨_, _, _, _, heq, ht⟩ := hu
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq
      rcases heq with ⟨_, _, _, rfl⟩
      subst he101 he102
      exact ⟨Heap.Extends.refl _, ht⟩
    · rw [hc135] at hfuel
      simp at hfuel
  | succ fuel ih =>
    intro us lvlPtr r h h' calls hfuel hlvl ev
    rcases «Convert::binder_tree_of».obs ev with
      ⟨_, he24, hm23, _⟩ |
      ⟨_, _, _, _, x_t, ld12, _, he101, he102, _⟩ |
      ⟨_, _, _, cs111, v114, m116, cs124, _, _, _, ev126, ev113, hc135⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, .empty (by simp)⟩
    · obtain ⟨_, _, _, hu, _⟩ := Core.RepList.cons_of_load hlvl ld12
      obtain ⟨_, _, _, _, heq, ht⟩ := hu
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq
      rcases heq with ⟨_, _, _, rfl⟩
      subst he101 he102
      exact ⟨Heap.Extends.refl _, ht⟩
    · obtain ⟨ext1, us', hus'⟩ := binder_pairs_go us.length (Nat.le_refl _) hlvl ev126
      have hlen111 : cs111.length ≤ fuel := by
        rw [hc135] at hfuel
        simp only [List.length_cons, List.length_append] at hfuel
        omega
      obtain ⟨ext2, htree⟩ := ih hlen111 hus' ev113
      exact ⟨ext1.trans ext2, htree⟩

/-- `Convert::binder_table` builds a `RepBinderTree` from a constant's `binders` list. -/
theorem binder_table_spec {bound : Nat} {blocks : List Ixon.BinderBlock}
    {blocksPtr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hblks : RepList binderBlockListEnum RepBinderBlock h blocks blocksPtr)
    (hplt : ∀ b ∈ blocks, ∀ nd ∈ b.nodes.toList, BinderNodeParamsLt bound nd)
    (ev : ObsFn W "Convert::binder_table" [blocksPtr] h r h' cs) :
    Heap.Extends h h' ∧ RepBinderTree bound h' r := by
  obtain ⟨cs4, v7, m9, _, ev19, ev6, _⟩ := «Convert::binder_table».obs ev
  obtain ⟨ext1, us, hus⟩ := binder_leaves_spec hblks hplt ev19
  obtain ⟨ext2, htree⟩ := binder_tree_of_go cs4.length (Nat.le_refl _) hus ev6
  exact ⟨ext1.trans ext2, htree⟩

/-- `Convert::binder_nodes` looks up a block's `BinderNode` list in `tree` without allocation. -/
theorem binder_nodes_spec {bound : Nat} {tree : SourceValue F} {h : Heap F}
    (htree : RepBinderTree bound h tree) :
    ∀ {ek ei evar r : SourceValue F} {h' : Heap F} {cs : List (Call F)},
      ObsFn W "Convert::binder_nodes" [tree, ek, ei, evar] h r h' cs →
      h' = h ∧ ∃ ns : List Ixon.BinderNode,
        RepList binderNodeListEnum RepBinderNode h ns r ∧
        ∀ nd ∈ ns, BinderNodeParamsLt bound nd := by
  induction htree with
  | empty cell =>
    intro ek ei evar r h' cs ev
    rcases «Convert::binder_nodes».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld12, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld12, _, _, _⟩
    all_goals exact (Core.load_cell_ne cell ld12 (by decide)).elim
  | leaf cell hrep hplt =>
    intro ek ei evar r h' cs ev
    rcases «Convert::binder_nodes».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, he125, he126, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld12, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld12, _, _, _⟩
    · have hxs := (Core.load_cell cell ld12).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨_, _, _, rfl⟩
      subst he125 he126
      exact ⟨rfl, _, hrep, hplt⟩
    all_goals exact (Core.load_cell_ne cell ld12 (by decide)).elim
  | node cell _ _ ihl ihr =>
    intro ek ei evar r h' cs ev
    rcases «Convert::binder_nodes».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, m161, _, _, ld12, ev174, ev232, _⟩ |
      ⟨_, _, _, _, _, m161, _, _, ld12, ev174, ev276, _⟩
    · exact (Core.load_cell_ne cell ld12 (by decide)).elim
    · have hxs := (Core.load_cell cell ld12).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨_, _, _, rfl, rfl⟩
      have hm := binder_key_lt_spec ev174
      subst hm
      exact ihl ev232
    · have hxs := (Core.load_cell cell ld12).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨_, _, _, rfl, rfl⟩
      have hm := binder_key_lt_spec ev174
      subst hm
      exact ihr ev276

/-- The exact max chain emitted for a serialized list of universe parameters.
The empty case is unused by a successful `params_level` invocation. -/
def paramsLevel : List UInt64 → Core.KLevel
  | [] => .zero
  | [p] => .param p.toNat
  | p :: ps => .max (.param p.toNat) (paramsLevel ps)

/-- The exact level emitted for a serialized binder node. Share and undecided nodes are
rejected at a binder, so their total-function values are not used by successful runs. -/
def binderLevel : Ixon.BinderNode → Core.KLevel
  | .never _ => .succ .zero
  | .zero _ => .zero
  | .ifAllZero params _ => paramsLevel params.toList
  | .share _ | .undecided _ => .zero

/-- The parameter-level conversion preserves the exact serialized parameter sequence. -/
theorem params_level_exact_spec {params : List UInt64} :
    ∀ {paramsPtr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList u64ListEnum RepU64 h params paramsPtr →
      (∀ p ∈ params, p.toNat < 4294967296) →
      ObsFn W "Convert::params_level" [paramsPtr] h r h' cs →
      Heap.Extends h h' ∧ KernelLevels.RepKLevel h' (paramsLevel params) r := by
  induction params with
  | nil =>
    intro paramsPtr r h h' cs hps _ ev
    rw [u64ListEnum_eq] at hps
    rcases «Convert::params_level».obs ev with
      ⟨_, _, _, _, _, _, ld11, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, ld11, _, _, _, _, _, _, _, _⟩
    all_goals exact absurd rfl (repList_ne_nil_of_load_cons hps ld11)
  | cons p rest ih =>
    intro paramsPtr r h h' cs hps hplt ev
    rw [u64ListEnum_eq] at hps
    rcases «Convert::params_level».obs ev with
      ⟨x_p, x_rest, m27, v41, m43, _, ld11, hm37, ev53, ld73, he82, he83, _⟩ |
      ⟨x_p, x_rest, m27, v41, m43, _, _, v98, m107, _, ld11, hm37, ev53, ld73, hne85,
        he93, hm92, ev117, _⟩
    · obtain ⟨p', rest', heq, hp, hrest⟩ := Core.RepList.cons_of_load hps ld11
      cases heq
      obtain ⟨_, hv41, hm43⟩ := Lib.u64_to_field_spec hp ev53
      subst v41 m43
      have ext_lp : Heap.Extends h m27 := by rw [hm37]; exact Heap.Extends.snoc _ _
      have restNil := Lib.rep_nil_of_load (repList_heapMono₂ _ repU64_heapMono₂ ext_lp hrest) ld73
      subst rest
      subst m27 r h'
      exact ⟨Heap.Extends.snoc _ _, .param (hplt p (by simp)) (by simp)⟩
    · obtain ⟨p', rest', heq, hp, hrest⟩ := Core.RepList.cons_of_load hps ld11
      cases heq
      obtain ⟨_, hv41, hm43⟩ := Lib.u64_to_field_spec hp ev53
      subst v41 m43
      have ext_lp : Heap.Extends h m27 := by rw [hm37]; exact Heap.Extends.snoc _ _
      have restNonempty : rest ≠ [] := by
        intro empty
        rw [empty] at hrest
        cases hrest with
        | nil cell =>
          have hv := Except.ok.inj ((Lib.load_enum_cell (ext_lp.getElem?_eq cell)).symm.trans ld73)
          exact hne85 [] rfl hv.symm
      have chain : paramsLevel (p :: rest) = .max (.param p.toNat) (paramsLevel rest) := by
        cases rest with
        | nil => exact False.elim (restNonempty rfl)
        | cons q qs => rfl
      have hlp : KernelLevels.RepKLevel m27 (.param p.toNat)
          (.ptr (.enum Core.klevelEnum) h.length) := by
        rw [hm37]; exact .param (hplt p (by simp)) (by simp)
      rw [← u64ListEnum_eq] at hrest
      obtain ⟨ext_rec, hℓ_rest⟩ :=
        ih (repList_heapMono₂ _ repU64_heapMono₂ ext_lp hrest)
          (fun q hq => hplt q (List.mem_cons_of_mem _ hq)) ev117
      subst r h'
      have ext_max := Heap.Extends.snoc m107
        (.construct Core.klevelEnum "Max" [.ptr (.enum Core.klevelEnum) h.length, v98])
      rw [chain]
      exact ⟨(ext_lp.trans ext_rec).trans ext_max,
        .max (by simp) (hlp.mono (ext_rec.trans ext_max)) (hℓ_rest.mono ext_max)⟩

/-- The binder-level conversion is determined by its serialized binder node. -/
theorem binder_level_exact_spec {nd : Ixon.BinderNode} {nodeVal r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hnd : RepBinderNode h nd nodeVal)
    (hplt : BinderNodeParamsLt 4294967296 nd)
    (ev : ObsFn W "Convert::binder_level" [nodeVal] h r h' cs) :
    Heap.Extends h h' ∧ KernelLevels.RepKLevel h' (binderLevel nd) r := by
  rcases «Convert::binder_level».obs ev with
    ⟨w17, m33, hv15, he27, hm26, hm41, _⟩ |
    ⟨w53, _, hv51, he63, hm62, _⟩ |
    ⟨x_params, w75, _, _, _, hv73, ev91, _⟩ |
    ⟨_, _, _, _, _, heq139, _, _, _⟩ |
    ⟨_, _, _, _, _, _, heq187, _, _, _⟩
  · cases hnd with
    | never m =>
      subst he27 hm26 hm41
      have ext1 := Heap.Extends.snoc h (.construct Core.klevelEnum "Zero" [])
      have ext2 := Heap.Extends.snoc (h ++ [.construct Core.klevelEnum "Zero" []])
        (.construct Core.klevelEnum "Succ" [.ptr (.enum Core.klevelEnum) h.length])
      have hz : KernelLevels.RepKLevel (h ++ [.construct Core.klevelEnum "Zero" []]) .zero
          (.ptr (.enum Core.klevelEnum) h.length) := .zero (by simp)
      exact ⟨ext1.trans ext2, .succ (by simp) (hz.mono ext2)⟩
    | zero _ | ifAllZero _ _ | share _ | undecided _ => simp at hv15
  · cases hnd with
    | zero m =>
      subst he63 hm62
      exact ⟨Heap.Extends.snoc _ _, .zero (by simp)⟩
    | never _ | ifAllZero _ _ | share _ | undecided _ => simp at hv51
  · cases hnd with
    | never _ | zero _ | share _ | undecided _ => simp at hv73
    | ifAllZero m hrep =>
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv73
      rcases hv73 with ⟨rfl, _⟩
      simpa only [binderLevel, List.toList_toArray] using params_level_exact_spec hrep hplt.2 ev91
  · simp at heq139
  · simp at heq187

theorem params_level_spec {params : List UInt64} :
    ∀ {paramsPtr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList u64ListEnum RepU64 h params paramsPtr →
      (∀ p ∈ params, p.toNat < 4294967296) →
      ObsFn W "Convert::params_level" [paramsPtr] h r h' cs →
      Heap.Extends h h' ∧ ∃ ℓ : Core.KLevel, KernelLevels.RepKLevel h' ℓ r := by
  intro paramsPtr r h h' cs hps hplt ev
  obtain ⟨ext, rep⟩ := params_level_exact_spec hps hplt ev
  exact ⟨ext, paramsLevel params, rep⟩

theorem binder_level_spec {nd : Ixon.BinderNode} {nodeVal r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hnd : RepBinderNode h nd nodeVal)
    (hplt : BinderNodeParamsLt 4294967296 nd)
    (ev : ObsFn W "Convert::binder_level" [nodeVal] h r h' cs) :
    Heap.Extends h h' ∧ ∃ ℓ : Core.KLevel, KernelLevels.RepKLevel h' ℓ r := by
  obtain ⟨ext, rep⟩ := binder_level_exact_spec hnd hplt ev
  exact ⟨ext, binderLevel nd, rep⟩

end IxVM.Refinement.Ingress
