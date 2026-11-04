import IxSharingVerify.NeverFails
import IxSharingVerify.FamilyWritingBound
import IxC.Kernel.Audit.Axioms

/-!
# The output of the sharing rule is polynomial in its DAG

The full endpoint of the family product stores every certain-stored and
every uncertain term, and its uniform length is at most the charge
`modelBound`: a table count, the local payload of every DAG node and two
Share widths per root occurrence and edge (`fullStored_ulen_le_residual`,
`residualCharge_le`). Every family member, the endpoint included, is at
least as long as the selected set (`initial_minimum_cost`), so the model
length of the uniform phase is at most `modelBound` at every width
(`selected_ulen_le_modelBound`).

An expression has fewer nodes than twice its length under any Share price
of at least one byte (`nodeCount_lt_size`): each telescope node pairs with a
side child of at least one byte, and every other node writes at least one
byte itself. This bounds the expressions the re-expansion checks walk by the
lengths the phases compute.

A phase-1 layout is at most nine times its uniform length, since a Share
reference is at most nine bytes wide (`uniformParts_layout_le`), and phase 3
is never longer than phase 1, so a successful run of the family route
writes at most `9 · modelBound ex 3` bytes (`familyExpanded_output_le`).
-/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (Desc)

/-- The uniform-length charge of the full endpoint at `width`: the table
count of a table of every term, every node's local payload, and two
widths per root occurrence and per edge. -/
def modelBound (ex : Expanded) (width : Nat) : Nat :=
  tag0Size ex.dag.size + ((List.range ex.dag.size).map fun t => residualLocalPayload ex t).sum +
    2 * width * (ex.roots.size +
      ((List.range ex.dag.size).map fun t => (ex.dag.node t).children.size).sum)

/-- **The selected set is no longer than the full endpoint**, so its
uniform length is at most `modelBound`. -/
theorem selected_ulen_le_modelBound (cfg : Config) {ex : Expanded} {width : Nat}
    (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    (checked : let sg := stg width ex
      componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) = true)
    {delta : _root_.Int} {set : Array Nat}
    (selected : LeastProductOutput cfg (stg width ex).cs.size (initialFactors ex (stg width ex)) delta set) :
    ulen ex.dag width ex.roots (mergeSorted (stg width ex).cs set).toList ≤ modelBound ex width := by
  obtain ⟨sets, minimum, -, setEq, -, -⟩ := selected
  have least := initial_minimum_cost wf roots reachable checked minimum
    (fullChoices (initialFactors ex (stg width ex))) (initial_full_member cfg ex width wf checked)
  rw [← setEq] at least
  have full := fullStored_ulen_le_residual cfg ex width wf roots checked
  have charge := residualCharge_le cfg ex width wf roots reachable checked
  have count : (fullStored ex width).size ≤ ex.dag.size := by
    have := Ix.Sharing.Verify.Totality.length_le_of_nodup (fullStored_nodup cfg ex width wf checked)
      (fun t present => ((initial_full_stored_mem cfg ex width wf checked t).mp present).1)
    simpa using this
  have header := tag0Size_mono count
  unfold fullStored at full count header charge
  unfold modelBound
  omega

end Ix.Sharing.Family

namespace Ix.Sharing.Verify.Totality

open Ix.Sharing.Exact
open Ix.Sharing.Verify.CanonicalMeaning (nodeCount)

/-- Node counts against the length facts of an expression: at most twice
each continuation length, less one. -/
theorem nodeCount_size_facts (sc : Nat → Nat) (pos : ∀ i, 1 ≤ sc i) :
    ∀ e : Ixon.Expr,
      nodeCount e + 1 ≤ 2 * (sizeInfoWith sc e).appCont.2 ∧
      nodeCount e + 1 ≤ 2 * (sizeInfoWith sc e).lamCont.2 ∧
      nodeCount e + 1 ≤ 2 * (sizeInfoWith sc e).allCont.2 ∧
      (sizeInfoWith sc e).appCont.2 ≤ (sizeInfoWith sc e).full ∧
      (sizeInfoWith sc e).lamCont.2 ≤ (sizeInfoWith sc e).full ∧
      (sizeInfoWith sc e).allCont.2 ≤ (sizeInfoWith sc e).full := by
  intro e
  induction e with
  | sort i =>
    have := Ix.Sharing.Verify.UniformModel.tag4Size_pos i.toNat
    simp only [sizeInfoWith, SizeInfo.plain, nodeCount]; omega
  | var i =>
    have := Ix.Sharing.Verify.UniformModel.tag4Size_pos i.toNat
    simp only [sizeInfoWith, SizeInfo.plain, nodeCount]; omega
  | ref r us =>
    have := Ix.Sharing.Verify.UniformModel.tag4Size_pos us.size
    simp only [sizeInfoWith, SizeInfo.plain, nodeCount]; omega
  | recur r us =>
    have := Ix.Sharing.Verify.UniformModel.tag4Size_pos us.size
    simp only [sizeInfoWith, SizeInfo.plain, nodeCount]; omega
  | str i =>
    have := Ix.Sharing.Verify.UniformModel.tag4Size_pos i.toNat
    simp only [sizeInfoWith, SizeInfo.plain, nodeCount]; omega
  | nat i =>
    have := Ix.Sharing.Verify.UniformModel.tag4Size_pos i.toNat
    simp only [sizeInfoWith, SizeInfo.plain, nodeCount]; omega
  | share i =>
    have := pos i.toNat
    simp only [sizeInfoWith, SizeInfo.plain, nodeCount]; omega
  | prj t f v ih =>
    have := Ix.Sharing.Verify.UniformModel.tag4Size_pos f.toNat
    simp only [sizeInfoWith, SizeInfo.plain, nodeCount]; omega
  | app f a ihf iha =>
    rcases hc : (sizeInfoWith sc f).appCont with ⟨n, b⟩
    rw [hc] at ihf
    dsimp only at ihf
    have := Ix.Sharing.Verify.UniformModel.tag4Size_pos (n + 1)
    simp only [sizeInfoWith, hc, nodeCount]
    omega
  | lam c ty body iht ihb =>
    rcases hc : (sizeInfoWith sc body).lamCont with ⟨n, b⟩
    rw [hc] at ihb
    dsimp only at ihb
    have := Ix.Sharing.Verify.UniformModel.tag4Size_pos (n + 1)
    simp only [sizeInfoWith, hc, nodeCount]
    omega
  | all c r ty body iht ihb =>
    rcases hc : (sizeInfoWith sc body).allCont with ⟨n, b⟩
    rw [hc] at ihb
    dsimp only at ihb
    have := Ix.Sharing.Verify.UniformModel.tag4Size_pos (n + 1)
    simp only [sizeInfoWith, hc, nodeCount]
    omega
  | letE c ty v body iht ihv ihb =>
    have := Ix.Sharing.Verify.UniformModel.tag4Size_pos c.flags.toNat
    simp only [sizeInfoWith, SizeInfo.plain, nodeCount]; omega

/-- **An expression has fewer nodes than twice its length** when every
Share costs at least one byte. -/
theorem nodeCount_lt_size (sc : Nat → Nat) (pos : ∀ i, 1 ≤ sc i) (e : Ixon.Expr) :
    nodeCount e + 1 ≤ 2 * (sizeInfoWith sc e).full := by
  obtain ⟨h, -, -, le, -, -⟩ := nodeCount_size_facts sc pos e
  omega

end Ix.Sharing.Verify.Totality

namespace Ix.Sharing.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Sharing.Verify.SharingExact (materializeDependent_parts indexOfTable_spec)

/-- Sums of a pointwise equation. -/
theorem forall₂_sum_eq {α β : Type} {f : β → Nat} {g : α → Nat} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ (fun x y => f y = g x) xs ys →
      (ys.map f).sum = (xs.map g).sum
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [List.map_cons, List.sum_cons, h, forall₂_sum_eq hs]

/-- A sum of a list bounded termwise. -/
theorem sum_le_of_le {α : Type} {f g : α → Nat} :
    ∀ (l : List α), (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl _
  | x :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_le_of_le l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have := h x List.mem_cons_self
    omega

/-- A sum scaled termwise. -/
theorem sum_mul_left {α : Type} (c : Nat) (g : α → Nat) :
    ∀ (l : List α), (l.map fun x => c * g x).sum = c * (l.map g).sum
  | [] => by simp
  | x :: l => by simp only [List.map_cons, List.sum_cons, sum_mul_left c g l, Nat.mul_add]

/-- A TagN Share is at most nine bytes. -/
theorem tagNWidth_le_nine (i : Nat) : tagNWidth i ≤ 9 := by
  rw [Ix.Sharing.Verify.SharingExact.tagNWidth_eq_byteWidth]
  unfold Ixon.tagNByteWidth
  repeat' split
  all_goals omega

theorem widthAt_le_nine (layout : ShareLayout) (i : Nat) : layout.widthAt i ≤ 9 := by
  cases layout with
  | tagN => exact tagNWidth_le_nine i

section Parts

variable {w : Nat} {limits : Limits} {ex : Expanded} {deg : Array Nat} {stored : Array Nat}
  {table : Array Nat} {es rs : Array Ixon.Expr} {model work : Nat}

/-- **The materialized uniform table is a set of writings**: its bodies and
roots are writings of their terms with the table's dictionary, Shares by
table index. -/
theorem uniformParts_trees (hwf : DagWF ex.dag) (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (hin : ∀ t ∈ stored.toList, t < ex.dag.size) (htable : table = pinnedOrder ex.dag deg stored)
    (hmat : (Prep.ofDag ex.dag).materializeDependent table ex.roots
      (stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)) limits =
        .ok (es, rs, model, work)) :
    List.Forall₂ (fun t e => ∃ T, TreeOf (Prep.ofDag ex.dag) (fun t => decide (t ∈ table.toList))
        (indexOfPairs ex.dag.size table.toList.zipIdx) true t e T) table.toList es.toList ∧
      List.Forall₂ (fun r e => ∃ T, TreeOf (Prep.ofDag ex.dag) (fun t => decide (t ∈ table.toList))
        (indexOfPairs ex.dag.size table.toList.zipIdx) false r e T) ex.roots.toList rs.toList := by
  have hp := prepWF_ofDag hwf
  have hperm : table.toList.Perm stored.toList := by
    rw [htable]; exact pinnedOrder_perm _ _ _
  have hin' : ∀ t ∈ table.toList, t < ex.dag.size := fun t ht => hin t (hperm.subset ht)
  obtain ⟨hsize, hents, hrts⟩ := materializeDependent_parts _ _ _ _ _ hmat
  let width1 := stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)
  let avail1 := fun t => decide (t ∈ table.toList)
  let index1 := indexOfPairs ex.dag.size table.toList.zipIdx
  have hwidth : ∀ t, widthOf width1 t = if avail1 t then some w else none := by
    intro t
    simp only [width1, avail1]
    rw [← Array.foldl_toList, widthOfStored ex.dag.size w stored.toList hin t]
    simp only [hperm.mem_iff]
  have hindex : ∀ t, (index1[t]?.getD none).isSome = avail1 t :=
    fun t => indexOfTable_isSome _ _ hin' t
  have hidx : ∀ (t i : Nat), index1[t]?.getD none = some i → i < UInt64.size := by
    intro t i hi
    have := indexOfTable_spec _ _ t i hi
    have := (Array.getElem?_eq_some_iff.mp this).1
    omega
  have hev := hp.evalAll_ok (ofDag_empty_size ex.dag) (wd := fun _ => w) (avail := avail1)
    width1 hwidth
  refine ⟨?_, ?_⟩
  · refine Ix.Sharing.Verify.Tiered.forall₂_imp_mem hents fun t ht e he => ?_
    exact hp.gBuild_tree _ hev index1 width1 hwidth hindex hidx _ true t e (hin' t ht) he
  · refine Ix.Sharing.Verify.Tiered.forall₂_imp_mem hrts fun r hr e he => ?_
    exact hp.gBuild_tree _ hev index1 width1 hwidth hindex hidx _ false r e (hroots r hr) he

/-- **The materialized uniform table writes its model length**: the table
count and the lengths of its bodies and roots, every Share priced at the
uniform width, add up to the predicted total. -/
theorem uniformParts_sizes (hwf : DagWF ex.dag) (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (hin : ∀ t ∈ stored.toList, t < ex.dag.size) (htable : table = pinnedOrder ex.dag deg stored)
    (hmat : (Prep.ofDag ex.dag).materializeDependent table ex.roots
      (stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)) limits =
        .ok (es, rs, model, work)) :
    tag0Size es.size + (es.toList.map fun e => (sizeInfoWith (fun _ => w) e).full).sum +
      (rs.toList.map fun e => (sizeInfoWith (fun _ => w) e).full).sum = model := by
  have hp := prepWF_ofDag hwf
  have hperm : table.toList.Perm stored.toList := by
    rw [htable]; exact pinnedOrder_perm _ _ _
  have hin' : ∀ t ∈ table.toList, t < ex.dag.size := fun t ht => hin t (hperm.subset ht)
  have total := materializeDependent_total hmat
  obtain ⟨hsize, hents, hrts⟩ := materializeDependent_parts _ _ _ _ _ hmat
  let width1 := stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)
  let avail1 := fun t => decide (t ∈ table.toList)
  let index1 := indexOfPairs ex.dag.size table.toList.zipIdx
  have hwidth : ∀ t, widthOf width1 t = if avail1 t then some w else none := by
    intro t
    simp only [width1, avail1]
    rw [← Array.foldl_toList, widthOfStored ex.dag.size w stored.toList hin t]
    simp only [hperm.mem_iff]
  have hindex : ∀ t, (index1[t]?.getD none).isSome = avail1 t :=
    fun t => indexOfTable_isSome _ _ hin' t
  have hidx : ∀ (t i : Nat), index1[t]?.getD none = some i → i < UInt64.size := by
    intro t i hi
    have := indexOfTable_spec _ _ t i hi
    have := (Array.getElem?_eq_some_iff.mp this).1
    omega
  have hev := hp.evalAll_ok (ofDag_empty_size ex.dag) (wd := fun _ => w) (avail := avail1)
    width1 hwidth
  have hsc : ∀ (v i : Nat), index1[v]?.getD none = some i →
      i < UInt64.size ∧ (fun _ => w) i = (fun _ => w) v := fun v i hi => ⟨hidx v i hi, rfl⟩
  have entries : List.Forall₂ (fun t e => (sizeInfoWith (fun _ => w) e).full =
      (Prep.ofDag ex.dag).inlineCost ((Prep.ofDag ex.dag).evalAll width1) index1 width1 t)
      table.toList es.toList := by
    refine Ix.Sharing.Verify.Tiered.forall₂_imp_mem hents fun t ht e he => ?_
    rw [(hp.gBuild_size _ hev index1 width1 hwidth hindex _ hsc _ true t e (hin' t ht) he).1,
      ite_eq_left rfl, hp.gInlineCost_eq _ hev index1 width1 hwidth hindex t (hin' t ht)]
  have rootRows : List.Forall₂ (fun r e => (sizeInfoWith (fun _ => w) e).full =
      ((Prep.ofDag ex.dag).evalAll width1).cost[r]!) ex.roots.toList rs.toList := by
    refine Ix.Sharing.Verify.Tiered.forall₂_imp_mem hrts fun r hr e he => ?_
    rw [(hp.gBuild_size _ hev index1 width1 hwidth hindex _ hsc _ false r e (hroots r hr) he).1,
      ite_eq_right Bool.false_ne_true, hev.cost]
  have sizes : es.size = table.size := by
    have := (Ix.Sharing.Verify.SharingExact.forall₂_getElem hents).1
    simpa using this.symm
  rw [forall₂_sum_eq entries, forall₂_sum_eq rootRows, sizes]
  exact total.symm

/-- **A writing priced by a layout is at most nine times its uniform
length** at any width of at least one byte. -/
theorem treeOf_layout_le {p : Prep} {avail : Nat → Bool} {index : Array (Option Nat)}
    {entry : Bool} {t : Nat} {e : Ixon.Expr} {T : WTree} (tree : TreeOf p avail index entry t e T)
    (layout : ShareLayout) (hw : 1 ≤ w) :
    (sizeInfoWith layout.widthAt e).full ≤ 9 * (sizeInfoWith (fun _ => w) e).full := by
  have hl := (tree.2.2.2 layout.widthAt (fun u => layout.widthAt ((index[u]?.getD none).getD 0))
    (fun u i hi => by simp only [hi]; rfl)).1
  have hu := (tree.2.2.2 (fun _ => w) (fun _ => w) (fun _ _ _ => rfl)).1
  rw [hl, WTree.gcost_eq]
  rw [hu, WTree.gcost_eq]
  have leaves := sum_le_of_le T.leaves (f := fun u => layout.widthAt ((index[u]?.getD none).getD 0))
    (g := fun _ => 9 * w)
    (fun u _ => by have := widthAt_le_nine layout ((index[u]?.getD none).getD 0); omega)
  rw [sum_mul_left] at leaves
  rw [Nat.mul_add]
  omega

/-- **The materialized uniform table priced by a layout is at most nine
times its model length** at any width of at least one byte. -/
theorem uniformParts_layout_le (hw : 1 ≤ w) (hwf : DagWF ex.dag)
    (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (hin : ∀ t ∈ stored.toList, t < ex.dag.size) (htable : table = pinnedOrder ex.dag deg stored)
    (hmat : (Prep.ofDag ex.dag).materializeDependent table ex.roots
      (stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)) limits =
        .ok (es, rs, model, work)) (layout : ShareLayout) :
    layoutBytes layout es rs ≤ 9 * model := by
  have sizes := uniformParts_sizes hwf hroots hin htable hmat
  obtain ⟨hents, hrts⟩ := uniformParts_trees hwf hroots hin htable hmat
  have entries := sum_le_of_le es.toList
    (f := fun e => (sizeInfoWith layout.widthAt e).full)
    (g := fun e => 9 * (sizeInfoWith (fun _ => w) e).full)
    (fun e he => by
      obtain ⟨t, -, T, tree⟩ := forall₂_mem_right' hents e he
      exact treeOf_layout_le tree layout hw)
  have rootSum := sum_le_of_le rs.toList
    (f := fun e => (sizeInfoWith layout.widthAt e).full)
    (g := fun e => 9 * (sizeInfoWith (fun _ => w) e).full)
    (fun e he => by
      obtain ⟨r, -, T, tree⟩ := forall₂_mem_right' hrts e he
      exact treeOf_layout_le tree layout hw)
  rw [sum_mul_left] at entries rootSum
  unfold layoutBytes
  simp only
  rw [array_foldl_add_sum, array_foldl_add_sum]
  omega

/-- **The materialized uniform table has fewer than twice its model length
in expression nodes.** -/
theorem uniformParts_nodes (hw : 1 ≤ w) (hwf : DagWF ex.dag)
    (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (hin : ∀ t ∈ stored.toList, t < ex.dag.size) (htable : table = pinnedOrder ex.dag deg stored)
    (hmat : (Prep.ofDag ex.dag).materializeDependent table ex.roots
      (stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)) limits =
        .ok (es, rs, model, work)) :
    (es.toList.map Ix.Sharing.Verify.CanonicalMeaning.nodeCount).sum +
      (rs.toList.map Ix.Sharing.Verify.CanonicalMeaning.nodeCount).sum ≤ 2 * model := by
  have sizes := uniformParts_sizes hwf hroots hin htable hmat
  have pos : ∀ i : Nat, 1 ≤ (fun _ => w) i := fun _ => hw
  have entries := sum_le_of_le es.toList
    (f := Ix.Sharing.Verify.CanonicalMeaning.nodeCount)
    (g := fun e => 2 * (sizeInfoWith (fun _ => w) e).full)
    (fun e _ => by have := Ix.Sharing.Verify.Totality.nodeCount_lt_size _ pos e; omega)
  have rootSum := sum_le_of_le rs.toList
    (f := Ix.Sharing.Verify.CanonicalMeaning.nodeCount)
    (g := fun e => 2 * (sizeInfoWith (fun _ => w) e).full)
    (fun e _ => by have := Ix.Sharing.Verify.Totality.nodeCount_lt_size _ pos e; omega)
  rw [sum_mul_left] at entries rootSum
  omega

end Parts

end Ix.Sharing.Verify.UniformModel

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (Desc)

theorem modelBound_mono (ex : Expanded) {a b : Nat} (le : a ≤ b) : modelBound ex a ≤ modelBound ex b := by
  unfold modelBound
  have := Nat.mul_le_mul_right (ex.roots.size +
    ((List.range ex.dag.size).map fun t => (ex.dag.node t).children.size).sum)
    (Nat.mul_le_mul_left 2 le)
  omega

/-- A finished uniform phase priced by a layout is at most nine times its
model length. -/
theorem UniformFinished.layout_le {width : Nat} {limits : Limits} {ex : Expanded}
    {out : UniformSharingResult} (finished : UniformFinished width limits ex out) (hw : 1 ≤ width)
    (wf : DagWF ex.dag) (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size) (layout : ShareLayout) :
    layoutBytes layout out.result.sharing out.result.roots ≤ 9 * out.result.modelBytes := by
  obtain ⟨work, hmat⟩ := finished.materialized
  exact uniformParts_layout_le hw wf roots finished.inBounds finished.table hmat layout

/-- **The output of the production rule is polynomial in its DAG**: a
successful run of the family route writes at most nine times the full
endpoint's charge at the widest phase-1 width. -/
theorem familyExpanded_output_le {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {ex : Expanded} (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y)
    {out : TieredSharingResult} (run : familyExpanded cfg layout limits ex = .ok out) :
    out.result.modelBytes ≤ 9 * modelBound ex 3 := by
  obtain ⟨⟨width, admitted, delta, set, least, stored, finished⟩, output⟩ :=
    familyExpanded_checked wf roots reachable run
  have range : 1 ≤ width ∧ width ≤ 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
    omega
  have selectedBound := selected_ulen_le_modelBound cfg wf roots reachable
    (stage_componentsChecked width ex wf) least
  have layout1 := finished.layout_le range.1 wf roots layout
  have phase3 := output.phase3_le
  have wider := modelBound_mono ex range.2
  rw [finished.model, stored] at layout1
  omega

end Ix.Sharing.Family
#guard_kernel_axioms Ix.Sharing.Family.selected_ulen_le_modelBound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.nodeCount_size_facts [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.nodeCount_lt_size [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.UniformModel.tagNWidth_le_nine [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.UniformModel.uniformParts_trees [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.UniformModel.uniformParts_sizes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.UniformModel.treeOf_layout_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.UniformModel.uniformParts_layout_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.UniformModel.uniformParts_nodes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.UniformFinished.layout_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyExpanded_output_le [propext, Classical.choice, Quot.sound]
