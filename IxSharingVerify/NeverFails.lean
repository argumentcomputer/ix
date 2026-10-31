import IxSharingVerify.FinishSuccess
import IxSharingVerify.AllocateSuccess
import IxSharingVerify.RematerializeSuccess
import IxC.Kernel.Audit.Axioms

/-!
# The production sharing rule never fails

Every refusal of the family route is unreachable once the budgets are large
enough, on every input whose canonical DAG has fewer than `2^64` terms and
whose references carry fewer than `2^64` universes:

* `familyAtWidth_ok`: one width, i.e. the uniform phase, the slot allocation
  and the re-materialization at the layout widths;
* `familyExpanded_ok`: the DAG checks and all three widths;
* `canonicalSharingTiered_ok`: the production entry on Share-free roots of
  fewer than `2^64` expression nodes whose references carry fewer than
  `2^64` universes.

With `Budget.canonicalSharingTiered_mono` the entry then succeeds under every
larger budget, and by `Budget.canonicalSharingTiered_budget_independent`
every successful run returns the same result. `canonicalSharingTiered_output_expands`
closes the output domain: a raw expansion of the output, with its sharing
table, succeeds.
-/

namespace Ix.Sharing.Verify.Totality

open Ix.Sharing.Exact
open Ix.Sharing.Family
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (DagArity Desc Below SharesIn ShareFrom termOf
  materializeDependent_parts indexOfTable_spec forall₂_getElem build_shares_below SharesIn.mono)
open Ix.Sharing.Verify.CanonicalMeaning (ExpandedOK expand_facts)
open Ix.Sharing.Verify.Budget (LimitsLe Limits.join)
open Ix.Sharing.Verify.Tiered (allocate_ok rematerialize_ok tierDeps_spec mem_bodyRefs)

/-! ## The uniform table's body references -/

theorem shareIndices_mem {P : Nat → Prop} :
    ∀ (e : Ixon.Expr) (acc : Array Nat), SharesIn P e →
      ∀ j ∈ (shareIndices e acc).toList, j ∈ acc.toList ∨ P j := by
  intro e
  induction e with
  | share i =>
    intro acc h j hj
    simp only [shareIndices, Array.toList_push, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact Or.inl hj
    · exact Or.inr h
  | prj _ _ _ ih => intro acc h; exact ih acc h
  | app f a ihf iha =>
    intro acc h j hj
    rcases iha _ h.2 j hj with hj | hj
    · exact ihf acc h.1 j hj
    · exact Or.inr hj
  | lam _ t b iht ihb =>
    intro acc h j hj
    rcases ihb _ h.2 j hj with hj | hj
    · exact iht acc h.1 j hj
    · exact Or.inr hj
  | all _ _ t b iht ihb =>
    intro acc h j hj
    rcases ihb _ h.2 j hj with hj | hj
    · exact iht acc h.1 j hj
    · exact Or.inr hj
  | letE _ t v b iht ihv ihb =>
    intro acc h j hj
    rcases ihb _ h.2.2 j hj with hj | hj
    · rcases ihv _ h.2.1 j hj with hj | hj
      · exact iht acc h.1 j hj
      · exact Or.inr hj
    · exact Or.inr hj
  | _ => intro acc _ j hj; exact Or.inl hj

/-- Every Share in a materialized entry body names an entry strictly below
that entry's term. -/
theorem materializeDependent_refs (p : Prep) (table roots : Array Nat) (width : Array (Option Nat))
    (limits : Limits) (harity : DagArity p.dag) {es rs : Array Ixon.Expr} {total work : Nat}
    (h : p.materializeDependent table roots width limits = .ok (es, rs, total, work)) :
    es.size = table.size ∧ ∀ k (hk : k < es.size),
      SharesIn (fun i => ∃ hi : i < table.size, Below p.dag table[k]! table[i]) es[k] := by
  obtain ⟨_, hes, _⟩ := materializeDependent_parts p table roots width limits h
  have hspec := indexOfTable_spec p.dag.size table
  have hidx : ∀ (u i : Nat), (indexOfPairs p.dag.size table.toList.zipIdx)[u]?.getD none =
      some i → i < UInt64.size := fun u i hi => by
    have := (Array.getElem?_eq_some_iff.mp (hspec u i hi)).1
    have := (Ix.Sharing.Verify.SharingExact.materializeDependent_parts p table roots width limits h).1
    omega
  obtain ⟨hlen, hget⟩ := forall₂_getElem hes
  simp only [Array.length_toList] at hlen
  refine ⟨hlen.symm, fun k hk => ?_⟩
  have hb := hget k (by simp; omega) (by simpa using hk)
  simp only [Array.getElem_toList] at hb
  refine SharesIn.mono ?_ _ (build_shares_below p _ _ width harity hidx _ true _ _ hb)
  rintro i ⟨u, hu, hor⟩
  rcases hor with ⟨hf, _⟩ | hbelow
  · cases hf
  · obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp (hspec u i hu)
    refine ⟨hi, ?_⟩
    rw [getElem!_pos table k (by omega)]
    exact hbelow

/-- The body references of a uniform table in a dependency order are
earlier entries strictly below their user. -/
theorem uniform_deps {dag : Dag} {table : Array Nat} {es : Array Ixon.Expr}
    (size : es.size = table.size) (nodup : table.toList.Nodup)
    (refs : ∀ k (hk : k < es.size),
      SharesIn (fun i => ∃ hi : i < table.size, Below dag table[k]! table[i]) es[k])
    (order : ∀ k j (hk : k < table.size) (hj : j < table.size), Below dag table[k] table[j] → j < k) :
    ∀ i (hi : i < table.size), ∀ d ∈ (tierDeps table es).getD table[i] [],
      ∃ j, j < i ∧ table[j]? = some d ∧ Below dag table[i] d := by
  intro i hi d hd
  rw [tierDeps_spec nodup es hi, mem_bodyRefs] at hd
  obtain ⟨j, hj, hjd⟩ := hd
  rw [Array.getElem?_eq_getElem (by omega), Option.getD_some] at hj
  rcases shareIndices_mem _ _ (refs i (by omega)) j hj with h | ⟨hjs, below⟩
  · simp at h
  · obtain ⟨_, rfl⟩ := Array.getElem?_eq_some_iff.mp hjd
    rw [getElem!_pos table i hi] at below
    exact ⟨j, order i j hi hjs below, hjd, below⟩

/-! ## One width -/

/-- **One width never refuses.** -/
theorem familyAtWidth_ok (cfg : Config) (layout : ShareLayout) {ex : Expanded} (ok : ExpandedOK ex)
    (fits : ∀ t, t < ex.dag.size → HeadFits (ex.dag.node t).head)
    (small : ex.dag.size < UInt64.size) (candidates width : Nat) :
    ∃ limits out, familyAtWidth cfg layout limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) candidates width = .ok out := by
  have hwf := ok.wf
  have hcp := Ix.Sharing.Family.childrenPrecede_of_cp hwf.precede
  obtain ⟨first, u, hu⟩ := familyUniform_ok cfg ok width small
  obtain ⟨results, states, work, delta, set, lowerBracket, -, -, -, -, finish⟩ :=
    familyUniform_finish hwf hu
  have std : uniformFinish width first ex (Prep.ofDag ex.dag)
      (familyChoice ex width states work delta set lowerBracket) = .ok u := by
    rw [uniformFinish_eq_F]
    exact finish
  obtain ⟨hin, checked, _, htable, _, work', hmat, _⟩ := uniformFinish_spec std
  have storedNodup := (inClass_of_check hin checked).1
  rw [← htable] at hmat
  have tablePerm : u.result.tableTerms.toList.Perm
      (familyChoice ex width states work delta set lowerBracket).stored.toList := by
    rw [htable]; exact pinnedOrder_perm _ _ _
  have tableNodup := tablePerm.nodup_iff.mpr storedNodup
  have tableIn : ∀ t ∈ u.result.tableTerms.toList, t < ex.dag.size :=
    fun t ht => hin t (tablePerm.subset ht)
  obtain ⟨esSize, refs⟩ := materializeDependent_refs _ _ _ _ _ (dagArity_of hwf) hmat
  have order : ∀ k j (hk : k < u.result.tableTerms.size) (hj : j < u.result.tableTerms.size),
      Below ex.dag u.result.tableTerms[k] u.result.tableTerms[j] → j < k := by
    intro k j hk hj below
    have := Ix.Sharing.Verify.Pinned.pinnedOrder_backward hwf
      (familyChoice ex width states work delta set lowerBracket).facts.deg
      (familyChoice ex width states work delta set lowerBracket).stored hin storedNodup k j
      (by rw [← htable]; exact hk) (by rw [← htable]; exact hj) (by simpa only [htable] using below)
    exact this
  obtain ⟨second, a, ha⟩ := allocate_ok layout hwf (graphFacts ex.dag ex.roots).deg
    u.result.sharing u.result.roots tableNodup tableIn
    (uniform_deps esSize tableNodup refs order)
  have trees := uniformTrees_of_finish hwf ok.roots std
  obtain ⟨third, m, hm⟩ := rematerialize_ok ok fits small trees ha
  let all := Limits.join (Limits.join first second) third
  have le1 : LimitsLe first all :=
    LimitsLe.trans (LimitsLe.join_left first second) (LimitsLe.join_left _ third)
  have le2 : LimitsLe second all :=
    LimitsLe.trans (LimitsLe.join_right first second) (LimitsLe.join_left _ third)
  have le3 : LimitsLe third all := LimitsLe.join_right _ third
  have hu' := Budget.familyUniform_mono le1 cfg ex _ width hcp hu
  have ha' := Budget.allocate_mono le2 layout ex.dag _ _ _ _ ha
  have hm' := Budget.rematerialize_mono le3 layout ex _ _ hm
  rw [rematerialize_eq_P] at hm'
  refine ⟨all, ?_⟩
  unfold familyAtWidth
  rw [Budget.bind_ok_eq hu']
  try dsimp only
  rw [Budget.bind_ok_eq ha']
  try dsimp only
  rw [Budget.bind_ok_eq hm']
  exact ⟨_, rfl⟩

/-! ## The three widths -/

/-- **The family route never refuses** a canonical DAG of fewer than `2^64`
terms whose references carry fewer than `2^64` universes. -/
theorem familyExpanded_ok (cfg : Config) (layout : ShareLayout) {ex : Expanded} (ok : ExpandedOK ex)
    (fits : ∀ t, t < ex.dag.size → HeadFits (ex.dag.node t).head)
    (small : ex.dag.size < UInt64.size) :
    ∃ limits out, familyExpanded cfg layout limits ex = .ok out := by
  have hcp := Ix.Sharing.Family.childrenPrecede_of_cp ok.wf.precede
  let candidates := tieredCandidateCount ex.dag.size (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
  obtain ⟨l1, c1, h1⟩ := familyAtWidth_ok cfg layout ok fits small candidates 1
  obtain ⟨l2, c2, h2⟩ := familyAtWidth_ok cfg layout ok fits small candidates 2
  obtain ⟨l3, c3, h3⟩ := familyAtWidth_ok cfg layout ok fits small candidates 3
  let all := Limits.join (Limits.join l1 l2) l3
  have le1 : LimitsLe l1 all :=
    LimitsLe.trans (LimitsLe.join_left l1 l2) (LimitsLe.join_left _ l3)
  have le2 : LimitsLe l2 all :=
    LimitsLe.trans (LimitsLe.join_right l1 l2) (LimitsLe.join_left _ l3)
  have le3 : LimitsLe l3 all := LimitsLe.join_right _ l3
  have h1' := Budget.familyAtWidth_mono le1 cfg layout ex _ _ _ hcp h1
  have h2' := Budget.familyAtWidth_mono le2 cfg layout ex _ _ _ hcp h2
  have h3' := Budget.familyAtWidth_mono le3 cfg layout ex _ _ _ hcp h3
  refine ⟨all, ?_⟩
  unfold familyExpanded
  rw [Budget.bind_ok_eq (uniformDagChecks_ok ok.wf ok.roots ok.reachable)]
  try dsimp only
  rw [tieredCandidates_eq, Budget.bind_ok_eq h1']
  try dsimp only
  rw [Budget.bind_ok_eq h2']
  try dsimp only
  rw [Budget.bind_ok_eq h3']
  exact ⟨_, rfl⟩

/-! ## The input domain -/

/-- Every reference in the expression carries fewer than `2^64` universes. -/
def RefsFit : Ixon.Expr → Prop
  | .ref _ us => us.size < UInt64.size
  | .recur _ us => us.size < UInt64.size
  | .prj _ _ v => RefsFit v
  | .app f a => RefsFit f ∧ RefsFit a
  | .lam _ t b => RefsFit t ∧ RefsFit b
  | .all _ _ t b => RefsFit t ∧ RefsFit b
  | .letE _ t v b => RefsFit t ∧ RefsFit v ∧ RefsFit b
  | _ => True

theorem refsFit_toExpr (n : Node) (f : Nat → Ixon.Expr) (h : RefsFit (n.toExpr f)) :
    HeadFits n.head ∧ ∀ k, k < n.head.arity → RefsFit (f (n.child k)) := by
  unfold Node.toExpr at h
  cases hh : n.head with
  | ref r us =>
    simp only [hh, RefsFit] at h
    exact ⟨h, fun k hk => by simp [Head.arity] at hk⟩
  | recur r us =>
    simp only [hh, RefsFit] at h
    exact ⟨h, fun k hk => by simp [Head.arity] at hk⟩
  | prj t i =>
    simp only [hh, RefsFit] at h
    refine ⟨trivial, fun k hk => ?_⟩
    simp only [Head.arity] at hk
    obtain rfl : k = 0 := by omega
    exact h
  | app =>
    simp only [hh, RefsFit] at h
    refine ⟨trivial, fun k hk => ?_⟩
    simp only [Head.arity] at hk
    rcases k with _ | _ | k
    · exact h.1
    · exact h.2
    · omega
  | lam c =>
    simp only [hh, RefsFit] at h
    refine ⟨trivial, fun k hk => ?_⟩
    simp only [Head.arity] at hk
    rcases k with _ | _ | k
    · exact h.1
    · exact h.2
    · omega
  | all c r =>
    simp only [hh, RefsFit] at h
    refine ⟨trivial, fun k hk => ?_⟩
    simp only [Head.arity] at hk
    rcases k with _ | _ | k
    · exact h.1
    · exact h.2
    · omega
  | letE c =>
    simp only [hh, RefsFit] at h
    refine ⟨trivial, fun k hk => ?_⟩
    simp only [Head.arity] at hk
    rcases k with _ | _ | _ | k
    · exact h.1
    · exact h.2.1
    · exact h.2.2
    · omega
  | sort _ | var _ | str _ | nat _ =>
    exact ⟨trivial, fun k hk => by simp [Head.arity] at hk⟩

/-- Every term below a term whose expression fits has a fitting head. -/
theorem headFits_of_desc {dag : Dag} (hwf : DagWF dag) :
    ∀ {a b : Nat}, Desc dag a b → RefsFit (termOf dag.nodes a) → HeadFits (dag.node b).head := by
  intro a b d
  induction d with
  | refl t =>
    intro fit
    rw [Ix.Sharing.Verify.CanonicalMeaning.dagModel_termOf hwf t] at fit
    exact (refsFit_toExpr _ _ fit).1
  | @child t u k hk rest ih =>
    intro fit
    rw [Ix.Sharing.Verify.CanonicalMeaning.dagModel_termOf hwf t] at fit
    exact ih ((refsFit_toExpr _ _ fit).2 k (by rw [← dagArity_of hwf t]; exact hk))

theorem rangeNodes_all (sources : Array Ixon.Expr) :
    Ix.Sharing.Verify.CanonicalMeaning.rangeNodes sources 0 sources.size =
      (sources.toList.map Ix.Sharing.Verify.CanonicalMeaning.nodeCount).sum := by
  unfold Ix.Sharing.Verify.CanonicalMeaning.rangeNodes
  rw [← List.range_eq_range']
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  rw [getElem!_pos sources i (by simpa using h1)]

/-! ## The production entries -/

/-- **The production sharing rule never fails** on Share-free roots of fewer
than `2^64` expression nodes whose references carry fewer than `2^64`
universes: some budget admits it, and by `Budget.canonicalSharingTiered_mono`
so does every larger one. -/
theorem canonicalSharingTiered_ok (layout : ShareLayout) (roots : Array Ixon.Expr)
    (free : ∀ i, i < roots.size → Ix.Sharing.Verify.CanonicalMeaning.ShareFree roots[i]!)
    (fit : ∀ e ∈ roots.toList, RefsFit e)
    (small : (roots.toList.map Ix.Sharing.Verify.CanonicalMeaning.nodeCount).sum < UInt64.size) :
    ∃ limits out, canonicalSharingTiered layout roots limits = .ok out := by
  obtain ⟨first, ex, ran, size⟩ := Ix.Sharing.Verify.CanonicalMeaning.expand_ok roots free
  have ok := expand_facts ran
  rw [rangeNodes_all] at size
  obtain ⟨-, -, rows⟩ := Ix.Sharing.Verify.CanonicalMeaning.expand_unshared first roots ex ran
  have fits : ∀ t, t < ex.dag.size → HeadFits (ex.dag.node t).head := by
    intro t ht
    obtain ⟨r, hr, desc⟩ := ok.reachable t ht
    obtain ⟨source, hs, rel⟩ := forall₂_mem_right' rows r hr
    exact headFits_of_desc ok.wf desc (by rw [rel.2]; exact fit source hs)
  obtain ⟨second, out, h⟩ := familyExpanded_ok canonicalFamilyConfig layout ok fits (by omega)
  refine ⟨Limits.join first second, out, ?_⟩
  unfold canonicalSharingTiered
  rw [Budget.bind_ok_eq (Budget.expand_mono (LimitsLe.join_left first second) ran),
    familyReferenceExpanded_eq_cached]
  exact Budget.familyExpanded_mono (LimitsLe.join_right first second) _ _ _ h

/-- **The production rule with a sharing table never fails** once its input
expands, on a canonical DAG of fewer than `2^64` terms whose references carry
fewer than `2^64` universes. -/
theorem canonicalSharingTieredTable_ok (layout : ShareLayout) (sharing roots : Array Ixon.Expr)
    {first : Limits} {ex : Expanded} (ran : expand first sharing roots true = .ok ex)
    (fits : ∀ t, t < ex.dag.size → HeadFits (ex.dag.node t).head)
    (small : ex.dag.size < UInt64.size) :
    ∃ limits out, canonicalSharingTieredTable layout sharing roots limits = .ok out := by
  obtain ⟨second, out, h⟩ := familyExpanded_ok canonicalFamilyConfig layout (expand_facts ran) fits
    small
  refine ⟨Limits.join first second, out, ?_⟩
  unfold canonicalSharingTieredTable
  rw [Budget.bind_ok_eq (Budget.expand_mono (LimitsLe.join_left first second) ran),
    familyReferenceExpanded_eq_cached]
  exact Budget.familyExpanded_mono (LimitsLe.join_right first second) _ _ _ h

/-! ## The output domain -/

/-- An encoding in the format domain expands. -/
theorem expand_ok_of_format {sharing roots : Array Ixon.Expr}
    (format : Ix.Sharing.Verify.Tiered.FormatOK sharing roots) :
    ∃ limits ex, expand limits sharing roots true = .ok ex := by
  obtain ⟨-, -, capacity, backward, rootsBack⟩ := format
  obtain ⟨limits, ex, h, -⟩ := Ix.Sharing.Verify.CanonicalMeaning.expand_ok_of sharing roots true
    capacity
    (fun index bound acc size => Ix.Sharing.Verify.CanonicalMeaning.sharesValid_of_below _ rfl _ (by
      change SharesIn (· < acc.size) sharing[index]!
      rw [size, getElem!_pos sharing index bound]
      exact backward index bound))
    (fun index bound resolved size => Ix.Sharing.Verify.CanonicalMeaning.sharesValid_of_below _ rfl _ (by
      change SharesIn (· < resolved.size) roots[index]!
      rw [size]
      exact rootsBack _ (by rw [getElem!_pos roots index bound]; exact Array.getElem_mem_toList bound)))
  exact ⟨limits, ex, h⟩

/-- **The output domain is closed**: the output of a successful run, with
its sharing table, expands again. -/
theorem canonicalSharingTiered_output_expands {layout : ShareLayout} {roots : Array Ixon.Expr}
    {limits : Limits} {out : TieredSharingResult}
    (run : canonicalSharingTiered layout roots limits = .ok out) :
    ∃ limits' ex', expand limits' out.result.sharing out.result.roots true = .ok ex' := by
  unfold canonicalSharingTiered at run
  rw [familyReferenceExpanded_eq_cached] at run
  obtain ⟨ex, ranE, ranF⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok run
  have ok := expand_facts ranE
  exact expand_ok_of_format (familyExpanded_output ok.wf ok.roots ok.reachable ranF).1

/-- The output closure for the entry with a sharing table. -/
theorem canonicalSharingTieredTable_output_expands {layout : ShareLayout}
    {sharing roots : Array Ixon.Expr} {limits : Limits} {out : TieredSharingResult}
    (run : canonicalSharingTieredTable layout sharing roots limits = .ok out) :
    ∃ limits' ex', expand limits' out.result.sharing out.result.roots true = .ok ex' := by
  unfold canonicalSharingTieredTable at run
  rw [familyReferenceExpanded_eq_cached] at run
  obtain ⟨ex, ranE, ranF⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok run
  have ok := expand_facts ranE
  exact expand_ok_of_format (familyExpanded_output ok.wf ok.roots ok.reachable ranF).1

end Ix.Sharing.Verify.Totality

#guard_kernel_axioms Ix.Sharing.Verify.Totality.familyAtWidth_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.familyExpanded_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.canonicalSharingTiered_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.canonicalSharingTieredTable_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.canonicalSharingTiered_output_expands [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.canonicalSharingTieredTable_output_expands [propext, Classical.choice, Quot.sound]
