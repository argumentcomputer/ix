import IxSharingVerify.OutputBound
import IxSharingVerify.AllocateBudget
import IxC.Kernel.Audit.Axioms

/-!
# A sufficient budget for the production sharing rule

`NeverFails` shows that some budget admits every input of the domain. This
module names one: `limitsFor N`, polynomial in the size `N` of the input
(its expression nodes plus its universe arguments, `inputSize`), under which
the production entry succeeds on Share-free roots
(`canonicalSharingTiered_limitsFor`), with the same output under every
larger budget (`canonicalSharingTiered_above`).

Every stage is first shown to succeed under every budget that covers an
explicit count of the DAG (the `*_within` theorems): the family calls and
work, the knapsack cells, the model length (at most `modelBound`, by the
output-size bound of `OutputBound`), the materialized lengths and work, the
expression nodes the re-expansion checks walk (fewer than twice the
lengths), and the first-tier states (`AllocateBudget`). The counts are then
bounded by powers of `B = N + 1`. The DAG has at most `N` terms, every
reference carries at most `N` universes, and the components hold at most
`N` terms in all, so the component calls are at most `2^17·B²` and their
work `6·2^16·B³`, the knapsack cells `B²`, the model `64·B²` bytes, the
materialization work `B³ + 576·B²`, and the first-tier states `B^9`.

The budget bounds what the meters count. Which loops of the compiled code
the meters charge, and which they bound only through other counts, is
recorded in `docs/sharing-minimum.md` (§14.3).
-/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (Desc)

/-! ## The knapsack cells -/

theorem groupByRoot_size (n : Nat) (cls : Array UClass) (root : Nat → Nat) :
    (groupByRoot n cls root).size ≤ n := by
  unfold groupByRoot
  have step : ∀ (l : List Nat) (acc : Array (Option Nat) × Array (Array Nat)),
      (l.foldl (groupStep cls root) acc).2.size ≤ acc.2.size + l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons t l ih =>
      intro acc
      rw [List.foldl_cons]
      have rest := ih (groupStep cls root acc t)
      have one : (groupStep cls root acc t).2.size ≤ acc.2.size + 1 := by
        unfold groupStep
        split
        · split <;> simp
        · simp
      simp only [List.length_cons]
      omega
  have := step (List.range n) (Array.replicate n none, #[])
  simpa using this

theorem comps_size_le (width : Nat) (ex : Expanded) : (stg width ex).comps.size ≤ ex.dag.size := by
  have comps : (stg width ex).comps = uncertainComponents ex.dag (stg width ex).cls := rfl
  rw [comps]
  exact groupByRoot_size _ _ _

theorem unc_size_le (width : Nat) (ex : Expanded) : (stg width ex).unc.size ≤ ex.dag.size := by
  have := congrArg List.length (stage_unc (w := width) (ex := ex))
  simp only [Array.length_toList] at this
  rw [this, uunc]
  simpa using List.length_filter_le _ (List.range ex.dag.size)

theorem tag0BracketStart_le (k : Nat) : tag0BracketStart k ≤ k := by
  unfold tag0BracketStart
  repeat' split
  all_goals omega

theorem foldl_mergeSorted_size (sets : List CompResult) (start : Array Nat) :
    (sets.foldl (fun acc r => mergeSorted acc r.bestSet) start).size =
      start.size + (sets.map (·.bestSet.size)).sum := by
  induction sets generalizing start with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih]
    have := (Ix.Sharing.Exact.mergeSorted_perm start r.bestSet).length_eq
    simp only [Array.length_toList, List.length_append] at this
    simp only [List.map_cons, List.sum_cons]
    omega

theorem forall₂_sum_le {α β : Type} {R : α → β → Prop} {f : α → Nat} {g : β → Nat}
    (each : ∀ a b, R a b → g b ≤ f a) :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → (ys.map g).sum ≤ (xs.map f).sum
  | _, _, .nil => Nat.le_refl _
  | _, _, .cons h hs => by
    simp only [List.map_cons, List.sum_cons]
    have := each _ _ h
    have := forall₂_sum_le each hs
    omega

/-- **The knapsack has at most `(n + 1) · n` cells** on a DAG of `n` terms:
at most one row per term and a capacity below the number of uncertain
terms. -/
theorem knapsackCells_le (cfg : Config) (ex : Expanded) (width : Nat) (wf : DagWF ex.dag)
    {limits : Limits} {results : Array CompResult} {states work : Nat}
    (produced : familyComponents cfg limits ex (stg width ex) width (parentsOf ex.dag) =
      .ok (results, states, work)) :
    knapsackCells (stg width ex).cs.size results ≤ (ex.dag.size + 1) * ex.dag.size := by
  have checked := stage_componentsChecked width ex wf
  have rows := familyComponents_rows (dagWF_childrenPrecede wf) produced
  have count := familyComponents_count (dagWF_childrenPrecede wf) produced
  have compsSize := comps_size_le width ex
  obtain ⟨valid, -, capacityLe⟩ := initial_factors_partition ex width wf checked
  have uncSize := unc_size_le width ex
  have coherent := rows.coherent valid
  have sound := rows.sound
  have bestLe : ∀ f r, ResultRow cfg (stg width ex).slack f r → f.members.Nodup →
      r.bestSet.size ≤ f.members.length := by
    intro f r row nodup
    obtain ⟨k, at_k⟩ := bestSetOf_row (row.sorted nodup) row.2.2
    obtain ⟨-, inFamily, -⟩ := row.sound k _ at_k
    have sorted := family_sorted cfg f.cost f.members nodup _ inFamily
    have := List.Nodup.length_le_of_subset (sorted.imp Nat.ne_of_lt)
      (family_members cfg f.cost f.members _ inFamily)
    simpa using this
  have bestSum : (results.toList.map (·.bestSet.size)).sum ≤
      ((initialFactors ex (stg width ex)).map (·.members.length)).sum := by
    have : List.Forall₂ (fun f r => ResultRow cfg (stg width ex).slack f r ∧ f.members.Nodup)
        (initialFactors ex (stg width ex)) results.toList := by
      have pairs := Ix.Sharing.Verify.SharingExact.forall₂_getElem rows
      apply Ix.Sharing.Verify.Tiered.forall₂_of_getElem pairs.1
      intro k h1 h2
      exact ⟨pairs.2 k h1 h2, valid _ (List.getElem_mem h1)⟩
    exact forall₂_sum_le (fun f r h => bestLe f r h.1 h.2) this
  have capLe : ((initialFactors ex (stg width ex)).map (·.members.length)).sum ≤
      (stg width ex).unc.size := by
    unfold capacity at capacityLe
    exact Nat.le_of_add_le_add_left capacityLe
  unfold knapsackCells
  dsimp only
  rw [← Array.foldl_toList, foldl_mergeSorted_size, Array.size_empty, Nat.zero_add]
  have start := tag0BracketStart_le ((stg width ex).cs.size + (results.toList.map (·.bestSet.size)).sum)
  split
  · exact Nat.mul_le_mul (by omega) (by omega)
  · exact Nat.zero_le _

end Ix.Sharing.Family

namespace Ix.Sharing.Verify.Totality

open Ix.Sharing.Exact
open Ix.Sharing.Family
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (DagArity Desc Below bind_eq_ok termOf materializeDependent_parts
  materializeDependent_backward materializeDependent_correct forall₂_getElem)
open Ix.Sharing.Verify.CanonicalMeaning (ExpandedOK reexpand_ids_within dagModel_termOf rangeNodes)

/-! ## The uniform phase -/

/-- **The uniform finisher succeeds under every budget that covers its
model length** (twice it for the expression nodes it re-expands). -/
theorem uniformFinishF_within {w : Nat} (hw : 1 ≤ w) {ex : Expanded} (ok : ExpandedOK ex)
    (deg : Array Nat) (c : UniformChoice) (hin : ∀ t ∈ c.stored.toList, t < ex.dag.size)
    (sorted : c.stored.toList.Pairwise (· < ·)) (degrees : ∀ t ∈ c.stored.toList, 2 ≤ deg[t]!)
    (model : c.model = ulen ex.dag w ex.roots c.stored.toList)
    (capacity : ex.dag.size < wordBound) (limits : Limits)
    (matRoom : c.model ≤ limits.maxMaterialize)
    (visitRoom : 2 * c.model ≤ limits.maxExprVisits) (depthRoom : 2 * c.model ≤ limits.maxDepth)
    (nodeRoom : ex.dag.size + 2 * c.model ≤ limits.maxNodes) :
    ∃ out, uniformFinishF w limits ex (Prep.ofDag ex.dag) deg c = .ok out := by
  have hwf := ok.wf
  let order := pinnedOrder ex.dag c.facts.deg c.stored
  have hperm : order.toList.Perm c.stored.toList := pinnedOrder_perm _ _ _
  have nodup : c.stored.toList.Nodup := sorted.imp Nat.ne_of_lt
  have orderSize : order.size < wordBound := by
    have h1 := length_le_of_nodup nodup hin
    have h2 := hperm.length_eq
    simp only [Array.length_toList] at h1 h2
    omega
  have totalEq : dependentTotal (Prep.ofDag ex.dag) order ex.roots (storedWidth ex.dag.size w c.stored) =
      c.model := by
    rw [model]
    exact dependentTotal_eq (roots := ex.roots) hwf hin hperm
  obtain ⟨es, rs, work, materialized⟩ := materializeDependent_ok hwf hin hperm ok.roots orderSize limits
    (by rw [totalEq]; exact matRoom)
  obtain ⟨esSize, backward, rootsBelow⟩ := materializeDependent_backward _ order ex.roots _ limits
    (dagArity_of hwf) (fun k j hk hj below => Ix.Sharing.Verify.Pinned.pinnedOrder_backward hwf
      c.facts.deg c.stored hin nodup k j hk hj below) materialized
  obtain ⟨entries, rootRows⟩ := materializeDependent_correct _ order ex.roots _ limits materialized
    (termOf ex.dag.nodes) (dagModel_termOf hwf)
  have rsSize : rs.size = ex.roots.size := by
    have := (forall₂_getElem rootRows).1
    simpa using this.symm
  have nodes := uniformParts_nodes hw hwf ok.roots hin rfl materialized
  rw [totalEq] at nodes
  rw [← rangeNodes_all, ← rangeNodes_all] at nodes
  obtain ⟨visits, reexpanded⟩ := reexpand_ids_within hwf ok.injective
    (fun t ht => hin t (hperm.subset ht)) ok.roots esSize rsSize backward rootsBelow entries rootRows
    (by omega) limits (by omega) (by omega) (by omega)
  have mat : (Prep.ofDag ex.dag).materializeDependent (pinnedOrder ex.dag c.facts.deg c.stored)
      ex.roots (c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none))
      limits = .ok (es, rs, dependentTotal (Prep.ofDag ex.dag) (pinnedOrder ex.dag c.facts.deg c.stored)
        ex.roots (c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)),
        work) := materialized
  have re : reexpand limits ex.dag es rs =
      .ok (pinnedOrder ex.dag c.facts.deg c.stored, ex.roots, visits) := reexpanded
  unfold uniformFinishF
  dsimp only
  have bounded : (c.stored.all (· < ex.dag.size)) = true := by
    rw [Array.all_eq_true']
    intro t member
    exact decide_eq_true (hin t (Array.mem_toList_iff.mpr member))
  have checkModel : (dependentTotal (Prep.ofDag ex.dag) (pinnedOrder ex.dag c.facts.deg c.stored)
      ex.roots (c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none))
      == c.model) = true := beq_iff_eq.mpr totalEq
  rw [ite_eq_left bounded, ite_eq_left (inClassCheckD_ok sorted degrees)]
  rw [Budget.bind_ok_eq mat]
  dsimp only
  rw [ite_eq_left checkModel]
  rw [Budget.bind_ok_eq re]
  dsimp only
  rw [ite_eq_left (beq_self_eq_true _), ite_eq_left (beq_self_eq_true _)]
  exact ⟨_, rfl⟩

/-- **The family phase succeeds under every budget that covers its counts**:
the family calls and work, the knapsack cells, and the model bound for the
output length, the materialized length and the re-expanded nodes. -/
theorem familyUniform_within (cfg : Config) {ex : Expanded} (ok : ExpandedOK ex) {width : Nat}
    (hw : 1 ≤ width) (capacity : ex.dag.size < wordBound) (limits : Limits)
    (stateRoom : familyCallTotal cfg (stg width ex).comps.toList ≤ limits.maxStates)
    (workRoom : familyWorkTotal cfg ex (stg width ex) (stg width ex).comps.toList ≤ limits.maxCostEvals)
    (cellRoom : (ex.dag.size + 1) * ex.dag.size ≤ limits.maxKnapsackCells)
    (outputRoom : modelBound ex width ≤ limits.maxOutputBytes)
    (matRoom : modelBound ex width ≤ limits.maxMaterialize)
    (visitRoom : 2 * modelBound ex width ≤ limits.maxExprVisits)
    (depthRoom : 2 * modelBound ex width ≤ limits.maxDepth)
    (nodeRoom : ex.dag.size + 2 * modelBound ex width ≤ limits.maxNodes) :
    ∃ out, familyUniform cfg limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) width = .ok out := by
  have wf := ok.wf
  have checked := stage_componentsChecked width ex wf
  have hcp := Ix.Sharing.Family.childrenPrecede_of_cp wf.precede
  have membersNodup := (checked_components_capacity wf checked).1
  obtain ⟨⟨results, states, work⟩, produced⟩ := familyComponents_ok cfg limits ex (stg width ex) width
    hcp membersNodup stateRoom workRoom
  obtain ⟨⟨delta, set, lowerBracket⟩, chosen⟩ := uniformKnapsack_ok limits _ results
    (Nat.le_trans (knapsackCells_le cfg ex width wf produced) cellRoom)
  have selected := familyComponents_least cfg limits ex width wf checked produced chosen
  have modelEq := (selected_model_nonnegative wf ok.roots ok.reachable checked selected).2
  have bound := selected_ulen_le_modelBound cfg wf ok.roots ok.reachable checked selected
  obtain ⟨storedFacts, sorted⟩ := selected_stored wf checked selected
  have small : (familyModel ex width delta set).toNat ≤ modelBound ex width := by
    unfold familyModel
    rw [modelEq]
    exact bound
  obtain ⟨out, finish⟩ := uniformFinishF_within hw ok (graphFacts ex.dag ex.roots).deg
    (familyChoice ex width states work delta set lowerBracket)
    (fun t ht => (storedFacts t ht).1) sorted (fun t ht => (storedFacts t ht).2) modelEq capacity limits
    (by change (familyModel ex width delta set).toNat ≤ _; omega)
    (by change 2 * (familyModel ex width delta set).toNat ≤ _; omega)
    (by change 2 * (familyModel ex width delta set).toNat ≤ _; omega)
    (by change _ + 2 * (familyModel ex width delta set).toNat ≤ _; omega)
  exact ⟨out, familyUniform_of_parts produced chosen (by omega) finish⟩

/-! ## Table materialization -/

theorem cutScan_work_le (spineLen sides : Array Nat) (below : Array (Option Nat))
    (width : Array (Option Nat)) (l s : Nat) :
    ∀ fuel cur best work, (cutScan spineLen sides below width l s fuel cur best work).2 ≤ work + fuel
  | 0, _, _, _ => by simp [cutScan]
  | _ + 1, none, _, _ => by simp [cutScan]
  | fuel + 1, some u, best, work => by
    simp only [cutScan]
    exact Nat.le_trans (cutScan_work_le spineLen sides below width l s fuel _ _ (work + 1)) (by omega)

theorem cutScan_snd_le {spineLen sides : Array Nat} {below : Array (Option Nat)}
    {width : Array (Option Nat)} {l s fuel : Nat} {cur : Option Nat} {best work : Nat} {r : Nat × Nat}
    (h : cutScan spineLen sides below width l s fuel cur best work = r) : r.2 ≤ work + fuel :=
  h ▸ cutScan_work_le spineLen sides below width l s fuel cur best work

theorem evalStep_work_le (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (width : Array (Option Nat)) (affected : Array Bool) (st : DictEval) (t : Nat) :
    (evalStep dag family spineLen tail width affected st t).work ≤ st.work + spineLen[t]! + 1 := by
  unfold evalStep
  split
  · dsimp only
    split
    · simp only; omega
    · dsimp only
      exact Nat.add_le_add_right (cutScan_work_le _ _ _ _ _ _ _ _ _ _) 1
  · omega

/-- A range fold whose every step adds at most `B` work adds at most
`count · B`. -/
theorem foldRange_work_le (f : DictEval → Nat → DictEval) (bound B : Nat)
    (step : ∀ st k, k < bound → (f st k).work ≤ st.work + B) :
    ∀ count k st, k + count ≤ bound → (foldRange f k count st).work ≤ st.work + count * B := by
  intro count
  induction count with
  | zero => intro k st _; simp [foldRange]
  | succ count ih =>
    intro k st room
    simp only [foldRange]
    have := ih (k + 1) (f st k) (by omega)
    have := step st k (by omega)
    rw [Nat.succ_mul]
    omega

/-- **A re-evaluation works at most `n · (n + 1)`**: each term once, each
visiting at most its spine. -/
theorem evalUp_work_le {dag : Dag} (hwf : DagWF dag) (ev : DictEval) (width : Array (Option Nat))
    (t : Nat) : ((Prep.ofDag dag).evalUp ev width t).work ≤ dag.size * (dag.size + 1) := by
  have hp := prepWF_ofDag hwf
  unfold Prep.evalUp
  rcases Nat.lt_or_ge dag.size t with outside | inside
  · rw [show (Prep.ofDag dag).dag.size - t = 0 by simp only [ofDag_dag]; omega]
    simp [foldRange]
  have := foldRange_work_le
    (evalStep (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
      (Prep.ofDag dag).tail width (ancestorMarks (Prep.ofDag dag).dag t))
    dag.size (dag.size + 1)
    (fun st k hk => by
      have := evalStep_work_le (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
        (Prep.ofDag dag).tail width (ancestorMarks (Prep.ofDag dag).dag t) st k
      have := hp.spineLen_le k hk
      omega)
    ((Prep.ofDag dag).dag.size - t) t { ev with work := 0 } (by simp only [ofDag_dag]; omega)
  refine Nat.le_trans this ?_
  have := Nat.mul_le_mul_right (dag.size + 1) (show (Prep.ofDag dag).dag.size - t ≤ dag.size by
    simp only [ofDag_dag]; omega)
  simp only
  omega

theorem evalAll_work_le {dag : Dag} (hwf : DagWF dag) (width : Array (Option Nat)) :
    ((Prep.ofDag dag).evalAll width).work ≤ dag.size * (dag.size + 1) := by
  have hp := prepWF_ofDag hwf
  unfold Prep.evalAll Prep.eval evalFrom
  have := foldRange_work_le
    (evalStep (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
      (Prep.ofDag dag).tail width (Array.replicate (Prep.ofDag dag).dag.size true))
    dag.size (dag.size + 1)
    (fun st k hk => by
      have := evalStep_work_le (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
        (Prep.ofDag dag).tail width (Array.replicate (Prep.ofDag dag).dag.size true) st k
      have := hp.spineLen_le k hk
      omega)
    (Prep.ofDag dag).dag.size 0 { (Prep.ofDag dag).empty with work := 0 }
    (by simp only [ofDag_dag]; omega)
  refine Nat.le_trans this ?_
  simp only [ofDag_dag, Nat.zero_add]
  exact Nat.le_refl _

/-- A table step only adds to the predicted length and the work. -/
theorem materializeStep_grows {p : Prep} {table : Array Nat} {limits : Limits} {widthAt : Nat → Nat}
    {st next : TableState} {i : Nat} (h : materializeStep p table limits widthAt st i = .ok next) :
    next.predicted = st.predicted + st.ev.cost[table[i]!]! ∧
      next.work = st.work + st.ev.work + st.ev.cost[table[i]!]! ∧
      next.ev = p.evalUp st.ev (st.width.set! table[i]! (some (widthAt i))) table[i]! := by
  unfold materializeStep at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨e, _, h⟩ := bind_eq_ok h
  split at h
  · cases h
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem materializeFold_grows {p : Prep} {table : Array Nat} {limits : Limits} {widthAt : Nat → Nat} :
    ∀ (l : List Nat) (st final : TableState),
      l.foldlM (materializeStep p table limits widthAt) st = .ok final →
      st.predicted ≤ final.predicted ∧ st.work ≤ final.work
  | [], st, final, h => by cases h; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | i :: l, st, final, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨next, step, rest⟩ := bind_eq_ok h
    obtain ⟨hp, hw, -⟩ := materializeStep_grows step
    have := materializeFold_grows l next final rest
    omega

/-- A table fold that succeeds under one budget succeeds under every budget
that covers its final predicted length and work. -/
theorem materializeFold_down {p : Prep} {table : Array Nat} {widthAt : Nat → Nat} {a b : Limits} :
    ∀ (l : List Nat) (st final : TableState),
      l.foldlM (materializeStep p table a widthAt) st = .ok final →
      final.predicted ≤ b.maxMaterialize → final.work ≤ b.maxMaterializeWork →
      l.foldlM (materializeStep p table b widthAt) st = .ok final
  | [], st, final, h, _, _ => h
  | i :: l, st, final, h, room, roomWork => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨next, step, rest⟩ := bind_eq_ok h
    obtain ⟨hp, hw, -⟩ := materializeStep_grows step
    obtain ⟨gp, gw⟩ := materializeFold_grows l next final rest
    have stepB : materializeStep p table b widthAt st i = .ok next := by
      unfold materializeStep at step ⊢
      dsimp only at step ⊢
      split at step
      · cases step
      rw [ite_eq_right (show ¬ st.ev.cost[table[i]!]! > b.maxMaterialize by omega)]
      obtain ⟨e, built, step⟩ := bind_eq_ok step
      rw [Budget.bind_ok_eq built]
      try dsimp only at step ⊢
      split at step
      · cases step
      rw [ite_eq_right (show ¬ st.work + st.ev.work + st.ev.cost[table[i]!]! > b.maxMaterializeWork by
        omega)]
      exact step
    rw [Budget.bind_ok_eq stepB]
    exact materializeFold_down l next final rest room roomWork

/-- **`materializeTable` succeeds under every budget that covers the
predicted length and the work it returns.** -/
theorem materializeTable_down {p : Prep} {table roots : Array Nat} {widthAt : Nat → Nat}
    {a b : Limits} {es rs : Array Ixon.Expr} {predicted work : Nat}
    (h : materializeTable p table roots a widthAt = .ok (es, rs, predicted, work))
    (room : predicted ≤ b.maxMaterialize) (roomWork : work ≤ b.maxMaterializeWork) :
    materializeTable p table roots b widthAt = .ok (es, rs, predicted, work) := by
  unfold materializeTable at h ⊢
  split at h
  · cases h
  rw [ite_eq_right (by assumption)]
  split at h
  · cases h
  rw [ite_eq_right (by assumption)]
  obtain ⟨final, folded, h⟩ := bind_eq_ok h
  try dsimp only at h
  split at h
  · cases h
  obtain ⟨rs', built, h⟩ := bind_eq_ok h
  try dsimp only at h
  split at h
  · cases h
  cases h
  have rootsEq : rootsCost final.ev.cost roots = roots.foldl (fun acc r => acc + final.ev.cost[r]!) 0 := rfl
  rw [Budget.bind_ok_eq (materializeFold_down _ _ final folded (by rw [rootsEq] at room; omega)
    (by omega))]
  dsimp only
  rw [ite_eq_right (show ¬ roots.foldl (fun acc r => acc + final.ev.cost[r]!) 0 > b.maxMaterialize by
    rw [rootsEq] at room; omega)]
  rw [Budget.bind_ok_eq built]
  try dsimp only
  rw [ite_eq_right (show ¬ final.work + final.ev.work + roots.foldl (fun acc r => acc + final.ev.cost[r]!) 0 >
    b.maxMaterializeWork by omega)]
  rfl

theorem materializeFold_work {dag : Dag} (hwf : DagWF dag) {table : Array Nat} {limits : Limits}
    {widthAt : Nat → Nat} :
    ∀ (l : List Nat) (st final : TableState),
      l.foldlM (materializeStep (Prep.ofDag dag) table limits widthAt) st = .ok final →
      st.ev.work ≤ dag.size * (dag.size + 1) →
      final.ev.work ≤ dag.size * (dag.size + 1) ∧
        final.work + st.predicted ≤ st.work + l.length * (dag.size * (dag.size + 1)) + final.predicted
  | [], st, final, h, start => by cases h; exact ⟨start, by simp⟩
  | i :: l, st, final, h, start => by
    rw [List.foldlM_cons] at h
    obtain ⟨next, step, rest⟩ := bind_eq_ok h
    obtain ⟨hp, hw, hev⟩ := materializeStep_grows step
    have nextWork : next.ev.work ≤ dag.size * (dag.size + 1) := by
      rw [hev]; exact evalUp_work_le hwf _ _ _
    obtain ⟨finalWork, sum⟩ := materializeFold_work hwf l next final rest nextWork
    refine ⟨finalWork, ?_⟩
    simp only [List.length_cons, Nat.succ_mul]
    omega

/-- **The materialization work of a table is at most one evaluation per
entry plus one, and the predicted length.** -/
theorem materializeTable_work_le {dag : Dag} (hwf : DagWF dag) {table roots : Array Nat}
    {limits : Limits} {widthAt : Nat → Nat} {es rs : Array Ixon.Expr} {predicted work : Nat}
    (h : materializeTable (Prep.ofDag dag) table roots limits widthAt = .ok (es, rs, predicted, work)) :
    work ≤ (table.size + 1) * (dag.size * (dag.size + 1)) + predicted := by
  unfold materializeTable at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨final, folded, h⟩ := bind_eq_ok h
  try dsimp only at h
  split at h
  · cases h
  obtain ⟨rs', built, h⟩ := bind_eq_ok h
  try dsimp only at h
  split at h
  · cases h
  cases h
  obtain ⟨finalWork, sum⟩ := materializeFold_work hwf _ _ final folded (evalAll_work_le hwf _)
  simp only [List.length_range] at sum
  have rootsEq : rootsCost final.ev.cost roots = roots.foldl (fun acc r => acc + final.ev.cost[r]!) 0 := rfl
  rw [Nat.succ_mul]
  rw [← rootsEq]
  omega

/-- Expressions have fewer nodes than twice their layout length. -/
theorem layout_nodes (layout : ShareLayout) (es rs : Array Ixon.Expr) :
    (es.toList.map Ix.Sharing.Verify.CanonicalMeaning.nodeCount).sum +
      (rs.toList.map Ix.Sharing.Verify.CanonicalMeaning.nodeCount).sum ≤ 2 * layoutBytes layout es rs := by
  have pos : ∀ i, 1 ≤ layout.widthAt i := fun i => by
    cases layout with
    | tagN => exact Ix.Sharing.Verify.SharingExact.tagNWidth_pos i
  have entries := sum_le_of_le es.toList
    (f := Ix.Sharing.Verify.CanonicalMeaning.nodeCount)
    (g := fun e => 2 * (sizeInfoWith layout.widthAt e).full)
    (fun e _ => by have := nodeCount_lt_size _ pos e; omega)
  have rootSum := sum_le_of_le rs.toList
    (f := Ix.Sharing.Verify.CanonicalMeaning.nodeCount)
    (g := fun e => 2 * (sizeInfoWith layout.widthAt e).full)
    (fun e _ => by have := nodeCount_lt_size _ pos e; omega)
  rw [sum_mul_left] at entries rootSum
  unfold layoutBytes
  simp only
  rw [array_foldl_add_sum, array_foldl_add_sum]
  omega

open Ix.Sharing.Verify.Tiered in
open Ix.Sharing.Verify.SharingExact (materializeTable_backward materializeTable_correct) in
/-- **Re-materialization succeeds under every budget that covers the
phase-1 layout length** for the materialized length and the re-expanded
nodes, plus one evaluation per entry for the materialization work. -/
theorem rematerialize_within {layout : ShareLayout} {ex : Expanded} (ok : ExpandedOK ex)
    (fits : ∀ t, t < ex.dag.size → HeadFits (ex.dag.node t).head)
    (small : ex.dag.size < UInt64.size) {u : UniformSharingResult} (trees : UniformTrees ex u)
    {allocLimits : Limits} {a : Allocation}
    (ha : allocate layout allocLimits ex.dag (graphFacts ex.dag ex.roots).deg u.result.tableTerms
      u.result.sharing u.result.roots = .ok a) (limits : Limits)
    (matRoom : layoutBytes layout u.result.sharing u.result.roots ≤ limits.maxMaterialize)
    (workRoom : (ex.dag.size + 1) * (ex.dag.size * (ex.dag.size + 1)) +
      layoutBytes layout u.result.sharing u.result.roots ≤ limits.maxMaterializeWork)
    (visitRoom : 2 * layoutBytes layout u.result.sharing u.result.roots ≤ limits.maxExprVisits)
    (depthRoom : 2 * layoutBytes layout u.result.sharing u.result.roots ≤ limits.maxDepth)
    (nodeRoom : ex.dag.size + 2 * layoutBytes layout u.result.sharing u.result.roots ≤
      limits.maxNodes) :
    ∃ m, rematerialize layout limits ex a.order
      (layoutBytes layout u.result.sharing u.result.roots) = .ok m := by
  have hwf := ok.wf
  obtain ⟨_, _, hin1, hsize1, _, _, _⟩ := id trees
  obtain ⟨hnd1, -, hperm, -⟩ := allocate_spec ha
  have orderIn : ∀ t ∈ a.order.toList, t < ex.dag.size := fun t ht => hin1 t (hperm.subset ht)
  have orderNodup : a.order.toList.Nodup := hperm.nodup_iff.mpr hnd1
  have orderSize : a.order.size = u.result.tableTerms.size := by
    simpa using hperm.length_eq
  have orderLe : a.order.size ≤ ex.dag.size := by
    have := length_le_of_nodup orderNodup orderIn
    simpa using this
  obtain ⟨first, ⟨entries, rs, predicted, work⟩, hm⟩ := materializeTable_ok hwf layout.widthAt
    (show a.order.size < wordBound by unfold wordBound; omega) orderIn ok.roots
  obtain ⟨-, -, -, predictedEq⟩ := materializeTable_spec hwf ok.roots hm
  have priced : layoutBytes layout entries rs = predicted := by
    rw [layoutBytes_eq, predictedEq]
  have bound := rematerialized_le_of_trees trees ha hm
  have workLe := materializeTable_work_le hwf hm
  have hm' := materializeTable_down hm (b := limits) (by omega)
    (by
      have := Nat.mul_le_mul_right (ex.dag.size * (ex.dag.size + 1))
        (show a.order.size + 1 ≤ ex.dag.size + 1 by omega)
      omega)
  obtain ⟨esSize, backward, rootsBelow⟩ := materializeTable_backward _ _ _ _ _
    (by omega) hm
  obtain ⟨entries', rootRows⟩ := materializeTable_correct _ _ _ _ _ (by omega) hm
    (termOf ex.dag.nodes) (dagModel_termOf hwf)
  have rsSize : rs.size = ex.roots.size := by
    have := (forall₂_getElem rootRows).1
    simpa using this.symm
  have nodes := layout_nodes layout entries rs
  rw [priced, ← rangeNodes_all, ← rangeNodes_all] at nodes
  obtain ⟨visits, reexpanded⟩ := reexpand_ids_within hwf ok.injective orderIn ok.roots esSize rsSize
    backward rootsBelow (entries_forall₂ esSize entries') rootRows (by unfold wordBound; omega) limits
    (by omega) (by omega) (by omega)
  have wire := materializeTable_wire hwf fits small ok.roots hm
  have allWire : ((entries ++ rs).all fun e => (wireCounts e).isSome) = true := by
    rw [Array.all_eq_true']
    intro e he
    exact wire e (by simpa using he)
  unfold rematerialize
  rw [materializeTableOnePass_eq, Budget.bind_ok_eq hm']
  dsimp only
  rw [checkInternal_true _ (by simp [priced]), checkInternal_true _ (by simp [bound])]
  rw [Budget.bind_ok_eq reexpanded]
  dsimp only
  rw [checkInternal_true _ (beq_self_eq_true _), checkInternal_true _ (beq_self_eq_true _),
    checkInternal_true _ allWire]
  exact ⟨_, rfl⟩

/-! ## One width and the family route -/

/-- **One width succeeds under every budget that covers its counts.** -/
theorem familyAtWidth_within (cfg : Config) (layout : ShareLayout) {ex : Expanded} (ok : ExpandedOK ex)
    (fits : ∀ t, t < ex.dag.size → HeadFits (ex.dag.node t).head)
    (small : ex.dag.size < UInt64.size) (candidates : Nat) {width : Nat} (hw : 1 ≤ width)
    (limits : Limits)
    (stateRoom : familyCallTotal cfg (stg width ex).comps.toList ≤ limits.maxStates)
    (tierRoom : (ex.dag.size + 1) ^ 9 ≤ limits.maxStates)
    (workRoom : familyWorkTotal cfg ex (stg width ex) (stg width ex).comps.toList ≤ limits.maxCostEvals)
    (cellRoom : (ex.dag.size + 1) * ex.dag.size ≤ limits.maxKnapsackCells)
    (outputRoom : modelBound ex width ≤ limits.maxOutputBytes)
    (matRoom : 9 * modelBound ex width ≤ limits.maxMaterialize)
    (matWorkRoom : (ex.dag.size + 1) * (ex.dag.size * (ex.dag.size + 1)) + 9 * modelBound ex width ≤
      limits.maxMaterializeWork)
    (visitRoom : 18 * modelBound ex width ≤ limits.maxExprVisits)
    (depthRoom : 18 * modelBound ex width ≤ limits.maxDepth)
    (nodeRoom : ex.dag.size + 18 * modelBound ex width ≤ limits.maxNodes) :
    ∃ out, familyAtWidth cfg layout limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) candidates width = .ok out := by
  have hwf := ok.wf
  obtain ⟨u, hu⟩ := familyUniform_within cfg ok hw (by unfold wordBound; omega) limits stateRoom
    workRoom cellRoom outputRoom (by omega) (by omega) (by omega) (by omega)
  obtain ⟨results, states, work, delta, set, lowerBracket, checked, produced, chosen, -, finish⟩ :=
    familyUniform_finish ok.wf hu
  have selected := familyComponents_least cfg limits ex width hwf checked produced chosen
  have modelEq := (selected_model_nonnegative hwf ok.roots ok.reachable checked selected).2
  have modelLe := selected_ulen_le_modelBound cfg hwf ok.roots ok.reachable checked selected
  have std : uniformFinish width limits ex (Prep.ofDag ex.dag)
      (familyChoice ex width states work delta set lowerBracket) = .ok u := by
    rw [uniformFinish_eq_F]
    exact finish
  obtain ⟨hin, checkedClass, _, htable, modelBytes, work', hmat, _⟩ := uniformFinish_spec std
  have layoutLe := uniformParts_layout_le hw hwf ok.roots hin rfl hmat layout
  have choiceModel : (familyChoice ex width states work delta set lowerBracket).model ≤
      modelBound ex width := by
    change (familyModel ex width delta set).toNat ≤ _
    unfold familyModel
    rw [modelEq]
    exact modelLe
  have storedNodup := (inClass_of_check hin checkedClass).1
  rw [← htable] at hmat
  have tablePerm : u.result.tableTerms.toList.Perm
      (familyChoice ex width states work delta set lowerBracket).stored.toList := by
    rw [htable]; exact pinnedOrder_perm _ _ _
  have tableNodup := tablePerm.nodup_iff.mpr storedNodup
  have tableIn : ∀ t ∈ u.result.tableTerms.toList, t < ex.dag.size :=
    fun t ht => hin t (tablePerm.subset ht)
  have tableSize : u.result.tableTerms.size ≤ ex.dag.size := by
    have := length_le_of_nodup tableNodup tableIn
    simpa using this
  obtain ⟨esSize, refs⟩ := materializeDependent_refs _ _ _ _ _ (dagArity_of hwf) hmat
  have order : ∀ k j (hk : k < u.result.tableTerms.size) (hj : j < u.result.tableTerms.size),
      Below ex.dag u.result.tableTerms[k] u.result.tableTerms[j] → j < k := by
    intro k j hk hj below
    exact Ix.Sharing.Verify.Pinned.pinnedOrder_backward hwf
      (familyChoice ex width states work delta set lowerBracket).facts.deg
      (familyChoice ex width states work delta set lowerBracket).stored hin storedNodup k j
      (by rw [← htable]; exact hk) (by rw [← htable]; exact hj) (by simpa only [htable] using below)
  obtain ⟨a, ha⟩ := Ix.Sharing.Verify.Tiered.allocate_within layout hwf (graphFacts ex.dag ex.roots).deg
    u.result.sharing u.result.roots tableNodup tableIn
    (uniform_deps esSize tableNodup refs order) (limits := limits)
    (Nat.le_trans (Nat.pow_le_pow_left (by omega) 9) tierRoom)
  have trees := uniformTrees_of_finish hwf ok.roots std
  have layoutBound : layoutBytes layout u.result.sharing u.result.roots ≤ 9 * modelBound ex width := by
    have := Nat.mul_le_mul_left 9 choiceModel
    omega
  obtain ⟨m, hm⟩ := rematerialize_within ok fits small trees ha limits (by omega) (by omega)
    (by omega) (by omega) (by omega)
  rw [rematerialize_eq_P] at hm
  unfold familyAtWidth
  rw [Budget.bind_ok_eq hu]
  try dsimp only
  rw [Budget.bind_ok_eq ha]
  try dsimp only
  rw [Budget.bind_ok_eq hm]
  exact ⟨_, rfl⟩

/-- **The family route succeeds under every budget that covers the counts
of its three widths.** -/
theorem familyExpanded_within (cfg : Config) (layout : ShareLayout) {ex : Expanded} (ok : ExpandedOK ex)
    (fits : ∀ t, t < ex.dag.size → HeadFits (ex.dag.node t).head)
    (small : ex.dag.size < UInt64.size) (limits : Limits)
    (stateRoom : ∀ w, familyCallTotal cfg (stg w ex).comps.toList ≤ limits.maxStates)
    (tierRoom : (ex.dag.size + 1) ^ 9 ≤ limits.maxStates)
    (workRoom : ∀ w, familyWorkTotal cfg ex (stg w ex) (stg w ex).comps.toList ≤ limits.maxCostEvals)
    (cellRoom : (ex.dag.size + 1) * ex.dag.size ≤ limits.maxKnapsackCells)
    (outputRoom : modelBound ex 3 ≤ limits.maxOutputBytes)
    (matRoom : 9 * modelBound ex 3 ≤ limits.maxMaterialize)
    (matWorkRoom : (ex.dag.size + 1) * (ex.dag.size * (ex.dag.size + 1)) + 9 * modelBound ex 3 ≤
      limits.maxMaterializeWork)
    (visitRoom : 18 * modelBound ex 3 ≤ limits.maxExprVisits)
    (depthRoom : 18 * modelBound ex 3 ≤ limits.maxDepth)
    (nodeRoom : ex.dag.size + 18 * modelBound ex 3 ≤ limits.maxNodes) :
    ∃ out, familyExpanded cfg layout limits ex = .ok out := by
  let candidates := tieredCandidateCount ex.dag.size (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
  have one := modelBound_mono ex (show 1 ≤ 3 by omega)
  have two := modelBound_mono ex (show 2 ≤ 3 by omega)
  obtain ⟨c1, h1⟩ := familyAtWidth_within cfg layout ok fits small candidates (width := 1) (by omega)
    limits (stateRoom 1) tierRoom (workRoom 1) cellRoom (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  obtain ⟨c2, h2⟩ := familyAtWidth_within cfg layout ok fits small candidates (width := 2) (by omega)
    limits (stateRoom 2) tierRoom (workRoom 2) cellRoom (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  obtain ⟨c3, h3⟩ := familyAtWidth_within cfg layout ok fits small candidates (width := 3) (by omega)
    limits (stateRoom 3) tierRoom (workRoom 3) cellRoom outputRoom matRoom matWorkRoom visitRoom
    depthRoom nodeRoom
  unfold familyExpanded
  rw [Budget.bind_ok_eq (uniformDagChecks_ok ok.wf ok.roots ok.reachable)]
  try dsimp only
  rw [tieredCandidates_eq, Budget.bind_ok_eq h1]
  try dsimp only
  rw [Budget.bind_ok_eq h2]
  try dsimp only
  rw [Budget.bind_ok_eq h3]
  exact ⟨_, rfl⟩

/-! ## The size of the input -/

section InputSize

open Ix.Sharing.Verify.CanonicalMeaning (nodeCount rangeNodes sharesValid_of_free)

/-- The universe arguments of an expression: the total length of its
references' universe vectors. -/
def univCount : Ixon.Expr → Nat
  | .ref _ us => us.size
  | .recur _ us => us.size
  | .prj _ _ v => univCount v
  | .app f a => univCount f + univCount a
  | .lam _ t b => univCount t + univCount b
  | .all _ _ t b => univCount t + univCount b
  | .letE _ t v b => univCount t + univCount v + univCount b
  | _ => 0

/-- **The size of a sharing input**: its expression nodes plus its universe
arguments. -/
def inputSize (roots : Array Ixon.Expr) : Nat :=
  (roots.toList.map fun e => nodeCount e + univCount e).sum

/-- Every reference of an expression carries at most `K` universes. -/
def RefsWithin (K : Nat) : Ixon.Expr → Prop
  | .ref _ us => us.size ≤ K
  | .recur _ us => us.size ≤ K
  | .prj _ _ v => RefsWithin K v
  | .app f a => RefsWithin K f ∧ RefsWithin K a
  | .lam _ t b => RefsWithin K t ∧ RefsWithin K b
  | .all _ _ t b => RefsWithin K t ∧ RefsWithin K b
  | .letE _ t v b => RefsWithin K t ∧ RefsWithin K v ∧ RefsWithin K b
  | _ => True

/-- A reference head carries at most `K` universes. -/
def HeadWithin (K : Nat) : Head → Prop
  | .ref _ us => us.size ≤ K
  | .recur _ us => us.size ≤ K
  | _ => True

theorem refsWithin_univCount (K : Nat) : ∀ e : Ixon.Expr, univCount e ≤ K → RefsWithin K e
  | .ref _ _, h => h
  | .recur _ _, h => h
  | .prj _ _ v, h => refsWithin_univCount K v h
  | .app f a, h => by
    simp only [univCount] at h
    exact ⟨refsWithin_univCount K f (by omega), refsWithin_univCount K a (by omega)⟩
  | .lam _ t b, h => by
    simp only [univCount] at h
    exact ⟨refsWithin_univCount K t (by omega), refsWithin_univCount K b (by omega)⟩
  | .all _ _ t b, h => by
    simp only [univCount] at h
    exact ⟨refsWithin_univCount K t (by omega), refsWithin_univCount K b (by omega)⟩
  | .letE _ t v b, h => by
    simp only [univCount] at h
    exact ⟨refsWithin_univCount K t (by omega), refsWithin_univCount K v (by omega),
      refsWithin_univCount K b (by omega)⟩
  | .sort _, _ | .var _, _ | .str _, _ | .nat _, _ | .share _, _ => trivial

theorem refsWithin_toExpr {K : Nat} (n : Node) (f : Nat → Ixon.Expr) (h : RefsWithin K (n.toExpr f)) :
    HeadWithin K n.head ∧ ∀ k, k < n.head.arity → RefsWithin K (f (n.child k)) := by
  unfold Node.toExpr at h
  cases hh : n.head with
  | ref r us =>
    simp only [hh, RefsWithin] at h
    exact ⟨h, fun k hk => by simp [Head.arity] at hk⟩
  | recur r us =>
    simp only [hh, RefsWithin] at h
    exact ⟨h, fun k hk => by simp [Head.arity] at hk⟩
  | prj t i =>
    simp only [hh, RefsWithin] at h
    refine ⟨trivial, fun k hk => ?_⟩
    simp only [Head.arity] at hk
    obtain rfl : k = 0 := by omega
    exact h
  | app =>
    simp only [hh, RefsWithin] at h
    refine ⟨trivial, fun k hk => ?_⟩
    simp only [Head.arity] at hk
    rcases k with _ | _ | k
    · exact h.1
    · exact h.2
    · omega
  | lam c =>
    simp only [hh, RefsWithin] at h
    refine ⟨trivial, fun k hk => ?_⟩
    simp only [Head.arity] at hk
    rcases k with _ | _ | k
    · exact h.1
    · exact h.2
    · omega
  | all c r =>
    simp only [hh, RefsWithin] at h
    refine ⟨trivial, fun k hk => ?_⟩
    simp only [Head.arity] at hk
    rcases k with _ | _ | k
    · exact h.1
    · exact h.2
    · omega
  | letE c =>
    simp only [hh, RefsWithin] at h
    refine ⟨trivial, fun k hk => ?_⟩
    simp only [Head.arity] at hk
    rcases k with _ | _ | _ | k
    · exact h.1
    · exact h.2.1
    · exact h.2.2
    · omega
  | sort _ | var _ | str _ | nat _ =>
    exact ⟨trivial, fun k hk => by simp [Head.arity] at hk⟩

/-- Every term below a term whose references carry at most `K` universes
has a head that carries at most `K`. -/
theorem headWithin_of_desc {K : Nat} {dag : Dag} (hwf : DagWF dag) :
    ∀ {a b : Nat}, Desc dag a b → RefsWithin K (termOf dag.nodes a) → HeadWithin K (dag.node b).head := by
  intro a b d
  induction d with
  | refl t =>
    intro fit
    rw [Ix.Sharing.Verify.CanonicalMeaning.dagModel_termOf hwf t] at fit
    exact (refsWithin_toExpr _ _ fit).1
  | @child t u k hk rest ih =>
    intro fit
    rw [Ix.Sharing.Verify.CanonicalMeaning.dagModel_termOf hwf t] at fit
    exact ih ((refsWithin_toExpr _ _ fit).2 k (by rw [← dagArity_of hwf t]; exact hk))

theorem headFits_of_within {K : Nat} (small : K < UInt64.size) : ∀ {h : Head}, HeadWithin K h → HeadFits h
  | .ref _ _, w => by simp only [HeadWithin] at w; simp only [HeadFits]; omega
  | .recur _ _, w => by simp only [HeadWithin] at w; simp only [HeadFits]; omega
  | .sort _, _ | .var _, _ | .prj _ _, _ | .str _, _ | .nat _, _ | .app, _ | .lam _, _ | .all _ _, _
  | .letE _, _ => trivial

theorem tag0Size_le_nine (n : Nat) : tag0Size n ≤ 9 := by
  unfold tag0Size Ixon.tagNByteWidth
  repeat' split
  all_goals omega

theorem univIdxsSize_le (us : Array UInt64) : univIdxsSize us ≤ 9 * us.size := by
  unfold univIdxsSize
  rw [← Array.foldl_toList]
  have step : ∀ (l : List UInt64) (acc : Nat),
      l.foldl (fun acc u => acc + tag0Size u.toNat) acc ≤ acc + 9 * l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons u l ih =>
      intro acc
      rw [List.foldl_cons]
      have := ih (acc + tag0Size u.toNat)
      have := tag0Size_le_nine u.toNat
      simp only [List.length_cons]
      omega
  have := step us.toList 0
  simpa using this

theorem ownBytes_le {K : Nat} : ∀ {h : Head}, HeadWithin K h → h.ownBytes ≤ 18 + 9 * K
  | .ref r us, w => by
    simp only [HeadWithin] at w
    have := tag4Size_le_nine us.size
    have := tag0Size_le_nine r.toNat
    have := univIdxsSize_le us
    simp only [Head.ownBytes]
    omega
  | .recur r us, w => by
    simp only [HeadWithin] at w
    have := tag4Size_le_nine us.size
    have := tag0Size_le_nine r.toNat
    have := univIdxsSize_le us
    simp only [Head.ownBytes]
    omega
  | .sort i, _ => by have := tag4Size_le_nine i.toNat; simp only [Head.ownBytes]; omega
  | .var i, _ => by have := tag4Size_le_nine i.toNat; simp only [Head.ownBytes]; omega
  | .prj t f, _ => by
    have := tag4Size_le_nine f.toNat
    have := tag0Size_le_nine t.toNat
    simp only [Head.ownBytes]
    omega
  | .str i, _ => by have := tag4Size_le_nine i.toNat; simp only [Head.ownBytes]; omega
  | .nat i, _ => by have := tag4Size_le_nine i.toNat; simp only [Head.ownBytes]; omega
  | .letE c, _ => by have := tag4Size_le_nine c.flags.toNat; simp only [Head.ownBytes]; omega
  | .app, _ | .lam _, _ | .all _ _, _ => by simp only [Head.ownBytes]; omega

theorem sideExtra_le (n : Node) : n.sideExtra ≤ 1 := by
  unfold Node.sideExtra
  split <;> omega

theorem arity_le_three (h : Head) : h.arity ≤ 3 := by
  cases h <;> simp [Head.arity]

theorem sum_range_le_mul (c : Nat) (f : Nat → Nat) :
    ∀ n, (∀ t, t < n → f t ≤ c) → ((List.range n).map f).sum ≤ n * c
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    have := sum_range_le_mul c f n (fun t ht => h t (by omega))
    have := h n (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.succ_mul]
    omega

theorem length_le_sum {α : Type} (f : α → Nat) :
    ∀ (l : List α), (∀ a ∈ l, 1 ≤ f a) → l.length ≤ (l.map f).sum
  | [], _ => by simp
  | a :: l, h => by
    have := length_le_sum f l (fun b hb => h b (by simp [hb]))
    have := h a (by simp)
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem le_sum_of_mem {α : Type} (f : α → Nat) {a : α} :
    ∀ {l : List α}, a ∈ l → f a ≤ (l.map f).sum
  | b :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_sum_of_mem f h
      omega

theorem forall₂_length {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → xs.length = ys.length
  | _, _, .nil => rfl
  | _, _, .cons _ rest => by simp only [List.length_cons, forall₂_length rest]

theorem nodeCount_pos (e : Ixon.Expr) : 1 ≤ nodeCount e := by
  cases e <;> simp only [nodeCount] <;> omega

/-- **The model length is quadratic in the input**: `modelBound` counts
each term's payload (at most `28 + 9K` bytes when references carry at most
`K` universes), and `2·width` per root and child edge (at most three per
term). -/
theorem modelBound_le (ex : Expanded) (wf : DagWF ex.dag) {K : Nat}
    (heads : ∀ t, t < ex.dag.size → HeadWithin K (ex.dag.node t).head) (width : Nat) :
    modelBound ex width ≤
      9 + ex.dag.size * (28 + 9 * K) + 2 * width * (ex.roots.size + ex.dag.size * 3) := by
  unfold modelBound
  have tag := tag0Size_le_nine ex.dag.size
  have payload := sum_range_le_mul (28 + 9 * K) (fun t => residualLocalPayload ex t) ex.dag.size
    (fun t ht => by
      have := ownBytes_le (heads t ht)
      have := sideExtra_le (ex.dag.node t)
      unfold residualLocalPayload
      omega)
  have edges := sum_range_le_mul 3 (fun t => (ex.dag.node t).children.size) ex.dag.size
    (fun t _ => by rw [dagArity_of wf t]; exact arity_le_three _)
  have := Nat.mul_le_mul_left (2 * width) (Nat.add_le_add_left edges ex.roots.size)
  omega

end InputSize

/-! ## The family counts -/

theorem sizes_modify_push (t : Nat) : ∀ (l : List (Array Nat)) (i : Nat),
    ((l.modify i (·.push t)).map Array.size).sum ≤ (l.map Array.size).sum + 1
  | [], _ => by simp
  | a :: l, 0 => by
    simp only [List.modify_zero_cons, List.map_cons, List.sum_cons, Array.size_push]
    omega
  | a :: l, i + 1 => by
    have := sizes_modify_push t l i
    simp only [List.modify_succ_cons, List.map_cons, List.sum_cons]
    omega

/-- The groups hold at most `n` terms in all. -/
theorem groupByRoot_members (n : Nat) (cls : Array UClass) (root : Nat → Nat) :
    ((groupByRoot n cls root).toList.map Array.size).sum ≤ n := by
  unfold groupByRoot
  have step : ∀ (l : List Nat) (acc : Array (Option Nat) × Array (Array Nat)),
      ((l.foldl (groupStep cls root) acc).2.toList.map Array.size).sum ≤
        (acc.2.toList.map Array.size).sum + l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons t l ih =>
      intro acc
      rw [List.foldl_cons]
      have rest := ih (groupStep cls root acc t)
      have one : ((groupStep cls root acc t).2.toList.map Array.size).sum ≤
          (acc.2.toList.map Array.size).sum + 1 := by
        unfold groupStep
        split
        · split
          · simp only [Array.toList_modify]
            exact sizes_modify_push t _ _
          · simp
        · simp
      simp only [List.length_cons]
      omega
  have := step (List.range n) (Array.replicate n none, #[])
  simpa using this

theorem comps_members_le (width : Nat) (ex : Expanded) :
    ((stg width ex).comps.toList.map Array.size).sum ≤ ex.dag.size := by
  have comps : (stg width ex).comps = uncertainComponents ex.dag (stg width ex).cls := rfl
  rw [comps]
  exact groupByRoot_members _ _ _

theorem closure_size_le (ex : Expanded) (sg : UStage) (members : Array Nat) :
    (componentContext ex sg members).closure.size ≤ ex.dag.size := by
  change (upClosure ex.dag _).size ≤ _
  unfold upClosure
  exact Nat.le_trans Array.size_filter_le (by simp)

theorem familyCalls_le (cfg : Config) {m n : Nat} (hm : m ≤ n) :
    familyCalls cfg m ≤ 2 ^ cfg.exactLimit * (n + 1) * (m + 1) := by
  have pos : 1 ≤ 2 ^ cfg.exactLimit := Nat.one_le_two_pow
  have sq : (m + 1) * (m + 1) ≤ (n + 1) * (m + 1) := Nat.mul_le_mul_right _ (by omega)
  have one : 1 ≤ (n + 1) * (m + 1) := Nat.mul_pos (by omega) (by omega)
  have scaled : (n + 1) * (m + 1) ≤ 2 ^ cfg.exactLimit * ((n + 1) * (m + 1)) :=
    Nat.le_mul_of_pos_left _ pos
  have top : 2 ^ cfg.exactLimit ≤ 2 ^ cfg.exactLimit * ((n + 1) * (m + 1)) :=
    Nat.le_mul_of_pos_right _ one
  rw [Nat.mul_assoc]
  unfold familyCalls
  split
  · have := Nat.pow_le_pow_right (show 0 < 2 by omega) (by assumption : m ≤ cfg.exactLimit)
    omega
  · have expand : (m + 1) * (m + 1) = m * (m + 1) + (m + 1) := Nat.succ_mul m (m + 1)
    have := Nat.div_le_self (m * (m + 1)) 2
    omega

theorem familyStoredSum_le (cfg : Config) {m n : Nat} (hm : m ≤ n) :
    familyStoredSum cfg m ≤ 2 ^ cfg.exactLimit * ((n + 1) * (n + 1)) * (m + 1) := by
  have pos : 1 ≤ 2 ^ cfg.exactLimit := Nat.one_le_two_pow
  have square : 1 ≤ (n + 1) * (n + 1) := Nat.mul_pos (by omega) (by omega)
  have big : m + 1 ≤ (n + 1) * (n + 1) * (m + 1) := Nat.le_mul_of_pos_left _ square
  have scaled : (n + 1) * (n + 1) * (m + 1) ≤ 2 ^ cfg.exactLimit * ((n + 1) * (n + 1) * (m + 1)) :=
    Nat.le_mul_of_pos_left _ pos
  rw [Nat.mul_assoc]
  unfold familyStoredSum
  split
  · have powLe := Nat.pow_le_pow_right (show 0 < 2 by omega)
      (show m - 1 ≤ cfg.exactLimit by omega)
    have := Nat.mul_le_mul (show m ≤ (n + 1) * (n + 1) * (m + 1) by omega) powLe
    rw [Nat.mul_comm ((n + 1) * (n + 1) * (m + 1))] at this
    omega
  · have e1 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    have e2 : m * (m + 2) = m * m + 2 * m := by
      simp only [Nat.mul_add]
      omega
    have inner : m * (m + 2) ≤ (n + 1) * (n + 1) := by
      have := Nat.mul_le_mul (show m + 1 ≤ n + 1 by omega) (show m + 1 ≤ n + 1 by omega)
      omega
    have cube : m * (m + 1) * (m + 2) ≤ (n + 1) * (n + 1) * (m + 1) := by
      rw [Nat.mul_right_comm]
      exact Nat.mul_le_mul_right _ inner
    have mlt : m ≤ (n + 1) * (n + 1) := by
      have := Nat.mul_le_mul (show 1 ≤ n + 1 by omega) (show m ≤ n + 1 by omega)
      omega
    have pair : m * (m + 1) ≤ (n + 1) * (n + 1) * (m + 1) := Nat.mul_le_mul_right _ mlt
    have := Nat.div_le_self (m * (m + 1) * (m + 2)) 6
    have := Nat.div_le_self (m * (m + 1)) 2
    omega

theorem familyWork_le (cfg : Config) {m cl n : Nat} (hm : m ≤ n) (hc : cl ≤ n) :
    familyWork cfg m cl ≤ 3 * (2 ^ cfg.exactLimit * ((n + 1) * (n + 1))) * (m + 1) := by
  have calls := familyCalls_le cfg hm
  have stored := familyStoredSum_le cfg hm
  have pos : 1 ≤ 2 ^ cfg.exactLimit := Nat.one_le_two_pow
  unfold familyWork
  have times := Nat.mul_le_mul (Nat.add_le_add_right calls 1) hc
  have split : (2 ^ cfg.exactLimit * (n + 1) * (m + 1) + 1) * n =
      2 ^ cfg.exactLimit * ((n + 1) * n) * (m + 1) + n := by
    rw [Nat.add_mul, Nat.one_mul]
    congr 1
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have shrink : 2 ^ cfg.exactLimit * ((n + 1) * n) * (m + 1) ≤
      2 ^ cfg.exactLimit * ((n + 1) * (n + 1)) * (m + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
  have small : n ≤ 2 ^ cfg.exactLimit * ((n + 1) * (n + 1)) * (m + 1) := by
    have a : n ≤ (n + 1) * (n + 1) := by
      have := Nat.mul_le_mul (show 1 ≤ n + 1 by omega) (show n ≤ n + 1 by omega)
      omega
    have b := Nat.le_mul_of_pos_left ((n + 1) * (n + 1)) pos
    have c := Nat.le_mul_of_pos_right (2 ^ cfg.exactLimit * ((n + 1) * (n + 1)))
      (show 0 < m + 1 by omega)
    omega
  rw [Nat.mul_assoc 3]
  omega

theorem sum_comps_le (C : Nat) (f : Array Nat → Nat) :
    ∀ (comps : List (Array Nat)), (∀ c ∈ comps, f c ≤ C * (c.size + 1)) →
      (comps.map f).sum ≤ C * ((comps.map Array.size).sum + comps.length)
  | [], _ => by simp
  | c :: cs, h => by
    have rest := sum_comps_le C f cs (fun d hd => h d (by simp [hd]))
    have head := h c (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have : C * (c.size + (cs.map Array.size).sum + (cs.length + 1)) =
        C * (c.size + 1) + C * ((cs.map Array.size).sum + cs.length) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    omega

/-- **The component loop makes at most `2^(K+1)·(N+1)²` calls** on a DAG of
at most `N` terms, with exhaustive search up to `K` members. -/
theorem familyCallTotal_le (cfg : Config) (ex : Expanded) (width : Nat) {N : Nat}
    (hn : ex.dag.size ≤ N) :
    familyCallTotal cfg (stg width ex).comps.toList ≤
      2 ^ (cfg.exactLimit + 1) * ((N + 1) * (N + 1)) := by
  have total := comps_members_le width ex
  have count := comps_size_le width ex
  have sum := sum_comps_le (2 ^ cfg.exactLimit * (N + 1)) (fun c => familyCalls cfg c.size)
    (stg width ex).comps.toList (fun c hc => by
      have := le_sum_of_mem Array.size hc
      exact familyCalls_le cfg (show c.size ≤ N by omega))
  have room := Nat.mul_le_mul_left (2 ^ cfg.exactLimit * (N + 1))
    (show ((stg width ex).comps.toList.map Array.size).sum + (stg width ex).comps.toList.length ≤
      2 * (N + 1) by simp only [Array.length_toList]; omega)
  have eq : 2 ^ cfg.exactLimit * (N + 1) * (2 * (N + 1)) =
      2 ^ (cfg.exactLimit + 1) * ((N + 1) * (N + 1)) := by
    rw [Nat.pow_succ]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  unfold familyCallTotal
  omega

/-- **The component loop works at most `6·2^K·(N+1)³`**: each component's
calls over its upward closure (at most `N` terms). -/
theorem familyWorkTotal_le (cfg : Config) (ex : Expanded) (width : Nat) {N : Nat}
    (hn : ex.dag.size ≤ N) :
    familyWorkTotal cfg ex (stg width ex) (stg width ex).comps.toList ≤
      6 * 2 ^ cfg.exactLimit * ((N + 1) * (N + 1) * (N + 1)) := by
  have total := comps_members_le width ex
  have count := comps_size_le width ex
  have sum := sum_comps_le (3 * (2 ^ cfg.exactLimit * ((N + 1) * (N + 1))))
    (fun members => familyWork cfg members.size (componentContext ex (stg width ex) members).closure.size)
    (stg width ex).comps.toList (fun c hc => by
      have := le_sum_of_mem Array.size hc
      have := closure_size_le ex (stg width ex) c
      exact familyWork_le cfg (show c.size ≤ N by omega) (by omega))
  have room := Nat.mul_le_mul_left (3 * (2 ^ cfg.exactLimit * ((N + 1) * (N + 1))))
    (show ((stg width ex).comps.toList.map Array.size).sum + (stg width ex).comps.toList.length ≤
      2 * (N + 1) by simp only [Array.length_toList]; omega)
  have eq : 3 * (2 ^ cfg.exactLimit * ((N + 1) * (N + 1))) * (2 * (N + 1)) =
      6 * 2 ^ cfg.exactLimit * ((N + 1) * (N + 1) * (N + 1)) := by
    rw [show (6 : Nat) = 3 * 2 from rfl]
    ac_rfl
  unfold familyWorkTotal
  omega

/-! ## The budget -/

/-- **A sufficient budget for an input of size `N`**, polynomial in `N`
(`B = N + 1`): quadratic in the walked nodes and the lengths, cubic in the
component and materialization work, and `B^9` in the first-tier states. The
production rule does not use the transition count or the exhaustive oracle,
and gets none of them. -/
def limitsFor (N : Nat) : Limits :=
  let B := N + 1
  { maxExprVisits := 2 ^ 11 * B ^ 2
    maxDepth := 2 ^ 11 * B ^ 2
    maxNodes := 2 ^ 12 * B ^ 2
    maxStates := 2 ^ 17 * B ^ 9
    maxKnapsackCells := B ^ 2
    maxTransitions := 0
    maxCostEvals := 2 ^ 19 * B ^ 3
    maxOutputBytes := 2 ^ 6 * B ^ 2
    maxMaterialize := 2 ^ 10 * B ^ 2
    maxMaterializeWork := 2 ^ 11 * B ^ 3
    maxOracleTables := 0
    maxOracleVariants := 0 }

open Ix.Sharing.Verify.CanonicalMeaning (nodeCount sharesValid_of_free expand_within expand_facts) in
/-- **The production rule succeeds under `limitsFor N`** on Share-free roots
whose size (expression nodes plus universe arguments) is at most
`N < 2^64`. -/
theorem canonicalSharingTiered_limitsFor (layout : ShareLayout) (roots : Array Ixon.Expr)
    (free : ∀ i, i < roots.size → Ix.Sharing.Verify.CanonicalMeaning.ShareFree roots[i]!)
    {N : Nat} (size : inputSize roots ≤ N) (small : N < UInt64.size) :
    ∃ out, canonicalSharingTiered layout roots (limitsFor N) = .ok out := by
  unfold inputSize at size
  have nodesLe : (roots.toList.map nodeCount).sum ≤ N := by
    have := sum_le_of_le roots.toList (f := nodeCount) (g := fun e => nodeCount e + univCount e)
      (fun e _ => by omega)
    omega
  have sq : (N + 1) ^ 2 = (N + 1) * (N + 1) := Nat.pow_two _
  have cube : (N + 1) ^ 3 = (N + 1) * (N + 1) * (N + 1) := by rw [Nat.pow_succ, Nat.pow_two]
  have sqExpand : (N + 1) * (N + 1) = N * N + 2 * N + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  have sqCube : (N + 1) * (N + 1) ≤ (N + 1) * (N + 1) * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have zero : rangeNodes (#[] : Array Ixon.Expr) 0 (#[] : Array Ixon.Expr).size = 0 := rfl
  have total : rangeNodes roots 0 roots.size ≤ N := by rw [rangeNodes_all]; exact nodesLe
  obtain ⟨ex, ran, dagSize⟩ := expand_within #[] roots false (by simp [wordBound])
    (fun index bound => absurd bound (by simp))
    (fun index bound resolved _ => sharesValid_of_free _ _ (free index bound)) (limitsFor N)
    (by change _ ≤ 2 ^ 11 * (N + 1) ^ 2; omega)
    (by change _ ≤ 2 ^ 11 * (N + 1) ^ 2; omega)
    (by change _ ≤ 2 ^ 12 * (N + 1) ^ 2; omega)
  have n : ex.dag.size ≤ N := by omega
  have ok := expand_facts ran
  obtain ⟨-, -, rows⟩ := Ix.Sharing.Verify.CanonicalMeaning.expand_unshared _ roots ex ran
  have heads : ∀ t, t < ex.dag.size → HeadWithin N (ex.dag.node t).head := by
    intro t ht
    obtain ⟨r, hr, desc⟩ := ok.reachable t ht
    obtain ⟨source, hs, rel⟩ := forall₂_mem_right' rows r hr
    refine headWithin_of_desc ok.wf desc ?_
    rw [rel.2]
    apply refsWithin_univCount
    have := le_sum_of_mem (fun e => nodeCount e + univCount e) hs
    omega
  have fits : ∀ t, t < ex.dag.size → HeadFits (ex.dag.node t).head :=
    fun t ht => headFits_of_within small (heads t ht)
  have rootsLe : ex.roots.size ≤ N := by
    have lengths := forall₂_length rows
    simp only [Array.length_toList] at lengths
    have := length_le_sum nodeCount roots.toList (fun e _ => nodeCount_pos e)
    simp only [Array.length_toList] at this
    omega
  have model : modelBound ex 3 ≤ 64 * ((N + 1) * (N + 1)) := by
    have bound := modelBound_le ex ok.wf heads 3
    have scale := Nat.mul_le_mul_right (28 + 9 * N) n
    have expand : N * (28 + 9 * N) = N * 28 + 9 * (N * N) := by
      rw [Nat.mul_add, Nat.mul_left_comm]
    omega
  have cfgLimit : canonicalFamilyConfig.exactLimit = 16 := rfl
  have sqNine : (N + 1) ^ 2 ≤ (N + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have work : (ex.dag.size + 1) * (ex.dag.size * (ex.dag.size + 1)) ≤ (N + 1) * (N + 1) * (N + 1) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
  obtain ⟨out, h⟩ := familyExpanded_within canonicalFamilyConfig layout ok fits (by omega) (limitsFor N)
    (fun w => by
      have := familyCallTotal_le canonicalFamilyConfig ex w n
      rw [cfgLimit] at this
      change _ ≤ 2 ^ 17 * (N + 1) ^ 9
      have := Nat.mul_le_mul_left (2 ^ 17) sqNine
      omega)
    (by
      change _ ≤ 2 ^ 17 * (N + 1) ^ 9
      have := Nat.pow_le_pow_left (show ex.dag.size + 1 ≤ N + 1 by omega) 9
      have := Nat.le_mul_of_pos_left ((N + 1) ^ 9) (show 0 < 2 ^ 17 by omega)
      omega)
    (fun w => by
      have := familyWorkTotal_le canonicalFamilyConfig ex w n
      rw [cfgLimit] at this
      change _ ≤ 2 ^ 19 * (N + 1) ^ 3
      omega)
    (by
      change _ ≤ (N + 1) ^ 2
      have := Nat.mul_le_mul (show ex.dag.size + 1 ≤ N + 1 by omega) (show ex.dag.size ≤ N + 1 by omega)
      omega)
    (by change _ ≤ 2 ^ 6 * (N + 1) ^ 2; omega)
    (by change _ ≤ 2 ^ 10 * (N + 1) ^ 2; omega)
    (by change _ ≤ 2 ^ 11 * (N + 1) ^ 3; omega)
    (by change _ ≤ 2 ^ 11 * (N + 1) ^ 2; omega)
    (by change _ ≤ 2 ^ 11 * (N + 1) ^ 2; omega)
    (by change _ ≤ 2 ^ 12 * (N + 1) ^ 2; omega)
  refine ⟨out, ?_⟩
  unfold canonicalSharingTiered
  rw [Budget.bind_ok_eq ran, Ix.Sharing.Family.familyReferenceExpanded_eq_cached]
  exact h

/-- **Every budget above `limitsFor N` admits the input**, with the same
output. -/
theorem canonicalSharingTiered_above (layout : ShareLayout) (roots : Array Ixon.Expr)
    (free : ∀ i, i < roots.size → Ix.Sharing.Verify.CanonicalMeaning.ShareFree roots[i]!)
    {N : Nat} (size : inputSize roots ≤ N) (small : N < UInt64.size) {limits : Limits}
    (le : Budget.LimitsLe (limitsFor N) limits) :
    ∃ out, canonicalSharingTiered layout roots (limitsFor N) = .ok out ∧
      canonicalSharingTiered layout roots limits = .ok out := by
  obtain ⟨out, h⟩ := canonicalSharingTiered_limitsFor layout roots free size small
  exact ⟨out, h, Budget.canonicalSharingTiered_mono le layout roots h⟩


end Ix.Sharing.Verify.Totality

#guard_kernel_axioms Ix.Sharing.Family.groupByRoot_size [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.knapsackCells_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.uniformFinishF_within [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.familyUniform_within [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.evalUp_work_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.evalAll_work_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.materializeTable_down [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.materializeTable_work_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.layout_nodes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.rematerialize_within [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.familyAtWidth_within [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.familyExpanded_within [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.headWithin_of_desc [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.modelBound_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.groupByRoot_members [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.familyCallTotal_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.familyWorkTotal_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.canonicalSharingTiered_limitsFor [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.canonicalSharingTiered_above [propext, Classical.choice, Quot.sound]
