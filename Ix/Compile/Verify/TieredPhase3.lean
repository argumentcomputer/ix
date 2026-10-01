import Ix.Compile.Verify.TieredModel
import Ix.Compile.Verify.TieredTier

/-!
# Tiered construction, phase 3: re-materialization

`materializeTable` writes table entry `k` against the dictionary of the
entries before it and the roots against the whole table, every Share priced
by the layout width of its index. Each part it writes is a minimum for its
dictionary at those widths: its layout length is `gCost` of the part's term
under that dictionary (`materializeTable_spec`), which is the minimum length
over all writings of the term with that dictionary, and is attained
(`materializeTable_min`). The predicted length is the layout length of the
output.

For the tiered construction (`rematerialize_spec`): the parts are minimal
as above, the output expands to the same terms (entry `k` to `order[k]`,
the roots to the input roots), entry `k` only references entries below `k`,
and the layout length is at most the phase-1 candidate's layout length.
Each part is exact for its dictionary; the composition of the phases is NOT
claimed to be a global byte minimum.
-/

namespace Ix.Compile.Verify.Tiered

open Ix.Sharing.Exact
open Ix.Compile.Verify.UniformModel
open Ix.Compile.Verify.SharingExact (bind_eq_ok indexOfPrefix_succ indexOfPrefix_zero
  foldlM_range_inv materializeStep_spec materializeTable_parts toNat_toUInt64_of_lt
  indexOfPrefix_spec mapM_ok_forall₂ forall₂_getElem)

/-! ## The prefix dictionaries -/

/-- The terms of the first `k` table entries. -/
def prefixAvail (n : Nat) (table : Array Nat) (k u : Nat) : Bool :=
  ((indexOfPrefix n table k)[u]?.getD none).isSome

/-- Their Share widths: the layout width of the entry's index. -/
def prefixWd (n : Nat) (table : Array Nat) (widthAt : Nat → Nat) (k u : Nat) : Nat :=
  match (indexOfPrefix n table k)[u]?.getD none with
  | some i => widthAt i
  | none => 0

theorem prefix_width (n : Nat) (table : Array Nat) (widthAt : Nat → Nat) (k u : Nat) :
    widthOf ((indexOfPrefix n table k).map (·.map widthAt)) u =
      if prefixAvail n table k u then some (prefixWd n table widthAt k u) else none := by
  rw [widthOf_eq]
  unfold prefixAvail prefixWd
  simp only [getElem!_def, Array.getElem?_map]
  cases h : (indexOfPrefix n table k)[u]? with
  | none => rfl
  | some o => cases o <;> simp

theorem prefix_succ_agree (n : Nat) (table : Array Nat) (widthAt : Nat → Nat) {k : Nat}
    (hk : k < table.size) (v : Nat) (hv : v ≠ table[k]!) :
    prefixAvail n table (k + 1) v = prefixAvail n table k v ∧
      prefixWd n table widthAt (k + 1) v = prefixWd n table widthAt k v := by
  unfold prefixAvail prefixWd
  rw [indexOfPrefix_succ n table hk]
  simp [Array.set!, Ne.symm hv]

/-- The index bound of a prefix dictionary. -/
theorem prefix_index_lt {n : Nat} {table : Array Nat} {k u i : Nat}
    (h : (indexOfPrefix n table k)[u]?.getD none = some i) : i < k :=
  (indexOfPrefix_spec n table k u i h).1

/-! ## The table loop -/

/-- The table loop after `k` entries: the dictionary is the prefix
dictionary of the first `k` entries, the evaluation gives its model rows,
every entry so far has the layout length of its model cost under its own
prefix dictionary, and the predicted length is the count plus those. -/
def TableEvInv (dag : Dag) (table : Array Nat) (widthAt : Nat → Nat) (k : Nat)
    (st : TableState) : Prop :=
  k ≤ table.size ∧ st.index = indexOfPrefix dag.size table k ∧
    st.width = (indexOfPrefix dag.size table k).map (·.map widthAt) ∧
    GEvalOK (Prep.ofDag dag) (prefixWd dag.size table widthAt k) (prefixAvail dag.size table k)
      st.ev ∧
    st.entries.size = k ∧
    (∀ j (hj : j < st.entries.size), (sizeInfoWith widthAt st.entries[j]).full =
      gCost (Prep.ofDag dag) (prefixWd dag.size table widthAt j) (prefixAvail dag.size table j)
        table[j]!) ∧
    st.predicted = tag0Size table.size +
      ((List.range k).map fun j => gCost (Prep.ofDag dag) (prefixWd dag.size table widthAt j)
        (prefixAvail dag.size table j) table[j]!).sum

/-- The layout length of an expression built against a prefix dictionary is
the model cost there. -/
theorem build_prefix_size {dag : Dag} (hwf : DagWF dag) {table : Array Nat}
    (hsize : table.size < UInt64.size) (widthAt : Nat → Nat) {k : Nat} (hk : k ≤ table.size)
    {ev : DictEval}
    (hev : GEvalOK (Prep.ofDag dag) (prefixWd dag.size table widthAt k)
      (prefixAvail dag.size table k) ev)
    {t : Nat} (ht : t < dag.size) {e : Ixon.Expr}
    (h : (Prep.ofDag dag).build ev (indexOfPrefix dag.size table k)
      ((indexOfPrefix dag.size table k).map (·.map widthAt)) false (dag.size + 1) t = .ok e) :
    (sizeInfoWith widthAt e).full =
      gCost (Prep.ofDag dag) (prefixWd dag.size table widthAt k) (prefixAvail dag.size table k) t := by
  have hp := prepWF_ofDag hwf
  have := (hp.gBuild_size ev hev (indexOfPrefix dag.size table k)
    ((indexOfPrefix dag.size table k).map (·.map widthAt))
    (prefix_width dag.size table widthAt k) (fun u => rfl) widthAt (fun u i hi => ⟨by
      have := prefix_index_lt hi; omega, by unfold prefixWd; rw [hi]⟩)
    (dag.size + 1) false t e ht h).1
  simpa using this

theorem tableEvInv_step {dag : Dag} (hwf : DagWF dag) {table : Array Nat} {limits : Limits}
    {widthAt : Nat → Nat} (hsize : table.size < UInt64.size)
    (hrange : ∀ k, k < table.size → table[k]! < dag.size) {i : Nat} {st st' : TableState}
    (hI : TableEvInv dag table widthAt i st) (hi : i < table.size)
    (h : materializeStep (Prep.ofDag dag) table limits widthAt st i = .ok st') :
    TableEvInv dag table widthAt (i + 1) st' := by
  obtain ⟨_, hidx, hwid, hev, hsz, hent, hpred⟩ := hI
  obtain ⟨e, he, hent', hidx', hwid', hev', hpred', -⟩ := materializeStep_spec h
  have hsucc := indexOfPrefix_succ dag.size table hi
  have ht := hrange i hi
  have hwidth' : st.width.set! table[i]! (some (widthAt i)) =
      (indexOfPrefix dag.size table (i + 1)).map (·.map widthAt) := by
    rw [hwid, hsucc]
    simp [Array.set!, Array.map_setIfInBounds]
  have hsize_e : (sizeInfoWith widthAt e).full = gCost (Prep.ofDag dag)
      (prefixWd dag.size table widthAt i) (prefixAvail dag.size table i) table[i]! := by
    rw [hidx, hwid] at he
    exact build_prefix_size hwf hsize widthAt (by omega) hev ht he
  refine ⟨by omega, by rw [hidx', hidx, hsucc], by rw [hwid', hwidth'], ?_, ?_, ?_, ?_⟩
  · rw [hev', hwidth']
    exact evalUp_ok hwf hev ht (fun v hv => prefix_succ_agree dag.size table widthAt hi v hv) _
      (prefix_width dag.size table widthAt (i + 1))
  · rw [hent']; simp [hsz]
  · intro j hj
    have hj2 : j < (st.entries.push e).size := hent' ▸ hj
    have heq : st'.entries[j] = (st.entries.push e)[j] := by simp only [hent']
    rw [heq]
    by_cases hji : j < st.entries.size
    · rw [Array.getElem_push_lt hji]
      exact hent j hji
    · have : j = st.entries.size := by simp at hj2; omega
      simp only [this, Array.getElem_push_eq]
      rw [hsz]
      exact hsize_e
  · rw [hpred', hpred, List.range_succ, List.map_append, List.sum_append, hev.cost]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem tableEvInv_loop {dag : Dag} (hwf : DagWF dag) {table : Array Nat} {limits : Limits}
    {widthAt : Nat → Nat} (hsize : table.size < UInt64.size)
    (hrange : ∀ k, k < table.size → table[k]! < dag.size) {st : TableState}
    (h : (List.range table.size).foldlM (materializeStep (Prep.ofDag dag) table limits widthAt)
        { entries := #[], index := Array.replicate (Prep.ofDag dag).dag.size none,
          width := Array.replicate (Prep.ofDag dag).dag.size none,
          ev := (Prep.ofDag dag).evalAll (Array.replicate (Prep.ofDag dag).dag.size none),
          predicted := tag0Size table.size, work := 0 } = .ok st) :
    TableEvInv dag table widthAt table.size st := by
  have hp := prepWF_ofDag hwf
  refine foldlM_range_inv _ (fun k st => k ≤ table.size → TableEvInv dag table widthAt k st)
    (fun i s s' hI hs hle => tableEvInv_step hwf hsize hrange (hI (by omega)) (by omega) hs)
    table.size _ st (fun _ => ?_) h (Nat.le_refl _)
  have hidx0 := indexOfPrefix_zero dag.size table
  refine ⟨Nat.zero_le _, by rw [hidx0]; rfl, by rw [hidx0]; simp; rfl, ?_, rfl,
    fun j hj => absurd hj (by simp), by simp⟩
  refine hp.evalAll_ok (ofDag_empty_size dag) _ fun u => ?_
  rw [widthOf_eq]
  unfold prefixAvail
  rw [hidx0]
  simp only [ofDag_dag]
  by_cases hu : u < dag.size
  · simp [hu]
  · simp [hu]; rfl

theorem forall₂_imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      (∀ a ∈ xs, ∀ b, R a b → S a b) → List.Forall₂ S xs ys
  | _, _, .nil, _ => .nil
  | _, _, .cons hr hs, h => .cons (h _ List.mem_cons_self _ hr)
      (forall₂_imp_mem hs fun a ha b hab => h a (List.mem_cons_of_mem _ ha) b hab)

theorem sum_range_eq {α : Type} (g : α → Nat) (arr : Array α) {f : Nat → Nat}
    (h : ∀ j (hj : j < arr.size), f j = g arr[j]) :
    ((List.range arr.size).map f).sum = (arr.toList.map g).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  exact h j (by simpa using h1)

/-! ## The materialized table -/

/-- **Re-materialization lengths.** A successful `materializeTable` over a
canonical DAG writes every entry `k` with the layout length `gCost` of
`table[k]` under the dictionary of the entries before it (Shares priced
`widthAt (index)`), every root with `gCost` under the whole table, and
predicts exactly the layout length of its output. -/
theorem materializeTable_spec {dag : Dag} (hwf : DagWF dag) {table roots : Array Nat}
    {limits : Limits} {widthAt : Nat → Nat} {entries rs : Array Ixon.Expr} {predicted work : Nat}
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (h : materializeTable (Prep.ofDag dag) table roots limits widthAt =
      .ok (entries, rs, predicted, work)) :
    entries.size = table.size ∧
      (∀ k (hk : k < entries.size), (sizeInfoWith widthAt entries[k]).full =
        gCost (Prep.ofDag dag) (prefixWd dag.size table widthAt k)
          (prefixAvail dag.size table k) table[k]!) ∧
      List.Forall₂ (fun r e => (sizeInfoWith widthAt e).full =
        gCost (Prep.ofDag dag) (prefixWd dag.size table widthAt table.size)
          (prefixAvail dag.size table table.size) r) roots.toList rs.toList ∧
      predicted = tag0Size entries.size +
        (entries.toList.map fun e => (sizeInfoWith widthAt e).full).sum +
        (rs.toList.map fun e => (sizeInfoWith widthAt e).full).sum := by
  have hp := prepWF_ofDag hwf
  obtain ⟨hsize, hrange, st, hst, rfl, hrs, hpred⟩ := materializeTable_parts _ _ _ _ _ h
  obtain ⟨_, hidx, hwid, hev, hsz, hent, hstpred⟩ := tableEvInv_loop hwf hsize hrange hst
  -- the roots
  rw [Array.mapM_eq_mapM_toList] at hrs
  cases hm : List.mapM (fun r => (Prep.ofDag dag).build st.ev st.index st.width false
      ((Prep.ofDag dag).dag.size + 1) r) roots.toList with
  | error err => rw [hm] at hrs; cases hrs
  | ok l =>
    rw [hm] at hrs
    have hl : rs = l.toArray := by cases hrs; rfl
    subst hl
    have hfor := mapM_ok_forall₂ _ _ _ hm
    have hroots' : List.Forall₂ (fun r e => (sizeInfoWith widthAt e).full =
        gCost (Prep.ofDag dag) (prefixWd dag.size table widthAt table.size)
          (prefixAvail dag.size table table.size) r) roots.toList l := by
      refine forall₂_imp_mem hfor fun r hr e he => ?_
      rw [hidx, hwid] at he
      exact build_prefix_size hwf hsize widthAt (Nat.le_refl _) hev (hroots r hr) he
    refine ⟨hsz, hent, hroots', ?_⟩
    rw [hpred, hstpred, ← hsz, sum_range_eq (fun e => (sizeInfoWith widthAt e).full) _
      (fun j hj => (hent j hj).symm)]
    unfold rootsCost
    rw [Ix.Compile.Verify.UniformModel.array_foldl_add_sum]
    have hr := forall₂_sum (f := fun r => gCost (Prep.ofDag dag)
      (prefixWd dag.size table widthAt table.size) (prefixAvail dag.size table table.size) r)
      (g := fun e => (sizeInfoWith widthAt e).full) hroots' (fun a _ b h => h)
    have hc : (roots.toList.map fun r => st.ev.cost[r]!) = roots.toList.map fun r =>
        gCost (Prep.ofDag dag) (prefixWd dag.size table widthAt table.size)
          (prefixAvail dag.size table table.size) r :=
      List.map_congr_left fun r _ => hev.cost r
    rw [hc, ← hr]

/-- **Re-materialized parts are minimal.** Entry `k` of a successful
`materializeTable` is no longer than any writing of `table[k]` with the
dictionary of the entries before it (Shares priced by the layout width of
their index), and some writing attains its length; likewise every root with
the whole table. -/
theorem materializeTable_min {dag : Dag} (hwf : DagWF dag) {table roots : Array Nat}
    {limits : Limits} {widthAt : Nat → Nat} {entries rs : Array Ixon.Expr} {predicted work : Nat}
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (h : materializeTable (Prep.ofDag dag) table roots limits widthAt =
      .ok (entries, rs, predicted, work)) :
    (∀ k (hk : k < entries.size),
      (∀ T, Valid (Prep.ofDag dag) (prefixAvail dag.size table k) table[k]! T →
        (sizeInfoWith widthAt entries[k]).full ≤
          T.gcost (Prep.ofDag dag) (prefixWd dag.size table widthAt k)) ∧
      ∃ T, Valid (Prep.ofDag dag) (prefixAvail dag.size table k) table[k]! T ∧
        T.gcost (Prep.ofDag dag) (prefixWd dag.size table widthAt k) =
          (sizeInfoWith widthAt entries[k]).full) ∧
    List.Forall₂ (fun r e =>
      (∀ T, Valid (Prep.ofDag dag) (prefixAvail dag.size table table.size) r T →
        (sizeInfoWith widthAt e).full ≤
          T.gcost (Prep.ofDag dag) (prefixWd dag.size table widthAt table.size)) ∧
      ∃ T, Valid (Prep.ofDag dag) (prefixAvail dag.size table table.size) r T ∧
        T.gcost (Prep.ofDag dag) (prefixWd dag.size table widthAt table.size) =
          (sizeInfoWith widthAt e).full) roots.toList rs.toList := by
  have hp := prepWF_ofDag hwf
  obtain ⟨hsz, hent, hrs, _⟩ := materializeTable_spec hwf hroots h
  obtain ⟨_, hrange, -⟩ := materializeTable_parts _ _ _ _ _ h
  refine ⟨fun k hk => ?_, forall₂_imp_mem hrs fun r hr e he => ?_⟩
  · have ht := hrange k (by omega)
    rw [hent k hk]
    exact ⟨fun T hT => (hp.gValid_cost _ _ hT ht).1,
      (hp.gExists_opt _ _ _ ht).1⟩
  · rw [he]
    exact ⟨fun T hT => (hp.gValid_cost _ _ hT (hroots r hr)).1,
      (hp.gExists_opt _ _ _ (hroots r hr)).1⟩

/-! ## Phase 3 of the tiered construction -/

theorem layoutBytes_eq (l : ShareLayout) (sharing roots : Array Ixon.Expr) :
    layoutBytes l sharing roots = tag0Size sharing.size +
      (sharing.toList.map fun e => (sizeInfoWith l.widthAt e).full).sum +
      (roots.toList.map fun e => (sizeInfoWith l.widthAt e).full).sum := by
  unfold layoutBytes
  simp only
  rw [Ix.Compile.Verify.UniformModel.array_foldl_add_sum,
    Ix.Compile.Verify.UniformModel.array_foldl_add_sum]

/-- The parts of a successful phase 3. -/
theorem rematerialize_parts {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {order : Array Nat} {phase1Layout : Nat} {m : Rematerialized}
    (h : rematerialize layout limits ex order phase1Layout = .ok m) :
    ∃ work, materializeTable (Prep.ofDag ex.dag) order ex.roots limits layout.widthAt =
        .ok (m.entries, m.roots, m.bytes, work) ∧
      m.bytes ≤ phase1Layout ∧
      (∃ k, reexpand limits ex.dag m.entries m.roots = .ok (order, ex.roots, k)) ∧
      (m.entries ++ m.roots).all (fun e => (wireCounts e).isSome) = true := by
  unfold rematerialize at h
  obtain ⟨⟨entries, roots, predicted, work⟩, hmat, h⟩ := bind_eq_ok h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, hc2, h⟩ := bind_eq_ok h
  obtain ⟨⟨entryIds, rootIds, k⟩, hre, h⟩ := bind_eq_ok h
  dsimp only at h
  obtain ⟨_, hc3, h⟩ := bind_eq_ok h
  obtain ⟨_, hc4, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, hc6, h⟩ := bind_eq_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have h6 := checkInternal_ok hc6
  have h2 := checkInternal_ok hc2
  have h3 := checkInternal_ok hc3
  have h4 := checkInternal_ok hc4
  simp only [decide_eq_true_eq, beq_iff_eq] at h2 h3 h4
  subst h3 h4
  exact ⟨work, hmat, h2, ⟨k, hre⟩, h6⟩

/-- **Phase 3.** A successful re-materialization of the allocated order
`order` (on an input whose DAG and roots passed the phase-1 checks):
* entry `k` has the minimum layout length over all writings of `order[k]`
  with the entries before it as the dictionary, and each root the minimum
  with the whole table (Shares priced by the layout width of their index);
* the predicted length is the layout length of the output, and it is at
  most the phase-1 candidate's layout length;
* entry `k` references only entries below `k`, the roots only table entries;
* with every `Share(i)` replaced by the term of entry `i`, entry `k` is the
  term `order[k]` and each root is its input term, and the output re-expands
  to the table terms `order` and the input roots.
Each part is exact for its dictionary; the composition is not claimed to be
a global byte minimum. -/
theorem rematerialize_spec {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {order : Array Nat} {phase1Layout : Nat} {m : Rematerialized}
    (hwf : DagWF ex.dag) (hroots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (h : rematerialize layout limits ex order phase1Layout = .ok m) :
    m.entries.size = order.size ∧
    (∀ k (hk : k < m.entries.size),
      (∀ T, Valid (Prep.ofDag ex.dag) (prefixAvail ex.dag.size order k) order[k]! T →
        (sizeInfoWith layout.widthAt m.entries[k]).full ≤
          T.gcost (Prep.ofDag ex.dag) (prefixWd ex.dag.size order layout.widthAt k)) ∧
      ∃ T, Valid (Prep.ofDag ex.dag) (prefixAvail ex.dag.size order k) order[k]! T ∧
        T.gcost (Prep.ofDag ex.dag) (prefixWd ex.dag.size order layout.widthAt k) =
          (sizeInfoWith layout.widthAt m.entries[k]).full) ∧
    List.Forall₂ (fun r e =>
      (∀ T, Valid (Prep.ofDag ex.dag) (prefixAvail ex.dag.size order order.size) r T →
        (sizeInfoWith layout.widthAt e).full ≤
          T.gcost (Prep.ofDag ex.dag) (prefixWd ex.dag.size order layout.widthAt order.size)) ∧
      ∃ T, Valid (Prep.ofDag ex.dag) (prefixAvail ex.dag.size order order.size) r T ∧
        T.gcost (Prep.ofDag ex.dag) (prefixWd ex.dag.size order layout.widthAt order.size) =
          (sizeInfoWith layout.widthAt e).full) ex.roots.toList m.roots.toList ∧
    m.bytes = layoutBytes layout m.entries m.roots ∧ m.bytes ≤ phase1Layout ∧
    (∀ k (hk : k < m.entries.size), Ix.Compile.Verify.SharingExact.SharesIn (· < k)
      m.entries[k]) ∧
    (∀ r ∈ m.roots.toList, Ix.Compile.Verify.SharingExact.SharesIn (· < order.size) r) ∧
    (∀ (E : Nat → Ixon.Expr), Ix.Compile.Verify.SharingExact.DagModel ex.dag E →
      (∀ k (hk : k < m.entries.size),
        Ix.Compile.Verify.SharingExact.substShares (fun i => E order[i]!) m.entries[k] =
          E order[k]!) ∧
      List.Forall₂ (fun r e =>
        Ix.Compile.Verify.SharingExact.substShares (fun i => E order[i]!) e = E r)
        ex.roots.toList m.roots.toList) ∧
    ∃ k, reexpand limits ex.dag m.entries m.roots = .ok (order, ex.roots, k) := by
  obtain ⟨work, hmat, hle, hre, -⟩ := rematerialize_parts h
  obtain ⟨hsz, -, -, hpred⟩ := materializeTable_spec hwf hroots hmat
  obtain ⟨hmin, hrmin⟩ := materializeTable_min hwf hroots hmat
  obtain ⟨hsize, -, -⟩ := materializeTable_parts _ _ _ _ _ hmat
  obtain ⟨_, hback, hrback⟩ := Ix.Compile.Verify.SharingExact.materializeTable_backward _ _ _ _ _
    (by omega) hmat
  refine ⟨hsz, hmin, hrmin, by rw [layoutBytes_eq, hpred], hle, hback, hrback,
    fun E hE => Ix.Compile.Verify.SharingExact.materializeTable_correct _ _ _ _ _ (by omega)
      hmat E hE, hre⟩

end Ix.Compile.Verify.Tiered
