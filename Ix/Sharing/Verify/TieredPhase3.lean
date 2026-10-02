import Ix.Sharing.Verify.TieredModel
import Ix.Sharing.Verify.TieredTier

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

namespace Ix.Sharing.Verify.Tiered

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (bind_eq_ok indexOfPrefix_succ indexOfPrefix_zero
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
    rw [Ix.Sharing.Verify.UniformModel.array_foldl_add_sum]
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

/-! ## One evaluation for an order closed under stored descendants

`materializeTableOnePass` (the materialization `rematerialize` runs) prices
and builds every entry from one evaluation of the whole dictionary when the
table order passes `onePassOrder`, and recomputes the work `materializeTable`
counts from the spine counts (`spineAdd`) and a walk up the parent lists
(`ancestorWork`). `materializeTableOnePass_eq` proves it equal to
`materializeTable` on every input, so every statement about `materializeTable`
below holds for it:
* under the order check, below an entry the whole dictionary and the
  dictionary of the entries before it agree (`prefix_agree_below`), so the
  entry's cost with its own Share hidden is its cost there
  (`evalHidden_model`) and `buildTop` writes what `build` writes there
  (`buildTop_eq`);
* the spine count of a term is the number of available terms strictly below
  it on its spine (`spineAdd_spec`, `spineCount_add`), and the walk sums the
  work of a re-evaluation over the entry and the terms above it
  (`ancestorWork_spec`, `evalUp_work`);
* step by step the loop returns what the table loop returns
  (`onePassLoop_sim`). -/

section OnePass

open Ix.Sharing.Verify.SharingExact (Desc Desc.trans setBang_getElem! child_eq_getElem
  pickOption_mem)

/-! ## Spine counts -/

/-- `t` lies strictly below `u` on `u`'s spine. -/
def OnSpine (p : Prep) (t u : Nat) : Prop :=
  p.family[u]! ≠ .none ∧ ∃ k, 1 ≤ k ∧ k < p.spineLen[u]! ∧ spineAt p u k = t

/-- The terms whose spine continues into `x`, in increasing order. -/
theorem spineParentLists_spec {dag : Dag} (x : Nat) (hx : x < dag.size) :
    ((spineParentLists dag (Prep.ofDag dag).family)[x]?.getD #[]).toList =
      (List.range dag.size).filter fun u =>
        ((Prep.ofDag dag).family[u]! != .none &&
          (Prep.ofDag dag).family[(dag.node u).spineNext]! == (Prep.ofDag dag).family[u]!) &&
        (dag.node u).spineNext == x := by
  let cond := fun u =>
    ((Prep.ofDag dag).family[u]! != .none &&
      (Prep.ofDag dag).family[(dag.node u).spineNext]! == (Prep.ofDag dag).family[u]!)
  have hinv : ∀ j, (foldRange (fun (sp : Array (Array Nat)) u =>
        let fam := (Prep.ofDag dag).family[u]!
        let nxt := (dag.node u).spineNext
        if (fam != .none && (Prep.ofDag dag).family[nxt]! == fam) = true then
          sp.modify nxt (·.push u) else sp)
      0 j (Array.replicate dag.size #[])).size = dag.size ∧
      ∀ x, x < dag.size →
        ((foldRange (fun (sp : Array (Array Nat)) u =>
          let fam := (Prep.ofDag dag).family[u]!
          let nxt := (dag.node u).spineNext
          if (fam != .none && (Prep.ofDag dag).family[nxt]! == fam) = true then
            sp.modify nxt (·.push u) else sp)
        0 j (Array.replicate dag.size #[]))[x]?.getD #[]).toList =
        (List.range j).filter fun u => cond u && (dag.node u).spineNext == x := by
    intro j
    induction j with
    | zero =>
      refine ⟨by simp [foldRange], fun x hx => ?_⟩
      simp [foldRange, hx]
    | succ j ih =>
      obtain ⟨hs, hl⟩ := ih
      rw [foldRange_eq] at hs hl ⊢
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range' 0 j).foldl _ _ = sp at hs hl
      simp only [Nat.zero_add]
      refine ⟨?_, fun x hx => ?_⟩
      · split <;> simp [hs]
      · rw [List.range_succ, List.filter_append]
        split
        · rename_i hc
          rw [Array.getElem?_modify]
          by_cases hxj : (dag.node j).spineNext = x
          · subst hxj
            rw [if_pos rfl, Array.getElem?_eq_getElem (by rw [hs]; exact hx)]
            simp only [Option.map_some, Option.getD_some, Array.toList_push]
            rw [← hl _ hx, Array.getElem?_eq_getElem (by rw [hs]; exact hx)]
            simp [cond, hc]
          · rw [if_neg hxj, hl x hx]
            simp [hxj]
        · rename_i hc
          rw [hl x hx]
          simp [cond, hc]
  unfold spineParentLists
  exact (hinv dag.size).2 x hx

section Spine

variable {dag : Dag} (hwf : DagWF dag)

theorem sp_mem {x : Nat} (hx : x < dag.size) (y : Nat) :
    y ∈ ((spineParentLists dag (Prep.ofDag dag).family)[x]?.getD #[]).toList ↔
      y < dag.size ∧ (Prep.ofDag dag).family[y]! ≠ .none ∧
        (Prep.ofDag dag).family[snext (Prep.ofDag dag) y]! = (Prep.ofDag dag).family[y]! ∧
        snext (Prep.ofDag dag) y = x := by
  rw [spineParentLists_spec x hx, List.mem_filter, List.mem_range]
  simp only [snext, ofDag_dag, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, h4⟩

theorem sp_nodup (x : Nat) (hx : x < dag.size) :
    ((spineParentLists dag (Prep.ofDag dag).family)[x]?.getD #[]).toList.Nodup := by
  rw [spineParentLists_spec x hx]
  exact (List.nodup_range).filter _

include hwf in
/-- A spine parent of `x` has `x` at position 1 of its spine. -/
theorem sp_onSpine {x y : Nat} (hx : x < dag.size)
    (hy : y ∈ ((spineParentLists dag (Prep.ofDag dag).family)[x]?.getD #[]).toList) :
    OnSpine (Prep.ofDag dag) x y ∧ 2 ≤ (Prep.ofDag dag).spineLen[y]! ∧
      spineAt (Prep.ofDag dag) y 1 = x := by
  have hp := prepWF_ofDag hwf
  obtain ⟨hyn, hfy, hfs, hsn⟩ := (sp_mem hx y).mp hy
  have hlen : 2 ≤ (Prep.ofDag dag).spineLen[y]! := by
    rcases hp.spine_step hyn hfy with ⟨_, hl, _⟩ | ⟨hne, _, _⟩
    · have := (hp.spine (snext (Prep.ofDag dag) y) (Nat.lt_trans (hp.snext_lt hyn hfy) hyn)
        (by rw [hfs]; exact hfy)).1
      omega
    · exact absurd hfs hne
  exact ⟨⟨hfy, 1, Nat.le_refl _, by omega, hsn⟩, hlen, hsn⟩

include hwf in
/-- The terms with `x` strictly below them on their spine are the spine
parents of `x` and the terms with one of those below them. -/
theorem onSpine_decomp {x : Nat} (hx : x < dag.size) {u : Nat} (hu : u < dag.size) :
    OnSpine (Prep.ofDag dag) x u ↔
      ∃ y ∈ ((spineParentLists dag (Prep.ofDag dag).family)[x]?.getD #[]).toList,
        u = y ∨ OnSpine (Prep.ofDag dag) y u := by
  have hp := prepWF_ofDag hwf
  constructor
  · rintro ⟨hfu, k, hk1, hkl, hkx⟩
    obtain ⟨_, hsp, _, _, _⟩ := hp.spine u hu hfu
    by_cases hk : k = 1
    · subst hk
      refine ⟨u, (sp_mem hx u).mpr ⟨hu, hfu, ?_, ?_⟩, Or.inl rfl⟩
      · obtain ⟨_, hf1, _, _⟩ := hsp 1 hkl
        simpa [spineAt] using hf1
      · simpa [spineAt] using hkx
    · obtain ⟨hle, hfk, _, _⟩ := hsp (k - 1) (by omega)
      obtain ⟨_, hfk', _, _⟩ := hsp k hkl
      have hstep : spineAt (Prep.ofDag dag) u k =
          snext (Prep.ofDag dag) (spineAt (Prep.ofDag dag) u (k - 1)) := by
        have := spineAt_add (Prep.ofDag dag) (k - 1) 1 u
        rw [show k - 1 + 1 = k by omega] at this
        rw [this]; rfl
      refine ⟨spineAt (Prep.ofDag dag) u (k - 1), (sp_mem hx _).mpr ⟨by omega,
        by rw [hfk]; exact hfu, by rw [← hstep, hfk', hfk], by rw [← hstep, hkx]⟩, Or.inr ?_⟩
      exact ⟨hfu, k - 1, by omega, by omega, rfl⟩
  · rintro ⟨y, hy, hu'⟩
    obtain ⟨⟨hfy, _⟩, hlen, hyx⟩ := sp_onSpine hwf hx hy
    rcases hu' with rfl | ⟨hfu, k, hk1, hkl, hky⟩
    · exact ⟨hfy, 1, Nat.le_refl _, by omega, hyx⟩
    · obtain ⟨_, hsp, _, _, _⟩ := hp.spine u hu hfu
      obtain ⟨_, _, hlenk, _⟩ := hsp k hkl
      have hadd := spineAt_add (Prep.ofDag dag) k 1 u
      refine ⟨hfu, k + 1, by omega, ?_, ?_⟩
      · rw [hky] at hlenk; omega
      · rw [hadd, hky]; exact hyx

include hwf in
/-- At most one spine parent of `x` is at or below `u` on `u`'s spine. -/
theorem onSpine_unique {x : Nat} (hx : x < dag.size) {u : Nat} (hu : u < dag.size)
    {y₁ y₂ : Nat}
    (h₁ : y₁ ∈ ((spineParentLists dag (Prep.ofDag dag).family)[x]?.getD #[]).toList)
    (h₂ : y₂ ∈ ((spineParentLists dag (Prep.ofDag dag).family)[x]?.getD #[]).toList)
    (hu₁ : u = y₁ ∨ OnSpine (Prep.ofDag dag) y₁ u) (hu₂ : u = y₂ ∨ OnSpine (Prep.ofDag dag) y₂ u) :
    y₁ = y₂ := by
  have hp := prepWF_ofDag hwf
  -- the position of a spine parent `y` of `x` on `u`'s spine, followed by `x`
  have hpos : ∀ y, y ∈ ((spineParentLists dag (Prep.ofDag dag).family)[x]?.getD #[]).toList →
      (u = y ∨ OnSpine (Prep.ofDag dag) y u) →
      (Prep.ofDag dag).family[u]! ≠ .none ∧ ∃ k, k + 1 < (Prep.ofDag dag).spineLen[u]! ∧
        spineAt (Prep.ofDag dag) u k = y ∧ spineAt (Prep.ofDag dag) u (k + 1) = x := by
    intro y hy huy
    obtain ⟨⟨hfy, _⟩, hlen, hyx⟩ := sp_onSpine hwf hx hy
    rcases huy with rfl | ⟨hfu, k, hk1, hkl, hky⟩
    · exact ⟨hfy, 0, by omega, rfl, hyx⟩
    · obtain ⟨_, hsp, _, _, _⟩ := hp.spine u hu hfu
      obtain ⟨_, _, hlenk, _⟩ := hsp k hkl
      have hadd := spineAt_add (Prep.ofDag dag) k 1 u
      refine ⟨hfu, k, ?_, hky, by rw [hadd, hky]; exact hyx⟩
      rw [hky] at hlenk; omega
  obtain ⟨hfu, k₁, hk₁, hy₁, hx₁⟩ := hpos y₁ h₁ hu₁
  obtain ⟨_, k₂, hk₂, hy₂, hx₂⟩ := hpos y₂ h₂ hu₂
  have : k₁ = k₂ := by
    rcases Nat.lt_trichotomy k₁ k₂ with hlt | heq | hgt
    · have := hp.spineAt_strict hu hfu (show k₁ + 1 < k₂ + 1 by omega) (Nat.le_of_lt hk₂)
      omega
    · exact heq
    · have := hp.spineAt_strict hu hfu (show k₂ + 1 < k₁ + 1 by omega) (Nat.le_of_lt hk₁)
      omega
  subst this
  rw [← hy₁, ← hy₂]

theorem filter_length_unique {L : List Nat} (hL : L.Nodup) (q : Nat → Prop) [DecidablePred q]
    (huniq : ∀ a ∈ L, ∀ b ∈ L, q a → q b → a = b) :
    (L.filter fun y => decide (q y)).length = if ∃ y ∈ L, q y then 1 else 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hL' := (List.nodup_cons.mp hL).2
    have ha := (List.nodup_cons.mp hL).1
    have ih' := ih hL' fun x hx y hy => huniq x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    by_cases hqa : q a
    · have hnone : (L.filter fun y => decide (q y)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy hqy
        have := huniq a List.mem_cons_self y (List.mem_cons_of_mem _ hy) hqa (by simpa using hqy)
        subst this
        exact ha hy
      simp [hqa, hnone]
    · simp only [List.filter_cons, hqa, decide_false, Bool.false_eq_true, if_false, ih']
      congr 1
      apply propext
      constructor
      · rintro ⟨y, hy, hqy⟩; exact ⟨y, List.mem_cons_of_mem _ hy, hqy⟩
      · rintro ⟨y, hy, hqy⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact absurd hqy hqa
        · exact ⟨y, hy, hqy⟩

open Classical in
include hwf in
theorem sp_count {x : Nat} (hx : x < dag.size) {u : Nat} (hu : u < dag.size) :
    (((spineParentLists dag (Prep.ofDag dag).family)[x]?.getD #[]).toList.filter
      fun y => decide (u = y ∨ OnSpine (Prep.ofDag dag) y u)).length =
      if OnSpine (Prep.ofDag dag) x u then 1 else 0 := by
  classical
  rw [filter_length_unique (sp_nodup x hx) _ fun a ha b hb hqa hqb =>
    onSpine_unique hwf hx hu ha hb hqa hqb]
  congr 1
  apply propext
  exact (onSpine_decomp hwf hx hu).symm

theorem modify_getElem!_nat (a : Array Nat) (x u : Nat) (f : Nat → Nat) (hx : x < a.size) :
    (a.modify x f)[u]! = if x = u then f a[u]! else a[u]! := by
  simp only [getElem!_def, Array.getElem?_modify]
  by_cases h : x = u
  · subst h; simp [Array.getElem?_eq_getElem hx]
  · simp [h]

include hwf in
theorem onSpine_ne {x u : Nat} (hu : u < dag.size) (h : OnSpine (Prep.ofDag dag) x u) : u ≠ x := by
  obtain ⟨hf, k, hk1, hkl, rfl⟩ := h
  have := (prepWF_ofDag hwf).spineAt_lt hu hf hk1 hkl
  omega

open Classical in
include hwf in
theorem spineAddGo_spec :
    ∀ (fuel : Nat) (stack : List Nat) (sc sc' : Array Nat), sc.size = dag.size →
      (∀ x ∈ stack, x < dag.size) →
      spineAddGo (spineParentLists dag (Prep.ofDag dag).family) fuel stack sc = some sc' →
      sc'.size = dag.size ∧ ∀ u, u < dag.size →
        sc'[u]! = sc[u]! + (stack.filter fun y => decide (u = y ∨ OnSpine (Prep.ofDag dag) y u)).length := by
  intro fuel
  induction fuel with
  | zero =>
    intro stack sc sc' hs _ h
    cases stack with
    | nil => simp only [spineAddGo, Option.some.injEq] at h; subst h; exact ⟨hs, fun u _ => by simp⟩
    | cons _ _ => simp [spineAddGo] at h
  | succ fuel ih =>
    intro stack sc sc' hs hst h
    cases stack with
    | nil => simp only [spineAddGo, Option.some.injEq] at h; subst h; exact ⟨hs, fun u _ => by simp⟩
    | cons x S =>
      simp only [spineAddGo] at h
      have hx := hst x List.mem_cons_self
      have hst' : ∀ y ∈ ((spineParentLists dag (Prep.ofDag dag).family)[x]?.getD #[]).toList ++ S,
          y < dag.size := by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact ((sp_mem hx y).mp hy).1
        · exact hst y (List.mem_cons_of_mem _ hy)
      obtain ⟨hs', hrow⟩ := ih _ _ sc' (by simp [hs]) hst' h
      refine ⟨hs', fun u hu => ?_⟩
      rw [hrow u hu, modify_getElem!_nat sc x u _ (by omega), List.filter_append, List.length_append,
        sp_count hwf hx hu, List.filter_cons]
      have hne : OnSpine (Prep.ofDag dag) x u → u ≠ x := fun h => onSpine_ne hwf hu h
      by_cases hux : x = u
      · subst hux
        have : ¬ OnSpine (Prep.ofDag dag) x x := fun h => hne h rfl
        simp [this]
        omega
      · have hux' : u ≠ x := fun h => hux h.symm
        by_cases hon : OnSpine (Prep.ofDag dag) x u
        · simp [hux, hux', hon]; omega
        · simp [hux, hux', hon]

open Classical in
include hwf in
/-- **Spine counts.** After `t` becomes available, `spineAdd` adds one to the
count of exactly the terms with `t` strictly below them on their spine. -/
theorem spineAdd_spec {sc sc' : Array Nat} (hs : sc.size = dag.size) {t : Nat} (ht : t < dag.size)
    (h : spineAdd (spineParentLists dag (Prep.ofDag dag).family) sc t = some sc') :
    sc'.size = dag.size ∧ ∀ u, u < dag.size →
      sc'[u]! = sc[u]! + if OnSpine (Prep.ofDag dag) t u then 1 else 0 := by
  unfold spineAdd at h
  obtain ⟨hs', hrow⟩ := spineAddGo_spec hwf _ _ sc sc' hs (fun y hy => ((sp_mem ht y).mp hy).1) h
  exact ⟨hs', fun u hu => by rw [hrow u hu, sp_count hwf ht hu]⟩

theorem filter_length_or (L : List Nat) (p p' q : Nat → Bool)
    (h : ∀ k ∈ L, p' k = (p k || q k)) (hd : ∀ k ∈ L, ¬ (p k = true ∧ q k = true)) :
    (L.filter p').length = (L.filter p).length + (L.filter q).length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ih' := ih (fun k hk => h k (List.mem_cons_of_mem _ hk))
      (fun k hk => hd k (List.mem_cons_of_mem _ hk))
    have ha := h a List.mem_cons_self
    have hda := hd a List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

open Classical in
include hwf in
/-- A spine count after `t` becomes available: one more exactly for the
terms with `t` strictly below them on their spine. -/
theorem spineCount_add {A A' : Nat → Bool} {t : Nat} (hA't : A' t = true) (hAt : A t = false)
    (hsame : ∀ v, v ≠ t → A' v = A v) {u : Nat} (hu : u < dag.size) :
    (if (Prep.ofDag dag).family[u]! = .none then 0
      else spineAvailCount (Prep.ofDag dag) A' u 1) =
    (if (Prep.ofDag dag).family[u]! = .none then 0
      else spineAvailCount (Prep.ofDag dag) A u 1) +
      if OnSpine (Prep.ofDag dag) t u then 1 else 0 := by
  have hp := prepWF_ofDag hwf
  by_cases hf : (Prep.ofDag dag).family[u]! = .none
  · have : ¬ OnSpine (Prep.ofDag dag) t u := fun h => h.1 hf
    simp [hf, this]
  · simp only [hf, if_false]
    unfold spineAvailCount
    rw [filter_length_or _ (fun k => A (spineAt (Prep.ofDag dag) u k))
      (fun k => A' (spineAt (Prep.ofDag dag) u k)) (fun k => decide (spineAt (Prep.ofDag dag) u k = t))
      (fun k _ => by
        by_cases hk : spineAt (Prep.ofDag dag) u k = t
        · rw [hk, hA't, hAt]; simp
        · rw [hsame _ hk]; simp [hk])
      (fun k _ h => by
        obtain ⟨h1, h2⟩ := h
        have hk : spineAt (Prep.ofDag dag) u k = t := by simpa using h2
        rw [hk, hAt] at h1; cases h1)]
    congr 1
    rw [filter_length_unique List.nodup_range' _ fun a ha b hb hqa hqb => ?_]
    · congr 1
      apply propext
      constructor
      · rintro ⟨k, hk, hkt⟩
        rw [List.mem_range'_1] at hk
        exact ⟨hf, k, hk.1, by omega, hkt⟩
      · rintro ⟨_, k, hk1, hkl, hkt⟩
        exact ⟨k, List.mem_range'_1.mpr ⟨hk1, by omega⟩, hkt⟩
    · rw [List.mem_range'_1] at ha hb
      rcases Nat.lt_trichotomy a b with hlt | heq | hgt
      · have := hp.spineAt_strict hu hf hlt (by omega); omega
      · exact heq
      · have := hp.spineAt_strict hu hf hgt (by omega); omega

end Spine

/-! ## The ancestor walk -/

/-- Invariant of `awGo`. -/
structure AwInv (dag : Dag) (sc : Array Nat) (epoch t k j : Nat) (mark queue : Array Nat)
    (sum : Nat) : Prop where
  size : mark.size = dag.size
  marked : ∀ u : Nat, mark[u]! = epoch ↔ u ∈ queue
  le : ∀ u : Nat, mark[u]! ≤ epoch
  anc : ∀ u ∈ queue, u < dag.size ∧ Desc dag u t
  nodup : queue.toList.Nodup
  start : t ∈ queue
  sum : sum = (queue.toList.map fun u => 1 + sc[u]!).sum
  closed : ∀ i, i < k → ∀ p ∈ ((parentEdgeLists dag)[queue[i]!]?.getD #[]).toList, p ∈ queue
  part : k < queue.size →
    ∀ p ∈ (((parentEdgeLists dag)[queue[k]!]?.getD #[]).toList.take j), p ∈ queue
  kle : k ≤ queue.size

section Walk

variable {dag : Dag} (sc : Array Nat) (epoch t : Nat)

theorem push_getElem! {queue : Array Nat} {u i : Nat} (hi : i < queue.size) :
    (queue.push u)[i]! = queue[i]! := by
  rw [getElem!_pos (queue.push u) i (by simp; omega), getElem!_pos queue i hi]
  simp [Array.getElem_push, hi]

theorem awGo_spec :
    ∀ (fuel k j : Nat) (mark queue : Array Nat) (sum : Nat) (r : Nat × Array Nat × Array Nat),
      AwInv dag sc epoch t k j mark queue sum →
      awGo (parentEdgeLists dag) sc epoch fuel k j mark queue sum = some r →
      AwInv dag sc epoch t r.2.2.size 0 r.2.1 r.2.2 r.1 := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ h; simp [awGo] at h
  | succ fuel ih =>
    intro k j mark queue sum r hinv h
    unfold awGo at h
    split at h
    · rename_i hk
      have hqk : queue[k]! = queue[k] := getElem!_pos queue k hk
      dsimp only at h
      split at h
      · rename_i hj
        have hpk := hinv.anc _ (Array.getElem_mem hk)
        have hu := Array.getElem_mem hj
        have hpar := (parentEdgeLists_ok dag _ hpk.1 _).mp hu
        have hdesc : Desc dag (((parentEdgeLists dag)[queue[k]]?.getD #[])[j]) t :=
          (desc_of_child hpar.2).trans hpk.2
        have htake : ∀ p, p ∈ (((parentEdgeLists dag)[queue[k]!]?.getD #[]).toList.take (j + 1)) →
            p ∈ (((parentEdgeLists dag)[queue[k]!]?.getD #[]).toList.take j) ∨
              p = ((parentEdgeLists dag)[queue[k]]?.getD #[])[j] := by
          intro p hp
          rw [hqk] at hp ⊢
          rw [List.take_add_one, List.mem_append] at hp
          rcases hp with hp | hp
          · exact Or.inl hp
          · right
            rw [List.getElem?_toArray] at hp
            simp [Array.getElem?_eq_getElem hj] at hp
            exact hp
        split at h
        · rename_i hm
          have hin : ((parentEdgeLists dag)[queue[k]]?.getD #[])[j] ∈ queue :=
            (hinv.marked _).mp (by simpa using hm)
          refine ih k (j + 1) mark queue sum r { hinv with part := fun hk' p hp => ?_ } h
          rcases htake p hp with hp | rfl
          · exact hinv.part hk' p hp
          · exact hin
        · rename_i hm
          have hnot : ((parentEdgeLists dag)[queue[k]]?.getD #[])[j] ∉ queue := fun hin =>
            hm (by simpa using (hinv.marked _).mpr hin)
          apply ih k (j + 1) _ _ _ r _ h
          refine ⟨by simp [Array.set!_eq_setIfInBounds, hinv.size], fun v => ?_, fun v => ?_,
            fun v hv => ?_, ?_, Array.mem_push.mpr (Or.inl hinv.start), ?_, fun i hik p hp => ?_,
            fun hk' p hp => ?_, by simp; have := hinv.kle; omega⟩
          · rw [setBang_getElem!, Array.mem_push]
            by_cases hv : v = ((parentEdgeLists dag)[queue[k]]?.getD #[])[j]
            · subst hv; simp [hinv.size, hpar.1]
            · simp only [hv, false_and, if_false, Ne.symm hv]
              rw [hinv.marked v]
              simp
          · rw [setBang_getElem!]
            split
            · exact Nat.le_refl _
            · exact hinv.le v
          · rcases Array.mem_push.mp hv with hv | rfl
            · exact hinv.anc v hv
            · exact ⟨hpar.1, hdesc⟩
          · rw [Array.toList_push, List.nodup_append]
            refine ⟨hinv.nodup, by simp, ?_⟩
            intro a ha b hb
            simp at hb
            subst hb
            intro hab
            subst hab
            exact hnot (Array.mem_toList_iff.mp ha)
          · rw [Array.toList_push, List.map_append, List.sum_append, hinv.sum]
            simp
            omega
          · have hi' : i < queue.size := by have := hinv.kle; omega
            rw [push_getElem! hi'] at hp
            exact Array.mem_push.mpr (Or.inl (hinv.closed i hik p hp))
          · rw [push_getElem! hk] at hp
            rcases htake p hp with hp | rfl
            · exact Array.mem_push.mpr (Or.inl (hinv.part hk p hp))
            · exact Array.mem_push.mpr (Or.inr rfl)
      · rename_i hj
        apply ih (k + 1) 0 mark queue sum r _ h
        refine { hinv with
          closed := fun i hik p hp => ?_
          part := fun _ p hp => by simp at hp
          kle := by omega }
        by_cases hik' : i < k
        · exact hinv.closed i hik' p hp
        · have hik'' : i = k := by omega
          subst hik''
          have := hinv.part hk p
          rw [hqk, List.take_of_length_le (by simp; omega)] at this
          exact this (by rw [hqk] at hp; exact hp)
    · rename_i hk
      simp only [Option.some.injEq] at h
      subst h
      have hke : k = queue.size := by have := hinv.kle; omega
      show AwInv dag sc epoch t queue.size 0 mark queue sum
      exact { hinv with
        closed := fun i hi => hinv.closed i (by omega)
        part := fun hk' => absurd hk' (Nat.lt_irrefl _)
        kle := Nat.le_refl _ }

theorem awInv_complete (hwf : DagWF dag) {mark queue : Array Nat} {w : Nat}
    (hinv : AwInv dag sc epoch t queue.size 0 mark queue w) :
    ∀ u, u < dag.size → Desc dag u t → u ∈ queue := by
  suffices h : ∀ u, Desc dag u t → u < dag.size → u ∈ queue from fun u hu hd => h u hd hu
  intro u hd
  induction hd with
  | refl => intro _; exact hinv.start
  | @child v u' k hk hc ih =>
    intro hu
    have hck : (dag.node v).child k ∈ (dag.node v).children := by
      rw [child_eq_getElem _ k hk]; exact Array.getElem_mem hk
    have hlt := hwf.child_lt hu hck
    have hcin : (dag.node v).child k ∈ queue := by
      exact ih hinv (Nat.lt_trans hlt hu)
    obtain ⟨i, hi, hqi⟩ := Array.mem_iff_getElem.mp hcin
    have hpar := (parentEdgeLists_ok dag _ (Nat.lt_trans hlt hu) v).mpr ⟨hu, hck⟩
    apply hinv.closed i hi v
    rw [getElem!_pos queue i hi, hqi]
    exact Array.mem_toList_iff.mpr hpar

/-- **Ancestor work.** The walk sums `1 + sc` over `t` and the terms above it
(as `ancestorMarks` lists them), leaving its marks at most `epoch`. -/
theorem ancestorWork_spec (hwf : DagWF dag) {mark queue mark' queue' : Array Nat}
    {fuel w : Nat} (ht : t < dag.size) (hms : mark.size = dag.size)
    (hlt : ∀ u : Nat, mark[u]! < epoch)
    (h : ancestorWork (parentEdgeLists dag) sc epoch t fuel mark queue = some (w, mark', queue')) :
    w = (((List.range' t (dag.size - t)).filter fun u => (ancestorMarks dag t)[u]!).map
        fun u => 1 + sc[u]!).sum ∧
      mark'.size = dag.size ∧ ∀ u : Nat, mark'[u]! ≤ epoch := by
  have hq0 : ((queue.shrink 0).push t).toList = [t] := by
    simp
  have hinv0 : AwInv dag sc epoch t 0 0 (mark.set! t epoch) ((queue.shrink 0).push t)
      (1 + sc[t]!) := by
    refine ⟨by simp [Array.set!_eq_setIfInBounds, hms], fun u => ?_, fun u => ?_,
      fun u hu => ?_, ?_, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun _ p hp => by simp at hp, Nat.zero_le _⟩
    · rw [setBang_getElem!, ← Array.mem_toList_iff, hq0, List.mem_singleton]
      by_cases hut : u = t
      · subst hut; simp [hms, ht]
      · rw [if_neg (fun h => hut h.1.symm)]
        have := hlt u
        constructor
        · intro h; omega
        · intro h; exact absurd h hut
    · rw [setBang_getElem!]
      split
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (hlt u)
    · rw [← Array.mem_toList_iff, hq0, List.mem_singleton] at hu
      subst hu
      exact ⟨ht, .refl _⟩
    · rw [hq0]; simp
    · rw [← Array.mem_toList_iff, hq0]; simp
    · rw [hq0]; simp
  unfold ancestorWork at h
  have hfin := awGo_spec sc epoch t fuel 0 0 _ _ _ _ hinv0 h
  simp only at hfin
  refine ⟨?_, hfin.size, hfin.le⟩
  rw [hfin.sum]
  apply List.Perm.sum_nat
  apply List.Perm.map
  rw [List.perm_ext_iff_of_nodup hfin.nodup ((List.nodup_range').filter _)]
  intro u
  rw [Array.mem_toList_iff, List.mem_filter, List.mem_range'_1]
  constructor
  · intro hu
    obtain ⟨hun, hd⟩ := hfin.anc u hu
    have hle := Desc.le_of_wf hwf hd hun
    exact ⟨⟨hle, by omega⟩, (ancestorMarks_iff hwf ht u hun).mpr hd⟩
  · rintro ⟨⟨h1, h2⟩, hm⟩
    have hun : u < dag.size := by omega
    exact awInv_complete sc epoch t hwf hfin u hun ((ancestorMarks_iff hwf ht u hun).mp hm)

end Walk

/-! ## An entry priced and built under the whole dictionary -/

section Entry

variable {dag : Dag} (hwf : DagWF dag)

include hwf in
/-- **Hidden cost.** Under an evaluation of a dictionary `(wdK, AK)`, the cost
of `t` with its own Share hidden is its cost under any dictionary without
`t` that agrees strictly below it. -/
theorem evalHidden_model {wdK wdi : Nat → Nat} {AK Ai : Nat → Bool} {ev : DictEval}
    (hev : GEvalOK (Prep.ofDag dag) wdK AK ev) (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if AK u then some (wdK u) else none)
    {t : Nat} (ht : t < dag.size) (hAi : Ai t = false) (hwdi : wdi t = 0)
    (hag : ∀ w, Desc dag t w → w ≠ t → AK w = Ai w ∧ wdK w = wdi w) :
    evalHidden (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
        (Prep.ofDag dag).tail width (Array.replicate dag.size true) ev t =
      gCost (Prep.ofDag dag) wdi Ai t := by
  have hp := prepWF_ofDag hwf
  rw [← evalHidden_eq]
  have hwidth' : ∀ u, widthOf (width.set! t none) u =
      if (if u = t then false else AK u) then some (if u = t then 0 else wdK u) else none := by
    intro u
    rw [widthOf_setBang_none]
    by_cases hu : u = t
    · simp [hu]
    · simp only [hu, if_false]; exact hwidth u
  have hrows : ∀ u, u < t → GEvalRow (Prep.ofDag dag) (fun u => if u = t then 0 else wdK u)
      (fun u => if u = t then false else AK u) ev u := by
    intro u hu
    refine gEvalRow_local hwf (by omega) (fun v hv => ?_) (hev.2 u (by simp [ofDag_dag]; omega))
    have := Desc.le_of_wf hwf hv (by omega)
    have hvt : v ≠ t := by omega
    simp [hvt]
  have haff : (Array.replicate dag.size true)[t]! = true := by simp [ht]
  obtain ⟨_, hrows'⟩ := hp.gEvalStep_spec (width.set! t none) hwidth'
    (Array.replicate dag.size true) ev t ht haff hev.1 hrows
  rw [(hrows' t (Nat.lt_succ_self t)).1]
  refine gCost_local hwf t ht fun v hv => ?_
  by_cases hvt : v = t
  · subst hvt; simp [hAi, hwdi]
  · simp only [hvt, if_false]; exact hag v hv hvt

variable {wdA wdB : Nat → Nat} {A B : Nat → Bool}
  {ev ev' : DictEval} {index index' width width' : Array (Option Nat)}
  (hev : GEvalOK (Prep.ofDag dag) wdA A ev) (hev' : GEvalOK (Prep.ofDag dag) wdB B ev')
  (hwA : ∀ u, widthOf width u = if A u then some (wdA u) else none)
  (hwB : ∀ u, widthOf width' u = if B u then some (wdB u) else none)
  (hiA : ∀ u, (index[u]?.getD none).isSome = A u)
  (hiB : ∀ u, (index'[u]?.getD none).isSome = B u)

include hwf hev hev' hwA hwB hiA hiB in
/-- **Entry body.** `buildTop` under a dictionary with `t` writes what `build`
writes under a dictionary without `t` that agrees strictly below it, when
given that dictionary's cost of `t`. -/
theorem buildTop_eq {t : Nat} (ht : t < dag.size) (hnone : index'[t]?.getD none = none)
    (hag : ∀ w, Desc dag t w → w ≠ t →
      index[w]?.getD none = index'[w]?.getD none ∧ wdA w = wdB w) (fuel : Nat) :
    (Prep.ofDag dag).buildTop ev index width ev'.cost[t]! (fuel + 1) t =
      (Prep.ofDag dag).build ev' index' width' false (fuel + 1) t := by
  have hp := prepWF_ofDag hwf
  have hsub : ∀ c, Desc dag t c → c ≠ t → c < dag.size →
      (Prep.ofDag dag).build ev index width false fuel c =
        (Prep.ofDag dag).build ev' index' width' false fuel c := by
    intro c hc hne hcn
    refine build_congr hwf hev hev' hwA hwB hiA hiB fuel false c hcn fun w hw => hag w (hc.trans hw) ?_
    have := Desc.le_of_wf hwf hw hcn
    have := Desc.le_of_wf hwf hc ht
    omega
  have hshare : optShare index' width' t = #[] := by unfold optShare; rw [hnone]
  have hopts : (Prep.ofDag dag).options ev' index' width' t =
      optRest (Prep.ofDag dag) ev' index' width' t := by
    rw [options_split, hshare, Array.empty_append]
  have hpick : (Prep.ofDag dag).pickBuild ev index width true t =
      pickOption ((Prep.ofDag dag).options ev' index' width' t) := by
    have h1 := pick_options_lazy (Prep.ofDag dag) ev index width true t
    rw [pickLazy_eq_pickBuild, if_pos rfl] at h1
    rw [← h1, options_filter, hopts, optRest_congr hwf hev hev' hwA hwB hiA hiB ht hag]
  simp only [Prep.buildTop, Prep.build, hpick, Bool.false_eq_true, if_false, Bool.false_or]
  generalize hpk : pickOption ((Prep.ofDag dag).options ev' index' width' t) = pk
  rcases pk with _ | ⟨choice, c⟩
  · rfl
  · obtain ⟨b, hb⟩ := pickOption_mem _ hpk
    have hopt' := hp.gOptions_mem ev' hev' index' width' hwB hiB ht hb
    simp only [ofDag_dag]
    by_cases hchk : (c == ev'.cost[t]!) = true
    · simp only [hchk, if_true]
      cases choice with
      | share =>
        rw [hopts] at hb
        exact absurd rfl (optRest_noShare _ _ _ _ _ _ hb)
      | inline =>
        have har := hwf.children_size ht
        have hchild : ∀ k, k < (dag.node t).head.arity →
            Desc dag t ((dag.node t).child k) ∧ (dag.node t).child k ≠ t ∧
              (dag.node t).child k < dag.size := by
          intro k hk
          have hk' : k < (dag.node t).children.size := by rw [har]; exact hk
          have := hwf.childAt_lt ht hk
          exact ⟨.child k hk' (.refl _), by omega, by omega⟩
        cases hh : (dag.node t).head
        case prj ti f =>
          have h0 := hchild 0 (by simp [hh, Head.arity])
          simp only
          rw [hsub _ h0.1 h0.2.1 h0.2.2]
        case letE lc =>
          have h0 := hchild 0 (by simp [hh, Head.arity])
          have h1 := hchild 1 (by simp [hh, Head.arity])
          have h2 := hchild 2 (by simp [hh, Head.arity])
          simp only
          rw [hsub _ h0.1 h0.2.1 h0.2.2, hsub _ h1.1 h1.2.1 h1.2.2, hsub _ h2.1 h2.2.1 h2.2.2]
        all_goals rfl
      | cut j =>
        obtain ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨j', hj', hf, hj1, hjl, _⟩ := hopt'
        · cases h1
        · cases h1
        cases hj'
        dsimp only
        rw [spineWalk_eq]
        simp only
        have hside : ∀ n ∈ (List.range j).map (fun k => (Prep.ofDag dag).dag.node
            (spineAt (Prep.ofDag dag) t k)), ∀ acc,
            (do let side ← (Prep.ofDag dag).build ev index width false fuel n.sideChild
                rebuildSpineNode n acc side : Except SharingError Ixon.Expr) =
            (do let side ← (Prep.ofDag dag).build ev' index' width' false fuel n.sideChild
                rebuildSpineNode n acc side) := by
          intro n hn acc
          obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hn
          rw [List.mem_range] at hk'
          have hd := desc_sideAt hwf ht hf (k := k) (by omega)
          have hlt := hp.sideAt_lt ht hf (k := k) (by omega)
          unfold sideAt at hd hlt
          rw [hsub _ hd (by omega) (by omega)]
        split
        · rfl
        · split
          · rename_i hjlt
            have hdj := desc_spineAt hwf ht hf j (by omega)
            have hjt := hp.spineAt_lt ht hf (k := j) (by omega) hjlt
            rw [(hag _ hdj (by omega)).1]
            split
            · simp only [pure_bind]
              exact foldrM_congr_mem hside _
            · rfl
          · rename_i hjlt
            have hdj := desc_spineAt hwf ht hf j (by omega)
            obtain ⟨_, _, hend, htl, _⟩ := hp.spine t ht hf
            have hjeq : j = (Prep.ofDag dag).spineLen[t]! := by omega
            have hjt : spineAt (Prep.ofDag dag) t j < t := by rw [hjeq, hend]; exact htl
            rw [hsub _ hdj (by omega) (by omega)]
            cases (Prep.ofDag dag).build ev' index' width' false fuel
              (spineAt (Prep.ofDag dag) t j) with
            | error e => rfl
            | ok tl => exact foldrM_congr_mem hside _
    · simp only [hchk, Bool.false_eq_true, if_false]
      rfl

end Entry

/-! ## The order check -/

section Guard

theorem foldl_max_bound (f : Nat → Nat) : ∀ (l : List Nat) (init : Nat),
    init ≤ l.foldl (fun m c => max m (f c)) init ∧
      ∀ c ∈ l, f c ≤ l.foldl (fun m c => max m (f c)) init
  | [], _ => ⟨Nat.le_refl _, fun _ h => absurd h (List.not_mem_nil)⟩
  | a :: l, init => by
    obtain ⟨h1, h2⟩ := foldl_max_bound f l (max init (f a))
    simp only [List.foldl_cons]
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 c hc

/-- The running maximum of the check: at least `pos v` for every term `v`
strictly below `u`. -/
theorem maxBelow_ge {dag : Dag} (hwf : DagWF dag) (pos : Nat → Nat) :
    ∀ u v, Desc dag u v → u < dag.size → v ≠ u →
      pos v ≤ (foldRange (fun (mb : Array Nat) u =>
        mb.set! u ((dag.node u).children.foldl (fun m c => max m (max (pos c) mb[c]!)) 0))
        0 dag.size (Array.replicate dag.size 0))[u]! := by
  let F := fun (mb : Array Nat) u =>
    mb.set! u ((dag.node u).children.foldl (fun m c => max m (max (pos c) mb[c]!)) 0)
  have hinv : ∀ m, m ≤ dag.size →
      ((List.range' 0 m).foldl F (Array.replicate dag.size 0)).size = dag.size ∧
      ∀ u, u < m → ∀ c ∈ (dag.node u).children,
        pos c ≤ ((List.range' 0 m).foldl F (Array.replicate dag.size 0))[u]! ∧
        ((List.range' 0 m).foldl F (Array.replicate dag.size 0))[c]! ≤
          ((List.range' 0 m).foldl F (Array.replicate dag.size 0))[u]! := by
    intro m
    induction m with
    | zero => intro _; exact ⟨by simp, fun u hu => absurd hu (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs, hrow⟩ := ih (by omega)
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
      generalize (List.range' 0 m).foldl F (Array.replicate dag.size 0) = st at hs hrow
      have hkeep : ∀ x, x ≠ m → (F st m)[x]! = st[x]! := by
        intro x hx
        simp only [F]
        rw [setBang_getElem!, if_neg (fun h => hx h.1.symm)]
      refine ⟨by simp [F, hs], fun u hu c hc => ?_⟩
      have hcu := hwf.child_lt (by omega) hc
      rw [hkeep c (by omega)]
      by_cases hum : u = m
      · subst hum
        have hset : (F st u)[u]! = (dag.node u).children.foldl
            (fun m c => max m (max (pos c) st[c]!)) 0 := by
          simp only [F]
          rw [setBang_getElem!, if_pos ⟨rfl, by omega⟩]
        rw [hset, ← Array.foldl_toList]
        have := (foldl_max_bound (fun c => max (pos c) st[c]!) (dag.node u).children.toList 0).2 c
          (Array.mem_toList_iff.mpr hc)
        exact ⟨Nat.le_trans (Nat.le_max_left _ _) this, Nat.le_trans (Nat.le_max_right _ _) this⟩
      · rw [hkeep u hum]
        exact hrow u (by omega) c hc
  obtain ⟨_, hrow⟩ := hinv dag.size (Nat.le_refl _)
  rw [foldRange_eq]
  intro u v hd
  induction hd with
  | refl => intro _ h; exact absurd rfl h
  | @child u' v' k hk hc ih =>
    intro hu hne
    have hck : (dag.node u').child k ∈ (dag.node u').children := by
      rw [child_eq_getElem _ k hk]; exact Array.getElem_mem hk
    have hlt := hwf.child_lt hu hck
    obtain ⟨h1, h2⟩ := hrow u' hu _ hck
    by_cases hvc : v' = (dag.node u').child k
    · rw [hvc]; exact h1
    · exact Nat.le_trans (ih (by omega) hvc) h2

/-- The prefix dictionaries of a table of distinct terms. -/
theorem indexOfPrefix_iff {n : Nat} {table : Array Nat}
    (htab : ∀ i, i < table.size → table[i]! < n)
    (hdist : ∀ i j, i < table.size → j < table.size → table[i]! = table[j]! → i = j) :
    ∀ k, k ≤ table.size → (indexOfPrefix n table k).size = n ∧
      ∀ u j, (indexOfPrefix n table k)[u]?.getD none = some j ↔ j < k ∧ table[j]! = u := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [indexOfPrefix_zero]
    refine ⟨by simp, fun u j => ?_⟩
    by_cases hu : u < n <;> simp [hu]
  | succ k ih =>
    intro hk
    obtain ⟨hs, hiff⟩ := ih (by omega)
    rw [indexOfPrefix_succ n table (by omega)]
    refine ⟨by simp [hs], fun u j => ?_⟩
    rw [getD_setBang, hs]
    have htk := htab k (by omega)
    by_cases hut : u = table[k]!
    · subst hut
      rw [if_pos ⟨rfl, htk⟩, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨by omega, rfl⟩
      · rintro ⟨hj, hjk⟩
        exact (hdist j k (by omega) (by omega) hjk).symm
    · rw [if_neg (fun h => hut h.1.symm), hiff]
      constructor
      · rintro ⟨hj, rfl⟩; exact ⟨by omega, rfl⟩
      · rintro ⟨hj, rfl⟩
        refine ⟨?_, rfl⟩
        by_cases hjk : j = k
        · subst hjk; exact absurd rfl hut
        · omega

/-- What a passing order check gives. -/
theorem onePassOrder_spec {dag : Dag} {table roots : Array Nat} {index : Array (Option Nat)}
    (h : onePassOrder dag table roots index = true) :
    DagWF dag ∧ (∀ r ∈ roots.toList, r < dag.size) ∧
      ∀ i, i < table.size → index[table[i]!]?.getD none = some i ∧
        (table[i]! < dag.size → ∀ v j, Desc dag table[i]! v → v ≠ table[i]! →
          index[v]?.getD none = some j → j < i) := by
  unfold onePassOrder at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨hcp, har⟩, hroots⟩, hord⟩ := h
  have hwf := dagWF_of_checks hcp har
  refine ⟨hwf, fun r hr => ?_, fun i hi => ⟨(hord i hi).1, fun ht v j hd hne hv => ?_⟩⟩
  · rw [Array.all_eq_true] at hroots
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
    simpa using hroots k (by simpa using hk)
  · have h2 := (hord i hi).2
    have := Nat.le_trans (maxBelow_ge hwf _ _ v hd ht hne) h2
    simp only [hv] at this
    have h3 : j + 1 ≤ i := this
    omega

end Guard

/-! ## The loop -/

section Loop

theorem materializeStep_eq (p : Prep) (table : Array Nat) (limits : Limits) (widthAt : Nat → Nat)
    (st : TableState) (i : Nat) :
    materializeStep p table limits widthAt st i =
      if st.ev.cost[table[i]!]! > limits.maxMaterialize then
        .error (.resourceExhausted .materialize limits.maxMaterialize)
      else match p.build st.ev st.index st.width false (p.dag.size + 1) table[i]! with
      | .error e => .error e
      | .ok e =>
        if st.work + st.ev.work + st.ev.cost[table[i]!]! > limits.maxMaterializeWork then
          .error (.resourceExhausted .materializeWork limits.maxMaterializeWork)
        else .ok { entries := st.entries.push e,
                   index := st.index.set! table[i]! (some i),
                   width := st.width.set! table[i]! (some (widthAt i)),
                   ev := p.evalUp st.ev (st.width.set! table[i]! (some (widthAt i))) table[i]!,
                   predicted := st.predicted + st.ev.cost[table[i]!]!,
                   work := st.work + st.ev.work + st.ev.cost[table[i]!]! } := by
  unfold materializeStep
  by_cases h1 : st.ev.cost[table[i]!]! > limits.maxMaterialize
  · simp [h1, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · cases hb : p.build st.ev st.index st.width false (p.dag.size + 1) table[i]! with
    | error e => simp [h1, hb, bind, Except.bind]
    | ok e =>
      by_cases h2 : st.work + st.ev.work + st.ev.cost[table[i]!]! > limits.maxMaterializeWork
      · simp [h1, h2, hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
      · simp [h1, h2, hb, bind, Except.bind, pure, Except.pure]

/-- The spine counts after `i` entries. -/
def ScInv (dag : Dag) (table : Array Nat) (i : Nat) (sc : Array Nat) : Prop :=
  sc.size = dag.size ∧ ∀ u, u < dag.size →
    sc[u]! = if (Prep.ofDag dag).family[u]! = .none then 0
      else spineAvailCount (Prep.ofDag dag) (prefixAvail dag.size table i) u 1

/-- What the loop returns, against the table loop of `materializeTable`. -/
def LoopRel (p : Prep) (table : Array Nat) (limits : Limits) (widthAt : Nat → Nat) (i k : Nat)
    (st : TableState) (r : Except SharingError (Array Ixon.Expr × Nat × Nat × Nat))
    (inv : TableState → Prop) : Prop :=
  match r with
  | .error e => (List.range' i k).foldlM (materializeStep p table limits widthAt) st = .error e
  | .ok (entries, work, evWork, predicted) =>
    ∃ st', (List.range' i k).foldlM (materializeStep p table limits widthAt) st = .ok st' ∧
      inv st' ∧ st'.entries = entries ∧ st'.work = work ∧ st'.ev.work = evWork ∧
      st'.predicted = predicted

theorem loopRel_step {p : Prep} {table : Array Nat} {limits : Limits} {widthAt : Nat → Nat}
    {i k : Nat} {st st' : TableState} {r : Except SharingError (Array Ixon.Expr × Nat × Nat × Nat)}
    {inv : TableState → Prop} (h : materializeStep p table limits widthAt st i = .ok st')
    (hr : LoopRel p table limits widthAt (i + 1) k st' r inv) :
    LoopRel p table limits widthAt i (k + 1) st r inv := by
  have hf : (List.range' i (k + 1)).foldlM (materializeStep p table limits widthAt) st =
      (List.range' (i + 1) k).foldlM (materializeStep p table limits widthAt) st' := by
    rw [List.range'_succ, List.foldlM_cons, h]; rfl
  unfold LoopRel at hr ⊢
  rw [hf]
  exact hr

theorem loopRel_error {p : Prep} {table : Array Nat} {limits : Limits} {widthAt : Nat → Nat}
    {i k : Nat} {st : TableState} {e : SharingError} {inv : TableState → Prop}
    (h : materializeStep p table limits widthAt st i = .error e) :
    LoopRel p table limits widthAt i (k + 1) st (.error e) inv := by
  unfold LoopRel
  rw [List.range'_succ, List.foldlM_cons, h]
  rfl

variable {dag : Dag} (hwf : DagWF dag) {table : Array Nat} {limits : Limits} {widthAt : Nat → Nat}
  (hsize : table.size < UInt64.size)
  (hrange : ∀ k, k < table.size → table[k]! < dag.size)
  (hiff : ∀ k, k ≤ table.size → ∀ u j,
    (indexOfPrefix dag.size table k)[u]?.getD none = some j ↔ j < k ∧ table[j]! = u)
  (hcl : ∀ i, i < table.size → ∀ v j, Desc dag table[i]! v → v ≠ table[i]! →
    (indexOfPrefix dag.size table table.size)[v]?.getD none = some j → j < i)

include hiff hcl in
theorem prefix_agree_below {i : Nat} (hi : i < table.size) {v : Nat} (hd : Desc dag table[i]! v)
    (hne : v ≠ table[i]!) :
    (indexOfPrefix dag.size table i)[v]?.getD none =
      (indexOfPrefix dag.size table table.size)[v]?.getD none := by
  cases hK : (indexOfPrefix dag.size table table.size)[v]?.getD none with
  | some j =>
    have hj := hcl i hi v j hd hne hK
    have := ((hiff table.size (Nat.le_refl _) v j).mp hK).2
    exact (hiff i (by omega) v j).mpr ⟨hj, this⟩
  | none =>
    cases hI : (indexOfPrefix dag.size table i)[v]?.getD none with
    | none => rfl
    | some j =>
      obtain ⟨hj, hjv⟩ := (hiff i (by omega) v j).mp hI
      have := (hiff table.size (Nat.le_refl _) v j).mpr ⟨by omega, hjv⟩
      rw [hK] at this; cases this

include hiff in
theorem prefix_none_self {i : Nat} (hi : i < table.size) :
    (indexOfPrefix dag.size table i)[table[i]!]?.getD none = none := by
  cases hI : (indexOfPrefix dag.size table i)[table[i]!]?.getD none with
  | none => rfl
  | some j =>
    obtain ⟨hj, hjv⟩ := (hiff i (by omega) _ j).mp hI
    have h1 := (hiff table.size (Nat.le_refl _) _ j).mpr ⟨by omega, hjv⟩
    have h2 := (hiff table.size (Nat.le_refl _) table[i]! i).mpr ⟨hi, rfl⟩
    rw [h1] at h2
    cases h2; omega

open Classical in
include hwf hsize hrange hiff hcl in
/-- **The loop.** From the state of `materializeTable` after `i` entries,
`onePassLoop` returns what the table loop returns (when its walks do not run
out of fuel). -/
theorem onePassLoop_sim :
    ∀ (k i : Nat) (st : TableState) (ew : Nat) (sc mark queue : Array Nat)
      (r : Except SharingError (Array Ixon.Expr × Nat × Nat × Nat)),
      i + k = table.size → TableEvInv dag table widthAt i st → ew = st.ev.work →
      ScInv dag table i sc →
      mark.size = dag.size → (∀ u : Nat, mark[u]! < i + 1) →
      onePassLoop (Prep.ofDag dag) table limits
          ((Prep.ofDag dag).evalAll ((indexOfPrefix dag.size table table.size).map (·.map widthAt)))
          (indexOfPrefix dag.size table table.size)
          ((indexOfPrefix dag.size table table.size).map (·.map widthAt))
          (Array.replicate dag.size true) (parentEdgeLists dag)
          (spineParentLists dag (Prep.ofDag dag).family) k i st.entries st.work ew
          st.predicted sc mark queue = some r →
      LoopRel (Prep.ofDag dag) table limits widthAt i k st r
        (TableEvInv dag table widthAt table.size) := by
  have hp := prepWF_ofDag hwf
  have hevK : GEvalOK (Prep.ofDag dag) (prefixWd dag.size table widthAt table.size)
      (prefixAvail dag.size table table.size)
      ((Prep.ofDag dag).evalAll ((indexOfPrefix dag.size table table.size).map (·.map widthAt))) :=
    hp.evalAll_ok (ofDag_empty_size dag) _ (prefix_width dag.size table widthAt table.size)
  intro k
  induction k with
  | zero =>
    intro i st ew sc mark queue r hik hI hew _ _ _ h
    subst hew
    simp only [onePassLoop, Option.some.injEq] at h
    subst h
    have : i = table.size := by omega
    subst this
    exact ⟨st, rfl, hI, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    intro i st ew sc mark queue r hik hI hew hsc hms hml h
    subst hew
    have hi : i < table.size := by omega
    have ht := hrange i hi
    obtain ⟨_, hidx, hwid, hev, _, _, _⟩ := hI
    -- the dictionaries below the entry
    have hag : ∀ w, Desc dag table[i]! w → w ≠ table[i]! →
        (indexOfPrefix dag.size table table.size)[w]?.getD none =
          (indexOfPrefix dag.size table i)[w]?.getD none ∧
        prefixWd dag.size table widthAt table.size w = prefixWd dag.size table widthAt i w := by
      intro w hw hne
      have := prefix_agree_below hiff hcl hi hw hne
      refine ⟨this.symm, ?_⟩
      unfold prefixWd
      rw [this]
    have hnone := prefix_none_self hiff hi
    have hE1 : evalHidden (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
        (Prep.ofDag dag).tail ((indexOfPrefix dag.size table table.size).map (·.map widthAt))
        (Array.replicate dag.size true)
        ((Prep.ofDag dag).evalAll ((indexOfPrefix dag.size table table.size).map (·.map widthAt)))
        table[i]! = st.ev.cost[table[i]!]! := by
      rw [hev.cost]
      refine evalHidden_model hwf hevK _ (prefix_width dag.size table widthAt table.size) ht
        (by unfold prefixAvail; rw [hnone]; rfl) (by unfold prefixWd; rw [hnone])
        fun w hw hne => ⟨?_, (hag w hw hne).2⟩
      unfold prefixAvail
      rw [(hag w hw hne).1]
    have hE2 : (Prep.ofDag dag).buildTop
        ((Prep.ofDag dag).evalAll ((indexOfPrefix dag.size table table.size).map (·.map widthAt)))
        (indexOfPrefix dag.size table table.size)
        ((indexOfPrefix dag.size table table.size).map (·.map widthAt)) st.ev.cost[table[i]!]!
        (dag.size + 1) table[i]! =
        (Prep.ofDag dag).build st.ev st.index st.width false (dag.size + 1) table[i]! := by
      rw [hidx, hwid]
      exact buildTop_eq hwf hevK hev (prefix_width dag.size table widthAt table.size)
        (prefix_width dag.size table widthAt i) (fun u => rfl) (fun u => rfl) ht hnone hag _
    simp only [onePassLoop] at h
    simp only [hE1] at h
    simp only [ofDag_dag] at h
    by_cases hc : st.ev.cost[table[i]!]! > limits.maxMaterialize
    · simp only [hc, if_true, Option.some.injEq] at h
      subst h
      apply loopRel_error
      rw [materializeStep_eq]
      simp [hc]
    · simp only [hc, if_false] at h
      rw [hE2] at h
      cases hb : (Prep.ofDag dag).build st.ev st.index st.width false (dag.size + 1) table[i]! with
      | error e =>
        rw [hb] at h
        simp only [Option.some.injEq] at h
        subst h
        apply loopRel_error
        rw [materializeStep_eq]
        simp [hc, hb, ofDag_dag]
      | ok e =>
        rw [hb] at h
        simp only at h
        by_cases hw : st.work + st.ev.work + st.ev.cost[table[i]!]! > limits.maxMaterializeWork
        · simp only [hw, if_true, Option.some.injEq] at h
          subst h
          apply loopRel_error
          rw [materializeStep_eq]
          simp [hc, hb, hw, ofDag_dag]
        · simp only [hw, if_false] at h
          cases hsa : spineAdd (spineParentLists dag (Prep.ofDag dag).family) sc table[i]! with
          | none => rw [hsa] at h; cases h
          | some sc' =>
            rw [hsa] at h
            simp only at h
            cases haw : ancestorWork (parentEdgeLists dag) sc' (i + 1) table[i]!
                (4 * dag.size + 2) mark queue with
            | none => rw [haw] at h; cases h
            | some x =>
              obtain ⟨w, mark', queue'⟩ := x
              rw [haw] at h
              simp only at h
              let st' : TableState := ⟨st.entries.push e, st.index.set! table[i]! (some i),
                st.width.set! table[i]! (some (widthAt i)),
                (Prep.ofDag dag).evalUp st.ev (st.width.set! table[i]! (some (widthAt i))) table[i]!,
                st.predicted + st.ev.cost[table[i]!]!, st.work + st.ev.work + st.ev.cost[table[i]!]!⟩
              have hstep : materializeStep (Prep.ofDag dag) table limits widthAt st i = .ok st' := by
                rw [materializeStep_eq]
                simp only [ofDag_dag, hc, if_false, hb, hw]
                rfl
              have hI' := tableEvInv_step hwf hsize hrange ⟨by omega, hidx, hwid, hev, by assumption,
                by assumption, by assumption⟩ hi hstep
              -- spine counts
              obtain ⟨hs', hrow'⟩ := spineAdd_spec hwf hsc.1 ht hsa
              have hsucc_avail : ∀ v, v ≠ table[i]! →
                  prefixAvail dag.size table (i + 1) v = prefixAvail dag.size table i v :=
                fun v hv => (prefix_succ_agree dag.size table widthAt hi v hv).1
              have hAt' : prefixAvail dag.size table (i + 1) table[i]! = true := by
                unfold prefixAvail
                rw [(hiff (i + 1) (by omega) _ i).mpr ⟨by omega, rfl⟩]
                rfl
              have hAt : prefixAvail dag.size table i table[i]! = false := by
                unfold prefixAvail; rw [hnone]; rfl
              have hsc' : ScInv dag table (i + 1) sc' := by
                refine ⟨hs', fun u hu => ?_⟩
                rw [hrow' u hu, hsc.2 u hu]
                exact (spineCount_add hwf hAt' hAt hsucc_avail hu).symm
              -- the walk
              obtain ⟨hwsum, hms', hml'⟩ := ancestorWork_spec sc' (i + 1) table[i]! hwf ht hms hml haw
              have hwidth' : st.width.set! table[i]! (some (widthAt i)) =
                  (indexOfPrefix dag.size table (i + 1)).map (·.map widthAt) := by
                rw [hwid, indexOfPrefix_succ dag.size table hi]
                simp [Array.set!, Array.map_setIfInBounds]
              have hwork := evalUp_work hwf hev ht
                (fun v hv => prefix_succ_agree dag.size table widthAt hi v hv)
                (st.width.set! table[i]! (some (widthAt i)))
                (by rw [hwidth']; exact prefix_width dag.size table widthAt (i + 1))
              have hw' : w = st'.ev.work := by
                show w = ((Prep.ofDag dag).evalUp st.ev
                  (st.width.set! table[i]! (some (widthAt i))) table[i]!).work
                rw [hwork, hwsum]
                congr 1
                apply List.map_congr_left
                intro u hu
                have hun : u < dag.size := by
                  have := (List.mem_range'_1.mp (List.mem_filter.mp hu).1); omega
                unfold nodeWork
                rw [hsc'.2 u hun]
              have := ih (i + 1) st' w sc' mark' queue' r (by omega) hI' hw' hsc' hms'
                (fun u => Nat.lt_succ_of_le (hml' u)) h
              exact loopRel_step hstep this

end Loop

/-! ## The one-pass materialization -/

theorem list_mapM_congr {α β ε : Type} {f g : α → Except ε β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a List.mem_cons_self,
      list_mapM_congr l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **One-pass phase 3.** `materializeTableOnePass` returns exactly what
`materializeTable` returns, on every input: entries, roots, predicted length,
work, errors and the points where the limits are checked. -/
theorem materializeTableOnePass_eq (dag : Dag) (table roots : Array Nat) (limits : Limits)
    (widthAt : Nat → Nat) :
    materializeTableOnePass (Prep.ofDag dag) table roots limits widthAt =
      materializeTable (Prep.ofDag dag) table roots limits widthAt := by
  unfold materializeTableOnePass
  by_cases h1 : table.size ≥ wordBound
  · unfold materializeTable; simp [h1]
  cases h2 : table.all (· < (Prep.ofDag dag).dag.size)
  · unfold materializeTable; simp [h1, h2]
  simp only [h1, if_false, Bool.not_true, Bool.false_eq_true]
  by_cases h3f : onePassOrder (Prep.ofDag dag).dag table roots
      (indexOfPrefix (Prep.ofDag dag).dag.size table table.size) = false
  · simp [h3f]
  have h3 : onePassOrder dag table roots (indexOfPrefix dag.size table table.size) = true := by
    cases hb : onePassOrder dag table roots (indexOfPrefix dag.size table table.size) with
    | true => rfl
    | false => exact absurd hb h3f
  have h3' : (!onePassOrder (Prep.ofDag dag).dag table roots
      (indexOfPrefix (Prep.ofDag dag).dag.size table table.size)) = false := by
    rw [ofDag_dag, h3]; rfl
  simp only [h3', Bool.false_eq_true, if_false]
  obtain ⟨hwf, hroots, hord⟩ := onePassOrder_spec h3
  have hp := prepWF_ofDag hwf
  have htab : ∀ i, i < table.size → table[i]! < dag.size := by
    intro i hi
    rw [getElem!_pos table i hi]
    exact of_decide_eq_true (Array.all_eq_true.mp h2 i hi)
  have hdist : ∀ i j, i < table.size → j < table.size → table[i]! = table[j]! → i = j := by
    intro i j hi hj hij
    have h1 := (hord i hi).1
    rw [hij, (hord j hj).1] at h1
    cases h1; rfl
  have hiff := fun k hk => (indexOfPrefix_iff htab hdist k hk).2
  have hcl : ∀ i, i < table.size → ∀ v j, Desc dag table[i]! v → v ≠ table[i]! →
      (indexOfPrefix dag.size table table.size)[v]?.getD none = some j → j < i :=
    fun i hi v j hd hne hv => (hord i hi).2 (htab i hi) v j hd hne hv
  have hsize : table.size < UInt64.size := by unfold wordBound at h1; omega
  have hI0 : TableEvInv dag table widthAt 0
      { entries := #[], index := Array.replicate (Prep.ofDag dag).dag.size none,
        width := Array.replicate (Prep.ofDag dag).dag.size none,
        ev := (Prep.ofDag dag).evalAll (Array.replicate (Prep.ofDag dag).dag.size none),
        predicted := tag0Size table.size, work := 0 } := by
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
  have hsc0 : ScInv dag table 0 (Array.replicate dag.size 0) := by
    refine ⟨by simp, fun u hu => ?_⟩
    rw [spineAvailCount_nil]
    · simp [hu]
    · intro k _ _
      unfold prefixAvail
      rw [indexOfPrefix_zero]
      simp only [Array.getElem?_replicate]
      split <;> rfl
  have hevK : GEvalOK (Prep.ofDag dag) (prefixWd dag.size table widthAt table.size)
      (prefixAvail dag.size table table.size)
      ((Prep.ofDag dag).evalAll ((indexOfPrefix dag.size table table.size).map (·.map widthAt))) :=
    hp.evalAll_ok (ofDag_empty_size dag) _ (prefix_width dag.size table widthAt table.size)
  generalize hloop : onePassLoop (Prep.ofDag dag) table limits
      ((Prep.ofDag dag).evalAll
        ((indexOfPrefix (Prep.ofDag dag).dag.size table table.size).map (·.map widthAt)))
      (indexOfPrefix (Prep.ofDag dag).dag.size table table.size)
      ((indexOfPrefix (Prep.ofDag dag).dag.size table table.size).map (·.map widthAt))
      (Array.replicate (Prep.ofDag dag).dag.size true) (parentEdgeLists (Prep.ofDag dag).dag)
      (spineParentLists (Prep.ofDag dag).dag (Prep.ofDag dag).family) table.size 0 #[] 0
      (Prep.ofDag dag).dag.size (tag0Size table.size)
      (Array.replicate (Prep.ofDag dag).dag.size 0) (Array.replicate (Prep.ofDag dag).dag.size 0)
      #[] = res
  rcases res with _ | res
  · rfl
  have hrel := onePassLoop_sim hwf hsize htab hiff hcl table.size 0 _ _ _ _ _ res (by omega) hI0
    (evalAll_none_work hwf).symm hsc0
    (by simp [ofDag_dag]) (fun u => by by_cases hu : u < dag.size <;> simp [hu, ofDag_dag])
    hloop
  unfold materializeTable
  simp only [h1, h2, if_false, Bool.not_true, Bool.false_eq_true]
  rw [List.range_eq_range']
  rcases res with e | ⟨entries, work, evWork, predicted⟩
  · simp only [LoopRel] at hrel
    rw [hrel]
    rfl
  · obtain ⟨st', hfold, hI', rfl, rfl, rfl, rfl⟩ := hrel
    rw [hfold]
    obtain ⟨_, hidx, hwid, hev', _, _, _⟩ := hI'
    have hcost : ((Prep.ofDag dag).evalAll
        ((indexOfPrefix (Prep.ofDag dag).dag.size table table.size).map (·.map widthAt))).cost =
        st'.ev.cost := by
      apply Array.ext
      · exact hevK.1.1.trans hev'.1.1.symm
      · intro j hj1 hj2
        have := (hevK.cost j).trans (hev'.cost j).symm
        rwa [getElem!_pos _ j hj1, getElem!_pos _ j hj2] at this
    have hbuild : roots.mapM (fun r => (Prep.ofDag dag).build
        ((Prep.ofDag dag).evalAll
          ((indexOfPrefix (Prep.ofDag dag).dag.size table table.size).map (·.map widthAt)))
        (indexOfPrefix (Prep.ofDag dag).dag.size table table.size)
        ((indexOfPrefix (Prep.ofDag dag).dag.size table table.size).map (·.map widthAt)) false
        ((Prep.ofDag dag).dag.size + 1) r) =
        roots.mapM (fun r => (Prep.ofDag dag).build st'.ev st'.index st'.width false
          ((Prep.ofDag dag).dag.size + 1) r) := by
      rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, hidx, hwid]
      congr 1
      exact list_mapM_congr _ fun r hr => build_congr hwf hevK hev'
        (prefix_width dag.size table widthAt table.size)
        (prefix_width dag.size table widthAt table.size) (fun u => rfl) (fun u => rfl)
        (dag.size + 1) false r (hroots r hr) fun w _ => ⟨rfl, rfl⟩
    simp only [hcost, hbuild]
    rfl

end OnePass

/-! ## Phase 3 of the tiered construction -/

theorem layoutBytes_eq (l : ShareLayout) (sharing roots : Array Ixon.Expr) :
    layoutBytes l sharing roots = tag0Size sharing.size +
      (sharing.toList.map fun e => (sizeInfoWith l.widthAt e).full).sum +
      (roots.toList.map fun e => (sizeInfoWith l.widthAt e).full).sum := by
  unfold layoutBytes
  simp only
  rw [Ix.Sharing.Verify.UniformModel.array_foldl_add_sum,
    Ix.Sharing.Verify.UniformModel.array_foldl_add_sum]

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
  rw [materializeTableOnePass_eq] at hmat
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, hc2, h⟩ := bind_eq_ok h
  obtain ⟨⟨entryIds, rootIds, k⟩, hre, h⟩ := bind_eq_ok h
  dsimp only at h
  obtain ⟨_, hc3, h⟩ := bind_eq_ok h
  obtain ⟨_, hc4, h⟩ := bind_eq_ok h
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

/-- The length phase 3 records: the layout length of its output, as both
`bytes` and `measured`. -/
theorem rematerialize_measured {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {order : Array Nat} {phase1Layout : Nat} {m : Rematerialized}
    (h : rematerialize layout limits ex order phase1Layout = .ok m) :
    m.measured = layoutBytes layout m.entries m.roots ∧ m.bytes = m.measured := by
  unfold rematerialize at h
  obtain ⟨⟨entries, roots, predicted, work⟩, -, h⟩ := bind_eq_ok h
  dsimp only at h
  obtain ⟨_, hc1, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨entryIds, rootIds, k⟩, -, h⟩ := bind_eq_ok h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have h1 := checkInternal_ok hc1
  simp only [beq_iff_eq] at h1
  exact ⟨rfl, h1.symm⟩

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
    (∀ k (hk : k < m.entries.size), Ix.Sharing.Verify.SharingExact.SharesIn (· < k)
      m.entries[k]) ∧
    (∀ r ∈ m.roots.toList, Ix.Sharing.Verify.SharingExact.SharesIn (· < order.size) r) ∧
    (∀ (E : Nat → Ixon.Expr), Ix.Sharing.Verify.SharingExact.DagModel ex.dag E →
      (∀ k (hk : k < m.entries.size),
        Ix.Sharing.Verify.SharingExact.substShares (fun i => E order[i]!) m.entries[k] =
          E order[k]!) ∧
      List.Forall₂ (fun r e =>
        Ix.Sharing.Verify.SharingExact.substShares (fun i => E order[i]!) e = E r)
        ex.roots.toList m.roots.toList) ∧
    ∃ k, reexpand limits ex.dag m.entries m.roots = .ok (order, ex.roots, k) := by
  obtain ⟨work, hmat, hle, hre, -⟩ := rematerialize_parts h
  obtain ⟨hsz, -, -, hpred⟩ := materializeTable_spec hwf hroots hmat
  obtain ⟨hmin, hrmin⟩ := materializeTable_min hwf hroots hmat
  obtain ⟨hsize, -, -⟩ := materializeTable_parts _ _ _ _ _ hmat
  obtain ⟨_, hback, hrback⟩ := Ix.Sharing.Verify.SharingExact.materializeTable_backward _ _ _ _ _
    (by omega) hmat
  refine ⟨hsz, hmin, hrmin, by rw [layoutBytes_eq, hpred], hle, hback, hrback,
    fun E hE => Ix.Sharing.Verify.SharingExact.materializeTable_correct _ _ _ _ _ (by omega)
      hmat E hE, hre⟩

end Ix.Sharing.Verify.Tiered
