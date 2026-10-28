import Ix.Cert.ReportChecks
import Ix.Cert.InductiveCompile
import Ix.Cert.GraphWalk
import Ix.CompileCert.ReaderIndexDiscovery
import Ix.CompileCert.Canon.QSortSorted

/-! # The recursor index over a store: facts independent of the closure

`Ix.Kernel.Reader.buildIndex` files every recursor member of its records under the block and
motive its analysis gives (`analyseRecursor`), keeps the first per motive, and sorts each block's
recursors by motive. This module states what the closure's index needs of it, over any store,
beside the compile report's checks that pin an input family's recursors to their names
(`Ix.Cert.ReportChecks`: `RecursorSlotsUnique`, `RecursorShapes`, `FamilyNamesStored`,
`FamilyLevelParams`):

* **The analysis reads the store only through references** (`analyseWith_mono`,
  `recursorAnalysis_spec`): a store that resolves every reference the analysis consults alike
  gives the same analysis.
* **Two invariants of the builder** that `ReaderIndex` does not state: a block shape's order is
  a filed candidate's carrier order (`shapeOrder`), and the motives filed at one block are
  distinct (`motives_nodup`); with them a block's recursor list is its filed pairs sorted by
  motive (`buildIndex_at`), and a sorted list of distinct motives is determined
  (`sorted_eq_range`).
* **The compile's headers**: a block compiled one member per class keeps each member's
  level-parameter count and counts (`block_headers`), and so does a lone recursor
  (`lone_header`). -/

namespace Ix.Cert.RecursorIndex

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader
open Ix.CompileCert
open Ix.CompileCert.ReaderIndex (inductives orderFor orderValid From Coherent)

/-! ## The analysis reads the store through references -/

/-- `analyseRecursor` with the reference lookup it makes (`headRef`) abstracted. -/
def analyseWith (c : Ixon.Constant) (r : Ixon.Recursor) (head : Ixon.Expr → Option (ConstRef Address)) :
    Option (Nat × Array (ConstRef Address) × ConstRef Address) := do
  let nP := r.params.toNat
  let nM := r.motives.toNat
  let nm := r.minors.toNat
  let nI := r.indices.toNat
  let depth := nP + nM + nm + nI + 1
  let (doms, body) ← stripAll c depth r.typ
  let .var k := appHead c spineFuel body | none
  let pos := depth - 1 - k.toNat
  guard (k.toNat < depth && nP ≤ pos && pos < nP + nM)
  let carriers ← (doms.drop nP |>.take nM).toArray.mapM fun dom => do
    let (bs, _) := stripAllFull c spineFuel dom
    head (← bs.getLast?)
  let major ← head (← doms.getLast?)
  pure (pos - nP, carriers, major)

theorem analyse_eq (store : Store) (owner : Address) (c : Ixon.Constant) (r : Ixon.Recursor) :
    analyseRecursor store owner c r = analyseWith c r (headRef store owner c) := rfl

theorem list_mapM_mono {α β : Type} {f₁ f₂ : α → Option β} {P : β → Prop}
    (hf : ∀ a b, f₁ a = some b → f₂ a = some b ∧ P b) :
    ∀ (l : List α) (ys : List β), l.mapM f₁ = some ys → l.mapM f₂ = some ys ∧ ∀ y ∈ ys, P y
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ h => nomatch h⟩
  | a :: l, ys, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨hb₂, pb⟩ := hf a b hb
    obtain ⟨hbs₂, pbs⟩ := list_mapM_mono hf l bs hbs
    refine ⟨?_, ?_⟩
    · simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
      exact ⟨b, hb₂, bs, hbs₂, rfl⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact pb
      · exact pbs y hy

/-- **The analysis is monotone in its reference lookup**: a lookup that answers alike wherever
the first answers, with answers satisfying `P`, gives the same analysis, whose carriers and
major premise satisfy `P`. -/
theorem analyseWith_mono {c : Ixon.Constant} {r : Ixon.Recursor} {h₁ h₂ : Ixon.Expr → Option (ConstRef Address)}
    {P : ConstRef Address → Prop} (hh : ∀ e q, h₁ e = some q → h₂ e = some q ∧ P q)
    {x : Nat × Array (ConstRef Address) × ConstRef Address} (hx : analyseWith c r h₁ = some x) :
    analyseWith c r h₂ = some x ∧ (∀ y ∈ x.2.1, P y) ∧ P x.2.2 := by
  unfold analyseWith at hx ⊢
  simp only [bind, Option.bind_eq_some_iff, pure] at hx ⊢
  obtain ⟨⟨doms, body⟩, hs, hx⟩ := hx
  split at hx
  · rename_i k hk
    simp only [Option.bind_eq_some_iff] at hx
    obtain ⟨u, hg, carriers, hc, l, hl, major, hm, hx⟩ := hx
    cases Option.some.inj hx
    rw [Array.mapM_eq_mapM_toList, List.toList_toArray, Option.map_eq_map, Option.map_eq_some_iff] at hc
    obtain ⟨ys, hys, rfl⟩ := hc
    obtain ⟨hys₂, pys⟩ := list_mapM_mono (P := P)
      (f₂ := fun dom => (stripAllFull c spineFuel dom).fst.getLast?.bind fun e => h₂ e) (fun dom b hb => by
        obtain ⟨e, he, hb⟩ := Option.bind_eq_some_iff.mp hb
        exact ⟨Option.bind_eq_some_iff.mpr ⟨e, he, (hh e b hb).1⟩, (hh e b hb).2⟩) _ ys hys
    obtain ⟨hm₂, pm⟩ := hh l major hm
    refine ⟨⟨(doms, body), hs, ?_⟩, fun y hy => pys y (by simpa using hy), pm⟩
    simp only [hk, Option.bind_eq_some_iff]
    refine ⟨u, hg, ys.toArray, ?_, l, hl, major, hm₂, rfl⟩
    rw [Array.mapM_eq_mapM_toList, List.toList_toArray, hys₂]
    rfl
  · cases hx

/-- **The analysis the index files by, unfolded**: the analysis, the first carrier a member of
the block, the block a record of inductives, the carrier order valid. -/
theorem recursorAnalysis_spec {store : Store} {owner : Address} {c : Ixon.Constant} {r : Ixon.Recursor}
    {b : Address} {m : Nat} {cs : Array (ConstRef Address)} {mj : ConstRef Address} :
    recursorAnalysis? store owner c r = some (b, m, cs, mj) ↔
      analyseRecursor store owner c r = some (m, cs, mj) ∧ ∃ fi bc ms slot first,
        cs[0]? = some (.member b fi) ∧ store b = some bc ∧ bc.info = .muts ms ∧
        (inductives ms)[0]? = some (slot, first) ∧
        orderValid fi (inductives ms) (orderFor cs b (inductives ms).size) = true := by
  unfold recursorAnalysis?
  simp only [inductiveMembers_eq, motiveOrder_eq, motiveOrderValid_eq, bind, Option.bind_eq_some_iff]
  constructor
  · intro h
    obtain ⟨⟨m', cs', mj'⟩, ha, car, hcar, h⟩ := h
    split at h
    · rename_i block fi
      obtain ⟨bc, hbc, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i ms hms
        obtain ⟨⟨slot, first⟩, hfirst, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u, hg, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        have hv : orderValid fi (inductives ms) (orderFor cs' block (inductives ms).size) = true := by
          cases hc : orderValid fi (inductives ms) (orderFor cs' block (inductives ms).size)
          · simp [hc, guard, failure] at hg
          · rfl
        exact ⟨ha, fi, bc, ms, slot, first, hcar, hbc, hms, hfirst, hv⟩
      · cases h
    · cases h
  · rintro ⟨ha, fi, bc, ms, slot, first, hcar, hbc, hms, hfirst, hv⟩
    refine ⟨(m, cs, mj), ha, .member b fi, hcar, ?_⟩
    dsimp only
    rw [hbc, Option.bind_some]
    split
    · rename_i ms' hms'
      rw [hms] at hms'
      cases hms'
      rw [hfirst, Option.bind_some]
      simp [hv, guard, pure]
    · rename_i hne
      exact absurd hms (hne ms)

/-- **The filing analysis transfers between stores** that answer the analysis's reference
lookups alike (with answers in `D`), and agree on the records `D` holds. -/
theorem recursorAnalysis_transfer {s₁ s₂ : Store} {owner : Address} {c : Ixon.Constant} {r : Ixon.Recursor}
    {D : Address → Prop} (hh : ∀ e q, headRef s₁ owner c e = some q → headRef s₂ owner c e = some q ∧ D q.block)
    (hD : ∀ a bc, D a → s₁ a = some bc → s₂ a = some bc)
    {y : Address × Nat × Array (ConstRef Address) × ConstRef Address}
    (h : recursorAnalysis? s₁ owner c r = some y) :
    recursorAnalysis? s₂ owner c r = some y ∧ (∀ q ∈ y.2.2.1, D q.block) ∧ D y.2.2.2.block := by
  obtain ⟨b, m, cs, mj⟩ := y
  obtain ⟨ha, fi, bc, ms, slot, first, hcar, hbc, hms, hfirst, hv⟩ := recursorAnalysis_spec.mp h
  rw [analyse_eq] at ha
  obtain ⟨ha₂, pcs, pmj⟩ := analyseWith_mono (P := fun q => D q.block) hh ha
  have hb : D b := by
    have := pcs _ (Array.mem_of_getElem? hcar)
    simpa using this
  exact ⟨recursorAnalysis_spec.mpr ⟨by rw [analyse_eq]; exact ha₂, fi, bc, ms, slot, first, hcar,
    hD b bc hb hbc, hms, hfirst, hv⟩, pcs, pmj⟩

/-- A filing analysis is a candidate's provenance, for a record among the scanned ones. -/
theorem from_of_analysis {store : Store} {records : Array (Address × Ixon.Constant)} {owner : Address}
    {c : Ixon.Constant} {j : Nat} {r : Ixon.Recursor} {b : Address} {m : Nat} {cs : Array (ConstRef Address)}
    {mj : ConstRef Address} (present : (owner, c) ∈ records) (member : (j, r) ∈ recursorMembers c)
    (h : recursorAnalysis? store owner c r = some (b, m, cs, mj)) :
    ∃ first slot bc ms, store b = some bc ∧ bc.info = .muts ms ∧ (inductives ms)[0]? = some (slot, first) ∧
      From store records (.member owner j) ⟨b, m, mj, r.lvls.toNat == first.lvls.toNat + 1⟩ := by
  obtain ⟨ha, fi, bc, ms, slot, first, hcar, hbc, hms, hfirst, hv⟩ := recursorAnalysis_spec.mp h
  exact ⟨first, slot, bc, ms, hbc, hms, hfirst,
    owner, c, j, r, cs, fi, bc, ms, slot, first, rfl, present, member, ha, hcar, hbc, hms, hfirst, hv, rfl⟩

/-- A candidate's provenance is a filing analysis of a scanned record. -/
theorem analysis_of_from {store : Store} {records : Array (Address × Ixon.Constant)} {ref : ConstRef Address}
    {entry : RecEntry} (h : From store records ref entry) :
    ∃ owner c j r cs, ref = .member owner j ∧ (owner, c) ∈ records ∧ (j, r) ∈ recursorMembers c ∧
      recursorAnalysis? store owner c r = some (entry.block, entry.motive, cs, entry.major) := by
  obtain ⟨owner, c, j, r, cs, fi, bc, ms, slot, first, hr, present, member, ha, hcar, hbc, hms, hfirst, hv, -⟩ := h
  exact ⟨owner, c, j, r, cs, hr, present, member,
    recursorAnalysis_spec.mpr ⟨ha, fi, bc, ms, slot, first, hcar, hbc, hms, hfirst, hv⟩⟩

/-! ## Two invariants of the index builder -/

open Ix.CompileCert.ReaderIndex (Found BuildState candidate recordStep completeStep added candidate_step)
open Ix.CompileCert.CanonUnivMeaning (StepHolds)

/-- A block shape's order is the carrier order of a candidate analysed into the block. -/
def OrderBy (store : Store) (records : Array (Address × Ixon.Constant)) (index : RecIndex) : Prop :=
  ∀ b shape, index.blocks[b]? = some shape → ∃ owner c j r motive cs major fi bc ms slot first,
    (owner, c) ∈ records ∧ (j, r) ∈ recursorMembers c ∧
    analyseRecursor store owner c r = some (motive, cs, major) ∧
    cs[0]? = some (.member b fi) ∧ store b = some bc ∧ bc.info = .muts ms ∧
    (inductives ms)[0]? = some (slot, first) ∧ orderValid fi (inductives ms) (orderFor cs b (inductives ms).size) = true ∧
    shape.order = orderFor cs b (inductives ms).size

/-- The motives filed at each block are distinct. -/
def MotivesApart (found : Found) : Prop := ∀ b, ((found.getD b #[]).toList.map (·.1)).Nodup

/-- The builder's collected state. -/
abbrev collected (store : Store) (records : Array (Address × Ixon.Constant)) : BuildState :=
  forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)

theorem candidate_inv (store : Store) (records : Array (Address × Ixon.Constant)) (owner : Address)
    (c : Ixon.Constant) (present : (owner, c) ∈ records) (member : Nat × Ixon.Recursor)
    (memberPresent : member ∈ recursorMembers c) (before : BuildState)
    (valid : OrderBy store records before.1 ∧ MotivesApart before.2) :
    StepHolds (fun s => OrderBy store records s.1 ∧ MotivesApart s.2) (candidate store owner c member before) := by
  obtain ⟨after, ran, step⟩ := candidate_step store owner c member before
  rw [ran]
  cases step with
  | keep => exact valid
  | add motive carriers major block firstIndex blockRecord members slot first fresh analysed carrier stored
      kind firstFound guarded unused =>
    refine ⟨?_, ?_⟩
    · intro b shape found
      unfold added at found
      dsimp only at found
      split at found
      · exact valid.1 b shape found
      · rw [Std.HashMap.getElem?_insert] at found
        split at found
        · rename_i same
          have equal := beq_iff_eq.mp same
          subst b
          cases Option.some.inj found
          exact ⟨owner, c, member.1, member.2, motive, carriers, major, firstIndex, blockRecord, members, slot,
            first, present, memberPresent, analysed, carrier, stored, kind, firstFound, guarded, rfl⟩
        · exact valid.1 b shape found
    · show MotivesApart (added owner member before motive major block _ first).2
      rw [ReaderIndexDiscovery.added_found]
      intro b
      by_cases same : block == b
      · have equal := beq_iff_eq.mp same
        subst b
        simp only [Std.HashMap.getD_insert_self, Array.toList_push, List.map_append, List.map_cons,
          List.map_nil]
        refine (List.perm_append_comm.nodup_iff).mpr (List.nodup_cons.mpr ⟨?_, valid.2 block⟩)
        intro hm
        obtain ⟨x, hx, hxm⟩ := List.mem_map.mp hm
        have detected : (before.2.getD block #[]).any (·.1 == motive) = true :=
          Array.any_eq_true'.mpr ⟨x, Array.mem_toList_iff.mp hx, beq_iff_eq.mpr hxm⟩
        rw [unused] at detected
        cases detected
      · rw [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_insert]
        simp only [same, Bool.false_eq_true, ↓reduceIte]
        simpa only [Std.HashMap.getD_eq_getD_getElem?] using valid.2 b

/-- **The collected state's invariants**: shape orders are candidates' carrier orders, and the
motives filed at each block are distinct. -/
theorem collect_inv (store : Store) (records : Array (Address × Ixon.Constant)) :
    OrderBy store records (collected store records).1 ∧ MotivesApart (collected store records).2 :=
  CanonUnivEmit.arrayLoop_preserves (fun s : BuildState => OrderBy store records s.1 ∧ MotivesApart s.2)
    records ({}, {}) (recordStep store) ⟨fun b shape h => by simp at h, fun b => by simp⟩
    (fun record present state good =>
      CanonUnivEmit.arrayLoop_preserves (fun s : BuildState => OrderBy store records s.1 ∧ MotivesApart s.2)
        (recursorMembers record.2) state (candidate store record.1 record.2) good
        (fun member memberPresent state' good' =>
          candidate_inv store records record.1 record.2 present member memberPresent state' good'))

/-- One completion step's index: the block's shape with its pairs sorted. -/
def completed (e : Address × Array (Nat × ConstRef Address)) (idx : RecIndex) : RecIndex :=
  let sorted := e.2.qsort (fun x y => x.1 < y.1)
  let shape := idx.blocks.getD e.1 default
  { idx with blocks := idx.blocks.insert e.1 { shape with recs := sorted.map (·.2) } }

theorem complete_cons (e : Address × Array (Nat × ConstRef Address))
    (l : List (Address × Array (Nat × ConstRef Address))) (idx : RecIndex) :
    forIn (m := Id) (e :: l) idx completeStep = forIn (m := Id) l (completed e idx) completeStep := by
  simp only [List.forIn_cons]
  rfl

/-- The completion loop sets a block's recursors once: at its found pairs, sorted. -/
theorem complete_at (found : Found) (b : Address) (pairs : Array (Nat × ConstRef Address))
    (hb : found[b]? = some pairs) (index : RecIndex) (s : BlockShape) (hs : index.blocks[b]? = some s) :
    (forIn (m := Id) found.toList index completeStep).blocks[b]? =
      some { s with recs := (pairs.qsort (fun x y => x.1 < y.1)).map (·.2) } := by
  suffices h : ∀ (l : List (Address × Array (Nat × ConstRef Address))) (idx : RecIndex),
      (∀ e ∈ l, e.1 = b → e.2 = pairs) →
      ((b, pairs) ∈ l ∧ idx.blocks[b]? = some s ∨
        idx.blocks[b]? = some { s with recs := (pairs.qsort (fun x y => x.1 < y.1)).map (·.2) }) →
      (forIn (m := Id) l idx completeStep).blocks[b]? =
        some { s with recs := (pairs.qsort (fun x y => x.1 < y.1)).map (·.2) } by
    refine h _ index (fun e he hk => ?_) (.inl ⟨Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hb, hs⟩)
    have := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp he
    rw [hk, hb] at this
    exact (Option.some.inj this).symm
  intro l
  induction l with
  | nil =>
    intro idx _ h
    rcases h with ⟨h, -⟩ | h
    · exact absurd h List.not_mem_nil
    · exact h
  | cons e l ih =>
    intro idx hl h
    rw [complete_cons]
    refine ih _ (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) ?_
    by_cases same : e.1 = b
    · have hv := hl e List.mem_cons_self same
      obtain ⟨e1, e2⟩ := e
      simp only at same hv
      subst same hv
      refine .inr ?_
      change (idx.blocks.insert e1 _)[e1]? = _
      rw [Std.HashMap.getElem?_insert_self, Std.HashMap.getD_eq_getD_getElem?]
      rcases h with ⟨-, h⟩ | h <;> rw [h] <;> rfl
    · have keep : (completed e idx).blocks[b]? = idx.blocks[b]? := by
        change (idx.blocks.insert e.1 _)[b]? = _
        rw [Std.HashMap.getElem?_insert]
        simp [beq_iff_eq, same]
      rw [keep]
      rcases h with ⟨hm, h⟩ | h
      · rcases List.mem_cons.mp hm with he | hm
        · exact absurd (congrArg Prod.fst he).symm same
        · exact .inl ⟨hm, h⟩
      · exact .inr h

/-- **A block's shape in the index**: its order is the collected one, a candidate's carrier
order, and its recursors are its found pairs sorted by motive. -/
theorem buildIndex_at (store : Store) (records : Array (Address × Ixon.Constant)) {b : Address}
    {shape : BlockShape} (h : (buildIndex store records).blocks[b]? = some shape)
    {pairs : Array (Nat × ConstRef Address)} (hp : (collected store records).2[b]? = some pairs) :
    ∃ s, (collected store records).1.blocks[b]? = some s ∧
      shape = { s with recs := (pairs.qsort (fun x y => x.1 < y.1)).map (·.2) } := by
  obtain ⟨s, hs⟩ := (ReaderIndex.collect_valid store records).2 b pairs hp
  refine ⟨s, hs, ?_⟩
  rw [← ReaderIndex.run_eq] at h
  unfold ReaderIndex.run at h
  rw [complete_at (collected store records).2 b pairs hp _ s hs] at h
  exact (Option.some.inj h).symm

/-- The index's recursors are the collected ones: completion only sorts block shapes. -/
theorem buildIndex_recs (store : Store) (records : Array (Address × Ixon.Constant)) :
    (buildIndex store records).recs = (collected store records).1.recs := by
  rw [← ReaderIndex.run_eq]
  exact ReaderIndexDiscovery.complete_recs _ _

theorem mem_getD {m : Std.HashMap Address (Array (Nat × ConstRef Address))} {k : Address}
    {x : Nat × ConstRef Address} (h : x ∈ m.getD k #[]) : ∃ v, m[k]? = some v ∧ x ∈ v := by
  rw [Std.HashMap.getD_eq_getD_getElem?] at h
  cases hk : m[k]? with
  | none => rw [hk] at h; simp at h
  | some v => rw [hk] at h; exact ⟨v, rfl, h⟩

/-- **A list sorted by distinct motives) is determined**: found pairs whose motives are distinct,
each `(j, g j)` for `j < N` and all of them there, sort to `g 0, …, g (N - 1)`. -/
theorem sorted_eq_range {pairs : Array (Nat × ConstRef Address)} {N : Nat} {g : Nat → ConstRef Address}
    (apart : (pairs.toList.map (·.1)).Nodup) (sub : ∀ p ∈ pairs, p.1 < N ∧ p.2 = g p.1)
    (sup : ∀ j < N, (j, g j) ∈ pairs) :
    ((pairs.qsort (fun x y => x.1 < y.1)).map (·.2)).toList = (List.range N).map g := by
  let T : List (Nat × ConstRef Address) := (List.range N).map fun j => (j, g j)
  have memT : ∀ x, x ∈ T ↔ x ∈ pairs := by
    intro x
    constructor
    · intro hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact sup j (List.mem_range.mp hj)
    · intro hx
      obtain ⟨hlt, hg⟩ := sub x hx
      exact List.mem_map.mpr ⟨x.1, List.mem_range.mpr hlt, by rw [← hg]⟩
  have nodupT : T.Nodup :=
    List.Pairwise.map (fun j => (j, g j)) (fun a b hab heq => hab (congrArg Prod.fst heq)) List.nodup_range
  have nodupP : pairs.toList.Nodup := by
    unfold List.Nodup at apart ⊢
    exact List.Pairwise.of_map _ (fun a b h heq => h (congrArg Prod.fst heq)) apart
  have permT : pairs.toList.Perm T :=
    (List.perm_ext_iff_of_nodup nodupP nodupT).mpr fun x => by
      rw [Array.mem_toList_iff, memT]
  have sortedT : T.Pairwise (fun a b => decide (b.1 < a.1) = false) := by
    refine List.pairwise_map.mpr ?_
    refine List.Pairwise.imp (fun {a b} (h : a < b) => ?_) List.pairwise_lt_range
    simp only [decide_eq_false_iff_not, Nat.not_lt]
    exact Nat.le_of_lt h
  have sorted := Canon.qsort_pairwise pairs (fun x y => x.1 < y.1) (fun a => by simp)
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
  have eq : (pairs.qsort (fun x y => x.1 < y.1)).toList = T := by
    refine List.Perm.eq_of_pairwise (fun a b ha hb hab hba => ?_) sorted sortedT
      ((Canon.qsort_perm pairs _).toList.trans permT)
    have ha' : a ∈ T := (memT a).mpr ((Canon.mem_qsort (lt := fun x y => x.1 < y.1)).mp (Array.mem_toList_iff.mp ha))
    have hab' : a.1 = b.1 := by
      simp only [decide_eq_false_iff_not, Nat.not_lt] at hab hba
      omega
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hb
    simp only at hab'
    rw [hab']
  rw [Array.toList_map, eq, List.map_map]
  rfl

/-! ## A recursor's name and its motive -/

/-- The motive a name gives is below the family's motive count. -/
theorem namedMotive_lt {first : Ix.InductiveVal} {x : Ix.Name} {m : Nat} (h : namedMotive? first x = some m) :
    m < first.all.size + first.numNested := by
  unfold namedMotive? at h
  cases hf : first.all.toList.findIdx? (fun T => Ix.LeanIngress.isStrName T "rec" x) with
  | some i =>
    simp only [hf, Option.orElse, Option.some.injEq] at h
    subst h
    obtain ⟨hi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp only [Array.length_toList] at hi
    omega
  | none =>
    simp only [hf, Option.orElse, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    omega

/-- **The motive a name gives is at most its position in `blockRecursors`' order**: the name
matches that position's pattern, and the lookups return their first match. -/
theorem namedMotive_le {first : Ix.InductiveVal} {x : Ix.Name} {m j : Nat} (h : namedMotive? first x = some m)
    (w : (∃ hj : j < first.all.size, Ix.LeanIngress.isStrName first.all[j] "rec" x = true) ∨
      (first.all.size ≤ j ∧ j - first.all.size < first.numNested ∧
        Ix.LeanIngress.isStrName first.cnst.name s!"rec_{j - first.all.size + 1}" x = true)) : m ≤ j := by
  unfold namedMotive? at h
  cases hf : first.all.toList.findIdx? (fun T => Ix.LeanIngress.isStrName T "rec" x) with
  | some i =>
    simp only [hf, Option.orElse, Option.some.injEq] at h
    subst h
    obtain ⟨hi, -, before⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp only [Array.length_toList] at hi
    rcases w with ⟨hj, hw⟩ | ⟨hj, -, -⟩
    · refine Nat.le_of_not_lt fun hlt => before j hlt ?_
      simpa only [Array.getElem_toList] using hw
    · omega
  | none =>
    simp only [hf, Option.orElse, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    rcases w with ⟨hj, hw⟩ | ⟨hj, hn, hw⟩
    · have := List.findIdx?_eq_none_iff.mp hf first.all[j] (Array.getElem_mem_toList hj)
      rw [hw] at this
      cases this
    · obtain ⟨-, i, hi, hik, before⟩ := List.find?_eq_some_iff_getElem.mp hk
      simp only [List.getElem_range] at hik
      subst hik
      refine Nat.add_le_of_le_sub' hj (Nat.le_of_not_lt fun hlt => ?_)
      have := before (j - first.all.size) hlt
      simp only [List.getElem_range] at this
      rw [hw] at this
      cases this

/-- **`blockRecursors`' order**: `T.rec` for each member `T` of the first type's block, then
`first.rec_{j+1}` for each nested auxiliary motive. -/
theorem blockRecursors_at {first : Ix.InductiveVal} {cands recs : Array Ix.RecursorVal}
    (h : Ix.LeanIngress.blockRecursors first cands = .ok recs) :
    recs.size = first.all.size + first.numNested ∧ ∀ j (hj : j < recs.size),
      (∃ hj' : j < first.all.size, Ix.LeanIngress.isStrName first.all[j] "rec" recs[j].cnst.name = true) ∨
      (first.all.size ≤ j ∧ j - first.all.size < first.numNested ∧
        Ix.LeanIngress.isStrName first.cnst.name s!"rec_{j - first.all.size + 1}" recs[j].cnst.name = true) := by
  have found : ∀ {q : Ix.RecursorVal → Bool} {e : String} {y : Ix.RecursorVal},
      (match cands.find? q with
        | some r => (pure r : Except String Ix.RecursorVal)
        | none => throw e) = .ok y → q y = true := by
    intro q e y hy
    cases hq : cands.find? q with
    | none => rw [hq] at hy; cases hy
    | some r =>
      rw [hq] at hy
      cases hy
      exact Array.find?_some hq
  unfold Ix.LeanIngress.blockRecursors at h
  obtain ⟨own, hown, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  obtain ⟨aux, haux, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have fo := ReaderUnits.array_mapM_ok hown
  have fa := ReaderUnits.array_mapM_ok haux
  have lo : own.size = first.all.size := by
    have := InductiveCompile.forall₂_length fo
    simpa using this.symm
  have la : aux.size = first.numNested := by
    have := InductiveCompile.forall₂_length fa
    simpa using this.symm
  refine ⟨by rw [Array.size_append, lo, la], fun j hj => ?_⟩
  by_cases hjo : j < own.size
  · refine .inl ⟨lo ▸ hjo, ?_⟩
    rw [Array.getElem_append_left hjo]
    have := InductiveCompile.forall₂_getElem fo j (by simpa [lo] using hjo) (by simpa using hjo)
    simp only [Array.getElem_toList] at this
    exact found this
  · refine .inr ⟨by omega, by rw [Array.size_append] at hj; omega, ?_⟩
    rw [Array.getElem_append_right (by omega)]
    have hk : j - own.size < aux.size := by rw [Array.size_append] at hj; omega
    have := InductiveCompile.forall₂_getElem fa (j - own.size) (by simpa [la] using hk) (by simpa using hk)
    simp only [Array.getElem_toList, Array.toList_range, List.getElem_range] at this
    rw [← lo]
    exact found this

/-! ## Level parameters -/

/-- A large eliminator's own numbering of distinct level parameters: its first parameter is
the last position, the others count from `0`. -/
theorem params_large {names : Array Ix.Name} (hnd : names.toList.Nodup) (hpos : 0 < names.size) :
    (Ix.LeanIngress.Numbering.mk names true).params = (names.size - 1) :: List.range (names.size - 1) := by
  have hpos' : ∀ i (hi : i < names.size),
      (Ix.LeanIngress.Numbering.mk names true).pos names[i] = if i = 0 then names.size - 1 else i - 1 := by
    intro i hi
    rcases names with ⟨l⟩
    have h := RecordReadings.findIdx?_beqRaw_nodup hnd (i := i) (by simpa using hi)
    have h' : (List.toArray l).findIdx? (Ix.Name.beqRaw · (List.toArray l)[i]) = some i := by
      simpa [List.findIdx?_toArray] using h
    unfold Ix.LeanIngress.Numbering.pos
    simp only [h']
    cases i <;> simp
  apply List.ext_getElem
  · simp only [Ix.LeanIngress.Numbering.params, List.length_map, Array.length_toList, List.length_cons,
      List.length_range]
    omega
  · intro i h₁ h₂
    simp only [Ix.LeanIngress.Numbering.params, List.getElem_map, Array.getElem_toList]
    rw [hpos' i (by simpa [Ix.LeanIngress.Numbering.params] using h₁)]
    cases i with
    | zero => simp
    | succ k => simp

/-- **A recursor's level parameters, as the reader and quotient Source number them**: with
distinct names, of the family's count `L` or one more, the reader's `recLps` at the large flag
is quotient Source's numbering. -/
theorem recLps_params {names : Array Ix.Name} {L : Nat} (hnd : names.toList.Nodup)
    (size : names.size = L ∨ names.size = L + 1) :
    recLps (names.size == L + 1) (List.range L) =
      (Ix.LeanIngress.Numbering.mk names (names.size == L + 1)).params := by
  rcases size with h | h
  · have hf : (names.size == L + 1) = false := by simp [h]
    rw [hf, RecordReadings.params_nodup hnd, h]
    rfl
  · have ht : (names.size == L + 1) = true := by simp [h]
    rw [ht, params_large hnd (by omega), h]
    simp [recLps]

/-! ## A recursor references its rules' constructors -/

open Ix.Cert.GraphWalk (MemoOK) in
theorem forIn_rules_ctor (f : Ix.RecursorRule → Ix.Set Ix.Name → Ix.GraphM (ForInStep (Ix.Set Ix.Name)))
    (hf : ∀ rule r env s, f rule r env s =
      (.yield ((r.insert rule.ctor).union (Ix.graphExpr rule.rhs env s).1), (Ix.graphExpr rule.rhs env s).2))
    (env : Ix.Environment) :
    ∀ (rules : List Ix.RecursorRule) (r0 : Ix.Set Ix.Name) (s : Ix.GraphState), MemoOK s →
      ∀ rule ∈ rules, (forIn rules r0 f env s).1.contains rule.ctor = true
  | [], _, _, _ => fun _ h => nomatch h
  | rule :: rules, r0, s, hs => by
    obtain ⟨s1, -⟩ := GraphWalk.graphExpr_refs rule.rhs env s hs
    have step : forIn (rule :: rules) r0 f env s =
        forIn rules ((r0.insert rule.ctor).union (Ix.graphExpr rule.rhs env s).1) f env
          (Ix.graphExpr rule.rhs env s).2 := by
      rw [List.forIn_cons, GraphWalk.bind_run, hf]
    rw [step]
    obtain ⟨keep, -⟩ := GraphWalk.forIn_rules f hf env rules _ _ s1
    intro rule' hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact keep _ (GraphWalk.contains_union_iff.mpr (.inl (GraphWalk.contains_insert_iff.mpr (.inl BEq.rfl))))
    · exact forIn_rules_ctor f hf env rules _ _ s1 rule' hr

/-- **A recursor references each rule's constructor.** -/
theorem refsOf_rule (v : Ix.RecursorVal) {rule : Ix.RecursorRule} (hr : rule ∈ v.rules.toList) :
    (refsOf (.recInfo v)).contains rule.ctor = true := by
  obtain ⟨st, -⟩ := GraphWalk.graphExpr_refs v.cnst.type { consts := {} } Ix.GraphState.init GraphWalk.memoOK_init
  show (Ix.graphConst (.recInfo v) { consts := {} } Ix.GraphState.init).1.contains rule.ctor = true
  rw [Ix.graphConst, GraphWalk.bind_run, GraphWalk.bind_run, ← Array.forIn_toList]
  refine GraphWalk.foldl_insert_keeps _ _ _ ?_
  exact forIn_rules_ctor _ (fun _ _ _ _ => rfl) _ v.rules.toList _ _ st rule hr

/-! ## The compile's headers -/

section Headers

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline

/-- What a member's compiled payload keeps of its counts: an inductive's header, a recursor's. -/
def HeaderOf : MutConst → Ixon.MutConst → Prop
  | .defn _, _ => True
  | .indc i, p => ∃ t, p = .indc t ∧ ProjectionLayout.IndHeader i t
  | .recr r, p => ∃ t, p = .recr t ∧ BlockEmission.RecHeader r t

theorem member_header (context : CompileEnv × BlockEnv) (m : MutConst) {before after : BlockState}
    {member : CompiledMutConstMember} (ran : rawRun (compileMutConstMember m) context before = (.ok member, after)) :
    HeaderOf m member.payload := by
  cases m with
  | defn d => trivial
  | indc i =>
    obtain ⟨out, outRan, hp⟩ := BlockEmission.member_indc i ran
    obtain ⟨header, -, -⟩ := ProjectionLayout.inductiveData_headers i _ _ _ _ outRan
    exact ⟨out.1, hp, header⟩
  | recr r =>
    obtain ⟨out, outRan, hp⟩ := BlockEmission.member_recr r ran
    exact ⟨out.1, hp, BlockEmission.recursor_headers r _ _ _ _ outRan⟩

theorem classes_headers (context : CompileEnv × BlockEnv) :
    ∀ (ms : List MutConst) (acc : MutConstCompileState) {before after : BlockState} {state : MutConstCompileState},
      rawRun (compileMutConstClasses (ms.map ([·])) acc) context before = (.ok state, after) →
      ∃ ps : List Ixon.MutConst, state.payloads = acc.payloads ++ ps.toArray ∧ List.Forall₂ HeaderOf ms ps
  | [], acc, before, after, state, ran => by
    rw [List.map_nil, compileMutConstClasses, rawRun_pure] at ran
    cases ran
    exact ⟨[], by simp, .nil⟩
  | m :: ms, acc, before, after, state, ran => by
    rw [List.map_cons, compileMutConstClasses] at ran
    obtain ⟨classState, middle, classRan, restRan⟩ := bind_ok ran
    rw [compileMutConstClass] at classRan
    obtain ⟨member, memberMiddle, memberRan, equivRan⟩ := bind_ok classRan
    rw [compileEquivalentMutConsts, rawRun_pure] at equivRan
    cases equivRan
    obtain ⟨ps, hps, headers⟩ := classes_headers context ms _ restRan
    refine ⟨member.payload :: ps, ?_, .cons (member_header context m memberRan) headers⟩
    rw [hps]
    simp [MutConstCompileState.addRepresentative]

/-- **A block compiled one member per class keeps its members' headers**: its record is its
payloads' block up to the expressions' roots. -/
theorem block_headers {ms : List MutConst} {context : CompileEnv × BlockEnv} {before after : BlockState}
    {output : BlockResult} (ran : rawRun (compileMutualBlock (ms.map ([·]))) context before = (.ok output, after)) :
    ∃ ps : List Ixon.MutConst, List.Forall₂ HeaderOf ms ps ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (BlockEmission.blockInfo ps) := by
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, seededState, seeded, compiled⟩ := bind_ok ran
  unfold compileMutualPayload at compiled
  obtain ⟨payload, middle, payloadRan, finished⟩ := bind_ok compiled
  unfold compileMutConsts at payloadRan
  obtain ⟨state, middle', classesRan, finish⟩ := bind_ok payloadRan
  rw [rawRun_pure] at finish
  cases finish
  obtain ⟨ps, hps, headers⟩ := classes_headers _ ms {} classesRan
  obtain ⟨same, _, built⟩ := ProjectionLayout.finish_mutual_ok _ _ _ _ finished
  subst same
  simp only [hps] at built
  have hps' : (({} : MutConstCompileState).payloads ++ ps.toArray) = ps.toArray := by simp
  rw [hps'] at built
  unfold buildCompiledMutualBlock at built
  refine ⟨ps, headers, ?_⟩
  cases hs : standaloneMutConstInfo? ps.toArray with
  | some info =>
    rw [hs] at built
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok built
    cases Except.ok.inj returned
    have hinfo : BlockEmission.blockInfo ps = info := by unfold BlockEmission.blockInfo; rw [hs]
    rw [hinfo]
    exact (SharingRoots.build_roots (md := .anon) _ _ _ _ _ hb).1
  | none =>
    rw [hs] at built
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok built
    cases Except.ok.inj returned
    have hinfo : BlockEmission.blockInfo ps = .muts ps.toArray := by unfold BlockEmission.blockInfo; rw [hs]
    rw [hinfo]
    exact (SharingRoots.build_roots (md := .anon) _ _ _ _ _ hb).1

/-- **A lone recursor compiled as a single constant keeps its header.** -/
theorem lone_header {r : Ix.RecursorVal} {context : CompileEnv × BlockEnv} {before after : BlockState}
    {output : BlockResult} (ran : rawRun (compileConstantInfo (.recInfo r)) context before = (.ok output, after)) :
    ∃ t, SharingRoots.erase output.block.info = SharingRoots.erase (BlockEmission.blockInfo [.recr t]) ∧
      BlockEmission.RecHeader r t := by
  rw [EmissionDispatch.recursor_run context r before] at ran
  unfold compileRecursorInfo at ran
  obtain ⟨_, _, _, compiled⟩ := bind_ok ran
  unfold compileRecursorBlock at compiled
  obtain ⟨value, hrun, hbuild, -⟩ := EmissionBlocks.block_ok (fun p => .recr p.1) (fun p => p.2.1)
    (fun p => by obtain ⟨_, _, _⟩ := p; rfl) compiled
  exact ⟨value.1, (SharingRoots.build_roots (md := .anon) _ _ _ _ _ hbuild).1,
    BlockEmission.recursor_headers r _ _ _ _ hrun⟩

theorem recHeader_erase {r : Ix.RecursorVal} {t t' : Ixon.Recursor} (h : BlockEmission.RecHeader r t)
    (e : SharingRoots.eraseMut (.recr t') = SharingRoots.eraseMut (.recr t)) : BlockEmission.RecHeader r t' := by
  simp only [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots, Ixon.MutConst.recr.injEq,
    Ixon.Recursor.mk.injEq] at e
  obtain ⟨-, -, hl, hp, hi, hm, hn, -, -⟩ := e
  obtain ⟨lvls, params, indices, motives, minors, bounded⟩ := h
  exact ⟨hl ▸ lvls, hp ▸ params, hi ▸ indices, hm ▸ motives, hn ▸ minors, bounded⟩

theorem indHeader_erase {i : Ix.Ind} {t t' : Ixon.Inductive} (h : ProjectionLayout.IndHeader i t)
    (e : SharingRoots.eraseMut (.indc t') = SharingRoots.eraseMut (.indc t)) : ProjectionLayout.IndHeader i t' := by
  simp only [SharingRoots.eraseMut, Ix.Sharing.Exact.mapMutConstRoots, Ixon.MutConst.indc.injEq,
    Ixon.Inductive.mk.injEq] at e
  obtain ⟨-, hl, hp, hi, -, hc⟩ := e
  have hsize : t'.ctors.size = t.ctors.size := by
    have := congrArg Array.size hc
    simpa using this
  obtain ⟨lvls, params, indices, size⟩ := h
  exact ⟨hl ▸ lvls, hp ▸ params, hi ▸ indices, hsize ▸ size⟩

theorem headers_indcs : ∀ {inds : List Ix.Ind} {ps : List Ixon.MutConst},
    List.Forall₂ HeaderOf (inds.map MutConst.indc) ps →
      ∃ ts : List Ixon.Inductive, ps = ts.map .indc ∧ List.Forall₂ ProjectionLayout.IndHeader inds ts
  | [], [], _ => ⟨[], rfl, .nil⟩
  | i :: inds, p :: ps, .cons ⟨t, hp, ht⟩ rest => by
    obtain ⟨ts, rfl, hts⟩ := headers_indcs rest
    exact ⟨t :: ts, by rw [hp]; rfl, .cons ht hts⟩

theorem headers_recrs : ∀ {recs : List Ix.RecursorVal} {ps : List Ixon.MutConst},
    List.Forall₂ HeaderOf (recs.map MutConst.recr) ps →
      ∃ ts : List Ixon.Recursor, ps = ts.map .recr ∧ List.Forall₂ BlockEmission.RecHeader recs ts
  | [], [], _ => ⟨[], rfl, .nil⟩
  | r :: recs, p :: ps, .cons ⟨t, hp, ht⟩ rest => by
    obtain ⟨ts, rfl, hts⟩ := headers_recrs rest
    exact ⟨t :: ts, by rw [hp]; rfl, .cons ht hts⟩

theorem forall₂_erase {α β : Type} {R : α → β → Prop} {S : β → β → Prop} {T : α → β → Prop}
    (h : ∀ a b b', R a b → S b' b → T a b') :
    ∀ {l : List α} {m m' : List β}, List.Forall₂ R l m → List.Forall₂ S m' m → List.Forall₂ T l m'
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons r rs, .cons s ss => .cons (h _ _ _ r s) (forall₂_erase h rs ss)

/-- **A recursor family's record's members** are the family's recursors, each with its
header, whichever way it was compiled. -/
theorem family_members {recs : List Ix.RecursorVal} (hne : recs ≠ []) {c : Ixon.Constant}
    {ts : List Ixon.Recursor} (same : SharingRoots.erase c.info = SharingRoots.erase (BlockEmission.blockInfo (ts.map .recr)))
    (headers : List.Forall₂ BlockEmission.RecHeader recs ts) :
    ∀ p rI, (p, rI) ∈ recursorMembers c → ∃ hp : p < recs.length, BlockEmission.RecHeader recs[p] rI := by
  obtain ⟨ts', hinfo, herase⟩ := InductiveCompile.erase_recrs same
  have headers' : List.Forall₂ BlockEmission.RecHeader recs ts' :=
    forall₂_erase (R := BlockEmission.RecHeader) (T := BlockEmission.RecHeader)
      (S := fun t' t => SharingRoots.eraseMut (.recr t') = SharingRoots.eraseMut (.recr t))
      (fun _ _ _ h e => recHeader_erase h e) headers herase
  have hlen := InductiveCompile.forall₂_length headers'
  intro p rI hm
  have source := ReaderIndex.member_source c p rI hm
  rcases ts' with _ | ⟨u, _ | ⟨u₂, rest⟩⟩
  · cases recs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hlen
  · have hi : c.info = .recr u := hinfo
    rw [hi] at source
    obtain ⟨rfl, rfl⟩ := source
    have h0 : 0 < recs.length := by simp at hlen; omega
    exact ⟨h0, InductiveCompile.forall₂_getElem headers' 0 h0 (by simp)⟩
  · have hi : c.info = .muts ((u :: u₂ :: rest).map Ixon.MutConst.recr).toArray := hinfo
    rw [hi] at source
    have hs : ((u :: u₂ :: rest).map Ixon.MutConst.recr)[p]? = some (.recr rI) := by simpa using source
    rw [List.getElem?_map, Option.map_eq_some_iff] at hs
    obtain ⟨v, hv, hve⟩ := hs
    cases hve
    obtain ⟨hp, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    have hp' : p < recs.length := by rw [hlen]; exact hp
    exact ⟨hp', InductiveCompile.forall₂_getElem headers' p hp' hp⟩

end Headers

/-! ## The inductives of a block of inductives -/

theorem filterMap_indcs (f : Ixon.MutConst × Nat → Option (Nat × Ixon.Inductive))
    (hf : ∀ t k, f (.indc t, k) = some (k, t)) :
    ∀ (ts : List Ixon.Inductive) (k : Nat),
      ((ts.map Ixon.MutConst.indc).zipIdx k).filterMap f = (ts.zipIdx k).map fun p => (p.2, p.1)
  | [], _ => rfl
  | t :: ts, k => by
    rw [List.map_cons, List.zipIdx_cons, List.zipIdx_cons, List.filterMap_cons, hf, List.map_cons,
      filterMap_indcs f hf ts (k + 1)]

theorem inductives_indcs (ts : List Ixon.Inductive) :
    (inductives (ts.map Ixon.MutConst.indc).toArray).toList = ts.zipIdx.map fun p => (p.2, p.1) := by
  unfold inductives
  rw [Array.toList_filterMap, Array.toList_zipIdx, List.toList_toArray]
  exact filterMap_indcs _ (fun t k => rfl) ts 0

theorem inductives_indcs_size (ts : List Ixon.Inductive) :
    (inductives (ts.map Ixon.MutConst.indc).toArray).size = ts.length := by
  rw [← Array.length_toList, inductives_indcs]
  simp

theorem inductives_indcs_get (ts : List Ixon.Inductive) (i : Nat) :
    (inductives (ts.map Ixon.MutConst.indc).toArray)[i]? = (ts[i]?).map ((i, ·)) := by
  rw [← Array.getElem?_toList, inductives_indcs, List.getElem?_map, List.getElem?_zipIdx]
  cases ts[i]? <;> simp

/-- An analysed recursor's motive is one of its motives. -/
theorem analyse_motive_lt {store : Store} {owner : Address} {c : Ixon.Constant} {r : Ixon.Recursor} {m : Nat}
    {cs : Array (ConstRef Address)} {mj : ConstRef Address} (h : analyseRecursor store owner c r = some (m, cs, mj)) :
    m < r.motives.toNat := by
  rw [analyse_eq] at h
  unfold analyseWith at h
  simp only [bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨⟨doms, body⟩, -, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨u, hg, carriers, hc, l, hl, major, hm, hx⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, -, -⟩ := hx
    unfold guard at hg
    split at hg
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      omega
    · cases hg
  · cases h

/-! ## The artifact's stored records -/

theorem mem_storedRecords {ixe : Ixon.Env} {o : Address} {c : Ixon.Constant} (hc : recordAt ixe o = some c) :
    (o, c) ∈ storedRecords ixe := by
  obtain ⟨lc, hlc, hget⟩ : ∃ lc, ixe.consts.get? o = some lc ∧ lc.get? = some c := by
    unfold recordAt at hc
    cases hl : ixe.consts.get? o with
    | none => rw [hl] at hc; cases hc
    | some lc => rw [hl] at hc; exact ⟨lc, rfl, hc⟩
  have hin : (o, lc) ∈ ixe.consts.toArray := by
    rw [Std.HashMap.mem_toArray_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact hlc
  exact Array.mem_filterMap.mpr ⟨(o, lc), hin, by simp [hget]⟩

theorem storedRecords_coherent (ixe : Ixon.Env) : Coherent (recordAt ixe) (storedRecords ixe) := by
  intro a c h
  obtain ⟨⟨a', lc⟩, hin, he⟩ := Array.mem_filterMap.mp h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at he
  obtain ⟨c', hc', rfl, rfl⟩ := he
  have hget : ixe.consts.get? a' = some lc := by
    rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.mem_toArray_iff_getElem?_eq_some]
    exact hin
  unfold recordAt
  rw [hget]
  exact hc'

/--
info: 'Ix.Cert.RecursorIndex.analyseWith_mono' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms analyseWith_mono

/--
info: 'Ix.Cert.RecursorIndex.buildIndex_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms buildIndex_at

/--
info: 'Ix.Cert.RecursorIndex.sorted_eq_range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sorted_eq_range

/--
info: 'Ix.Cert.RecursorIndex.block_headers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms block_headers

end Ix.Cert.RecursorIndex
