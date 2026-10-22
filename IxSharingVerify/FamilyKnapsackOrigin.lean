import IxSharingVerify.FamilySlack
import IxSharingVerify.UniformOptimality

/-! Exact entry witnesses for the existing knapsack. These lemmas preserve
both signed deltas and merged sets, independently of optimality or a finisher. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (setBang_getElem!)

def joinEntry (a b : Entry) : Entry := (a.1 + b.1, mergeSorted a.2 b.2)

def RowsIn (tables : List CTable) (entries : List Entry) : Prop :=
  List.Forall₂ (fun tb e => ∃ k : Nat, tb[k]! = some e) tables entries

def EntryOrigin (tables : List CTable) (value : Entry) : Prop :=
  ∃ entries, RowsIn tables entries ∧ value = entries.foldl joinEntry (0, #[])

/-- Every new step entry is exactly the sum-and-merge of two actual rows. -/
theorem knapStep_entry_origin {cap : Nat} {dp bySize : CTable} :
    ∀ (j : Nat) (e : Entry), (knapStep cap dp bySize)[j]! = some e →
      ∃ (c k : Nat) (ec ek : Entry), dp[c]! = some ec ∧ bySize[k]! = some ek ∧
        e = joinEntry ec ek := by
  rw [knapStep_eq]
  let P : CTable → Prop := fun t => ∀ (j : Nat) (e : Entry), t[j]! = some e →
    ∃ (c k : Nat) (ec ek : Entry), dp[c]! = some ec ∧ bySize[k]! = some ek ∧
      e = joinEntry ec ek
  have h0 : P (Array.replicate (cap + 1) none) := fun j e he => by
    by_cases hk : j < cap + 1
    · rw [getElem!_pos _ j (by simpa using hk)] at he; simp at he
    · simp [hk] at he
  have hin : ∀ (c : Nat) (d : _root_.Int) (s : Array Nat), dp[c]! = some (d, s) → ∀ acc k,
      P acc → P (knapIn cap c d s bySize acc k) := by
    intro c d s hdc acc k hacc
    rw [knapIn_eq]
    cases hbk : bySize[k]! with
    | none => exact hacc
    | some ek =>
      obtain ⟨dk, sk⟩ := ek
      simp only
      split
      · exact hacc
      · split
        · intro j x hx
          rw [setBang_getElem!] at hx
          split at hx
          · cases hx; exact ⟨c, k, _, _, hdc, hbk, rfl⟩
          · exact hacc j x hx
        · exact hacc
  have hout : ∀ acc c, P acc → P (knapOut cap dp bySize acc c) := by
    intro acc c hacc
    unfold knapOut
    cases hdc : dp[c]! with
    | none => exact hacc
    | some e =>
      obtain ⟨d, s⟩ := e
      simp only
      generalize List.range bySize.size = l
      induction l generalizing acc with
      | nil => exact hacc
      | cons k l ih => rw [List.foldl_cons]; exact ih _ (hin c d s hdc acc k hacc)
  exact foldl_inv (knapOut cap dp bySize) P hout _ _ h0

/-- A fold chooses one row from each table, in table order. -/
theorem knapFold_entry_origin (cap : Nat) (tables : List CTable) (dp : CTable)
    {j : Nat} {e : Entry} (row : (tables.foldl (knapStep cap) dp)[j]! = some e) :
    ∃ start entries, (∃ k : Nat, dp[k]! = some start) ∧ RowsIn tables entries ∧
      e = entries.foldl joinEntry start := by
  induction tables generalizing dp with
  | nil => exact ⟨e, [], ⟨j, row⟩, List.Forall₂.nil, rfl⟩
  | cons tb tables ih =>
    obtain ⟨start, entries, ⟨k, first⟩, rest, result⟩ := ih _ row
    obtain ⟨c, n, ec, ek, hc, hk, he⟩ := knapStep_entry_origin k start first
    exact ⟨ec, ek :: entries, ⟨c, hc⟩, List.Forall₂.cons ⟨n, hk⟩ rest,
      by simpa only [List.foldl_cons, ← he] using result⟩

theorem knapSeed_entry {cap k : Nat} {e : Entry}
    (row : (#[some ((0 : _root_.Int), (#[] : Array Nat))] ++ Array.replicate cap none)[k]! = some e) :
    e = (0, #[]) := by
  by_cases hk : k = 0
  · subst hk
    rw [getElem!_pos _ 0 (by rw [Array.size_append]; simp; omega)] at row
    simpa using row.symm
  · by_cases hk' : k < 1 + cap
    · rw [getElem!_pos _ k (by simp; omega), Array.getElem_append_right (by simp; omega)] at row
      simp at row
    · simp [show ¬ k < 1 + cap by omega] at row

theorem knapFold_origin (cap : Nat) (tables : List CTable) {j : Nat} {e : Entry}
    (row : (tables.foldl (knapStep cap)
      (#[some (0, #[])] ++ Array.replicate cap none))[j]! = some e) : EntryOrigin tables e := by
  obtain ⟨start, entries, ⟨k, first⟩, rest, result⟩ := knapFold_entry_origin cap tables _ row
  exact ⟨entries, rest, by simpa only [knapSeed_entry first] using result⟩

theorem joinEntry_fold (entries : List Entry) (start : Entry) :
    (entries.foldl joinEntry start).1 = start.1 + (entries.map Prod.fst).sum ∧
    (entries.foldl joinEntry start).2 = (entries.map Prod.snd).foldl mergeSorted start.2 ∧
    (entries.foldl joinEntry start).2.size = start.2.size +
      ((entries.map Prod.snd).map Array.size).sum := by
  induction entries generalizing start with
  | nil => simp
  | cons e entries ih =>
    obtain ⟨delta, set, size⟩ := ih (joinEntry start e)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, joinEntry, Exact.mergeSorted_size] at *
    exact ⟨by omega, set, by omega⟩

theorem knapChoose_property (P : Entry → Prop) (kCS : Nat) (dp : CTable)
    (init : _root_.Int × Array Nat × Bool) (initial : P (init.1, init.2.1))
    (rows : ∀ (k : Nat) (e : Entry), dp[k]! = some e → P e) :
    let out := knapChoose kCS dp init
    P (out.1, out.2.1) := by
  let step := fun (acc : _root_.Int × Array Nat × Bool) c =>
    match dp[c]! with
    | none => acc
    | some (d, s) =>
      if d + (tag0Size (kCS + c) : _root_.Int) <
          acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int) ||
        (d + (tag0Size (kCS + c) : _root_.Int) ==
          acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int) && setPrec s acc.2.1)
      then (d, s, true) else acc
  change P (((List.range dp.size).foldl step init).1, ((List.range dp.size).foldl step init).2.1)
  have preserves : ∀ acc c, P (acc.1, acc.2.1) → P ((step acc c).1, (step acc c).2.1) := by
    intro acc c hacc
    dsimp only [step]
    cases hrow : dp[c]! with
    | none => exact hacc
    | some e =>
      obtain ⟨d, s⟩ := e
      simp only
      split
      · exact rows c (d, s) hrow
      · exact hacc
  generalize List.range dp.size = indices
  induction indices generalizing init with
  | nil => exact initial
  | cons c indices ih => exact ih (step init c) (preserves init c initial)

theorem knapChoose_entry_origin (kCS : Nat) (dp : CTable) (init : _root_.Int × Array Nat × Bool) :
    let out := knapChoose kCS dp init
    (out.1, out.2.1) = (init.1, init.2.1) ∨ ∃ k : Nat, dp[k]! = some (out.1, out.2.1) :=
  knapChoose_property (fun e => e = (init.1, init.2.1) ∨ ∃ k : Nat, dp[k]! = some e)
    kCS dp init (Or.inl rfl) (fun k _ h => Or.inr ⟨k, h⟩)

theorem bestRows_fold (rs : List CompResult) (start : Entry) :
    (rs.map (fun r => (r.bestDelta, r.bestSet))).foldl joinEntry start =
      (rs.foldl (fun d r => d + r.bestDelta) start.1,
       rs.foldl (fun s r => mergeSorted s r.bestSet) start.2) := by
  induction rs generalizing start with
  | nil => rfl
  | cons r rs ih =>
    simpa only [List.map_cons, List.foldl_cons, joinEntry] using ih (joinEntry start (r.bestDelta, r.bestSet))

/-- The best-row path is sound only when both fields name the same actual
retained row; an independently chosen best delta and set are insufficient. -/
theorem bestRows_origin (results : Array CompResult)
    (coherent : ∀ r ∈ results.toList, ∃ k : Nat, r.bySize[k]! = some (r.bestDelta, r.bestSet)) :
    EntryOrigin (results.toList.map (·.bySize))
      (results.foldl (fun d r => d + r.bestDelta) 0,
       results.foldl (fun s r => mergeSorted s r.bestSet) #[]) := by
  refine ⟨results.toList.map (fun r => (r.bestDelta, r.bestSet)), ?_, ?_⟩
  · generalize results.toList = rs at coherent ⊢
    induction rs with
    | nil => exact List.Forall₂.nil
    | cons r rs ih =>
      exact List.Forall₂.cons (coherent r List.mem_cons_self)
        (ih (fun r hr => coherent r (List.mem_cons_of_mem _ hr)))
  · rw [bestRows_fold, ← Array.foldl_toList, ← Array.foldl_toList]

theorem bestSetOf_row {tb : CTable} (sorted : SortedT tb) {delta : _root_.Int} {set : Array Nat}
    (chosen : bestSetOf tb delta = some set) : ∃ k : Nat, tb[k]! = some (delta, set) := by
  obtain ⟨e, member, hd, hs⟩ := (bestSetOf_spec sorted chosen).1
  obtain ⟨k, row⟩ := mem_toList_getElem! member
  exact ⟨k, by simpa only [← hd, ← hs] using row⟩

/-- Successful execution returns the ordered sum-and-merge of one actual
row per component, regardless of which count bracket wins. -/
theorem uniformKnapsack_entry_origin {limits : Limits} {kCS : Nat} {results : Array CompResult}
    {delta : _root_.Int} {set : Array Nat} {lowerBracket : Bool}
    (run : uniformKnapsack limits kCS results = .ok (delta, set, lowerBracket))
    (coherent : ∀ r ∈ results.toList, ∃ k : Nat, r.bySize[k]! = some (r.bestDelta, r.bestSet)) :
    EntryOrigin (results.toList.map (·.bySize)) (delta, set) := by
  have base := bestRows_origin results coherent
  unfold uniformKnapsack at run
  simp only at run
  generalize hbx : results.foldl (fun acc r => mergeSorted acc r.bestSet) #[] = bestX at run base
  generalize hbd : results.foldl (fun acc r => acc + r.bestDelta) (0 : _root_.Int) = bestDelta at run base
  split at run
  · split at run
    · cases run
    · simp only [pure, Except.pure, Except.ok.injEq] at run
      generalize hcap : tag0BracketStart (kCS + bestX.size) - 1 - kCS = cap at run
      have hdp : results.foldl (fun dp r => knapStep cap dp r.bySize)
          (#[some (0, #[])] ++ Array.replicate cap none) =
          (results.toList.map (·.bySize)).foldl (knapStep cap)
            (#[some (0, #[])] ++ Array.replicate cap none) := by
        rw [← Array.foldl_toList, List.foldl_map]
      rw [hdp] at run
      have origin := knapChoose_property (EntryOrigin (results.toList.map (·.bySize))) kCS _
        (bestDelta, bestX, false) base (fun _ _ row => knapFold_origin cap _ row)
      rw [run] at origin
      exact origin
  · simp only [pure, Except.pure, Except.ok.injEq] at run
    cases run
    exact base

def FamilyTables (cfg : Config) (factors : List Factor) (tables : List CTable) : Prop :=
  List.Forall₂ (fun f tb => Entries tb (fun e =>
    e.2 ∈ family cfg f.cost f.members ∧ e.1 = f.cost e.2)) factors tables

theorem RowsIn.family {cfg : Config} {factors : List Factor} {tables : List CTable} {entries : List Entry}
    (sound : FamilyTables cfg factors tables) (rows : RowsIn tables entries) :
    ProductMember cfg factors (entries.map Prod.snd) ∧
      deltaSum factors (entries.map Prod.snd) = (entries.map Prod.fst).sum := by
  induction sound generalizing entries with
  | nil => cases rows; exact ⟨List.Forall₂.nil, rfl⟩
  | @cons f tb factors tables head tail ih =>
    cases rows with
    | cons entry rest =>
      obtain ⟨k, row⟩ := entry
      obtain ⟨inside, cost⟩ := (head k _ row).2
      obtain ⟨member, delta⟩ := ih rest
      exact ⟨List.Forall₂.cons inside member, by
        simp only [List.map_cons, List.sum_cons, deltaSum, delta, cost]⟩

/-- The witness retains the exact ordered merged set, selected count and
signed objective. No minimality is inferred from entry soundness alone. -/
theorem EntryOrigin.family {cfg : Config} {factors : List Factor} {tables : List CTable} {value : Entry}
    (origin : EntryOrigin tables value) (sound : FamilyTables cfg factors tables) (baseCount : Nat) :
    ∃ sets, ProductMember cfg factors sets ∧ value.1 = deltaSum factors sets ∧
      value.2 = sets.foldl mergeSorted #[] ∧ value.2.size = selectedCount sets ∧
      value.1 + (tag0Size (baseCount + value.2.size) : _root_.Int) =
        productObjective baseCount factors sets := by
  obtain ⟨entries, rows, rfl⟩ := origin
  obtain ⟨member, delta⟩ := RowsIn.family sound rows
  obtain ⟨hd, hs, hn⟩ := joinEntry_fold entries (0, #[])
  simp only [Int.zero_add, Array.size_empty, Nat.zero_add] at hd hs hn
  refine ⟨entries.map Prod.snd, member, hd.trans delta.symm, hs, hn, ?_⟩
  simp only [productObjective, selectedCount, hd, hn, delta]

theorem trimmed_family_tables (cfg : Config) (factors : List Factor) (slack : Nat) :
    FamilyTables cfg factors (factors.map (fun f => CTable.trim (table cfg f.cost f.members) slack)) := by
  induction factors with
  | nil => exact List.Forall₂.nil
  | cons f fs ih =>
    exact List.Forall₂.cons (trim_entries (table_meaning cfg f.cost f.members).sound slack) ih

/-- The exported successful-run bridge: actual table provenance yields a
member of the declared family product with exactly the reported objective. -/
theorem uniformKnapsack_family {cfg : Config} {factors : List Factor} {limits : Limits}
    {kCS : Nat} {results : Array CompResult} {delta : _root_.Int} {set : Array Nat} {lowerBracket : Bool}
    (run : uniformKnapsack limits kCS results = .ok (delta, set, lowerBracket))
    (coherent : ∀ r ∈ results.toList, ∃ k : Nat, r.bySize[k]! = some (r.bestDelta, r.bestSet))
    (sound : FamilyTables cfg factors (results.toList.map (·.bySize))) :
    ∃ sets, ProductMember cfg factors sets ∧ delta = deltaSum factors sets ∧
      set = sets.foldl mergeSorted #[] ∧ set.size = selectedCount sets ∧
      delta + (tag0Size (kCS + set.size) : _root_.Int) = productObjective kCS factors sets :=
  EntryOrigin.family (uniformKnapsack_entry_origin run coherent) sound kCS

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.knapStep_entry_origin [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.knapFold_entry_origin [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.knapFold_origin [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.knapChoose_entry_origin [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.bestSetOf_row [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.uniformKnapsack_entry_origin [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.EntryOrigin.family [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.trimmed_family_tables [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.uniformKnapsack_family [propext, Quot.sound]
