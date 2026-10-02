import Ix.Sharing.Verify.UniformTies

/-!
# Stage 4: the search tables

Count-indexed tables of `(Δ, set)` entries: what `add`, `best`, `trim`,
`conv` and folds of `add` keep and produce.
-/

namespace Ix.Sharing.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Sharing.Verify.SharingExact (setBang_getElem!)

/-- A table entry. -/
abbrev Entry := _root_.Int × Array Nat

/-- `tb` has an entry at count `k` of value at most `v`. -/
def HasAt (tb : CTable) (k : Nat) (v : _root_.Int) : Prop := ∃ e, tb[k]! = some e ∧ e.1 ≤ v

/-- Every entry of `tb` lies at its count and satisfies `P`. -/
def Entries (tb : CTable) (P : Entry → Prop) : Prop :=
  ∀ k e, tb[k]! = some e → e.2.size = k ∧ P e

/-- `tb'` has an entry at least as good at every count where `tb` has one. -/
def Improves (tb tb' : CTable) : Prop := ∀ k e, tb[k]! = some e → HasAt tb' k e.1

theorem improves_refl (tb : CTable) : Improves tb tb := fun _ e h => ⟨e, h, Int.le_refl _⟩

theorem improves_trans {a b c : CTable} (h1 : Improves a b) (h2 : Improves b c) : Improves a c := by
  intro k e he
  obtain ⟨e', he', hle⟩ := h1 k e he
  obtain ⟨e'', he'', hle'⟩ := h2 k e' he'
  exact ⟨e'', he'', Int.le_trans hle' hle⟩

theorem HasAt.mono {a b : CTable} {k : Nat} {v : _root_.Int} (h : HasAt a k v)
    (hi : Improves a b) : HasAt b k v := by
  obtain ⟨e, he, hle⟩ := h
  obtain ⟨e', he', hle'⟩ := hi k e he
  exact ⟨e', he', Int.le_trans hle' hle⟩

theorem HasAt.weaken {a : CTable} {k : Nat} {v v' : _root_.Int} (h : HasAt a k v) (hv : v ≤ v') :
    HasAt a k v' := by
  obtain ⟨e, he, hle⟩ := h
  exact ⟨e, he, Int.le_trans hle hv⟩

theorem getElem!_mem_toList {tb : CTable} {k : Nat} {e : Entry} (h : tb[k]! = some e) :
    some e ∈ tb.toList := by
  by_cases hk : k < tb.size
  · rw [getElem!_pos tb k hk] at h
    rw [← h]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem hk)
  · simp [hk] at h

theorem mem_toList_getElem! {tb : CTable} {e : Entry} (h : some e ∈ tb.toList) :
    ∃ k : Nat, tb[k]! = some e := by
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp h
  simp only [Array.length_toList] at hk
  refine ⟨k, ?_⟩
  rw [getElem!_pos tb k hk]
  simpa using he

theorem Entries.mem {tb : CTable} {P : Entry → Prop} (h : Entries tb P) {e : Entry}
    (he : some e ∈ tb.toList) : P e := by
  obtain ⟨k, hk⟩ := mem_toList_getElem! he
  exact (h k e hk).2

theorem Entries.imp {tb : CTable} {P Q : Entry → Prop} (h : Entries tb P) (hPQ : ∀ e, P e → Q e) :
    Entries tb Q := fun k e he => ⟨(h k e he).1, hPQ e (h k e he).2⟩

/-! ## Adding an entry -/

theorem ext_getElem! (tb : CTable) (m j : Nat) :
    (tb ++ Array.replicate m none)[j]! = tb[j]! := by
  by_cases hj : j < tb.size
  · rw [getElem!_pos _ j (by simp; omega), getElem!_pos tb j hj, Array.getElem_append_left hj]
  · by_cases hj' : j < tb.size + m
    · rw [getElem!_pos _ j (by simp; omega), Array.getElem_append_right (by omega)]
      simp [hj]
      rfl
    · simp [hj, hj']

theorem add_getElem! (tb : CTable) (e : Entry) (j : Nat) :
    (tb.add e)[j]! = if j = e.2.size ∧ betterEntry e tb[e.2.size]! = true then some e else tb[j]! := by
  unfold CTable.add
  simp only
  generalize hext : (if tb.size ≤ e.2.size then tb ++ Array.replicate (e.2.size + 1 - tb.size) none
    else tb) = tb1
  have hget : ∀ j : Nat, tb1[j]! = tb[j]! := by
    intro j; rw [← hext]; split
    · exact ext_getElem! _ _ _
    · rfl
  have hsz : e.2.size < tb1.size := by
    rw [← hext]; split
    · simp; omega
    · omega
  rw [hget]
  by_cases hb : betterEntry e tb[e.2.size]! = true
  · rw [if_pos hb, setBang_getElem!]
    by_cases hj : j = e.2.size
    · subst hj; simp [hsz, hb]
    · rw [if_neg (fun h => hj h.1.symm), if_neg (fun h => hj h.1), hget]
  · rw [if_neg hb, if_neg (fun h => hb h.2), hget]

theorem add_hasAt (tb : CTable) (e : Entry) : HasAt (tb.add e) e.2.size e.1 := by
  by_cases hb : betterEntry e tb[e.2.size]! = true
  · exact ⟨e, by rw [add_getElem!, if_pos ⟨rfl, hb⟩], Int.le_refl _⟩
  · have hget : (tb.add e)[e.2.size]! = tb[e.2.size]! := by
      rw [add_getElem!, if_neg (fun h => hb h.2)]
    rw [Bool.not_eq_true] at hb
    cases ho : tb[e.2.size]! with
    | none => rw [ho] at hb; simp [betterEntry] at hb
    | some x =>
      rw [ho] at hb
      simp only [betterEntry, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_imp,
        beq_iff_eq] at hb
      refine ⟨x, by rw [hget, ho], ?_⟩
      omega

theorem add_improves (tb : CTable) (e : Entry) : Improves tb (tb.add e) := by
  intro j x hx
  by_cases hj : j = e.2.size ∧ betterEntry e tb[e.2.size]! = true
  · obtain ⟨rfl, hb⟩ := hj
    refine ⟨e, by rw [add_getElem!, if_pos ⟨rfl, hb⟩], ?_⟩
    rw [hx] at hb
    simp only [betterEntry, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hb
    omega
  · exact ⟨x, by rw [add_getElem!, if_neg hj, hx], Int.le_refl _⟩

theorem add_entries {tb : CTable} {P : Entry → Prop} (h : Entries tb P) {e : Entry} (he : P e) :
    Entries (tb.add e) P := by
  intro j x hx
  rw [add_getElem!] at hx
  split at hx
  · rename_i hj; cases hx; exact ⟨hj.1.symm, he⟩
  · exact h j x hx

/-! ## Folds of improving steps -/

theorem foldl_improves {α : Type} (f : CTable → α → CTable) (hf : ∀ acc x, Improves acc (f acc x)) :
    ∀ (l : List α) (acc : CTable), Improves acc (l.foldl f acc)
  | [], acc => improves_refl acc
  | x :: xs, acc => improves_trans (hf acc x) (foldl_improves f hf xs (f acc x))

theorem foldl_hasAt {α : Type} (f : CTable → α → CTable) (hf : ∀ acc x, Improves acc (f acc x))
    {l : List α} {x : α} (hx : x ∈ l) {k : Nat} {v : _root_.Int}
    (hstep : ∀ acc, HasAt (f acc x) k v) (acc : CTable) : HasAt (l.foldl f acc) k v := by
  induction l generalizing acc with
  | nil => exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (hstep acc).mono (foldl_improves f hf ys _)
    · exact ih hx _

theorem foldl_entries {α : Type} (f : CTable → α → CTable) {P : Entry → Prop} {Q : α → Prop}
    (hf : ∀ acc x, Q x → Entries acc P → Entries (f acc x) P) :
    ∀ (l : List α) (acc : CTable), (∀ x ∈ l, Q x) → Entries acc P → Entries (l.foldl f acc) P
  | [], _, _, h => h
  | x :: xs, acc, hq, h => foldl_entries f hf xs _ (fun y hy => hq y (List.mem_cons_of_mem _ hy))
      (hf acc x (hq x List.mem_cons_self) h)

/-- Adding the entries of `comb` to `tb`. -/
def addAll (tb comb : CTable) : CTable :=
  comb.foldl (fun acc o => match o with
    | some e => acc.add e
    | none => acc) tb

theorem addAll_step_improves (acc : CTable) (o : Option Entry) :
    Improves acc (match o with
      | some e => acc.add e
      | none => acc) := by
  cases o with
  | none => exact improves_refl acc
  | some e => exact add_improves acc e

theorem addAll_improves (tb comb : CTable) : Improves tb (addAll tb comb) := by
  unfold addAll
  rw [← Array.foldl_toList]
  exact foldl_improves _ addAll_step_improves _ _

theorem addAll_hasAt (tb comb : CTable) {e : Entry} (he : some e ∈ comb.toList) :
    HasAt (addAll tb comb) e.2.size e.1 := by
  unfold addAll
  rw [← Array.foldl_toList]
  exact foldl_hasAt _ addAll_step_improves he (fun acc => add_hasAt acc e) tb

theorem addAll_entries {tb comb : CTable} {P : Entry → Prop} (h1 : Entries tb P)
    (h2 : ∀ e, some e ∈ comb.toList → P e) : Entries (addAll tb comb) P := by
  unfold addAll
  rw [← Array.foldl_toList]
  refine foldl_entries _ (Q := fun o => ∀ e, o = some e → P e) ?_ comb.toList tb ?_ h1
  · intro acc o hq hacc
    cases o with
    | none => exact hacc
    | some e => exact add_entries hacc (hq e rfl)
  · intro o ho e he
    subst he
    exact h2 _ ho

/-! ## The best entry -/

/-- The step of `CTable.best`. -/
def bestStep (acc : Option _root_.Int) (o : Option Entry) : Option _root_.Int :=
  match o, acc with
  | none, _ => acc
  | some (d, _), none => some d
  | some (d, _), some b => some (min d b)

theorem best_eq (tb : CTable) : tb.best = tb.toList.foldl bestStep none := by
  unfold CTable.best
  rw [← Array.foldl_toList]
  rfl

theorem bestFold_spec : ∀ (L : List (Option Entry)) (acc : Option _root_.Int),
    (∀ e, some e ∈ L → ∃ b, L.foldl bestStep acc = some b ∧ b ≤ e.1) ∧
    (∀ a, acc = some a → ∃ b, L.foldl bestStep acc = some b ∧ b ≤ a) ∧
    (∀ b, L.foldl bestStep acc = some b → acc = some b ∨ ∃ e, some e ∈ L ∧ e.1 = b)
  | [], acc => ⟨fun _ h => absurd h List.not_mem_nil, fun a h => ⟨a, h, Int.le_refl _⟩,
      fun b h => Or.inl h⟩
  | o :: L, acc => by
    obtain ⟨h1, h2, h3⟩ := bestFold_spec L (bestStep acc o)
    rw [List.foldl_cons]
    refine ⟨fun e he => ?_, fun a ha => ?_, fun b hb => ?_⟩
    · rcases List.mem_cons.mp he with rfl | he
      · have : ∃ c, bestStep acc (some e) = some c ∧ c ≤ e.1 := by
          obtain ⟨d, s⟩ := e
          cases acc with
          | none => exact ⟨d, rfl, Int.le_refl _⟩
          | some b => exact ⟨min d b, rfl, Int.min_le_left _ _⟩
        obtain ⟨c, hc, hce⟩ := this
        obtain ⟨b, hb, hbc⟩ := h2 c hc
        exact ⟨b, hb, Int.le_trans hbc hce⟩
      · exact h1 e he
    · have : ∃ c, bestStep acc o = some c ∧ c ≤ a := by
        subst ha
        cases o with
        | none => exact ⟨a, rfl, Int.le_refl _⟩
        | some e => obtain ⟨d, s⟩ := e; exact ⟨min d a, rfl, Int.min_le_right _ _⟩
      obtain ⟨c, hc, hca⟩ := this
      obtain ⟨b, hb, hbc⟩ := h2 c hc
      exact ⟨b, hb, Int.le_trans hbc hca⟩
    · rcases h3 b hb with h | ⟨e, he, heb⟩
      · cases o with
        | none => exact Or.inl h
        | some e =>
          obtain ⟨d, s⟩ := e
          cases acc with
          | none =>
            simp only [bestStep, Option.some.injEq] at h
            exact Or.inr ⟨(d, s), List.mem_cons_self, h⟩
          | some a =>
            simp only [bestStep, Option.some.injEq] at h
            rcases Int.le_total d a with hda | hda
            · rw [Int.min_eq_left hda] at h
              exact Or.inr ⟨(d, s), List.mem_cons_self, h⟩
            · rw [Int.min_eq_right hda] at h
              exact Or.inl (by rw [h])
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, heb⟩

theorem best_le {tb : CTable} {b : _root_.Int} (hb : tb.best = some b) {k : Nat} {e : Entry}
    (he : tb[k]! = some e) : b ≤ e.1 := by
  rw [best_eq] at hb
  obtain ⟨b', hb', hle⟩ := (bestFold_spec tb.toList none).1 e (getElem!_mem_toList he)
  rw [hb] at hb'
  cases hb'
  exact hle

theorem best_attained {tb : CTable} {b : _root_.Int} (hb : tb.best = some b) :
    ∃ (k : Nat) (e : Entry), tb[k]! = some e ∧ e.1 = b := by
  rw [best_eq] at hb
  rcases (bestFold_spec tb.toList none).2.2 b hb with h | ⟨e, he, heb⟩
  · cases h
  · obtain ⟨k, hk⟩ := mem_toList_getElem! he
    exact ⟨k, e, hk, heb⟩

theorem best_isSome {tb : CTable} {k : Nat} {e : Entry} (he : tb[k]! = some e) :
    ∃ b, tb.best = some b := by
  rw [best_eq]
  obtain ⟨b, hb, _⟩ := (bestFold_spec tb.toList none).1 e (getElem!_mem_toList he)
  exact ⟨b, hb⟩

/-! ## Trimming -/

theorem trim_getElem! (tb : CTable) (s : Nat) (k : Nat) :
    (tb.trim s)[k]! = match tb.best with
      | none => tb[k]!
      | some b => match (tb[k]! : Option Entry) with
        | some (e : Entry) => if e.1 > b + (s : _root_.Int) then none else some e
        | none => none := by
  unfold CTable.trim
  cases hb : tb.best with
  | none => rfl
  | some b =>
    simp only
    by_cases hk : k < tb.size
    · rw [getElem!_pos _ k (by simp; exact hk), getElem!_pos tb k hk, Array.getElem_map]
      cases tb[k] with
      | none => rfl
      | some e => obtain ⟨d, s'⟩ := e; rfl
    · simp [hk]
      rfl

theorem trim_entries {tb : CTable} {P : Entry → Prop} (h : Entries tb P) (s : Nat) :
    Entries (tb.trim s) P := by
  intro k e he
  rw [trim_getElem!] at he
  cases hb : tb.best with
  | none => rw [hb] at he; exact h k e he
  | some b =>
    rw [hb] at he
    simp only at he
    cases hk : tb[k]! with
    | none => rw [hk] at he; cases he
    | some x =>
      rw [hk] at he
      simp only at he
      split at he
      · cases he
      · exact (Option.some.inj he) ▸ h k x hk

theorem trim_hasAt {tb : CTable} {s k : Nat} {v : _root_.Int} (h : HasAt tb k v)
    (hv : ∀ b, tb.best = some b → v ≤ b + (s : _root_.Int)) : HasAt (tb.trim s) k v := by
  obtain ⟨e, he, hle⟩ := h
  refine ⟨e, ?_, hle⟩
  rw [trim_getElem!]
  cases hb : tb.best with
  | none => exact he
  | some b =>
    simp only
    rw [he]
    simp only
    have := hv b hb
    rw [if_neg (by omega)]

/-! ## Convolution -/

theorem mergeSorted_size (a b : Array Nat) : (mergeSorted a b).size = a.size + b.size := by
  rw [← Array.length_toList, (mergeSorted_perm a b).length_eq]
  simp

/-- The inner step of `CTable.conv`. -/
def convIn (da : _root_.Int) (sa : Array Nat) (out : CTable) (ob : Option Entry) : CTable :=
  match ob with
  | none => out
  | some (db, sb) => out.add (da + db, mergeSorted sa sb)

/-- The outer step of `CTable.conv`. -/
def convOut (b : CTable) (out : CTable) (oa : Option Entry) : CTable :=
  match oa with
  | none => out
  | some (da, sa) => b.toList.foldl (convIn da sa) out

theorem conv_eq (a b : CTable) : a.conv b = a.toList.foldl (convOut b) #[] := by
  unfold CTable.conv
  rw [← Array.foldl_toList]
  congr 1
  funext out oa
  cases oa with
  | none => rfl
  | some e =>
    obtain ⟨da, sa⟩ := e
    simp only [convOut]
    rw [← Array.foldl_toList]
    rfl

theorem convIn_improves (da : _root_.Int) (sa : Array Nat) (out : CTable) (ob : Option Entry) :
    Improves out (convIn da sa out ob) := by
  cases ob with
  | none => exact improves_refl out
  | some e => obtain ⟨db, sb⟩ := e; exact add_improves out _

theorem convOut_improves (b : CTable) (out : CTable) (oa : Option Entry) :
    Improves out (convOut b out oa) := by
  cases oa with
  | none => exact improves_refl out
  | some e =>
    obtain ⟨da, sa⟩ := e
    exact foldl_improves _ (convIn_improves da sa) _ _

/-- **Convolution covers every pair of entries.** -/
theorem conv_hasAt {a b : CTable} {ea eb : Entry} (ha : some ea ∈ a.toList)
    (hb : some eb ∈ b.toList) :
    HasAt (a.conv b) (ea.2.size + eb.2.size) (ea.1 + eb.1) := by
  rw [conv_eq]
  apply foldl_hasAt _ (convOut_improves b) ha _ #[]
  intro acc
  obtain ⟨da, sa⟩ := ea
  simp only [convOut]
  apply foldl_hasAt _ (convIn_improves da sa) hb _ acc
  intro acc'
  obtain ⟨db, sb⟩ := eb
  simp only [convIn]
  have := add_hasAt acc' (da + db, mergeSorted sa sb)
  simp only [mergeSorted_size] at this
  exact this

/-- **Convolution entries are sums of pairs of entries.** -/
theorem conv_entries {a b : CTable} {Pa Pb : Entry → Prop} (ha : ∀ e, some e ∈ a.toList → Pa e)
    (hb : ∀ e, some e ∈ b.toList → Pb e) :
    Entries (a.conv b) (fun e => ∃ ea eb, Pa ea ∧ Pb eb ∧
      e = (ea.1 + eb.1, mergeSorted ea.2 eb.2)) := by
  rw [conv_eq]
  refine foldl_entries _ (Q := fun o => ∀ e, o = some e → Pa e) ?_ a.toList #[] ?_ ?_
  · intro acc oa hq hacc
    cases oa with
    | none => exact hacc
    | some ea =>
      obtain ⟨da, sa⟩ := ea
      have hPa := hq (da, sa) rfl
      simp only [convOut]
      refine foldl_entries _ (Q := fun o => ∀ e, o = some e → Pb e) ?_ b.toList acc ?_ hacc
      · intro acc' ob hq' hacc'
        cases ob with
        | none => exact hacc'
        | some eb =>
          obtain ⟨db, sb⟩ := eb
          exact add_entries hacc' ⟨(da, sa), (db, sb), hPa, hq' (db, sb) rfl, rfl⟩
      · intro ob hob e he
        subst he
        exact hb _ hob
  · intro oa hoa e he
    subst he
    exact ha _ hoa
  · intro k e he
    simp at he

/-! ## Tables with the tie order -/

/-- `e` is at least as good as `e'`: a smaller `Δ`, or the same and an earlier
or equal set. -/
def TLe (e e' : Entry) : Prop := e.1 < e'.1 ∨ (e.1 = e'.1 ∧ LeL e.2.toList e'.2.toList)

/-- `tb` has an entry at count `k` at least as good as `(v, S)`. -/
def HasAtT (tb : CTable) (k : Nat) (v : _root_.Int) (S : List Nat) : Prop :=
  ∃ e, tb[k]! = some e ∧ (e.1 < v ∨ (e.1 = v ∧ LeL e.2.toList S))

/-- `tb'` has an entry at least as good at every count where `tb` has one. -/
def ImprovesT (tb tb' : CTable) : Prop :=
  ∀ (k : Nat) (e : Entry), tb[k]! = some e → ∃ e', tb'[k]! = some e' ∧ TLe e' e

/-- Every entry's set is strictly increasing. -/
def SortedT (tb : CTable) : Prop := ∀ (k : Nat) (e : Entry), tb[k]! = some e → e.2.toList.Pairwise (· < ·)

theorem tle_refl (e : Entry) : TLe e e := Or.inr ⟨rfl, leL_refl _⟩

theorem tle_trans {a b c : Entry} (h1 : TLe a b) (h2 : TLe b c) : TLe a c := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (Int.lt_trans h1 h2)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, leL_trans h1' h2'⟩

theorem improvesT_refl (tb : CTable) : ImprovesT tb tb := fun _ e h => ⟨e, h, tle_refl e⟩

theorem improvesT_trans {a b c : CTable} (h1 : ImprovesT a b) (h2 : ImprovesT b c) :
    ImprovesT a c := by
  intro k e he
  obtain ⟨e', he', h⟩ := h1 k e he
  obtain ⟨e'', he'', h'⟩ := h2 k e' he'
  exact ⟨e'', he'', tle_trans h' h⟩

theorem HasAtT.mono {a b : CTable} {k : Nat} {v : _root_.Int} {S : List Nat} (h : HasAtT a k v S)
    (hi : ImprovesT a b) : HasAtT b k v S := by
  obtain ⟨e, he, hv⟩ := h
  obtain ⟨e', he', hle⟩ := hi k e he
  refine ⟨e', he', ?_⟩
  rcases hle with hle | ⟨hle, hle'⟩ <;> rcases hv with hv | ⟨hv, hv'⟩
  · exact Or.inl (Int.lt_trans hle hv)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, leL_trans hle' hv'⟩

theorem HasAtT.congr {tb : CTable} {k : Nat} {v : _root_.Int} {S S' : List Nat} (h : HasAtT tb k v S)
    (hS : ∀ u, u ∈ S ↔ u ∈ S') : HasAtT tb k v S' := by
  obtain ⟨e, he, hv⟩ := h
  refine ⟨e, he, ?_⟩
  rcases hv with hv | ⟨hv, hv'⟩
  · exact Or.inl hv
  · exact Or.inr ⟨hv, leL_congr (fun _ => Iff.rfl) hS hv'⟩

theorem HasAtT.weakenT {tb : CTable} {k : Nat} {v v' : _root_.Int} {S S' : List Nat}
    (h : HasAtT tb k v S) (hv : v < v' ∨ (v = v' ∧ LeL S S')) : HasAtT tb k v' S' := by
  obtain ⟨e, he, hgood⟩ := h
  refine ⟨e, he, ?_⟩
  rcases hgood with h1 | ⟨h1, h1'⟩ <;> rcases hv with h2 | ⟨h2, h2'⟩
  · exact Or.inl (Int.lt_trans h1 h2)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, leL_trans h1' h2'⟩

theorem HasAtT.toHasAt {tb : CTable} {k : Nat} {v : _root_.Int} {S : List Nat} (h : HasAtT tb k v S) :
    HasAt tb k v := by
  obtain ⟨e, he, hv⟩ := h
  exact ⟨e, he, by rcases hv with hv | ⟨hv, _⟩ <;> omega⟩

theorem HasAtT.of_tle {tb : CTable} {k : Nat} {e : Entry} (he : tb[k]! = some e) {v : _root_.Int}
    {S : List Nat} (hv : e.1 < v ∨ (e.1 = v ∧ LeL e.2.toList S)) : HasAtT tb k v S :=
  ⟨e, he, hv⟩

/-- An entry at least as good as `(v, S)` stays so under a no-worse entry. -/
theorem tle_good {e' e : Entry} {v : _root_.Int} {S : List Nat} (h : TLe e' e)
    (hv : e.1 < v ∨ (e.1 = v ∧ LeL e.2.toList S)) : e'.1 < v ∨ (e'.1 = v ∧ LeL e'.2.toList S) := by
  rcases h with h | ⟨h, h'⟩ <;> rcases hv with hv | ⟨hv, hv'⟩
  · exact Or.inl (Int.lt_trans h hv)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, leL_trans h' hv'⟩

/-- `betterEntry` decides the tie order on sorted sets. -/
theorem better_tle {e : Entry} {o : Entry} (he : e.2.toList.Pairwise (· < ·))
    (ho : o.2.toList.Pairwise (· < ·)) :
    (betterEntry e (some o) = true → TLe e o) ∧ (betterEntry e (some o) = false → TLe o e) := by
  obtain ⟨d, s⟩ := e
  obtain ⟨d0, s0⟩ := o
  simp only [betterEntry]
  constructor
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inr ((setPrec_iff he ho).mp h')⟩
  · intro h
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_imp, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    by_cases hd : d = d0
    · have hns := h2 hd
      refine Or.inr ⟨hd.symm, ?_⟩
      rcases leL_total ho he with h | h
      · exact h
      · exact absurd ((setPrec_iff he ho).mpr h) (by simp [hns])
    · exact Or.inl (by simp only at h1 hd ⊢; omega)

theorem add_improvesT {tb : CTable} {e : Entry} (hs : SortedT tb) (he : e.2.toList.Pairwise (· < ·)) :
    ImprovesT tb (tb.add e) := by
  intro j x hx
  by_cases hj : j = e.2.size ∧ betterEntry e tb[e.2.size]! = true
  · obtain ⟨rfl, hb⟩ := hj
    refine ⟨e, by rw [add_getElem!, if_pos ⟨rfl, hb⟩], ?_⟩
    rw [hx] at hb
    exact (better_tle he (hs _ x hx)).1 hb
  · exact ⟨x, by rw [add_getElem!, if_neg hj, hx], tle_refl x⟩

theorem add_hasAtT {tb : CTable} {e : Entry} (hs : SortedT tb) (he : e.2.toList.Pairwise (· < ·)) :
    HasAtT (tb.add e) e.2.size e.1 e.2.toList := by
  by_cases hb : betterEntry e tb[e.2.size]! = true
  · exact ⟨e, by rw [add_getElem!, if_pos ⟨rfl, hb⟩], Or.inr ⟨rfl, leL_refl _⟩⟩
  · have hget : (tb.add e)[e.2.size]! = tb[e.2.size]! := by
      rw [add_getElem!, if_neg (fun h => hb h.2)]
    cases ho : tb[e.2.size]! with
    | none => rw [ho] at hb; simp [betterEntry] at hb
    | some x =>
      rw [ho] at hb
      have := (better_tle he (hs _ x ho)).2 (by simpa using hb)
      exact ⟨x, by rw [hget, ho], tle_good this (Or.inr ⟨rfl, leL_refl _⟩)⟩

theorem add_sortedT {tb : CTable} {e : Entry} (hs : SortedT tb) (he : e.2.toList.Pairwise (· < ·)) :
    SortedT (tb.add e) := by
  intro j x hx
  rw [add_getElem!] at hx
  split at hx
  · cases hx; exact he
  · exact hs j x hx

theorem foldl_improvesT_inv {α : Type} (f : CTable → α → CTable) (Inv : CTable → Prop)
    (hinv : ∀ acc x, Inv acc → Inv (f acc x)) (hf : ∀ acc x, Inv acc → ImprovesT acc (f acc x)) :
    ∀ (l : List α) (acc : CTable), Inv acc → ImprovesT acc (l.foldl f acc)
  | [], acc, _ => improvesT_refl acc
  | x :: xs, acc, h => improvesT_trans (hf acc x h)
      (foldl_improvesT_inv f Inv hinv hf xs (f acc x) (hinv acc x h))

theorem foldl_inv {α : Type} (f : CTable → α → CTable) (Inv : CTable → Prop)
    (hinv : ∀ acc x, Inv acc → Inv (f acc x)) :
    ∀ (l : List α) (acc : CTable), Inv acc → Inv (l.foldl f acc)
  | [], _, h => h
  | x :: xs, acc, h => foldl_inv f Inv hinv xs _ (hinv acc x h)

theorem foldl_hasAtT_inv {α : Type} (f : CTable → α → CTable) (Inv : CTable → Prop)
    (hinv : ∀ acc x, Inv acc → Inv (f acc x)) (hf : ∀ acc x, Inv acc → ImprovesT acc (f acc x))
    {l : List α} {x : α} (hx : x ∈ l) (k : Nat) (v : _root_.Int) (S : List Nat) (acc : CTable)
    (hacc : Inv acc) (hstep : ∀ acc, Inv acc → HasAtT (f acc x) k v S) :
    HasAtT (l.foldl f acc) k v S := by
  induction l generalizing acc with
  | nil => exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (hstep acc hacc).mono (foldl_improvesT_inv f Inv hinv hf ys _ (hinv acc _ hacc))
    · exact ih hx _ (hinv acc y hacc)

/-- The step of `addAll`. -/
def addStep (acc : CTable) (o : Option Entry) : CTable :=
  match o with
  | some e => acc.add e
  | none => acc

theorem addAll_eq (tb comb : CTable) : addAll tb comb = comb.toList.foldl addStep tb := by
  unfold addAll; rw [← Array.foldl_toList]; rfl

theorem addAll_tie {tb comb : CTable} (h1 : SortedT tb)
    (h2 : ∀ e, some e ∈ comb.toList → e.2.toList.Pairwise (· < ·)) :
    SortedT (addAll tb comb) ∧ ImprovesT tb (addAll tb comb) ∧
      ∀ e, some e ∈ comb.toList → HasAtT (addAll tb comb) e.2.size e.1 e.2.toList := by
  rw [addAll_eq]
  let Inv : CTable → Prop := SortedT
  have hinv : ∀ acc (o : Option Entry), o ∈ comb.toList → Inv acc → Inv (addStep acc o) := by
    intro acc o ho h
    cases o with
    | none => exact h
    | some e => exact add_sortedT h (h2 e ho)
  have key : ∀ (l : List (Option Entry)), (∀ o ∈ l, o ∈ comb.toList) → ∀ acc, Inv acc →
      Inv (l.foldl addStep acc) ∧ ImprovesT acc (l.foldl addStep acc) ∧
        ∀ e, some e ∈ l → HasAtT (l.foldl addStep acc) e.2.size e.1 e.2.toList := by
    intro l
    induction l with
    | nil => intro _ acc h; exact ⟨h, improvesT_refl _, fun e he => absurd he List.not_mem_nil⟩
    | cons o l ih =>
      intro hl acc h
      rw [List.foldl_cons]
      have hstep := hinv acc o (hl o List.mem_cons_self) h
      obtain ⟨r1, r2, r3⟩ := ih (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) _ hstep
      have himp : ImprovesT acc (addStep acc o) := by
        cases o with
        | none => exact improvesT_refl _
        | some e => exact add_improvesT h (h2 e (hl _ List.mem_cons_self))
      refine ⟨r1, improvesT_trans himp r2, fun e he => ?_⟩
      rcases List.mem_cons.mp he with he | he
      · subst he
        exact (add_hasAtT h (h2 e (hl _ List.mem_cons_self))).mono r2
      · exact r3 e he
  exact key comb.toList (fun o ho => ho) tb h1

theorem trim_tie {tb : CTable} (s : Nat) (hs : SortedT tb) :
    SortedT (tb.trim s) ∧ ∀ {k : Nat} {v : _root_.Int} {S : List Nat}, HasAtT tb k v S →
      (∀ b, tb.best = some b → v ≤ b + (s : _root_.Int)) → HasAtT (tb.trim s) k v S := by
  have hsub : ∀ (k : Nat) (e : Entry), (tb.trim s)[k]! = some e → tb[k]! = some e := by
    intro k e he
    rw [trim_getElem!] at he
    cases hb : tb.best with
    | none => rw [hb] at he; exact he
    | some b =>
      rw [hb] at he
      simp only at he
      cases hk : tb[k]! with
      | none => rw [hk] at he; cases he
      | some x =>
        rw [hk] at he
        simp only at he
        split at he
        · cases he
        · exact (Option.some.inj he) ▸ rfl
  refine ⟨fun k e he => hs k e (hsub k e he), fun {k v S} h hv => ?_⟩
  obtain ⟨e, he, hgood⟩ := h
  refine ⟨e, ?_, hgood⟩
  rw [trim_getElem!]
  cases hb : tb.best with
  | none => exact he
  | some b =>
    simp only
    rw [he]
    simp only
    have := hv b hb
    rw [if_neg (by rcases hgood with h | ⟨h, _⟩ <;> omega)]

theorem mergeSorted_strict {a b : Array Nat} (ha : a.toList.Pairwise (· < ·))
    (hb : b.toList.Pairwise (· < ·)) (hd : ∀ x ∈ a.toList, x ∉ b.toList) :
    (mergeSorted a b).toList.Pairwise (· < ·) := by
  have hn : (mergeSorted a b).toList.Nodup :=
    (mergeSorted_perm a b).nodup_iff.mpr (nodup_app (ha.imp Nat.ne_of_lt) (hb.imp Nat.ne_of_lt) hd)
  have hle := mergeSorted_sorted a b
  have : (mergeSorted a b).toList.Pairwise (fun x y => x ≤ y ∧ x ≠ y) :=
    List.Pairwise.and hle hn
  exact this.imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)

/-- **Convolution with the tie order.** -/
theorem conv_tie {a b : CTable} (ha : ∀ e, some e ∈ a.toList → e.2.toList.Pairwise (· < ·))
    (hb : ∀ e, some e ∈ b.toList → e.2.toList.Pairwise (· < ·))
    (hd : ∀ ea, some ea ∈ a.toList → ∀ eb, some eb ∈ b.toList → ∀ x ∈ ea.2.toList, x ∉ eb.2.toList) :
    SortedT (a.conv b) ∧ ∀ ea, some ea ∈ a.toList → ∀ eb, some eb ∈ b.toList →
      HasAtT (a.conv b) (ea.2.size + eb.2.size) (ea.1 + eb.1) (mergeSorted ea.2 eb.2).toList := by
  rw [conv_eq]
  -- the inner steps of one outer entry
  have hin : ∀ (da : _root_.Int) (sa : Array Nat), some (da, sa) ∈ a.toList → ∀ acc (ob : Option Entry),
      ob ∈ b.toList → SortedT acc → SortedT (convIn da sa acc ob) ∧ ImprovesT acc (convIn da sa acc ob) := by
    intro da sa hsa acc ob hob hacc
    cases ob with
    | none => exact ⟨hacc, improvesT_refl _⟩
    | some eb =>
      obtain ⟨db, sb⟩ := eb
      have hs := mergeSorted_strict (ha _ hsa) (hb _ hob) (hd _ hsa _ hob)
      exact ⟨add_sortedT hacc hs, add_improvesT hacc hs⟩
  have hinner : ∀ (da : _root_.Int) (sa : Array Nat), some (da, sa) ∈ a.toList →
      ∀ (l : List (Option Entry)), (∀ o ∈ l, o ∈ b.toList) → ∀ acc, SortedT acc →
        SortedT (l.foldl (convIn da sa) acc) ∧ ImprovesT acc (l.foldl (convIn da sa) acc) := by
    intro da sa hsa l
    induction l with
    | nil => intro _ acc h; exact ⟨h, improvesT_refl _⟩
    | cons o l ih =>
      intro hl acc h
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := hin da sa hsa acc o (hl o List.mem_cons_self) h
      obtain ⟨h3, h4⟩ := ih (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) _ h1
      exact ⟨h3, improvesT_trans h2 h4⟩
  have hout : ∀ acc (oa : Option Entry), oa ∈ a.toList → SortedT acc →
      SortedT (convOut b acc oa) ∧ ImprovesT acc (convOut b acc oa) := by
    intro acc oa hoa hacc
    cases oa with
    | none => exact ⟨hacc, improvesT_refl _⟩
    | some ea =>
      obtain ⟨da, sa⟩ := ea
      exact hinner da sa hoa b.toList (fun o ho => ho) acc hacc
  have houter : ∀ (l : List (Option Entry)), (∀ o ∈ l, o ∈ a.toList) → ∀ acc, SortedT acc →
      SortedT (l.foldl (convOut b) acc) ∧ ImprovesT acc (l.foldl (convOut b) acc) := by
    intro l
    induction l with
    | nil => intro _ acc h; exact ⟨h, improvesT_refl _⟩
    | cons o l ih =>
      intro hl acc h
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := hout acc o (hl o List.mem_cons_self) h
      obtain ⟨h3, h4⟩ := ih (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) _ h1
      exact ⟨h3, improvesT_trans h2 h4⟩
  have hsorted0 : SortedT (#[] : CTable) := fun k e he => by simp at he
  refine ⟨(houter a.toList (fun o ho => ho) #[] hsorted0).1, fun ea hea eb heb => ?_⟩
  -- the pair's entry, then improvement by the rest
  have key : ∀ (l : List (Option Entry)), (∀ o ∈ l, o ∈ a.toList) → some ea ∈ l → ∀ acc, SortedT acc →
      HasAtT (l.foldl (convOut b) acc) (ea.2.size + eb.2.size) (ea.1 + eb.1)
        (mergeSorted ea.2 eb.2).toList := by
    intro l
    induction l with
    | nil => intro _ h; exact absurd h List.not_mem_nil
    | cons o l ih =>
      intro hl hmem acc hacc
      rw [List.foldl_cons]
      obtain ⟨hs1, _⟩ := hout acc o (hl o List.mem_cons_self) hacc
      rcases List.mem_cons.mp hmem with rfl | hmem
      · have hrest := (houter l (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) _ hs1).2
        refine HasAtT.mono ?_ hrest
        obtain ⟨da, sa⟩ := ea
        simp only [convOut]
        -- inner: the pair's add, then the rest of the inner fold
        have kin : ∀ (l' : List (Option Entry)), (∀ o ∈ l', o ∈ b.toList) → some eb ∈ l' →
            ∀ acc', SortedT acc' → HasAtT (l'.foldl (convIn da sa) acc') ((da, sa).2.size + eb.2.size)
              ((da, sa).1 + eb.1) (mergeSorted (da, sa).2 eb.2).toList := by
          intro l'
          induction l' with
          | nil => intro _ h; exact absurd h List.not_mem_nil
          | cons o' l' ih' =>
            intro hl' hmem' acc' hacc'
            rw [List.foldl_cons]
            obtain ⟨hs2, _⟩ := hin da sa hea acc' o' (hl' o' List.mem_cons_self) hacc'
            rcases List.mem_cons.mp hmem' with rfl | hmem'
            · have hrest' := (hinner da sa hea l' (fun o ho => hl' o (List.mem_cons_of_mem _ ho)) _ hs2).2
              refine HasAtT.mono ?_ hrest'
              obtain ⟨db, sb⟩ := eb
              have hs := mergeSorted_strict (ha _ hea) (hb _ heb) (hd _ hea _ heb)
              have := add_hasAtT hacc' hs (e := (da + db, mergeSorted sa sb))
              simp only [mergeSorted_size] at this
              exact this
            · exact ih' (fun o ho => hl' o (List.mem_cons_of_mem _ ho)) hmem' _ hs2
        exact kin b.toList (fun o ho => ho) heb acc hacc
      · exact ih (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) hmem _ hs1
  exact key a.toList (fun o ho => ho) hea #[] hsorted0

end Ix.Sharing.Verify.UniformModel
