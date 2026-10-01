import Ix.Compile.Verify.UniformRevisible

/-!
# Stage 4: the search tables

Count-indexed tables of `(Δ, set)` entries: what `add`, `best`, `trim`,
`conv` and folds of `add` keep and produce.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (setBang_getElem!)

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
  · simp [getElem!_def, hk] at h

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
      simp [getElem!_def, hj]
      rfl
    · simp [getElem!_def, hj, hj']

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
    · simp [getElem!_def, hk]
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
    simp [getElem!_def] at he

end Ix.Compile.Verify.UniformModel
