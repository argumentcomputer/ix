import Ix.Compile.Verify.UniformSearchSpec

/-!
# Stage 4: the count knapsack of the uniform optimizer

The knapsack over the component tables (`knapStep`) and the choice among
its counts (`knapChoose`): every choice of one entry per table within the
count cap is matched by a no-worse combination, and the chosen total is at
most every candidate's.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (setBang_getElem!)

/-- `foldl_hasAt` under an invariant of the accumulator. -/
theorem foldl_hasAt_inv {α : Type} (f : CTable → α → CTable) (Inv : CTable → Prop)
    (hinv : ∀ acc x, Inv acc → Inv (f acc x)) (hf : ∀ acc x, Improves acc (f acc x))
    {l : List α} {x : α} (hx : x ∈ l) (k : Nat) (v : _root_.Int) (acc : CTable) (hacc : Inv acc)
    (hstep : ∀ acc, Inv acc → HasAt (f acc x) k v) : HasAt (l.foldl f acc) k v := by
  induction l generalizing acc with
  | nil => exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (hstep acc hacc).mono (foldl_improves f hf ys _)
    · exact ih hx _ (hinv acc y hacc)

/-! ## One knapsack step -/

/-- The inner step of `knapStep` for one count `c` with entry `(d, s)`. -/
def knapIn (cap c : Nat) (d : _root_.Int) (s : Array Nat) (bySize : CTable) (ndp : CTable) (k : Nat) :
    CTable :=
  match bySize[k]! with
  | none => ndp
  | some (dk, sk) =>
    if c + k > cap then ndp
    else if betterEntry (d + dk, mergeSorted s sk) ndp[c + k]! then
      ndp.set! (c + k) (some (d + dk, mergeSorted s sk))
    else ndp

/-- The outer step of `knapStep` for count `c`. -/
def knapOut (cap : Nat) (dp : CTable) (bySize : CTable) (ndp : CTable) (c : Nat) : CTable :=
  match dp[c]! with
  | none => ndp
  | some (d, s) => (List.range bySize.size).foldl (knapIn cap c d s bySize) ndp

theorem knapStep_eq (cap : Nat) (dp bySize : CTable) :
    knapStep cap dp bySize =
      (List.range dp.size).foldl (knapOut cap dp bySize) (Array.replicate (cap + 1) none) := rfl

theorem knapIn_eq (cap c : Nat) (d : _root_.Int) (s : Array Nat) (bySize ndp : CTable) (k : Nat) :
    knapIn cap c d s bySize ndp k = match bySize[k]! with
      | none => ndp
      | some (dk, sk) =>
        if c + k > cap then ndp
        else if betterEntry (d + dk, mergeSorted s sk) ndp[c + k]! then
          ndp.set! (c + k) (some (d + dk, mergeSorted s sk))
        else ndp := rfl

theorem knapIn_size (cap c : Nat) (d : _root_.Int) (s : Array Nat) (bySize ndp : CTable) (k : Nat) :
    (knapIn cap c d s bySize ndp k).size = ndp.size := by
  rw [knapIn_eq]
  cases bySize[k]! with
  | none => rfl
  | some e =>
    obtain ⟨dk, sk⟩ := e
    simp only
    split
    · rfl
    · split
      · simp [Array.set!]
      · rfl

theorem setBang_improves {ndp : CTable} {j : Nat} {e : Entry} (hb : betterEntry e ndp[j]! = true) :
    Improves ndp (ndp.set! j (some e)) := by
  intro i x hx
  by_cases hij : j = i ∧ j < ndp.size
  · obtain ⟨rfl, hj⟩ := hij
    refine ⟨e, by rw [setBang_getElem!, ite_eq_left ⟨rfl, hj⟩], ?_⟩
    rw [hx] at hb
    simp only [betterEntry, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hb
    omega
  · exact ⟨x, by rw [setBang_getElem!, ite_eq_right hij, hx], Int.le_refl _⟩

theorem knapIn_improves (cap c : Nat) (d : _root_.Int) (s : Array Nat) (bySize ndp : CTable) (k : Nat) :
    Improves ndp (knapIn cap c d s bySize ndp k) := by
  rw [knapIn_eq]
  cases bySize[k]! with
  | none => exact improves_refl _
  | some e =>
    obtain ⟨dk, sk⟩ := e
    simp only
    split
    · exact improves_refl _
    · split
      · rename_i hbet; exact setBang_improves hbet
      · exact improves_refl _

theorem knapIn_hasAt (cap c : Nat) (d : _root_.Int) (s : Array Nat) (bySize ndp : CTable) (k : Nat)
    {dk : _root_.Int} {sk : Array Nat} (hk : bySize[k]! = some (dk, sk)) (hck : c + k ≤ cap)
    (hsz : cap < ndp.size) : HasAt (knapIn cap c d s bySize ndp k) (c + k) (d + dk) := by
  rw [knapIn_eq, hk]
  simp only
  rw [ite_eq_right (by omega)]
  split
  · exact ⟨_, by rw [setBang_getElem!, ite_eq_left ⟨rfl, by omega⟩], Int.le_refl _⟩
  · rename_i hbet
    cases ho : ndp[c + k]! with
    | none => rw [ho] at hbet; simp [betterEntry] at hbet
    | some x =>
      rw [ho] at hbet
      obtain ⟨d0, s0⟩ := x
      simp only [betterEntry, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
        not_or, not_and] at hbet
      exact ⟨(d0, s0), ho, by simp only; omega⟩

theorem knapOut_size (cap : Nat) (dp bySize ndp : CTable) (c : Nat) :
    (knapOut cap dp bySize ndp c).size = ndp.size := by
  unfold knapOut
  cases dp[c]! with
  | none => rfl
  | some e =>
    obtain ⟨d, s⟩ := e
    simp only
    generalize List.range bySize.size = l
    induction l generalizing ndp with
    | nil => rfl
    | cons k l ih => rw [List.foldl_cons, ih, knapIn_size]

theorem knapOut_improves (cap : Nat) (dp bySize ndp : CTable) (c : Nat) :
    Improves ndp (knapOut cap dp bySize ndp c) := by
  unfold knapOut
  cases dp[c]! with
  | none => exact improves_refl _
  | some e =>
    obtain ⟨d, s⟩ := e
    exact foldl_improves _ (knapIn_improves cap c d s bySize) _ _

theorem knapStep_size (cap : Nat) (dp bySize : CTable) : (knapStep cap dp bySize).size = cap + 1 := by
  rw [knapStep_eq]
  generalize List.range dp.size = l
  suffices h : ∀ (ndp : CTable), (l.foldl (knapOut cap dp bySize) ndp).size = ndp.size by
    rw [h]; simp
  induction l with
  | nil => intro _; rfl
  | cons c l ih => intro ndp; rw [List.foldl_cons, ih, knapOut_size]

/-- **A knapsack step covers every pair** of a count entry and a table entry
within the cap. -/
theorem knapStep_hasAt {cap : Nat} {dp bySize : CTable} {c k : Nat} {e ek : Entry}
    (hc : dp[c]! = some e) (hk : bySize[k]! = some ek) (hck : c + k ≤ cap) :
    HasAt (knapStep cap dp bySize) (c + k) (e.1 + ek.1) := by
  rw [knapStep_eq]
  have hcl : c < dp.size := Classical.byContradiction fun h => by
    simp [show ¬ c < dp.size from h] at hc
  have hkl : k < bySize.size := Classical.byContradiction fun h => by
    simp [show ¬ k < bySize.size from h] at hk
  have hsizes : ∀ (l : List Nat) (ndp : CTable), (l.foldl (knapOut cap dp bySize) ndp).size = ndp.size := by
    intro l; induction l with
    | nil => intro _; rfl
    | cons c l ih => intro ndp; rw [List.foldl_cons, ih, knapOut_size]
  refine foldl_hasAt_inv _ (fun t => cap < t.size)
    (fun acc c' h => by rw [knapOut_size]; exact h) (knapOut_improves cap dp bySize)
    (List.mem_range.mpr hcl) (c + k) (e.1 + ek.1) _ (by simp) ?_
  intro acc hacc
  unfold knapOut
  rw [hc]
  obtain ⟨d, s⟩ := e
  obtain ⟨dk, sk⟩ := ek
  simp only
  refine foldl_hasAt_inv _ (fun t => cap < t.size)
    (fun acc k' h => by rw [knapIn_size]; exact h) (knapIn_improves cap c d s bySize)
    (List.mem_range.mpr hkl) (c + k) (d + dk) _ hacc ?_
  intro acc' hacc'
  exact knapIn_hasAt cap c d s bySize acc' k hk hck hacc'

/-- Entries at their counts (the sets have the count's size). -/
def Indexed (tb : CTable) : Prop := ∀ (k : Nat) (e : Entry), tb[k]! = some e → e.2.size = k

theorem knapIn_indexed {cap c : Nat} {d : _root_.Int} {s : Array Nat} {bySize ndp : CTable}
    (hs : s.size = c) (hb : Indexed bySize) (hn : Indexed ndp) (k : Nat) :
    Indexed (knapIn cap c d s bySize ndp k) := by
  rw [knapIn_eq]
  cases hbk : bySize[k]! with
  | none => exact hn
  | some ek =>
    obtain ⟨dk, sk⟩ := ek
    have hsk := hb k _ hbk
    simp only
    split
    · exact hn
    · split
      · intro j x hx
        rw [setBang_getElem!] at hx
        split at hx
        · rename_i hj
          cases hx
          rw [← hj.1, mergeSorted_size, hs]
          simp only at hsk
          omega
        · exact hn j x hx
      · exact hn

theorem knapStep_indexed {cap : Nat} {dp bySize : CTable} (hd : Indexed dp) (hb : Indexed bySize) :
    Indexed (knapStep cap dp bySize) := by
  rw [knapStep_eq]
  suffices h : ∀ (l : List Nat) (ndp : CTable), Indexed ndp →
      Indexed (l.foldl (knapOut cap dp bySize) ndp) from h _ _ (fun k e he => by
        by_cases hk : k < cap + 1
        · rw [getElem!_pos _ k (by simpa using hk)] at he; simp at he
        · simp [hk] at he)
  intro l
  induction l with
  | nil => intro _ h; exact h
  | cons c l ih =>
    intro ndp hn
    rw [List.foldl_cons]
    apply ih
    unfold knapOut
    cases hdc : dp[c]! with
    | none => exact hn
    | some e =>
      obtain ⟨d, s⟩ := e
      have hs := hd c _ hdc
      simp only at hs ⊢
      generalize List.range bySize.size = l'
      induction l' generalizing ndp with
      | nil => exact hn
      | cons k l' ih' =>
        rw [List.foldl_cons]
        exact ih' _ (knapIn_indexed hs hb hn k)
/-- **The knapsack covers every choice** of one entry per table within the
cap. -/
theorem knapFold_hasAt {cap : Nat} (ts : List CTable) :
    ∀ (ks : List Nat) (vs : List _root_.Int) (dp : CTable) (c0 : Nat) (v0 : _root_.Int),
      ks.length = ts.length → vs.length = ts.length →
      (∀ j, j < ts.length → HasAt ts[j]! ks[j]! vs[j]!) →
      HasAt dp c0 v0 → c0 + ks.sum ≤ cap →
      HasAt (ts.foldl (knapStep cap) dp) (c0 + ks.sum) (v0 + vs.sum) := by
  induction ts with
  | nil =>
    intro ks vs dp c0 v0 hk hv _ hdp _
    have h1 : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk)
    have h2 : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hv)
    subst h1; subst h2
    simpa using hdp
  | cons t ts ih =>
    intro ks vs dp c0 v0 hk hv hall hdp hcap
    cases ks with
    | nil => simp at hk
    | cons k ks =>
      cases vs with
      | nil => simp at hv
      | cons v vs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hk hv
        simp only [List.sum_cons] at hcap ⊢
        rw [List.foldl_cons]
        obtain ⟨e, he, hev⟩ := hdp
        obtain ⟨ek, hek, hekv⟩ := hall 0 (by simp)
        simp only [List.getElem!_cons_zero] at hek hekv
        have hstep := knapStep_hasAt (cap := cap) he hek (by omega)
        have := ih ks vs (knapStep cap dp t) (c0 + k) (v0 + v) hk hv
          (fun j hj => by simpa using hall (j + 1) (by simp; omega))
          (hstep.weaken (by omega)) (by omega)
        rw [show c0 + (k + ks.sum) = c0 + k + ks.sum by omega,
          show v0 + (v + vs.sum) = v0 + v + vs.sum by omega]
        exact this

/-! ## The choice among the counts -/

/-- The length a choice stands for: its `Δ` and its count's TagN. -/
def knapTotal (kCS : Nat) (acc : _root_.Int × Array Nat × Bool) : _root_.Int :=
  acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int)

/-- **The chosen total is at most every candidate's.** -/
theorem knapChoose_le (kCS : Nat) {dp : CTable} (hd : Indexed dp) (init : _root_.Int × Array Nat × Bool) :
    knapTotal kCS (knapChoose kCS dp init) ≤ knapTotal kCS init ∧
      ∀ c e, dp[c]! = some e → knapTotal kCS (knapChoose kCS dp init) ≤
        e.1 + (tag0Size (kCS + c) : _root_.Int) := by
  unfold knapChoose
  have key : ∀ (l : List Nat) (acc : _root_.Int × Array Nat × Bool),
      let r := l.foldl (fun (acc : _root_.Int × Array Nat × Bool) c =>
        match dp[c]! with
        | none => acc
        | some (d, s) =>
          let l : _root_.Int := d + (tag0Size (kCS + c) : _root_.Int)
          let l0 : _root_.Int := acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int)
          if l < l0 || (l == l0 && setPrec s acc.2.1) then (d, s, true) else acc) acc
      knapTotal kCS r ≤ knapTotal kCS acc ∧
        ∀ c ∈ l, ∀ e, dp[c]! = some e → knapTotal kCS r ≤ e.1 + (tag0Size (kCS + c) : _root_.Int) := by
    intro l
    induction l with
    | nil => intro acc; exact ⟨Int.le_refl _, fun c hc => absurd hc List.not_mem_nil⟩
    | cons c l ih =>
      intro acc
      simp only [List.foldl_cons]
      generalize hstep : (match dp[c]! with
        | none => acc
        | some (d, s) =>
          if d + (tag0Size (kCS + c) : _root_.Int) < acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int) ||
            (d + (tag0Size (kCS + c) : _root_.Int) == acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int) &&
              setPrec s acc.2.1) then (d, s, true) else acc) = acc'
      obtain ⟨h1, h2⟩ := ih acc'
      have hle : knapTotal kCS acc' ≤ knapTotal kCS acc ∧
          ∀ e, dp[c]! = some e → knapTotal kCS acc' ≤ e.1 + (tag0Size (kCS + c) : _root_.Int) := by
        rw [← hstep]
        cases hdc : dp[c]! with
        | none => exact ⟨Int.le_refl _, fun e he => by cases he⟩
        | some e =>
          obtain ⟨d, s⟩ := e
          have hs := hd c _ hdc
          simp only at hs ⊢
          split
          · rename_i hlt
            simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hlt
            refine ⟨?_, fun e he => ?_⟩
            · unfold knapTotal; simp only; rw [hs]; unfold knapTotal at *; omega
            · cases he; unfold knapTotal; simp only; rw [hs]; exact Int.le_refl _
          · rename_i hlt
            simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, not_or,
              not_and] at hlt
            refine ⟨Int.le_refl _, fun e he => ?_⟩
            cases he
            unfold knapTotal; simp only; omega
      refine ⟨Int.le_trans h1 hle.1, fun c' hc' e he => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact Int.le_trans h1 (hle.2 e he)
      · exact h2 c' hc' e he
  obtain ⟨h1, h2⟩ := key (List.range dp.size) init
  refine ⟨h1, fun c e he => ?_⟩
  have hc : c < dp.size := Classical.byContradiction fun h => by
    simp [show ¬ c < dp.size from h] at he
  exact h2 c (List.mem_range.mpr hc) e he

/-! ## The knapsack with the tie order -/

/-- Every entry's set lies in `U`. -/
def SetsIn (tb : CTable) (U : Nat → Prop) : Prop := ∀ (k : Nat) (e : Entry), tb[k]! = some e → ∀ x ∈ e.2.toList, U x

theorem knapIn_tie {cap c : Nat} {d : _root_.Int} {s : Array Nat} {bySize ndp : CTable} (k : Nat)
    (hs : s.toList.Pairwise (· < ·)) (hb : SortedT bySize)
    (hd : ∀ (k' : Nat) (e : Entry), bySize[k']! = some e → ∀ x ∈ s.toList, x ∉ e.2.toList)
    (hn : SortedT ndp) :
    SortedT (knapIn cap c d s bySize ndp k) ∧ ImprovesT ndp (knapIn cap c d s bySize ndp k) := by
  rw [knapIn_eq]
  cases hbk : bySize[k]! with
  | none => exact ⟨hn, improvesT_refl _⟩
  | some ek =>
    obtain ⟨dk, sk⟩ := ek
    have hm := mergeSorted_strict hs (hb k _ hbk) (hd k _ hbk)
    simp only
    split
    · exact ⟨hn, improvesT_refl _⟩
    · split
      · rename_i hbet
        refine ⟨fun j x hx => ?_, ?_⟩
        · rw [setBang_getElem!] at hx
          split at hx
          · cases hx; exact hm
          · exact hn j x hx
        · intro j x hx
          by_cases hij : c + k = j ∧ c + k < ndp.size
          · obtain ⟨rfl, hj⟩ := hij
            refine ⟨_, by rw [setBang_getElem!, ite_eq_left ⟨rfl, hj⟩], ?_⟩
            rw [hx] at hbet
            exact (better_tle hm (hn _ x hx)).1 hbet
          · exact ⟨x, by rw [setBang_getElem!, ite_eq_right hij, hx], tle_refl x⟩
      · exact ⟨hn, improvesT_refl _⟩

theorem knapIn_hasAtT {cap c : Nat} {d : _root_.Int} {s : Array Nat} {bySize ndp : CTable} {k : Nat}
    {dk : _root_.Int} {sk : Array Nat} (hk : bySize[k]! = some (dk, sk)) (hck : c + k ≤ cap)
    (hsz : cap < ndp.size) (hn : SortedT ndp) (hm : (mergeSorted s sk).toList.Pairwise (· < ·)) :
    HasAtT (knapIn cap c d s bySize ndp k) (c + k) (d + dk) (mergeSorted s sk).toList := by
  rw [knapIn_eq, hk]
  simp only
  rw [ite_eq_right (by omega)]
  split
  · exact ⟨_, by rw [setBang_getElem!, ite_eq_left ⟨rfl, by omega⟩], Or.inr ⟨rfl, leL_refl _⟩⟩
  · rename_i hbet
    cases ho : ndp[c + k]! with
    | none => rw [ho] at hbet; simp [betterEntry] at hbet
    | some x =>
      rw [ho] at hbet
      have := (better_tle hm (hn _ x ho)).2 (by simpa using hbet)
      exact ⟨x, ho, tle_good this (Or.inr ⟨rfl, leL_refl _⟩)⟩

/-- **A knapsack step with the tie order.** -/
theorem knapStep_tie {cap : Nat} {dp bySize : CTable} (hdp : SortedT dp) (hb : SortedT bySize)
    (hd : ∀ (c : Nat) (e : Entry), dp[c]! = some e → ∀ (k : Nat) (ek : Entry), bySize[k]! = some ek →
      ∀ x ∈ e.2.toList, x ∉ ek.2.toList) :
    SortedT (knapStep cap dp bySize) ∧
      ∀ {c k : Nat} {e ek : Entry}, dp[c]! = some e → bySize[k]! = some ek → c + k ≤ cap →
        HasAtT (knapStep cap dp bySize) (c + k) (e.1 + ek.1) (mergeSorted e.2 ek.2).toList := by
  rw [knapStep_eq]
  have hsorted0 : SortedT (Array.replicate (cap + 1) (none : Option Entry)) := fun k e he => by
    by_cases hk : k < cap + 1
    · rw [getElem!_pos _ k (by simpa using hk)] at he; simp at he
    · simp [hk] at he
  -- the outer step
  have hout : ∀ acc (c : Nat), SortedT acc → SortedT (knapOut cap dp bySize acc c) ∧
      ImprovesT acc (knapOut cap dp bySize acc c) := by
    intro acc c hacc
    unfold knapOut
    cases hdc : dp[c]! with
    | none => exact ⟨hacc, improvesT_refl _⟩
    | some e =>
      obtain ⟨d, s⟩ := e
      simp only
      have hs := hdp c _ hdc
      have key : ∀ (l : List Nat) acc, SortedT acc →
          SortedT (l.foldl (knapIn cap c d s bySize) acc) ∧
            ImprovesT acc (l.foldl (knapIn cap c d s bySize) acc) := by
        intro l
        induction l with
        | nil => intro acc h; exact ⟨h, improvesT_refl _⟩
        | cons k l ih =>
          intro acc h
          rw [List.foldl_cons]
          obtain ⟨h1, h2⟩ := knapIn_tie k hs hb (fun k' e he x hx => hd c _ hdc k' e he x hx) h
          obtain ⟨h3, h4⟩ := ih _ h1
          exact ⟨h3, improvesT_trans h2 h4⟩
      exact key _ acc hacc
  have houter : ∀ (l : List Nat) acc, SortedT acc →
      SortedT (l.foldl (knapOut cap dp bySize) acc) ∧ ImprovesT acc (l.foldl (knapOut cap dp bySize) acc) := by
    intro l
    induction l with
    | nil => intro acc h; exact ⟨h, improvesT_refl _⟩
    | cons c l ih =>
      intro acc h
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := hout acc c h
      obtain ⟨h3, h4⟩ := ih _ h1
      exact ⟨h3, improvesT_trans h2 h4⟩
  refine ⟨(houter _ _ hsorted0).1, fun {c k e ek} hc hk hck => ?_⟩
  have hcl : c < dp.size := Classical.byContradiction fun h => by
    simp [show ¬ c < dp.size from h] at hc
  have hkl : k < bySize.size := Classical.byContradiction fun h => by
    simp [show ¬ k < bySize.size from h] at hk
  refine foldl_hasAtT_inv _ (fun t => cap < t.size ∧ SortedT t)
    (fun acc c' h => ⟨by rw [knapOut_size]; exact h.1, (hout acc c' h.2).1⟩)
    (fun acc c' h => (hout acc c' h.2).2) (List.mem_range.mpr hcl) (c + k) (e.1 + ek.1) _ _
    ⟨by simp, hsorted0⟩ ?_
  intro acc hacc
  unfold knapOut
  rw [hc]
  obtain ⟨d, s⟩ := e
  obtain ⟨dk, sk⟩ := ek
  simp only
  have hs := hdp c _ hc
  refine foldl_hasAtT_inv _ (fun t => cap < t.size ∧ SortedT t)
    (fun acc k' h => ⟨by rw [knapIn_size]; exact h.1,
      (knapIn_tie k' hs hb (fun k'' e he x hx => hd c _ hc k'' e he x hx) h.2).1⟩)
    (fun acc k' h => (knapIn_tie k' hs hb (fun k'' e he x hx => hd c _ hc k'' e he x hx) h.2).2)
    (List.mem_range.mpr hkl) (c + k) (d + dk) _ _ hacc ?_
  intro acc' hacc'
  exact knapIn_hasAtT hk hck hacc'.1 hacc'.2
    (mergeSorted_strict hs (hb k _ hk) (hd c _ hc k _ hk))

/-- Every entry of a knapsack step merges an entry of each side. -/
theorem knapStep_origin {cap : Nat} {dp bySize : CTable} :
    ∀ (j : Nat) (e : Entry), (knapStep cap dp bySize)[j]! = some e →
      ∃ (c k : Nat) (ec ek : Entry), dp[c]! = some ec ∧ bySize[k]! = some ek ∧
        e.2 = mergeSorted ec.2 ek.2 := by
  rw [knapStep_eq]
  let P : CTable → Prop := fun t => ∀ (j : Nat) (e : Entry), t[j]! = some e →
    ∃ (c k : Nat) (ec ek : Entry), dp[c]! = some ec ∧ bySize[k]! = some ek ∧ e.2 = mergeSorted ec.2 ek.2
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
  generalize List.range dp.size = l
  suffices h : ∀ acc, P acc → P (l.foldl (knapOut cap dp bySize) acc) from h _ h0
  induction l with
  | nil => intro acc h; exact h
  | cons c l ih => intro acc h; rw [List.foldl_cons]; exact ih _ (hout acc c h)

/-- **The knapsack covers every choice with the tie order**, for tables on
disjoint universes. -/
theorem knapFold_tie {cap : Nat} (Uf : Nat → Nat → Prop)
    (hU : ∀ i i' x, i ≠ i' → Uf i x → ¬ Uf i' x) (ts : List CTable) :
    ∀ (j0 : Nat) (ks : List Nat) (vs : List _root_.Int) (Ss : List (List Nat)) (dp : CTable)
      (c0 : Nat) (v0 : _root_.Int) (S0 : List Nat),
      ks.length = ts.length → vs.length = ts.length → Ss.length = ts.length →
      (∀ j, j < ts.length → SortedT ts[j]! ∧ SetsIn ts[j]! (Uf (j0 + j)) ∧
        HasAtT ts[j]! ks[j]! vs[j]! Ss[j]! ∧ ∀ x ∈ Ss[j]!, Uf (j0 + j) x) →
      SortedT dp → SetsIn dp (fun x => ∃ i, i < j0 ∧ Uf i x) → HasAtT dp c0 v0 S0 →
      (∀ x ∈ S0, ∃ i, i < j0 ∧ Uf i x) → c0 + ks.sum ≤ cap → cap < dp.size →
      HasAtT (ts.foldl (knapStep cap) dp) (c0 + ks.sum) (v0 + vs.sum) (S0 ++ Ss.flatten) := by
  induction ts with
  | nil =>
    intro j0 ks vs Ss dp c0 v0 S0 hk hv hS _ _ _ hdp _ _ _
    have h1 : ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hk)
    have h2 : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hv)
    have h3 : Ss = [] := List.eq_nil_of_length_eq_zero (by simpa using hS)
    subst h1; subst h2; subst h3
    simpa using hdp
  | cons t ts ih =>
    intro j0 ks vs Ss dp c0 v0 S0 hk hv hS hall hdps hdpU hdp hS0 hcap hsz
    cases ks with
    | nil => simp at hk
    | cons k ks =>
      cases vs with
      | nil => simp at hv
      | cons v vs =>
        cases Ss with
        | nil => simp at hS
        | cons S Ss =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hk hv hS
          simp only [List.sum_cons, List.flatten_cons] at hcap ⊢
          rw [List.foldl_cons]
          obtain ⟨hts, htU, htH, hSU⟩ := hall 0 (by simp)
          simp only [List.getElem!_cons_zero, Nat.add_zero] at hts htU htH hSU
          -- disjointness of the two sides
          have hdisj : ∀ (c : Nat) (e : Entry), dp[c]! = some e → ∀ (k' : Nat) (ek : Entry),
              t[k']! = some ek → ∀ x ∈ e.2.toList, x ∉ ek.2.toList := by
            intro c e he k' ek hek x hx hx'
            obtain ⟨i, hi, hxi⟩ := hdpU c e he x hx
            exact hU i j0 x (by omega) hxi (htU k' ek hek x hx')
          obtain ⟨hstepS, hstepH⟩ := knapStep_tie (cap := cap) hdps hts hdisj
          obtain ⟨e, he, hev⟩ := hdp
          obtain ⟨ek, hek, hekv⟩ := htH
          have hnew := hstepH he hek (by omega)
          -- compose the two tie conditions
          have hcomp : (e.1 + ek.1 < v0 + v) ∨ (e.1 + ek.1 = v0 + v ∧
              LeL (mergeSorted e.2 ek.2).toList (S0 ++ S)) := by
            rcases hev with h1 | ⟨h1, h1'⟩ <;> rcases hekv with h2 | ⟨h2, h2'⟩
            · exact Or.inl (by omega)
            · exact Or.inl (by omega)
            · exact Or.inl (by omega)
            · refine Or.inr ⟨by omega, ?_⟩
              apply precL_union (X1 := e.2.toList) (Y1 := S0) (X2 := ek.2.toList) (Y2 := S)
              · intro a ha hb
                have ha' : ∃ i, i < j0 ∧ Uf i a := by
                  rcases ha with ha | ha
                  · exact hdpU _ e he a ha
                  · exact hS0 a ha
                have hb' : Uf j0 a := by
                  rcases hb with hb | hb
                  · exact htU _ ek hek a hb
                  · exact hSU a hb
                obtain ⟨i, hi, hia⟩ := ha'
                exact hU i j0 a (by omega) hia hb'
              · intro u; rw [(mergeSorted_perm e.2 ek.2).mem_iff, List.mem_append]
              · intro u; rw [List.mem_append]
              · exact h1'
              · exact h2'
          have := ih (j0 + 1) ks vs Ss (knapStep cap dp t) (c0 + k) (v0 + v) (S0 ++ S) hk hv hS
            (fun j hj => by
              have := hall (j + 1) (by simp; omega)
              simp only [List.getElem!_cons_succ] at this
              rw [show j0 + 1 + j = j0 + (j + 1) by omega]
              exact this)
            hstepS
            (fun c e' he' x hx => by
              obtain ⟨c1, k1, ec, ek', hec, hek', hset⟩ := knapStep_origin c e' he'
              rw [hset] at hx
              rcases List.mem_append.mp ((mergeSorted_perm ec.2 ek'.2).mem_iff.mp hx) with h | h
              · obtain ⟨i, hi, hxi⟩ := hdpU c1 ec hec x h
                exact ⟨i, by omega, hxi⟩
              · exact ⟨j0, by omega, htU k1 ek' hek' x h⟩)
            (hnew.weakenT hcomp)
            (fun x hx => by
              rcases List.mem_append.mp hx with h | h
              · obtain ⟨i, hi, hxi⟩ := hS0 x h
                exact ⟨i, by omega, hxi⟩
              · exact ⟨j0, by omega, hSU x h⟩)
            (by omega) (by rw [knapStep_size]; omega)
          rw [show c0 + (k + ks.sum) = c0 + k + ks.sum by omega,
            show v0 + (v + vs.sum) = v0 + v + vs.sum by omega, ← List.append_assoc]
          exact this

/-- A total and set at least as good as another. -/
def CLe (t1 : _root_.Int) (s1 : List Nat) (t2 : _root_.Int) (s2 : List Nat) : Prop :=
  t1 < t2 ∨ (t1 = t2 ∧ LeL s1 s2)

theorem cle_trans {t1 t2 t3 : _root_.Int} {s1 s2 s3 : List Nat} (h1 : CLe t1 s1 t2 s2)
    (h2 : CLe t2 s2 t3 s3) : CLe t1 s1 t3 s3 := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (Int.lt_trans h1 h2)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, leL_trans h1' h2'⟩

theorem cle_refl (t : _root_.Int) (s : List Nat) : CLe t s t s := Or.inr ⟨rfl, leL_refl _⟩

/-- **The chosen total and set are at least as good as every candidate's.** -/
theorem knapChoose_tie (kCS : Nat) {dp : CTable} (hd : Indexed dp) (hs : SortedT dp)
    (init : _root_.Int × Array Nat × Bool) (hinit : init.2.1.toList.Pairwise (· < ·)) :
    CLe (knapTotal kCS (knapChoose kCS dp init)) (knapChoose kCS dp init).2.1.toList
        (knapTotal kCS init) init.2.1.toList ∧
      ∀ c e, dp[c]! = some e → CLe (knapTotal kCS (knapChoose kCS dp init))
        (knapChoose kCS dp init).2.1.toList (e.1 + (tag0Size (kCS + c) : _root_.Int)) e.2.toList := by
  unfold knapChoose
  have key : ∀ (l : List Nat) (acc : _root_.Int × Array Nat × Bool), acc.2.1.toList.Pairwise (· < ·) →
      let r := l.foldl (fun (acc : _root_.Int × Array Nat × Bool) c =>
        match dp[c]! with
        | none => acc
        | some (d, s) =>
          let l : _root_.Int := d + (tag0Size (kCS + c) : _root_.Int)
          let l0 : _root_.Int := acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int)
          if l < l0 || (l == l0 && setPrec s acc.2.1) then (d, s, true) else acc) acc
      CLe (knapTotal kCS r) r.2.1.toList (knapTotal kCS acc) acc.2.1.toList ∧
        ∀ c ∈ l, ∀ e, dp[c]! = some e → CLe (knapTotal kCS r) r.2.1.toList
          (e.1 + (tag0Size (kCS + c) : _root_.Int)) e.2.toList := by
    intro l
    induction l with
    | nil => intro acc _; exact ⟨cle_refl _ _, fun c hc => absurd hc List.not_mem_nil⟩
    | cons c l ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      generalize hstep : (match dp[c]! with
        | none => acc
        | some (d, s) =>
          if d + (tag0Size (kCS + c) : _root_.Int) < acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int) ||
            (d + (tag0Size (kCS + c) : _root_.Int) == acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int) &&
              setPrec s acc.2.1) then (d, s, true) else acc) = acc'
      have hstepP : acc'.2.1.toList.Pairwise (· < ·) ∧
          CLe (knapTotal kCS acc') acc'.2.1.toList (knapTotal kCS acc) acc.2.1.toList ∧
          ∀ e, dp[c]! = some e → CLe (knapTotal kCS acc') acc'.2.1.toList
            (e.1 + (tag0Size (kCS + c) : _root_.Int)) e.2.toList := by
        rw [← hstep]
        cases hdc : dp[c]! with
        | none => exact ⟨hacc, cle_refl _ _, fun e he => by cases he⟩
        | some e =>
          obtain ⟨d, s⟩ := e
          have hsz := hd c _ hdc
          have hss := hs c _ hdc
          simp only at hsz hss ⊢
          split
          · rename_i hlt
            simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hlt
            refine ⟨hss, ?_, fun e he => ?_⟩
            · unfold knapTotal; simp only; rw [hsz]
              rcases hlt with h | ⟨h, h'⟩
              · exact Or.inl (by unfold knapTotal at *; omega)
              · exact Or.inr ⟨by unfold knapTotal at *; omega, Or.inr ((setPrec_iff hss hacc).mp h')⟩
            · cases he; unfold knapTotal; simp only; rw [hsz]; exact cle_refl _ _
          · rename_i hlt
            simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, not_or,
              not_and] at hlt
            refine ⟨hacc, cle_refl _ _, fun e he => ?_⟩
            cases he
            unfold knapTotal; simp only
            by_cases heq : d + (tag0Size (kCS + c) : _root_.Int) =
                acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int)
            · have hns := hlt.2 heq
              refine Or.inr ⟨by omega, ?_⟩
              rcases leL_total hacc hss with h | h
              · exact h
              · exact absurd ((setPrec_iff hss hacc).mpr h) (by simp [hns])
            · exact Or.inl (by omega)
      obtain ⟨hP, h1, h2⟩ := hstepP
      obtain ⟨r1, r2⟩ := ih acc' hP
      refine ⟨cle_trans r1 h1, fun c' hc' e he => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact cle_trans r1 (h2 e he)
      · exact r2 c' hc' e he
  obtain ⟨h1, h2⟩ := key (List.range dp.size) init hinit
  refine ⟨h1, fun c e he => ?_⟩
  have hc : c < dp.size := Classical.byContradiction fun h => by
    simp [show ¬ c < dp.size from h] at he
  exact h2 c (List.mem_range.mpr hc) e he

/-- The knapsack keeps strictly increasing sets in the processed universes. -/
theorem knapFold_sorted {cap : Nat} (Uf : Nat → Nat → Prop)
    (hU : ∀ i i' x, i ≠ i' → Uf i x → ¬ Uf i' x) (ts : List CTable) :
    ∀ (j0 : Nat) (dp : CTable),
      (∀ j, j < ts.length → SortedT ts[j]! ∧ SetsIn ts[j]! (Uf (j0 + j))) →
      SortedT dp → SetsIn dp (fun x => ∃ i, i < j0 ∧ Uf i x) →
      SortedT (ts.foldl (knapStep cap) dp) := by
  induction ts with
  | nil => intro _ dp _ h _; exact h
  | cons t ts ih =>
    intro j0 dp hall hdps hdpU
    rw [List.foldl_cons]
    obtain ⟨hts, htU⟩ := hall 0 (by simp)
    simp only [List.getElem!_cons_zero, Nat.add_zero] at hts htU
    have hdisj : ∀ (c : Nat) (e : Entry), dp[c]! = some e → ∀ (k' : Nat) (ek : Entry),
        t[k']! = some ek → ∀ x ∈ e.2.toList, x ∉ ek.2.toList := by
      intro c e he k' ek hek x hx hx'
      obtain ⟨i, hi, hxi⟩ := hdpU c e he x hx
      exact hU i j0 x (by omega) hxi (htU k' ek hek x hx')
    apply ih (j0 + 1) _ (fun j hj => by
      have := hall (j + 1) (by simp; omega)
      simp only [List.getElem!_cons_succ] at this
      rw [show j0 + 1 + j = j0 + (j + 1) by omega]
      exact this) (knapStep_tie hdps hts hdisj).1
    intro c e' he' x hx
    obtain ⟨c1, k1, ec, ek', hec, hek', hset⟩ := knapStep_origin c e' he'
    rw [hset] at hx
    rcases List.mem_append.mp ((mergeSorted_perm ec.2 ek'.2).mem_iff.mp hx) with h | h
    · obtain ⟨i, hi, hxi⟩ := hdpU c1 ec hec x h
      exact ⟨i, by omega, hxi⟩
    · exact ⟨j0, by omega, htU k1 ek' hek' x h⟩

end Ix.Compile.Verify.UniformModel
