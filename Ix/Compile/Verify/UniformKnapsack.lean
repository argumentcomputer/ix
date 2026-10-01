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
    refine ⟨e, by rw [setBang_getElem!, if_pos ⟨rfl, hj⟩], ?_⟩
    rw [hx] at hb
    simp only [betterEntry, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hb
    omega
  · exact ⟨x, by rw [setBang_getElem!, if_neg hij, hx], Int.le_refl _⟩

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
  rw [if_neg (by omega)]
  split
  · exact ⟨_, by rw [setBang_getElem!, if_pos ⟨rfl, by omega⟩], Int.le_refl _⟩
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
    simp [getElem!_def, show ¬ c < dp.size from h] at hc
  have hkl : k < bySize.size := Classical.byContradiction fun h => by
    simp [getElem!_def, show ¬ k < bySize.size from h] at hk
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
        · simp [getElem!_def, hk] at he)
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

/-- The length a choice stands for: its `Δ` and its count's `Tag0`. -/
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
    simp [getElem!_def, show ¬ c < dp.size from h] at he
  exact h2 c (List.mem_range.mpr hc) e he

end Ix.Compile.Verify.UniformModel
