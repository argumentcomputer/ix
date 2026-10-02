import Ix.Compile.Verify.UniformWritings
import Ix.Compile.Verify.UniformSearch

/-!
# The fixed-dictionary model at per-term Share widths

The uniform-width model (`UniformModel`, `UniformWritings`) prices every
Share at one width `w`. Phase 3 of the tiered construction prices the Share
of each table entry by its real width `widthAt (index)`. This module is the
same model with a width per term, `wd : Nat → Nat` (used where `avail` holds):

* `gCost` / `gInl`: the cheapest standalone / inline writing of a term;
* `gEvalFrom_spec`, `gEvalAll_cost`: the executable dictionary evaluation
  computes them;
* `gBuild_size`: every expression `Prep.build` emits has that length;
* `gValid_cost`, `gExists_opt`: they are the minimum lengths of a writing
  (`Valid`), with Shares priced by `wd`, and the minima are attained;
* `gCost_local`, `evalUp_ok`: the incremental re-evaluation after adding
  one term to the dictionary computes the new model.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (CP NodeArity getElem!_eq_getElem setBang_getElem!
  child_eq_getElem cp_of_childrenPrecede bind_eq_ok sizeInfoWith_app_full sizeInfoWith_app_appCont
  sizeInfoWith_lam_full sizeInfoWith_lam_lamCont sizeInfoWith_all_full sizeInfoWith_all_allCont
  toNat_toUInt64_of_lt pickOption_mem pickOption_filter_ne_share)

/-! ## The model -/

/-- The cost of the cut after `j` spine nodes of `t`: the prefix, ending in
the Share of the `j`-th spine node. -/
def gCutCost (p : Prep) (wd : Nat → Nat) (cost : Nat → Nat) (t j : Nat) : Nat :=
  tag4Size j + prefixSides p cost t j + wd (spineAt p t j)

/-- The available cuts of `t` at spine positions `j, …, spineLen t - 1`. -/
def gCutsFrom (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j : Nat) :
    List Nat :=
  (List.range' j (p.spineLen[t]! - j)).filterMap fun j' =>
    if avail (spineAt p t j') then some (gCutCost p wd cost t j') else none

/-- The internal cuts of telescope `t`. -/
def gCutCosts (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t : Nat) :
    List Nat :=
  gCutsFrom p wd avail cost t 1

theorem gCutCosts_eq (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (cost : Nat → Nat)
    (t : Nat) : gCutCosts p wd avail cost t = gCutsFrom p wd avail cost t 1 := rfl

/-- Cheapest inline writing of `t` given the costs of the terms below it. -/
def gInlOf (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t : Nat) : Nat :=
  if p.family[t]! = .none then
    (p.dag.node t).children.foldl (fun acc c => acc + cost c) (p.dag.node t).head.ownBytes
  else
    (gCutCosts p wd avail cost t).foldl min (naturalCost p cost t)

/-- Cheapest standalone writing of `t`: its Share if stored and shorter. -/
def gCostOf (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t : Nat) :
    Nat :=
  if avail t then min (gInlOf p wd avail cost t) (wd t) else gInlOf p wd avail cost t

/-- The model values of every term, children first. -/
def gVals (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) : Array Nat :=
  foldRange (fun arr t => arr.set! t (gCostOf p wd avail (arr[·]!) t)) 0 p.dag.size
    (Array.replicate p.dag.size 0)

/-- `C_M(t)`: the cheapest standalone writing of `t` with the dictionary
`avail` at the widths `wd`. -/
def gCost (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (t : Nat) : Nat :=
  (gVals p wd avail)[t]!

/-- The cheapest inline writing of `t` (the body of its entry). -/
def gInl (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (t : Nat) : Nat :=
  gInlOf p wd avail (gCost p wd avail) t

section Model


variable {p : Prep} (hp : PrepWF p)
include hp

theorem PrepWF.gInlOf_congr {wd : Nat → Nat} {avail : Nat → Bool} {f g : Nat → Nat} {t : Nat}
    (ht : t < p.dag.size) (hfg : ∀ c, c < t → f c = g c) :
    gInlOf p wd avail f t = gInlOf p wd avail g t := by
  unfold gInlOf
  split
  · rw [← Array.foldl_toList, ← Array.foldl_toList]
    have hch : ∀ c ∈ (p.dag.node t).children.toList, f c = g c :=
      fun c hc => hfg c (hp.dag.child_lt ht (Array.mem_toList_iff.mp hc))
    generalize (p.dag.node t).children.toList = l at hch
    generalize (p.dag.node t).head.ownBytes = acc
    induction l generalizing acc with
    | nil => rfl
    | cons c l ih =>
      simp only [List.foldl_cons]
      rw [hch c List.mem_cons_self]
      exact ih (fun c hc => hch c (List.mem_cons_of_mem _ hc)) _
  · rename_i hf
    obtain ⟨_, _, _, htl, _⟩ := hp.spine t ht hf
    have hcuts : gCutCosts p wd avail f t = gCutCosts p wd avail g t := by
      unfold gCutCosts gCutsFrom
      apply filterMap_congr'
      intro j hj
      rw [List.mem_range'_1] at hj
      unfold gCutCost
      rw [hp.prefixSides_congr j t ht hf (by omega) hfg]
    unfold naturalCost
    rw [hcuts, hp.prefixSides_congr _ t ht hf (Nat.le_refl _) hfg, hfg _ htl]

theorem PrepWF.gCostOf_congr {wd : Nat → Nat} {avail : Nat → Bool} {f g : Nat → Nat} {t : Nat}
    (ht : t < p.dag.size) (hfg : ∀ c, c < t → f c = g c) :
    gCostOf p wd avail f t = gCostOf p wd avail g t := by
  unfold gCostOf
  rw [hp.gInlOf_congr ht hfg]

/-- The model recurrence: `C_S(t)` from the costs of the terms below `t`. -/
theorem PrepWF.gCost_eq (wd : Nat → Nat) (avail : Nat → Bool) (t : Nat) (ht : t < p.dag.size) :
    gCost p wd avail t = gCostOf p wd avail (gCost p wd avail) t := by
  let step := fun (arr : Array Nat) (t : Nat) => arr.set! t (gCostOf p wd avail (arr[·]!) t)
  have hinv : ∀ m, m ≤ p.dag.size →
      ((List.range m).foldl step (Array.replicate p.dag.size 0)).size = p.dag.size ∧
      ∀ t, t < m → ((List.range m).foldl step (Array.replicate p.dag.size 0))[t]! =
        gCostOf p wd avail (((List.range m).foldl step (Array.replicate p.dag.size 0))[·]!) t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      obtain ⟨hsize, hprev⟩ := ih (by omega)
      rw [foldl_range_succ]
      generalize hA : (List.range m).foldl step (Array.replicate p.dag.size 0) = A at hsize hprev
      have hsame : ∀ c, c < m → (step A m)[c]! = A[c]! := by
        intro c hc
        simp only [step, setBang_getElem!]
        rw [ite_eq_right (by omega)]
      refine ⟨by simp [step, hsize], fun t' ht' => ?_⟩
      have hcongr : gCostOf p wd avail ((step A m)[·]!) t' = gCostOf p wd avail (A[·]!) t' :=
        hp.gCostOf_congr (by omega) fun c hc => hsame c (by omega)
      rw [hcongr]
      by_cases htm : t' = m
      · subst htm
        simp only [step, setBang_getElem!, hsize]
        rw [ite_eq_left (by simp; omega)]
      · rw [hsame t' (by omega)]
        exact hprev t' (by omega)
  have := (hinv p.dag.size (Nat.le_refl _)).2 t ht
  unfold gCost gVals
  rw [foldRange_zero]
  exact this

end Model

theorem gCutsFrom_split (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j k : Nat)
    (hjk : j ≤ k) (hk : k < p.spineLen[t]!) (hav : avail (spineAt p t k) = true)
    (hnone : ∀ k', j ≤ k' → k' < k → avail (spineAt p t k') = false) :
    gCutsFrom p wd avail cost t j = gCutCost p wd cost t k :: gCutsFrom p wd avail cost t (k + 1) := by
  unfold gCutsFrom
  rw [show p.spineLen[t]! - j = (k - j) + (1 + (p.spineLen[t]! - (k + 1))) by omega,
    ← List.range'_append_1, ← List.range'_append_1, List.filterMap_append,
    List.filterMap_append]
  have hpre : (List.range' j (k - j)).filterMap (fun j' =>
      if avail (spineAt p t j') then some (gCutCost p wd cost t j') else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro a ha
    rw [List.mem_range'_1] at ha
    rw [hnone a ha.1 (by omega)]
    rfl
  rw [hpre, show j + (k - j) = k by omega]
  simp [hav]

theorem gCutsFrom_nil (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j : Nat)
    (hnone : ∀ k, j ≤ k → k < p.spineLen[t]! → avail (spineAt p t k) = false) :
    gCutsFrom p wd avail cost t j = [] := by
  unfold gCutsFrom
  rw [List.filterMap_eq_nil_iff]
  intro a ha
  rw [List.mem_range'_1] at ha
  rw [hnone a ha.1 (by omega)]
  rfl

theorem PrepWF.gCutScan_spec {p : Prep} (hp : PrepWF p) {wd : Nat → Nat} {avail : Nat → Bool}
    {cost : Nat → Nat} (sides : Array Nat) (below : Array (Option Nat))
    (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none)
    (hsides : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      sides[spineAt p t k]! = prefixSides p cost (spineAt p t k) (p.spineLen[t]! - k))
    (hbelow : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      FirstAvail p avail (spineAt p t k) 1 below[spineAt p t k]!) :
    ∀ (fuel j : Nat) (cur : Option Nat) (best work : Nat), 1 ≤ j → j ≤ p.spineLen[t]! →
      p.spineLen[t]! - j ≤ fuel → FirstAvail p avail t j cur →
      (cutScan p.spineLen sides below width p.spineLen[t]!
          (prefixSides p cost t p.spineLen[t]!) fuel cur best work).1 =
        (gCutsFrom p wd avail cost t j).foldl min best := by
  obtain ⟨_, hk, _, _, _⟩ := hp.spine t ht hf
  intro fuel
  induction fuel with
  | zero =>
    intro j cur best work _ hj hfuel _
    have : gCutsFrom p wd avail cost t j = [] := by
      unfold gCutsFrom
      rw [show p.spineLen[t]! - j = 0 by omega]
      rfl
    rw [this]
    rfl
  | succ fuel ih =>
    intro j cur best work hj1 hj hfuel hcur
    cases cur with
    | none =>
      rw [gCutsFrom_nil p wd avail cost t j hcur]
      rfl
    | some u =>
      obtain ⟨k, hjk, hkl, rfl, hav, hnone⟩ := hcur
      obtain ⟨_, _, hlenk, _⟩ := hk k hkl
      simp only [cutScan]
      rw [gCutsFrom_split p wd avail cost t j k hjk hkl hav hnone, List.foldl_cons,
        ite_lt_eq_min]
      have hcand : tag4Size (p.spineLen[t]! - p.spineLen[spineAt p t k]!) +
          (prefixSides p cost t p.spineLen[t]! - sides[spineAt p t k]!) +
          (widthOf width (spineAt p t k)).getD 0 = gCutCost p wd cost t k := by
        rw [hlenk, hsides k (by omega) hkl, hwidth, ite_eq_left hav]
        have hsplit := prefixSides_add p cost k (p.spineLen[t]! - k) t
        rw [show k + (p.spineLen[t]! - k) = p.spineLen[t]! by omega] at hsplit
        unfold gCutCost
        rw [show p.spineLen[t]! - (p.spineLen[t]! - k) = k by omega, hsplit]
        simp
      rw [hcand]
      exact ih (k + 1) _ _ _ (by omega) (by omega) (by omega)
        (FirstAvail.shift hlenk (hbelow k (by omega) hkl))


def GEvalRow (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (st : DictEval) (t : Nat) : Prop :=
  st.cost[t]! = gCost p wd avail t ∧
    (p.family[t]! ≠ .none →
      st.sides[t]! = prefixSides p (gCost p wd avail) t p.spineLen[t]! ∧
        FirstAvail p avail t 1 st.below[t]!)

theorem PrepWF.gEvalStep_spec {p : Prep} (hp : PrepWF p) {wd : Nat → Nat} {avail : Nat → Bool}
    (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    (affected : Array Bool) (st : DictEval) (m : Nat) (hm : m < p.dag.size)
    (haff : affected[m]! = true)
    (hsz : st.cost.size = p.dag.size ∧ st.sides.size = p.dag.size ∧
      st.below.size = p.dag.size)
    (hrows : ∀ t, t < m → GEvalRow p wd avail st t) :
    let st' := evalStep p.dag p.family p.spineLen p.tail width affected st m
    (st'.cost.size = p.dag.size ∧ st'.sides.size = p.dag.size ∧
      st'.below.size = p.dag.size) ∧ ∀ t, t < m + 1 → GEvalRow p wd avail st' t := by
  intro st'
  obtain ⟨hcs, hss, hbs⟩ := hsz
  have keepN : ∀ (v : Nat) (arr : Array Nat) (i : Nat), i ≠ m → (arr.set! m v)[i]! = arr[i]! := by
    intro v arr i hi
    rw [setBang_getElem!, ite_eq_right (by intro h; exact hi h.1.symm)]
  have keepO : ∀ (v : Option Nat) (arr : Array (Option Nat)) (i : Nat), i ≠ m →
      (arr.set! m v)[i]! = arr[i]! := by
    intro v arr i hi
    rw [setBang_getElem!, ite_eq_right (by intro h; exact hi h.1.symm)]
  have atN : ∀ (v : Nat) (arr : Array Nat), arr.size = p.dag.size → (arr.set! m v)[m]! = v := by
    intro v arr hs
    rw [setBang_getElem!, ite_eq_left ⟨rfl, by omega⟩]
  have atO : ∀ (v : Option Nat) (arr : Array (Option Nat)), arr.size = p.dag.size →
      (arr.set! m v)[m]! = v := by
    intro v arr hs
    rw [setBang_getElem!, ite_eq_left ⟨rfl, by omega⟩]
  have hcostLt : ∀ c, c < m → st.cost[c]! = gCost p wd avail c := fun c hc => (hrows c hc).1
  have hcm := hp.gCost_eq wd avail m hm
  have hcostOf : ∀ inl, gInlOf p wd avail (gCost p wd avail) m = inl →
      (match widthOf width m with
        | some w => min inl w
        | none => inl) = gCost p wd avail m := by
    intro inl hinl
    rw [hcm]
    unfold gCostOf
    rw [hinl, hwidth]
    by_cases ha : avail m = true <;> simp [ha]
  by_cases hf : p.family[m]! = .none
  · -- non-telescope
    have hfold : (p.dag.node m).children.foldl (fun acc c => acc + st.cost[c]!)
        (p.dag.node m).head.ownBytes = gInlOf p wd avail (gCost p wd avail) m := by
      unfold gInlOf
      rw [ite_eq_left hf]
      exact foldl_add_congr _ _ fun c hc => hcostLt c (hp.dag.child_lt hm hc)
    have hst' : st'.cost = st.cost.set! m (gCost p wd avail m) ∧ st'.sides = st.sides ∧
        st'.below = st.below := by
      simp only [st', evalStep, haff, ite_true, hf, beq_self_eq_true]
      refine ⟨?_, trivial, trivial⟩
      congr 1
      exact hcostOf _ hfold.symm
    obtain ⟨hc', hs', hb'⟩ := hst'
    refine ⟨⟨by simp [hc', hcs], by rw [hs']; exact hss, by rw [hb']; exact hbs⟩,
      fun t ht => ?_⟩
    by_cases htm : t = m
    · subst htm
      exact ⟨by rw [hc', atN _ _ hcs], fun h => absurd hf h⟩
    · obtain ⟨h1, h2⟩ := hrows t (by omega)
      refine ⟨by rw [hc', keepN _ _ _ htm, h1], ?_⟩
      rw [hs', hb']
      exact h2
  · -- telescope
    obtain ⟨hl1, hk, hend, htl, _⟩ := hp.spine m hm hf
    have hlt := hp.snext_lt hm hf
    have hside := hp.sideChild_lt hm hf
    have hS : (p.dag.node m).sideExtra + st.cost[(p.dag.node m).sideChild]! +
        (if p.family[snext p m]! = p.family[m]! then st.sides[snext p m]! else 0) =
        prefixSides p (gCost p wd avail) m p.spineLen[m]! := by
      rw [hcostLt _ hside]
      rcases hp.spine_step hm hf with ⟨hs, hl, _⟩ | ⟨hs, hl, _⟩
      · rw [ite_eq_left hs, ((hrows _ hlt).2 (by rw [hs]; exact hf)).1, hl]
        rfl
      · rw [ite_eq_right hs, hl]
        simp [prefixSides, sideCost]
    have hB : FirstAvail p avail m 1
        (if p.family[snext p m]! = p.family[m]! then
          (if (widthOf width (snext p m)).isSome then some (snext p m)
            else st.below[snext p m]!) else none) := by
      rcases hp.spine_step hm hf with ⟨hs, hl, _⟩ | ⟨hs, hl, _⟩
      · rw [ite_eq_left hs, hwidth]
        have hn1 := (hp.spine (snext p m) (by omega) (by rw [hs]; exact hf)).1
        by_cases hav : avail (snext p m) = true
        · rw [ite_eq_left hav]
          exact ⟨1, Nat.le_refl _, by omega, rfl, hav, fun k' h1 h2 => by omega⟩
        · rw [ite_eq_right hav]
          simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
          have hrow := ((hrows _ hlt).2 (by rw [hs]; exact hf)).2
          have hlen1 : p.spineLen[spineAt p m 1]! = p.spineLen[m]! - 1 := by
            simp only [spineAt]; omega
          exact FirstAvail.unshift (by omega) (by simpa [spineAt] using hav)
            (FirstAvail.shift hlen1 hrow)
      · rw [ite_eq_right hs]
        intro k h1 h2
        omega
    generalize hBdef : (if p.family[snext p m]! = p.family[m]! then
          (if (widthOf width (snext p m)).isSome then some (snext p m)
            else st.below[snext p m]!) else none) = B at hB
    generalize hSdef : prefixSides p (gCost p wd avail) m p.spineLen[m]! = S at hS
    -- rows of the spine nodes below `m`
    have hspine : ∀ k, 1 ≤ k → k < p.spineLen[m]! →
        spineAt p m k ≠ m ∧ GEvalRow p wd avail st (spineAt p m k) ∧
          p.family[spineAt p m k]! ≠ .none ∧
          p.spineLen[spineAt p m k]! = p.spineLen[m]! - k := by
      intro k h1 h2
      have hlt' := hp.spineAt_lt hm hf h1 h2
      obtain ⟨_, hkf, hklen, _⟩ := hk k h2
      exact ⟨by omega, hrows _ hlt', by rw [hkf]; exact hf, hklen⟩
    have hsides : ∀ k, 1 ≤ k → k < p.spineLen[m]! →
        (st.sides.set! m S)[spineAt p m k]! =
          prefixSides p (gCost p wd avail) (spineAt p m k) (p.spineLen[m]! - k) := by
      intro k h1 h2
      obtain ⟨hne, hrow, hfk, hlenk⟩ := hspine k h1 h2
      rw [keepN _ _ _ hne, (hrow.2 hfk).1, hlenk]
    have hbelow : ∀ k, 1 ≤ k → k < p.spineLen[m]! →
        FirstAvail p avail (spineAt p m k) 1 (st.below.set! m B)[spineAt p m k]! := by
      intro k h1 h2
      obtain ⟨hne, hrow, hfk, _⟩ := hspine k h1 h2
      rw [keepO _ _ _ hne]
      exact (hrow.2 hfk).2
    have hscan := hp.gCutScan_spec (cost := gCost p wd avail) (st.sides.set! m S)
      (st.below.set! m B) width hwidth hm hf hsides hbelow p.spineLen[m]! 1 B
      (tag4Size p.spineLen[m]! + S + st.cost[p.tail[m]!]!) st.work (Nat.le_refl _)
      (by omega) (by omega) hB
    rw [hSdef] at hscan
    have hinl : gInlOf p wd avail (gCost p wd avail) m =
        (cutScan p.spineLen (st.sides.set! m S) (st.below.set! m B) width p.spineLen[m]! S
          p.spineLen[m]! B (tag4Size p.spineLen[m]! + S + st.cost[p.tail[m]!]!) st.work).1 := by
      rw [hscan, hcostLt _ htl]
      unfold gInlOf
      rw [ite_eq_right hf, gCutCosts_eq, naturalCost, hSdef]
    have hst' : st'.cost = st.cost.set! m (gCost p wd avail m) ∧
        st'.sides = st.sides.set! m S ∧ st'.below = st.below.set! m B := by
      simp only [st', evalStep, haff, ite_true]
      have hfb : (p.family[m]! == Family.none) = false := by simpa using hf
      simp only [hfb, Bool.false_eq_true, ite_false]
      simp only [ite_beq_family]
      rw [show (p.dag.node m).spineNext = snext p m from rfl, hS, hBdef]
      refine ⟨?_, rfl, rfl⟩
      congr 1
      exact hcostOf _ hinl
    obtain ⟨hc', hs', hb'⟩ := hst'
    refine ⟨⟨by simp [hc', hcs], by simp [hs', hss], by simp [hb', hbs]⟩, fun t ht => ?_⟩
    by_cases htm : t = m
    · subst htm
      refine ⟨by rw [hc', atN _ _ hcs], fun _ => ⟨?_, ?_⟩⟩
      · rw [hs', atN _ _ hss, hSdef]
      · rw [hb', atO _ _ hbs]
        exact hB
    · obtain ⟨h1, h2⟩ := hrows t (by omega)
      refine ⟨by rw [hc', keepN _ _ _ htm, h1], fun hft => ?_⟩
      obtain ⟨h3, h4⟩ := h2 hft
      exact ⟨by rw [hs', keepN _ _ _ htm, h3], by rw [hb', keepO _ _ _ htm]; exact h4⟩

theorem PrepWF.gEvalFrom_spec {p : Prep} (hp : PrepWF p) {wd : Nat → Nat} {avail : Nat → Bool}
    (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none) (init : DictEval)
    (hsz : init.cost.size = p.dag.size ∧ init.sides.size = p.dag.size ∧
      init.below.size = p.dag.size)
    (affected : Array Bool) (haff : ∀ t, t < p.dag.size → affected[t]! = true) :
    ∀ t, t < p.dag.size →
      GEvalRow p wd avail (evalFrom p.dag p.family p.spineLen p.tail init width affected) t := by
  have hinv : ∀ m, m ≤ p.dag.size →
      let st := (List.range m).foldl (evalStep p.dag p.family p.spineLen p.tail width affected)
        { init with work := 0 }
      (st.cost.size = p.dag.size ∧ st.sides.size = p.dag.size ∧ st.below.size = p.dag.size) ∧
        ∀ t, t < m → GEvalRow p wd avail st t := by
    intro m
    induction m with
    | zero => intro _; exact ⟨hsz, fun t h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs, hrows⟩ := ih (by omega)
      simp only at hs hrows ⊢
      rw [foldl_range_succ]
      exact hp.gEvalStep_spec width hwidth affected _ m (by omega) (haff m (by omega)) hs hrows
  intro t ht
  unfold evalFrom
  rw [foldRange_zero]
  exact (hinv p.dag.size (Nat.le_refl _)).2 t ht

theorem gVals_size (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) :
    (gVals p wd avail).size = p.dag.size := by
  unfold gVals
  rw [foldRange_zero]
  generalize List.range p.dag.size = l
  suffices h : ∀ (arr : Array Nat),
      (l.foldl (fun arr t => arr.set! t (gCostOf p wd avail (arr[·]!) t)) arr).size = arr.size by
    rw [h]; simp
  induction l with
  | nil => intro _; rfl
  | cons x l ih => intro arr; rw [List.foldl_cons, ih]; simp

theorem gCost_of_ge (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) {t : Nat}
    (ht : p.dag.size ≤ t) : gCost p wd avail t = 0 := by
  unfold gCost
  simp [gVals_size, show ¬ t < p.dag.size by omega]

/-- `Prep.evalAll` computes `C_S` for every term (`0` out of range on both
sides). -/
theorem PrepWF.gEvalAll_cost {p : Prep} (hp : PrepWF p) {wd : Nat → Nat} {avail : Nat → Bool}
    (hempty : p.empty.cost.size = p.dag.size ∧ p.empty.sides.size = p.dag.size ∧
      p.empty.below.size = p.dag.size)
    (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none) (t : Nat) :
    (p.evalAll width).cost[t]! = gCost p wd avail t := by
  by_cases ht : t < p.dag.size
  · exact (hp.gEvalFrom_spec width hwidth p.empty hempty _
      (fun t ht => by simp [ht]) t ht).1
  · have hs := (evalFrom_size p.dag p.family p.spineLen p.tail p.empty width
      (Array.replicate p.dag.size true)).1
    rw [gCost_of_ge p wd avail (by omega)]
    unfold Prep.evalAll Prep.eval
    simp [hs, hempty.1, show ¬ t < p.dag.size by omega]

/-! ## The entry cost of materialization -/


/-- An evaluation whose rows are the model rows of every term. -/
def GEvalOK (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (ev : DictEval) : Prop :=
  (ev.cost.size = p.dag.size ∧ ev.sides.size = p.dag.size ∧ ev.below.size = p.dag.size) ∧
    ∀ t, t < p.dag.size → GEvalRow p wd avail ev t

theorem GEvalOK.cost {p : Prep} {wd : Nat → Nat} {avail : Nat → Bool} {ev : DictEval}
    (h : GEvalOK p wd avail ev) (c : Nat) : ev.cost[c]! = gCost p wd avail c := by
  by_cases hc : c < p.dag.size
  · exact (h.2 c hc).1
  · rw [gCost_of_ge p wd avail (by omega)]
    simp [h.1.1, hc]

/-- `Prep.evalAll` gives the model rows. -/
theorem PrepWF.evalAll_ok {p : Prep} (hp : PrepWF p)
    (hempty : p.empty.cost.size = p.dag.size ∧ p.empty.sides.size = p.dag.size ∧
      p.empty.below.size = p.dag.size)
    {wd : Nat → Nat} {avail : Nat → Bool} (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none) :
    GEvalOK p wd avail (p.evalAll width) := by
  refine ⟨?_, hp.gEvalFrom_spec width hwidth p.empty hempty _ (fun t ht => by simp [ht])⟩
  obtain ⟨a, b, c⟩ := evalFrom_size p.dag p.family p.spineLen p.tail p.empty width
    (Array.replicate p.dag.size true)
  exact ⟨a.trans hempty.1, b.trans hempty.2.1, c.trans hempty.2.2⟩

/-! ## Options and built lengths -/

/-- The internal-cut options found by `Prep.cutOptions` are the available cuts. -/
theorem PrepWF.gCutOptions_spec {p : Prep} (hp : PrepWF p) {wd : Nat → Nat} {avail : Nat → Bool}
    (ev : DictEval) (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u)
    {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) (flag : UInt8)
    (hsides : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      ev.sides[spineAt p t k]! =
        prefixSides p (gCost p wd avail) (spineAt p t k) (p.spineLen[t]! - k))
    (hbelow : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      FirstAvail p avail (spineAt p t k) 1 ev.below[spineAt p t k]!) :
    ∀ (fuel j : Nat) (cur : Option Nat) (opts : Array (Choice × Nat × ByteArray)),
      1 ≤ j → j ≤ p.spineLen[t]! → p.spineLen[t]! - j ≤ fuel → FirstAvail p avail t j cur →
      ∃ L : List (Choice × Nat × ByteArray),
        (p.cutOptions ev index width flag p.spineLen[t]!
          (prefixSides p (gCost p wd avail) t p.spineLen[t]!) fuel cur opts).toList =
          opts.toList ++ L ∧
        L.map (·.2.1) = gCutsFrom p wd avail (gCost p wd avail) t j ∧
        ∀ o ∈ L, o.1 ≠ .share := by
  obtain ⟨_, hk, _, _, _⟩ := hp.spine t ht hf
  intro fuel
  induction fuel with
  | zero =>
    intro j cur opts _ hj hfuel _
    refine ⟨[], by simp [Prep.cutOptions], ?_, fun o ho => by cases ho⟩
    unfold gCutsFrom
    rw [show p.spineLen[t]! - j = 0 by omega]
    rfl
  | succ fuel ih =>
    intro j cur opts hj1 hj hfuel hcur
    cases cur with
    | none =>
      exact ⟨[], by simp [Prep.cutOptions], by rw [gCutsFrom_nil p wd avail _ t j hcur]; rfl,
        fun o ho => by cases ho⟩
    | some u =>
      obtain ⟨k, hjk, hkl, rfl, hav, hnone⟩ := hcur
      obtain ⟨_, _, hlenk, _⟩ := hk k hkl
      have hcand : tag4Size (p.spineLen[t]! - p.spineLen[spineAt p t k]!) +
          (prefixSides p (gCost p wd avail) t p.spineLen[t]! - ev.sides[spineAt p t k]!) +
          (widthOf width (spineAt p t k)).getD 0 = gCutCost p wd (gCost p wd avail) t k := by
        rw [hlenk, hsides k (by omega) hkl, hwidth, ite_eq_left hav]
        have hsplit := prefixSides_add p (gCost p wd avail) k (p.spineLen[t]! - k) t
        rw [show k + (p.spineLen[t]! - k) = p.spineLen[t]! by omega] at hsplit
        unfold gCutCost
        rw [show p.spineLen[t]! - (p.spineLen[t]! - k) = k by omega, hsplit]
        simp
      have hidx : (index[spineAt p t k]?.getD none).isSome = true := by rw [hindex]; exact hav
      simp only [Prep.cutOptions, hidx, ite_true]
      obtain ⟨L, hL, hcost, hnot⟩ := ih (k + 1) _ _ (by omega) (by omega) (by omega)
        (FirstAvail.shift hlenk (hbelow k (by omega) hkl))
      refine ⟨(Choice.cut (p.spineLen[t]! - p.spineLen[spineAt p t k]!),
        tag4Size (p.spineLen[t]! - p.spineLen[spineAt p t k]!) +
          (prefixSides p (gCost p wd avail) t p.spineLen[t]! - ev.sides[spineAt p t k]!) +
          (widthOf width (spineAt p t k)).getD 0,
        tag4Bytes flag (p.spineLen[t]! - p.spineLen[spineAt p t k]!)) :: L, ?_, ?_, ?_⟩
      · rw [hL]; simp
      · rw [List.map_cons, hcost, gCutsFrom_split p wd avail _ t j k hjk hkl hav hnone]
        simp only
        rw [hcand]
      · intro o ho
        rcases List.mem_cons.mp ho with rfl | ho
        · simp
        · exact hnot o ho

/-- The entry cost used by `materializeDependent` is the model's inline cost. -/
theorem PrepWF.gInlineCost_eq {p : Prep} (hp : PrepWF p)
    {wd : Nat → Nat} {avail : Nat → Bool} (ev : DictEval) (hev : GEvalOK p wd avail ev) (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u) (t : Nat) (ht : t < p.dag.size) :
    p.inlineCost ev index width t = gInl p wd avail t := by
  have hrow : ∀ t', t' < p.dag.size → GEvalRow p wd avail ev t' :=
    hev.2
  have hcost : ∀ c, c < p.dag.size → ev.cost[c]! = gCost p wd avail c :=
    fun c hc => (hrow c hc).1
  let base : Array (Choice × Nat × ByteArray) :=
    match index[t]?.getD none with
    | some i => #[(Choice.share, (widthOf width t).getD 0, tag4Bytes Ixon.Expr.FLAG_SHARE i)]
    | none => #[]
  have hbase : base.toList.filter (fun o => o.1 != Choice.share) = [] :=
    share_opts_filter index width t
  unfold Prep.inlineCost Prep.options gInl
  by_cases hf : p.family[t]! = .none
  · have hfb : (p.family[t]! == Family.none) = true := by simp [hf]
    simp only [hfb, ite_true]
    have hfold : (p.dag.node t).children.foldl (fun acc c => acc + ev.cost[c]!)
        (p.dag.node t).head.ownBytes = gInlOf p wd avail (gCost p wd avail) t := by
      unfold gInlOf
      rw [ite_eq_left hf]
      exact foldl_add_congr _ _ fun c hc =>
        hcost c (by have := hp.dag.child_lt ht hc; omega)
    rw [pickOption_cost _ (Choice.inline, gInlOf p wd avail (gCost p wd avail) t,
      Ixon.runPut (Ixon.putTagN 4 (p.dag.node t).head.flag (p.dag.node t).head.tag4Field)) []]
    · rfl
    · rw [Array.toList_filter, Array.toList_push, List.filter_append]
      change base.toList.filter _ ++ _ = _
      rw [hbase, hfold]
      rfl
  · have hfb : (p.family[t]! == Family.none) = false := by simpa using hf
    simp only [hfb, Bool.false_eq_true, ite_false]
    obtain ⟨hs, hb⟩ := (hrow t ht).2 hf
    obtain ⟨_, hk, _, htl, _⟩ := hp.spine t ht hf
    have hspine : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
        GEvalRow p wd avail ev (spineAt p t k) ∧
          p.family[spineAt p t k]! ≠ .none ∧
          p.spineLen[spineAt p t k]! = p.spineLen[t]! - k := by
      intro k h1 h2
      have hlt' := hp.spineAt_lt ht hf h1 h2
      obtain ⟨_, hkf, hklen, _⟩ := hk k h2
      exact ⟨hrow _ (by omega), by rw [hkf]; exact hf, hklen⟩
    let natOpt : Choice × Nat × ByteArray :=
      (Choice.cut p.spineLen[t]!,
        tag4Size p.spineLen[t]! + ev.sides[t]! +
          ev.cost[p.tail[t]!]!,
        tag4Bytes (p.dag.node t).head.flag p.spineLen[t]!)
    obtain ⟨L, hL, hLcost, hLnot⟩ := hp.gCutOptions_spec ev index width hwidth
      hindex ht hf (p.dag.node t).head.flag
      (fun k h1 h2 => by
        obtain ⟨hr, hfk, hlenk⟩ := hspine k h1 h2
        rw [(hr.2 hfk).1, hlenk])
      (fun k h1 h2 => by
        obtain ⟨hr, hfk, _⟩ := hspine k h1 h2
        exact (hr.2 hfk).2)
      p.spineLen[t]! 1 _ (base.push natOpt) (Nat.le_refl _) (by omega) (by omega) hb
    rw [← hs] at hL
    have hnat : natOpt.2.1 = naturalCost p (gCost p wd avail) t := by
      simp only [natOpt]
      rw [hs, hcost _ (by omega)]
      rfl
    rw [pickOption_cost _ natOpt L]
    · rw [hLcost, hnat]
      unfold gInlOf
      rw [ite_eq_right hf, gCutCosts_eq]
    · simp only [base, natOpt] at hL hbase
      rw [Array.toList_filter]
      refine (congrArg (List.filter _) hL).trans ?_
      rw [Array.toList_push, List.filter_append, List.filter_append,
        hbase, List.filter_eq_self.mpr (fun o ho => choice_ne_share (hLnot o ho))]
      rfl

/-- The internal cuts with their choices. -/
def gCutsFromC (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j : Nat) :
    List (Choice × Nat) :=
  (List.range' j (p.spineLen[t]! - j)).filterMap fun j' =>
    if avail (spineAt p t j') then some (.cut j', gCutCost p wd cost t j') else none

theorem mem_gCutsFromC {p : Prep} {wd : Nat → Nat} {avail : Nat → Bool} {cost : Nat → Nat} {t j : Nat}
    {ch : Choice} {c : Nat} (h : (ch, c) ∈ gCutsFromC p wd avail cost t j) :
    ∃ k, j ≤ k ∧ k < p.spineLen[t]! ∧ avail (spineAt p t k) = true ∧ ch = .cut k ∧
      c = gCutCost p wd cost t k := by
  unfold gCutsFromC at h
  obtain ⟨k, hk, hkv⟩ := List.mem_filterMap.mp h
  rw [List.mem_range'_1] at hk
  split at hkv
  · rename_i hav
    simp only [Option.some.injEq, Prod.mk.injEq] at hkv
    exact ⟨k, hk.1, by omega, hav, hkv.1.symm, hkv.2.symm⟩
  · cases hkv

theorem gCutsFromC_split (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j k : Nat)
    (hjk : j ≤ k) (hk : k < p.spineLen[t]!) (hav : avail (spineAt p t k) = true)
    (hnone : ∀ k', j ≤ k' → k' < k → avail (spineAt p t k') = false) :
    gCutsFromC p wd avail cost t j =
      (Choice.cut k, gCutCost p wd cost t k) :: gCutsFromC p wd avail cost t (k + 1) := by
  unfold gCutsFromC
  rw [show p.spineLen[t]! - j = (k - j) + (1 + (p.spineLen[t]! - (k + 1))) by omega,
    ← List.range'_append_1, ← List.range'_append_1, List.filterMap_append,
    List.filterMap_append]
  have hpre : (List.range' j (k - j)).filterMap (fun j' =>
      if avail (spineAt p t j') then some (Choice.cut j', gCutCost p wd cost t j') else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro a ha
    rw [List.mem_range'_1] at ha
    rw [hnone a ha.1 (by omega)]
    rfl
  rw [hpre, show j + (k - j) = k by omega]
  simp [hav]

theorem gCutsFromC_nil (p : Prep) (wd : Nat → Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j : Nat)
    (hnone : ∀ k, j ≤ k → k < p.spineLen[t]! → avail (spineAt p t k) = false) :
    gCutsFromC p wd avail cost t j = [] := by
  unfold gCutsFromC
  rw [List.filterMap_eq_nil_iff]
  intro a ha
  rw [List.mem_range'_1] at ha
  rw [hnone a ha.1 (by omega)]
  rfl

/-- The internal-cut options found by `Prep.cutOptions`, with their choices. -/
theorem PrepWF.gCutOptions_pairs {p : Prep} (hp : PrepWF p) {wd : Nat → Nat} {avail : Nat → Bool}
    (ev : DictEval) (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u)
    {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) (flag : UInt8)
    (hsides : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      ev.sides[spineAt p t k]! =
        prefixSides p (gCost p wd avail) (spineAt p t k) (p.spineLen[t]! - k))
    (hbelow : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      FirstAvail p avail (spineAt p t k) 1 ev.below[spineAt p t k]!) :
    ∀ (fuel j : Nat) (cur : Option Nat) (opts : Array (Choice × Nat × ByteArray)),
      1 ≤ j → j ≤ p.spineLen[t]! → p.spineLen[t]! - j ≤ fuel → FirstAvail p avail t j cur →
      ∃ L : List (Choice × Nat × ByteArray),
        (p.cutOptions ev index width flag p.spineLen[t]!
          (prefixSides p (gCost p wd avail) t p.spineLen[t]!) fuel cur opts).toList =
          opts.toList ++ L ∧
        L.map (fun o => (o.1, o.2.1)) = gCutsFromC p wd avail (gCost p wd avail) t j := by
  obtain ⟨_, hk, _, _, _⟩ := hp.spine t ht hf
  intro fuel
  induction fuel with
  | zero =>
    intro j cur opts _ hj hfuel _
    refine ⟨[], by simp [Prep.cutOptions], ?_⟩
    unfold gCutsFromC
    rw [show p.spineLen[t]! - j = 0 by omega]
    rfl
  | succ fuel ih =>
    intro j cur opts hj1 hj hfuel hcur
    cases cur with
    | none =>
      exact ⟨[], by simp [Prep.cutOptions], by rw [gCutsFromC_nil p wd avail _ t j hcur]; rfl⟩
    | some u =>
      obtain ⟨k, hjk, hkl, rfl, hav, hnone⟩ := hcur
      obtain ⟨_, _, hlenk, _⟩ := hk k hkl
      have hcand : tag4Size (p.spineLen[t]! - p.spineLen[spineAt p t k]!) +
          (prefixSides p (gCost p wd avail) t p.spineLen[t]! - ev.sides[spineAt p t k]!) +
          (widthOf width (spineAt p t k)).getD 0 = gCutCost p wd (gCost p wd avail) t k := by
        rw [hlenk, hsides k (by omega) hkl, hwidth, ite_eq_left hav]
        have hsplit := prefixSides_add p (gCost p wd avail) k (p.spineLen[t]! - k) t
        rw [show k + (p.spineLen[t]! - k) = p.spineLen[t]! by omega] at hsplit
        unfold gCutCost
        rw [show p.spineLen[t]! - (p.spineLen[t]! - k) = k by omega, hsplit]
        simp
      have hidx : (index[spineAt p t k]?.getD none).isSome = true := by rw [hindex]; exact hav
      simp only [Prep.cutOptions, hidx, ite_true]
      obtain ⟨L, hL, hcost⟩ := ih (k + 1) _ _ (by omega) (by omega) (by omega)
        (FirstAvail.shift hlenk (hbelow k (by omega) hkl))
      refine ⟨(Choice.cut (p.spineLen[t]! - p.spineLen[spineAt p t k]!),
        tag4Size (p.spineLen[t]! - p.spineLen[spineAt p t k]!) +
          (prefixSides p (gCost p wd avail) t p.spineLen[t]! - ev.sides[spineAt p t k]!) +
          (widthOf width (spineAt p t k)).getD 0,
        tag4Bytes flag (p.spineLen[t]! - p.spineLen[spineAt p t k]!)) :: L, ?_, ?_⟩
      · rw [hL]; simp
      · rw [List.map_cons, hcost, gCutsFromC_split p wd avail _ t j k hjk hkl hav hnone]
        simp only
        rw [hcand, hlenk, show p.spineLen[t]! - (p.spineLen[t]! - k) = k by omega]

/-- The options of a term: its Share (if stored), its inline node, or a
telescope cut of `j` spine nodes, with the model costs. -/
theorem PrepWF.gOptions_mem {p : Prep} (hp : PrepWF p)
    {wd : Nat → Nat} {avail : Nat → Bool} (ev : DictEval) (hev : GEvalOK p wd avail ev) (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u) {t : Nat} (ht : t < p.dag.size)
    {ch : Choice} {c : Nat} {b : ByteArray}
    (h : (ch, c, b) ∈ (p.options ev index width t).toList) :
    (ch = .share ∧ c = wd t ∧ avail t = true) ∨
      (ch = .inline ∧ p.family[t]! = .none ∧ c = gInl p wd avail t) ∨
      (∃ j, ch = .cut j ∧ p.family[t]! ≠ .none ∧ 1 ≤ j ∧ j ≤ p.spineLen[t]! ∧
        ((j = p.spineLen[t]! ∧ c = naturalCost p (gCost p wd avail) t) ∨
          (j < p.spineLen[t]! ∧ avail (spineAt p t j) = true ∧
            c = gCutCost p wd (gCost p wd avail) t j))) := by
  have hrow : ∀ t', t' < p.dag.size → GEvalRow p wd avail ev t' :=
    hev.2
  have hcost : ∀ c, ev.cost[c]! = gCost p wd avail c :=
    hev.cost
  -- the base: the Share option, if any
  have hbase : ∀ x ∈ (match index[t]?.getD none with
      | some i => #[(Choice.share, (widthOf width t).getD 0, tag4Bytes Ixon.Expr.FLAG_SHARE i)]
      | none => (#[] : Array (Choice × Nat × ByteArray))).toList,
      x.1 = .share ∧ x.2.1 = wd t ∧ avail t = true := by
    intro x hx
    split at hx
    · rename_i i hi
      simp only [List.mem_singleton] at hx
      have hav : avail t = true := by rw [← hindex, hi]; rfl
      subst hx
      exact ⟨rfl, by simp [hwidth, hav], hav⟩
    · simp at hx
  unfold Prep.options at h
  by_cases hf : p.family[t]! = .none
  · have hfb : (p.family[t]! == Family.none) = true := by simp [hf]
    simp only [hfb, ite_true, Array.toList_push, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · obtain ⟨h1, h2, h3⟩ := hbase _ h
      exact Or.inl ⟨h1, h2, h3⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, _⟩ := h
      refine Or.inr (Or.inl ⟨rfl, hf, ?_⟩)
      unfold gInl gInlOf
      rw [ite_eq_left hf]
      exact foldl_add_congr _ _ fun c _ => hcost c
  · have hfb : (p.family[t]! == Family.none) = false := by simpa using hf
    simp only [hfb, Bool.false_eq_true, ite_false] at h
    obtain ⟨hs, hb⟩ := (hrow t ht).2 hf
    obtain ⟨hl1, hk, _, htl, _⟩ := hp.spine t ht hf
    have hspine : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
        GEvalRow p wd avail ev (spineAt p t k) ∧
          p.family[spineAt p t k]! ≠ .none ∧
          p.spineLen[spineAt p t k]! = p.spineLen[t]! - k := by
      intro k h1 h2
      have hlt' := hp.spineAt_lt ht hf h1 h2
      obtain ⟨_, hkf, hklen, _⟩ := hk k h2
      exact ⟨hrow _ (by omega), by rw [hkf]; exact hf, hklen⟩
    obtain ⟨L, hL, hLc⟩ := hp.gCutOptions_pairs ev index width hwidth
      hindex ht hf (p.dag.node t).head.flag
      (fun k h1 h2 => by
        obtain ⟨hr, hfk, hlenk⟩ := hspine k h1 h2
        rw [(hr.2 hfk).1, hlenk])
      (fun k h1 h2 => by
        obtain ⟨hr, hfk, _⟩ := hspine k h1 h2
        exact (hr.2 hfk).2)
      p.spineLen[t]! 1 _ ((match index[t]?.getD none with
        | some i => #[(Choice.share, (widthOf width t).getD 0, tag4Bytes Ixon.Expr.FLAG_SHARE i)]
        | none => #[]).push (Choice.cut p.spineLen[t]!,
          tag4Size p.spineLen[t]! + ev.sides[t]! +
            ev.cost[p.tail[t]!]!,
          tag4Bytes (p.dag.node t).head.flag p.spineLen[t]!)) (Nat.le_refl _) (by omega)
        (by omega) hb
    rw [← hs] at hL
    have h' := hL ▸ h
    simp only [List.mem_append, Array.toList_push, List.mem_singleton] at h'
    rcases h' with (h' | h') | h'
    · obtain ⟨h1, h2, h3⟩ := hbase _ h'
      exact Or.inl ⟨h1, h2, h3⟩
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, _⟩ := h'
      refine Or.inr (Or.inr ⟨_, rfl, hf, hl1, Nat.le_refl _, Or.inl ⟨rfl, ?_⟩⟩)
      rw [hs, hcost]
      rfl
    · have hm : (ch, c) ∈ gCutsFromC p wd avail (gCost p wd avail) t 1 := by
        rw [← hLc]
        exact List.mem_map.mpr ⟨_, h', rfl⟩
      obtain ⟨k, hk1, hkl, hav, rfl, rfl⟩ := mem_gCutsFromC hm
      exact Or.inr (Or.inr ⟨k, rfl, hf, hk1, by omega, Or.inr ⟨hkl, hav, rfl⟩⟩)

/-- Every expression `build` emits has the length of the model: its entry
cost for an entry body, its standalone cost otherwise (Shares priced by `wd`),
and it continues no telescope of another family. -/
theorem PrepWF.gBuild_size {p : Prep} (hp : PrepWF p)
    {wd : Nat → Nat} {avail : Nat → Bool} (ev : DictEval) (hev : GEvalOK p wd avail ev) (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u)
    (sc : Nat → Nat)
    (hsc : ∀ (u i : Nat), index[u]?.getD none = some i → i < UInt64.size ∧ sc i = wd u) :
    ∀ (fuel : Nat) (entry : Bool) (t : Nat) (e : Ixon.Expr), t < p.dag.size →
      p.build ev index width entry fuel t = .ok e →
      (sizeInfoWith sc e).full = (if entry then gInl p wd avail t else gCost p wd avail t) ∧
        OnlyCont p.family[t]! (sizeInfoWith sc e) := by
  have hcost : ∀ c, ev.cost[c]! = gCost p wd avail c :=
    hev.cost
  have hshare : ∀ (u i : Nat), index[u]?.getD none = some i →
      (sizeInfoWith sc (.share i.toUInt64)).full = wd u := by
    intro u i hi
    obtain ⟨hlt, hw⟩ := hsc u i hi
    simp only [sizeInfoWith, SizeInfo.plain, toNat_toUInt64_of_lt hlt, hw]
  intro fuel
  induction fuel with
  | zero => intro entry t e _ h; simp [Prep.build] at h
  | succ fuel ih =>
    intro entry t e ht h
    simp only [Prep.build] at h
    split at h
    · rename_i choice c hpick
      split at h
      · rename_i hcheck
        -- the chosen option and its cost
        obtain ⟨b, hb⟩ := pickOption_mem _ hpick
        have hmem : (choice, c, b) ∈ (p.options ev index width t).toList := by
          split at hb
          · rw [Array.toList_filter] at hb; exact (List.mem_filter.mp hb).1
          · exact hb
        have hc : (if entry then gInl p wd avail t else gCost p wd avail t) = c := by
          cases entry with
          | false =>
            simp only [Bool.false_or, beq_iff_eq] at hcheck
            simp only [Bool.false_eq_true, ite_false]
            rw [← hcost, hcheck]
          | true =>
            simp only [ite_true]
            rw [← hp.gInlineCost_eq ev hev index width hwidth hindex t ht]
            unfold Prep.inlineCost
            simp only [ite_true] at hpick
            rw [hpick]
            rfl
        rw [hc]
        have hopt := hp.gOptions_mem ev hev index width hwidth hindex ht hmem
        split at h
        · -- Share
          obtain ⟨_, rfl, _⟩ | ⟨h1, _⟩ | ⟨j, h1, _⟩ := hopt
          · split at h
            · rename_i i hi
              cases h
              exact ⟨hshare t i hi, share_onlyCont sc _ _⟩
            · cases h
          · cases h1
          · cases h1
        · -- inline node
          obtain ⟨h1, _⟩ | ⟨_, hf, hcv⟩ | ⟨j, h1, _⟩ := hopt
          · cases h1
          · rw [hcv]
            unfold gInl gInlOf
            rw [ite_eq_left hf]
            have har := hp.dag.arity t ht
            rw [← dag_node_eq ht] at har
            cases hh : (p.dag.node t).head <;> simp only [hh] at h har
            case prj ti f =>
              obtain ⟨v, hv, hpure⟩ := bind_eq_ok h
              cases hpure
              have hc0 : (p.dag.node t).child 0 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              obtain ⟨hvs, _⟩ := ih false _ v (by omega) hv
              simp only [Bool.false_eq_true, ite_false] at hvs
              refine ⟨?_, fun F' _ => by cases F' <;> rfl⟩
              rw [← Array.foldl_toList, children_toList (m := 1) (by simpa [Head.arity] using har)]
              simp [sizeInfoWith, SizeInfo.plain, hvs, Head.ownBytes] <;> omega
            case letE lc =>
              obtain ⟨ty, hty, h2⟩ := bind_eq_ok h
              obtain ⟨v, hv, h3⟩ := bind_eq_ok h2
              obtain ⟨bd, hbd, hpure⟩ := bind_eq_ok h3
              cases hpure
              have hc0 : (p.dag.node t).child 0 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              have hc1 : (p.dag.node t).child 1 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              have hc2 : (p.dag.node t).child 2 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              obtain ⟨hs0, _⟩ := ih false _ ty (by omega) hty
              obtain ⟨hs1, _⟩ := ih false _ v (by omega) hv
              obtain ⟨hs2, _⟩ := ih false _ bd (by omega) hbd
              simp only [Bool.false_eq_true, ite_false] at hs0 hs1 hs2
              refine ⟨?_, fun F' _ => by cases F' <;> rfl⟩
              rw [← Array.foldl_toList, children_toList (m := 3) (by simpa [Head.arity] using har)]
              simp [sizeInfoWith, SizeInfo.plain, hs0, hs1, hs2, Head.ownBytes,
                List.range_succ] <;> omega
            all_goals first
              | (cases h; done)
              | (cases h
                 simp only [Node.toExpr, hh]
                 refine ⟨?_, fun F' _ => by cases F' <;> rfl⟩
                 rw [← Array.foldl_toList,
                   children_toList (m := 0) (by simpa [Head.arity] using har)]
                 simp [sizeInfoWith, SizeInfo.plain, Head.ownBytes])
          · cases h1
        · -- telescope cut
          rename_i j
          obtain ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨j', hj', hf, hj1, hjl, hcase⟩ := hopt
          · cases h1
          · cases h1
          cases hj'
          obtain ⟨_, hk, hend, htl, htf⟩ := hp.spine t ht hf
          have hfam : ∀ n ∈ (List.range j).map (fun k => p.dag.node (spineAt p t k)),
              n.head.family = p.family[t]! := by
            intro n hn
            obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hn
            rw [List.mem_range] at hk'
            obtain ⟨hle, hkf, _, _⟩ := hk k (by omega)
            rw [← hp.family _ (by omega), hkf]
          have hsz : ∀ n ∈ (List.range j).map (fun k => p.dag.node (spineAt p t k)), ∀ e',
              p.build ev index width false fuel n.sideChild = .ok e' →
              (sizeInfoWith sc e').full = gCost p wd avail n.sideChild := by
            intro n hn e' he'
            obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hn
            rw [List.mem_range] at hk'
            obtain ⟨hle, hkf, _, _⟩ := hk k (by omega)
            have hs := hp.sideChild_lt (t := spineAt p t k) (by omega) (by rw [hkf]; exact hf)
            have := (ih false _ e' (by omega) he').1
            simpa using this
          have hsum : (((List.range j).map (fun k => p.dag.node (spineAt p t k))).map
              (fun n => n.sideExtra + gCost p wd avail n.sideChild)).sum =
              prefixSides p (gCost p wd avail) t j := by
            rw [prefixSides_eq_sum, List.map_map]
            rfl
          have hlen : ((List.range j).map (fun k => p.dag.node (spineAt p t k))).length = j := by
            simp
          have hne : (List.range j).map (fun k => p.dag.node (spineAt p t k)) ≠ [] := by
            intro h0
            have := congrArg List.length h0
            simp at this
            omega
          rw [spineWalk_eq] at h
          split at h
          · cases h
          split at h
          · -- the prefix ends in a Share
            rename_i _ hjlt
            split at h
            · rename_i i hi
              obtain ⟨tl, htl', hfold⟩ := bind_eq_ok h
              cases htl'
              obtain ⟨_, hfull, honly⟩ := spineFold_size sc p.family[t]! _
                (fun n => gCost p wd avail n.sideChild) _ _ _ hfam hsz
                (by cases p.family[t]! <;> rfl) hfold
              refine ⟨?_, honly hne⟩
              rw [hfull hne, hlen, hsum, hshare _ i hi]
              rcases hcase with ⟨hjl', _⟩ | ⟨_, _, hcv⟩
              · omega
              · rw [hcv]
                unfold gCutCost
                simp only at *
                omega
            · obtain ⟨tl, htl', _⟩ := bind_eq_ok h
              cases htl'
          · -- the full spine ends in the natural tail
            rename_i _ hjlt
            have hjeq : j = p.spineLen[t]! := by omega
            obtain ⟨tl, htl', hfold⟩ := bind_eq_ok h
            simp only at htl'
            rw [hjeq, hend] at htl'
            obtain ⟨htfull, htonly⟩ := ih false _ tl (by omega) htl'
            simp only [Bool.false_eq_true, ite_false] at htfull
            obtain ⟨_, hfull, honly⟩ := spineFold_size sc p.family[t]! _
              (fun n => gCost p wd avail n.sideChild) _ _ _ hfam hsz
              (htonly _ (Ne.symm htf)) hfold
            refine ⟨?_, honly hne⟩
            rw [hfull hne, hlen, hsum, htfull]
            rcases hcase with ⟨_, hcv⟩ | ⟨hjl', _, _⟩
            · rw [hcv, hjeq]
              unfold naturalCost
              omega
            · omega
      · cases h
    · cases h

/-! ## Writings at per-term widths -/

mutual
/-- Length of a writing (the Share of `x` priced `wd x`). -/
def WTree.gcost (p : Prep) (wd : Nat → Nat) : WTree → Nat
  | .share x => wd x
  | .node x kids => (p.dag.node x).head.ownBytes + WTree.gcosts p wd kids
  | .tele x j sides tail =>
    tag4Size j + j * (p.dag.node x).sideExtra + WTree.gcosts p wd sides + WTree.gcost p wd tail
/-- Total length of a list of writings. -/
def WTree.gcosts (p : Prep) (wd : Nat → Nat) : List WTree → Nat
  | [] => 0
  | k :: ks => WTree.gcost p wd k + WTree.gcosts p wd ks
end

theorem WTree.gcosts_eq (p : Prep) (wd : Nat → Nat) (l : List WTree) :
    WTree.gcosts p wd l = (l.map (WTree.gcost p wd)).sum := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [WTree.gcosts, ih]

theorem gCostOf_le_inl (p : Prep) (wd : Nat → Nat) (S : Nat → Bool) (f : Nat → Nat) (x : Nat) :
    gCostOf p wd S f x ≤ gInlOf p wd S f x := by
  unfold gCostOf; split <;> omega

theorem PrepWF.gInl_node {p : Prep} (hp : PrepWF p) (wd : Nat → Nat) (S : Nat → Bool) (f : Nat → Nat)
    {x : Nat} (hx : x < p.dag.size) (hf : p.family[x]! = .none) :
    gInlOf p wd S f x = (p.dag.node x).head.ownBytes +
      ((List.range (p.dag.node x).head.arity).map fun i => f ((p.dag.node x).child i)).sum := by
  unfold gInlOf
  rw [ite_eq_left hf, ← Array.foldl_toList, foldl_add_eq_sum]
  have har := hp.dag.arity x hx
  rw [← dag_node_eq hx] at har
  rw [children_toList har, List.map_map]
  rfl

theorem gInl_tele {p : Prep} (wd : Nat → Nat) (S : Nat → Bool) (f : Nat → Nat)
    {x : Nat} (hf : p.family[x]! ≠ .none) :
    gInlOf p wd S f x = (gCutCosts p wd S f x).foldl min (naturalCost p f x) := by
  unfold gInlOf
  rw [ite_eq_right hf]

theorem gCut_mem_cutCosts (p : Prep) (wd : Nat → Nat) (S : Nat → Bool) (f : Nat → Nat) {x j : Nat}
    (hj1 : 1 ≤ j) (hj : j < p.spineLen[x]!) (hS : S (spineAt p x j) = true) :
    gCutCost p wd f x j ∈ gCutCosts p wd S f x := by
  rw [gCutCosts_eq]
  unfold gCutsFrom
  apply List.mem_filterMap.mpr
  refine ⟨j, List.mem_range'_1.mpr ⟨hj1, by omega⟩, ?_⟩
  rw [ite_eq_left hS]

theorem gcosts_eq_range (p : Prep) (wd : Nat → Nat) (l : List WTree) :
    WTree.gcosts p wd l = ((List.range l.length).map fun k => (l[k]?.getD default).gcost p wd).sum := by
  rw [WTree.gcosts_eq]
  congr 1
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getElem?_eq_getElem (by simpa using h1)]
  rfl

/-- **Lower bound.** Every writing of `x` is at least `C_S(x)` long, and
every inline writing at least `inl_S(x)`. -/
theorem PrepWF.gValid_cost {p : Prep} (hp : PrepWF p) (wd : Nat → Nat) (S : Nat → Bool) :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → x < p.dag.size →
      gCost p wd S x ≤ T.gcost p wd ∧ (T.isShare = false → gInl p wd S x ≤ T.gcost p wd) := by
  intro x T h
  induction h with
  | share hS =>
    intro hx
    refine ⟨?_, fun h => by simp [WTree.isShare] at h⟩
    rw [hp.gCost_eq wd S _ hx]
    unfold gCostOf
    simp only [hS, ite_true, WTree.gcost]
    omega
  | @node x kids hf hlen _ ih =>
    intro hx
    have hinl : gInl p wd S x ≤ (WTree.node x kids).gcost p wd := by
      unfold gInl
      rw [hp.gInl_node wd S _ hx hf]
      simp only [WTree.gcost]
      rw [gcosts_eq_range, hlen]
      have : ∀ i ∈ List.range (p.dag.node x).head.arity,
          gCost p wd S ((p.dag.node x).child i) ≤ (kids[i]?.getD default).gcost p wd := by
        intro i hi
        rw [List.mem_range] at hi
        have hc := hp.dag.childAt_lt hx hi
        rw [show kids[i]?.getD default = kids[i]'(by omega) by simp [hlen ▸ hi]]
        exact (ih i (by omega) (by omega)).1
      have := sum_le_sum_of_le _ this
      omega
    refine ⟨?_, fun _ => hinl⟩
    rw [hp.gCost_eq wd S _ hx]
    exact Nat.le_trans (gCostOf_le_inl _ _ _ _ _) hinl
  | @teleCut x j sides hf hj1 hj hlen _ hS ih =>
    intro hx
    have hinl : gInl p wd S x ≤ (WTree.tele x j sides (.share (spineAt p x j))).gcost p wd := by
      unfold gInl
      rw [gInl_tele wd S _ hf]
      refine Nat.le_trans (foldl_min_le _ _ _ (List.mem_cons_of_mem _
        (gCut_mem_cutCosts p wd S _ hj1 hj hS))) ?_
      unfold gCutCost
      rw [hp.prefixSides_eq _ hx hf (by omega)]
      simp only [WTree.gcost]
      rw [gcosts_eq_range, hlen]
      have : ∀ k ∈ List.range j, gCost p wd S (sideAt p x k) ≤ (sides[k]?.getD default).gcost p wd := by
        intro k hk
        rw [List.mem_range] at hk
        rw [show sides[k]?.getD default = sides[k]'(by omega) by simp [hlen ▸ hk]]
        exact (ih k (by omega) (by have := hp.sideAt_lt hx hf (k := k) (by omega); omega)).1
      have := sum_le_sum_of_le _ this
      omega
    refine ⟨?_, fun _ => hinl⟩
    rw [hp.gCost_eq wd S _ hx]
    exact Nat.le_trans (gCostOf_le_inl _ _ _ _ _) hinl
  | @teleFull x sides tail hf hlen _ _ ih iht =>
    intro hx
    obtain ⟨_, _, _, htl, _⟩ := hp.spine x hx hf
    have hinl : gInl p wd S x ≤ (WTree.tele x p.spineLen[x]! sides tail).gcost p wd := by
      unfold gInl
      rw [gInl_tele wd S _ hf]
      refine Nat.le_trans (foldl_min_le _ _ _ List.mem_cons_self) ?_
      unfold naturalCost
      rw [hp.prefixSides_eq _ hx hf (Nat.le_refl _)]
      simp only [WTree.gcost]
      rw [gcosts_eq_range, hlen]
      have : ∀ k ∈ List.range p.spineLen[x]!,
          gCost p wd S (sideAt p x k) ≤ (sides[k]?.getD default).gcost p wd := by
        intro k hk
        rw [List.mem_range] at hk
        rw [show sides[k]?.getD default = sides[k]'(by omega) by simp [hlen ▸ hk]]
        exact (ih k (by omega) (by have := hp.sideAt_lt hx hf (k := k) (by omega); omega)).1
      have := sum_le_sum_of_le _ this
      have ht := (iht (by omega)).1
      omega
    refine ⟨?_, fun _ => hinl⟩
    rw [hp.gCost_eq wd S _ hx]
    exact Nat.le_trans (gCostOf_le_inl _ _ _ _ _) hinl

theorem mem_gCutCosts {p : Prep} {wd : Nat → Nat} {S : Nat → Bool} {f : Nat → Nat} {x c : Nat}
    (h : c ∈ gCutCosts p wd S f x) :
    ∃ j, 1 ≤ j ∧ j < p.spineLen[x]! ∧ S (spineAt p x j) = true ∧ c = gCutCost p wd f x j := by
  rw [gCutCosts_eq] at h
  unfold gCutsFrom at h
  obtain ⟨j, hj, hjv⟩ := List.mem_filterMap.mp h
  rw [List.mem_range'_1] at hj
  split at hjv
  · rename_i hS
    simp only [Option.some.injEq] at hjv
    exact ⟨j, hj.1, by omega, hS, hjv.symm⟩
  · cases hjv

theorem gcosts_map_range (p : Prep) (wd : Nat → Nat) (g : Nat → WTree) (n : Nat) :
    WTree.gcosts p wd ((List.range n).map g) = ((List.range n).map fun k => (g k).gcost p wd).sum := by
  rw [WTree.gcosts_eq, List.map_map]
  rfl

/-- **Attainment.** Some writing of `x` has length `C_S(x)`, and some inline
writing has length `inl_S(x)`. -/
theorem PrepWF.gExists_opt {p : Prep} (hp : PrepWF p) (wd : Nat → Nat) (S : Nat → Bool) :
    ∀ x, x < p.dag.size →
      (∃ T, Valid p S x T ∧ T.gcost p wd = gCost p wd S x) ∧
        ∃ T, Valid p S x T ∧ T.isShare = false ∧ T.gcost p wd = gInl p wd S x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx
    classical
    let g : Nat → WTree := fun c =>
      if h : c < x ∧ c < p.dag.size then Classical.choose (ih c h.1 h.2).1 else default
    have hg : ∀ c, c < x → Valid p S c (g c) ∧ (g c).gcost p wd = gCost p wd S c := by
      intro c hc
      have hcn : c < p.dag.size := by omega
      simp only [g, dite_eq_left (And.intro hc hcn)]
      exact Classical.choose_spec (ih c hc hcn).1
    -- an optimal inline writing
    have hinl : ∃ T, Valid p S x T ∧ T.isShare = false ∧ T.gcost p wd = gInl p wd S x := by
      by_cases hf : p.family[x]! = .none
      · let ar := (p.dag.node x).head.arity
        refine ⟨.node x ((List.range ar).map fun i => g ((p.dag.node x).child i)), ?_, rfl, ?_⟩
        · refine Valid.node hf (by simp [ar]) fun i hi => ?_
          simp only [List.length_map, List.length_range] at hi
          simp only [List.getElem_map, List.getElem_range]
          exact (hg _ (hp.dag.childAt_lt hx hi)).1
        · simp only [WTree.gcost, gcosts_map_range]
          unfold gInl
          rw [hp.gInl_node wd S _ hx hf]
          simp only [ar]
          congr 2
          apply List.map_congr_left
          intro i hi
          rw [List.mem_range] at hi
          exact (hg _ (hp.dag.childAt_lt hx hi)).2
      · obtain ⟨hl1, _, hend, htl, _⟩ := hp.spine x hx hf
        have hmin := foldl_min_mem (gCutCosts p wd S (gCost p wd S) x)
          (naturalCost p (gCost p wd S) x)
        rw [← gInl_tele wd S _ hf] at hmin
        have hsides : ∀ j, j ≤ p.spineLen[x]! →
            WTree.gcosts p wd ((List.range j).map fun k => g (sideAt p x k)) =
              ((List.range j).map fun k => gCost p wd S (sideAt p x k)).sum := by
          intro j hj
          rw [gcosts_map_range]
          congr 1
          apply List.map_congr_left
          intro k hk
          rw [List.mem_range] at hk
          exact (hg _ (hp.sideAt_lt hx hf (by omega))).2
        have hsv : ∀ j, j ≤ p.spineLen[x]! → ∀ (k : Nat)
            (h : k < ((List.range j).map fun k => g (sideAt p x k)).length),
            Valid p S (sideAt p x k) ((List.range j).map fun k => g (sideAt p x k))[k] := by
          intro j hj k hk
          simp only [List.length_map, List.length_range] at hk
          simp only [List.getElem_map, List.getElem_range]
          exact (hg _ (hp.sideAt_lt hx hf (by omega))).1
        rcases List.mem_cons.mp hmin with hnat | hcut
        · refine ⟨.tele x p.spineLen[x]! ((List.range p.spineLen[x]!).map fun k => g (sideAt p x k))
            (g p.tail[x]!), Valid.teleFull hf (by simp) (hsv _ (Nat.le_refl _))
              (hg _ htl).1, rfl, ?_⟩
          simp only [WTree.gcost]
          rw [hsides _ (Nat.le_refl _), (hg _ htl).2]
          unfold gInl
          rw [hnat]
          unfold naturalCost
          rw [hp.prefixSides_eq _ hx hf (Nat.le_refl _)]
          omega
        · obtain ⟨j, hj1, hjl, hS, hc⟩ := mem_gCutCosts hcut
          refine ⟨.tele x j ((List.range j).map fun k => g (sideAt p x k))
            (.share (spineAt p x j)), Valid.teleCut hf hj1 hjl (by simp) (hsv _ (by omega)) hS,
            rfl, ?_⟩
          simp only [WTree.gcost]
          rw [hsides _ (by omega)]
          unfold gInl
          rw [hc]
          unfold gCutCost
          rw [hp.prefixSides_eq _ hx hf (by omega)]
          omega
    refine ⟨?_, hinl⟩
    obtain ⟨T, hT, hTs, hTc⟩ := hinl
    rw [hp.gCost_eq wd S x hx]
    unfold gCostOf
    by_cases hS : S x = true
    · by_cases hle : wd x ≤ gInlOf p wd S (gCost p wd S) x
      · refine ⟨.share x, Valid.share hS, ?_⟩
        simp only [hS, ite_true, WTree.gcost]
        omega
      · refine ⟨T, hT, ?_⟩
        simp only [hS, ite_true]
        unfold gInl at hTc
        omega
    · refine ⟨T, hT, ?_⟩
      simp only [hS, Bool.false_eq_true, ite_false]
      exact hTc

/-! ## Locality and the incremental re-evaluation -/

open Ix.Compile.Verify.SharingExact (Desc Desc.trans) in
/-- The spine nodes of `y` up to its tail are below it. -/
theorem desc_spineAt {dag : Dag} (hwf : DagWF dag) {y : Nat} (hy : y < dag.size)
    (hf : (Prep.ofDag dag).family[y]! ≠ .none) :
    ∀ k, k ≤ (Prep.ofDag dag).spineLen[y]! → Desc dag y (spineAt (Prep.ofDag dag) y k) := by
  have hp := prepWF_ofDag hwf
  obtain ⟨_, hk, _, _, _⟩ := hp.spine y hy hf
  intro k
  induction k with
  | zero => intro _; exact .refl _
  | succ k ih =>
    intro hkl
    have hd := ih (by omega)
    obtain ⟨hle, hkf, _, _⟩ := hk k (by omega)
    have hks : spineAt (Prep.ofDag dag) y k < dag.size := by
      have : spineAt (Prep.ofDag dag) y k ≤ y := hle
      omega
    have hfk : (Prep.ofDag dag).family[spineAt (Prep.ofDag dag) y k]! ≠ .none := by
      rw [hkf]; exact hf
    obtain ⟨m, hm, he⟩ := hp.snext_edge hks hfk
    rw [← snext_spineAt, ← he]
    exact desc_snoc hd (by rw [hwf.children_size hks]; exact hm)

open Ix.Compile.Verify.SharingExact (Desc Desc.trans) in
theorem desc_sideAt {dag : Dag} (hwf : DagWF dag) {y : Nat} (hy : y < dag.size)
    (hf : (Prep.ofDag dag).family[y]! ≠ .none) {k : Nat} (hk : k < (Prep.ofDag dag).spineLen[y]!) :
    Desc dag y (sideAt (Prep.ofDag dag) y k) := by
  have hp := prepWF_ofDag hwf
  obtain ⟨_, hk', _, _, _⟩ := hp.spine y hy hf
  obtain ⟨hle, hkf, _, _⟩ := hk' k hk
  have hks : spineAt (Prep.ofDag dag) y k < dag.size := by
    have : spineAt (Prep.ofDag dag) y k ≤ y := hle
    omega
  have hfk : (Prep.ofDag dag).family[spineAt (Prep.ofDag dag) y k]! ≠ .none := by
    rw [hkf]; exact hf
  obtain ⟨m, hm, he⟩ := hp.side_edge hks hfk
  unfold sideAt
  rw [← he]
  exact desc_snoc (desc_spineAt hwf hy hf k (by omega))
    (by rw [hwf.children_size hks]; exact hm)

open Ix.Compile.Verify.SharingExact (Desc Desc.trans) in
/-- **Locality.** The model cost of `y` depends only on the dictionary on the
terms at or below `y`. -/
theorem gCost_local {dag : Dag} (hwf : DagWF dag) {wdA wdB : Nat → Nat} {A B : Nat → Bool} :
    ∀ y, y < dag.size → (∀ v, Desc dag y v → A v = B v ∧ wdA v = wdB v) →
      gCost (Prep.ofDag dag) wdA A y = gCost (Prep.ofDag dag) wdB B y := by
  have hp := prepWF_ofDag hwf
  intro y
  induction y using Nat.strongRecOn with
  | _ y ih =>
    intro hy hag
    have hsub : ∀ c, c < y → Desc dag y c →
        gCost (Prep.ofDag dag) wdA A c = gCost (Prep.ofDag dag) wdB B c :=
      fun c hc hd => ih c hc (by omega) fun v hv => hag v (hd.trans hv)
    rw [hp.gCost_eq wdA A y hy, hp.gCost_eq wdB B y hy]
    obtain ⟨hAy, hwy⟩ := hag y (.refl _)
    have hinl : gInlOf (Prep.ofDag dag) wdA A (gCost (Prep.ofDag dag) wdA A) y =
        gInlOf (Prep.ofDag dag) wdB B (gCost (Prep.ofDag dag) wdB B) y := by
      unfold gInlOf
      split
      · apply foldl_add_congr
        intro c hc
        have hc' : c ∈ (dag.node y).children := hc
        have hlt := hwf.child_lt hy hc'
        obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hc'
        have hd : Desc dag ((dag.node y).child k) (dag.node y).children[k] := by
          rw [child_eq_getElem _ k hk]; exact .refl _
        exact hsub _ hlt (.child k hk hd)
      · rename_i hf
        obtain ⟨_, _, hend, htl, _⟩ := hp.spine y hy hf
        have hsides : ∀ j, j ≤ (Prep.ofDag dag).spineLen[y]! →
            prefixSides (Prep.ofDag dag) (gCost (Prep.ofDag dag) wdA A) y j =
              prefixSides (Prep.ofDag dag) (gCost (Prep.ofDag dag) wdB B) y j := by
          intro j hj
          apply prefixSides_local
          intro i hi
          exact hsub _ (hp.sideAt_lt hy hf (by omega)) (desc_sideAt hwf hy hf (by omega))
        have hcuts : gCutCosts (Prep.ofDag dag) wdA A (gCost (Prep.ofDag dag) wdA A) y =
            gCutCosts (Prep.ofDag dag) wdB B (gCost (Prep.ofDag dag) wdB B) y := by
          unfold gCutCosts gCutsFrom
          apply filterMap_congr'
          intro j hj
          rw [List.mem_range'_1] at hj
          obtain ⟨hA, hw⟩ := hag _ (desc_spineAt hwf hy hf j (by omega))
          unfold gCutCost
          rw [hA, hw, hsides j (by omega)]
        rw [hcuts]
        unfold naturalCost
        rw [hsides _ (Nat.le_refl _), hsub _ htl (by
          rw [← hend]; exact desc_spineAt hwf hy hf _ (Nat.le_refl _))]
    unfold gCostOf
    rw [hinl, hAy, hwy]

open Ix.Compile.Verify.SharingExact (Desc Desc.trans) in
/-- The evaluation rows of `t` carry over between dictionaries that agree
at and below `t`. -/
theorem gEvalRow_local {dag : Dag} (hwf : DagWF dag) {wdA wdB : Nat → Nat} {A B : Nat → Bool}
    {st : DictEval} {t : Nat} (ht : t < dag.size)
    (hag : ∀ v, Desc dag t v → A v = B v ∧ wdA v = wdB v)
    (h : GEvalRow (Prep.ofDag dag) wdA A st t) : GEvalRow (Prep.ofDag dag) wdB B st t := by
  have hp := prepWF_ofDag hwf
  obtain ⟨hc, hs⟩ := h
  refine ⟨by rw [hc]; exact gCost_local hwf t ht hag, fun hf => ?_⟩
  obtain ⟨hsd, hfa⟩ := hs hf
  refine ⟨?_, ?_⟩
  · rw [hsd]
    apply prefixSides_local
    intro i hi
    have hlt := hp.sideAt_lt ht hf hi
    have hd := desc_sideAt hwf ht hf hi
    exact gCost_local hwf _ (by omega) fun v hv => hag v (hd.trans hv)
  · have hagk : ∀ k, k < (Prep.ofDag dag).spineLen[t]! →
        A (spineAt (Prep.ofDag dag) t k) = B (spineAt (Prep.ofDag dag) t k) :=
      fun k hk => (hag _ (desc_spineAt hwf ht hf k (by omega))).1
    cases hb : st.below[t]! with
    | none =>
      rw [hb] at hfa
      intro k hk1 hk2
      rw [← hagk k hk2]; exact hfa k hk1 hk2
    | some u =>
      rw [hb] at hfa
      obtain ⟨k, hk1, hk2, hu, hau, hnone⟩ := hfa
      refine ⟨k, hk1, hk2, hu, by rw [hu, ← hagk k hk2, ← hu]; exact hau, fun k' h1 h2 => ?_⟩
      rw [← hagk k' (by omega)]; exact hnone k' h1 h2

open Ix.Compile.Verify.SharingExact (Desc) in
theorem desc_inv {dag : Dag} {a b : Nat} (h : Desc dag a b) :
    a = b ∨ ∃ k, ∃ _ : k < (dag.node a).children.size, Desc dag ((dag.node a).child k) b := by
  cases h with
  | refl => exact Or.inl rfl
  | child k hk h => exact Or.inr ⟨k, hk, h⟩

open Ix.Compile.Verify.SharingExact (Desc Desc.trans) in
/-- The marks of `ancestorMarks`: `u` is marked iff `t` is at or below it. -/
theorem ancestorMarks_iff {dag : Dag} (hwf : DagWF dag) {t : Nat} (ht : t < dag.size) :
    ∀ u, u < dag.size → ((ancestorMarks dag t)[u]! = true ↔ Desc dag u t) := by
  let f := fun (acc : Array Bool) u =>
    acc.set! u (u == t || (dag.node u).children.any (acc[·]!))
  have hinv : ∀ m, m ≤ dag.size - t →
      let acc := (List.range' t m).foldl f (Array.replicate dag.size false)
      acc.size = dag.size ∧ (∀ u, u < dag.size → (u < t ∨ t + m ≤ u) → acc[u]! = false) ∧
        ∀ u, t ≤ u → u < t + m → (acc[u]! = true ↔ Desc dag u t) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨by simp, fun u hu _ => ?_, fun u h1 h2 => absurd h2 (by omega)⟩
      simp [hu]
    | succ m ih =>
      intro hm
      obtain ⟨hs, hz, hrows⟩ := ih (by omega)
      simp only at hs hz hrows ⊢
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize hacc : (List.range' t m).foldl f (Array.replicate dag.size false) = acc
        at hs hz hrows
      have hkeep : ∀ u, u ≠ t + m → (f acc (t + m))[u]! = acc[u]! :=
        fun u hu => setBang_getElem!_ne _ _ hu
      refine ⟨by simp [f, hs], fun u hu hr => ?_, fun u h1 h2 => ?_⟩
      · rw [hkeep u (by omega)]
        exact hz u hu (by omega)
      · by_cases hum : u = t + m
        · subst hum
          simp only [f]
          rw [setBang_getElem!_self _ _ (by omega)]
          rw [Bool.or_eq_true, beq_iff_eq, Array.any_eq_true]
          constructor
          · rintro (h | ⟨k, hk, hc⟩)
            · rw [h]; exact .refl _
            · have hlt : (dag.node (t + m)).children[k] < t + m :=
                hwf.child_lt (by omega) (Array.getElem_mem _)
              refine .child k hk ?_
              rw [child_eq_getElem _ k hk]
              by_cases hct : (dag.node (t + m)).children[k] < t
              · rw [hz _ (by omega) (Or.inl hct)] at hc; cases hc
              · exact (hrows _ (by omega) hlt).mp hc
          · intro hd
            rcases desc_inv hd with heq | ⟨k, hk, hd⟩
            · exact Or.inl (by omega)
            · right
              refine ⟨k, hk, ?_⟩
              rw [child_eq_getElem _ k hk] at hd
              have hlt : (dag.node (t + m)).children[k] < t + m :=
                hwf.child_lt (by omega) (Array.getElem_mem _)
              have hge : t ≤ (dag.node (t + m)).children[k] :=
                Desc.le_of_wf hwf hd (by omega)
              exact (hrows _ hge hlt).mpr hd
        · rw [hkeep u hum]
          exact hrows u h1 (by omega)
  intro u hu
  obtain ⟨_, hz, hrows⟩ := hinv (dag.size - t) (Nat.le_refl _)
  unfold ancestorMarks
  rw [foldRange_eq]
  by_cases hut : t ≤ u
  · exact hrows u hut (by omega)
  · rw [hz u hu (Or.inl (by omega))]
    constructor
    · intro h; cases h
    · intro hd; have := Desc.le_of_wf hwf hd hu; omega

theorem gEvalRow_of_agree {p : Prep} {wd : Nat → Nat} {A : Nat → Bool} {st st' : DictEval}
    {t : Nat} (h1 : st'.cost[t]! = st.cost[t]!) (h2 : st'.sides[t]! = st.sides[t]!)
    (h3 : st'.below[t]! = st.below[t]!) (h : GEvalRow p wd A st t) : GEvalRow p wd A st' t := by
  obtain ⟨hc, hs⟩ := h
  exact ⟨by rw [h1, hc], fun hf => by rw [h2, h3]; exact hs hf⟩

open Ix.Compile.Verify.SharingExact (Desc Desc.trans) in
/-- **Incremental re-evaluation.** If `ev` gives the model rows of a
dictionary and the new dictionary (`width`, model `A'`, `wd'`) differs from
it only at `t`, then `Prep.evalUp ev width t` gives the new model rows. -/
theorem evalUp_ok {dag : Dag} (hwf : DagWF dag) {wd wd' : Nat → Nat} {A A' : Nat → Bool}
    {ev : DictEval} (hev : GEvalOK (Prep.ofDag dag) wd A ev) {t : Nat} (ht : t < dag.size)
    (hdiff : ∀ v, v ≠ t → A' v = A v ∧ wd' v = wd v) (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if A' u then some (wd' u) else none) :
    GEvalOK (Prep.ofDag dag) wd' A' ((Prep.ofDag dag).evalUp ev width t) := by
  have hp := prepWF_ofDag hwf
  let p := Prep.ofDag dag
  have hag : ∀ u, u < dag.size → ¬ Desc dag u t → ∀ v, Desc dag u v → A v = A' v ∧ wd v = wd' v := by
    intro u hu hnd v hv
    have hvt : v ≠ t := fun h => hnd (h ▸ hv)
    exact ⟨(hdiff v hvt).1.symm, (hdiff v hvt).2.symm⟩
  let marks := ancestorMarks dag t
  let step := evalStep p.dag p.family p.spineLen p.tail width marks
  have hinv : ∀ m, m ≤ dag.size - t →
      let st := (List.range' t m).foldl step { ev with work := 0 }
      (st.cost.size = dag.size ∧ st.sides.size = dag.size ∧ st.below.size = dag.size) ∧
        (∀ u, u < t + m → GEvalRow p wd' A' st u) ∧
        ∀ u, t + m ≤ u → st.cost[u]! = ev.cost[u]! ∧ st.sides[u]! = ev.sides[u]! ∧
          st.below[u]! = ev.below[u]! := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨hev.1, fun u hu => ?_, fun u _ => ⟨rfl, rfl, rfl⟩⟩
      have hud : u < dag.size := by omega
      exact gEvalRow_local hwf hud (hag u hud fun hd => by
        have := Desc.le_of_wf hwf hd hud; omega) (hev.2 u hud)
    | succ m ih =>
      intro hm
      obtain ⟨hs, hrows, hrest⟩ := ih (by omega)
      simp only at hs hrows hrest ⊢
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize hst : (List.range' t m).foldl step { ev with work := 0 } = st
        at hs hrows hrest
      have hkeep : ∀ u, u ≠ t + m → (step st (t + m)).cost[u]! = st.cost[u]! ∧
          (step st (t + m)).sides[u]! = st.sides[u]! ∧
          (step st (t + m)).below[u]! = st.below[u]! :=
        fun u hu => evalStep_keep _ _ _ _ width marks st hu
      have htm : t + m < dag.size := by omega
      by_cases hmark : marks[t + m]! = true
      · obtain ⟨hs', hrows'⟩ := hp.gEvalStep_spec width hwidth marks st (t + m) htm hmark hs
          hrows
        refine ⟨hs', fun u hu => hrows' u (by omega), fun u hu => ?_⟩
        obtain ⟨k1, k2, k3⟩ := hkeep u (by omega)
        obtain ⟨r1, r2, r3⟩ := hrest u (by omega)
        exact ⟨k1.trans r1, k2.trans r2, k3.trans r3⟩
      · have hid : step st (t + m) = st := by
          simp only [step, evalStep]
          rw [ite_eq_right hmark]
        rw [hid]
        refine ⟨hs, fun u hu => ?_, fun u hu => hrest u (by omega)⟩
        by_cases hum : u < t + m
        · exact hrows u hum
        · have hu' : u = t + m := by omega
          subst hu'
          have hnd : ¬ Desc dag (t + m) t := fun hd =>
            hmark ((ancestorMarks_iff hwf ht (t + m) htm).mpr hd)
          obtain ⟨r1, r2, r3⟩ := hrest (t + m) (Nat.le_refl _)
          refine gEvalRow_local hwf htm (hag _ htm hnd) ?_
          exact gEvalRow_of_agree r1 r2 r3 (hev.2 _ htm)
  obtain ⟨hs, hrows, _⟩ := hinv (dag.size - t) (Nat.le_refl _)
  have hn : (Prep.ofDag dag).dag.size = dag.size := rfl
  refine ⟨?_, fun u hu => ?_⟩
  · unfold Prep.evalUp
    rw [foldRange_eq]
    exact hs
  · unfold Prep.evalUp
    rw [foldRange_eq]
    exact hrows u (by rw [hn] at hu; omega)

/-! ## Locality of options and builds, and the work of an evaluation

Used by the one-pass phase 3 (`materializeTableOnePass_eq`): `build_congr`
(a build depends only on the dictionary at and below its term),
`rows_agree_strict` and `cost_agree` (evaluation rows of two dictionaries
that agree below a term), `evalUp_work` (the work `Prep.evalUp` counts). -/

section OnePass

open Ix.Compile.Verify.SharingExact (Desc Desc.trans)

/-! ## Agreement of evaluations below a term -/

theorem FirstAvail.unique {p : Prep} {avail : Nat → Bool} {t j : Nat} {x y : Option Nat}
    (hx : FirstAvail p avail t j x) (hy : FirstAvail p avail t j y) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some v =>
      obtain ⟨k, h1, h2, rfl, hav, _⟩ := hy
      rw [hx k h1 h2] at hav; cases hav
  | some u =>
    cases y with
    | none =>
      obtain ⟨k, h1, h2, rfl, hav, _⟩ := hx
      rw [hy k h1 h2] at hav; cases hav
    | some v =>
      obtain ⟨k, h1, h2, rfl, hav, hn⟩ := hx
      obtain ⟨k', h1', h2', rfl, hav', hn'⟩ := hy
      rcases Nat.lt_trichotomy k k' with hlt | rfl | hgt
      · rw [hn' k h1 hlt] at hav; cases hav
      · rfl
      · rw [hn k' h1' hgt] at hav'; cases hav'

theorem FirstAvail.congr {p : Prep} {A B : Nat → Bool} {t j : Nat} {x : Option Nat}
    (hag : ∀ k, j ≤ k → k < p.spineLen[t]! → A (spineAt p t k) = B (spineAt p t k))
    (h : FirstAvail p A t j x) : FirstAvail p B t j x := by
  cases x with
  | none => intro k h1 h2; rw [← hag k h1 h2]; exact h k h1 h2
  | some u =>
    obtain ⟨k, h1, h2, hu, hau, hn⟩ := h
    refine ⟨k, h1, h2, hu, by rw [hu, ← hag k h1 h2, ← hu]; exact hau, fun k' h1' h2' => ?_⟩
    rw [← hag k' h1' (by omega)]; exact hn k' h1' h2'

/-- Two evaluations with the model rows of dictionaries that agree strictly
below a telescope term `v` have the same spine sums and descendant links at
`v`. -/
theorem rows_agree_strict {dag : Dag} (hwf : DagWF dag) {wdA wdB : Nat → Nat} {A B : Nat → Bool}
    {ev ev' : DictEval} (hev : GEvalOK (Prep.ofDag dag) wdA A ev)
    (hev' : GEvalOK (Prep.ofDag dag) wdB B ev') {v : Nat} (hv : v < dag.size)
    (hf : (Prep.ofDag dag).family[v]! ≠ .none)
    (hag : ∀ w, Desc dag v w → w ≠ v → A w = B w ∧ wdA w = wdB w) :
    ev.sides[v]! = ev'.sides[v]! ∧ ev.below[v]! = ev'.below[v]! := by
  have hp := prepWF_ofDag hwf
  obtain ⟨hsd, hfa⟩ := (hev.2 v hv).2 hf
  obtain ⟨hsd', hfa'⟩ := (hev'.2 v hv).2 hf
  refine ⟨?_, ?_⟩
  · rw [hsd, hsd']
    apply prefixSides_local
    intro i hi
    have hlt := hp.sideAt_lt hv hf hi
    have hd := desc_sideAt hwf hv hf hi
    exact gCost_local hwf _ (by omega) fun w hw =>
      hag w (hd.trans hw) (by have := Desc.le_of_wf hwf hw (by omega); omega)
  · apply FirstAvail.unique _ hfa'
    refine FirstAvail.congr (fun k h1 h2 => ?_) hfa
    have hlt := hp.spineAt_lt hv hf h1 h2
    exact (hag _ (desc_spineAt hwf hv hf k (by omega)) (by omega)).1

theorem cost_agree {dag : Dag} (hwf : DagWF dag) {wdA wdB : Nat → Nat} {A B : Nat → Bool}
    {ev ev' : DictEval} (hev : GEvalOK (Prep.ofDag dag) wdA A ev)
    (hev' : GEvalOK (Prep.ofDag dag) wdB B ev') {v : Nat} (hv : v < dag.size)
    (hag : ∀ w, Desc dag v w → A w = B w ∧ wdA w = wdB w) :
    ev.cost[v]! = ev'.cost[v]! := by
  rw [hev.cost, hev'.cost]
  exact gCost_local hwf v hv hag


/-! ## Options and builds depend only on the dictionary at and below the term -/

/-- The Share option of `t`, if `t` is in the dictionary. -/
def optShare (index width : Array (Option Nat)) (t : Nat) : Array (Choice × Nat × ByteArray) :=
  match index[t]?.getD none with
  | some i => #[(.share, (widthOf width t).getD 0, tag4Bytes Ixon.Expr.FLAG_SHARE i)]
  | none => #[]

/-- The options of `t` written inline. -/
def optRest (p : Prep) (ev : DictEval) (index width : Array (Option Nat)) (t : Nat) :
    Array (Choice × Nat × ByteArray) :=
  let node := p.dag.node t
  if p.family[t]! == .none then
    #[(.inline, node.children.foldl (fun acc c => acc + ev.cost[c]!) node.head.ownBytes,
      Ixon.runPut (Ixon.putTagN 4 node.head.flag node.head.tag4Field))]
  else
    p.cutOptions ev index width node.head.flag p.spineLen[t]! ev.sides[t]! p.spineLen[t]!
      ev.below[t]! #[(.cut p.spineLen[t]!,
        tag4Size p.spineLen[t]! + ev.sides[t]! + ev.cost[p.tail[t]!]!,
        tag4Bytes node.head.flag p.spineLen[t]!)]

theorem cutOptions_append (p : Prep) (ev : DictEval) (index width : Array (Option Nat))
    (flag : UInt8) (l s : Nat) :
    ∀ (fuel : Nat) (cur : Option Nat) (a b : Array (Choice × Nat × ByteArray)),
      p.cutOptions ev index width flag l s fuel cur (a ++ b) =
        a ++ p.cutOptions ev index width flag l s fuel cur b
  | 0, _, _, _ => rfl
  | _ + 1, none, _, _ => rfl
  | fuel + 1, some u, a, b => by
    simp only [Prep.cutOptions]
    split
    · rw [← Array.append_push, cutOptions_append p ev index width flag l s fuel]
    · rw [cutOptions_append p ev index width flag l s fuel]

theorem cutOptions_noShare (p : Prep) (ev : DictEval) (index width : Array (Option Nat))
    (flag : UInt8) (l s : Nat) :
    ∀ (fuel : Nat) (cur : Option Nat) (b : Array (Choice × Nat × ByteArray)),
      (∀ o ∈ b.toList, o.1 ≠ .share) →
      ∀ o ∈ (p.cutOptions ev index width flag l s fuel cur b).toList, o.1 ≠ .share
  | 0, _, _, hb => hb
  | _ + 1, none, _, hb => hb
  | fuel + 1, some u, b, hb => by
    simp only [Prep.cutOptions]
    split
    · apply cutOptions_noShare p ev index width flag l s fuel
      intro o ho
      rw [Array.toList_push, List.mem_append] at ho
      rcases ho with ho | ho
      · exact hb o ho
      · simp at ho; rw [ho]; simp
    · exact cutOptions_noShare p ev index width flag l s fuel _ _ hb

theorem options_split (p : Prep) (ev : DictEval) (index width : Array (Option Nat)) (t : Nat) :
    p.options ev index width t = optShare index width t ++ optRest p ev index width t := by
  unfold Prep.options optShare optRest
  by_cases hf : (p.family[t]! == Family.none) = true
  · simp only [hf, ite_true]
    rw [Array.push_eq_append]
    rfl
  · simp only [hf, ite_false, Bool.false_eq_true]
    rw [Array.push_eq_append, cutOptions_append]
    rfl

theorem optRest_noShare (p : Prep) (ev : DictEval) (index width : Array (Option Nat)) (t : Nat) :
    ∀ o ∈ (optRest p ev index width t).toList, o.1 ≠ .share := by
  unfold optRest
  split
  · intro o ho; simp at ho; rw [ho]; simp
  · exact cutOptions_noShare _ _ _ _ _ _ _ _ _ _ (by intro o ho; simp at ho; rw [ho]; simp)

theorem options_filter (p : Prep) (ev : DictEval) (index width : Array (Option Nat)) (t : Nat) :
    (p.options ev index width t).filter (·.1 != .share) = optRest p ev index width t := by
  rw [options_split]
  apply Array.ext'
  rw [Array.toList_filter, Array.toList_append, List.filter_append]
  have h1 : (optShare index width t).toList.filter (·.1 != .share) = [] := by
    unfold optShare
    split
    · rfl
    · rfl
  rw [h1, List.nil_append, List.filter_eq_self]
  intro o ho
  have := optRest_noShare p ev index width t o ho
  cases h : o.1 with
  | share => exact absurd h this
  | inline => rfl
  | cut j => rfl


section Congr

variable {dag : Dag} (hwf : DagWF dag) {wdA wdB : Nat → Nat} {A B : Nat → Bool}
  {ev ev' : DictEval} {index index' width width' : Array (Option Nat)}
  (hev : GEvalOK (Prep.ofDag dag) wdA A ev) (hev' : GEvalOK (Prep.ofDag dag) wdB B ev')
  (hwA : ∀ u, widthOf width u = if A u then some (wdA u) else none)
  (hwB : ∀ u, widthOf width' u = if B u then some (wdB u) else none)
  (hiA : ∀ u, (index[u]?.getD none).isSome = A u)
  (hiB : ∀ u, (index'[u]?.getD none).isSome = B u)

include hiA hiB hwA hwB in
theorem agree_dict {w : Nat}
    (h : index[w]?.getD none = index'[w]?.getD none ∧ wdA w = wdB w) :
    A w = B w ∧ wdA w = wdB w ∧ widthOf width w = widthOf width' w := by
  have hA : A w = B w := by rw [← hiA, ← hiB, h.1]
  exact ⟨hA, h.2, by rw [hwA, hwB, hA, h.2]⟩

include hwf hev hev' hwA hwB hiA hiB in
/-- The internal-cut options of a telescope term agree when the dictionaries
agree strictly below it. -/
theorem cutOptions_congr {t : Nat} (ht : t < dag.size)
    (hf : (Prep.ofDag dag).family[t]! ≠ .none)
    (hag : ∀ w, Desc dag t w → w ≠ t →
      index[w]?.getD none = index'[w]?.getD none ∧ wdA w = wdB w)
    (flag : UInt8) (l s : Nat) :
    ∀ (fuel j : Nat) (cur : Option Nat) (opts : Array (Choice × Nat × ByteArray)),
      1 ≤ j → FirstAvail (Prep.ofDag dag) A t j cur →
      (Prep.ofDag dag).cutOptions ev index width flag l s fuel cur opts =
        (Prep.ofDag dag).cutOptions ev' index' width' flag l s fuel cur opts := by
  have hp := prepWF_ofDag hwf
  obtain ⟨_, hk, _, _, _⟩ := hp.spine t ht hf
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _; rfl
  | succ fuel ih =>
    intro j cur opts hj hcur
    cases cur with
    | none => rfl
    | some u =>
      obtain ⟨k, hjk, hkl, rfl, _, _⟩ := hcur
      have hlt := hp.spineAt_lt ht hf (by omega) hkl
      have hkn : spineAt (Prep.ofDag dag) t k < dag.size := Nat.lt_trans hlt ht
      have hdk := desc_spineAt hwf ht hf k (by omega)
      obtain ⟨_, hkf, hlenk, _⟩ := hk k hkl
      have hfk : (Prep.ofDag dag).family[spineAt (Prep.ofDag dag) t k]! ≠ .none := by
        rw [hkf]; exact hf
      obtain ⟨hi, hw, hwid⟩ := agree_dict hwA hwB hiA hiB (hag _ hdk (by omega))
      obtain ⟨hs, hb⟩ := rows_agree_strict hwf hev hev' hkn hfk fun w hw hne =>
        agree_dict hwA hwB hiA hiB (hag w (hdk.trans hw)
          (by have := Desc.le_of_wf hwf hw hkn; omega)) |>.elim fun a b => ⟨a, b.1⟩
      simp only [Prep.cutOptions]
      rw [hs, hb, hwid]
      have hidx : (index[spineAt (Prep.ofDag dag) t k]?.getD none).isSome =
          (index'[spineAt (Prep.ofDag dag) t k]?.getD none).isSome := by
        rw [(hag _ hdk (by omega)).1]
      have hnext : FirstAvail (Prep.ofDag dag) A t (k + 1)
          ev'.below[spineAt (Prep.ofDag dag) t k]! := by
        rw [← hb]
        exact FirstAvail.shift hlenk ((hev.2 _ hkn).2 hfk).2
      rw [hidx]
      split
      · exact ih (k + 1) _ _ (by omega) hnext
      · exact ih (k + 1) _ _ (by omega) hnext

theorem desc_of_child {dag : Dag} {t c : Nat} (hc : c ∈ (dag.node t).children) : Desc dag t c := by
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hc
  exact .child k hk (by rw [child_eq_getElem _ k hk]; exact .refl _)

include hwf hev hev' hwA hwB hiA hiB in
/-- The inline options of `t` agree when the dictionaries agree strictly
below it. -/
theorem optRest_congr {t : Nat} (ht : t < dag.size)
    (hag : ∀ w, Desc dag t w → w ≠ t →
      index[w]?.getD none = index'[w]?.getD none ∧ wdA w = wdB w) :
    optRest (Prep.ofDag dag) ev index width t = optRest (Prep.ofDag dag) ev' index' width' t := by
  have hp := prepWF_ofDag hwf
  have hagB : ∀ w, Desc dag t w → w ≠ t → A w = B w ∧ wdA w = wdB w := fun w hw hne =>
    (agree_dict hwA hwB hiA hiB (hag w hw hne)).elim fun a b => ⟨a, b.1⟩
  have hcostBelow : ∀ c, Desc dag t c → c < t → ev.cost[c]! = ev'.cost[c]! := by
    intro c hc hlt
    exact cost_agree hwf hev hev' (by omega) fun w hw =>
      hagB w (hc.trans hw) (by have := Desc.le_of_wf hwf hw (by omega); omega)
  unfold optRest
  by_cases hf : ((Prep.ofDag dag).family[t]! == .none) = true
  · simp only [hf, ite_true, ofDag_dag]
    rw [foldl_add_congr _ _ fun c hc => hcostBelow c (desc_of_child hc) (hwf.child_lt ht hc)]
  · simp only [hf, ite_false, Bool.false_eq_true]
    have hf' : (Prep.ofDag dag).family[t]! ≠ .none := by simpa using hf
    obtain ⟨_, _, hend, htl, _⟩ := hp.spine t ht hf'
    obtain ⟨hs, hb⟩ := rows_agree_strict hwf hev hev' ht hf' hagB
    have htail : ev.cost[(Prep.ofDag dag).tail[t]!]! = ev'.cost[(Prep.ofDag dag).tail[t]!]! :=
      hcostBelow _ (by rw [← hend]; exact desc_spineAt hwf ht hf' _ (Nat.le_refl _)) htl
    rw [hs, hb, htail]
    apply cutOptions_congr hwf hev hev' hwA hwB hiA hiB ht hf' hag _ _ _ _ 1 _ _ (Nat.le_refl _)
    rw [← hb]
    exact ((hev.2 t ht).2 hf').2

include hwf hev hev' hwA hwB hiA hiB in
theorem options_congr {t : Nat} (ht : t < dag.size)
    (hag : ∀ w, Desc dag t w → index[w]?.getD none = index'[w]?.getD none ∧ wdA w = wdB w) :
    (Prep.ofDag dag).options ev index width t = (Prep.ofDag dag).options ev' index' width' t := by
  rw [options_split, options_split,
    optRest_congr hwf hev hev' hwA hwB hiA hiB ht fun w hw _ => hag w hw]
  obtain ⟨_, _, hwid⟩ := agree_dict hwA hwB hiA hiB (hag t (.refl _))
  unfold optShare
  rw [(hag t (.refl _)).1, hwid]

theorem foldrM_congr_mem {β : Type} {l : List Node} {f g : Node → β → Except SharingError β}
    (h : ∀ n ∈ l, ∀ b, f n b = g n b) (init : β) : l.foldrM f init = l.foldrM g init := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldrM_cons]
    rw [ih (fun n hn b => h n (List.mem_cons_of_mem _ hn) b)]
    congr 1
    funext b
    exact h a List.mem_cons_self b

include hwf hev hev' hwA hwB hiA hiB in
/-- **Build locality.** `build` at `t` depends only on the dictionary at and
below `t`: two evaluations with the model rows of dictionaries that agree
there build the same expression. -/
theorem build_congr :
    ∀ (fuel : Nat) (entry : Bool) (t : Nat), t < dag.size →
      (∀ w, Desc dag t w → index[w]?.getD none = index'[w]?.getD none ∧ wdA w = wdB w) →
      (Prep.ofDag dag).build ev index width entry fuel t =
        (Prep.ofDag dag).build ev' index' width' entry fuel t := by
  have hp := prepWF_ofDag hwf
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _; rfl
  | succ fuel ih =>
    intro entry t ht hag
    have hopt := options_congr hwf hev hev' hwA hwB hiA hiB ht hag
    have hcost := cost_agree hwf hev hev' ht fun w hw =>
      (agree_dict hwA hwB hiA hiB (hag w hw)).elim fun a b => ⟨a, b.1⟩
    have hsub : ∀ c, Desc dag t c → c < dag.size →
        (Prep.ofDag dag).build ev index width false fuel c =
          (Prep.ofDag dag).build ev' index' width' false fuel c :=
      fun c hc hcn => ih false c hcn fun w hw => hag w (hc.trans hw)
    simp only [Prep.build, hopt, hcost]
    generalize hpk : pickOption (if entry = true then
        Array.filter (fun x => x.fst != Choice.share) ((Prep.ofDag dag).options ev' index' width' t)
      else (Prep.ofDag dag).options ev' index' width' t) = pk
    rcases pk with _ | ⟨choice, c⟩
    · rfl
    · obtain ⟨b, hb⟩ := pickOption_mem _ hpk
      have hmem : (choice, c, b) ∈ ((Prep.ofDag dag).options ev' index' width' t).toList := by
        split at hb
        · rw [Array.toList_filter] at hb; exact (List.mem_filter.mp hb).1
        · exact hb
      have hopt' := hp.gOptions_mem ev' hev' index' width' hwB hiB ht hmem
      simp only [ofDag_dag]
      by_cases hchk : (entry || c == ev'.cost[t]!) = true
      · simp only [hchk, ite_true]
        cases choice with
        | share => rw [(hag t (.refl _)).1]
        | inline =>
          have har := hwf.children_size ht
          have hchild : ∀ k, k < (dag.node t).head.arity →
              Desc dag t ((dag.node t).child k) ∧ (dag.node t).child k < dag.size := by
            intro k hk
            have hk' : k < (dag.node t).children.size := by rw [har]; exact hk
            refine ⟨.child k hk' (.refl _), ?_⟩
            have := hwf.childAt_lt ht hk
            omega
          cases hh : (dag.node t).head
          case prj ti f =>
            have h0 := hchild 0 (by simp [hh, Head.arity])
            simp only
            rw [hsub _ h0.1 h0.2]
          case letE lc =>
            have h0 := hchild 0 (by simp [hh, Head.arity])
            have h1 := hchild 1 (by simp [hh, Head.arity])
            have h2 := hchild 2 (by simp [hh, Head.arity])
            simp only
            rw [hsub _ h0.1 h0.2, hsub _ h1.1 h1.2, hsub _ h2.1 h2.2]
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
            rw [hsub _ hd (by omega)]
          split
          · rfl
          · split
            · rename_i hjlt
              have hdj := desc_spineAt hwf ht hf j (by omega)
              rw [(hag _ hdj).1]
              split
              · simp only [pure_bind]
                exact foldrM_congr_mem hside _
              · rfl
            · rename_i hjlt
              have hdj := desc_spineAt hwf ht hf j (by omega)
              have hjn : spineAt (Prep.ofDag dag) t j < dag.size := by
                have := Desc.le_of_wf hwf hdj ht; omega
              rw [hsub _ hdj hjn]
              cases (Prep.ofDag dag).build ev' index' width' false fuel
                (spineAt (Prep.ofDag dag) t j) with
              | error e => rfl
              | ok tl => exact foldrM_congr_mem hside _
      · simp only [hchk, Bool.false_eq_true, ite_false]
        rfl

end Congr

/-! ## The work of an evaluation step -/

/-- The available terms of `t`'s spine at positions `j, …, spineLen t - 1`. -/
def spineAvailCount (p : Prep) (avail : Nat → Bool) (t j : Nat) : Nat :=
  ((List.range' j (p.spineLen[t]! - j)).filter fun k => avail (spineAt p t k)).length

theorem spineAvailCount_nil (p : Prep) (avail : Nat → Bool) (t j : Nat)
    (hnone : ∀ k, j ≤ k → k < p.spineLen[t]! → avail (spineAt p t k) = false) :
    spineAvailCount p avail t j = 0 := by
  unfold spineAvailCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro a ha
  rw [List.mem_range'_1] at ha
  rw [hnone a ha.1 (by omega)]
  simp

theorem spineAvailCount_split (p : Prep) (avail : Nat → Bool) (t j k : Nat)
    (hjk : j ≤ k) (hk : k < p.spineLen[t]!) (hav : avail (spineAt p t k) = true)
    (hnone : ∀ k', j ≤ k' → k' < k → avail (spineAt p t k') = false) :
    spineAvailCount p avail t j = spineAvailCount p avail t (k + 1) + 1 := by
  unfold spineAvailCount
  rw [show p.spineLen[t]! - j = (k - j) + (1 + (p.spineLen[t]! - (k + 1))) by omega,
    ← List.range'_append_1, ← List.range'_append_1, List.filter_append, List.filter_append]
  have hpre : (List.range' j (k - j)).filter (fun k => avail (spineAt p t k)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    rw [List.mem_range'_1] at ha
    rw [hnone a ha.1 (by omega)]
    simp
  rw [hpre, show j + (k - j) = k by omega]
  simp [hav]

theorem PrepWF.gCutScan_work {p : Prep} (hp : PrepWF p) {avail : Nat → Bool}
    (sides : Array Nat) (below : Array (Option Nat)) (width : Array (Option Nat))
    {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) (l s : Nat)
    (hbelow : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      FirstAvail p avail (spineAt p t k) 1 below[spineAt p t k]!) :
    ∀ (fuel j : Nat) (cur : Option Nat) (best work : Nat), 1 ≤ j → j ≤ p.spineLen[t]! →
      p.spineLen[t]! - j ≤ fuel → FirstAvail p avail t j cur →
      (cutScan p.spineLen sides below width l s fuel cur best work).2 =
        work + spineAvailCount p avail t j := by
  obtain ⟨_, hk, _, _, _⟩ := hp.spine t ht hf
  intro fuel
  induction fuel with
  | zero =>
    intro j cur best work _ hj hfuel _
    have : spineAvailCount p avail t j = 0 := by
      unfold spineAvailCount
      rw [show p.spineLen[t]! - j = 0 by omega]
      rfl
    rw [this]
    rfl
  | succ fuel ih =>
    intro j cur best work hj1 hj hfuel hcur
    cases cur with
    | none =>
      rw [spineAvailCount_nil p avail t j hcur]
      rfl
    | some u =>
      obtain ⟨k, hjk, hkl, rfl, hav, hnone⟩ := hcur
      obtain ⟨_, _, hlenk, _⟩ := hk k hkl
      simp only [cutScan]
      rw [spineAvailCount_split p avail t j k hjk hkl hav hnone,
        ih (k + 1) _ _ _ (by omega) (by omega) (by omega)
          (FirstAvail.shift hlenk (hbelow k (by omega) hkl))]
      omega

/-- The work `evalStep` counts at an affected term whose descendants already
have their model rows: 1, plus for a telescope term one per available term
strictly below it on its spine. -/
theorem PrepWF.gEvalStep_work {p : Prep} (hp : PrepWF p) {wd : Nat → Nat} {avail : Nat → Bool}
    (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    (affected : Array Bool) (st : DictEval) (m : Nat) (hm : m < p.dag.size)
    (haff : affected[m]! = true)
    (hsz : st.cost.size = p.dag.size ∧ st.sides.size = p.dag.size ∧
      st.below.size = p.dag.size)
    (hrows : ∀ t, t < m → GEvalRow p wd avail st t) :
    (evalStep p.dag p.family p.spineLen p.tail width affected st m).work =
      st.work + 1 + (if p.family[m]! = .none then 0 else spineAvailCount p avail m 1) := by
  obtain ⟨_, _, hbs⟩ := hsz
  have keepO : ∀ (v : Option Nat) (arr : Array (Option Nat)) (i : Nat), i ≠ m →
      (arr.set! m v)[i]! = arr[i]! := by
    intro v arr i hi
    rw [setBang_getElem!, ite_eq_right (by intro h; exact hi h.1.symm)]
  by_cases hf : p.family[m]! = .none
  · simp only [evalStep, haff, ite_true, hf, beq_self_eq_true]
  · obtain ⟨hl1, hk, _, _, _⟩ := hp.spine m hm hf
    have hlt := hp.snext_lt hm hf
    have hB : FirstAvail p avail m 1
        (if p.family[snext p m]! = p.family[m]! then
          (if (widthOf width (snext p m)).isSome then some (snext p m)
            else st.below[snext p m]!) else none) := by
      rcases hp.spine_step hm hf with ⟨hs, hl, _⟩ | ⟨hs, hl, _⟩
      · rw [ite_eq_left hs, hwidth]
        have hn1 := (hp.spine (snext p m) (by omega) (by rw [hs]; exact hf)).1
        by_cases hav : avail (snext p m) = true
        · rw [ite_eq_left hav]
          exact ⟨1, Nat.le_refl _, by omega, rfl, hav, fun k' h1 h2 => by omega⟩
        · rw [ite_eq_right hav]
          simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
          have hrow := ((hrows _ hlt).2 (by rw [hs]; exact hf)).2
          have hlen1 : p.spineLen[spineAt p m 1]! = p.spineLen[m]! - 1 := by
            simp only [spineAt]; omega
          exact FirstAvail.unshift (by omega) (by simpa [spineAt] using hav)
            (FirstAvail.shift hlen1 hrow)
      · rw [ite_eq_right hs]
        intro k h1 h2
        omega
    generalize hBdef : (if p.family[snext p m]! = p.family[m]! then
          (if (widthOf width (snext p m)).isSome then some (snext p m)
            else st.below[snext p m]!) else none) = B at hB
    have hbelow : ∀ k, 1 ≤ k → k < p.spineLen[m]! →
        FirstAvail p avail (spineAt p m k) 1 (st.below.set! m B)[spineAt p m k]! := by
      intro k h1 h2
      have hlt' := hp.spineAt_lt hm hf h1 h2
      obtain ⟨_, hkf, _, _⟩ := hk k h2
      rw [keepO _ _ _ (by omega)]
      exact ((hrows _ hlt').2 (by rw [hkf]; exact hf)).2
    have hwork := fun best => hp.gCutScan_work (st.sides.set! m
        ((p.dag.node m).sideExtra + st.cost[(p.dag.node m).sideChild]! +
          (if p.family[snext p m]! = p.family[m]! then st.sides[snext p m]! else 0)))
      (st.below.set! m B) width hm hf p.spineLen[m]!
      ((p.dag.node m).sideExtra + st.cost[(p.dag.node m).sideChild]! +
          (if p.family[snext p m]! = p.family[m]! then st.sides[snext p m]! else 0))
      hbelow p.spineLen[m]! 1 B best st.work (Nat.le_refl _) (by omega) (by omega) hB
    simp only [evalStep, haff, ite_true]
    have hfb : (p.family[m]! == Family.none) = false := by simpa using hf
    simp only [hfb, Bool.false_eq_true, ite_false]
    simp only [ite_beq_family]
    rw [show (p.dag.node m).spineNext = snext p m from rfl, hBdef, ite_eq_right hf]
    rw [hwork]
    omega

/-- The work an evaluation counts at `u` (`gEvalStep_work`). -/
def nodeWork (p : Prep) (avail : Nat → Bool) (u : Nat) : Nat :=
  1 + (if p.family[u]! = .none then 0 else spineAvailCount p avail u 1)

/-- **Re-evaluation work.** The work `Prep.evalUp` counts is `nodeWork` under
the new dictionary summed over `t` and the terms above it. -/
theorem evalUp_work {dag : Dag} (hwf : DagWF dag) {wd wd' : Nat → Nat} {A A' : Nat → Bool}
    {ev : DictEval} (hev : GEvalOK (Prep.ofDag dag) wd A ev) {t : Nat} (ht : t < dag.size)
    (hdiff : ∀ v, v ≠ t → A' v = A v ∧ wd' v = wd v) (width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if A' u then some (wd' u) else none) :
    ((Prep.ofDag dag).evalUp ev width t).work =
      (((List.range' t (dag.size - t)).filter fun u => (ancestorMarks dag t)[u]!).map
        (nodeWork (Prep.ofDag dag) A')).sum := by
  have hp := prepWF_ofDag hwf
  have hag : ∀ u, u < dag.size → ¬ Desc dag u t → ∀ v, Desc dag u v → A v = A' v ∧ wd v = wd' v := by
    intro u hu hnd v hv
    have hvt : v ≠ t := fun h => hnd (h ▸ hv)
    exact ⟨(hdiff v hvt).1.symm, (hdiff v hvt).2.symm⟩
  let marks := ancestorMarks dag t
  let step := evalStep (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen (Prep.ofDag dag).tail width marks
  have hinv : ∀ m, m ≤ dag.size - t →
      let st := (List.range' t m).foldl step { ev with work := 0 }
      (st.cost.size = dag.size ∧ st.sides.size = dag.size ∧ st.below.size = dag.size) ∧
        (∀ u, u < t + m → GEvalRow (Prep.ofDag dag) wd' A' st u) ∧
        (∀ u, t + m ≤ u → st.cost[u]! = ev.cost[u]! ∧ st.sides[u]! = ev.sides[u]! ∧
          st.below[u]! = ev.below[u]!) ∧
        st.work = (((List.range' t m).filter fun u => marks[u]!).map (nodeWork (Prep.ofDag dag) A')).sum := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨hev.1, fun u hu => ?_, fun u _ => ⟨rfl, rfl, rfl⟩, rfl⟩
      have hud : u < dag.size := by omega
      exact gEvalRow_local hwf hud (hag u hud fun hd => by
        have := Desc.le_of_wf hwf hd hud; omega) (hev.2 u hud)
    | succ m ih =>
      intro hm
      obtain ⟨hs, hrows, hrest, hwork⟩ := ih (by omega)
      simp only at hs hrows hrest hwork ⊢
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.filter_append, List.map_append, List.sum_append]
      generalize hst : (List.range' t m).foldl step { ev with work := 0 } = st
        at hs hrows hrest hwork
      have hkeep : ∀ u, u ≠ t + m → (step st (t + m)).cost[u]! = st.cost[u]! ∧
          (step st (t + m)).sides[u]! = st.sides[u]! ∧
          (step st (t + m)).below[u]! = st.below[u]! :=
        fun u hu => evalStep_keep _ _ _ _ width marks st hu
      have htm : t + m < dag.size := by omega
      by_cases hmark : marks[t + m]! = true
      · obtain ⟨hs', hrows'⟩ := hp.gEvalStep_spec width hwidth marks st (t + m) htm hmark hs
          hrows
        have hw' := hp.gEvalStep_work width hwidth marks st (t + m) htm hmark hs hrows
        refine ⟨hs', fun u hu => hrows' u (by omega), fun u hu => ?_, ?_⟩
        · obtain ⟨k1, k2, k3⟩ := hkeep u (by omega)
          obtain ⟨r1, r2, r3⟩ := hrest u (by omega)
          exact ⟨k1.trans r1, k2.trans r2, k3.trans r3⟩
        · rw [hw', hwork]
          simp only [List.filter_cons, List.filter_nil, hmark, ite_true, List.map_cons,
            List.map_nil, List.sum_cons, List.sum_nil]
          unfold nodeWork
          omega
      · have hid : step st (t + m) = st := by
          simp only [step, evalStep]
          rw [ite_eq_right hmark]
        rw [hid]
        refine ⟨hs, fun u hu => ?_, fun u hu => hrest u (by omega), ?_⟩
        · by_cases hum : u < t + m
          · exact hrows u hum
          · have hu' : u = t + m := by omega
            subst hu'
            have hnd : ¬ Desc dag (t + m) t := fun hd =>
              hmark ((ancestorMarks_iff hwf ht (t + m) htm).mpr hd)
            obtain ⟨r1, r2, r3⟩ := hrest (t + m) (Nat.le_refl _)
            refine gEvalRow_local hwf htm (hag _ htm hnd) ?_
            exact gEvalRow_of_agree r1 r2 r3 (hev.2 _ htm)
        · rw [hwork]
          simp [hmark]
  obtain ⟨_, _, _, hw⟩ := hinv (dag.size - t) (Nat.le_refl _)
  unfold Prep.evalUp
  rw [foldRange_eq]
  exact hw

/-- **Empty-dictionary work.** Evaluating the empty dictionary counts one
per term: no term has an available term on its spine. -/
theorem evalAll_none_work {dag : Dag} (hwf : DagWF dag) :
    ((Prep.ofDag dag).evalAll (Array.replicate dag.size none)).work = dag.size := by
  have hp := prepWF_ofDag hwf
  have hwidth : ∀ u, widthOf (Array.replicate dag.size none) u =
      if (fun _ => false) u then some ((fun _ => 0) u) else none := by
    intro u
    simp only [widthOf, Array.getElem?_replicate, Bool.false_eq_true, ite_false]
    split <;> rfl
  let step := evalStep (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
    (Prep.ofDag dag).tail (Array.replicate dag.size none) (Array.replicate dag.size true)
  have hinv : ∀ m, m ≤ dag.size →
      let st := (List.range m).foldl step { (Prep.ofDag dag).empty with work := 0 }
      (st.cost.size = dag.size ∧ st.sides.size = dag.size ∧ st.below.size = dag.size) ∧
        (∀ t, t < m → GEvalRow (Prep.ofDag dag) (fun _ => 0) (fun _ => false) st t) ∧
        st.work = m := by
    intro m
    induction m with
    | zero => intro _; exact ⟨ofDag_empty_size dag, fun t h => absurd h (Nat.not_lt_zero _), rfl⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs, hrows, hw⟩ := ih (by omega)
      simp only at hs hrows hw ⊢
      rw [foldl_range_succ]
      have haff : (Array.replicate dag.size true)[m]! = true := by simp [show m < dag.size by omega]
      obtain ⟨hs', hrows'⟩ := hp.gEvalStep_spec _ hwidth _ _ m (by simp [ofDag_dag]; omega) haff hs
        hrows
      refine ⟨hs', hrows', ?_⟩
      rw [hp.gEvalStep_work _ hwidth _ _ m (by simp [ofDag_dag]; omega) haff hs hrows, hw,
        spineAvailCount_nil _ _ _ _ fun _ _ _ => rfl]
      split <;> rfl
  unfold Prep.evalAll Prep.eval evalFrom
  rw [foldRange_zero]
  exact (hinv dag.size (Nat.le_refl _)).2.2


end OnePass

end Ix.Compile.Verify.UniformModel
