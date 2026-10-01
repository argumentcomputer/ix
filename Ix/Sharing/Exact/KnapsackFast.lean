/-
  Rank-based table-count knapsack (phase 1, `uniformKnapsack`).

  The knapsack over the component tables keeps, per count `c`, the least
  `(Δ, set)` (Δ, then `setPrec`) over one entry per component with counts
  summing to `c`. The specification (`knapStep`) builds the merged set of
  every candidate and compares sets element by element: cubic in the count
  bracket. The fast version keeps per cell only Δ, the entry it took, and the
  rank of its set among the layer's sets in `setPrec` order, with a sparse
  table over the first differences of rank-adjacent sets. Comparing
  `S_a ∪ X` with `S_b ∪ Y` (`S` from earlier components, `X`, `Y` entries of
  the next one, over disjoint domains) needs the least element of their
  symmetric difference: the smaller of that of `S_a, S_b` (the least
  first difference of the rank-adjacent sets between them) and that of
  `X, Y`; the set without it precedes. The chosen cell's set is rebuilt from
  the entries taken. (Rust: `Knapsack`, `sharing_exact/uniform.rs`.)

  `uniformKnapsack_eq_fast : @uniformKnapsack = @uniformKnapsackFast`
  (`@[csimp]`) holds for every input; the fast knapsack runs when every
  table entry is an ascending list of its count's length and the tables'
  terms are disjoint across components (true of the component tables),
  the specification otherwise. Both check `knapsackCells` the same way.
-/
module

public import Ix.Sharing.Exact.SortedSets
public import Ix.Sharing.Exact.PinnedFast
public import Ix.Sharing.Exact.Uniform
import all Ix.Sharing.Exact.Uniform
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Common
import all Ix.Sharing.Exact.PinnedFast
import all Ix.Sharing.Exact.SortedSets

public section

namespace Ix.Sharing.Exact

/-! ## The tie order is a strict total order -/

instance compareDesc_transCmp : Std.TransCmp compareDesc :=
  inferInstanceAs (Std.TransCmp fun x y : Nat => compare y x)

instance compareDesc_lawfulEqCmp : Std.LawfulEqCmp compareDesc :=
  inferInstanceAs (Std.LawfulEqCmp fun x y : Nat => compare y x)

theorem setPrec_eq_lt (a b : Array Nat) :
    setPrec a b = true ↔ Array.compareLex compareDesc a b = .lt := by
  unfold setPrec
  cases Array.compareLex compareDesc a b <;> decide

theorem setPrec_irrefl' (a : Array Nat) : setPrec a a = false := by
  unfold setPrec
  rw [Std.ReflCmp.compare_self (cmp := Array.compareLex compareDesc)]
  decide

theorem setPrec_trans' {a b c : Array Nat} (h₁ : setPrec a b = true)
    (h₂ : setPrec b c = true) : setPrec a c = true := by
  rw [setPrec_eq_lt] at *
  exact Std.TransCmp.lt_trans h₁ h₂

theorem setPrec_asymm' {a b : Array Nat} (h : setPrec a b = true) : setPrec b a = false := by
  rw [setPrec_eq_lt] at h
  unfold setPrec
  rw [Std.OrientedCmp.eq_swap (cmp := Array.compareLex compareDesc), h]
  decide

theorem setPrec_total' {a b : Array Nat} (h : a ≠ b) :
    setPrec a b = true ∨ setPrec b a = true := by
  rw [setPrec_eq_lt, setPrec_eq_lt]
  cases hc : Array.compareLex compareDesc a b
  · exact Or.inl rfl
  · exact absurd (Std.LawfulEqCmp.eq_of_compare hc) h
  · right
    rw [Std.OrientedCmp.eq_swap (cmp := Array.compareLex compareDesc), hc]
    rfl

/-- The order of `betterEntry` on values. -/
def entryLt (x y : _root_.Int × Array Nat) : Bool :=
  x.1 < y.1 || (x.1 == y.1 && setPrec x.2 y.2)

theorem betterEntry_some (x y : _root_.Int × Array Nat) :
    betterEntry x (some y) = entryLt x y := by
  unfold betterEntry entryLt
  rfl

theorem entryLt_irrefl (x : _root_.Int × Array Nat) : entryLt x x = false := by
  unfold entryLt
  simp [setPrec_irrefl']

theorem entryLt_trans {x y z : _root_.Int × Array Nat} (h₁ : entryLt x y = true)
    (h₂ : entryLt y z = true) : entryLt x z = true := by
  unfold entryLt at *
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at *
  rcases h₁ with h₁ | ⟨h₁, h₁'⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂'⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, setPrec_trans' h₁' h₂'⟩

theorem entryLt_total {x y : _root_.Int × Array Nat} (h : x ≠ y) :
    entryLt x y = true ∨ entryLt y x = true := by
  unfold entryLt
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  rcases Int.lt_trichotomy x.1 y.1 with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · have hne : x.2 ≠ y.2 := fun h2 => h (Prod.ext heq h2)
    rcases setPrec_total' hne with h' | h'
    · exact Or.inl (Or.inr ⟨heq, h'⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, h'⟩)
  · exact Or.inr (Or.inl hgt)

/-! ## Folds that keep the least element -/

/-- A fold that replaces its value by a strictly smaller element ends with an
element that no element of the list is below, and that is the initial value
or below it (on the elements satisfying `P`, where the step compares by
`lt` through `abs`). -/
theorem foldl_least {α β : Type} (P : α → Prop) (abs : α → β) (lt : β → β → Bool)
    (hirr : ∀ x, lt x x = false)
    (htrans : ∀ x y z, lt x y = true → lt y z = true → lt x z = true)
    (f : Option α → α → Option α) (hf1 : ∀ x, f none x = some x)
    (hf2 : ∀ a x, P a → P x → f (some a) x = if lt (abs x) (abs a) then some x else some a) :
    ∀ (L : List α) (acc : Option α), (∀ x ∈ L, P x) → (∀ a, acc = some a → P a) →
      (L.foldl f acc = none ↔ acc = none ∧ L = []) ∧
        ∀ m, L.foldl f acc = some m → (m ∈ L ∨ acc = some m) ∧
          (∀ x ∈ L, lt (abs x) (abs m) = false) ∧
          (∀ a, acc = some a → m = a ∨ lt (abs m) (abs a) = true) := by
  have hasymm : ∀ x y, lt x y = true → lt y x = false := by
    intro x y h
    cases h' : lt y x
    · rfl
    · have := htrans _ _ _ h h'; rw [hirr] at this; cases this
  intro L
  induction L with
  | nil =>
    intro acc _ _
    simp only [List.foldl_nil]
    refine ⟨by simp, fun m hm => ⟨Or.inr hm, fun x hx => by simp at hx, fun a ha => ?_⟩⟩
    rw [hm] at ha; cases ha; exact Or.inl rfl
  | cons t ts ih =>
    intro acc hL hacc
    have ht := hL t List.mem_cons_self
    have hts : ∀ x ∈ ts, P x := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    simp only [List.foldl_cons]
    cases acc with
    | none =>
      rw [hf1]
      obtain ⟨hnone, hsome⟩ := ih (some t) hts (fun a ha => by cases ha; exact ht)
      refine ⟨⟨fun h => absurd (hnone.mp h).1 (by simp), fun h => by simp at h⟩, fun m hm => ?_⟩
      obtain ⟨hmem, hle, hlea⟩ := hsome m hm
      refine ⟨?_, fun x hx => ?_, fun a ha => by cases ha⟩
      · rcases hmem with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · cases h; exact Or.inl List.mem_cons_self
      · rcases List.mem_cons.mp hx with h | h
        · subst h
          rcases hlea x rfl with h | h
          · subst h; exact hirr _
          · exact hasymm _ _ h
        · exact hle x h
    | some a =>
      have ha := hacc a rfl
      rw [hf2 a t ha ht]
      by_cases hb : lt (abs t) (abs a) = true
      · simp only [hb, ite_true]
        obtain ⟨hnone, hsome⟩ := ih (some t) hts (fun a ha => by cases ha; exact ht)
        refine ⟨⟨fun h => absurd (hnone.mp h).1 (by simp), fun h => by simp at h⟩, fun m hm => ?_⟩
        obtain ⟨hmem, hle, hlea⟩ := hsome m hm
        have hmt := hlea t rfl
        refine ⟨?_, fun x hx => ?_, fun a' ha' => ?_⟩
        · rcases hmem with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · cases h; exact Or.inl List.mem_cons_self
        · rcases List.mem_cons.mp hx with h | h
          · subst h
            rcases hmt with h | h
            · subst h; exact hirr _
            · exact hasymm _ _ h
          · exact hle x h
        · cases ha'
          rcases hmt with h | h
          · subst h; exact Or.inr hb
          · exact Or.inr (htrans _ _ _ h hb)
      · simp only [hb, Bool.false_eq_true, ite_false]
        obtain ⟨hnone, hsome⟩ := ih (some a) hts (fun a' ha' => by cases ha'; exact ha)
        refine ⟨⟨fun h => absurd (hnone.mp h).1 (by simp), fun h => by simp at h⟩, fun m hm => ?_⟩
        obtain ⟨hmem, hle, hlea⟩ := hsome m hm
        refine ⟨?_, fun x hx => ?_, hlea⟩
        · rcases hmem with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h
        · rcases List.mem_cons.mp hx with h | h
          · subst h
            cases h : lt (abs x) (abs m)
            · rfl
            · exfalso
              rcases hlea a rfl with h' | h'
              · subst h'; exact hb h
              · exact hb (htrans _ _ _ h h')
          · exact hle x h

/-- Two least elements of the same list are equal when the order is total. -/
theorem least_unique {β : Type} (lt : β → β → Bool)
    (htot : ∀ x y, x ≠ y → lt x y = true ∨ lt y x = true) {L : List β} {m m' : β}
    (hm : m ∈ L) (hm' : m' ∈ L) (h : ∀ x ∈ L, lt x m = false) (h' : ∀ x ∈ L, lt x m' = false) :
    m = m' := by
  by_cases he : m = m'
  · exact he
  · rcases htot m m' he with h1 | h1
    · rw [h' m hm] at h1; cases h1
    · rw [h m' hm'] at h1; cases h1

/-! ## The specification's step, cell by cell -/

/-- The candidate of a knapsack layer from cell `c` (value `e`) and table
entry `k` (value `x`): the summed Δ and the merged set. -/
def knapCand (e x : _root_.Int × Array Nat) : _root_.Int × Array Nat :=
  (e.1 + x.1, mergeSorted e.2 x.2)

/-- The inner update of `knapStep` for source cell `c` with value `e`. -/
def knapInner (cap c : Nat) (e : _root_.Int × Array Nat) (bySize : CTable)
    (ndp : Array (Option (_root_.Int × Array Nat))) (k : Nat) :
    Array (Option (_root_.Int × Array Nat)) :=
  (bySize[k]!).elim ndp fun x =>
    if c + k > cap then ndp
    else if betterEntry (knapCand e x) ndp[c + k]! then ndp.set! (c + k) (some (knapCand e x))
    else ndp

/-- `knapStep` with the matches written as `Option.elim`. -/
def knapStepElim (cap : Nat) (dp : Array (Option (_root_.Int × Array Nat))) (bySize : CTable) :
    Array (Option (_root_.Int × Array Nat)) :=
  (List.range dp.size).foldl (fun ndp c =>
    (dp[c]!).elim ndp fun e => (List.range bySize.size).foldl (knapInner cap c e bySize) ndp)
    (Array.replicate (cap + 1) none)

theorem knapStep_eq_elim : @knapStep = @knapStepElim := by
  funext cap dp bySize
  unfold knapStep knapStepElim
  congr 1
  funext ndp c
  cases dp[c]! with
  | none => rfl
  | some e =>
    obtain ⟨d, s⟩ := e
    simp only [Option.elim]
    congr 1
    funext ndp k
    unfold knapInner knapCand
    cases bySize[k]! with
    | none => rfl
    | some x => obtain ⟨dk, sk⟩ := x; rfl

/-- The step of the least-candidate fold. -/
def betterStep (acc : Option (_root_.Int × Array Nat)) (x : _root_.Int × Array Nat) :
    Option (_root_.Int × Array Nat) :=
  if betterEntry x acc then some x else acc

/-- The candidate of the source cell `c` (value `e`) for the target `t`, among the
table entries below `n`: at most one. -/
def srcCands (cap c : Nat) (e : _root_.Int × Array Nat) (bySize : CTable) (n t : Nat) :
    List (_root_.Int × Array Nat) :=
  if c ≤ t ∧ t - c < n ∧ t ≤ cap then (bySize[t - c]!).elim [] fun x => [knapCand e x] else []

theorem getElem!_set!_ne' {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (v : α)
    (h : i ≠ j) : (a.set! i v)[j]! = a[j]! := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_def]
  rw [Array.getElem?_setIfInBounds]
  simp [h]

theorem getElem!_set!_self' {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α)
    (h : i < a.size) : (a.set! i v)[i]! = v := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_def]
  rw [Array.getElem?_setIfInBounds]
  simp [h]

/-- The inner loop of a source cell updates each target at most once. -/
theorem knapInner_fold (cap c : Nat) (e : _root_.Int × Array Nat) (bySize : CTable) :
    ∀ (n : Nat) (ndp : Array (Option (_root_.Int × Array Nat))), ndp.size = cap + 1 →
      ((List.range n).foldl (knapInner cap c e bySize) ndp).size = cap + 1 ∧
        ∀ t, t ≤ cap → ((List.range n).foldl (knapInner cap c e bySize) ndp)[t]! =
          (srcCands cap c e bySize n t).foldl betterStep ndp[t]! := by
  intro n
  induction n with
  | zero => intro ndp hs; simp [hs, srcCands]
  | succ n ih =>
    intro ndp hs
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hsz, hval⟩ := ih ndp hs
    generalize hr : (List.range n).foldl (knapInner cap c e bySize) ndp = r at hsz hval
    -- targets other than `c + n` are unchanged by entry `n`
    have hsame : ∀ t, t ≤ cap → t ≠ c + n →
        srcCands cap c e bySize (n + 1) t = srcCands cap c e bySize n t := by
      intro t _ htn
      unfold srcCands
      by_cases h1 : c ≤ t ∧ t - c < n ∧ t ≤ cap
      · have : c ≤ t ∧ t - c < n + 1 ∧ t ≤ cap := ⟨h1.1, by omega, h1.2.2⟩
        rw [ite_eq_left this, ite_eq_left h1]
      · have : ¬(c ≤ t ∧ t - c < n + 1 ∧ t ≤ cap) := by omega
        rw [ite_eq_right this, ite_eq_right h1]
    -- the target `c + n` gets entry `n`'s candidate, if any
    have hnew : c + n ≤ cap → srcCands cap c e bySize (n + 1) (c + n) =
        (bySize[n]!).elim [] fun x => [knapCand e x] := by
      intro hle
      unfold srcCands
      have : c ≤ c + n ∧ c + n - c < n + 1 ∧ c + n ≤ cap := ⟨by omega, by omega, hle⟩
      rw [ite_eq_left this, Nat.add_sub_cancel_left]
    have hold : c + n ≤ cap → srcCands cap c e bySize n (c + n) = [] := by
      intro _
      unfold srcCands
      have : ¬(c ≤ c + n ∧ c + n - c < n ∧ c + n ≤ cap) := by omega
      rw [ite_eq_right this]
    unfold knapInner
    cases hb : bySize[n]! with
    | none =>
      simp only [Option.elim_none]
      refine ⟨hsz, fun t ht => ?_⟩
      rw [hval t ht]
      by_cases htn : t = c + n
      · subst htn
        rw [hnew ht, hold ht, hb]
        rfl
      · rw [hsame t ht htn]
    | some x =>
      simp only [Option.elim_some]
      by_cases hcap : c + n > cap
      · simp only [hcap, ite_true]
        refine ⟨hsz, fun t ht => ?_⟩
        rw [hval t ht]
        have htn : t ≠ c + n := by omega
        rw [hsame t ht htn]
      · simp only [hcap, ite_false]
        have hle : c + n ≤ cap := by omega
        have hlt : c + n < r.size := by omega
        have hrcn : r[c + n]! = ndp[c + n]! := by
          rw [hval (c + n) hle, hold hle]; rfl
        have htgt : (srcCands cap c e bySize (n + 1) (c + n)).foldl betterStep ndp[c + n]! =
            betterStep ndp[c + n]! (knapCand e x) := by
          rw [hnew hle, hb]; rfl
        split
        · rename_i hbet
          refine ⟨by simp [hsz], fun t ht => ?_⟩
          by_cases htc : t = c + n
          · subst htc
            rw [getElem!_set!_self' _ _ _ hlt, htgt]
            rw [hrcn] at hbet
            simp [betterStep, hbet]
          · rw [getElem!_set!_ne' _ _ _ _ (fun h => htc h.symm), hval t ht, hsame t ht htc]
        · rename_i hbet
          refine ⟨hsz, fun t ht => ?_⟩
          by_cases htc : t = c + n
          · subst htc
            rw [hrcn, htgt]
            rw [hrcn] at hbet
            simp [betterStep, hbet]
          · rw [hval t ht, hsame t ht htc]

/-- The outer loop of `knapStep`: each target holds the least of the
candidates of the sources so far, in source order. -/
theorem knapStepElim_fold (cap : Nat) (dp : Array (Option (_root_.Int × Array Nat)))
    (bySize : CTable) :
    ∀ (m : Nat),
      let r := (List.range m).foldl (fun ndp c =>
        (dp[c]!).elim ndp fun e => (List.range bySize.size).foldl (knapInner cap c e bySize) ndp)
        (Array.replicate (cap + 1) none)
      r.size = cap + 1 ∧ ∀ t, t ≤ cap →
        r[t]! = ((List.range m).flatMap fun c =>
          (dp[c]!).elim [] fun e => srcCands cap c e bySize bySize.size t).foldl betterStep none := by
  intro m
  induction m with
  | zero =>
    refine ⟨by simp, fun t ht => ?_⟩
    rw [getElem!_pos _ t (by simp; omega)]
    simp
  | succ m ih =>
    obtain ⟨hsz, hval⟩ := ih
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    generalize hr : (List.range m).foldl (fun ndp c =>
        (dp[c]!).elim ndp fun e => (List.range bySize.size).foldl (knapInner cap c e bySize) ndp)
        (Array.replicate (cap + 1) none) = r at hsz hval
    cases hd : dp[m]! with
    | none =>
      simp only [Option.elim_none]
      exact ⟨hsz, hval⟩
    | some e =>
      simp only [Option.elim_some]
      obtain ⟨hsz', hval'⟩ := knapInner_fold cap m e bySize bySize.size r hsz
      refine ⟨hsz', fun t ht => ?_⟩
      rw [hval' t ht, hval t ht]

/-- `knapStep`'s cell `t`: the least candidate over the sources. -/
theorem knapStep_get (cap : Nat) (dp : Array (Option (_root_.Int × Array Nat))) (bySize : CTable) :
    (knapStep cap dp bySize).size = cap + 1 ∧ ∀ t, t ≤ cap →
      (knapStep cap dp bySize)[t]! = ((List.range dp.size).flatMap fun c =>
        (dp[c]!).elim [] fun e => srcCands cap c e bySize bySize.size t).foldl betterStep none := by
  rw [knapStep_eq_elim]
  exact knapStepElim_fold cap dp bySize dp.size

/-! ## The fast knapsack -/

/-- The entry set at count `k` of a table (empty if there is none). -/
@[inline] def entrySet (tab : CTable) (k : Nat) : Array Nat := (tab[k]!).elim #[] (·.2)

/-- A knapsack layer: per cell the least Δ (if any), the rank of its set
among the layer's sets in `setPrec` order, and the sparse table of the first
differences of rank-adjacent sets. -/
structure KLayer where
  delta : Array (Option _root_.Int)
  rank : Array Nat
  sp : Array (Array Nat)

/-- The least element of the symmetric difference of the sets of two cells of
a layer (`none` for the same cell). -/
def prevFD (L : KLayer) (a b : Nat) : Option Nat :=
  if a = b then none
  else some (sparseQuery L.sp (min L.rank[a]! L.rank[b]!) (max L.rank[a]! L.rank[b]!))

/-- The least element of the symmetric difference of the sets of two
candidates: cell `a` of the previous layer with entry `ka` of the table, and
cell `b` with entry `kb`. -/
def candFD (L : KLayer) (tab : CTable) (a ka b kb : Nat) : Option Nat :=
  minOpt (prevFD L a b) (firstDiff (entrySet tab ka).toList (entrySet tab kb).toList)

/-- Whether the set of candidate `(a, ka)` precedes that of `(b, kb)` in
`setPrec` order: the set without their least differing term. -/
def candPrec (L : KLayer) (tab : CTable) (a ka b kb : Nat) : Bool :=
  (candFD L tab a ka b kb).elim false fun m =>
    if prevFD L a b == some m then decide (L.rank[a]! < L.rank[b]!)
    else !(entrySet tab ka).contains m

/-- A candidate `(Δ, previous cell, entry count)` is better than another. -/
def candBetter (L : KLayer) (tab : CTable) (x y : _root_.Int × Nat × Nat) : Bool :=
  x.1 < y.1 || (x.1 == y.1 && candPrec L tab x.2.1 x.2.2 y.2.1 y.2.2)

/-- The candidates of cell `c`: entry `k` of the table with cell `c - k` of the
previous layer. -/
def cellCands (L : KLayer) (tab : CTable) (c : Nat) : List (_root_.Int × Nat × Nat) :=
  (List.range (min c (tab.size - 1) + 1)).filterMap fun k =>
    (tab[k]!).bind fun x => (L.delta[c - k]!).map fun da => (da + x.1, c - k, k)

/-- The step of the fold keeping the best candidate. -/
def candStep (L : KLayer) (tab : CTable) (acc : Option (_root_.Int × Nat × Nat))
    (x : _root_.Int × Nat × Nat) : Option (_root_.Int × Nat × Nat) :=
  acc.elim (some x) fun y => if candBetter L tab x y then some x else some y

/-- The best candidate of cell `c`. -/
def cellBest (L : KLayer) (tab : CTable) (c : Nat) : Option (_root_.Int × Nat × Nat) :=
  (cellCands L tab c).foldl (candStep L tab) none

/-- Position of every element of a list (`rank[l[i]] = i`). -/
def rankOf (n : Nat) (l : List Nat) : Array Nat :=
  l.zipIdx.foldl (fun rk p => rk.set! p.1 p.2) (Array.replicate n 0)

/-- The best candidate of every cell. -/
def knapBest (cap : Nat) (L : KLayer) (tab : CTable) : Array (Option (_root_.Int × Nat × Nat)) :=
  (Array.range (cap + 1)).map (cellBest L tab)

/-- The entry count taken by every cell. -/
def knapTook (best : Array (Option (_root_.Int × Nat × Nat))) : Array Nat :=
  best.map fun o => o.elim 0 (·.2.2)

/-- The nonempty cells of the next layer in `setPrec` order of their sets. -/
def knapOrd (cap : Nat) (L : KLayer) (tab : CTable) (best : Array (Option (_root_.Int × Nat × Nat)))
    (took : Array Nat) : List Nat :=
  ((List.range (cap + 1)).filter fun c => (best[c]!).isSome).mergeSort fun u v =>
    !candPrec L tab (v - took[v]!) took[v]! (u - took[u]!) took[u]!

/-- The first differences of rank-adjacent sets of the next layer. -/
def knapAdj (L : KLayer) (tab : CTable) (took : Array Nat) (ord : List Nat) : Array Nat :=
  let ordA := ord.toArray
  (Array.range (ordA.size - 1)).map fun r =>
    let u := ordA[r]!
    let v := ordA[r + 1]!
    (candFD L tab (u - took[u]!) took[u]! (v - took[v]!) took[v]!).getD 0

/-- The next layer with table `tab`, and the entry count taken by every cell. -/
def knapLayer (cap : Nat) (L : KLayer) (tab : CTable) : KLayer × Array Nat :=
  let best := knapBest cap L tab
  let took := knapTook best
  let ord := knapOrd cap L tab best took
  ({ delta := best.map (·.map (·.1)), rank := rankOf (cap + 1) ord,
     sp := sparseBuild (knapAdj L tab took ord) }, took)

/-- The layer before any table: only the empty set, at count 0. -/
def knapInit (cap : Nat) : KLayer :=
  { delta := #[some 0] ++ Array.replicate cap none, rank := Array.replicate (cap + 1) 0,
    sp := sparseBuild #[] }

/-- All layers: the last layer and the entry counts taken at every layer. -/
def knapRun (cap : Nat) (tabs : List CTable) : KLayer × Array (Array Nat) :=
  tabs.foldl (fun acc tab =>
    let r := knapLayer cap acc.1 tab
    (r.1, acc.2.push r.2)) (knapInit cap, #[])

/-- The set of cell `c` after the first `j` tables, from the entries taken. -/
def knapRecon (tabs : Array CTable) (tooks : Array (Array Nat)) : Nat → Nat → Array Nat
  | 0, _ => #[]
  | j + 1, c =>
    let k := tooks[j]![c]!
    mergeSorted (knapRecon tabs tooks j (c - k)) (entrySet tabs[j]! k)

/-- The terms of the entries taken along the path of cell `c`. -/
def knapCollect (tabs : Array CTable) (tooks : Array (Array Nat)) :
    Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | j + 1, c, acc =>
    let k := tooks[j]![c]!
    knapCollect tabs tooks j (c - k) ((entrySet tabs[j]! k).toList ++ acc)

/-- `knapRecon`, merged once. -/
def knapReconFast (tabs : Array CTable) (tooks : Array (Array Nat)) (j c : Nat) : Array Nat :=
  ((knapCollect tabs tooks j c []).mergeSort fun x y => decide (x ≤ y)).toArray

/-- The cell of the least length (then the first set in `setPrec` order, by rank). -/
def knapBestCell (kCS : Nat) (L : KLayer) (cap : Nat) : Option (_root_.Int × Nat × _root_.Int) :=
  (List.range (cap + 1)).foldl (fun acc c =>
    (L.delta[c]!).elim acc fun d =>
      let l : _root_.Int := d + (tag0Size (kCS + c) : _root_.Int)
      acc.elim (some (l, c, d)) fun b =>
        if l < b.1 || (l == b.1 && decide (L.rank[c]! < L.rank[b.2.1]!)) then some (l, c, d)
        else some b) none

/-- `knapChoose` on the fast layers. -/
def knapChooseFast (kCS cap : Nat) (tabs : Array CTable) (init : _root_.Int × Array Nat × Bool) :
    _root_.Int × Array Nat × Bool :=
  let r := knapRun cap tabs.toList
  (knapBestCell kCS r.1 cap).elim init fun b =>
    let s := knapReconFast tabs r.2 tabs.size b.2.1
    let l0 : _root_.Int := init.1 + (tag0Size (kCS + init.2.1.size) : _root_.Int)
    if b.1 < l0 || (b.1 == l0 && setPrec s init.2.1) then (b.2.2, s, true) else init

/-- Merge adjacent duplicates. -/
def dedupSorted : List Nat → List Nat
  | a :: b :: l => if a = b then dedupSorted (b :: l) else a :: dedupSorted (b :: l)
  | l => l

/-- The terms of a table's entries, ascending, without repeats (when it is
shaped). -/
def tableTerms (tab : CTable) : List Nat :=
  dedupSorted ((tab.toList.flatMap fun o => o.elim [] (·.2.toList)).mergeSort
    fun x y => decide (x ≤ y))

/-- Every entry of every table is an ascending list of its count's length, and
the terms of different tables are disjoint. -/
def tablesOK (tabs : Array CTable) : Bool :=
  tabs.all (fun tab => (List.range tab.size).all fun k =>
    (tab[k]!).elim true fun x => x.2.size == k && incList x.2.toList) &&
  incList ((tabs.toList.flatMap tableTerms).mergeSort fun x y => decide (x ≤ y))

/-- `uniformKnapsack` with the rank-based knapsack (module doc). -/
def uniformKnapsackFast (limits : Limits) (kCS : Nat) (results : Array CompResult) :
    Except SharingError (_root_.Int × Array Nat × Bool) := do
  let bestX := ((results.foldl (fun acc r => acc ++ r.bestSet) #[]).toList.mergeSort
    fun x y => decide (x ≤ y)).toArray
  let bestDelta := results.foldl (fun acc r => acc + r.bestDelta) (0 : _root_.Int)
  let start := tag0BracketStart (kCS + bestX.size)
  if start > kCS then
    let cap := start - 1 - kCS
    if (results.size + 1) * (cap + 1) > limits.maxKnapsackCells then
      throw (.resourceExhausted .knapsackCells limits.maxKnapsackCells)
    let tabs := results.map (·.bySize)
    if tablesOK tabs then
      pure (knapChooseFast kCS cap tabs (bestDelta, bestX, false))
    else
      let dp := results.foldl (fun dp r => knapStep cap dp r.bySize)
        (#[some (0, #[])] ++ Array.replicate cap none)
      pure (knapChoose kCS dp (bestDelta, bestX, false))
  else pure (bestDelta, bestX, false)

/-! ## Sorted merges and the guard -/

theorem incList_pairwise : ∀ (l : List Nat), incList l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => by simp
  | a :: b :: l, h => by
    have hlt := incList_lt a (b :: l) h
    have h2 : incList (b :: l) = true := by
      simp only [incList, Bool.and_eq_true] at h
      exact h.2
    exact List.pairwise_cons.mpr ⟨hlt, incList_pairwise (b :: l) h2⟩

theorem le_trans_dec (a b c : Nat) (h₁ : decide (a ≤ b) = true) (h₂ : decide (b ≤ c) = true) :
    decide (a ≤ c) = true := by
  simp only [decide_eq_true_eq] at *; omega

theorem le_total_dec (a b : Nat) : (decide (a ≤ b) || decide (b ≤ a)) = true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq]; omega

theorem mergeSorted_perm (a b : Array Nat) :
    (mergeSorted a b).toList.Perm (a.toList ++ b.toList) := by
  unfold mergeSorted
  exact List.mergeSort_perm _ _

theorem mem_mergeSorted {a b : Array Nat} {z : Nat} :
    z ∈ (mergeSorted a b).toList ↔ z ∈ a.toList ∨ z ∈ b.toList := by
  rw [(mergeSorted_perm a b).mem_iff, List.mem_append]

theorem mergeSorted_size (a b : Array Nat) : (mergeSorted a b).size = a.size + b.size := by
  rw [← Array.length_toList, (mergeSorted_perm a b).length_eq]
  simp

/-- An ascending list without repeats is strictly ascending. -/
theorem pairwise_lt_of_le {l : List Nat} (hle : l.Pairwise fun x y => decide (x ≤ y) = true)
    (hnd : l.Nodup) : l.Pairwise (· < ·) := by
  have := hle.and hnd
  exact this.imp fun ⟨h1, h2⟩ => by simp only [decide_eq_true_eq] at h1; omega

/-- The merge of two disjoint strictly ascending arrays is strictly ascending. -/
theorem mergeSorted_sorted {a b : Array Nat} (ha : a.toList.Pairwise (· < ·))
    (hb : b.toList.Pairwise (· < ·)) (hdisj : ∀ z ∈ a.toList, z ∉ b.toList) :
    (mergeSorted a b).toList.Pairwise (· < ·) := by
  apply pairwise_lt_of_le
  · unfold mergeSorted
    exact List.pairwise_mergeSort le_trans_dec le_total_dec _
  · apply List.Nodup.perm _ (mergeSorted_perm a b).symm
    exact List.nodup_append.mpr ⟨ha.imp Nat.ne_of_lt, hb.imp Nat.ne_of_lt,
      fun x hx y hy hxy => hdisj x hx (hxy ▸ hy)⟩

theorem firstDiff_comm {A B : List Nat} (hA : A.Pairwise (· < ·)) (hB : B.Pairwise (· < ·)) :
    firstDiff A B = firstDiff B A := by
  cases h : firstDiff A B with
  | none =>
    have := (firstDiff_none hA hB).mp h
    subst this
    exact h.symm
  | some m =>
    exact ((firstDiff_eq_some_iff hB hA).mpr ((firstDiff_eq_some_iff hA hB).mp h).symm).symm

theorem dedupSorted_mem : ∀ (l : List Nat) (z : Nat), z ∈ dedupSorted l ↔ z ∈ l
  | [], z => by simp [dedupSorted]
  | [a], z => by simp [dedupSorted]
  | a :: b :: l, z => by
    have ih := dedupSorted_mem (b :: l) z
    by_cases hab : a = b
    · subst hab
      simp only [dedupSorted, ite_true, ih, List.mem_cons]
      constructor
      · intro h; exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h
        · exact h
    · simp only [dedupSorted, hab, ite_false, List.mem_cons, ih]

/-- The terms of the entries of a table. -/
def InTable (tab : CTable) (z : Nat) : Prop :=
  ∃ k : Nat, ∃ x : _root_.Int × Array Nat, tab[k]! = some x ∧ z ∈ x.2.toList

/-- The terms of the first `j` tables. -/
def InPrev (tabs : Array CTable) (j z : Nat) : Prop := ∃ i, i < j ∧ InTable tabs[i]! z

theorem mem_tableTerms {tab : CTable} {z : Nat} (h : InTable tab z) : z ∈ tableTerms tab := by
  obtain ⟨k, x, hk, hz⟩ := h
  unfold tableTerms
  rw [dedupSorted_mem, List.mem_mergeSort, List.mem_flatMap]
  have hks : k < tab.size := by
    by_cases hk' : k < tab.size
    · exact hk'
    · rw [getElem!_neg tab k hk'] at hk; cases hk
  refine ⟨some x, ?_, by simpa using hz⟩
  rw [getElem!_pos tab k hks] at hk
  rw [← hk]
  exact Array.getElem_mem_toList hks

/-- The entries are shaped: ascending lists of their count's length. -/
theorem tablesOK_shape {tabs : Array CTable} (h : tablesOK tabs = true) {j : Nat}
    (hj : j < tabs.size) {k : Nat} {x : _root_.Int × Array Nat} (hx : tabs[j]![k]! = some x) :
    x.2.size = k ∧ x.2.toList.Pairwise (· < ·) := by
  unfold tablesOK at h
  rw [Bool.and_eq_true, Array.all_eq_true] at h
  have hj' := h.1 j hj
  rw [getElem!_pos tabs j hj] at hx
  have hks : k < tabs[j].size := by
    by_cases hk' : k < tabs[j].size
    · exact hk'
    · rw [getElem!_neg _ k hk'] at hx; cases hx
  rw [List.all_eq_true] at hj'
  have := hj' k (List.mem_range.mpr hks)
  rw [hx] at this
  simp only [Option.elim_some, Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1, incList_pairwise _ this.2⟩

/-- The terms of different tables are disjoint. -/
theorem tablesOK_disjoint {tabs : Array CTable} (h : tablesOK tabs = true) {i j : Nat}
    (hij : i < j) (hj : j < tabs.size) {z : Nat} (hi : InTable tabs[i]! z) :
    ¬ InTable tabs[j]! z := by
  intro hjz
  unfold tablesOK at h
  rw [Bool.and_eq_true] at h
  have hnd : (tabs.toList.flatMap tableTerms).Nodup := by
    have := (incList_pairwise _ h.2).imp Nat.ne_of_lt
    exact this.perm (List.mergeSort_perm _ _) (fun h => fun h' => h h'.symm)
  rw [List.Nodup, List.pairwise_flatMap] at hnd
  have hpw := List.pairwise_iff_getElem.mp hnd.2 i j (by simp; omega) (by simpa using hj) hij
  simp only [Array.getElem_toList] at hpw
  rw [getElem!_pos tabs i (by omega)] at hi
  rw [getElem!_pos tabs j hj] at hjz
  exact hpw z (mem_tableTerms hi) z (mem_tableTerms hjz) rfl

/-! ## The layer invariant -/

/-- A fast layer represents the specification's layer `dp` after the first `j`
tables, with the cells' sets `recon`. -/
structure LayerInv (cap : Nat) (tabs : Array CTable) (j : Nat)
    (dp : Array (Option (_root_.Int × Array Nat))) (L : KLayer) (recon : Nat → Array Nat) :
    Prop where
  size : dp.size = cap + 1
  cell : ∀ c, c ≤ cap → dp[c]! = (L.delta[c]!).map fun d => (d, recon c)
  sorted : ∀ c, c ≤ cap → (L.delta[c]!).isSome → (recon c).toList.Pairwise (· < ·)
  card : ∀ c, c ≤ cap → (L.delta[c]!).isSome → (recon c).size = c
  dom : ∀ c, c ≤ cap → (L.delta[c]!).isSome → ∀ z ∈ (recon c).toList, InPrev tabs j z
  rank : ∀ a b, a ≤ cap → b ≤ cap → (L.delta[a]!).isSome → (L.delta[b]!).isSome → a ≠ b →
    (L.rank[a]! < L.rank[b]! ↔ setPrec (recon a) (recon b) = true)
  fd : ∀ a b, a ≤ cap → b ≤ cap → (L.delta[a]!).isSome → (L.delta[b]!).isSome →
    L.rank[a]! < L.rank[b]! →
    firstDiff (recon a).toList (recon b).toList = some (sparseQuery L.sp L.rank[a]! L.rank[b]!)

/-- Sets of distinct nonempty cells differ (their sizes do). -/
theorem LayerInv.ne {cap : Nat} {tabs : Array CTable} {j : Nat} {dp} {L : KLayer} {recon}
    (h : LayerInv cap tabs j dp L recon) {a b : Nat} (ha : a ≤ cap) (hb : b ≤ cap)
    (hda : (L.delta[a]!).isSome) (hdb : (L.delta[b]!).isSome) (hab : a ≠ b) :
    recon a ≠ recon b := by
  intro he
  have := congrArg Array.size he
  rw [h.card a ha hda, h.card b hb hdb] at this
  exact hab this

theorem LayerInv.prevFD_eq {cap : Nat} {tabs : Array CTable} {j : Nat} {dp} {L : KLayer} {recon}
    (h : LayerInv cap tabs j dp L recon) {a b : Nat} (ha : a ≤ cap) (hb : b ≤ cap)
    (hda : (L.delta[a]!).isSome) (hdb : (L.delta[b]!).isSome) :
    prevFD L a b = firstDiff (recon a).toList (recon b).toList := by
  unfold prevFD
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl, (firstDiff_none (h.sorted a ha hda) (h.sorted a ha hda)).mpr rfl]
  · rw [ite_eq_right hab]
    rcases Nat.lt_trichotomy L.rank[a]! L.rank[b]! with hlt | heq | hgt
    · rw [Nat.min_eq_left (Nat.le_of_lt hlt), Nat.max_eq_right (Nat.le_of_lt hlt)]
      exact (h.fd a b ha hb hda hdb hlt).symm
    · exfalso
      have h1 := (h.rank a b ha hb hda hdb hab)
      have h2 := (h.rank b a hb ha hdb hda (fun e => hab e.symm))
      rw [heq] at h1 h2
      simp only [Nat.lt_irrefl, false_iff] at h1 h2
      rcases setPrec_total' (h.ne ha hb hda hdb hab) with h3 | h3
      · rw [h3] at h1; exact h1 rfl
      · rw [h3] at h2; exact h2 rfl
    · rw [Nat.min_eq_right (Nat.le_of_lt hgt), Nat.max_eq_left (Nat.le_of_lt hgt)]
      rw [firstDiff_comm (h.sorted a ha hda) (h.sorted b hb hdb)]
      exact (h.fd b a hb ha hdb hda hgt).symm

/-- The merged set of a candidate: cell `a`'s set with entry `k`. -/
def candSet (recon : Nat → Array Nat) (tab : CTable) (a k : Nat) : Array Nat :=
  mergeSorted (recon a) (entrySet tab k)

theorem minOpt_some {p q : Option Nat} {m : Nat} (h : minOpt p q = some m) :
    p = some m ∨ (q = some m ∧ ∀ p', p = some p' → m < p' ∨ m = p') := by
  cases p with
  | none => cases q with
    | none => simp [minOpt] at h
    | some b => simp only [minOpt] at h; exact Or.inr ⟨h, fun p' hp => by cases hp⟩
  | some a => cases q with
    | none => simp only [minOpt] at h; exact Or.inl h
    | some b =>
      simp only [minOpt, Option.some.injEq] at h
      by_cases hab : a ≤ b
      · rw [Nat.min_eq_left hab] at h; exact Or.inl (by rw [h])
      · rw [Nat.min_eq_right (by omega)] at h
        exact Or.inr ⟨by rw [h], fun p' hp => by cases hp; omega⟩

section Step

variable {cap : Nat} {tabs : Array CTable} {j : Nat} {dp : Array (Option (_root_.Int × Array Nat))}
  {L : KLayer} {recon : Nat → Array Nat}

theorem entrySet_shape (hok : tablesOK tabs = true) (hj : j < tabs.size) (k : Nat) :
    (entrySet tabs[j]! k).toList.Pairwise (· < ·) := by
  unfold entrySet
  cases hk : tabs[j]![k]! with
  | none => simp
  | some x => exact (tablesOK_shape hok hj hk).2

theorem entrySet_size (hok : tablesOK tabs = true) (hj : j < tabs.size) {k : Nat}
    (hk : (tabs[j]![k]!).isSome) : (entrySet tabs[j]! k).size = k := by
  unfold entrySet
  cases hk' : tabs[j]![k]! with
  | none => rw [hk'] at hk; cases hk
  | some x => exact (tablesOK_shape hok hj hk').1

theorem entrySet_inTable {tab : CTable} {k z : Nat} (h : z ∈ (entrySet tab k).toList) :
    InTable tab z := by
  unfold entrySet at h
  cases hk : tab[k]! with
  | none => rw [hk] at h; simp at h
  | some x => rw [hk] at h; exact ⟨k, x, hk, h⟩

/-- A term of the previous tables is not in the current table. -/
theorem notInTable_of_prev (hok : tablesOK tabs = true) (hj : j < tabs.size) {z : Nat}
    (hz : InPrev tabs j z) : ¬ InTable tabs[j]! z := by
  obtain ⟨i, hij, hi⟩ := hz
  exact tablesOK_disjoint hok hij hj hi

theorem candSet_sorted (hok : tablesOK tabs = true) (hj : j < tabs.size)
    (h : LayerInv cap tabs j dp L recon) {a k : Nat} (ha : a ≤ cap) (hda : (L.delta[a]!).isSome) :
    (candSet recon tabs[j]! a k).toList.Pairwise (· < ·) :=
  mergeSorted_sorted (h.sorted a ha hda) (entrySet_shape hok hj k)
    (fun z hz hz' => notInTable_of_prev hok hj (h.dom a ha hda z hz) (entrySet_inTable hz'))

theorem candFD_eq (hok : tablesOK tabs = true) (hj : j < tabs.size)
    (h : LayerInv cap tabs j dp L recon) {a ka b kb : Nat} (ha : a ≤ cap) (hb : b ≤ cap)
    (hda : (L.delta[a]!).isSome) (hdb : (L.delta[b]!).isSome) :
    candFD L tabs[j]! a ka b kb =
      firstDiff (candSet recon tabs[j]! a ka).toList (candSet recon tabs[j]! b kb).toList := by
  unfold candFD
  rw [h.prevFD_eq ha hb hda hdb]
  symm
  apply firstDiff_union (h.sorted a ha hda) (h.sorted b hb hdb) (entrySet_shape hok hj ka)
    (entrySet_shape hok hj kb) (candSet_sorted hok hj h ha hda) (candSet_sorted hok hj h hb hdb)
    (fun z => mem_mergeSorted) (fun z => mem_mergeSorted)
  intro z hz
  have hp : InPrev tabs j z := by
    rcases hz with hz | hz
    · exact h.dom a ha hda z hz
    · exact h.dom b hb hdb z hz
  exact ⟨fun hx => notInTable_of_prev hok hj hp (entrySet_inTable hx),
    fun hy => notInTable_of_prev hok hj hp (entrySet_inTable hy)⟩

theorem candPrec_eq (hok : tablesOK tabs = true) (hj : j < tabs.size)
    (h : LayerInv cap tabs j dp L recon) {a ka b kb : Nat} (ha : a ≤ cap) (hb : b ≤ cap)
    (hda : (L.delta[a]!).isSome) (hdb : (L.delta[b]!).isSome) :
    candPrec L tabs[j]! a ka b kb =
      setPrec (candSet recon tabs[j]! a ka) (candSet recon tabs[j]! b kb) := by
  have hU := candSet_sorted (k := ka) hok hj h ha hda
  have hV := candSet_sorted (k := kb) hok hj h hb hdb
  have hfd := candFD_eq (ka := ka) (kb := kb) hok hj h ha hb hda hdb
  apply Bool.eq_iff_iff.mpr
  rw [setPrec_iff hU hV]
  unfold candPrec
  rw [hfd]
  cases hm : firstDiff (candSet recon tabs[j]! a ka).toList (candSet recon tabs[j]! b kb).toList with
  | none => simp
  | some m =>
    simp only [Option.elim_some, Option.some.injEq, exists_eq_left']
    have hmfd := (firstDiff_eq_some_iff hU hV).mp hm
    -- where `m` comes from
    have hcand := hfd ▸ hm
    unfold candFD at hcand
    by_cases hpm : prevFD L a b = some m
    · simp only [hpm, beq_self_eq_true, ite_true, decide_eq_true_eq]
      have hab : a ≠ b := by intro e; subst e; simp [prevFD] at hpm
      rw [h.prevFD_eq ha hb hda hdb] at hpm
      have hrm := (firstDiff_eq_some_iff (h.sorted a ha hda) (h.sorted b hb hdb)).mp hpm
      have hmp : InPrev tabs j m := by
        by_cases hma : m ∈ (recon a).toList
        · exact h.dom a ha hda m hma
        · obtain ⟨hrm1, _⟩ := hrm
          apply h.dom b hb hdb m
          by_cases hmb : m ∈ (recon b).toList
          · exact hmb
          · exact absurd (hrm1.mpr hmb) hma
      have hmY : m ∉ (entrySet tabs[j]! kb).toList :=
        fun hy => notInTable_of_prev hok hj hmp (entrySet_inTable hy)
      rw [h.rank a b ha hb hda hdb hab, setPrec_iff (h.sorted a ha hda) (h.sorted b hb hdb), hpm]
      simp only [Option.some.injEq, exists_eq_left']
      unfold candSet
      rw [mem_mergeSorted]
      simp [hmY]
    · have hpm' : (prevFD L a b == some m) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact hpm
      simp only [hpm', Bool.false_eq_true, ite_false, Bool.not_eq_true']
      rcases minOpt_some hcand with hp | ⟨hq, _⟩
      · exact absurd hp hpm
      · have hxy := (firstDiff_eq_some_iff (entrySet_shape hok hj ka) (entrySet_shape hok hj kb)).mp hq
        obtain ⟨hxy1, _⟩ := hxy
        have hmT : InTable tabs[j]! m := by
          by_cases hmx : m ∈ (entrySet tabs[j]! ka).toList
          · exact entrySet_inTable hmx
          · apply entrySet_inTable (k := kb)
            by_cases hmy : m ∈ (entrySet tabs[j]! kb).toList
            · exact hmy
            · exact absurd (hxy1.mpr hmy) hmx
        have hmB : m ∉ (recon b).toList :=
          fun hb' => notInTable_of_prev hok hj (h.dom b hb hdb m hb') hmT
        unfold candSet
        rw [mem_mergeSorted]
        simp only [hmB, false_or]
        by_cases hx : m ∈ (entrySet tabs[j]! ka).toList
        · have hc : (entrySet tabs[j]! ka).contains m = true :=
            Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hx)
          rw [hc]
          simp only [Bool.true_eq_false, false_iff]
          exact hxy1.mp hx
        · have hc : (entrySet tabs[j]! ka).contains m = false := by
            cases hcc : (entrySet tabs[j]! ka).contains m
            · rfl
            · exact absurd (Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hcc)) hx
          rw [hc]
          simp only [true_iff]
          by_cases hy : m ∈ (entrySet tabs[j]! kb).toList
          · exact hy
          · exact absurd (hxy1.mpr hy) hx

/-- The value of a fast candidate: its Δ and merged set. -/
def candVal (recon : Nat → Array Nat) (tab : CTable) (x : _root_.Int × Nat × Nat) :
    _root_.Int × Array Nat :=
  (x.1, candSet recon tab x.2.1 x.2.2)

theorem candBetter_eq (hok : tablesOK tabs = true) (hj : j < tabs.size)
    (h : LayerInv cap tabs j dp L recon) {x y : _root_.Int × Nat × Nat}
    (hx : x.2.1 ≤ cap ∧ (L.delta[x.2.1]!).isSome) (hy : y.2.1 ≤ cap ∧ (L.delta[y.2.1]!).isSome) :
    candBetter L tabs[j]! x y = entryLt (candVal recon tabs[j]! x) (candVal recon tabs[j]! y) := by
  unfold candBetter entryLt candVal
  rw [candPrec_eq hok hj h hx.1 hy.1 hx.2 hy.2]

theorem mem_cellCands {tab : CTable} {t : Nat} {x : _root_.Int × Nat × Nat} :
    x ∈ cellCands L tab t ↔ ∃ k xk da, k ≤ t ∧ k < tab.size ∧ tab[k]! = some xk ∧
      L.delta[t - k]! = some da ∧ x = (da + xk.1, t - k, k) := by
  unfold cellCands
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [List.mem_range] at hk
    cases htk : tab[k]! with
    | none => rw [htk] at hx; cases hx
    | some xk =>
      rw [htk] at hx
      cases hd : L.delta[t - k]! with
      | none => rw [hd] at hx; simp at hx
      | some da =>
        rw [hd] at hx
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hx
        have hks : k < tab.size := by
          by_cases hk' : k < tab.size
          · exact hk'
          · rw [getElem!_neg tab k hk'] at htk; cases htk
        exact ⟨k, xk, da, by omega, hks, htk, hd, hx.symm⟩
  · rintro ⟨k, xk, da, hkt, hks, htk, hd, rfl⟩
    refine ⟨k, List.mem_range.mpr (by omega), ?_⟩
    rw [htk, Option.bind_some, hd]
    rfl

theorem cellCands_ok {tab : CTable} {t : Nat} (ht : t ≤ cap) {x : _root_.Int × Nat × Nat}
    (hx : x ∈ cellCands L tab t) : x.2.1 ≤ cap ∧ (L.delta[x.2.1]!).isSome := by
  obtain ⟨k, xk, da, hkt, _, _, hd, rfl⟩ := mem_cellCands.mp hx
  exact ⟨by simp; omega, by simp [hd]⟩

/-- The specification's candidates of target `t` are the values of the fast
candidates. -/
theorem specCands_iff (h : LayerInv cap tabs j dp L recon) {tab : CTable} {t : Nat} (ht : t ≤ cap)
    (v : _root_.Int × Array Nat) :
    v ∈ ((List.range dp.size).flatMap fun c =>
        (dp[c]!).elim [] fun e => srcCands cap c e tab tab.size t) ↔
      ∃ x ∈ cellCands L tab t, candVal recon tab x = v := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hv⟩
    rw [List.mem_range, h.size] at hc
    rw [h.cell c (by omega)] at hv
    cases hd : L.delta[c]! with
    | none => rw [hd] at hv; simp at hv
    | some d =>
      rw [hd] at hv
      simp only [Option.map_some, Option.elim_some] at hv
      unfold srcCands at hv
      split at hv
      · rename_i hcond
        cases htk : tab[t - c]! with
        | none => rw [htk] at hv; simp at hv
        | some xk =>
          rw [htk] at hv
          simp only [Option.elim_some, List.mem_singleton] at hv
          subst hv
          refine ⟨(d + xk.1, c, t - c), mem_cellCands.mpr ⟨t - c, xk, d, by omega, hcond.2.1,
            htk, by rw [show t - (t - c) = c by omega]; exact hd, by rw [show t - (t - c) = c by omega]⟩, ?_⟩
          unfold candVal candSet knapCand entrySet
          rw [htk]
          rfl
      · simp at hv
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, xk, da, hkt, hks, htk, hd, rfl⟩ := mem_cellCands.mp hx
    refine ⟨t - k, List.mem_range.mpr (by rw [h.size]; omega), ?_⟩
    rw [h.cell (t - k) (by omega), hd]
    simp only [Option.map_some, Option.elim_some]
    unfold srcCands
    have hcond : t - k ≤ t ∧ t - (t - k) < tab.size ∧ t ≤ cap := ⟨by omega, by omega, ht⟩
    rw [ite_eq_left hcond, show t - (t - k) = k by omega, htk]
    simp only [Option.elim_some, List.mem_singleton]
    unfold candVal candSet knapCand entrySet
    rw [htk]
    rfl

/-- Cell `t` of the next layer: the fast best candidate's value is the
specification's cell. -/
theorem cell_step (hok : tablesOK tabs = true) (hj : j < tabs.size)
    (h : LayerInv cap tabs j dp L recon) {t : Nat} (ht : t ≤ cap) :
    (knapStep cap dp tabs[j]!)[t]! = (cellBest L tabs[j]! t).map (candVal recon tabs[j]!) := by
  rw [(knapStep_get cap dp tabs[j]!).2 t ht]
  have hspec := foldl_least (fun _ => True) id entryLt entryLt_irrefl (fun _ _ _ => entryLt_trans)
    betterStep (fun x => by simp [betterStep, betterEntry])
    (fun a x _ _ => by simp only [betterStep, betterEntry_some, id])
    ((List.range dp.size).flatMap fun c => (dp[c]!).elim [] fun e => srcCands cap c e tabs[j]! tabs[j]!.size t)
    none (fun _ _ => trivial) (fun _ _ => trivial)
  have hfast := foldl_least (fun x => x.2.1 ≤ cap ∧ (L.delta[x.2.1]!).isSome)
    (candVal recon tabs[j]!) entryLt entryLt_irrefl (fun _ _ _ => entryLt_trans)
    (candStep L tabs[j]!) (fun x => rfl)
    (fun a x ha hx => by
      simp only [candStep, Option.elim_some]
      rw [candBetter_eq hok hj h hx ha])
    (cellCands L tabs[j]! t) none (fun x hx => cellCands_ok ht hx) (fun _ h => by cases h)
  obtain ⟨hsn, hss⟩ := hspec
  obtain ⟨hfn, hfs⟩ := hfast
  unfold cellBest
  cases hfr : (cellCands L tabs[j]! t).foldl (candStep L tabs[j]!) none with
  | none =>
    have hnil := (hfn.mp hfr).2
    rw [Option.map_none]
    apply hsn.mpr
    refine ⟨rfl, ?_⟩
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    obtain ⟨x, hx, _⟩ := (specCands_iff h ht v).mp hv
    rw [hnil] at hx
    simp at hx
  | some m =>
    obtain ⟨hmem, hle, _⟩ := hfs m hfr
    have hmL : m ∈ cellCands L tabs[j]! t := by
      rcases hmem with h' | h'
      · exact h'
      · cases h'
    rw [Option.map_some]
    cases hsr : ((List.range dp.size).flatMap fun c =>
        (dp[c]!).elim [] fun e => srcCands cap c e tabs[j]! tabs[j]!.size t).foldl betterStep none with
    | none =>
      exfalso
      have hnil := (hsn.mp hsr).2
      have := (specCands_iff h ht (candVal recon tabs[j]! m)).mpr ⟨m, hmL, rfl⟩
      rw [hnil] at this
      simp at this
    | some v =>
      obtain ⟨hvmem, hvle, _⟩ := hss v hsr
      have hvL : v ∈ ((List.range dp.size).flatMap fun c =>
          (dp[c]!).elim [] fun e => srcCands cap c e tabs[j]! tabs[j]!.size t) := by
        rcases hvmem with h' | h'
        · exact h'
        · cases h'
      congr 1
      apply least_unique entryLt (fun x y hxy => entryLt_total hxy) hvL
        ((specCands_iff h ht _).mpr ⟨m, hmL, rfl⟩) hvle
      intro w hw
      obtain ⟨x, hx, rfl⟩ := (specCands_iff h ht w).mp hw
      exact hle x hx

theorem cellBest_mem (hok : tablesOK tabs = true) (hj : j < tabs.size)
    (h : LayerInv cap tabs j dp L recon) {t : Nat} (ht : t ≤ cap) {x : _root_.Int × Nat × Nat}
    (hx : cellBest L tabs[j]! t = some x) : x ∈ cellCands L tabs[j]! t := by
  have hfast := foldl_least (fun x => x.2.1 ≤ cap ∧ (L.delta[x.2.1]!).isSome)
    (candVal recon tabs[j]!) entryLt entryLt_irrefl (fun _ _ _ => entryLt_trans)
    (candStep L tabs[j]!) (fun x => rfl)
    (fun a x ha hx => by
      simp only [candStep, Option.elim_some]
      rw [candBetter_eq hok hj h hx ha])
    (cellCands L tabs[j]! t) none (fun x hx => cellCands_ok ht hx) (fun _ h => by cases h)
  rcases (hfast.2 x hx).1 with h' | h'
  · exact h'
  · cases h'

end Step

theorem rankOf_aux (n : Nat) :
    ∀ (l : List Nat) (s : Nat) (A : Array Nat), l.Nodup → A.size = n →
      ((l.zipIdx s).foldl (fun rk p => rk.set! p.1 p.2) A).size = n ∧
      ∀ x, x < n → ((l.zipIdx s).foldl (fun rk p => rk.set! p.1 p.2) A)[x]! =
        if x ∈ l then l.idxOf x + s else A[x]! := by
  intro l
  induction l with
  | nil => intro s A _ hA; simp [hA]
  | cons a l ih =>
    intro s A hnd hA
    rw [List.nodup_cons] at hnd
    simp only [List.zipIdx_cons, List.foldl_cons]
    obtain ⟨hsz, hval⟩ := ih (s + 1) (A.set! a s) hnd.2 (by simp [hA])
    refine ⟨hsz, fun x hx => ?_⟩
    rw [hval x hx]
    by_cases hxa : x = a
    · subst hxa
      simp only [hnd.1, ite_false, List.mem_cons_self, ite_true, List.idxOf_cons_self]
      rw [getElem!_set!_self' _ _ _ (by omega)]
      omega
    · have hax : (a == x) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hxa h.symm
      rw [getElem!_set!_ne' _ _ _ _ (fun h => hxa h.symm)]
      by_cases hxl : x ∈ l
      · simp only [hxl, ite_true, List.mem_cons, hxa, false_or, List.idxOf_cons, hax, cond_false]
        omega
      · simp only [hxl, ite_false, List.mem_cons, hxa, false_or]

theorem rankOf_get {n : Nat} {l : List Nat} (hnd : l.Nodup) {x : Nat} (hx : x < n) (hxl : x ∈ l) :
    (rankOf n l)[x]! = l.idxOf x := by
  unfold rankOf
  rw [(rankOf_aux n l 0 (Array.replicate n 0) hnd (by simp)).2 x hx, ite_eq_left hxl]
  rfl

/-! ## Ranks of the next layer -/

/-- Sorting cells by a comparator that is `setPrec` on their (distinct) sets
puts the sets in `setPrec` order. -/
theorem mergeSort_setPrec (S : Nat → Array Nat) (cells : List Nat) (r : Nat → Nat → Bool)
    (hr : ∀ u ∈ cells, ∀ v ∈ cells, r u v = !setPrec (S v) (S u))
    (hdist : ∀ u ∈ cells, ∀ v ∈ cells, u ≠ v → S u ≠ S v) (hnd : cells.Nodup) :
    ∀ i k (hi : i < k) (hk : k < (cells.mergeSort r).length),
      setPrec (S (cells.mergeSort r)[i]) (S (cells.mergeSort r)[k]) = true := by
  intro i k hik hk
  let s : Array Nat → Array Nat → Bool := fun A B => !setPrec B A
  have hmap : (cells.mergeSort r).map S = (cells.map S).mergeSort s :=
    List.map_mergeSort (fun a ha b hb => hr a ha b hb)
  have htrans : ∀ A B C, s A B = true → s B C = true → s A C = true := by
    intro A B C h1 h2
    simp only [s, Bool.not_eq_true'] at *
    cases h3 : setPrec C A
    · rfl
    · exfalso
      by_cases hAB : A = B
      · subst hAB; rw [h2] at h3; cases h3
      · rcases setPrec_total' hAB with h4 | h4
        · rw [setPrec_trans' h3 h4] at h2; cases h2
        · rw [h4] at h1; cases h1
  have htotal : ∀ A B, (s A B || s B A) = true := by
    intro A B
    simp only [s, Bool.or_eq_true, Bool.not_eq_true']
    cases h : setPrec B A
    · exact Or.inl rfl
    · exact Or.inr (setPrec_asymm' h)
  have hpw := List.pairwise_mergeSort htrans htotal (cells.map S)
  rw [← hmap, List.pairwise_map] at hpw
  have hord := (List.pairwise_iff_getElem.mp hpw) i k (by omega) hk hik
  simp only [s, Bool.not_eq_true'] at hord
  have hndo : (cells.mergeSort r).Nodup := hnd.perm (List.mergeSort_perm cells r).symm
  have hne : (cells.mergeSort r)[i] ≠ (cells.mergeSort r)[k] := by
    intro he
    have := (List.getElem_inj hndo).mp he
    omega
  have hmi : (cells.mergeSort r)[i] ∈ cells :=
    List.mem_mergeSort.mp (List.getElem_mem (by omega))
  have hmk : (cells.mergeSort r)[k] ∈ cells := List.mem_mergeSort.mp (List.getElem_mem hk)
  rcases setPrec_total' (hdist _ hmi _ hmk hne) with h | h
  · exact h
  · rw [h] at hord; cases hord

/-! ## One layer -/

/-- The sets of the next layer: the previous cell's set with the entry taken. -/
def reconNext (recon : Nat → Array Nat) (tab : CTable) (took : Array Nat) (t : Nat) : Array Nat :=
  candSet recon tab (t - took[t]!) took[t]!

theorem knapBest_get {cap : Nat} {L : KLayer} {tab : CTable} {t : Nat} (ht : t ≤ cap) :
    (knapBest cap L tab)[t]! = cellBest L tab t := by
  unfold knapBest
  rw [getElem!_pos _ t (by simp; omega)]
  simp

theorem knapTook_get {best : Array (Option (_root_.Int × Nat × Nat))} {t : Nat}
    (ht : t < best.size) : (knapTook best)[t]! = (best[t]!).elim 0 (·.2.2) := by
  unfold knapTook
  rw [getElem!_pos _ t (by simpa using ht), getElem!_pos _ t ht]
  simp

theorem knapDelta_get {best : Array (Option (_root_.Int × Nat × Nat))} {t : Nat}
    (ht : t < best.size) : (best.map (·.map (·.1)))[t]! = (best[t]!).map (·.1) := by
  rw [getElem!_pos _ t (by simpa using ht), getElem!_pos _ t ht]
  simp

section Layer

variable {cap : Nat} {tabs : Array CTable} {j : Nat} {dp : Array (Option (_root_.Int × Array Nat))}
  {L : KLayer} {recon : Nat → Array Nat}

/-- What a nonempty cell of the next layer took: an entry `k ≤ t` present in the
table, from a nonempty cell `t - k` of the previous layer. -/
theorem cellBest_shape (hok : tablesOK tabs = true) (hj : j < tabs.size)
    (h : LayerInv cap tabs j dp L recon) {t : Nat} (ht : t ≤ cap) {x : _root_.Int × Nat × Nat}
    (hx : cellBest L tabs[j]! t = some x) :
    x.2.2 ≤ t ∧ x.2.1 = t - x.2.2 ∧ (tabs[j]![x.2.2]!).isSome ∧ (L.delta[t - x.2.2]!).isSome := by
  obtain ⟨k, xk, da, hkt, _, htk, hd, rfl⟩ := mem_cellCands.mp (cellBest_mem hok hj h ht hx)
  exact ⟨hkt, rfl, by simp [htk], by simp [hd]⟩

theorem knapLayer_inv (hok : tablesOK tabs = true) (hj : j < tabs.size)
    (h : LayerInv cap tabs j dp L recon) :
    LayerInv cap tabs (j + 1) (knapStep cap dp tabs[j]!) (knapLayer cap L tabs[j]!).1
      (reconNext recon tabs[j]! (knapLayer cap L tabs[j]!).2) := by
  -- names for the parts of the next layer
  have hbsz : (knapBest cap L tabs[j]!).size = cap + 1 := by simp [knapBest]
  have hdelta : ∀ t, t ≤ cap → (knapLayer cap L tabs[j]!).1.delta[t]! =
      (cellBest L tabs[j]! t).map (·.1) := by
    intro t ht
    show ((knapBest cap L tabs[j]!).map (·.map (·.1)))[t]! = _
    rw [knapDelta_get (by omega), knapBest_get ht]
  have htook : ∀ t, t ≤ cap → (knapLayer cap L tabs[j]!).2[t]! =
      (cellBest L tabs[j]! t).elim 0 (·.2.2) := by
    intro t ht
    show (knapTook (knapBest cap L tabs[j]!))[t]! = _
    rw [knapTook_get (by omega), knapBest_get ht]
  -- a nonempty cell of the next layer
  have hnon : ∀ t, t ≤ cap → ((knapLayer cap L tabs[j]!).1.delta[t]!).isSome →
      ∃ x, cellBest L tabs[j]! t = some x ∧ (knapLayer cap L tabs[j]!).2[t]! = x.2.2 := by
    intro t ht hs
    rw [hdelta t ht] at hs
    cases hb : cellBest L tabs[j]! t with
    | none => rw [hb] at hs; cases hs
    | some x => exact ⟨x, rfl, by rw [htook t ht, hb]; rfl⟩
  have hcandVal : ∀ t, t ≤ cap → ∀ x, cellBest L tabs[j]! t = some x →
      candVal recon tabs[j]! x = (x.1, reconNext recon tabs[j]! (knapLayer cap L tabs[j]!).2 t) := by
    intro t ht x hx
    obtain ⟨_, h2, _, _⟩ := cellBest_shape hok hj h ht hx
    have hk : (knapLayer cap L tabs[j]!).2[t]! = x.2.2 := by rw [htook t ht, hx]; rfl
    unfold candVal reconNext
    rw [hk, ← h2]
  have hprev : ∀ t, t ≤ cap → ((knapLayer cap L tabs[j]!).1.delta[t]!).isSome →
      t - (knapLayer cap L tabs[j]!).2[t]! ≤ cap ∧
      (L.delta[t - (knapLayer cap L tabs[j]!).2[t]!]!).isSome ∧
      (knapLayer cap L tabs[j]!).2[t]! ≤ t ∧
      (tabs[j]![(knapLayer cap L tabs[j]!).2[t]!]!).isSome := by
    intro t ht hs
    obtain ⟨x, hx, hk⟩ := hnon t ht hs
    obtain ⟨h1, _, h3, h4⟩ := cellBest_shape hok hj h ht hx
    rw [hk]
    exact ⟨by omega, h4, h1, h3⟩
  have hsorted : ∀ t, t ≤ cap → ((knapLayer cap L tabs[j]!).1.delta[t]!).isSome →
      (reconNext recon tabs[j]! (knapLayer cap L tabs[j]!).2 t).toList.Pairwise (· < ·) := by
    intro t ht hs
    obtain ⟨h1, h2, _, _⟩ := hprev t ht hs
    exact candSet_sorted hok hj h h1 h2
  have hcard : ∀ t, t ≤ cap → ((knapLayer cap L tabs[j]!).1.delta[t]!).isSome →
      (reconNext recon tabs[j]! (knapLayer cap L tabs[j]!).2 t).size = t := by
    intro t ht hs
    obtain ⟨h1, h2, h3, h4⟩ := hprev t ht hs
    unfold reconNext candSet
    rw [mergeSorted_size, h.card _ h1 h2, entrySet_size hok hj h4]
    omega
  -- comparisons of next-layer cells are `setPrec` on their sets
  have hprec : ∀ u v, u ≤ cap → v ≤ cap → ((knapLayer cap L tabs[j]!).1.delta[u]!).isSome →
      ((knapLayer cap L tabs[j]!).1.delta[v]!).isSome →
      candPrec L tabs[j]! (u - (knapLayer cap L tabs[j]!).2[u]!) (knapLayer cap L tabs[j]!).2[u]!
        (v - (knapLayer cap L tabs[j]!).2[v]!) (knapLayer cap L tabs[j]!).2[v]! =
      setPrec (reconNext recon tabs[j]! (knapLayer cap L tabs[j]!).2 u)
        (reconNext recon tabs[j]! (knapLayer cap L tabs[j]!).2 v) := by
    intro u v hu hv hsu hsv
    obtain ⟨hu1, hu2, _, _⟩ := hprev u hu hsu
    obtain ⟨hv1, hv2, _, _⟩ := hprev v hv hsv
    exact candPrec_eq hok hj h hu1 hv1 hu2 hv2
  have hdist : ∀ u v, u ≤ cap → v ≤ cap → ((knapLayer cap L tabs[j]!).1.delta[u]!).isSome →
      ((knapLayer cap L tabs[j]!).1.delta[v]!).isSome → u ≠ v →
      reconNext recon tabs[j]! (knapLayer cap L tabs[j]!).2 u ≠
        reconNext recon tabs[j]! (knapLayer cap L tabs[j]!).2 v := by
    intro u v hu hv hsu hsv huv he
    have := congrArg Array.size he
    rw [hcard u hu hsu, hcard v hv hsv] at this
    exact huv this
  -- the sorted order of the next layer's cells
  generalize hS : reconNext recon tabs[j]! (knapLayer cap L tabs[j]!).2 = S at *
  generalize hbest : knapBest cap L tabs[j]! = best at hbsz
  have hL1 : (knapLayer cap L tabs[j]!).1 =
      { delta := best.map (·.map (·.1)),
        rank := rankOf (cap + 1) (knapOrd cap L tabs[j]! best (knapTook best)),
        sp := sparseBuild (knapAdj L tabs[j]! (knapTook best) (knapOrd cap L tabs[j]! best (knapTook best))) } := by
    rw [← hbest]; rfl
  have hL2 : (knapLayer cap L tabs[j]!).2 = knapTook best := by rw [← hbest]; rfl
  generalize hcells : (List.range (cap + 1)).filter (fun c => (best[c]!).isSome) = cells
  have hord : knapOrd cap L tabs[j]! best (knapTook best) = cells.mergeSort fun u v =>
      !candPrec L tabs[j]! (v - (knapTook best)[v]!) (knapTook best)[v]!
        (u - (knapTook best)[u]!) (knapTook best)[u]! := by
    rw [← hcells]; rfl
  have hmemc : ∀ c, c ∈ cells ↔ c ≤ cap ∧ ((knapLayer cap L tabs[j]!).1.delta[c]!).isSome := by
    intro c
    rw [← hcells, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      have hc : c ≤ cap := by omega
      refine ⟨hc, ?_⟩
      rw [hdelta c hc, ← knapBest_get hc, hbest]
      simpa using h2
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      rw [hdelta c h1, ← knapBest_get h1, hbest] at h2
      simpa using h2
  have hndc : cells.Nodup := by
    rw [← hcells]; exact (List.nodup_range).filter _
  generalize hordv : knapOrd cap L tabs[j]! best (knapTook best) = ord at hL1 hord
  have hsetPrec := mergeSort_setPrec S cells (fun u v =>
      !candPrec L tabs[j]! (v - (knapTook best)[v]!) (knapTook best)[v]!
        (u - (knapTook best)[u]!) (knapTook best)[u]!)
    (fun u hu v hv => by
      obtain ⟨hu1, hu2⟩ := (hmemc u).mp hu
      obtain ⟨hv1, hv2⟩ := (hmemc v).mp hv
      rw [← hL2, hprec v u hv1 hu1 hv2 hu2])
    (fun u hu v hv huv => by
      obtain ⟨hu1, hu2⟩ := (hmemc u).mp hu
      obtain ⟨hv1, hv2⟩ := (hmemc v).mp hv
      exact hdist u v hu1 hv1 hu2 hv2 huv)
    hndc
  have hsetPrec' : ∀ i k (hi : i < k) (hk : k < ord.length), setPrec (S ord[i]) (S ord[k]) = true := by
    rw [hord]; exact hsetPrec
  have hndo : ord.Nodup := by
    rw [hord]; exact hndc.perm (List.mergeSort_perm _ _).symm
  have hmemo : ∀ c, c ∈ ord ↔ c ∈ cells := by
    intro c; rw [hord, List.mem_mergeSort]
  have hrank : ∀ c, c ∈ ord → (knapLayer cap L tabs[j]!).1.rank[c]! = ord.idxOf c := by
    intro c hc
    rw [hL1]
    exact rankOf_get hndo (by have := ((hmemc c).mp ((hmemo c).mp hc)).1; omega) hc
  refine {
    size := (knapStep_get cap dp tabs[j]!).1
    cell := fun t ht => ?_
    sorted := hsorted
    card := hcard
    dom := fun t ht hs z hz => ?_
    rank := fun a b ha hb hsa hsb hab => ?_
    fd := fun a b ha hb hsa hsb hlt => ?_ }
  · -- the cells
    rw [cell_step hok hj h ht, hdelta t ht]
    cases hb : cellBest L tabs[j]! t with
    | none => rfl
    | some x =>
      simp only [Option.map_some]
      rw [hcandVal t ht x hb]
  · -- the domain
    obtain ⟨h1, h2, _, _⟩ := hprev t ht hs
    rw [← hS] at hz
    unfold reconNext candSet at hz
    rcases mem_mergeSorted.mp hz with hz | hz
    · obtain ⟨i, hi, hiz⟩ := h.dom _ h1 h2 z hz
      exact ⟨i, by omega, hiz⟩
    · exact ⟨j, by omega, entrySet_inTable hz⟩
  · -- ranks
    have hao : a ∈ ord := (hmemo a).mpr ((hmemc a).mpr ⟨ha, hsa⟩)
    have hbo : b ∈ ord := (hmemo b).mpr ((hmemc b).mpr ⟨hb, hsb⟩)
    rw [hrank a hao, hrank b hbo]
    have hia := List.idxOf_lt_length_of_mem hao
    have hib := List.idxOf_lt_length_of_mem hbo
    have ea : ord[ord.idxOf a] = a := List.getElem_idxOf hia
    have eb : ord[ord.idxOf b] = b := List.getElem_idxOf hib
    constructor
    · intro hlt
      have := hsetPrec' _ _ hlt hib
      rwa [ea, eb] at this
    · intro hp
      rcases Nat.lt_trichotomy (ord.idxOf a) (ord.idxOf b) with hlt | heq | hgt
      · exact hlt
      · exfalso; apply hab; rw [← ea, ← eb]; simp only [heq]
      · exfalso
        have := hsetPrec' _ _ hgt hia
        rw [ea, eb] at this
        rw [setPrec_asymm' this] at hp
        cases hp
  · -- first differences through the sparse table
    have hao : a ∈ ord := (hmemo a).mpr ((hmemc a).mpr ⟨ha, hsa⟩)
    have hbo : b ∈ ord := (hmemo b).mpr ((hmemc b).mpr ⟨hb, hsb⟩)
    rw [hrank a hao, hrank b hbo] at hlt ⊢
    have hia := List.idxOf_lt_length_of_mem hao
    have hib := List.idxOf_lt_length_of_mem hbo
    have ea : ord[ord.idxOf a] = a := List.getElem_idxOf hia
    have eb : ord[ord.idxOf b] = b := List.getElem_idxOf hib
    -- every cell of the order is a nonempty cell
    have hcell : ∀ m (hm : m < ord.length), ord[m] ≤ cap ∧
        ((knapLayer cap L tabs[j]!).1.delta[ord[m]]!).isSome :=
      fun m hm => (hmemc _).mp ((hmemo _).mp (List.getElem_mem hm))
    have hordA : ∀ m (hm : m < ord.length), ord.toArray[m]! = ord[m] := by
      intro m hm
      rw [getElem!_pos _ m (by simpa using hm)]
      simp
    have hadjsz : (knapAdj L tabs[j]! (knapTook best) ord).size = ord.length - 1 := by
      simp [knapAdj]
    have hadj : ∀ m (hm : m + 1 < ord.length),
        firstDiff (S ord[m]).toList (S ord[m + 1]).toList =
          some (knapAdj L tabs[j]! (knapTook best) ord)[m]! ∧
        (knapAdj L tabs[j]! (knapTook best) ord)[m]! ∈ (S ord[m + 1]).toList := by
      intro m hm
      obtain ⟨hu1, hu2⟩ := hcell m (by omega)
      obtain ⟨hv1, hv2⟩ := hcell (m + 1) hm
      have hp := hsetPrec' m (m + 1) (by omega) hm
      obtain ⟨d, hd1, hd2⟩ := (setPrec_iff (hsorted _ hu1 hu2) (hsorted _ hv1 hv2)).mp hp
      have hval : (knapAdj L tabs[j]! (knapTook best) ord)[m]! = d := by
        unfold knapAdj
        rw [getElem!_pos _ m (by simp; omega)]
        simp only [Array.getElem_map, Array.getElem_range]
        rw [hordA m (by omega), hordA (m + 1) hm, ← hL2]
        obtain ⟨hp1, hp2, _, _⟩ := hprev _ hu1 hu2
        obtain ⟨hq1, hq2, _, _⟩ := hprev _ hv1 hv2
        rw [candFD_eq hok hj h hp1 hq1 hp2 hq2]
        have e1 : candSet recon tabs[j]! (ord[m] - (knapLayer cap L tabs[j]!).2[ord[m]]!)
            (knapLayer cap L tabs[j]!).2[ord[m]]! = S ord[m] := by rw [← hS]; rfl
        have e2 : candSet recon tabs[j]! (ord[m + 1] - (knapLayer cap L tabs[j]!).2[ord[m + 1]]!)
            (knapLayer cap L tabs[j]!).2[ord[m + 1]]! = S ord[m + 1] := by rw [← hS]; rfl
        rw [e1, e2, hd1]
        rfl
      rw [hval]
      exact ⟨hd1, hd2⟩
    have hchain := firstDiff_chain (sets := fun m => (S ord.toArray[m]!).toList)
      (d := fun m => (knapAdj L tabs[j]! (knapTook best) ord)[m]!) (n := ord.length)
      (fun m hm => by
        rw [hordA m hm]
        obtain ⟨h1, h2⟩ := hcell m hm
        exact hsorted _ h1 h2)
      (fun m hm => by
        rw [hordA m (by omega), hordA (m + 1) hm]
        exact hadj m hm)
      (ord.idxOf b - ord.idxOf a - 1) (ord.idxOf a) (by omega)
    have e : ord.idxOf a + (ord.idxOf b - ord.idxOf a - 1) + 1 = ord.idxOf b := by omega
    rw [e, hordA _ hia, hordA _ hib, ea, eb] at hchain
    rw [hchain.1, hL1]
    simp only
    rw [sparseQuery_eq _ hlt (by rw [hadjsz]; omega)]

end Layer

/-! ## All layers -/

theorem knapInit_inv (cap : Nat) (tabs : Array CTable) (recon : Nat → Array Nat)
    (hr : recon 0 = #[]) :
    LayerInv cap tabs 0 (#[some (0, #[])] ++ Array.replicate cap none) (knapInit cap) recon := by
  have hdel : ∀ c, c ≤ cap → (knapInit cap).delta[c]! = if c = 0 then some 0 else none := by
    intro c hc
    unfold knapInit
    simp only
    rw [getElem!_pos _ c (by simp; omega)]
    by_cases h0 : c = 0
    · subst h0; simp
    · simp only [h0, ite_false]
      rw [Array.getElem_append_right (by simp; omega)]
      simp
  have hnon : ∀ c, c ≤ cap → ((knapInit cap).delta[c]!).isSome → c = 0 := by
    intro c hc hs
    rw [hdel c hc] at hs
    by_cases h0 : c = 0
    · exact h0
    · simp [h0] at hs
  refine {
    size := by simp; omega
    cell := fun c hc => ?_
    sorted := fun c hc hs => by rw [hnon c hc hs, hr]; simp
    card := fun c hc hs => by rw [hnon c hc hs, hr]; rfl
    dom := fun c hc hs z hz => by rw [hnon c hc hs, hr] at hz; simp at hz
    rank := fun a b ha hb hsa hsb hab => absurd ((hnon a ha hsa).trans (hnon b hb hsb).symm) hab
    fd := fun a b ha hb hsa hsb hlt => ?_ }
  · rw [hdel c hc, getElem!_pos _ c (by simp; omega)]
    by_cases h0 : c = 0
    · subst h0; simp [hr]
    · simp only [h0, ite_false, Option.map_none]
      rw [Array.getElem_append_right (by simp; omega)]
      simp
  · have := hnon a ha hsa
    have := hnon b hb hsb
    subst a; subst b
    exact absurd hlt (Nat.lt_irrefl _)

theorem knapRecon_push (tabs : Array CTable) (tooks : Array (Array Nat)) (took : Array Nat) :
    ∀ j c, j ≤ tooks.size → knapRecon tabs (tooks.push took) j c = knapRecon tabs tooks j c := by
  intro j
  induction j with
  | zero => intro c _; rfl
  | succ j ih =>
    intro c hj
    simp only [knapRecon]
    have e : (tooks.push took)[j]! = tooks[j]! := by
      rw [getElem!_pos _ j (by simp; omega), getElem!_pos _ j (by omega)]
      simp [Array.getElem_push_lt (by omega : j < tooks.size)]
    rw [e, ih _ (by omega)]

/-- The run over the tables `l` (the tables from `j` on) keeps the invariant. -/
theorem knapRun_inv {cap : Nat} {tabs : Array CTable} (hok : tablesOK tabs = true) :
    ∀ (l : List CTable) (j : Nat) (dp : Array (Option (_root_.Int × Array Nat))) (L : KLayer)
      (tooks : Array (Array Nat)),
      l = tabs.toList.drop j → j ≤ tabs.size → tooks.size = j →
      LayerInv cap tabs j dp L (knapRecon tabs tooks j) →
      LayerInv cap tabs tabs.size (l.foldl (fun dp tab => knapStep cap dp tab) dp)
        (l.foldl (fun acc tab => let r := knapLayer cap acc.1 tab; (r.1, acc.2.push r.2)) (L, tooks)).1
        (knapRecon tabs
          (l.foldl (fun acc tab => let r := knapLayer cap acc.1 tab; (r.1, acc.2.push r.2)) (L, tooks)).2
          tabs.size) ∧
      (l.foldl (fun acc tab => let r := knapLayer cap acc.1 tab; (r.1, acc.2.push r.2)) (L, tooks)).2.size
        = tabs.size := by
  intro l
  induction l with
  | nil =>
    intro j dp L tooks hl hjs hsz hinv
    have hj : j = tabs.size := by
      have := congrArg List.length hl
      simp at this
      omega
    subst hj
    exact ⟨hinv, hsz⟩
  | cons tab l ih =>
    intro j dp L tooks hl hjs hsz hinv
    have hj : j < tabs.size := by
      have := congrArg List.length hl
      simp at this
      omega
    have htab : tab = tabs[j]! := by
      rw [List.drop_eq_getElem_cons (by simpa using hj)] at hl
      rw [getElem!_pos tabs j hj]
      simpa using (List.cons.inj hl).1
    subst htab
    simp only [List.foldl_cons]
    apply ih (j + 1)
    · rw [List.drop_eq_getElem_cons (by simpa using hj)] at hl
      exact (List.cons.inj hl).2
    · omega
    · simp [hsz]
    · have hstep := knapLayer_inv hok hj hinv
      have hrec : reconNext (knapRecon tabs tooks j) tabs[j]! (knapLayer cap L tabs[j]!).2 =
          knapRecon tabs (tooks.push (knapLayer cap L tabs[j]!).2) (j + 1) := by
        funext c
        simp only [knapRecon]
        have e : (tooks.push (knapLayer cap L tabs[j]!).2)[j]! = (knapLayer cap L tabs[j]!).2 := by
          rw [getElem!_pos _ j (by simp; omega)]
          simp [← hsz]
        rw [e, knapRecon_push _ _ _ _ _ (by omega)]
        rfl
      rw [hrec] at hstep
      exact hstep

/-! ## The choice of the bracket -/

theorem foldl_filterMap_elim {α β γ : Type} (f : α → Option β) (g : γ → β → γ) :
    ∀ (l : List α) (init : γ), (l.filterMap f).foldl g init = l.foldl (fun x y => (f y).elim x (g x)) init := by
  intro l
  induction l with
  | nil => intro init; rfl
  | cons a l ih =>
    intro init
    rw [List.filterMap_cons]
    cases h : f a with
    | none => simp only [List.foldl_cons, h, Option.elim_none]; exact ih init
    | some b => simp only [List.foldl_cons, h, Option.elim_some]; exact ih (g init b)

/-- The order of `knapChoose` on candidates `(Δ, set, lower)`: length, then
`setPrec`. -/
def chooseKey (kCS : Nat) (x : _root_.Int × Array Nat × Bool) : _root_.Int × Array Nat :=
  (x.1 + (tag0Size (kCS + x.2.1.size) : _root_.Int), x.2.1)

/-- The step of `knapChoose`. -/
def chooseStep (kCS : Nat) (acc x : _root_.Int × Array Nat × Bool) : _root_.Int × Array Nat × Bool :=
  if entryLt (chooseKey kCS x) (chooseKey kCS acc) then x else acc

theorem knapChoose_eq_fold (kCS : Nat) (dp : Array (Option (_root_.Int × Array Nat)))
    (init : _root_.Int × Array Nat × Bool)
    (hcard : ∀ c, c < dp.size → ∀ e, dp[c]! = some e → e.2.size = c) :
    knapChoose kCS dp init =
      ((List.range dp.size).filterMap fun c => (dp[c]!).map fun e => (e.1, e.2, true)).foldl
        (chooseStep kCS) init := by
  rw [foldl_filterMap_elim]
  unfold knapChoose
  have key : ∀ (l : List Nat) (acc : _root_.Int × Array Nat × Bool), (∀ c ∈ l, c < dp.size) →
      l.foldl (fun (acc : _root_.Int × Array Nat × Bool) c =>
        match dp[c]! with
        | none => acc
        | some (d, s) =>
          let l : _root_.Int := d + (tag0Size (kCS + c) : _root_.Int)
          let l0 : _root_.Int := acc.1 + (tag0Size (kCS + acc.2.1.size) : _root_.Int)
          if l < l0 || (l == l0 && setPrec s acc.2.1) then (d, s, true) else acc) acc =
      l.foldl (fun x y => ((dp[y]!).map fun e => (e.1, e.2, true)).elim x (chooseStep kCS x)) acc := by
    intro l
    induction l with
    | nil => intro acc _; rfl
    | cons c l ih =>
      intro acc hl
      simp only [List.foldl_cons]
      rw [← ih _ (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))]
      congr 1
      cases he : dp[c]! with
      | none => rfl
      | some e =>
        obtain ⟨d, s⟩ := e
        have hs := hcard c (hl c List.mem_cons_self) (d, s) he
        simp only [Option.map_some, Option.elim_some, chooseStep, chooseKey, entryLt]
        simp only at hs
        simp only [hs]
  exact key _ init (fun c hc => List.mem_range.mp hc)

/-- A fold that replaces its value by a strictly smaller element (no `Option`). -/
theorem foldl_least_init {α β : Type} (abs : α → β) (lt : β → β → Bool)
    (hirr : ∀ x, lt x x = false)
    (htrans : ∀ x y z, lt x y = true → lt y z = true → lt x z = true)
    (g : α → α → α) (hg : ∀ a x, g a x = if lt (abs x) (abs a) then x else a) :
    ∀ (L : List α) (init : α),
      (L.foldl g init ∈ L ∨ L.foldl g init = init) ∧
        (∀ x ∈ L, lt (abs x) (abs (L.foldl g init)) = false) ∧
        (L.foldl g init = init ∨ lt (abs (L.foldl g init)) (abs init) = true) := by
  have hasymm : ∀ x y, lt x y = true → lt y x = false := by
    intro x y h
    cases h' : lt y x
    · rfl
    · have := htrans _ _ _ h h'; rw [hirr] at this; cases this
  intro L
  induction L with
  | nil => intro init; simp
  | cons t ts ih =>
    intro init
    simp only [List.foldl_cons]
    obtain ⟨hmem, hle, hlea⟩ := ih (g init t)
    rw [hg] at hmem hle hlea ⊢
    by_cases hb : lt (abs t) (abs init) = true
    · simp only [hb, ite_true] at hmem hle hlea ⊢
      refine ⟨?_, fun x hx => ?_, ?_⟩
      · rcases hmem with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rw [h]; exact Or.inl List.mem_cons_self
      · rcases List.mem_cons.mp hx with h | h
        · subst h
          rcases hlea with h | h
          · rw [h]; exact hirr _
          · exact hasymm _ _ h
        · exact hle x h
      · rcases hlea with h | h
        · rw [h]; exact Or.inr hb
        · exact Or.inr (htrans _ _ _ h hb)
    · simp only [hb, Bool.false_eq_true, ite_false] at hmem hle hlea ⊢
      refine ⟨?_, fun x hx => ?_, hlea⟩
      · rcases hmem with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
      · rcases List.mem_cons.mp hx with h | h
        · subst h
          cases h : lt (abs x) (abs (ts.foldl g init))
          · rfl
          · exfalso
            rcases hlea with h' | h'
            · rw [h'] at h; exact hb h
            · exact hb (htrans _ _ _ h h')
        · exact hle x h

theorem tag0BracketStart_le (k : Nat) : tag0BracketStart k ≤ k := by
  unfold tag0BracketStart
  split
  · omega
  · split <;> (try split) <;> (try split) <;> (try split) <;> omega

/-! ## Rebuilding the chosen set -/

theorem knapRecon_sorted (tabs : Array CTable) (tooks : Array (Array Nat)) :
    ∀ j c, (knapRecon tabs tooks j c).toList.Pairwise fun x y => decide (x ≤ y) = true := by
  intro j
  cases j with
  | zero => intro c; simp [knapRecon]
  | succ j =>
    intro c
    simp only [knapRecon]
    unfold mergeSorted
    exact List.pairwise_mergeSort le_trans_dec le_total_dec _

theorem knapCollect_perm (tabs : Array CTable) (tooks : Array (Array Nat)) :
    ∀ j c acc, (knapCollect tabs tooks j c acc).Perm ((knapRecon tabs tooks j c).toList ++ acc) := by
  intro j
  induction j with
  | zero => intro c acc; simp [knapCollect, knapRecon]
  | succ j ih =>
    intro c acc
    simp only [knapCollect, knapRecon]
    refine (ih _ _).trans ?_
    rw [← List.append_assoc]
    exact List.Perm.append_right _ (mergeSorted_perm _ _).symm

theorem knapReconFast_eq (tabs : Array CTable) (tooks : Array (Array Nat)) (j c : Nat) :
    knapReconFast tabs tooks j c = knapRecon tabs tooks j c := by
  unfold knapReconFast
  apply Array.toList_inj.mp
  simp only
  apply List.Perm.eq_of_pairwise (le := fun x y => decide (x ≤ y) = true)
    (fun a b _ _ h1 h2 => by simp only [decide_eq_true_eq] at h1 h2; omega)
    (List.pairwise_mergeSort le_trans_dec le_total_dec _) (knapRecon_sorted tabs tooks j c)
  refine (List.mergeSort_perm _ _).trans ?_
  simpa using knapCollect_perm tabs tooks j c []

/-! ## The chosen bracket -/

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr' l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem knapBestCell_eq_fold (kCS : Nat) (L : KLayer) (cap : Nat) :
    knapBestCell kCS L cap =
      ((List.range (cap + 1)).filterMap fun c =>
          (L.delta[c]!).map fun d => (d + (tag0Size (kCS + c) : _root_.Int), c, d)).foldl
        (fun acc x => acc.elim (some x) fun b =>
          if x.1 < b.1 || (x.1 == b.1 && decide (L.rank[x.2.1]! < L.rank[b.2.1]!)) then some x
          else some b) none := by
  rw [foldl_filterMap_elim]
  unfold knapBestCell
  congr 1
  funext acc c
  cases L.delta[c]! <;> rfl

theorem knapChooseFast_eq {kCS cap : Nat} {tabs : Array CTable} {init : _root_.Int × Array Nat × Bool}
    (hinit : cap < init.2.1.size) {dp : Array (Option (_root_.Int × Array Nat))}
    (h : LayerInv cap tabs tabs.size dp (knapRun cap tabs.toList).1
      (knapRecon tabs (knapRun cap tabs.toList).2 tabs.size)) :
    knapChooseFast kCS cap tabs init = knapChoose kCS dp init := by
  generalize hL : (knapRun cap tabs.toList).1 = L at h
  generalize hR : knapRecon tabs (knapRun cap tabs.toList).2 tabs.size = recon at h
  have hcard : ∀ c, c < dp.size → ∀ e, dp[c]! = some e → e.2.size = c := by
    intro c hc e he
    rw [h.size] at hc
    rw [h.cell c (by omega)] at he
    cases hd : L.delta[c]! with
    | none => rw [hd] at he; cases he
    | some d =>
      rw [hd] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      exact h.card c (by omega) (by simp [hd])
  rw [knapChoose_eq_fold kCS dp init hcard]
  -- the specification's candidates
  have hspecv : ((List.range dp.size).filterMap fun c => (dp[c]!).map fun e => (e.1, e.2, true)) =
      ((List.range (cap + 1)).filterMap fun c => (L.delta[c]!).map fun d => (d, recon c, true)) := by
    rw [h.size]
    apply filterMap_congr'
    intro c hc
    rw [h.cell c (by simp at hc; omega)]
    cases L.delta[c]! <;> rfl
  rw [hspecv]
  generalize hV : ((List.range (cap + 1)).filterMap fun c =>
    (L.delta[c]!).map fun d => (d, recon c, true)) = V
  have hmemV : ∀ x, x ∈ V ↔ ∃ c d, c ≤ cap ∧ L.delta[c]! = some d ∧ x = (d, recon c, true) := by
    intro x
    rw [← hV, List.mem_filterMap]
    constructor
    · rintro ⟨c, hc, hx⟩
      cases hd : L.delta[c]! with
      | none => rw [hd] at hx; cases hx
      | some d =>
        rw [hd] at hx
        simp only [Option.map_some, Option.some.injEq] at hx
        exact ⟨c, d, by simp at hc; omega, hd, hx.symm⟩
    · rintro ⟨c, d, hc, hd, rfl⟩
      exact ⟨c, by simp; omega, by rw [hd]; rfl⟩
  have hkeyV : ∀ c d, c ≤ cap → L.delta[c]! = some d →
      chooseKey kCS (d, recon c, true) = (d + (tag0Size (kCS + c) : _root_.Int), recon c) := by
    intro c d hc hd
    unfold chooseKey
    simp only
    rw [h.card c hc (by simp [hd])]
  -- the specification's choice
  obtain ⟨hrmem, hrle, hrinit⟩ := foldl_least_init (chooseKey kCS) entryLt entryLt_irrefl
    (fun _ _ _ => entryLt_trans) (chooseStep kCS) (fun a x => rfl) V init
  generalize hr : V.foldl (chooseStep kCS) init = r at hrmem hrle hrinit
  -- the fast choice
  unfold knapChooseFast
  simp only
  rw [hL]
  rw [knapBestCell_eq_fold]
  generalize hC : ((List.range (cap + 1)).filterMap fun c =>
    (L.delta[c]!).map fun d => (d + (tag0Size (kCS + c) : _root_.Int), c, d)) = C
  have hmemC : ∀ x, x ∈ C ↔ ∃ c d, c ≤ cap ∧ L.delta[c]! = some d ∧
      x = (d + (tag0Size (kCS + c) : _root_.Int), c, d) := by
    intro x
    rw [← hC, List.mem_filterMap]
    constructor
    · rintro ⟨c, hc, hx⟩
      cases hd : L.delta[c]! with
      | none => rw [hd] at hx; cases hx
      | some d =>
        rw [hd] at hx
        simp only [Option.map_some, Option.some.injEq] at hx
        exact ⟨c, d, by simp at hc; omega, hd, hx.symm⟩
    · rintro ⟨c, d, hc, hd, rfl⟩
      exact ⟨c, by simp; omega, by rw [hd]; rfl⟩
  have hfast := foldl_least (fun x : _root_.Int × Nat × _root_.Int =>
      x.2.1 ≤ cap ∧ (L.delta[x.2.1]!).isSome)
    (fun x => (x.1, recon x.2.1)) entryLt entryLt_irrefl (fun _ _ _ => entryLt_trans)
    (fun acc x => acc.elim (some x) fun b =>
      if x.1 < b.1 || (x.1 == b.1 && decide (L.rank[x.2.1]! < L.rank[b.2.1]!)) then some x
      else some b) (fun x => rfl)
    (fun b x hb hx => by
      simp only [Option.elim_some]
      congr 1
      unfold entryLt
      by_cases hxb : x.2.1 = b.2.1
      · rw [hxb, setPrec_irrefl']
        simp
      · have hdec : decide (L.rank[x.2.1]! < L.rank[b.2.1]!) = setPrec (recon x.2.1) (recon b.2.1) := by
          rw [Bool.eq_iff_iff, decide_eq_true_iff]
          exact h.rank _ _ hx.1 hb.1 hx.2 hb.2 hxb
        rw [hdec])
    C none (fun x hx => by
      obtain ⟨c, d, hc, hd, rfl⟩ := (hmemC x).mp hx
      exact ⟨hc, by simp [hd]⟩) (fun _ h => by cases h)
  obtain ⟨hfn, hfs⟩ := hfast
  cases hb : C.foldl (fun acc x => acc.elim (some x) fun b =>
      if x.1 < b.1 || (x.1 == b.1 && decide (L.rank[x.2.1]! < L.rank[b.2.1]!)) then some x
      else some b) none with
  | none =>
    -- no cell: the specification keeps `init`
    have hCnil := (hfn.mp hb).2
    have hVnil : V = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      obtain ⟨c, d, hc, hd, _⟩ := (hmemV x).mp hx
      have := (hmemC _).mpr ⟨c, d, hc, hd, rfl⟩
      rw [hCnil] at this
      simp at this
    rw [hVnil] at hr
    simp only [Option.elim_none]
    rw [← hr]
    rfl
  | some b =>
    obtain ⟨hbmem, hble, _⟩ := hfs b hb
    have hbC : b ∈ C := by
      rcases hbmem with h' | h'
      · exact h'
      · cases h'
    obtain ⟨c, d, hc, hd, rfl⟩ := (hmemC _).mp hbC
    simp only [Option.elim_some]
    rw [knapReconFast_eq, hR]
    -- the best cell's candidate
    have hvV : (d, recon c, true) ∈ V := (hmemV _).mpr ⟨c, d, hc, hd, rfl⟩
    have hvmin : ∀ x ∈ V, entryLt (chooseKey kCS x) (chooseKey kCS (d, recon c, true)) = false := by
      intro x hx
      obtain ⟨c', d', hc', hd', rfl⟩ := (hmemV x).mp hx
      rw [hkeyV c' d' hc' hd', hkeyV c d hc hd]
      exact hble _ ((hmemC _).mpr ⟨c', d', hc', hd', rfl⟩)
    -- candidates of `V` are told apart by their keys, and differ from `init`
    have hinj : ∀ x ∈ V, ∀ y ∈ V, chooseKey kCS x = chooseKey kCS y → x = y := by
      intro x hx y hy hxy
      obtain ⟨c1, d1, hc1, hd1, rfl⟩ := (hmemV x).mp hx
      obtain ⟨c2, d2, hc2, hd2, rfl⟩ := (hmemV y).mp hy
      rw [hkeyV c1 d1 hc1 hd1, hkeyV c2 d2 hc2 hd2] at hxy
      have hs := congrArg (fun p => p.2.size) hxy
      simp only at hs
      rw [h.card c1 hc1 (by simp [hd1]), h.card c2 hc2 (by simp [hd2])] at hs
      subst hs
      rw [hd1] at hd2
      cases hd2
      rfl
    have hneinit : ∀ x ∈ V, chooseKey kCS x ≠ chooseKey kCS init := by
      intro x hx hxe
      obtain ⟨c1, d1, hc1, hd1, rfl⟩ := (hmemV x).mp hx
      have hs := congrArg (fun p => p.2.size) hxe
      simp only [chooseKey] at hs
      rw [h.card c1 hc1 (by simp [hd1])] at hs
      omega
    have hkv := hkeyV c d hc hd
    by_cases hlt : entryLt (chooseKey kCS (d, recon c, true)) (chooseKey kCS init) = true
    · -- the cell is chosen
      have hcond : (d + (tag0Size (kCS + c) : _root_.Int) <
            init.1 + (tag0Size (kCS + init.2.1.size) : _root_.Int) ||
          (d + (tag0Size (kCS + c) : _root_.Int) ==
              init.1 + (tag0Size (kCS + init.2.1.size) : _root_.Int) &&
            setPrec (recon c) init.2.1)) = true := by
        rw [hkv] at hlt
        exact hlt
      rw [ite_eq_left hcond]
      -- `r` is the cell's candidate
      rcases hrmem with hrV | hrinit'
      · have : chooseKey kCS r = chooseKey kCS (d, recon c, true) := by
          apply least_unique entryLt (fun x y hxy => entryLt_total hxy)
            (L := (V.map (chooseKey kCS))) (List.mem_map_of_mem hrV) (List.mem_map_of_mem hvV)
          · intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            exact hrle y hy
          · intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            exact hvmin y hy
        rw [← hinj _ hrV _ hvV this]
      · exfalso
        have := hrle _ hvV
        rw [hrinit', hlt] at this
        cases this
    · -- `init` is kept
      have hcond : (d + (tag0Size (kCS + c) : _root_.Int) <
            init.1 + (tag0Size (kCS + init.2.1.size) : _root_.Int) ||
          (d + (tag0Size (kCS + c) : _root_.Int) ==
              init.1 + (tag0Size (kCS + init.2.1.size) : _root_.Int) &&
            setPrec (recon c) init.2.1)) = false := by
        have h2 : entryLt (chooseKey kCS (d, recon c, true)) (chooseKey kCS init) = false := by
          simpa using hlt
        rw [hkv] at h2
        exact h2
      rw [ite_eq_right (by simp [hcond])]
      rcases hrinit with hri | hri
      · exact hri.symm
      · exfalso
        rcases hrmem with hrV | hrinit'
        · -- `r` is a cell below `init`, so it is the best cell
          have hle1 := hrle _ hvV
          have hle2 := hvmin r hrV
          have hne : chooseKey kCS r ≠ chooseKey kCS (d, recon c, true) ∨
              chooseKey kCS r = chooseKey kCS (d, recon c, true) := by
            by_cases he : chooseKey kCS r = chooseKey kCS (d, recon c, true)
            · exact Or.inr he
            · exact Or.inl he
          rcases hne with hne | he
          · rcases entryLt_total hne with h1 | h1
            · rw [h1] at hle2; cases hle2
            · rw [h1] at hle1; cases hle1
          · rw [he] at hri
            exact hlt hri
        · rw [hrinit', entryLt_irrefl] at hri
          cases hri

/-! ## The per-component optimum and the knapsack -/

theorem foldl_mergeSorted_perm :
    ∀ (l : List CompResult) (acc : Array Nat),
      (l.foldl (fun acc r => mergeSorted acc r.bestSet) acc).toList.Perm
        (acc.toList ++ l.flatMap fun r => r.bestSet.toList) := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons r l ih =>
    intro acc
    simp only [List.foldl_cons, List.flatMap_cons]
    refine (ih _).trans ?_
    rw [← List.append_assoc]
    exact List.Perm.append_right _ (mergeSorted_perm _ _)

theorem foldl_mergeSorted_sorted :
    ∀ (l : List CompResult) (acc : Array Nat),
      acc.toList.Pairwise (fun x y => decide (x ≤ y) = true) →
      (l.foldl (fun acc r => mergeSorted acc r.bestSet) acc).toList.Pairwise
        fun x y => decide (x ≤ y) = true := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons r l ih =>
    intro acc _
    simp only [List.foldl_cons]
    apply ih
    unfold mergeSorted
    exact List.pairwise_mergeSort le_trans_dec le_total_dec _

theorem foldl_append_toList :
    ∀ (l : List CompResult) (acc : Array Nat),
      (l.foldl (fun acc r => acc ++ r.bestSet) acc).toList =
        acc.toList ++ l.flatMap fun r => r.bestSet.toList := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons r l ih =>
    intro acc
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [ih, Array.toList_append, List.append_assoc]

/-- The union of the per-component optima, merged once. -/
theorem bestX_eq (results : Array CompResult) :
    results.foldl (fun acc r => mergeSorted acc r.bestSet) #[] =
      ((results.foldl (fun acc r => acc ++ r.bestSet) #[]).toList.mergeSort
        fun x y => decide (x ≤ y)).toArray := by
  apply Array.toList_inj.mp
  rw [← Array.foldl_toList, ← Array.foldl_toList, List.toList_toArray]
  apply List.Perm.eq_of_pairwise (le := fun x y => decide (x ≤ y) = true)
    (fun a b _ _ h1 h2 => by simp only [decide_eq_true_eq] at h1 h2; omega)
    (foldl_mergeSorted_sorted _ _ (by simp))
    (List.pairwise_mergeSort le_trans_dec le_total_dec _)
  refine (foldl_mergeSorted_perm _ _).trans ?_
  rw [foldl_append_toList]
  exact (List.mergeSort_perm _ _).symm

theorem uniformKnapsack_eq_fast_apply (limits : Limits) (kCS : Nat) (results : Array CompResult) :
    uniformKnapsack limits kCS results = uniformKnapsackFast limits kCS results := by
  unfold uniformKnapsack uniformKnapsackFast
  rw [bestX_eq]
  generalize ((results.foldl (fun acc r => acc ++ r.bestSet) #[]).toList.mergeSort
    fun x y => decide (x ≤ y)).toArray = bestX
  simp only
  split
  · rename_i hstart
    split
    · rfl
    · rename_i hcells
      split
      · rename_i hok
        congr 1
        have hdp : results.foldl (fun dp r => knapStep (tag0BracketStart (kCS + bestX.size) - 1 - kCS)
              dp r.bySize) (#[some (0, #[])] ++ Array.replicate
                (tag0BracketStart (kCS + bestX.size) - 1 - kCS) none) =
            (results.map (·.bySize)).toList.foldl
              (fun dp tab => knapStep (tag0BracketStart (kCS + bestX.size) - 1 - kCS) dp tab)
              (#[some (0, #[])] ++ Array.replicate
                (tag0BracketStart (kCS + bestX.size) - 1 - kCS) none) := by
          rw [← Array.foldl_toList, Array.toList_map, List.foldl_map]
        rw [hdp]
        have hinit := knapInit_inv (tag0BracketStart (kCS + bestX.size) - 1 - kCS)
          (results.map (·.bySize)) (knapRecon (results.map (·.bySize)) #[] 0) rfl
        have hrun := (knapRun_inv hok (results.map (·.bySize)).toList 0 _ _ #[] (by simp) (by omega)
          rfl hinit).1
        symm
        apply knapChooseFast_eq _ hrun
        have := tag0BracketStart_le (kCS + bestX.size)
        simp only
        omega
      · rfl
  · rfl

@[csimp] theorem uniformKnapsack_eq_fast : @uniformKnapsack = @uniformKnapsackFast := by
  funext limits kCS results
  exact uniformKnapsack_eq_fast_apply limits kCS results

end Ix.Sharing.Exact

end
