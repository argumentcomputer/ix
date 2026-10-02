/-
  Fast first-tier search of the tiered construction (phase 2).

  `firstTierFast` computes exactly `firstTier` (`firstTier_eq_fast`, attached
  with `@[csimp]`, so compiled callers run it): the same depth-first branch
  and bound over the same items in the same order, with the same states
  counted and the same errors. Two representation changes:

  * The undecided items are carried as the list `rest` (the suffix of the
    items from the current position), so the bound reads it directly instead
    of building `items.toList.drop pos` at every state.
  * The excluded set is not stored. On every search path each item before the
    current position is either chosen (in `inF`) or excluded, and no excluded
    term is ever chosen, so a term is excluded exactly when it is an item
    before the current position that is not chosen (`tierExcluded`, with the
    first position of every item precomputed). This needs every closure to
    contain its own term, which `tierClosures` guarantees and which is checked
    once (`closuresContainSelf`); otherwise the specification runs.
-/
module

public import Ix.Sharing.Exact.Tiered
import all Ix.Sharing.Exact.Tiered
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas

public section

namespace Ix.Sharing.Exact

/-! ## First positions -/

/-- First position (offset by `i`) of every term of a list, added to `m`
where `m` has no entry: the first occurrence wins. -/
def firstPosMap : List Nat → Nat → Std.HashMap Nat Nat → Std.HashMap Nat Nat
  | [], _, m => m
  | t :: ts, i, m => firstPosMap ts (i + 1) (m.insertIfNew t i)

/-- Whether the first position of `u` is before `pos`. -/
@[inline] def posBefore (posMap : Std.HashMap Nat Nat) (pos u : Nat) : Bool :=
  posMap[u]?.any (· < pos)

/-- Whether `u` is excluded on a search path at position `pos` with chosen set
`inF`: an item before `pos` that is not chosen. -/
@[inline] def tierExcluded (posMap : Std.HashMap Nat Nat) (pos : Nat) (inF : List Nat)
    (u : Nat) : Bool :=
  posBefore posMap pos u && !inF.contains u

/-! ## The search -/

/-- `tierDfs` with the undecided items as the list `rest` (starting at
position `pos`) and the excluded set derived from the position
(`tierExcluded`). -/
def tierDfsFast (posMap : Std.HashMap Nat Nat) (weight : Nat → Nat)
    (closure : Nat → Option (List Nat)) (cap : Nat) (limits : Limits) :
    Nat → Nat → List Nat → Nat → List Nat → TierState → Except SharingError TierState
  | 0, _, _, _, _, _ => throw (.internal "first-tier search fuel exhausted")
  | fuel + 1, pos, rest, cur, inF, st =>
    if st.states + 1 > limits.maxStates then
      throw (.resourceExhausted .states limits.maxStates)
    else
      let st := { st with states := st.states + 1 }
      if tierPruned st.best (tierBound weight inF rest (cap - inF.length) cur) then
        pure st
      else
        match rest with
        | [] => pure { st with best := tierUpd st.best cur inF }
        | t :: ts =>
          if inF.contains t then
            tierDfsFast posMap weight closure cap limits fuel (pos + 1) ts cur inF st
          else do
            let st ← match closure t with
              | some c =>
                let new := c.filter (!inF.contains ·)
                if !c.any (tierExcluded posMap pos inF) && inF.length + new.length ≤ cap then
                  tierDfsFast posMap weight closure cap limits fuel (pos + 1) ts
                    (new.foldl (fun acc u => acc + weight u) cur) (inF ++ new) st
                else pure st
              | none => pure st
            tierDfsFast posMap weight closure cap limits fuel (pos + 1) ts cur inF st

/-- Every computed closure of an item contains the item. -/
def closuresContainSelf (items : Array Nat) (closure : Nat → Option (List Nat)) : Bool :=
  items.all fun t => (closure t).all (·.contains t)

/-- `firstTier` with `tierDfsFast` (see the module doc). -/
def firstTierFast (topo : Array Nat) (weight : Nat → Nat) (deps : Nat → List Nat) (cap : Nat)
    (limits : Limits) : Except SharingError (Array Nat × Nat) := do
  let items := (topo.toList.mergeSort (tierOrder weight)).toArray
  let cl ← tierClosures topo deps cap
  let st ← if closuresContainSelf items (fun t => cl.getD t none) then
      tierDfsFast (firstPosMap items.toList 0 {}) weight (fun t => cl.getD t none) cap limits
        (items.size + 2) 0 items.toList 0 [] {}
    else
      tierDfs items weight (fun t => cl.getD t none) cap limits (items.size + 2) 0 0 [] {} {}
  match st.best with
  | some (_, s) => return ((s.mergeSort (· ≤ ·)).toArray, st.states)
  | none => return (#[], st.states)

/-! ## Equality with the specification -/

theorem firstPosMap_getElem? (l : List Nat) (i : Nat) (m : Std.HashMap Nat Nat) (u : Nat) :
    (firstPosMap l i m)[u]? = (m[u]?).or ((l.idxOf? u).map (· + i)) := by
  induction l generalizing i m with
  | nil => simp [firstPosMap]
  | cons t ts ih =>
    simp only [firstPosMap, ih, Std.HashMap.getElem?_insertIfNew, List.idxOf?_cons]
    by_cases htu : t = u
    · subst htu
      by_cases hm : t ∈ m
      · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (Std.HashMap.mem_iff_isSome_getElem?.mp hm)
        simp [hm]
      · have hn : m[t]? = none := Std.HashMap.getElem?_eq_none hm
        simp [hm]
    · have h1 : (t == u) = false := by simpa using htu
      simp only [h1, Bool.false_eq_true, false_and, ite_false, Option.map_map]
      congr 2
      funext q
      simp only [Function.comp]
      omega

/-- The first position of `u` in `l` is before `pos`. -/
def idxBefore (l : List Nat) (pos u : Nat) : Bool := (l.idxOf? u).any (· < pos)

theorem posBefore_firstPosMap (l : List Nat) (pos u : Nat) :
    posBefore (firstPosMap l 0 {}) pos u = idxBefore l pos u := by
  unfold posBefore idxBefore
  rw [firstPosMap_getElem?]
  simp

/-- The first position of `u` in `l` is before `pos + 1` exactly when it is
before `pos` or `u` is at `pos`. -/
theorem idxBefore_succ (l : List Nat) (u : Nat) :
    ∀ (pos : Nat) (h : pos < l.length),
      idxBefore l (pos + 1) u = (idxBefore l pos u || u == l[pos]) := by
  induction l with
  | nil => intro pos h; simp at h
  | cons a l ih =>
    intro pos h
    unfold idxBefore
    rw [List.idxOf?_cons]
    by_cases hau : a = u
    · subst hau
      cases pos with
      | zero => simp
      | succ p =>
        simp only [beq_self_eq_true, ite_true, Option.any_some]
        have : 0 < p + 1 := Nat.zero_lt_succ p
        simp [this]
    · have h1 : (a == u) = false := by simpa using hau
      simp only [h1, Bool.false_eq_true, ite_false, Option.any_map]
      cases pos with
      | zero =>
        have h2 : (u == a) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun h => hau h.symm
        cases l.idxOf? u <;> simp [h2]
      | succ p =>
        have hp : p < l.length := by simp at h; omega
        have := ih p hp
        unfold idxBefore at this
        simp only [List.getElem_cons_succ]
        have e1 : (fun a => decide (a + 1 < p + 1 + 1)) = (fun x => decide (x < p + 1)) := by
          funext x; simp
        have e2 : (fun a => decide (a + 1 < p + 1)) = (fun x => decide (x < p)) := by
          funext x; simp
        rw [e1, e2]
        exact this

theorem posBefore_zero (l : List Nat) (u : Nat) :
    posBefore (firstPosMap l 0 {}) 0 u = false := by
  rw [posBefore_firstPosMap]
  unfold idxBefore
  cases l.idxOf? u <;> simp

theorem posBefore_succ (items : Array Nat) (pos : Nat) (h : pos < items.size) (u : Nat) :
    posBefore (firstPosMap items.toList 0 {}) (pos + 1) u =
      (posBefore (firstPosMap items.toList 0 {}) pos u || u == items[pos]) := by
  rw [posBefore_firstPosMap, posBefore_firstPosMap,
    idxBefore_succ items.toList u pos (by simpa using h)]
  simp

/-- The excluded-set invariant of a search node at `pos`. -/
def ExclInv (posMap : Std.HashMap Nat Nat) (pos : Nat) (inF : List Nat)
    (excluded : Std.HashSet Nat) : Prop :=
  ∀ u, excluded.contains u = tierExcluded posMap pos inF u

/-- Skipping a chosen item keeps the invariant. -/
theorem ExclInv.skip {items : Array Nat} {pos : Nat} (hlt : pos < items.size) {inF : List Nat}
    {excluded : Std.HashSet Nat} (hinv : ExclInv (firstPosMap items.toList 0 {}) pos inF excluded)
    (hin : items[pos] ∈ inF) :
    ExclInv (firstPosMap items.toList 0 {}) (pos + 1) inF excluded := by
  intro u
  rw [hinv u]
  unfold tierExcluded
  rw [posBefore_succ items pos hlt u]
  by_cases hu : u = items[pos]
  · subst hu; simp [hin]
  · have : (u == items[pos]) = false := by simpa using hu
    simp [this]

/-- Excluding an unchosen item keeps the invariant. -/
theorem ExclInv.exclude {items : Array Nat} {pos : Nat} (hlt : pos < items.size)
    {inF : List Nat} {excluded : Std.HashSet Nat}
    (hinv : ExclInv (firstPosMap items.toList 0 {}) pos inF excluded) (hin : items[pos] ∉ inF) :
    ExclInv (firstPosMap items.toList 0 {}) (pos + 1) inF (excluded.insert items[pos]) := by
  intro u
  rw [Std.HashSet.contains_insert, hinv u]
  unfold tierExcluded
  rw [posBefore_succ items pos hlt u]
  by_cases hu : u = items[pos]
  · subst hu; simp [hin]
  · have h1 : (items[pos] == u) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h => hu h.symm
    have h2 : (u == items[pos]) = false := by simpa using hu
    simp [h1, h2]

/-- Choosing the closure of an unchosen item keeps the invariant, when the
closure contains the item and no excluded term. -/
theorem ExclInv.include {items : Array Nat} {pos : Nat} (hlt : pos < items.size)
    {inF c : List Nat} {excluded : Std.HashSet Nat}
    (hinv : ExclInv (firstPosMap items.toList 0 {}) pos inF excluded) (hin : items[pos] ∉ inF)
    (htc : items[pos] ∈ c)
    (hany : c.any (tierExcluded (firstPosMap items.toList 0 {}) pos inF) = false) :
    ExclInv (firstPosMap items.toList 0 {}) (pos + 1) (inF ++ c.filter (!inF.contains ·))
      excluded := by
  have hnot : ∀ x ∈ c, tierExcluded (firstPosMap items.toList 0 {}) pos inF x = false := by
    intro x hx
    cases h : tierExcluded (firstPosMap items.toList 0 {}) pos inF x
    · rfl
    · have : c.any (tierExcluded (firstPosMap items.toList 0 {}) pos inF) = true :=
        List.any_eq_true.mpr ⟨x, hx, h⟩
      rw [hany] at this
      cases this
  intro u
  rw [hinv u]
  by_cases hu : u = items[pos]
  · subst hu
    rw [hnot _ htc]
    unfold tierExcluded
    simp [hin, htc]
  · unfold tierExcluded
    rw [posBefore_succ items pos hlt u]
    have h2 : (u == items[pos]) = false := by simpa using hu
    simp only [h2, Bool.or_false]
    cases hb : posBefore (firstPosMap items.toList 0 {}) pos u
    · simp
    · by_cases hi : u ∈ inF
      · simp [hi]
      · have huc : u ∉ c := by
          intro huc
          have := hnot u huc
          simp [tierExcluded, hb, hi] at this
        simp [hi, huc]

theorem tierDfs_eq_fast (items : Array Nat) (weight : Nat → Nat)
    (closure : Nat → Option (List Nat)) (cap : Nat) (limits : Limits)
    (hself : closuresContainSelf items closure = true) :
    ∀ (fuel pos cur : Nat) (inF : List Nat) (excluded : Std.HashSet Nat) (st : TierState),
      ExclInv (firstPosMap items.toList 0 {}) pos inF excluded →
      tierDfs items weight closure cap limits fuel pos cur inF excluded st =
        tierDfsFast (firstPosMap items.toList 0 {}) weight closure cap limits fuel pos
          (items.toList.drop pos) cur inF st := by
  intro fuel
  induction fuel with
  | zero => intro pos cur inF excluded st _; simp [tierDfs, tierDfsFast]
  | succ fuel ih =>
    intro pos cur inF excluded st hinv
    simp only [tierDfs, tierDfsFast]
    split
    · rfl
    · split
      · rfl
      · by_cases hpos : pos ≥ items.size
        · have hd : items.toList.drop pos = [] := by simp; omega
          simp only [hpos, ite_true, hd]
        · have hlt : pos < items.size := by omega
          have hd : items.toList.drop pos = items[pos] :: items.toList.drop (pos + 1) := by
            rw [List.drop_eq_getElem_cons (by simpa using hlt)]
            simp
          simp only [hpos, ite_false, hd, getElem!_pos items pos hlt]
          by_cases hin : items[pos] ∈ inF
          · have hc : inF.contains items[pos] = true := by simpa using hin
            simp only [hc, ite_true]
            exact ih _ _ _ _ _ (hinv.skip hlt hin)
          · have hc : inF.contains items[pos] = false := by simpa using hin
            simp only [hc, Bool.false_eq_true, ite_false]
            have hfun : excluded.contains = tierExcluded (firstPosMap items.toList 0 {}) pos inF :=
              funext hinv
            have hex := hinv.exclude hlt hin
            cases hcl : closure items[pos] with
            | none =>
              simp only [pure_bind]
              exact ih _ _ _ _ _ hex
            | some c =>
              simp only
              rw [hfun]
              split
              · rename_i hcond
                have hany : c.any (tierExcluded (firstPosMap items.toList 0 {}) pos inF) = false := by
                  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
                  exact hcond.1
                have htc : items[pos] ∈ c := by
                  have hall := Array.all_eq_true.mp hself pos hlt
                  simp only [hcl, Option.all_some] at hall
                  simpa using hall
                rw [ih _ _ _ _ _ (hinv.include hlt hin htc hany)]
                congr 1
                funext st'
                exact ih _ _ _ _ _ hex
              · simp only [pure_bind]
                exact ih _ _ _ _ _ hex

theorem firstTier_eq_fast_apply (topo : Array Nat) (weight : Nat → Nat) (deps : Nat → List Nat)
    (cap : Nat) (limits : Limits) :
    firstTier topo weight deps cap limits = firstTierFast topo weight deps cap limits := by
  unfold firstTier firstTierFast
  simp only
  refine congrArg (fun f => tierClosures topo deps cap >>= f) (funext fun cl => ?_)
  split
  · rename_i hself
    rw [tierDfs_eq_fast _ weight _ cap limits hself _ 0 0 [] {} {}
      (fun u => by simp [tierExcluded, posBefore_zero])]
    simp only [List.drop_zero]
    rfl
  · rfl

@[csimp] theorem firstTier_eq_fast : @firstTier = @firstTierFast := by
  funext topo weight deps cap limits
  exact firstTier_eq_fast_apply topo weight deps cap limits

end Ix.Sharing.Exact

end
