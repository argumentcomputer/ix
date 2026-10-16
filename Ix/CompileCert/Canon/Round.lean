import Ix.CompileCert.Canon.Refine

/-! # Pass 1's refinement: one round

CS-01, ported from the donor `a9cf3607` (`Canon/Round`). At a round the
context is fixed, so the round's comparison is a total preorder on the
members (`constOrd_total`), and a correct merge sort followed by grouping
of adjacent equals yields exactly the equivalence classes of that
comparison on the class, ordered by it: `refineClassP_spec` (one class: its
groups partition it, members of one group compare `eq`, members of an
earlier group compare `lt` against a later one) and `refineClassesP_spec`
(a round: each class is replaced in place by its groups). The groups of
`List.groupByM` are the reference grouping's up to the last group's order
(`Group.lean`), and every group is re-sorted by name hash, so the proofs
read groups by membership. -/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name MutConst MutCtx)
open Ix.CompileCert.Loop (except_bind_ok)

/-! ## Equal and less, for a preorder -/

section order
variable {α : Type} {S : α → Prop} {pc : α → α → Except CmpError Ordering}
  (ht : PreOn S (fun a b => liftOrd (pc a b)))
include ht

theorem ord_swap {a b : α} (ha : S a) (hb : S b) {o : Ordering} (h : pc a b = .ok o) :
    pc b a = .ok o.swap := by
  have := ht.swap (a := a) (b := b) ha hb (s := true) (o := o) (by simp [liftOrd, h, Except.map])
  cases e : pc b a with
  | error err => rw [e] at this; cases this
  | ok o' => rw [e] at this; simp [liftOrd, Except.map] at this; rw [this]

omit ht in
theorem le_of_ok {a b : α} {o : Ordering} (h : pc a b = .ok o) (ho : o ≠ .gt) :
    Le (liftOrd (pc a b)) := ⟨true, o, by simp [liftOrd, h, Except.map], ho⟩

omit ht in
theorem ok_of_le {a b : α} (h : Le (liftOrd (pc a b))) : ∃ o, pc a b = .ok o ∧ o ≠ .gt := by
  obtain ⟨s, o, e, ho⟩ := h
  cases e' : pc a b with
  | error err => rw [e'] at e; cases e
  | ok o' => rw [e'] at e; simp [liftOrd, Except.map] at e; exact ⟨o', rfl, by rw [e.2]; exact ho⟩

theorem eq_symm' {a b : α} (ha : S a) (hb : S b) (h : pc a b = .ok .eq) : pc b a = .ok .eq := by
  simpa using ord_swap ht ha hb h

theorem eq_trans' {a b c : α} (ha : S a) (hb : S b) (hc : S c) (h₁ : pc a b = .ok .eq)
    (h₂ : pc b c = .ok .eq) : pc a c = .ok .eq := by
  obtain ⟨s, e⟩ := ht.eq_trans (a := a) (b := b) (c := c) ha hb hc (s1 := true)
    (s2 := true) (by simp [liftOrd, h₁, Except.map]) (by simp [liftOrd, h₂, Except.map])
  cases e' : pc a c with
  | error err => rw [e'] at e; cases e
  | ok o => rw [e'] at e; simp [liftOrd, Except.map] at e; rw [e.2]

theorem lt_of_lt_le' {a b c : α} (ha : S a) (hb : S b) (hc : S c) (h₁ : pc a b = .ok .lt)
    (h₂ : Le (liftOrd (pc b c))) : pc a c = .ok .lt := by
  obtain ⟨s, e⟩ := ht.lt_of_lt_le (a := a) (b := b) (c := c) ha hb hc (s := true)
    (by simp [liftOrd, h₁, Except.map]) h₂
  cases e' : pc a c with
  | error err => rw [e'] at e; cases e
  | ok o => rw [e'] at e; simp [liftOrd, Except.map] at e; rw [e.2]

theorem lt_of_le_lt' {a b c : α} (ha : S a) (hb : S b) (hc : S c) (h₁ : Le (liftOrd (pc a b)))
    (h₂ : pc b c = .ok .lt) : pc a c = .ok .lt := by
  obtain ⟨s, e⟩ := ht.lt_of_le_lt (a := a) (b := b) (c := c) ha hb hc (s := true) h₁
    (by simp [liftOrd, h₂, Except.map])
  cases e' : pc a c with
  | error err => rw [e'] at e; cases e
  | ok o => rw [e'] at e; simp [liftOrd, Except.map] at e; rw [e.2]

end order

/-! ## Sorted lists by position -/

theorem sorted_getElem {β : Type} {R : β → β → Prop} :
    ∀ {l : List β}, Sorted R l → ∀ (k : Nat) (hk : k + 1 < l.length), R l[k] l[k + 1]
  | [], _, k, hk => absurd hk (by simp)
  | [_], _, k, hk => absurd hk (by simp)
  | a :: b :: l, h, 0, _ => h.1
  | a :: b :: l, h, k + 1, hk => by
    have := sorted_getElem h.2 k (by simp at hk ⊢; omega)
    simpa using this

theorem sorted_flatten_adjacent {β : Type} {R : β → β → Prop} :
    ∀ {gs : List (List β)}, Sorted R gs.flatten → (∀ g ∈ gs, g ≠ []) →
      ∀ (i : Nat) (hi : i + 1 < gs.length) (u v : β), gs[i].getLast? = some u →
        gs[i + 1].head? = some v → R u v
  | [], _, _, i, hi, _, _, _, _ => absurd hi (by simp)
  | [_], _, _, i, hi, _, _, _, _ => absurd hi (by simp)
  | g :: g' :: gs, h, hne, 0, _, u, v, hu, hv => by
    rw [List.flatten_cons, sorted_append_iff] at h
    refine h.2.2 u v hu ?_
    simp only [List.flatten_cons]
    have : g' ≠ [] := hne g' (by simp)
    cases g' with
    | nil => exact absurd rfl this
    | cons x g' => simpa using hv
  | g :: g' :: gs, h, hne, i + 1, hi, u, v, hu, hv => by
    rw [List.flatten_cons, sorted_append_iff] at h
    exact sorted_flatten_adjacent h.2.1 (fun g hg => hne g (by simp [hg])) i
      (by simp at hi ⊢; omega) u v (by simpa using hu) (by simpa using hv)

/-! ## One class -/

section class_
variable {S : MutConst → Prop} {pc : MutConst → MutConst → Except CmpError Ordering}
  (ht : PreOn S (fun a b => liftOrd (pc a b)))
include ht

omit ht in
theorem eqOf_true {a b : MutConst} (h : eqOf pc a b = .ok true) : pc a b = .ok .eq := by
  unfold eqOf at h
  cases e : pc a b with
  | error err => rw [e] at h; cases h
  | ok o =>
    rw [e] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    simpa using h

omit ht in
theorem eqOf_false {a b : MutConst} (h : eqOf pc a b = .ok false) : ∃ o, pc a b = .ok o ∧ o ≠ .eq := by
  unfold eqOf at h
  cases e : pc a b with
  | error err => rw [e] at h; cases h
  | ok o =>
    rw [e] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨o, rfl, by simpa using h⟩

/-- Within a group, members at two positions compare `eq`. -/
theorem group_eq {g : List MutConst} (hS : ∀ x ∈ g, S x)
    (hs : Sorted (fun x y => eqOf pc y x = .ok true) g) :
    ∀ (i j : Nat) (hi : i < g.length) (hj : j < g.length), i < j → pc g[i] g[j] = .ok .eq := by
  intro i j hi hj hij
  induction j with
  | zero => omega
  | succ j ih =>
    have step : pc g[j] g[j + 1] = .ok .eq :=
      eq_symm' ht (hS _ (List.getElem_mem _)) (hS _ (List.getElem_mem _))
        (eqOf_true (sorted_getElem hs j hj))
    by_cases hij' : i = j
    · subst hij'; exact step
    · exact eq_trans' ht (hS _ (List.getElem_mem _)) (hS _ (List.getElem_mem _))
        (hS _ (List.getElem_mem _)) (ih (by omega) (by omega)) step

theorem group_eq_mem {g : List MutConst} (hS : ∀ x ∈ g, S x)
    (hs : Sorted (fun x y => eqOf pc y x = .ok true) g)
    {x y : MutConst} (hx : x ∈ g) (hy : y ∈ g) (hxy : x ≠ y) : pc x y = .ok .eq := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · exact group_eq ht hS hs i j hi hj h
  · exact absurd rfl hxy
  · exact eq_symm' ht (hS _ (List.getElem_mem _)) (hS _ (List.getElem_mem _))
      (group_eq ht hS hs j i hj hi h)

/-- Across groups, an earlier group's members are below a later group's. -/
theorem groups_lt {gs : List (List MutConst)} (hS : ∀ g ∈ gs, ∀ x ∈ g, S x)
    (hok : GroupsOK (eqOf pc) gs) (hs : Sorted (LeC pc) gs.flatten) :
    ∀ (i j : Nat) (hij : i < j) (hj : j < gs.length),
      ∀ x ∈ gs[i]'(Nat.lt_trans hij hj), ∀ y ∈ gs[j], pc x y = .ok .lt := by
  have mS : ∀ (k : Nat) (hk : k < gs.length), ∀ x ∈ gs[k], S x :=
    fun k hk => hS _ (List.getElem_mem hk)
  -- the step between consecutive groups
  have step : ∀ (i : Nat) (hi : i + 1 < gs.length), ∀ x ∈ gs[i], ∀ y ∈ gs[i + 1], pc x y = .ok .lt := by
    intro i hi x hx y hy
    have hne := hok.nonempty
    obtain ⟨u, hu⟩ : ∃ u, gs[i].getLast? = some u := by
      cases h : gs[i].getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 h) (hne _ (List.getElem_mem _))
      | some u => exact ⟨u, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, gs[i + 1].head? = some v := by
      cases h : gs[i + 1].head? with
      | none => exact absurd (List.head?_eq_none_iff.1 h) (hne _ (List.getElem_mem _))
      | some v => exact ⟨v, rfl⟩
    have hu' : u ∈ gs[i] := List.mem_of_getLast? hu
    have hv' : v ∈ gs[i + 1] := List.mem_of_mem_head? hv
    have Su := mS i (by omega) u hu'
    have Sv := mS (i + 1) hi v hv'
    have huv : LeC pc u v := sorted_flatten_adjacent hs hne i hi u v hu hv
    have hbr := sorted_getElem hok.breaks i hi u v hu hv
    obtain ⟨o, ho, hne'⟩ := eqOf_false hbr
    have hvu : pc u v = .ok o.swap := ord_swap ht Sv Su ho
    obtain ⟨o', ho', hng⟩ := huv
    rw [hvu] at ho'; cases ho'
    have hlt : pc u v = .ok .lt := by
      rw [hvu]; cases o <;> simp_all [Ordering.swap]
    have hin := hok.inner
    have Sx := mS i (by omega) x hx
    have Sy := mS (i + 1) hi y hy
    have hxu : x = u ∨ pc x u = .ok .eq := by
      by_cases e : x = u
      · exact .inl e
      · exact .inr (group_eq_mem ht (mS i (by omega)) (hin _ (List.getElem_mem _)) hx hu' e)
    have hvy : v = y ∨ pc v y = .ok .eq := by
      by_cases e : v = y
      · exact .inl e
      · exact .inr (group_eq_mem ht (mS (i + 1) hi) (hin _ (List.getElem_mem _)) hv' hy e)
    rcases hxu with rfl | hxu <;> rcases hvy with rfl | hvy
    · exact hlt
    · exact lt_of_lt_le' ht Sx Sv Sy hlt (le_of_ok hvy (by decide))
    · exact lt_of_le_lt' ht Sx Su Sy (le_of_ok hxu (by decide)) hlt
    · exact lt_of_le_lt' ht Sx Su Sy (le_of_ok hxu (by decide))
        (lt_of_lt_le' ht Su Sv Sy hlt (le_of_ok hvy (by decide)))
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    intro x hx y hy
    by_cases hij' : i = j
    · subst hij'; exact step i hj x hx y hy
    · -- go through the first member of group `j`
      have hjne := hok.nonempty gs[j] (List.getElem_mem _)
      obtain ⟨z, hz⟩ : ∃ z, z ∈ gs[j] := by
        cases h : gs[j] with
        | nil => exact absurd h hjne
        | cons z _ => exact ⟨z, by simp⟩
      exact lt_of_lt_le' ht (mS i (by omega) x hx) (mS j (by omega) z hz) (mS (j + 1) hj y hy)
        (ih (by omega) (by omega) x hx z hz) (le_of_ok (step j hj z hz y hy) (by decide))

end class_

/-! ## The groups the code returns -/

/-- The classes one class splits into: the reference groups with the last
one reversed (`List.groupByM`), each re-sorted by name hash. -/
def repOf (groups : List (List MutConst)) : List (List MutConst) := (lastRev groups).map sortByName

theorem repOf_length (groups : List (List MutConst)) : (repOf groups).length = groups.length := by
  simp [repOf, lastRev_length]

theorem repOf_getElem_mem (groups : List (List MutConst)) (i : Nat)
    (h₁ : i < (repOf groups).length) (h₂ : i < groups.length) (x : MutConst) :
    x ∈ (repOf groups)[i] ↔ x ∈ groups[i] := by
  have h₁' : i < (lastRev groups).length := by simpa [repOf] using h₁
  simp only [repOf, List.getElem_map]
  exact (sortByName_perm _).mem_iff.trans (lastRev_getElem_mem groups i h₁' h₂ x)

theorem mem_repOf (groups : List (List MutConst)) (g : List MutConst) :
    g ∈ repOf groups → ∃ g' ∈ groups, ∀ x, x ∈ g ↔ x ∈ g' := by
  intro h
  simp only [repOf, List.mem_map] at h
  obtain ⟨g'', hg'', rfl⟩ := h
  obtain ⟨g', hg', hiff⟩ := mem_lastRev hg''
  exact ⟨g', hg', fun x => (sortByName_perm g'').mem_iff.trans (hiff x)⟩

/-- **One class**: its groups partition it, members of one group compare
`eq`, and the members of an earlier group compare `lt` against those of a
later one. -/
theorem refineClassP_spec (addr? : Name → Option Address) (ctx : MutCtx) {N : Name → Prop}
    (hN : Faithful N) (xs : List MutConst) (hxs : ∀ x ∈ xs, ConstIn N x)
    (gs : List (List MutConst)) (h : refineClassP addr? ctx xs = .ok gs) :
    gs.flatten.Perm xs ∧ (∀ g ∈ gs, g ≠ []) ∧
    (∀ g ∈ gs, ∀ x ∈ g, ∀ y ∈ g, x ≠ y → constOrd addr? ctx x y = .ok .eq) ∧
    (∀ (i j : Nat) (hij : i < j) (hj : j < gs.length), ∀ x ∈ gs[i]'(Nat.lt_trans hij hj),
      ∀ y ∈ gs[j], constOrd addr? ctx x y = .ok .lt) := by
  have ht := (constOrd_total addr? ctx hN).mono (S' := (· ∈ xs)) fun x hx => hxs x hx
  match xs, hxs, ht, h with
  | [], _, _, h => simp [refineClassP] at h
  | [x], _, _, h =>
    simp only [refineClassP, pure, Except.pure, Except.ok.injEq] at h; subst h
    refine ⟨by simp, by simp, ?_, fun i j hij hj => by simp at hj; omega⟩
    intro g hg a ha b hb hab
    simp at hg; subst hg; simp at ha hb; subst ha; subst hb; exact absurd rfl hab
  | x :: y :: rest, hxs, ht, h =>
    have hp := refineClassP_perm addr? ctx hN _ gs hxs h
    simp only [refineClassP] at h
    obtain ⟨sorted, hs, h⟩ := except_bind_ok.1 h
    obtain ⟨groups, hg, h⟩ := except_bind_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    obtain ⟨hsp, hsorted⟩ := sortByM_spec (constOrd_oriented addr? ctx hN (S := (· ∈ x :: y :: rest))
      fun z hz => hxs z hz) _ (fun _ h => h) sorted hs
    rw [groupByM_eq] at hg
    obtain ⟨G, hG, rfl⟩ : ∃ G, groupAdjP (eqOf (constOrd addr? ctx)) sorted = .ok G ∧ groups = lastRev G := by
      cases hG : groupAdjP (eqOf (constOrd addr? ctx)) sorted with
      | error e => rw [hG] at hg; cases hg
      | ok G => rw [hG] at hg; cases hg; exact ⟨G, rfl, rfl⟩
    obtain ⟨hok, hf⟩ := groupAdjP_spec _ _ _ hG
    rw [← hf] at hsorted
    have hGS : ∀ g ∈ G, ∀ z ∈ g, z ∈ x :: y :: rest := fun g hg z hz =>
      hsp.mem_iff.1 (hf ▸ List.mem_flatten.2 ⟨g, hg, hz⟩)
    change (repOf G).flatten.Perm _ ∧ (∀ g ∈ repOf G, g ≠ []) ∧ _ ∧ _
    change (repOf G).flatten.Perm _ at hp
    refine ⟨hp, fun g hg' => ?_, fun g hg' a ha b hb hab => ?_, fun i j hij hj a ha b hb => ?_⟩
    · obtain ⟨g', hg'', hiff⟩ := mem_repOf G g hg'
      intro e; subst e
      have := hok.nonempty g' hg''
      cases g' with
      | nil => exact this rfl
      | cons z _ => exact absurd ((hiff z).2 (by simp)) (by simp)
    · obtain ⟨g', hg'', hiff⟩ := mem_repOf G g hg'
      exact group_eq_mem ht (hGS g' hg'') (hok.inner g' hg'') ((hiff a).1 ha) ((hiff b).1 hb) hab
    · have hj' : j < G.length := by simpa [lastRev_length] using hj
      exact groups_lt ht hGS hok hsorted i j hij hj' a
        ((repOf_getElem_mem G i _ (Nat.lt_trans hij hj') a).1 ha) b
        ((repOf_getElem_mem G j hj hj' b).1 hb)

/-! ## A round -/

/-- Two members of one class end in one group when they compare `eq`. -/
theorem same_group_of_eq (addr? : Name → Option Address) (ctx : MutCtx) {N : Name → Prop}
    (hN : Faithful N) {xs : List MutConst} (hxs : ∀ x ∈ xs, ConstIn N x) {gs : List (List MutConst)}
    (h : refineClassP addr? ctx xs = .ok gs) {x y : MutConst} (hx : x ∈ xs) (hy : y ∈ xs)
    (he : constOrd addr? ctx x y = .ok .eq) : ∃ g ∈ gs, x ∈ g ∧ y ∈ g := by
  obtain ⟨hp, -, -, hlt⟩ := refineClassP_spec addr? ctx hN xs hxs gs h
  have ht := constOrd_total addr? ctx hN
  obtain ⟨gx, hgx, hxg⟩ := List.mem_flatten.1 (hp.mem_iff.2 hx)
  obtain ⟨gy, hgy, hyg⟩ := List.mem_flatten.1 (hp.mem_iff.2 hy)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgy
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · rw [hlt i j hij hj x hxg y hyg] at he; cases he
  · exact ⟨_, hgx, hxg, hyg⟩
  · have := ord_swap ht (hxs y hy) (hxs x hx) (hlt j i hij hi y hyg x hxg); rw [this] at he; cases he

/-- **A round**: each class is replaced by its groups. -/
theorem refineClassesP_spec (addr? : Name → Option Address) (ctx : MutCtx) {N : Name → Prop}
    (hN : Faithful N) : ∀ (classes refined : List (List MutConst)), (∀ C ∈ classes, C ≠ []) →
      (∀ C ∈ classes, ∀ x ∈ C, ConstIn N x) →
      refineClassesP addr? ctx classes = .ok refined →
      refined.flatten.Perm classes.flatten ∧ (∀ g ∈ refined, g ≠ []) ∧ Refines refined classes ∧
      (∀ C ∈ classes, ∀ x ∈ C, ∀ y ∈ C, constOrd addr? ctx x y = .ok .eq →
        ∃ g ∈ refined, x ∈ g ∧ y ∈ g) ∧
      (∀ g ∈ refined, ∀ x ∈ g, ∀ y ∈ g, x ≠ y → constOrd addr? ctx x y = .ok .eq) ∧
      classes.length ≤ refined.length ∧
      (classes.length = refined.length → ∀ C ∈ classes, ∃ g ∈ refined, ∀ x, x ∈ g ↔ x ∈ C)
  | [], refined, _, _, h => by
    simp only [refineClassesP, pure, Except.pure, Except.ok.injEq] at h; subst h
    refine ⟨List.Perm.refl _, by simp, fun C hC => by simp at hC, by simp, by simp, by simp, by simp⟩
  | c :: cs, refined, hne, hin, h => by
    simp only [refineClassesP] at h
    obtain ⟨gs, hgs, h⟩ := except_bind_ok.1 h
    obtain ⟨rest, hr, h⟩ := except_bind_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have hc := hin c (by simp)
    obtain ⟨hp, hgne, heq, -⟩ := refineClassP_spec addr? ctx hN c hc gs hgs
    obtain ⟨rp, rne, rref, rsame, req, rlen, rone⟩ :=
      refineClassesP_spec addr? ctx hN cs rest (fun C hC => hne C (by simp [hC]))
        (fun C hC => hin C (by simp [hC])) hr
    have hgs1 : 1 ≤ gs.length := by
      cases gs with
      | nil =>
        have : c = [] := List.nil_perm.1 (by simpa using hp)
        exact absurd this (hne c (by simp))
      | cons _ _ => simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.flatten_append, List.flatten_cons]; exact hp.append rp
    · intro g hg; rcases List.mem_append.1 hg with hg | hg
      · exact hgne g hg
      · exact rne g hg
    · intro g hg m hm m' hm'
      rcases List.mem_append.1 hg with hg | hg
      · exact ⟨c, by simp, hp.mem_iff.1 (List.mem_flatten.2 ⟨g, hg, hm⟩),
          hp.mem_iff.1 (List.mem_flatten.2 ⟨g, hg, hm'⟩)⟩
      · obtain ⟨D, hD, h1, h2⟩ := rref g hg m hm m' hm'
        exact ⟨D, by simp [hD], h1, h2⟩
    · intro C hC x hx y hy he
      rcases List.mem_cons.1 hC with rfl | hC
      · obtain ⟨g, hg, h1, h2⟩ := same_group_of_eq addr? ctx hN hc hgs hx hy he
        exact ⟨g, List.mem_append_left _ hg, h1, h2⟩
      · obtain ⟨g, hg, h1, h2⟩ := rsame C hC x hx y hy he
        exact ⟨g, List.mem_append_right _ hg, h1, h2⟩
    · intro g hg x hx y hy hxy
      rcases List.mem_append.1 hg with hg | hg
      · exact heq g hg x hx y hy hxy
      · exact req g hg x hx y hy hxy
    · simp only [List.length_cons, List.length_append]; omega
    · intro hl C hC
      simp only [List.length_cons, List.length_append] at hl
      have hg1 : gs.length = 1 := by omega
      rcases List.mem_cons.1 hC with rfl | hC
      · obtain ⟨g, hgl⟩ : ∃ g, gs = [g] := by
          cases gs with
          | nil => simp at hg1
          | cons g t => cases t with
            | nil => exact ⟨g, rfl⟩
            | cons _ _ => simp at hg1
        subst hgl
        exact ⟨g, by simp, fun x => by simpa using hp.mem_iff (a := x)⟩
      · obtain ⟨g, hg, hiff⟩ := rone (by omega) C hC
        exact ⟨g, List.mem_append_right _ hg, hiff⟩

end Ix.CompileCert.Canon
