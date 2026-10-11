import Ix.CompileCert.Canon.Seed
import Ix.CompileCert.Canon.SortOk

/-!
# M7 L1, the class order does not depend on the seed

Design document §3.3 (c): "the ordered list of classes at round `n`, each class as a *set*,
is a function of the content alone … Hence the partition and the class order are
seed-independent, and the representative is the only seed-dependent output."

`sortClasses_setEq`: two runs of `sortClasses` on permutations of one member list, under rule
sets that agree on the level rule and the tie-break (they may differ in the seed, the
representative rule and the nested order), give the same ordered list of classes, class by
class as sets (`SetEq`: each class of one run a permutation of the class at the same position
in the other), as soon as one of them succeeds.

The argument is the paper's, by lockstep rounds: the context of a round depends only on the
classes as sets (`ctx_setEq`), so the round's comparison is the same in both runs
(`constOrd_lookup`); a successful round orders every pair of distinct members of a class, so
the other run's sort and grouping succeed on its permutation of the class (`SortOk.lean`); and
an ordered partition into the classes of a total preorder is unique (`ordPart_unique`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name MutConst MutCtx)

/-! ## Ordered lists of classes, equal class by class as sets -/

/-- The same classes in the same order, each class a permutation of the other's. -/
inductive SetEq {α : Type} : List (List α) → List (List α) → Prop
  | nil : SetEq [] []
  | cons {C D : List α} {P Q : List (List α)} : C.Perm D → SetEq P Q → SetEq (C :: P) (D :: Q)

theorem SetEq.refl {α : Type} : ∀ (P : List (List α)), SetEq P P
  | [] => SetEq.nil
  | C :: P => SetEq.cons (List.Perm.refl C) (SetEq.refl P)

theorem isEmpty_perm {α : Type} {C D : List α} (h : C.Perm D) : C.isEmpty = D.isEmpty := by
  cases C <;> cases D
  · rfl
  · exact absurd h.length_eq (by simp)
  · exact absurd h.length_eq (by simp)
  · rfl

theorem SetEq.length {P Q : List (List MutConst)} (h : SetEq P Q) : P.length = Q.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem SetEq.flatten {P Q : List (List MutConst)} (h : SetEq P Q) : P.flatten.Perm Q.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons hab _ ih => simp only [List.flatten_cons]; exact hab.append ih

theorem SetEq.append {P Q P' Q' : List (List MutConst)} (h : SetEq P Q) (h' : SetEq P' Q') :
    SetEq (P ++ P') (Q ++ Q') := by
  induction h with
  | nil => exact h'
  | cons hab _ ih => exact SetEq.cons hab ih

theorem SetEq.getElem? {P Q : List (List MutConst)} (h : SetEq P Q) :
    ∀ {j : Nat} {C : List MutConst}, P[j]? = some C → ∃ D, Q[j]? = some D ∧ C.Perm D := by
  induction h with
  | nil => intro j C hC; simp only [List.getElem?_nil, reduceCtorEq] at hC
  | cons hab _ ih =>
    intro j C hC
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hC; subst hC
      exact ⟨_, rfl, hab⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hC ⊢
      exact ih hC

theorem SetEq.any_isEmpty {P Q : List (List MutConst)} (h : SetEq P Q) :
    P.any (·.isEmpty) = Q.any (·.isEmpty) := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    simp only [List.any_cons, ih, isEmpty_perm hab]

/-! ## The context depends on the classes as sets -/

theorem maxC_perm {C D : List MutConst} (h : C.Perm D) : maxC C = maxC D := by
  unfold maxC
  exact h.foldl_eq' (fun x _ y _ z => by
    show max (max z x.ctors.size) y.ctors.size = max (max z y.ctors.size) x.ctors.size
    omega) 0

theorem offs_setEq {P Q : List (List MutConst)} (h : SetEq P Q) (j : Nat) : offs P j = offs Q j := by
  unfold offs
  induction h generalizing j with
  | nil => rfl
  | cons hab _ ih =>
    cases j with
    | zero => rfl
    | succ j => simp only [List.take_succ_cons, sumMaxC]; rw [maxC_perm hab, ih]

theorem any_beq_perm {l l' : List Name} (h : l.Perm l') (x : Name) :
    l.any (· == x) = l'.any (· == x) := h.any_eq

/-- **The context of a partition depends only on its classes as sets** (lookups agree). -/
theorem ctx_setEq {P Q : List (List MutConst)} (h : SetEq P Q) (hk : KeysDistinct P.flatten)
    (x : Name) : (MutConst.ctx P)[x]? = (MutConst.ctx Q)[x]? := by
  have hkQ : KeysDistinct Q.flatten := hk.perm h.flatten
  cases hv : (MutConst.ctx P)[x]? with
  | some v =>
    obtain ⟨j, C, m, hC, hm, hx⟩ := ctx_val hk hv
    obtain ⟨D, hD, pCD⟩ := h.getElem? hC
    have hmD := pCD.mem_iff.1 hm
    rcases hx with ⟨hxe, rfl⟩ | ⟨k, c, hc, hxe, rfl⟩
    · rw [← mutCtx_getElem?_congr _ hxe, ctx_member hkQ hD hmD]
    · rw [← mutCtx_getElem?_congr _ hxe, ctx_ctor hkQ hD hmD hc, h.length, offs_setEq h]
  | none =>
    have dP := ctx_dom P x
    have dQ := ctx_dom Q x
    rw [hv, any_beq_perm (List.Perm.flatMap_right keysOf h.flatten)] at dP
    rw [← dP] at dQ
    cases hw : (MutConst.ctx Q)[x]? with
    | none => rfl
    | some _ => rw [hw] at dQ; cases dQ

/-! ## Comparisons under contexts with the same lookups -/

/-- An `ok` result is kept. -/
def OkRel (r r' : Except String SOrder) : Prop := ∀ v, r = .ok v → r' = .ok v

theorem okRel : ResRel OkRel where
  refl _ _ h := h
  err _ _ _ h := by cases h
  cmpM {a a' b b'} ha hb v h := by
    obtain ⟨x, hx, (⟨hne, he⟩ | ⟨heq, y, hy, he⟩)⟩ := cmpM_ok.1 h
    · exact cmpM_ok.2 ⟨x, ha _ hx, .inl ⟨hne, he⟩⟩
    · exact cmpM_ok.2 ⟨x, ha _ hx, .inr ⟨heq, y, hb _ hy, he⟩⟩
  lexIf {a b b'} hb v h := by
    obtain ⟨x, hx, (⟨hne, he⟩ | ⟨heq, hy⟩)⟩ := lexIf_ok.1 h
    · exact lexIf_ok.2 ⟨x, hx, .inl ⟨hne, he⟩⟩
    · exact lexIf_ok.2 ⟨x, hx, .inr ⟨heq, hb _ hy⟩⟩

theorem compareRef_lookup {c c' : CmpCtx} (hm : c.mode = c'.mode) (ha : c.addr? = c'.addr?)
    (h : ∀ n : Name, c.mutCtx[n]? = c'.mutCtx[n]?) (x y : Name) : compareRef c x y = compareRef c' x y := by
  unfold compareRef compareExternal
  simp only [Std.TreeMap.get?_eq_getElem?, h x, h y, hm, ha]

theorem mapOrd_ok {r r' : Except String SOrder} (h : OkRel r r') {o : Ordering}
    (e : r.map (·.ord) = .ok o) : r'.map (·.ord) = .ok o := by
  cases hr : r with
  | error _ => rw [hr] at e; cases e
  | ok v => rw [hr] at e; rw [h v hr]; exact e

/-- **The round's comparison reads the context only through its lookups, and the rule set only
through the level rule and the tie-break.** -/
theorem constOrd_lookup {r₁ r₂ : Rules} (hl : r₁.levels = r₂.levels) (ht : r₁.tieBreak = r₂.tieBreak)
    (addr? : Name → Option Address) {m₁ m₂ : MutCtx} (hm : ∀ n : Name, m₁[n]? = m₂[n]?) (x y : MutConst)
    {o : Ordering} (h : constOrd r₁ addr? m₁ x y = .ok o) : constOrd r₂ addr? m₂ x y = .ok o := by
  have key : ∀ mode, OkRel (constP (ctxOf r₁ addr? mode m₁) x y) (constP (ctxOf r₂ addr? mode m₂) x y) :=
    fun mode => constP_rel okRel _ _ hl (fun a b v e => by
      rw [← compareRef_lookup (c := ctxOf r₁ addr? mode m₁) (c' := ctxOf r₂ addr? mode m₂) rfl rfl hm]
      exact e) x y
  unfold constOrd at h ⊢
  rw [← ht]
  cases htb : r₁.tieBreak with
  | inline => simp only [htb] at h ⊢; exact mapOrd_ok (key _) h
  | blind => simp only [htb] at h ⊢; exact mapOrd_ok (key _) h
  | byAddress =>
    simp only [htb] at h ⊢
    obtain ⟨b, hb, h⟩ := except_bind_ok.1 h
    rw [mapOrd_ok (key _) hb]
    simp only [bind, Except.bind]
    by_cases hbe : (b != .eq) = true
    · simp only [hbe, ↓reduceIte] at h ⊢; exact h
    · simp only [hbe, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact mapOrd_ok (key _) h

theorem constOrd_lookup_iff {r₁ r₂ : Rules} (hl : r₁.levels = r₂.levels) (ht : r₁.tieBreak = r₂.tieBreak)
    (addr? : Name → Option Address) {m₁ m₂ : MutCtx} (hm : ∀ n : Name, m₁[n]? = m₂[n]?) (x y : MutConst)
    (o : Ordering) : constOrd r₁ addr? m₁ x y = .ok o ↔ constOrd r₂ addr? m₂ x y = .ok o :=
  ⟨constOrd_lookup hl ht addr? hm x y, constOrd_lookup hl.symm ht.symm addr? (fun n => (hm n).symm) x y⟩

/-! ## An ordered partition into the classes of a total preorder is unique -/

section unique
variable {α ε : Type} {pc : α → α → Except ε Ordering}

/-- An ordered partition into classes of `pc`: nonempty groups, distinct members of one group
compare `eq`, members of an earlier group compare `lt` against a later one's. -/
structure OrdPart (pc : α → α → Except ε Ordering) (G : List (List α)) : Prop where
  ne : ∀ g ∈ G, g ≠ []
  eq : ∀ g ∈ G, ∀ x ∈ g, ∀ y ∈ g, x ≠ y → pc x y = .ok .eq
  lt : ∀ (i j : Nat) (hij : i < j) (hj : j < G.length), ∀ x ∈ G[i]'(Nat.lt_trans hij hj),
    ∀ y ∈ G[j], pc x y = .ok .lt

theorem OrdPart.tail {g : List α} {G : List (List α)} (h : OrdPart pc (g :: G)) : OrdPart pc G where
  ne g' hg := h.ne g' (List.mem_cons_of_mem _ hg)
  eq g' hg := h.eq g' (List.mem_cons_of_mem _ hg)
  lt i j hij hj x hx y hy :=
    h.lt (i + 1) (j + 1) (by omega) (by simp only [List.length_cons]; omega) x
      (by simpa only [List.getElem_cons_succ] using hx) y (by simpa only [List.getElem_cons_succ] using hy)

theorem OrdPart.head_lt {g : List α} {G : List (List α)} (h : OrdPart pc (g :: G)) {x : α} (hx : x ∈ g)
    {y : α} (hy : y ∈ G.flatten) : pc x y = .ok .lt := by
  obtain ⟨g', hg', hyg⟩ := List.mem_flatten.1 hy
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
  exact h.lt 0 (j + 1) (by omega) (by simp only [List.length_cons]; omega) x
    (by simpa only [List.getElem_cons_zero] using hx) y (by simpa only [List.getElem_cons_succ] using hyg)

theorem ordPart_head_sub (hor : ∀ a b o, pc a b = .ok o → pc b a = .ok o.swap) {g g' : List α}
    {G G' : List (List α)} (h : OrdPart pc (g :: G)) (h' : OrdPart pc (g' :: G'))
    (hp : (g ++ G.flatten).Perm (g' ++ G'.flatten)) {x : α} (hx : x ∈ g) : x ∈ g' := by
  rcases List.mem_append.1 (hp.mem_iff.1 (List.mem_append_left _ hx)) with hx' | hx'
  · exact hx'
  · exfalso
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil g' (h'.ne g' (List.mem_cons_self ..))
    have hyx : pc y x = .ok .lt := h'.head_lt hy hx'
    rcases List.mem_append.1 (hp.mem_iff.2 (List.mem_append_left _ hy)) with hy' | hy'
    · by_cases e : y = x
      · subst e; have := hor _ _ _ hyx; rw [hyx] at this; cases this
      · rw [h.eq g (List.mem_cons_self ..) y hy' x hx e] at hyx; cases hyx
    · have := hor _ _ _ (h.head_lt hx hy'); rw [hyx] at this; cases this

/-- **Uniqueness**: two ordered partitions of the same members into classes of one oriented
comparison are equal class by class as sets. -/
theorem ordPart_unique (hor : ∀ a b o, pc a b = .ok o → pc b a = .ok o.swap) :
    ∀ {G G' : List (List α)}, OrdPart pc G → OrdPart pc G' → G.flatten.Nodup →
      G.flatten.Perm G'.flatten → SetEq G G'
  | [], [], _, _, _, _ => SetEq.nil
  | [], g' :: G', _, h', _, hp => by
    exfalso
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil g' (h'.ne g' (List.mem_cons_self ..))
    have := hp.mem_iff.2 (List.mem_flatten.2 ⟨g', List.mem_cons_self .., hy⟩)
    simp only [List.flatten_nil, List.not_mem_nil] at this
  | g :: G, [], h, _, _, hp => by
    exfalso
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil g (h.ne g (List.mem_cons_self ..))
    have := hp.mem_iff.1 (List.mem_flatten.2 ⟨g, List.mem_cons_self .., hy⟩)
    simp only [List.flatten_nil, List.not_mem_nil] at this
  | g :: G, g' :: G', h, h', hn, hp => by
    simp only [List.flatten_cons] at hn hp
    have hn' : (g' ++ G'.flatten).Nodup := hp.nodup_iff.1 hn
    have e : g.Perm g' := (List.perm_ext_iff_of_nodup (List.nodup_append.1 hn).1
      (List.nodup_append.1 hn').1).2 fun x =>
        ⟨ordPart_head_sub hor h h' hp, ordPart_head_sub hor h' h hp.symm⟩
    exact SetEq.cons e (ordPart_unique hor h.tail h'.tail (List.nodup_append.1 hn).2.1
      ((List.perm_append_left_iff g).1 (hp.trans (List.Perm.append_right _ e.symm))))

end unique

/-! ## One round, in lockstep -/

theorem KeysDistinct.nodup {l : List MutConst} (h : KeysDistinct l) : l.Nodup := by
  have hn := h.names
  unfold NamesDistinct at hn
  rw [List.pairwise_map] at hn
  exact List.nodup_iff_pairwise_ne.2 (hn.imp fun {a b} e hab => by
    subst hab; rw [name_beq_refl] at e; cases e)

theorem ordPart_ok {pc : MutConst → MutConst → Except String Ordering}
    (ht : TotalPre (fun a b => liftOrd (pc a b))) {G : List (List MutConst)} (h : OrdPart pc G)
    {x y : MutConst} (hx : x ∈ G.flatten) (hy : y ∈ G.flatten) (hxy : x ≠ y) : ∃ o, pc x y = .ok o := by
  obtain ⟨gx, hgx, hxg⟩ := List.mem_flatten.1 hx
  obtain ⟨gy, hgy, hyg⟩ := List.mem_flatten.1 hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgy
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exact ⟨_, h.lt i j hij hj x hxg y hyg⟩
  · exact ⟨_, h.eq _ hgx x hxg y hyg hxy⟩
  · exact ⟨_, ord_swap ht (h.lt j i hij hi y hyg x hxg)⟩

theorem ordPart_of_spec {pc : MutConst → MutConst → Except String Ordering} {G : List (List MutConst)}
    (hne : ∀ g ∈ G, g ≠ []) (heq : ∀ g ∈ G, ∀ x ∈ g, ∀ y ∈ g, x ≠ y → pc x y = .ok .eq)
    (hlt : ∀ (i j : Nat) (hij : i < j) (hj : j < G.length), ∀ x ∈ G[i]'(Nat.lt_trans hij hj),
      ∀ y ∈ G[j], pc x y = .ok .lt) : OrdPart pc G := ⟨hne, heq, hlt⟩

theorem OrdPart.transport {pc pc' : MutConst → MutConst → Except String Ordering}
    (e : ∀ x y o, pc x y = .ok o → pc' x y = .ok o) {G : List (List MutConst)} (h : OrdPart pc G) :
    OrdPart pc' G :=
  ⟨h.ne, fun g hg x hx y hy hxy => e _ _ _ (h.eq g hg x hx y hy hxy),
    fun i j hij hj x hx y hy => e _ _ _ (h.lt i j hij hj x hx y hy)⟩

section lockstep
variable {r₁ r₂ : Rules} (hl : r₁.levels = r₂.levels) (ht : r₁.tieBreak = r₂.tieBreak)
  {addr? : Name → Option Address} (hA : AddrCongr addr?)
include hl ht hA

/-- **One class, in lockstep**: the same class under the same lookups, in another order and under
the other rule set, splits into the same groups as sets, in the same order. -/
theorem refineClassP_setEq {m₁ m₂ : MutCtx} (hm : ∀ n : Name, m₁[n]? = m₂[n]?) {C C' : List MutConst}
    (hC : C.Perm C') (hn : C.Nodup) {G : List (List MutConst)}
    (h : refineClassP r₁ addr? m₁ C = .ok G) :
    ∃ G', refineClassP r₂ addr? m₂ C' = .ok G' ∧ SetEq G G' := by
  have tr := constOrd_lookup_iff hl ht addr? hm
  have ht₁ := constOrd_total r₁ hA m₁
  obtain ⟨hp, hne, heq, hlt⟩ := refineClassP_spec r₁ hA m₁ C G h
  have hG : OrdPart (constOrd r₁ addr? m₁) G := ⟨hne, heq, hlt⟩
  have hn' : C'.Nodup := hC.nodup_iff.1 hn
  match C', hC, hn' with
  | [], hC, _ =>
    have : C = [] := List.Perm.eq_nil hC
    subst this; simp [refineClassP] at h
  | [x], hC, _ =>
    have : C = [x] := List.perm_singleton.1 hC
    subst this
    simp only [refineClassP, pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨_, rfl, SetEq.refl _⟩
  | x :: y :: rest, hC, hn' =>
    -- every two distinct members compare, in both orders, under the second run's comparison
    have hboth : (x :: y :: rest).Pairwise (BothOk (constOrd r₂ addr? m₂)) := by
      refine (List.nodup_iff_pairwise_ne.1 hn').imp_of_mem fun {a b} ha hb hab => ?_
      have ha' : a ∈ G.flatten := hp.mem_iff.2 (hC.mem_iff.2 ha)
      have hb' : b ∈ G.flatten := hp.mem_iff.2 (hC.mem_iff.2 hb)
      obtain ⟨o, ho⟩ := ordPart_ok ht₁ hG ha' hb' hab
      obtain ⟨o', ho'⟩ := ordPart_ok ht₁ hG hb' ha' (Ne.symm hab)
      exact ⟨⟨o, (tr a b o).1 ho⟩, ⟨o', (tr b a o').1 ho'⟩⟩
    have hor₂ := constOrd_oriented r₂ hA m₂ (S := fun _ => True)
    obtain ⟨sorted, hs⟩ := sortByM_ok hor₂ _ hboth
    obtain ⟨psorted, -⟩ := sortByM_spec hor₂ _ (fun _ _ => trivial) sorted hs
    have hboth' := pairwise_bothOk_perm psorted.symm hboth
    obtain ⟨groups, hg⟩ := groupAdjP_ok (eqOf (constOrd r₂ addr? m₂)) sorted (hboth'.imp fun {a b} hab => by
      obtain ⟨o, ho⟩ := hab.2
      exact ⟨o == .eq, by simp only [eqOf, ho, bind, Except.bind, pure, Except.pure]⟩)
    have h₂ : refineClassP r₂ addr? m₂ (x :: y :: rest) = .ok (repOf r₂ groups) := by
      simp only [refineClassP, hs, hg, bind, Except.bind, pure, Except.pure]
    obtain ⟨hp', hne', heq', hlt'⟩ := refineClassP_spec r₂ hA m₂ _ _ h₂
    have hG' : OrdPart (constOrd r₁ addr? m₁) (repOf r₂ groups) :=
      OrdPart.transport (fun a b o => (tr a b o).2) ⟨hne', heq', hlt'⟩
    refine ⟨_, h₂, ordPart_unique (fun a b o e => ord_swap ht₁ e) hG hG' (hp.nodup_iff.2 hn)
      (hp.trans (hC.trans hp'.symm))⟩

/-- **A round, in lockstep.** -/
theorem refineClassesP_setEq {m₁ m₂ : MutCtx} (hm : ∀ n : Name, m₁[n]? = m₂[n]?) :
    ∀ {P Q : List (List MutConst)}, SetEq P Q → P.flatten.Nodup → ∀ {R : List (List MutConst)},
      refineClassesP r₁ addr? m₁ P = .ok R →
      ∃ R', refineClassesP r₂ addr? m₂ Q = .ok R' ∧ SetEq R R' := by
  intro P Q h
  induction h with
  | nil =>
    intro _ R hR
    simp only [refineClassesP, pure, Except.pure, Except.ok.injEq] at hR; subst hR
    exact ⟨[], rfl, SetEq.nil⟩
  | cons hab _ ih =>
    intro hn R hR
    simp only [List.flatten_cons] at hn
    simp only [refineClassesP] at hR
    obtain ⟨gs, hgs, hR⟩ := except_bind_ok.1 hR
    obtain ⟨rest, hrest, hR⟩ := except_bind_ok.1 hR
    simp only [pure, Except.pure, Except.ok.injEq] at hR; subst hR
    obtain ⟨gs', hgs', e1⟩ := refineClassP_setEq hl ht hA hm hab (List.nodup_append.1 hn).1 hgs
    obtain ⟨rest', hrest', e2⟩ := ih (List.nodup_append.1 hn).2.1 hrest
    refine ⟨gs' ++ rest', ?_, e1.append e2⟩
    simp only [refineClassesP, hgs', hrest', bind, Except.bind, pure, Except.pure]

/-- **The loop, in lockstep**: the same number of rounds, the same classes as sets. -/
theorem sortLoopP_setEq : ∀ (fuel round : Nat) {P Q : List (List MutConst)}, SetEq P Q →
    KeysDistinct P.flatten → (∀ C ∈ P, C ≠ []) → ∀ {F : List (List MutConst)} {n : Nat},
    sortLoopP r₁ addr? fuel round P = .ok (F, n) →
    ∃ F', sortLoopP r₂ addr? fuel round Q = .ok (F', n) ∧ SetEq F F' := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ h; simp [sortLoopP] at h
  | succ fuel ih =>
    intro round P Q hPQ hk hne F n h
    simp only [sortLoopP] at h ⊢
    obtain ⟨refined, hr, h⟩ := except_bind_ok.1 h
    have hm := ctx_setEq hPQ hk
    obtain ⟨refined', hr', e⟩ := refineClassesP_setEq hl ht hA hm hPQ hk.nodup hr
    obtain ⟨rp, rne, -⟩ := refineClassesP_spec r₁ hA _ P refined hne hr
    rw [hr']
    simp only [bind, Except.bind]
    rw [← hPQ.length, ← e.length]
    split at h
    · rename_i hc
      simp only [hc, ↓reduceIte]
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨refined', ⟨rfl, rfl⟩, e⟩
    · rename_i hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ih (round + 1) e (hk.perm rp.symm) rne h

end lockstep

/-- **The pure refinement, in lockstep**: permuted input, another seed or representative rule,
the same ordered classes as sets. -/
theorem sortClassesP_setEq {r₁ r₂ : Rules} (hl : r₁.levels = r₂.levels) (ht : r₁.tieBreak = r₂.tieBreak)
    {addr? : Name → Option Address} (hA : AddrCongr addr?) {xs ys : List MutConst} (hp : xs.Perm ys)
    (hk : KeysDistinct xs) {F : List (List MutConst)} (h : sortClassesP r₁ addr? xs = .ok F) :
    ∃ F', sortClassesP r₂ addr? ys = .ok F' ∧ SetEq F F' := by
  unfold sortClassesP at h ⊢
  by_cases he : xs.isEmpty = true
  · have : xs = [] := by simpa using he
    subst this
    have : ys = [] := List.Perm.eq_nil hp.symm
    subst this
    simp only [List.isEmpty_nil, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h ⊢; subst h
    exact ⟨[], rfl, SetEq.nil⟩
  · have he' : ys.isEmpty = false := by
      cases ys with
      | nil => exact absurd (by simpa using List.Perm.eq_nil hp) he
      | cons _ _ => rfl
    have he₁ : xs.isEmpty = false := by simpa using he
    simp only [he₁, he', Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨⟨classes, rounds⟩, hlp, h⟩ := except_bind_ok.1 h
    have hseed : SetEq [seedOf r₁ xs] [seedOf r₂ ys] :=
      SetEq.cons (((seedOf_perm r₁ xs).trans hp).trans (seedOf_perm r₂ ys).symm) SetEq.nil
    have hk₁ : KeysDistinct [seedOf r₁ xs].flatten := by
      simpa using hk.perm (seedOf_perm r₁ xs).symm
    have hne₁ : ∀ C ∈ [seedOf r₁ xs], C ≠ [] := by
      intro C hC
      simp only [List.mem_singleton] at hC; subst hC
      intro e
      have := (seedOf_perm r₁ xs).symm
      rw [e] at this
      exact he (by simpa using List.Perm.eq_nil this)
    obtain ⟨F', hlp', e⟩ := sortLoopP_setEq hl ht hA (xs.length + 1) 0 hseed hk₁ hne₁ hlp
    rw [← hp.length_eq, hlp']
    simp only [bind, Except.bind]
    rw [← e.any_isEmpty, ← e.length]
    split at h
    · cases h
    · rename_i hany
      simp only [hany, Bool.false_eq_true, ↓reduceIte]
      split at h
      · cases h
      · rename_i hlen
        simp only [hlen, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h ⊢
        subst h
        exact ⟨F', rfl, e⟩

/-- **The class order does not depend on the seed** (design document §3.3 (c); §3.5 (iii)).
Two runs of `sortClasses` on permutations of the members, under rule sets with the port fixes
that agree on the level rule and the tie-break (the seed, the representative rule and the nested
order may differ), give the same classes in the same order, each class the same set of members,
as soon as one of them succeeds: the order of members inside a class, so the representative, is
the only output the seed can change. -/
theorem sortClasses_setEq {r₁ r₂ : Rules} (hpf₁ : r₁.portFixes = true) (hpf₂ : r₂.portFixes = true)
    (hl : r₁.levels = r₂.levels) (ht : r₁.tieBreak = r₂.tieBreak) {addr? : Name → Option Address}
    (hA : AddrCongr addr?) {xs ys : List MutConst} (hp : xs.Perm ys) (hk : KeysDistinct xs)
    {F : List (List MutConst)} {stats : SortStats} (h : sortClasses r₁ addr? xs = .ok (F, stats)) :
    ∃ F' stats', sortClasses r₂ addr? ys = .ok (F', stats') ∧ SetEq F F' := by
  have e₁ := sortClasses_eq hpf₁ hA hk
  rw [h] at e₁
  obtain ⟨F', h', e⟩ := sortClassesP_setEq hl ht hA hp hk e₁.symm
  have e₂ := sortClasses_eq hpf₂ hA (hk.perm hp)
  rw [h'] at e₂
  cases h₂ : sortClasses r₂ addr? ys with
  | error err => rw [h₂] at e₂; cases e₂
  | ok v =>
    rw [h₂] at e₂
    simp only [Except.map, Except.ok.injEq] at e₂
    refine ⟨v.1, v.2, rfl, ?_⟩
    rw [e₂]; exact e

end Ix.CompileCert.Canon
