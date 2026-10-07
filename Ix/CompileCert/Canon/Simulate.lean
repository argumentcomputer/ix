import Ix.CompileCert.Canon.SeedFree

/-!
# M7 L1, the refinement under a change of presentation

A general lockstep for Def 4.3's presentations. Run 1 refines the members `xs`; run 2 refines
`ys`, a permutation of the members of `xs` that `keep` selects, each mapped by `φ` (a renaming,
or a representative standing for its class). If run 1 succeeds with classes `F`, every class of
`F` keeps a member, and at every round partition `P` that `F` refines the two comparisons agree
on kept members (`T`: run 1's under `P`'s context, run 2's under the context of `P` restricted
and mapped), then run 2 succeeds with the classes of `F` restricted and mapped, in the same order
(`sortClassesP_sim`).

`SeedFree` is the case `keep = true`, `φ = id`; renaming (`Rename.lean`) keeps every member and
maps it to its renamed copy; collapse keeps one member per class.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name MutConst MutCtx)

/-- The kept members of a class, mapped. -/
def restrictC (keep : MutConst → Bool) (φ : MutConst → MutConst) (C : List MutConst) : List MutConst :=
  (C.filter keep).map φ

/-- The kept members of each class, mapped. -/
def restrictP (keep : MutConst → Bool) (φ : MutConst → MutConst) (P : List (List MutConst)) :
    List (List MutConst) :=
  P.map (restrictC keep φ)

section
variable {keep : MutConst → Bool} {φ : MutConst → MutConst}

theorem mem_restrictC {C : List MutConst} {x : MutConst} :
    x ∈ restrictC keep φ C ↔ ∃ a ∈ C, keep a = true ∧ φ a = x := by
  unfold restrictC
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, (List.mem_filter.1 ha).1, (List.mem_filter.1 ha).2, rfl⟩
  · rintro ⟨a, ha, hk, rfl⟩; exact ⟨a, List.mem_filter.2 ⟨ha, hk⟩, rfl⟩

theorem restrictP_flatten (P : List (List MutConst)) :
    (restrictP keep φ P).flatten = restrictC keep φ P.flatten := by
  induction P with
  | nil => rfl
  | cons C P ih =>
    simp only [restrictP, List.map_cons, List.flatten_cons] at ih ⊢
    rw [ih]; unfold restrictC; rw [List.filter_append, List.map_append]

theorem restrictC_perm {C D : List MutConst} (h : C.Perm D) :
    (restrictC keep φ C).Perm (restrictC keep φ D) :=
  (h.filter keep).map φ

theorem restrictP_length (P : List (List MutConst)) : (restrictP keep φ P).length = P.length :=
  List.length_map _

theorem restrictC_ne {C : List MutConst} (h : ∃ a ∈ C, keep a = true) : restrictC keep φ C ≠ [] := by
  obtain ⟨a, ha, hk⟩ := h
  intro e
  have : φ a ∈ restrictC keep φ C := mem_restrictC.2 ⟨a, ha, hk, rfl⟩
  rw [e] at this; cases this

theorem restrictP_getElem {P : List (List MutConst)} {i : Nat} (hi : i < (restrictP keep φ P).length)
    (hi' : i < P.length) : (restrictP keep φ P)[i] = restrictC keep φ P[i] :=
  List.getElem_map _

end

theorem mem_unique_of_nodup {P : List (List MutConst)} (hn : P.flatten.Nodup) :
    ∀ {g g' : List MutConst}, g ∈ P → g' ∈ P → ∀ {m : MutConst}, m ∈ g → m ∈ g' → g = g' := by
  induction P with
  | nil => intro g _ hg; cases hg
  | cons h P ih =>
    intro g g' hg hg' m hm hm'
    rw [List.flatten_cons] at hn
    have hd := (List.nodup_append.1 hn).2.2
    rcases List.mem_cons.1 hg with e | hg1 <;> rcases List.mem_cons.1 hg' with e' | hg1'
    · rw [e, e']
    · subst e; exact absurd rfl (hd m hm m (List.mem_flatten.2 ⟨g', hg1', hm'⟩))
    · subst e'; exact absurd rfl (hd m hm' m (List.mem_flatten.2 ⟨g, hg1, hm⟩))
    · exact ih (List.nodup_append.1 hn).2.1 hg1 hg1' hm hm'

/-! ## One class -/

section lockstep
variable {r₁ r₂ : Rules} {a₁ a₂ : Name → Option Address} (hA₁ : AddrCongr a₁) (hA₂ : AddrCongr a₂)
  {keep : MutConst → Bool} {φ : MutConst → MutConst}
include hA₁ hA₂

/-- **One class, simulated.** -/
theorem refineClassP_sim {m₁ m₂ : MutCtx} {C C' : List MutConst}
    (T : ∀ a ∈ C, ∀ b ∈ C, keep a = true → keep b = true → ∀ o,
      constOrd r₁ a₁ m₁ a b = .ok o ↔ constOrd r₂ a₂ m₂ (φ a) (φ b) = .ok o)
    (hC : (restrictC keep φ C).Perm C') (hn : C'.Nodup) {G : List (List MutConst)}
    (h : refineClassP r₁ a₁ m₁ C = .ok G) (hmeet : ∀ g ∈ G, ∃ a ∈ g, keep a = true) :
    ∃ G', refineClassP r₂ a₂ m₂ C' = .ok G' ∧ SetEq (G.map (restrictC keep φ)) G' := by
  have ht₁ := constOrd_total r₁ hA₁ m₁
  have ht₂ := constOrd_total r₂ hA₂ m₂
  obtain ⟨hp, hne, heq, hlt⟩ := refineClassP_spec r₁ hA₁ m₁ C G h
  have hG : OrdPart (constOrd r₁ a₁ m₁) G := ⟨hne, heq, hlt⟩
  have memC : ∀ {a : MutConst} {g : List MutConst}, g ∈ G → a ∈ g → a ∈ C := fun hg ha =>
    hp.mem_iff.1 (List.mem_flatten.2 ⟨_, hg, ha⟩)
  -- the restricted groups are an ordered partition for run 2
  have hG2 : OrdPart (constOrd r₂ a₂ m₂) (G.map (restrictC keep φ)) := by
    refine ⟨fun g' hg' => ?_, fun g' hg' x hx y hy hxy => ?_, fun i j hij hj x hx y hy => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
      exact restrictC_ne (hmeet g hg)
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
      obtain ⟨a, ha, hka, rfl⟩ := mem_restrictC.1 hx
      obtain ⟨b, hb, hkb, rfl⟩ := mem_restrictC.1 hy
      have hab : a ≠ b := fun e => hxy (by rw [e])
      exact (T a (memC hg ha) b (memC hg hb) hka hkb _).1 (heq g hg a ha b hb hab)
    · have hj' : j < G.length := by simpa using hj
      have hi' : i < G.length := by omega
      rw [List.getElem_map] at hx hy
      obtain ⟨a, ha, hka, rfl⟩ := mem_restrictC.1 hx
      obtain ⟨b, hb, hkb, rfl⟩ := mem_restrictC.1 hy
      exact (T a (memC (List.getElem_mem _) ha) b (memC (List.getElem_mem _) hb) hka hkb _).1
        (hlt i j hij hj' a ha b hb)
  -- every two distinct members of run 2's class compare
  have hboth : C'.Pairwise (BothOk (constOrd r₂ a₂ m₂)) := by
    refine (List.nodup_iff_pairwise_ne.1 hn).imp_of_mem fun {x y} hx hy hxy => ?_
    obtain ⟨a, ha, hka, rfl⟩ := mem_restrictC.1 (hC.mem_iff.2 hx)
    obtain ⟨b, hb, hkb, rfl⟩ := mem_restrictC.1 (hC.mem_iff.2 hy)
    have hab : a ≠ b := fun e => hxy (by rw [e])
    have ha' : a ∈ G.flatten := hp.mem_iff.2 ha
    have hb' : b ∈ G.flatten := hp.mem_iff.2 hb
    obtain ⟨o, ho⟩ := ordPart_ok ht₁ hG ha' hb' hab
    obtain ⟨o', ho'⟩ := ordPart_ok ht₁ hG hb' ha' (Ne.symm hab)
    exact ⟨⟨o, (T a ha b hb hka hkb o).1 ho⟩, ⟨o', (T b hb a ha hkb hka o').1 ho'⟩⟩
  -- run 2's round succeeds
  have hCne : C' ≠ [] := by
    intro e
    rw [e] at hC
    have hG0 : G ≠ [] := by
      intro e'; subst e'
      have : C = [] := List.Perm.eq_nil hp.symm
      subst this; simp [refineClassP] at h
    obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil G hG0
    obtain ⟨a, ha, hka⟩ := hmeet g hg
    have : φ a ∈ restrictC keep φ C := mem_restrictC.2 ⟨a, memC hg ha, hka, rfl⟩
    rw [List.Perm.eq_nil hC] at this; cases this
  obtain ⟨G', h₂⟩ : ∃ G', refineClassP r₂ a₂ m₂ C' = .ok G' := by
    match C', hboth, hCne with
    | [], _, hCne => exact absurd rfl hCne
    | [x], _, _ => exact ⟨[[x]], rfl⟩
    | x :: y :: rest, hboth, _ =>
      have hor₂ := constOrd_oriented r₂ hA₂ m₂ (S := fun _ => True)
      obtain ⟨sorted, hs⟩ := sortByM_ok hor₂ _ hboth
      obtain ⟨psorted, -⟩ := sortByM_spec hor₂ _ (fun _ _ => trivial) sorted hs
      have hboth' := pairwise_bothOk_perm psorted.symm hboth
      obtain ⟨groups, hg⟩ := groupAdjP_ok (eqOf (constOrd r₂ a₂ m₂)) sorted (hboth'.imp fun {a b} hab => by
        obtain ⟨o, ho⟩ := hab.2
        exact ⟨o == .eq, by simp only [eqOf, ho, bind, Except.bind, pure, Except.pure]⟩)
      exact ⟨repOf r₂ groups, by simp only [refineClassP, hs, hg, bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨hp', hne', heq', hlt'⟩ := refineClassP_spec r₂ hA₂ m₂ _ _ h₂
  have hflat : (G.map (restrictC keep φ)).flatten.Perm C' := by
    have : (G.map (restrictC keep φ)).flatten = restrictC keep φ G.flatten := restrictP_flatten G
    rw [this]; exact (restrictC_perm hp).trans hC
  exact ⟨G', h₂, ordPart_unique (fun a b o e => ord_swap ht₂ e) hG2 ⟨hne', heq', hlt'⟩
    (hflat.nodup_iff.2 hn) (hflat.trans hp'.symm)⟩

/-- **A round, simulated.** -/
theorem refineClassesP_sim {m₁ m₂ : MutCtx} :
    ∀ {P Q : List (List MutConst)}, SetEq (restrictP keep φ P) Q → Q.flatten.Nodup →
      (∀ a ∈ P.flatten, ∀ b ∈ P.flatten, keep a = true → keep b = true → ∀ o,
        constOrd r₁ a₁ m₁ a b = .ok o ↔ constOrd r₂ a₂ m₂ (φ a) (φ b) = .ok o) →
      ∀ {R : List (List MutConst)}, refineClassesP r₁ a₁ m₁ P = .ok R →
      (∀ g ∈ R, ∃ a ∈ g, keep a = true) →
      ∃ R', refineClassesP r₂ a₂ m₂ Q = .ok R' ∧ SetEq (restrictP keep φ R) R' := by
  intro P
  induction P with
  | nil =>
    intro Q hPQ _ _ R hR _
    cases hPQ
    simp only [refineClassesP, pure, Except.pure, Except.ok.injEq] at hR; subst hR
    exact ⟨[], rfl, SetEq.nil⟩
  | cons C P ih =>
    intro Q hPQ hn T R hR hmeet
    cases hPQ with
    | cons hCD hrest =>
      rename_i D Q'
      simp only [List.flatten_cons] at hn
      simp only [refineClassesP] at hR
      obtain ⟨gs, hgs, hR⟩ := except_bind_ok.1 hR
      obtain ⟨rest, hrest', hR⟩ := except_bind_ok.1 hR
      simp only [pure, Except.pure, Except.ok.injEq] at hR; subst hR
      have TC : ∀ a ∈ C, ∀ b ∈ C, keep a = true → keep b = true → ∀ o,
          constOrd r₁ a₁ m₁ a b = .ok o ↔ constOrd r₂ a₂ m₂ (φ a) (φ b) = .ok o :=
        fun a ha b hb => T a (by simp [ha]) b (by simp [hb])
      have TP : ∀ a ∈ P.flatten, ∀ b ∈ P.flatten, keep a = true → keep b = true → ∀ o,
          constOrd r₁ a₁ m₁ a b = .ok o ↔ constOrd r₂ a₂ m₂ (φ a) (φ b) = .ok o :=
        fun a ha b hb => T a (by simp [ha]) b (by simp [hb])
      obtain ⟨gs', hgs', e1⟩ := refineClassP_sim hA₁ hA₂ TC hCD (List.nodup_append.1 hn).1 hgs
        (fun g hg => hmeet g (List.mem_append_left _ hg))
      obtain ⟨rest', hr', e2⟩ := ih hrest (List.nodup_append.1 hn).2.1 TP hrest'
        (fun g hg => hmeet g (List.mem_append_right _ hg))
      refine ⟨gs' ++ rest', ?_, ?_⟩
      · simp only [refineClassesP, hgs', hr', bind, Except.bind, pure, Except.pure]
      · unfold restrictP; rw [List.map_append]; exact e1.append e2

end lockstep

/-! ## The loop -/

theorem length_le_flatten {P : List (List MutConst)} (h : ∀ C ∈ P, C ≠ []) :
    P.length ≤ P.flatten.length := by
  induction P with
  | nil => simp
  | cons C P ih =>
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    have h1 : C.length ≥ 1 := by
      cases C with
      | nil => exact absurd rfl (h [] (List.mem_cons_self ..))
      | cons _ _ => simp
    have := ih (fun D hD => h D (List.mem_cons_of_mem _ hD))
    omega

theorem SetEq.ne_nil {P Q : List (List MutConst)} (h : SetEq P Q) (hP : ∀ C ∈ P, C ≠ []) :
    ∀ D ∈ Q, D ≠ [] := by
  induction h with
  | nil => intro D hD; cases hD
  | cons hab _ ih =>
    intro D hD
    rcases List.mem_cons.1 hD with rfl | hD
    · intro e; subst e
      exact hP _ (List.mem_cons_self ..) (List.Perm.eq_nil hab)
    · exact ih (fun C hC => hP C (List.mem_cons_of_mem _ hC)) D hD

section loop
variable {r₁ r₂ : Rules} {a₁ a₂ : Name → Option Address} (hA₁ : AddrCongr a₁) (hA₂ : AddrCongr a₂)
  {keep : MutConst → Bool} {φ : MutConst → MutConst} {xs ys : List MutConst} (hk : KeysDistinct xs)
  (hky : KeysDistinct (restrictC keep φ xs)) (hys : (restrictC keep φ xs).Perm ys)
  {F : List (List MutConst)}
  (hFp : Partition F xs) (hFc : Consistent r₁ a₁ F) (hcover : ∀ D ∈ F, ∃ a ∈ D, keep a = true)
  (T : ∀ P, Partition P xs → Refines F P → ∀ a ∈ xs, ∀ b ∈ xs, keep a = true → keep b = true →
    ∀ o, constOrd r₁ a₁ (MutConst.ctx P) a b = .ok o ↔
      constOrd r₂ a₂ (MutConst.ctx (restrictP keep φ P)) (φ a) (φ b) = .ok o)
include hA₁ hA₂ hk hky hys hFp hFc hcover T

omit hA₁ hA₂ hky hys hFc T in
/-- Each class of a partition that `F` refines keeps a member. -/
theorem meets_of_refines {P : List (List MutConst)} (hP : Partition P xs) (href : Refines F P) :
    ∀ g ∈ P, ∃ a ∈ g, keep a = true := by
  intro g hg
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil g (hP.2 g hg)
  have hmx : m ∈ xs := hP.1.mem_iff.1 (List.mem_flatten.2 ⟨g, hg, hm⟩)
  obtain ⟨D, hD, hmD⟩ := List.mem_flatten.1 (hFp.1.mem_iff.2 hmx)
  obtain ⟨a, haD, hka⟩ := hcover D hD
  obtain ⟨g', hg', hmg', hag'⟩ := href D hD m hmD a haD
  have hn : P.flatten.Nodup := hP.1.nodup_iff.2 hk.nodup
  rw [mem_unique_of_nodup hn hg' hg hmg' hm] at hag'
  exact ⟨a, hag', hka⟩

/-- **The loop, simulated**, run 2 with any fuel that covers the rounds run 2 can make. -/
theorem sortLoopP_sim : ∀ (fuel₁ round : Nat) {P Q : List (List MutConst)},
    Partition P xs → Coarsest r₁ a₁ xs P → SetEq (restrictP keep φ P) Q → ∀ (fuel₂ : Nat),
    ys.length + 1 ≤ Q.length + fuel₂ → ∀ {n : Nat}, sortLoopP r₁ a₁ fuel₁ round P = .ok (F, n) →
    ∃ F', sortLoopP r₂ a₂ fuel₂ round Q = .ok (F', n) ∧ SetEq (restrictP keep φ F) F' := by
  intro fuel₁
  induction fuel₁ with
  | zero => intro _ _ _ _ _ _ _ _ _ h; simp [sortLoopP] at h
  | succ fuel ih =>
    intro round P Q hP hC hPQ fuel₂ hfuel n h
    simp only [sortLoopP] at h
    obtain ⟨refined, hr, h⟩ := except_bind_ok.1 h
    obtain ⟨rp, rne, rref, rsame, req, rlen, rone⟩ :=
      refineClassesP_spec r₁ hA₁ _ P refined hP.2 hr
    have hPr : Partition refined xs := ⟨rp.trans hP.1, rne⟩
    have hCr : Coarsest r₁ a₁ xs refined := by
      intro Q' hQ' hcons D hD m hm m' hm'
      obtain ⟨C, hCm, h1, h2⟩ := hC Q' hQ' hcons D hD m hm m' hm'
      by_cases e : m = m'
      · subst e
        obtain ⟨g, hg, hmg⟩ := List.mem_flatten.1 (rp.mem_iff.2 (List.mem_flatten.2 ⟨C, hCm, h1⟩))
        exact ⟨g, hg, hmg, hmg⟩
      · have heq := hcons D hD m hm m' hm' e
        have heq' := constOrd_eq_mono r₁ a₁ hk hQ'.1 hP.1 (hC Q' hQ' hcons) heq
        exact rsame C hCm m h1 m' h2 heq'
    -- the restricted partition and run 2's classes have the same lookups
    have hkP : KeysDistinct (restrictP keep φ P).flatten := by
      rw [restrictP_flatten]; exact hky.perm (restrictC_perm hP.1).symm
    have hm := ctx_setEq hPQ hkP
    have hnQ : Q.flatten.Nodup := (hkP.perm hPQ.flatten).nodup
    -- run 2's classes are nonempty and partition `ys`
    have hQne : ∀ D ∈ Q, D ≠ [] := hPQ.ne_nil fun C hCm => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hCm
      exact restrictC_ne (meets_of_refines hk hFp hcover hP (hC F hFp hFc) g hg)
    have hQlen : Q.length ≤ ys.length := by
      have := length_le_flatten hQne
      have hfl : Q.flatten.Perm ys := by
        refine hPQ.flatten.symm.trans ?_
        rw [restrictP_flatten]; exact (restrictC_perm hP.1).trans hys
      rw [hfl.length_eq] at this; exact this
    cases fuel₂ with
    | zero => omega
    | succ fuel₂ =>
    simp only [sortLoopP]
    have T' : ∀ a ∈ P.flatten, ∀ b ∈ P.flatten, keep a = true → keep b = true → ∀ o,
        constOrd r₁ a₁ (MutConst.ctx P) a b = .ok o ↔ constOrd r₂ a₂ (MutConst.ctx Q) (φ a) (φ b) = .ok o :=
      fun a ha b hb hka hkb o =>
        (T P hP (hC F hFp hFc) a (hP.1.mem_iff.1 ha) b (hP.1.mem_iff.1 hb) hka hkb o).trans
          (constOrd_lookup_iff rfl rfl a₂ hm _ _ o)
    obtain ⟨refined', hr', e⟩ := refineClassesP_sim hA₁ hA₂ hPQ hnQ T' hr
      (meets_of_refines hk hFp hcover hPr (hCr F hFp hFc))
    rw [hr']
    simp only [bind, Except.bind]
    have hlQ : Q.length = P.length := by rw [← hPQ.length, restrictP_length]
    have hlR : refined'.length = refined.length := by rw [← e.length, restrictP_length]
    rw [hlQ, hlR]
    split at h
    · rename_i hc
      simp only [hc, ↓reduceIte]
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨refined', ⟨rfl, rfl⟩, e⟩
    · rename_i hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hgt : P.length + 1 ≤ refined.length := by
        have : P.length ≠ refined.length := by simpa using hc
        omega
      exact ih (round + 1) hPr hCr e fuel₂ (by omega) h

end loop

/-- **The pure refinement, simulated.** -/
theorem sortClassesP_sim {r₁ r₂ : Rules} {a₁ a₂ : Name → Option Address} (hA₁ : AddrCongr a₁)
    (hA₂ : AddrCongr a₂) {keep : MutConst → Bool} {φ : MutConst → MutConst} {xs ys : List MutConst}
    (hk : KeysDistinct xs) (hky : KeysDistinct (restrictC keep φ xs))
    (hys : (restrictC keep φ xs).Perm ys) {F : List (List MutConst)}
    (h : sortClassesP r₁ a₁ xs = .ok F) (hcover : ∀ D ∈ F, ∃ a ∈ D, keep a = true)
    (T : ∀ P, Partition P xs → Refines F P → ∀ a ∈ xs, ∀ b ∈ xs, keep a = true → keep b = true →
      ∀ o, constOrd r₁ a₁ (MutConst.ctx P) a b = .ok o ↔
        constOrd r₂ a₂ (MutConst.ctx (restrictP keep φ P)) (φ a) (φ b) = .ok o) :
    ∃ G, sortClassesP r₂ a₂ ys = .ok G ∧ SetEq (restrictP keep φ F) G := by
  obtain ⟨hFp, hFc, -⟩ := sortClassesP_coarsest r₁ hA₁ hk h
  unfold sortClassesP at h ⊢
  by_cases he : xs.isEmpty = true
  · have : xs = [] := by simpa using he
    subst this
    simp only [List.isEmpty_nil, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h; subst h
    have : ys = [] := List.Perm.eq_nil hys.symm
    subst this
    exact ⟨[], rfl, SetEq.nil⟩
  · have he₁ : xs.isEmpty = false := by simpa using he
    simp only [he₁, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨⟨classes, rounds⟩, hlp, h⟩ := except_bind_ok.1 h
    have hF : classes = F := by
      split at h
      · cases h
      · split at h
        · cases h
        · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h
    subst hF
    have hFne : classes ≠ [] := by
      intro e
      have := hFp.1
      rw [e] at this
      exact he (by simpa using List.Perm.eq_nil this.symm)
    obtain ⟨D, hD⟩ := List.exists_mem_of_ne_nil classes hFne
    obtain ⟨a, haD, hka⟩ := hcover D hD
    have hys' : ys.isEmpty = false := by
      cases ys with
      | nil =>
        have : φ a ∈ restrictC keep φ xs :=
          mem_restrictC.2 ⟨a, hFp.1.mem_iff.1 (List.mem_flatten.2 ⟨D, hD, haD⟩), hka, rfl⟩
        rw [List.Perm.eq_nil hys] at this; cases this
      | cons _ _ => rfl
    simp only [hys', Bool.false_eq_true, ↓reduceIte]
    have hseed : SetEq (restrictP keep φ [seedOf r₁ xs]) [seedOf r₂ ys] :=
      SetEq.cons (((restrictC_perm (seedOf_perm r₁ xs)).trans hys).trans (seedOf_perm r₂ ys).symm)
        SetEq.nil
    have hP0 : Partition [seedOf r₁ xs] xs := by
      refine ⟨by simpa using seedOf_perm r₁ xs, fun C hC => ?_⟩
      simp only [List.mem_singleton] at hC; subst hC
      intro e
      have := (seedOf_perm r₁ xs).symm
      rw [e] at this
      exact he (by simpa using List.Perm.eq_nil this)
    have hC0 : Coarsest r₁ a₁ xs [seedOf r₁ xs] := by
      intro Q hQ _ D' hD' m hm m' hm'
      refine ⟨seedOf r₁ xs, by simp, ?_, ?_⟩
      · exact (seedOf_perm r₁ xs).mem_iff.2 (hQ.1.mem_iff.1 (List.mem_flatten.2 ⟨D', hD', hm⟩))
      · exact (seedOf_perm r₁ xs).mem_iff.2 (hQ.1.mem_iff.1 (List.mem_flatten.2 ⟨D', hD', hm'⟩))
    obtain ⟨F', hlp', e⟩ := sortLoopP_sim hA₁ hA₂ hk hky hys hFp hFc hcover T (xs.length + 1) 0 hP0
      hC0 hseed (ys.length + 1) (by simp only [List.length_singleton]; omega) hlp
    rw [hlp']
    simp only [bind, Except.bind]
    -- the final checks pass
    have hFne' : ∀ D ∈ F', D ≠ [] := e.ne_nil fun C hC => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hC
      exact restrictC_ne (hcover g hg)
    have hany : F'.any (·.isEmpty) = false := by
      cases hh : F'.any (·.isEmpty) with
      | false => rfl
      | true =>
        obtain ⟨D, hD, hDe⟩ := List.any_eq_true.1 hh
        exact absurd (List.isEmpty_iff.1 hDe) (hFne' D hD)
    have hlen : ¬ ys.length < F'.length := by
      have := length_le_flatten hFne'
      have hfl : F'.flatten.Perm ys := by
        refine e.flatten.symm.trans ?_
        rw [restrictP_flatten]; exact (restrictC_perm hFp.1).trans hys
      rw [hfl.length_eq] at this; omega
    simp only [hany, Bool.false_eq_true, ↓reduceIte, hlen, pure, Except.pure]
    exact ⟨F', rfl, e⟩

end Ix.CompileCert.Canon
