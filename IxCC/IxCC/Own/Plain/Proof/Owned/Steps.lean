import IxCC.Own.Plain.Proof.Owned.Takes
import IxCC.Own.Plain.Proof.Actions
import IxCC.Own.Plain.Proof.Projection
import IxCC.Own.Plain.Proof.Scalars
import IxCC.Own.Plain.Proof.NonCall

/-! # One step of an accepted body: actions and bindings that call nothing

Each lemma takes the state before a checked step and gives the actual Own step and the state
after it. The heap facts are the existing ones (`inc_root`, `dropAll_retaining`, `alloc_sound`,
the projection and primitive lemmas); what is new is the token bookkeeping (a token taken from any
position, `SameRefs`), the borrowed mode (`CanDup` and the value kept by every step that releases
nothing), and the immediates a primitive's signature creates. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var Arg Rhs)

theorem Ctx.avail_known {Γ : Ctx} {y : Var} (h : Γ.avail y = true) : Γ.known y = true := by
  simp only [Ctx.avail_eq, Ctx.known_eq, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl h)
  · refine Or.inl (Or.inr ?_)
    rw [Ctx.tokens_eq] at h
    cases hg : Γ.own.get? y with
    | none => rw [hg] at h; simp at h
    | some n => simp [Src.NatMap.contains, hg]
  · refine Or.inr ?_
    simp only [Ctx.borrowed_eq, beq_iff_eq] at h
    simp [h]

theorem canDup_inc {H H' : Heap} {u v : RVal} (hv : CanDup H v) (hi : Rc.inc H u 1 = some H') :
    CanDup H' v := by
  cases u with
  | loc l =>
    cases hc : H.cell? l with
    | none => simp [Rc.inc, changeCount, hc] at hi
    | some c =>
      cases c with
      | dead => simp [Rc.inc, changeCount, hc] at hi
      | live rc m b =>
        cases m with
        | static =>
          simp only [Rc.inc, changeCount, hc, Option.some.injEq] at hi
          subst hi; exact hv
        | dyn =>
          by_cases hz : rc = 0
          · simp [Rc.inc, changeCount, hc, hz] at hi
          · have hp : 0 < rc := by omega
            rw [inc_dyn hc hp 1] at hi
            cases hi
            have hl : l < H.size := (Array.getElem?_eq_some_iff.mp hc).1
            cases v with
            | loc k =>
              change 0 < dynCount (setCell H l (.live (rc + 1) .dyn b)) k
              change 0 < dynCount H k at hv
              by_cases hk : l = k
              · subst hk
                simp [dynCount, setCell_cell H l _ hl]
              · simp only [dynCount, setCell_cell H l _ hl, if_neg hk]
                exact hv
            | lit _ | ctor0 _ | erased => trivial
  | lit _ | ctor0 _ | erased =>
    simp only [Rc.inc, changeCount, Option.some.injEq] at hi
    subst hi; exact hv

theorem canDup_alloc {H : Heap} {v : RVal} (hv : CanDup H v) (b : Body) :
    CanDup (H.alloc .rc b).2 v := by
  cases v with
  | loc k =>
    change 0 < dynCount (H.alloc .rc b).2 k
    change 0 < dynCount H k at hv
    rw [dynCount_alloc]
    split <;> omega
  | lit _ | ctor0 _ | erased => trivial

theorem den_imm {H H' : Heap} {v : RVal} {w : Fir.Val} (hv : ImmVal v) (hd : Proof.Den H v w) :
    Proof.Den H' v w := by
  change H'.value? v = some w
  rw [← value?_eq_of_immVal H H' hv]
  exact hd

/-! ## `inc` and `dec` -/

theorem inc_step {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ Γ' : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal}
    {lex : Joins} {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo)
    {x : Var} {n : Nat} (hc : Γ.inc x n = .ok Γ') :
    ∃ H' owned', evalAction ρo H (.inc x n) = .ok H' ∧
      OwnedState functions H' external live Γ' ρf ρo owned' lex Δ Jf Jo ∧
      ExternalPreserved H H' external := by
  obtain ⟨rfl, hcase⟩ := Ctx.inc_ok hc
  obtain ⟨toks, htok, hroots⟩ := st.roots
  -- The value incremented, and why it may be.
  have havail : Γ.avail x = true := by
    rcases hcase with ⟨hi, _⟩ | ⟨_, hp, _⟩ | ⟨_, _, hb, _⟩
    · simp [Ctx.avail_eq, hi]
    · simp [Ctx.avail_eq, hp]
    · simp [Ctx.avail_eq, hb]
  obtain ⟨v, w, hv, hw, hd⟩ := st.den x havail
  have hcan : CanDup H v := by
    rcases hcase with ⟨hi, _⟩ | ⟨_, hp, _⟩ | ⟨_, _, hb, _⟩
    · obtain ⟨v', hv', himm⟩ := st.immOk x hi
      have : v' = v := Option.some.inj (hv'.symm.trans hv)
      subst this
      cases v' with
      | loc l => exact absurd rfl (himm l)
      | lit _ | ctor0 _ | erased => trivial
    · exact canDup_member st.counts (hroots.member (htok.mem hp) hv)
    · obtain ⟨v', hv', hc'⟩ := st.borrowed x hb
      have : v' = v := Option.some.inj (hv'.symm.trans hv)
      subst this; exact hc'
  obtain ⟨H', hinc, hb', hvals⟩ := inc_root st.counts hcan
  have hact : evalAction ρo H (.inc x 1) = .ok H' := by
    simp [evalAction, hv, hinc, Result.ofOption]
  have hpres : ExternalPreserved H H' external :=
    ExternalPreserved.of_values (fun root _ => hvals root)
  have hden : ∀ y, Γ.avail y = true →
      ∃ v w, ρo.get? y = some v ∧ ρf.get? y = some w ∧ Proof.Den H' v w := by
    intro y hy
    obtain ⟨v', w', h1, h2, h3⟩ := st.den y hy
    refine ⟨v', w', h1, h2, ?_⟩
    change H'.value? v' = some w'
    rw [← hvals v']; exact h3
  have hbrw : ∀ y, Γ.borrowed y = true → ∃ v, ρo.get? y = some v ∧ CanDup H' v := by
    intro y hy
    obtain ⟨v', h1, h2⟩ := st.borrowed y hy
    exact ⟨v', h1, canDup_inc h2 hinc⟩
  rcases hcase with ⟨hi, rfl⟩ | ⟨hi, hp, rfl⟩ | ⟨hi, h0, hb, rfl⟩
  · -- An immediate: a no-op; its vacuous token is not kept.
    obtain ⟨v', hv', himm⟩ := st.immOk x hi
    have : v' = v := Option.some.inj (hv'.symm.trans hv)
    subst this
    refine ⟨H', owned, hact, { st with den := hden, counts := (SameRefs.imm_cons himm owned).balance hb',
      borrowed := hbrw }, hpres⟩
  · refine ⟨H', v :: owned, hact, ?_, hpres⟩
    refine { st with den := fun y hy => hden y ?_, roots := ⟨x :: toks, htok.addOwn x,
      EnvRoots.cons hv hroots⟩, counts := hb', known := fun y hy => st.known y ?_,
      immOk := fun y hy => st.immOk y hy, borrowed := fun y hy => hbrw y hy,
      epochs := st.epochs }
    · simp only [Ctx.avail_eq, Ctx.isImm_addOwn, Ctx.tokens_addOwn, Ctx.borrowed_eq,
        Ctx.brw_addOwn, Ctx.epoch_addOwn, Bool.or_eq_true, decide_eq_true_eq] at hy ⊢
      split at hy
      · next he => subst he; exact Or.inl (Or.inr hp)
      · exact hy
    · simp only [Ctx.known_eq, Ctx.isImm_addOwn, Ctx.ownHas_addOwn, Ctx.brw_addOwn,
        Bool.or_eq_true, decide_eq_true_eq] at hy ⊢
      rcases hy with (h | h | h) | h
      · exact Or.inl (Or.inl h)
      · subst h
        have := Ctx.avail_known havail
        simpa [Ctx.known_eq] using this
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  · -- A borrowed variable becomes owned with one token.
    have htok' : Ctx.Tokens ({ Γ with brw := Γ.brw.erase x } : Ctx) toks := htok.same rfl rfl
    refine ⟨H', v :: owned, hact, ?_, hpres⟩
    refine { st with den := fun y hy => hden y ?_, roots := ⟨x :: toks, htok'.addOwn x,
      EnvRoots.cons hv hroots⟩, counts := hb', known := fun y hy => st.known y ?_,
      immOk := fun y hy => st.immOk y hy, borrowed := fun y hy => hbrw y ?_,
      epochs := fun y e hy => st.epochs y e ?_ }
    · by_cases he : y = x
      · subst he; exact havail
      · simp only [Ctx.avail_eq, Ctx.isImm_addOwn, Ctx.tokens_addOwn, if_neg he,
          Ctx.borrowed_eq, Ctx.brw_addOwn, Ctx.epoch_addOwn, Src.NatMap.get?_erase] at hy ⊢
        exact hy
    · by_cases he : y = x
      · subst he; exact Ctx.avail_known havail
      · simp only [Ctx.known_eq, Ctx.isImm_addOwn, Ctx.ownHas_addOwn, Ctx.brw_addOwn,
          Src.NatMap.get?_erase, he, decide_false, Bool.false_or, ↓reduceIte] at hy ⊢
        exact hy
    · by_cases he : y = x
      · subst he
        simp [Ctx.borrowed_eq, Src.NatMap.get?_erase] at hy
      · simp only [Ctx.borrowed_eq, Ctx.brw_addOwn, Ctx.epoch_addOwn, Src.NatMap.get?_erase,
          if_neg he] at hy ⊢
        exact hy
    · simp only [Ctx.brw_addOwn, Src.NatMap.get?_erase] at hy
      split at hy
      · cases hy
      · exact hy

theorem dec_step {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ Γ' : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal}
    {lex : Joins} {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo)
    {x : Var} (hc : Γ.dec x = .ok Γ') :
    ∃ H' owned', evalAction ρo H (.dec x) = .ok H' ∧
      OwnedState functions H' external live Γ' ρf ρo owned' lex Δ Jf Jo ∧
      ExternalPreserved H H' external := by
  obtain ⟨Γ₁, ht, rfl⟩ := Ctx.dec_ok hc
  obtain ⟨v, w, owned₁, hv, _, _, inv₁, hs, hw⟩ := take_sem st.takeInv ht
  have hb : Balance H external (v :: owned₁) := hs.balance st.counts
  obtain ⟨H', hact, hb', hheld, hext⟩ := evalAction_dec_owned hv hb
  obtain ⟨toks₁, htok₁, hroots₁⟩ := inv₁.roots
  refine ⟨H', owned₁, hact, ?_, ExternalPreserved.of_values hext⟩
  have hnb := release_borrowed (Γ := Γ₁) (by
    intro y e hy; rw [hw.brw] at hy; rw [hw.epoch]; exact st.epochs y e hy)
  refine ⟨fun y hy => ?_, ⟨toks₁, htok₁.same rfl rfl, hroots₁⟩, hb',
    fun y hy => st.known y (hw.known (by simpa [Ctx.known_eq] using hy)), st.distinct,
    fun y hy => inv₁.immOk y (by simpa using hy), fun y hy => by rw [hnb y] at hy; cases hy,
    fun y e hy => ?_, st.stack, st.scope⟩
  · simp only [Ctx.avail_eq, Ctx.isImm_release, Ctx.tokens_release, hnb, Bool.or_false,
      Bool.or_eq_true, decide_eq_true_eq] at hy
    have hy' : Γ₁.avail y = true := by simp [Ctx.avail_eq, hy]
    obtain ⟨v', w', h1, h2, h3⟩ := inv₁.den y hy'
    refine ⟨v', w', h1, h2, ?_⟩
    rcases hy with hi | hp
    · obtain ⟨u, hu, himm⟩ := inv₁.immOk y hi
      have : u = v' := Option.some.inj (hu.symm.trans h1)
      subst this
      exact den_imm himm h3
    · have hm := hroots₁.member (htok₁.mem hp) h1
      change H'.value? v' = some w'
      rw [← hheld v' hm]; exact h3
  · simp only [Ctx.brw_release, Ctx.epoch_release] at hy ⊢
    rw [hw.brw] at hy
    have := st.epochs y e hy
    rw [hw.epoch]; omega

end IxCC.Own.Plain
