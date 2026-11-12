import IxCC.Own.Plain.Proof.Owned.Binds

/-! # `inc` and `dec` steps

`inc x 1` adds a token: `inc_root` (owned: the token's own count; borrowed: the projected cell's
live edge, kept as `CanDup`; immediate: a no-op). `dec x` takes one and is a release:
`dropAll_retaining` keeps the value of every remaining token, and nothing stays borrowed. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var)

theorem mem_of_refsIn_pos {l : Nat} : ∀ {xs : List RVal}, 0 < refsIn l xs → RVal.loc l ∈ xs
  | [], h => by simp [refsIn] at h
  | x :: xs, h => by
    by_cases hx : x = .loc l
    · subst hx; exact List.mem_cons_self
    · simp only [refsIn, hx, ↓reduceIte, Nat.zero_add] at h
      exact List.mem_cons_of_mem _ (mem_of_refsIn_pos h)

/-- Values kept for the remaining tokens and for the external owners are kept for both. -/
theorem preserved_hold {H H' : Heap} {external : Nat → Nat} {held : List RVal}
    (hheld : ∀ root, root ∈ held → H.value? root = H'.value? root)
    (hext : ∀ root, ExternalRoot external root → H.value? root = H'.value? root) :
    ExternalPreserved H H' (holdRoots external held) := by
  intro root w hr hd
  change H'.value? root = some w
  have hv : H.value? root = H'.value? root := by
    cases root with
    | loc l =>
      change 0 < external l + refsIn l held at hr
      by_cases he : 0 < external l
      · exact hext _ he
      · exact hheld _ (mem_of_refsIn_pos (by omega))
    | lit _ | ctor0 _ | erased => exact hext _ trivial
  rw [← hv]; exact hd

section
variable {functions : Signatures} {H : Heap} {external : Nat → Nat} {live : List Var}
  {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins} {Δ : JCtx}
  {Jf : List Fir.JEntry} {Jo : List JEntry}

theorem inc_step (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo)
    {Γ' : Ctx} {x : Var} {n : Nat} (hc : Γ.inc x n = .ok Γ') :
    ∃ H' owned', evalAction ρo H (.inc x n) = .ok H' ∧
      OwnedState functions H' external live Γ' ρf ρo owned' lex Δ Jf Jo ∧
      ExternalPreserved H H' external := by
  obtain ⟨rfl, hcase⟩ := Ctx.inc_ok hc
  obtain ⟨toks, htok, hroots⟩ := st.roots
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
  have pre := st.pre.transport (H' := H')
    (fun u w' h => by change H'.value? u = some w'; rw [← hvals u]; exact h)
    (fun u hu => canDup_inc hu hinc)
  rcases hcase with ⟨hi, rfl⟩ | ⟨hi, hp, rfl⟩ | ⟨hi, h0, hb, rfl⟩
  · -- An immediate: a no-op; its vacuous token is not kept.
    refine ⟨H', owned, hact, ?_, hpres⟩
    obtain ⟨v', hv', himm⟩ := st.immOk x hi
    have : v' = v := Option.some.inj (hv'.symm.trans hv)
    subst this
    exact pre.toState ((SameRefs.imm_cons himm owned).balance hb')
  · refine ⟨H', v :: owned, hact, ?_, hpres⟩
    have hroots' : EnvRoots ρo (x :: toks) (v :: owned) := EnvRoots.cons hv hroots
    refine ⟨fun y hy => pre.den y ?_, ⟨x :: toks, htok.addOwn x, hroots'⟩, hb',
      fun y hy => pre.known y ?_, pre.distinct, fun y hy => pre.immOk y hy,
      fun y hy => pre.borrowed y hy, pre.epochs, pre.stack, pre.scope⟩
    · simp only [Ctx.avail_eq, Ctx.isImm_addOwn, Ctx.tokens_addOwn, Ctx.borrowed_eq,
        Ctx.brw_addOwn, Ctx.epoch_addOwn, Bool.or_eq_true, decide_eq_true_eq] at hy ⊢
      split at hy
      · next he => subst he; exact Or.inl (Or.inr hp)
      · exact hy
    · by_cases he : y = x
      · subst he; exact Ctx.avail_known havail
      · simp only [Ctx.known_eq, Ctx.isImm_addOwn, Ctx.ownHas_addOwn, Ctx.brw_addOwn, he,
          decide_false, Bool.false_or] at hy ⊢
        exact hy
  · -- A borrowed variable becomes owned with one token.
    refine ⟨H', v :: owned, hact, ?_, hpres⟩
    have htok' : Ctx.Tokens ({ Γ with brw := Γ.brw.erase x } : Ctx) toks := htok.same rfl rfl
    have hroots' : EnvRoots ρo (x :: toks) (v :: owned) := EnvRoots.cons hv hroots
    refine ⟨fun y hy => pre.den y ?_, ⟨x :: toks, htok'.addOwn x, hroots'⟩, hb',
      fun y hy => pre.known y ?_, pre.distinct, fun y hy => pre.immOk y hy,
      fun y hy => pre.borrowed y ?_, fun y e hy => pre.epochs y e ?_, pre.stack, pre.scope⟩
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

theorem dec_step (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo)
    {Γ' : Ctx} {x : Var} (hc : Γ.dec x = .ok Γ') :
    ∃ H' owned', evalAction ρo H (.dec x) = .ok H' ∧
      OwnedState functions H' external live Γ' ρf ρo owned' lex Δ Jf Jo ∧
      ExternalPreserved H H' external := by
  obtain ⟨Γ₁, ht, rfl⟩ := Ctx.dec_ok hc
  obtain ⟨v, w, owned₁, hv, _, _, inv₁, hs, hw⟩ := take_sem st.takeInv ht
  have hb : Balance H external (v :: owned₁) := hs.balance st.counts
  obtain ⟨H', hact, hb', hheld, hext⟩ := evalAction_dec_owned hv hb
  have pre₁ := st.pre.weaker hw inv₁.roots
  have hnb := release_borrowed pre₁.epochs
  have pre' := pre₁.release.call hnb (preserved_hold hheld hext)
  exact ⟨H', owned₁, hact, pre'.toState hb', ExternalPreserved.of_values hext⟩

end

end IxCC.Own.Plain
