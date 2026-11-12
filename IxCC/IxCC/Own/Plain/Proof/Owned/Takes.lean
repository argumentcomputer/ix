import IxCC.Own.Plain.Proof.Owned.State

/-! # Consuming tokens, and binding a fresh variable

`TakeInv` is the part of `OwnedState` a consuming use needs: what takes a token of each argument
(`takeArgs`) or of each captured variable (`takeVars`) yields the arguments' values, their
denotations, and the remaining tokens, with the consumed values' references split off
(`SameRefs owned (vs ++ owned')`, an immediate counting for nothing). `OwnedState.extend` builds
the state after a fresh binding from the per-variable facts a step establishes. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Fir (Var Arg)

/-- What a consuming use needs of the state. -/
structure TakeInv (H : Heap) (Γ : Ctx) (ρf : Fir.Env) (ρo : Own.Env) (owned : List RVal) : Prop where
  den : ∀ x, Γ.avail x = true → ∃ v w, ρo.get? x = some v ∧ ρf.get? x = some w ∧ Proof.Den H v w
  roots : ∃ toks, Ctx.Tokens Γ toks ∧ EnvRoots ρo toks owned
  immOk : ∀ x, Γ.isImm x = true → ∃ v, ρo.get? x = some v ∧ ImmVal v

theorem OwnedState.takeInv {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins}
    {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo) :
    TakeInv H Γ ρf ρo owned := ⟨st.den, st.roots, st.immOk⟩

theorem TakeInv.weaker {H : Heap} {Γ Γ' : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned owned' : List RVal}
    (h : TakeInv H Γ ρf ρo owned) (hw : Ctx.Weaker Γ' Γ)
    (hr : ∃ toks, Ctx.Tokens Γ' toks ∧ EnvRoots ρo toks owned') : TakeInv H Γ' ρf ρo owned' :=
  ⟨fun x hx => h.den x (hw.avail hx), hr, fun x hx => h.immOk x (by rw [← hw.isImm x]; exact hx)⟩

theorem take_sem {H : Heap} {Γ Γ' : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal}
    {x : Var} (h : TakeInv H Γ ρf ρo owned) (ht : Γ.take x = .ok Γ') :
    ∃ v w owned', ρo.get? x = some v ∧ ρf.get? x = some w ∧ Proof.Den H v w ∧
      TakeInv H Γ' ρf ρo owned' ∧ SameRefs owned (v :: owned') ∧ Ctx.Weaker Γ' Γ := by
  have hw := Ctx.take_weaker ht
  obtain ⟨toks, htok, hroots⟩ := h.roots
  cases hi : Γ.isImm x with
  | true =>
    have hΓ : Γ' = Γ := by
      rcases Ctx.take_ok ht with ⟨_, h'⟩ | ⟨hi', _⟩
      · exact h'
      · rw [hi] at hi'; cases hi'
    rw [hΓ]
    have havail : Γ.avail x = true := by simp [Ctx.avail_eq, hi]
    obtain ⟨v, w, hv, hw', hd⟩ := h.den x havail
    obtain ⟨v', hv', himm⟩ := h.immOk x hi
    have : v' = v := Option.some.inj (hv'.symm.trans hv)
    subst this
    exact ⟨v', w, owned, hv, hw', hd, h, (SameRefs.imm_cons himm owned).symm, Ctx.Weaker.refl _⟩
  | false =>
    obtain ⟨hm, hpos, htok'⟩ := htok.take ht hi
    have havail : Γ.avail x = true := by simp [Ctx.avail_eq, hpos]
    obtain ⟨v, w, hv, hw', hd⟩ := h.den x havail
    obtain ⟨owned', hr', hs⟩ := EnvRoots.erase hv hroots hm
    exact ⟨v, w, owned', hv, hw', hd, h.weaker hw ⟨_, htok', hr'⟩, hs, hw⟩

theorem takeArg_sem {H : Heap} {Γ Γ' : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal}
    {a : Arg} (h : TakeInv H Γ ρf ρo owned) (ht : Γ.takeArg a = .ok Γ') :
    ∃ v w owned', Own.evalArg ρo a = some v ∧ a.eval ρf = some w ∧ Proof.Den H v w ∧
      TakeInv H Γ' ρf ρo owned' ∧ SameRefs owned (v :: owned') ∧ Ctx.Weaker Γ' Γ := by
  cases a with
  | var x => exact take_sem h ht
  | lit l =>
    cases ht
    exact ⟨.lit l, .lit l, owned, rfl, rfl, Proof.den_lit H l, h,
      (SameRefs.imm_cons (by intro l h; cases h) owned).symm, Ctx.Weaker.refl _⟩
  | erased =>
    cases ht
    exact ⟨.erased, .erased, owned, rfl, rfl, Proof.den_erased H, h,
      (SameRefs.imm_cons (by intro l h; cases h) owned).symm, Ctx.Weaker.refl _⟩

theorem takeArgs_sem {H : Heap} {ρf : Fir.Env} {ρo : Own.Env} :
    ∀ {Γ Γ' : Ctx} {owned : List RVal} {args : List Arg},
      TakeInv H Γ ρf ρo owned → Γ.takeArgs args = .ok Γ' →
      ∃ vs ws owned', Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
        Sem.Forall2 (Proof.Den H) vs ws ∧ TakeInv H Γ' ρf ρo owned' ∧
        SameRefs owned (vs ++ owned') ∧ Ctx.Weaker Γ' Γ
  | Γ, Γ', owned, [], h, ht => by
    cases ht
    exact ⟨[], [], owned, rfl, rfl, .nil, h, SameRefs.refl _, Ctx.Weaker.refl _⟩
  | Γ, Γ', owned, a :: as, h, ht => by
    simp only [Ctx.takeArgs] at ht
    cases ha : Γ.takeArg a with
    | error e => rw [ha] at ht; cases ht
    | ok Γ₁ =>
      rw [ha] at ht
      obtain ⟨v, w, owned₁, hv, hw, hd, h₁, hs₁, hw₁⟩ := takeArg_sem h ha
      obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw'⟩ := takeArgs_sem h₁ ht
      refine ⟨v :: vs, w :: ws, owned', ?_, ?_, .cons hd hds, h', ?_, hw'.trans hw₁⟩
      · simp [Own.evalArgs, hv, hvs]
      · simp [Fir.evalArgs, hw, hws]
      · exact hs₁.trans (SameRefs.cons v hs')

theorem takeVars_sem {H : Heap} {ρf : Fir.Env} {ρo : Own.Env} :
    ∀ {Γ Γ' : Ctx} {owned : List RVal} {xs : List Var},
      TakeInv H Γ ρf ρo owned → Γ.takeVars xs = .ok Γ' →
      ∃ vs owned', EnvRoots ρo xs vs ∧ (∀ x, x ∈ xs → Γ.avail x = true) ∧
        TakeInv H Γ' ρf ρo owned' ∧ SameRefs owned (vs ++ owned') ∧ Ctx.Weaker Γ' Γ
  | Γ, Γ', owned, [], h, ht => by
    cases ht
    exact ⟨[], owned, rfl, fun _ hx => by simp at hx, h, SameRefs.refl _, Ctx.Weaker.refl _⟩
  | Γ, Γ', owned, x :: xs, h, ht => by
    simp only [Ctx.takeVars] at ht
    cases hx : Γ.take x with
    | error e => rw [hx] at ht; cases ht
    | ok Γ₁ =>
      rw [hx] at ht
      have havail : Γ.avail x = true := by
        rcases Ctx.take_ok hx with ⟨hi, _⟩ | ⟨_, n, hn, _⟩
        · simp [Ctx.avail_eq, hi]
        · simp [Ctx.avail_eq, Ctx.tokens_eq, hn]
      obtain ⟨v, _, owned₁, hv, _, _, h₁, hs₁, hw₁⟩ := take_sem h hx
      obtain ⟨vs, owned', hvs, havs, h', hs', hw'⟩ := takeVars_sem h₁ ht
      refine ⟨v :: vs, owned', EnvRoots.cons hv hvs, fun y hy => ?_, h', ?_, hw'.trans hw₁⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact havail
        · exact hw₁.avail (havs y hy)
      · exact hs₁.trans (SameRefs.cons v hs')

/-- A closed context holds no token. -/
theorem closed_nil {Γ : Ctx} {toks : List Var} {what : String} (ht : Ctx.Tokens Γ toks)
    (hc : Γ.closed what = .ok ()) : toks = [] := by
  unfold Ctx.closed at hc
  split at hc
  · next h =>
    have h0 : Γ.total = 0 := by simpa using h
    rw [ht.total] at h0
    exact List.eq_nil_of_length_eq_zero h0
  · cases hc

theorem EnvRoots.nil_inv {ρ : Own.Env} {vs : List RVal} (h : EnvRoots ρ [] vs) : vs = [] := by
  unfold EnvRoots at h
  simp [Own.evalArgs] at h
  exact h

/-- A variable holding a token is known, so it is in scope. -/
theorem Tokens.mem_known {Γ : Ctx} {toks : List Var} (ht : Ctx.Tokens Γ toks) {y : Var}
    (hy : y ∈ toks) : Γ.known y = true := by
  have hc := ht.count y
  have hpos : 0 < toks.count y := List.count_pos_iff.mpr hy
  rw [hc, Ctx.tokens_eq] at hpos
  cases hg : Γ.own.get? y with
  | none => rw [hg] at hpos; simp at hpos
  | some n => simp [Ctx.known_eq, Src.NatMap.contains, hg]

/-- After a release, nothing is borrowed. -/
theorem release_borrowed {Γ : Ctx} (he : ∀ x e, Γ.brw.get? x = some e → e ≤ Γ.epoch) (y : Var) :
    Γ.release.borrowed y = false := by
  cases hb : Γ.brw.get? y with
  | none => simp [Ctx.borrowed_eq, hb]
  | some e =>
    have := he y e hb
    simp only [Ctx.borrowed_eq, Ctx.brw_release, Ctx.epoch_release, hb, beq_eq_false_iff_ne,
      ne_eq, Option.some.injEq]
    omega

/-- **The state after a fresh binding**, from what the step establishes for each variable. -/
theorem OwnedState.extend {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins}
    {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo)
    {x : Var} (hx : x ∉ live) {Γ' : Ctx} {H' : Heap} {v : RVal} {w : Fir.Val}
    {owned' : List RVal}
    (hden : ∀ y, y ≠ x → Γ'.avail y = true →
      ∃ v w, ρo.get? y = some v ∧ ρf.get? y = some w ∧ Proof.Den H' v w)
    (hdenx : Proof.Den H' v w)
    (hroots : ∃ toks, Ctx.Tokens Γ' toks ∧ EnvRoots (ρo.insert x v) toks owned')
    (hcounts : Balance H' external owned')
    (hknown : ∀ y, Γ'.known y = true → y = x ∨ Γ.known y = true)
    (himm : ∀ y, y ≠ x → Γ'.isImm y = true → ∃ v, ρo.get? y = some v ∧ ImmVal v)
    (himmx : Γ'.isImm x = true → ImmVal v)
    (hbrw : ∀ y, y ≠ x → Γ'.borrowed y = true → ∃ v, ρo.get? y = some v ∧ CanDup H' v)
    (hbrwx : Γ'.borrowed x = true → CanDup H' v)
    (hepochs : ∀ y e, Γ'.brw.get? y = some e → e ≤ Γ'.epoch) :
    OwnedState functions H' external (live ++ [x]) Γ' (ρf.insert x w) (ρo.insert x v) owned'
      lex Δ Jf Jo := by
  refine ⟨fun y hy => ?_, hroots, hcounts, fun y hy => ?_,
    fresh_nodup_append st.distinct (by simp [fresh, hx]), fun y hy => ?_, fun y hy => ?_,
    hepochs, st.stack.bind x v w hx, st.scope.bind x⟩
  · by_cases he : y = x
    · subst he
      exact ⟨v, w, Src.NatMap.get?_insert_self .., Src.NatMap.get?_insert_self .., hdenx⟩
    · obtain ⟨v', w', h1, h2, h3⟩ := hden y he hy
      exact ⟨v', w', by rw [Src.NatMap.get?_insert_ne _ _ he]; exact h1,
        by rw [Src.NatMap.get?_insert_ne _ _ he]; exact h2, h3⟩
  · rcases hknown y hy with rfl | hk
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (st.known y hk)
  · by_cases he : y = x
    · subst he
      exact ⟨v, Src.NatMap.get?_insert_self .., himmx hy⟩
    · obtain ⟨v', h1, h2⟩ := himm y he hy
      exact ⟨v', by rw [Src.NatMap.get?_insert_ne _ _ he]; exact h1, h2⟩
  · by_cases he : y = x
    · subst he
      exact ⟨v, Src.NatMap.get?_insert_self .., hbrwx hy⟩
    · obtain ⟨v', h1, h2⟩ := hbrw y he hy
      exact ⟨v', by rw [Src.NatMap.get?_insert_ne _ _ he]; exact h1, h2⟩

/-- A variable not in scope is not known. -/
theorem OwnedState.unknown {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins}
    {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo) {x : Var}
    (hx : x ∉ live) : Γ.known x = false := by
  cases hk : Γ.known x with
  | false => rfl
  | true => exact absurd (st.known x hk) hx

end IxCC.Own.Plain
