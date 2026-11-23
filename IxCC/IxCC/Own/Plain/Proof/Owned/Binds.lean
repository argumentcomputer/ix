import IxCC.Own.Plain.Proof.Owned.Steps

/-! # Bindings that call nothing

`OwnedPre` is `OwnedState` without the count: the state of the other variables while a step's
tokens are in flight. A binding is a transformation of it (tokens taken, a release, a heap that
grew) followed by one of three ways to bind the fresh variable: owned with one token, an
immediate, or borrowed. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var Arg Rhs)

structure OwnedPre (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (live : List Var) (Γ : Ctx) (ρf : Fir.Env) (ρo : Own.Env) (owned : List RVal)
    (lex : Joins) (Δ : JCtx) (Jf : List Fir.JEntry) (Jo : List JEntry)
    (borrows : BorrowSigs := .leaf) : Prop where
  den : ∀ x, Γ.avail x = true → ∃ v w, ρo.get? x = some v ∧ ρf.get? x = some w ∧ Proof.Den H v w
  roots : ∃ toks, Ctx.Tokens Γ toks ∧ EnvRoots ρo toks owned
  known : ∀ x, Γ.known x = true → x ∈ live
  distinct : live.Nodup
  immOk : ∀ x, Γ.isImm x = true → ∃ v, ρo.get? x = some v ∧ ImmVal v
  borrowed : ∀ x, Γ.borrowed x = true → ∃ v, ρo.get? x = some v ∧ CanDup H v
  pbrwOk : ∀ x, Γ.isPbrw x = true → ∃ v, ρo.get? x = some v ∧ ReachableFrom H external v
  epochs : ∀ x e, Γ.brw.get? x = some e → e ≤ Γ.epoch
  stack : OwnedStack borrows Δ Γ.pbrw ρf ρo live lex Jf Jo
  scope : StackScope functions live lex Jf

section
variable {functions : Signatures} {H : Heap} {external : Nat → Nat} {live : List Var}
  {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins} {Δ : JCtx}
  {Jf : List Fir.JEntry} {Jo : List JEntry} {borrows : BorrowSigs}

theorem OwnedState.pre (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows) :
    OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows :=
  ⟨st.den, st.roots, st.known, st.distinct, st.immOk, st.borrowed, st.pbrwOk, st.epochs, st.stack, st.scope⟩

theorem OwnedPre.toState (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    (hb : Balance H external owned) :
    OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows :=
  ⟨pre.den, pre.roots, hb, pre.known, pre.distinct, pre.immOk, pre.borrowed, pre.pbrwOk, pre.epochs,
    pre.stack, pre.scope⟩

theorem OwnedPre.weaker (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    {Γ' : Ctx} {owned' : List RVal} (hw : Ctx.Weaker Γ' Γ)
    (hr : ∃ toks, Ctx.Tokens Γ' toks ∧ EnvRoots ρo toks owned') :
    OwnedPre functions H external live Γ' ρf ρo owned' lex Δ Jf Jo borrows :=
  ⟨fun x hx => pre.den x (hw.avail hx), hr, fun x hx => pre.known x (hw.known hx), pre.distinct,
    fun x hx => pre.immOk x (by rw [← hw.isImm x]; exact hx),
    fun x hx => pre.borrowed x (by rw [← hw.borrowed x]; exact hx),
    fun x hx => pre.pbrwOk x (by rw [← hw.isPbrw x]; exact hx),
    fun x e hx => by rw [hw.epoch]; exact pre.epochs x e (by rw [← hw.brw]; exact hx),
    hw.pbrw ▸ pre.stack, pre.scope⟩

/-- A release: nothing stays epoch-borrowed (`pbrw` survives). -/
theorem OwnedPre.release (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows) :
    OwnedPre functions H external live Γ.release ρf ρo owned lex Δ Jf Jo borrows := by
  have hnb := release_borrowed pre.epochs
  obtain ⟨toks, htok, hr⟩ := pre.roots
  refine ⟨fun y hy => pre.den y ?_, ⟨toks, htok.same rfl rfl, hr⟩,
    fun y hy => pre.known y (by simpa [Ctx.known_eq] using hy), pre.distinct,
    fun y hy => pre.immOk y (by simpa using hy), fun y hy => absurd hy (by simp [hnb y]),
    fun y hy => pre.pbrwOk y (by simpa using hy), fun y e hy => ?_, pre.stack, pre.scope⟩
  · simp only [Ctx.avail_eq, Ctx.isImm_release, Ctx.tokens_release, Ctx.isPbrw_release, hnb,
      Bool.or_false, Bool.or_eq_true] at hy
    simp only [Ctx.avail_eq, Bool.or_eq_true, decide_eq_true_eq]
    rcases hy with (hy | hy) | hy
    · exact Or.inl (Or.inl (Or.inl hy))
    · exact Or.inl (Or.inl (Or.inr (of_decide_eq_true hy)))
    · exact Or.inr hy
  · simp only [Ctx.brw_release, Ctx.epoch_release] at hy ⊢
    have := pre.epochs y e hy; omega

/-- A heap that keeps every denotation, every permission to increment, and every external-reachable cell. -/
theorem OwnedPre.transport (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    {H' : Heap} (hden : ∀ v w, Proof.Den H v w → Proof.Den H' v w)
    (hcan : ∀ v, CanDup H v → CanDup H' v)
    (hreach : ReachablePreserved H H' external) :
    OwnedPre functions H' external live Γ ρf ρo owned lex Δ Jf Jo borrows :=
  { pre with
    den := fun x hx => by
      obtain ⟨v, w, h1, h2, h3⟩ := pre.den x hx
      exact ⟨v, w, h1, h2, hden v w h3⟩
    borrowed := fun x hx => by
      obtain ⟨v, h1, h2⟩ := pre.borrowed x hx
      exact ⟨v, h1, hcan v h2⟩
    pbrwOk := fun x hx => by
      obtain ⟨v, h1, h2⟩ := pre.pbrwOk x hx
      exact ⟨v, h1, h2.transport hreach⟩ }

/-- After a call or `dec` that kept every live cell reachable from external owners and caller tokens. -/
theorem OwnedPre.call (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    (hnb : ∀ y, Γ.borrowed y = false) {H' : Heap}
    (hr : ReachablePreserved H H' (holdRoots external owned)) :
    OwnedPre functions H' external live Γ ρf ρo owned lex Δ Jf Jo borrows := by
  obtain ⟨toks, htok, hroots⟩ := pre.roots
  have hrext : ReachablePreserved H H' external := hr.of_holdRoots
  refine { pre with
    den := fun x hx => ?_
    borrowed := fun x hx => absurd hx (by simp [hnb x])
    pbrwOk := fun x hx => by
      obtain ⟨v, h1, h2⟩ := pre.pbrwOk x hx
      exact ⟨v, h1, h2.transport hrext⟩ }
  obtain ⟨v, w, h1, h2, h3⟩ := pre.den x hx
  refine ⟨v, w, h1, h2, ?_⟩
  simp only [Ctx.avail_eq, hnb, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hx
  rcases hx with (hi | hp') | hpb
  · obtain ⟨u, hu, himm⟩ := pre.immOk x hi
    have : u = v := Option.some.inj (hu.symm.trans h1)
    subst this
    exact den_imm himm h3
  · exact hr.externalPreserved v w (held_external (hroots.member (htok.mem hp') h1)) h3
  · obtain ⟨u, hu, hreach⟩ := pre.pbrwOk x hpb
    have : u = v := Option.some.inj (hu.symm.trans h1)
    subst this
    exact hrext.den hreach h3

/-! ## The fresh variable -/

theorem OwnedPre.fresh_facts (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    {x : Var} (hx : x ∉ live) :
    Γ.isImm x = false ∧ Γ.own.contains x = false ∧ Γ.brw.get? x = none ∧
      Γ.tokens x = 0 ∧ Γ.isPbrw x = false := by
  have hk : Γ.known x = false := by
    cases h : Γ.known x with
    | false => rfl
    | true => exact absurd (pre.known x h) hx
  simp only [Ctx.known_eq, Bool.or_eq_false_iff] at hk
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hk
  refine ⟨h1, h2, by simpa using h3, ?_, h4⟩
  simp only [Src.NatMap.contains] at h2
  simp only [Ctx.tokens_eq]
  cases hg : Γ.own.get? x with
  | none => rfl
  | some n => rw [hg] at h2; cases h2

theorem OwnedPre.not_tok (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    {x : Var} (hx : x ∉ live) {toks : List Var} (htok : Ctx.Tokens Γ toks) : x ∉ toks := by
  intro hm
  exact hx (pre.known x (Tokens.mem_known htok hm))

/-- The state after a fresh binding, from what the step establishes for each variable. -/
theorem OwnedPre.extend (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
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
    (hpbrw : ∀ y, y ≠ x → Γ'.isPbrw y = true → ∃ v, ρo.get? y = some v ∧ ReachableFrom H' external v)
    (hpbrwx : Γ'.isPbrw x = true → ReachableFrom H' external v)
    (hpbrwSub : ∀ y, Γ.pbrw.contains y = true → Γ'.pbrw.contains y = true)
    (hepochs : ∀ y e, Γ'.brw.get? y = some e → e ≤ Γ'.epoch) :
    OwnedState functions H' external (live ++ [x]) Γ' (ρf.insert x w) (ρo.insert x v) owned'
      lex Δ Jf Jo borrows := by
  refine ⟨fun y hy => ?_, hroots, hcounts, fun y hy => ?_,
    fresh_nodup_append pre.distinct (by simp [fresh, hx]), fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_, hepochs, (pre.stack.mono_pbrw hpbrwSub).bind x v w hx, pre.scope.bind x⟩
  · by_cases he : y = x
    · subst he
      exact ⟨v, w, Src.NatMap.get?_insert_self .., Src.NatMap.get?_insert_self .., hdenx⟩
    · obtain ⟨v', w', h1, h2, h3⟩ := hden y he hy
      exact ⟨v', w', by rw [Src.NatMap.get?_insert_ne _ _ he]; exact h1,
        by rw [Src.NatMap.get?_insert_ne _ _ he]; exact h2, h3⟩
  · rcases hknown y hy with rfl | hk
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (pre.known y hk)
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
  · by_cases he : y = x
    · subst he
      exact ⟨v, Src.NatMap.get?_insert_self .., hpbrwx hy⟩
    · obtain ⟨v', h1, h2⟩ := hpbrw y he hy
      exact ⟨v', by rw [Src.NatMap.get?_insert_ne _ _ he]; exact h1, h2⟩

theorem OwnedPre.bindOwned (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    {x : Var} (hx : x ∉ live) {v : RVal} {w : Fir.Val} (hd : Proof.Den H v w)
    (hb : Balance H external (v :: owned)) :
    OwnedState functions H external (live ++ [x]) (Γ.addOwn x 1) (ρf.insert x w)
      (ρo.insert x v) (v :: owned) lex Δ Jf Jo borrows := by
  obtain ⟨hi, _, hbx, _, hpbx⟩ := pre.fresh_facts hx
  obtain ⟨toks, htok, hr⟩ := pre.roots
  have hxt := pre.not_tok hx htok
  refine pre.extend hx (fun y he hy => pre.den y ?_) hd
    ⟨x :: toks, htok.addOwn x, EnvRoots.cons (Src.NatMap.get?_insert_self ..)
      (hr.insert_fresh x v hxt)⟩ hb (fun y hy => ?_) (fun y _ hy => pre.immOk y (by simpa using hy))
    (fun hy => by simp [hi] at hy) (fun y _ hy => pre.borrowed y (by simpa [Ctx.borrowed_eq] using hy))
    (fun hy => by simp [Ctx.borrowed_eq, hbx] at hy)
    (fun y _ hy => pre.pbrwOk y (by simpa using hy))
    (fun hy => by simp [hpbx] at hy) (fun _ h => h)
    (fun y e hy => pre.epochs y e (by simpa using hy))
  · simp only [Ctx.avail_eq, Ctx.isImm_addOwn, Ctx.tokens_addOwn, if_neg he, Ctx.borrowed_eq,
      Ctx.brw_addOwn, Ctx.epoch_addOwn, Ctx.isPbrw_addOwn] at hy ⊢
    exact hy
  · simp only [Ctx.known_eq, Ctx.isImm_addOwn, Ctx.ownHas_addOwn, Ctx.brw_addOwn, Ctx.isPbrw_addOwn,
      Bool.or_eq_true, decide_eq_true_eq] at hy ⊢
    rcases hy with ((h | h | h) | h) | h
    · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr h)

theorem OwnedPre.bindImm (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    {x : Var} (hx : x ∉ live) {v : RVal} {w : Fir.Val} (hd : Proof.Den H v w) (himm : ImmVal v)
    (hb : Balance H external owned) :
    OwnedState functions H external (live ++ [x]) (Γ.setImm x) (ρf.insert x w)
      (ρo.insert x v) owned lex Δ Jf Jo borrows := by
  obtain ⟨_, _, hbx, _, hpbx⟩ := pre.fresh_facts hx
  obtain ⟨toks, htok, hr⟩ := pre.roots
  have hxt := pre.not_tok hx htok
  have hf : toks.filter (fun y => y != x) = toks :=
    List.filter_eq_self.mpr (fun a ha => by
      have : a ≠ x := fun he => hxt (he ▸ ha)
      simpa using this)
  have htok' := htok.setImm x
  rw [hf] at htok'
  refine pre.extend hx (fun y he hy => pre.den y ?_) hd
    ⟨toks, htok', hr.insert_fresh x v hxt⟩ hb (fun y hy => ?_)
    (fun y he hy => pre.immOk y (by simpa [Ctx.isImm_setImm, he] using hy)) (fun _ => himm)
    (fun y he hy => pre.borrowed y (by simpa [Ctx.borrowed_eq, Ctx.brw_setImm, he] using hy))
    (fun hy => by simp [Ctx.borrowed_eq, Ctx.brw_setImm] at hy)
    (fun y _ hy => pre.pbrwOk y (by simpa using hy))
    (fun hy => by simp [hpbx] at hy) (fun _ h => h) (fun y e hy => ?_)
  · simp only [Ctx.avail_eq, Ctx.isImm_setImm, Ctx.tokens_setImm, Ctx.borrowed_eq,
      Ctx.brw_setImm, Ctx.epoch_setImm, Ctx.isPbrw_setImm, he, decide_false, Bool.false_or,
      ↓reduceIte] at hy ⊢
    exact hy
  · simp only [Ctx.known_eq, Ctx.isImm_setImm, Ctx.ownHas_setImm, Ctx.brw_setImm, Ctx.isPbrw_setImm,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hy ⊢
    by_cases he : y = x
    · exact Or.inl he
    · right
      simp only [he, decide_false, Bool.not_false, true_and, false_or, ↓reduceIte] at hy
      exact hy
  · simp only [Ctx.brw_setImm, Ctx.epoch_setImm] at hy
    split at hy
    · cases hy
    · exact pre.epochs y e hy

theorem OwnedPre.bindBorrow (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    {x : Var} (hx : x ∉ live) {v : RVal} {w : Fir.Val} (hd : Proof.Den H v w)
    (hcan : CanDup H v) (hb : Balance H external owned) :
    OwnedState functions H external (live ++ [x]) (Γ.setBorrow x) (ρf.insert x w)
      (ρo.insert x v) owned lex Δ Jf Jo borrows := by
  obtain ⟨hi, _, _, _, hpbx⟩ := pre.fresh_facts hx
  obtain ⟨toks, htok, hr⟩ := pre.roots
  have hxt := pre.not_tok hx htok
  refine pre.extend hx (fun y he hy => pre.den y ?_) hd
    ⟨toks, htok.same rfl rfl, hr.insert_fresh x v hxt⟩ hb (fun y hy => ?_)
    (fun y _ hy => pre.immOk y (by simpa using hy)) (fun hy => by simp [hi] at hy)
    (fun y he hy => pre.borrowed y (by simpa [Ctx.borrowed_eq, Ctx.brw_setBorrow, he] using hy))
    (fun _ => hcan)
    (fun y _ hy => pre.pbrwOk y (by simpa using hy))
    (fun hy => by simp [hpbx] at hy) (fun _ h => h) (fun y e hy => ?_)
  · simp only [Ctx.avail_eq, Ctx.isImm_setBorrow, Ctx.tokens_setBorrow, Ctx.borrowed_eq,
      Ctx.brw_setBorrow, Ctx.epoch_setBorrow, Ctx.isPbrw_setBorrow, he, ↓reduceIte] at hy ⊢
    exact hy
  · simp only [Ctx.known_eq, Ctx.isImm_setBorrow, Ctx.own_setBorrow, Ctx.brw_setBorrow,
      Ctx.isPbrw_setBorrow, Bool.or_eq_true] at hy ⊢
    by_cases he : y = x
    · exact Or.inl he
    · right
      simp only [he, ↓reduceIte] at hy
      exact hy
  · simp only [Ctx.brw_setBorrow, Ctx.epoch_setBorrow] at hy
    split at hy
    · cases hy; exact Nat.le_refl _
    · exact pre.epochs y e hy

theorem OwnedPre.bindPbrw (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    {x : Var} (hx : x ∉ live) {v : RVal} {w : Fir.Val} (hd : Proof.Den H v w)
    (hreach : ReachableFrom H external v) (hb : Balance H external owned) :
    OwnedState functions H external (live ++ [x]) (Γ.setPbrw x) (ρf.insert x w)
      (ρo.insert x v) owned lex Δ Jf Jo borrows := by
  obtain ⟨hi, _, hbx, _, _⟩ := pre.fresh_facts hx
  obtain ⟨toks, htok, hr⟩ := pre.roots
  have hxt := pre.not_tok hx htok
  refine pre.extend hx (fun y he hy => pre.den y ?_) hd
    ⟨toks, htok.same rfl rfl, hr.insert_fresh x v hxt⟩ hb (fun y hy => ?_)
    (fun y _ hy => pre.immOk y (by simpa using hy)) (fun hy => by simp [hi] at hy)
    (fun y _ hy => pre.borrowed y (by simpa [Ctx.borrowed_eq] using hy))
    (fun hy => by simp [Ctx.borrowed_eq, hbx] at hy)
    (fun y he hy => pre.pbrwOk y (by simpa [Ctx.isPbrw_setPbrw, he] using hy))
    (fun _ => hreach)
    (fun y hy => by
      change (Γ.setPbrw x).isPbrw y = true
      rw [Ctx.isPbrw_setPbrw]; exact Bool.or_eq_true_iff.mpr (Or.inr hy))
    (fun y e hy => pre.epochs y e hy)
  · simp only [Ctx.avail_eq, Ctx.isImm_setPbrw, Ctx.tokens_setPbrw, Ctx.borrowed_eq,
      Ctx.brw_setPbrw, Ctx.epoch_setPbrw, Ctx.isPbrw_setPbrw, he, decide_false, Bool.false_or] at hy ⊢
    exact hy
  · simp only [Ctx.known_eq, Ctx.isImm_setPbrw, Ctx.own_setPbrw, Ctx.brw_setPbrw, Ctx.isPbrw_setPbrw,
      Bool.or_eq_true, decide_eq_true_eq] at hy ⊢
    by_cases he : y = x
    · exact Or.inl he
    · right
      simp only [he, false_or] at hy
      exact hy

/-- A variable whose value is an immediate becomes one; its tokens were vacuous. -/
theorem OwnedPre.setImmVar (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    {y : Var} (hy : Γ.avail y = true) {u : RVal} (hu : ρo.get? y = some u) (himm : ImmVal u) :
    ∃ owned', OwnedPre functions H external live (Γ.setImm y) ρf ρo owned' lex Δ Jf Jo borrows ∧
      SameRefs owned owned' := by
  obtain ⟨toks, htok, hr⟩ := pre.roots
  obtain ⟨owned', hr', hs⟩ := EnvRoots.filter_imm hu himm hr
  refine ⟨owned', ⟨fun z hz => ?_, ⟨_, htok.setImm y, hr'⟩, fun z hz => pre.known z ?_,
    pre.distinct, fun z hz => ?_, fun z hz => pre.borrowed z ?_,
    fun z hz => pre.pbrwOk z (by simpa using hz), fun z e hz => ?_, pre.stack, pre.scope⟩, hs⟩
  · by_cases he : z = y
    · subst he; exact pre.den z hy
    · apply pre.den z
      simp only [Ctx.avail_eq, Ctx.isImm_setImm, Ctx.tokens_setImm, Ctx.borrowed_eq,
        Ctx.brw_setImm, Ctx.epoch_setImm, Ctx.isPbrw_setImm, he, decide_false, Bool.false_or,
        ↓reduceIte] at hz ⊢
      exact hz
  · by_cases he : z = y
    · subst he; exact Ctx.avail_known hy
    · simp only [Ctx.known_eq, Ctx.isImm_setImm, Ctx.ownHas_setImm, Ctx.brw_setImm, Ctx.isPbrw_setImm,
        he, decide_false, Bool.false_or, Bool.not_false, Bool.true_and, ↓reduceIte] at hz ⊢
      exact hz
  · by_cases he : z = y
    · subst he; exact ⟨u, hu, himm⟩
    · exact pre.immOk z (by simpa [Ctx.isImm_setImm, he] using hz)
  · by_cases he : z = y
    · subst he; simp [Ctx.borrowed_eq, Ctx.brw_setImm] at hz
    · simpa [Ctx.borrowed_eq, Ctx.brw_setImm, he] using hz
  · simp only [Ctx.brw_setImm, Ctx.epoch_setImm] at hz
    split at hz
    · cases hz
    · exact pre.epochs z e hz

theorem Ctx.avail_setImm {Γ : Ctx} {y z : Var} (h : Γ.avail y = true) : (Γ.setImm z).avail y = true := by
  by_cases he : y = z
  · subst he; simp [Ctx.avail_eq, Ctx.isImm_setImm]
  · simp only [Ctx.avail_eq, Ctx.isImm_setImm, Ctx.tokens_setImm, Ctx.borrowed_eq,
      Ctx.brw_setImm, Ctx.epoch_setImm, Ctx.isPbrw_setImm, he, decide_false, Bool.false_or,
      ↓reduceIte] at h ⊢
    exact h

/-- A primitive's marked arguments become immediates (their values are, once it has returned). -/
theorem OwnedPre.immArgs :
    ∀ (ms : List Bool) (args : List Arg) {Γ : Ctx} {owned : List RVal},
      OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows →
      (∀ y, Arg.var y ∈ args → Γ.avail y = true ∧ ∃ u, ρo.get? y = some u ∧ ImmVal u) →
      ∃ owned', OwnedPre functions H external live (Γ.immArgs ms args) ρf ρo owned' lex Δ Jf Jo borrows ∧
        SameRefs owned owned'
  | true :: ms, .var y :: as, Γ, owned, pre, hargs => by
    obtain ⟨hy, u, hu, himm⟩ := hargs y List.mem_cons_self
    obtain ⟨owned₁, pre₁, hs₁⟩ := pre.setImmVar hy hu himm
    obtain ⟨owned', pre', hs'⟩ := OwnedPre.immArgs ms as pre₁ (fun z hz => by
      obtain ⟨hz', rest⟩ := hargs z (List.mem_cons_of_mem _ hz)
      exact ⟨Ctx.avail_setImm hz', rest⟩)
    exact ⟨owned', by simpa [Ctx.immArgs] using pre', hs₁.trans hs'⟩
  | false :: ms, a :: as, Γ, owned, pre, hargs => by
    obtain ⟨owned', pre', hs'⟩ := OwnedPre.immArgs ms as pre
      (fun z hz => hargs z (List.mem_cons_of_mem _ hz))
    exact ⟨owned', by simpa [Ctx.immArgs] using pre', hs'⟩
  | true :: ms, .lit l :: as, Γ, owned, pre, hargs => by
    obtain ⟨owned', pre', hs'⟩ := OwnedPre.immArgs ms as pre
      (fun z hz => hargs z (List.mem_cons_of_mem _ hz))
    exact ⟨owned', by simpa [Ctx.immArgs] using pre', hs'⟩
  | true :: ms, .erased :: as, Γ, owned, pre, hargs => by
    obtain ⟨owned', pre', hs'⟩ := OwnedPre.immArgs ms as pre
      (fun z hz => hargs z (List.mem_cons_of_mem _ hz))
    exact ⟨owned', by simpa [Ctx.immArgs] using pre', hs'⟩
  | [], _, Γ, owned, pre, _ => ⟨owned, by simpa [Ctx.immArgs] using pre, SameRefs.refl _⟩
  | _ :: _, [], Γ, owned, pre, _ => ⟨owned, by simpa [Ctx.immArgs] using pre, SameRefs.refl _⟩

end

end IxCC.Own.Plain
