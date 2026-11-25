import IxCC.Own.Plain.Proof.Owned.Steps

/-! # Bindings that call nothing

`OwnedPre` is `OwnedState` without the count: the state of the other variables while a step's
tokens are in flight. A binding is a transformation of it (tokens taken, a release, a heap that
grew) followed by one of the fresh-variable bindings (`bindOwned`, `bindUniqOwned`, `bindImm`,
`bindImmUniq`, `bindBorrow`, `bindPbrw`), plus `setProj` and `setCtor` refinements. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var Arg Rhs)

structure OwnedPre (functions : Signatures) (H : Heap) (external : Nat → Nat)
    (live : List Var) (Γ : Ctx) (ρf : Fir.Env) (ρo : Own.Env) (owned : List RVal)
    (lex : Joins) (Δ : JCtx) (Jf : List Fir.JEntry) (Jo : List JEntry)
    (borrows : BorrowSigs := .leaf) (uniqs : UniqSigs := .leaf)
    (retUniq : Bool := false) (ctors : List Lam.CtorInfo := []) (K : Lam.Known := {})
    (priv : Nat → Prop := fun _ => False)
    (slots : Src.NatMap RVal := .leaf) (slotVals : List RVal := []) : Prop where
  den : ∀ x, Γ.avail x = true → ∃ v w, ρo.get? x = some v ∧ ρf.get? x = some w ∧ Proof.Den H v w
  roots : ∃ toks, Ctx.Tokens Γ toks ∧ EnvRoots ρo toks owned
  slotRoots : ∃ skeys, Ctx.SlotKeys Γ skeys ∧ EnvRoots slots skeys slotVals
  known : ∀ x, Γ.known x = true → x ∈ live
  distinct : live.Nodup
  immOk : ∀ x, Γ.isImm x = true → ∃ v, ρo.get? x = some v ∧ ImmVal v
  borrowed : ∀ x, Γ.borrowed x = true → ∃ v, ρo.get? x = some v ∧ BorrowVal H v
  pbrwOk : ∀ x, Γ.isPbrw x = true → ∃ v, ρo.get? x = some v ∧ ReachableFrom H external v
  epochs : ∀ x e, Γ.brw.get? x = some e → e ≤ Γ.epoch
  ctorOfKnown : ∀ x key, Γ.ctorOf.get? x = some key → x ∈ live
  projOfKnown : ∀ v x key idx, Γ.projOf.get? v = some (x, key, idx) → v ∈ live ∧ x ∈ live
  ctorOfOk : ∀ x key, Γ.avail x = true → Γ.ctorOf.get? x = some key →
    ∃ v fields, ρo.get? x = some v ∧ v.asCtor K H = some (key, fields)
  projOfOk : ∀ v x key idx, Γ.avail x = true → Γ.avail v = true →
    Γ.projOf.get? v = some (x, key, idx) →
    ∃ vx fields uv, ρo.get? x = some vx ∧ vx.asCtor K H = some (key, fields) ∧
      fields[idx]? = some uv ∧ ρo.get? v = some uv
  uniqOk : ∀ x, Γ.isUniq x = true →
    (Γ.isImm x = false → Γ.tokens x = 1 ∧ Γ.isPbrw x = false) ∧
    ∃ v, ρo.get? x = some v ∧ UniqVal ctors H external (owned ++ slotVals) v
  rsetOk : ∀ s cls u, Γ.rset.get? s = some (cls, u) →
    ∃ sv, slots.get? s = some sv ∧
      ((sv = .erased ∧ u = false) ∨
       (∃ l b, sv = .loc l ∧ H.cell? l = some (.live 1 .dyn b) ∧
         Ctx.validReuseCtor b.ctor = some cls ∧ b.fields = List.replicate b.ctor.arity .erased ∧
         external l = 0 ∧ edgeCount H l = 0 ∧ refsIn l (owned ++ slotVals) = 1))
  privBound : ∀ l, priv l → l < H.size
  privNoEdge : ∀ l, priv l → edgeCount H l = 0
  privNoVar : ∀ l, priv l → ∀ x, Γ.avail x = true → ρo.get? x ≠ some (.loc l)
  privNoSlot : ∀ l, priv l → ∀ s, Γ.rset.contains s = true → slots.get? s ≠ some (.loc l)
  stack : OwnedStack borrows uniqs retUniq ctors K Δ Γ.pbrw ρf ρo live lex Jf Jo
  scope : StackScope functions live lex Jf

section
variable {functions : Signatures} {H : Heap} {external : Nat → Nat} {live : List Var}
  {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins} {Δ : JCtx}
  {Jf : List Fir.JEntry} {Jo : List JEntry} {borrows : BorrowSigs} {uniqs : UniqSigs}
  {retUniq : Bool} {ctors : List Lam.CtorInfo} {K : Lam.Known} {priv : Nat → Prop}
  {slots : Src.NatMap RVal} {slotVals : List RVal}

theorem OwnedState.pre (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals) :
    OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq ctors K priv slots slotVals :=
  ⟨st.den, st.roots, st.slotRoots, st.known, st.distinct, st.immOk, st.borrowed, st.pbrwOk,
    st.epochs, st.ctorOfKnown, st.projOfKnown, st.ctorOfOk, st.projOfOk, st.uniqOk, st.rsetOk,
    st.privBound, st.privNoEdge, st.privNoVar, st.privNoSlot, st.stack, st.scope⟩

theorem OwnedPre.toState (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    (hb : Balance H external (owned ++ slotVals)) :
    OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq ctors K priv slots slotVals :=
  ⟨pre.den, pre.roots, pre.slotRoots, hb, pre.known, pre.distinct, pre.immOk, pre.borrowed,
    pre.pbrwOk, pre.epochs, pre.ctorOfKnown, pre.projOfKnown, pre.ctorOfOk, pre.projOfOk,
    pre.uniqOk, pre.rsetOk, pre.privBound, pre.privNoEdge, pre.privNoVar, pre.privNoSlot,
    pre.stack, pre.scope⟩

/-- Locations owned uniquely by surviving `@unique` variables or live reset slots of `pre`. -/
def OwnedPre.localPriv (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals) (l : Nat) : Prop :=
  priv l ∨
  (∃ s cls u, Γ.rset.get? s = some (cls, u) ∧ slots.get? s = some (.loc l)) ∨
  (∃ z, Γ.isUniq z = true ∧ Γ.isImm z = false ∧ ρo.get? z = some (.loc l))

theorem OwnedPre.localPriv_facts (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals) {l : Nat} (hl : pre.localPriv l) :
    l < H.size ∧ edgeCount H l = 0 := by
  rcases hl with hp | ⟨s, cls, u, hrs, hsl⟩ | ⟨z, hu, hi, hz⟩
  · exact ⟨pre.privBound l hp, pre.privNoEdge l hp⟩
  · obtain ⟨sv, hsv, hcase⟩ := pre.rsetOk s cls u hrs
    have : sv = .loc l := Option.some.inj (hsv.symm.trans hsl); subst this
    rcases hcase with ⟨hc, _⟩ | ⟨l', b, hEq, hc, _, _, _, hedge, _⟩
    · cases hc
    · cases hEq; exact ⟨Proof.cell?_some hc, hedge⟩
  · obtain ⟨_, v, hv, hvu⟩ := pre.uniqOk z hu
    have : v = .loc l := Option.some.inj (hv.symm.trans hz); subst this
    obtain ⟨b, hc, _, hedge, _⟩ := hvu
    exact ⟨Proof.cell?_some hc, hedge⟩

theorem OwnedPre.weaker (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {Γ' : Ctx} {owned' : List RVal} (hw : Ctx.Weaker Γ' Γ)
    (hr : ∃ toks, Ctx.Tokens Γ' toks ∧ EnvRoots ρo toks owned')
    (hle : ∀ k, refsIn k owned' ≤ refsIn k owned) :
    OwnedPre functions H external live Γ' ρf ρo owned' lex Δ Jf Jo
      borrows uniqs retUniq ctors K priv slots slotVals := by
  obtain ⟨skeys, hsk, hsroots⟩ := pre.slotRoots
  obtain ⟨toks', htok', hroots'⟩ := hr
  refine ⟨fun x hx => pre.den x (hw.avail hx), ⟨toks', htok', hroots'⟩,
    ⟨skeys, hsk.same hw.rset, hsroots⟩,
    fun x hx => pre.known x (hw.known hx), pre.distinct,
    fun x hx => pre.immOk x (by rw [← hw.isImm x]; exact hx),
    fun x hx => pre.borrowed x (by rw [← hw.borrowed x]; exact hx),
    fun x hx => pre.pbrwOk x (by rw [← hw.isPbrw x]; exact hx),
    fun x e hx => by rw [hw.epoch]; exact pre.epochs x e (by rw [← hw.brw]; exact hx),
    fun x key hc => pre.ctorOfKnown x key (by rw [← hw.ctorOf]; exact hc),
    fun v x key idx hp => pre.projOfKnown v x key idx (by rw [← hw.projOf]; exact hp),
    fun x key hx hc => pre.ctorOfOk x key (hw.avail hx) (by rw [← hw.ctorOf]; exact hc),
    fun v x key idx hx hv hp => pre.projOfOk v x key idx (hw.avail hx) (hw.avail hv)
      (by rw [← hw.projOf]; exact hp),
    fun x hx => ?_, fun s cls u hrs => ?_,
    pre.privBound, pre.privNoEdge,
    fun l hl x hx => pre.privNoVar l hl x (hw.avail hx),
    fun l hl s hs => pre.privNoSlot l hl s (by rw [← hw.rset]; exact hs),
    hw.pbrw ▸ pre.stack, pre.scope⟩
  · have hx0 := hw.isUniq x hx
    obtain ⟨hmeta, v, hv, hvu⟩ := pre.uniqOk x hx0
    refine ⟨fun hi => ?_, v, hv, ?_⟩
    · have hi0 : Γ.isImm x = false := by rw [← hw.isImm x]; exact hi
      obtain ⟨htok1, hpb⟩ := hmeta hi0
      exact ⟨(hw.uniqTok x hx hi).trans htok1, by rw [hw.isPbrw x]; exact hpb⟩
    · cases v with
      | lit _ | erased => trivial
      | ctor0 c => exact hvu
      | loc l =>
        cases hi : Γ'.isImm x with
        | true =>
          obtain ⟨u, hu, himm⟩ := pre.immOk x (by rw [← hw.isImm x]; exact hi)
          have : u = .loc l := Option.some.inj (hu.symm.trans hv); subst this
          exact absurd rfl (himm l)
        | false =>
          have hi0 : Γ.isImm x = false := by rw [← hw.isImm x]; exact hi
          have ht1 : Γ'.tokens x = 1 := (hw.uniqTok x hx hi).trans (hmeta hi0).1
          have hmem : RVal.loc l ∈ owned' := hroots'.member (htok'.mem (by omega)) hv
          have hpos := refsIn_pos hmem
          obtain ⟨b, hc, hext, hedge, hrefs⟩ := hvu
          have hl' := hle l
          rw [refsIn_append] at hrefs
          exact ⟨b, hc, hext, hedge, by rw [refsIn_append]; omega⟩
  · have hrs0 : Γ.rset.get? s = some (cls, u) := by rw [← hw.rset]; exact hrs
    obtain ⟨sv, hsv, hcase⟩ := pre.rsetOk s cls u hrs0
    refine ⟨sv, hsv, ?_⟩
    rcases hcase with h0 | ⟨l, b, rfl, hc, hvc, hbf, hext, hedge, hrefs⟩
    · exact Or.inl h0
    · right
      have hhas : Γ.rset.contains s = true := by simp [Src.NatMap.contains, hrs0]
      have hmem : RVal.loc l ∈ slotVals := hsroots.member ((hsk.mem s).mpr hhas) hsv
      have hpos := refsIn_pos hmem
      have hl' := hle l
      rw [refsIn_append] at hrefs
      exact ⟨l, b, rfl, hc, hvc, hbf, hext, hedge, by rw [refsIn_append]; omega⟩

/-- A release: nothing stays epoch-borrowed (`pbrw`, `uniq`, `rset`, `ctorOf`, `projOf` survive). -/
theorem OwnedPre.release (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals) :
    OwnedPre functions H external live Γ.release ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq ctors K priv slots slotVals := by
  have hnb := release_borrowed pre.epochs
  have hav : ∀ y, Γ.release.avail y = true → Γ.avail y = true := fun y hy => by
    simp only [Ctx.avail_eq, Ctx.isImm_release, Ctx.tokens_release, Ctx.isPbrw_release, hnb,
      Bool.or_false, Bool.or_eq_true] at hy
    simp only [Ctx.avail_eq, Bool.or_eq_true, decide_eq_true_eq]
    rcases hy with (hy | hy) | hy
    · exact Or.inl (Or.inl (Or.inl hy))
    · exact Or.inl (Or.inl (Or.inr (of_decide_eq_true hy)))
    · exact Or.inr hy
  obtain ⟨toks, htok, hr⟩ := pre.roots
  obtain ⟨skeys, hsk, hsr⟩ := pre.slotRoots
  refine ⟨fun y hy => pre.den y (hav y hy), ⟨toks, htok.same rfl rfl, hr⟩,
    ⟨skeys, hsk.same rfl, hsr⟩,
    fun y hy => pre.known y (by simpa [Ctx.known_eq] using hy), pre.distinct,
    fun y hy => pre.immOk y (by simpa using hy), fun y hy => absurd hy (by simp [hnb y]),
    fun y hy => pre.pbrwOk y (by simpa using hy), fun y e hy => ?_,
    pre.ctorOfKnown, pre.projOfKnown,
    fun y key hy hc => pre.ctorOfOk y key (hav y hy) hc,
    fun v y key idx hy hv hp => pre.projOfOk v y key idx (hav y hy) (hav v hv) hp,
    pre.uniqOk, pre.rsetOk, pre.privBound, pre.privNoEdge,
    fun l hl y hy => pre.privNoVar l hl y (hav y hy), pre.privNoSlot, pre.stack, pre.scope⟩
  simp only [Ctx.brw_release, Ctx.epoch_release] at hy ⊢
  have := pre.epochs y e hy; omega

/-- Transport across a non-releasing heap step (`inc`, `alloc`, `reuse` of a shell). -/
theorem OwnedPre.transport (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {H' : Heap}
    (hden : ∀ v w, Proof.Den H v w → Proof.Den H' v w)
    (hbrw : ∀ v, BorrowVal H v → BorrowVal H' v)
    (hreach : ReachablePreserved H H' external)
    (hasCtor : ∀ x key v fields, Γ.avail x = true → ρo.get? x = some v →
      v.asCtor K H = some (key, fields) → v.asCtor K H' = some (key, fields))
    (hpriv : PrivPreserved H H' pre.localPriv) :
    OwnedPre functions H' external live Γ ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq ctors K priv slots slotVals :=
  { pre with
    den := fun x hx => by
      obtain ⟨v, w, h1, h2, h3⟩ := pre.den x hx
      exact ⟨v, w, h1, h2, hden v w h3⟩
    borrowed := fun x hx => by
      obtain ⟨v, h1, h2⟩ := pre.borrowed x hx
      exact ⟨v, h1, hbrw v h2⟩
    pbrwOk := fun x hx => by
      obtain ⟨v, h1, h2⟩ := pre.pbrwOk x hx
      exact ⟨v, h1, h2.transport hreach⟩
    ctorOfOk := fun x key hx hc => by
      obtain ⟨v, fs, hv, hac⟩ := pre.ctorOfOk x key hx hc
      exact ⟨v, fs, hv, hasCtor x key v fs hx hv hac⟩
    projOfOk := fun v x key idx hx hv hp => by
      obtain ⟨vx, fs, uv, hvx, hac, hget, huv⟩ := pre.projOfOk v x key idx hx hv hp
      exact ⟨vx, fs, uv, hvx, hasCtor x key vx fs hx hvx hac, hget, huv⟩
    uniqOk := fun x hx => by
      obtain ⟨hmeta, v, hv, hvu⟩ := pre.uniqOk x hx
      refine ⟨hmeta, v, hv, ?_⟩
      cases v with
      | lit _ | erased => trivial
      | ctor0 c => exact hvu
      | loc l =>
        cases hi : Γ.isImm x with
        | true =>
          obtain ⟨u, hu, himm⟩ := pre.immOk x hi
          have : u = .loc l := Option.some.inj (hu.symm.trans hv); subst this
          exact absurd rfl (himm l)
        | false =>
          obtain ⟨b, hc, hext, _, hrefs⟩ := hvu
          obtain ⟨hcell, hedge⟩ := hpriv l (Or.inr (Or.inr ⟨x, hx, hi, hv⟩))
          exact ⟨b, hcell.trans hc, hext, hedge, hrefs⟩
    rsetOk := fun s cls u hrs => by
      obtain ⟨sv, hsv, hcase⟩ := pre.rsetOk s cls u hrs
      refine ⟨sv, hsv, ?_⟩
      rcases hcase with h0 | ⟨l, b, rfl, hc, hvc, hbf, hext, _, hrefs⟩
      · exact Or.inl h0
      · obtain ⟨hcell, hedge⟩ := hpriv l (Or.inr (Or.inl ⟨s, cls, u, hrs, hsv⟩))
        exact Or.inr ⟨l, b, rfl, hcell.trans hc, hvc, hbf, hext, hedge, hrefs⟩
    privBound := fun l hl => Nat.lt_of_lt_of_le (pre.privBound l hl) hreach.1
    privNoEdge := fun l hl => (hpriv l (Or.inl hl)).2 }

/-- After a releasing step (`dec`, `dropSlot`, non-tail `call`). -/
theorem OwnedPre.call (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    (hnb : ∀ y, Γ.borrowed y = false) {H' : Heap}
    (hr : ReachablePreserved H H' (holdRoots external (owned ++ slotVals)))
    (hpriv : PrivPreserved H H' pre.localPriv) :
    OwnedPre functions H' external live Γ ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq ctors K priv slots slotVals := by
  obtain ⟨toks, htok, hroots⟩ := pre.roots
  have hrext : ReachablePreserved H H' external := hr.of_holdRoots
  have hreachAvail : ∀ x v, Γ.avail x = true → ρo.get? x = some v →
      ReachableFrom H (holdRoots external (owned ++ slotVals)) v := by
    intro x v hx hv
    simp only [Ctx.avail_eq, hnb, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hx
    rcases hx with (hi | hp') | hpb
    · obtain ⟨u, hu, himm⟩ := pre.immOk x hi
      have : u = v := Option.some.inj (hu.symm.trans hv); subst this
      exact .imm himm
    · have hmem : v ∈ owned ++ slotVals := List.mem_append_left _ (hroots.member (htok.mem hp') hv)
      exact ReachableFrom.of_externalRoot (held_external hmem)
    · obtain ⟨u, hu, hreach⟩ := pre.pbrwOk x hpb
      have : u = v := Option.some.inj (hu.symm.trans hv); subst this
      exact hreach.mono_ext (fun l => by simp [holdRoots])
  refine { pre with
    den := fun x hx => by
      obtain ⟨v, w, h1, h2, h3⟩ := pre.den x hx
      exact ⟨v, w, h1, h2, hr.den (hreachAvail x v hx h1) h3⟩
    borrowed := fun x hx => absurd hx (by simp [hnb x])
    pbrwOk := fun x hx => by
      obtain ⟨v, h1, h2⟩ := pre.pbrwOk x hx
      exact ⟨v, h1, h2.transport hrext⟩
    ctorOfOk := fun x key hx hc => by
      obtain ⟨v, fs, hv, hac⟩ := pre.ctorOfOk x key hx hc
      exact ⟨v, fs, hv, hr.asCtor (hreachAvail x v hx hv) hac⟩
    projOfOk := fun v x key idx hx hv hp => by
      obtain ⟨vx, fs, uv, hvx, hac, hget, huv⟩ := pre.projOfOk v x key idx hx hv hp
      exact ⟨vx, fs, uv, hvx, hr.asCtor (hreachAvail x vx hx hvx) hac, hget, huv⟩
    uniqOk := fun x hx => by
      obtain ⟨hmeta, v, hv, hvu⟩ := pre.uniqOk x hx
      refine ⟨hmeta, v, hv, ?_⟩
      cases v with
      | lit _ | erased => trivial
      | ctor0 c => exact hvu
      | loc l =>
        cases hi : Γ.isImm x with
        | true =>
          obtain ⟨u, hu, himm⟩ := pre.immOk x hi
          have : u = .loc l := Option.some.inj (hu.symm.trans hv); subst this
          exact absurd rfl (himm l)
        | false =>
          obtain ⟨b, hc, hext, _, hrefs⟩ := hvu
          obtain ⟨hcell, hedge⟩ := hpriv l (Or.inr (Or.inr ⟨x, hx, hi, hv⟩))
          exact ⟨b, hcell.trans hc, hext, hedge, hrefs⟩
    rsetOk := fun s cls u hrs => by
      obtain ⟨sv, hsv, hcase⟩ := pre.rsetOk s cls u hrs
      refine ⟨sv, hsv, ?_⟩
      rcases hcase with h0 | ⟨l, b, rfl, hc, hvc, hbf, hext, _, hrefs⟩
      · exact Or.inl h0
      · obtain ⟨hcell, hedge⟩ := hpriv l (Or.inr (Or.inl ⟨s, cls, u, hrs, hsv⟩))
        exact Or.inr ⟨l, b, rfl, hcell.trans hc, hvc, hbf, hext, hedge, hrefs⟩
    privBound := fun l hl => Nat.lt_of_lt_of_le (pre.privBound l hl) hr.1
    privNoEdge := fun l hl => (hpriv l (Or.inl hl)).2 }

/-! ## The fresh variable -/

theorem OwnedPre.fresh_facts (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} (hx : x ∉ live) :
    Γ.isImm x = false ∧ Γ.own.contains x = false ∧ Γ.brw.get? x = none ∧
      Γ.tokens x = 0 ∧ Γ.isPbrw x = false ∧ Γ.isUniq x = false ∧
      Γ.ctorOf.get? x = none ∧ Γ.projOf.get? x = none := by
  have hk : Γ.known x = false := by
    cases h : Γ.known x with
    | false => rfl
    | true => exact absurd (pre.known x h) hx
  simp only [Ctx.known_eq, Bool.or_eq_false_iff] at hk
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hk
  have htok0 : Γ.tokens x = 0 := by
    simp only [Src.NatMap.contains] at h2
    simp only [Ctx.tokens_eq]
    cases hg : Γ.own.get? x with
    | none => rfl
    | some n => rw [hg] at h2; cases h2
  have hun : Γ.isUniq x = false := by
    cases hu : Γ.isUniq x with
    | false => rfl
    | true =>
      obtain ⟨hmeta, _⟩ := pre.uniqOk x hu
      have h1' := (hmeta h1).1
      omega
  have hct : Γ.ctorOf.get? x = none := by
    cases hc : Γ.ctorOf.get? x with
    | none => rfl
    | some key => exact absurd (pre.ctorOfKnown x key hc) hx
  have hpr : Γ.projOf.get? x = none := by
    cases hp : Γ.projOf.get? x with
    | none => rfl
    | some p => exact absurd (pre.projOfKnown x p.1 p.2.1 p.2.2 hp).1 hx
  exact ⟨h1, h2, by simpa using h3, htok0, h4, hun, hct, hpr⟩

theorem OwnedPre.not_tok (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} (hx : x ∉ live) {toks : List Var} (htok : Ctx.Tokens Γ toks) : x ∉ toks := by
  intro hm
  exact hx (pre.known x (Tokens.mem_known htok hm))

/-- The state after a fresh binding, from what the step establishes for each variable. -/
theorem OwnedPre.extend (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} (hx : x ∉ live) {Γ' : Ctx} {H' : Heap} {v : RVal} {w : Fir.Val}
    {owned' : List RVal}
    (hden : ∀ y, y ≠ x → Γ'.avail y = true →
      ∃ v w, ρo.get? y = some v ∧ ρf.get? y = some w ∧ Proof.Den H' v w)
    (hdenx : Proof.Den H' v w)
    (hroots : ∃ toks, Ctx.Tokens Γ' toks ∧ EnvRoots (ρo.insert x v) toks owned')
    (hsroots : ∃ skeys, Ctx.SlotKeys Γ' skeys ∧ EnvRoots slots skeys slotVals)
    (hcounts : Balance H' external (owned' ++ slotVals))
    (hknown : ∀ y, Γ'.known y = true → y = x ∨ Γ.known y = true)
    (himm : ∀ y, y ≠ x → Γ'.isImm y = true → ∃ v, ρo.get? y = some v ∧ ImmVal v)
    (himmx : Γ'.isImm x = true → ImmVal v)
    (hbrw : ∀ y, y ≠ x → Γ'.borrowed y = true → ∃ v, ρo.get? y = some v ∧ BorrowVal H' v)
    (hbrwx : Γ'.borrowed x = true → BorrowVal H' v)
    (hpbrw : ∀ y, y ≠ x → Γ'.isPbrw y = true → ∃ v, ρo.get? y = some v ∧ ReachableFrom H' external v)
    (hpbrwx : Γ'.isPbrw x = true → ReachableFrom H' external v)
    (hpbrwSub : ∀ y, Γ.pbrw.contains y = true → Γ'.pbrw.contains y = true)
    (hepochs : ∀ y e, Γ'.brw.get? y = some e → e ≤ Γ'.epoch)
    (hctorK : Γ'.ctorOf = Γ.ctorOf)
    (hprojK : Γ'.projOf = Γ.projOf)
    (hctor : ∀ y key, y ≠ x → Γ'.avail y = true → Γ'.ctorOf.get? y = some key →
      ∃ v' fs, ρo.get? y = some v' ∧ v'.asCtor K H' = some (key, fs))
    (hproj : ∀ y z key idx, y ≠ x → z ≠ x → Γ'.avail z = true → Γ'.avail y = true →
      Γ'.projOf.get? y = some (z, key, idx) →
      ∃ vz fs uv, ρo.get? z = some vz ∧ vz.asCtor K H' = some (key, fs) ∧
        fs[idx]? = some uv ∧ ρo.get? y = some uv)
    (huniq : ∀ y, y ≠ x → Γ'.isUniq y = true →
      (Γ'.isImm y = false → Γ'.tokens y = 1 ∧ Γ'.isPbrw y = false) ∧
      ∃ v', ρo.get? y = some v' ∧ UniqVal ctors H' external (owned' ++ slotVals) v')
    (huniqx : Γ'.isUniq x = true →
      (Γ'.isImm x = false → Γ'.tokens x = 1 ∧ Γ'.isPbrw x = false) ∧
      UniqVal ctors H' external (owned' ++ slotVals) v)
    (hrset : ∀ s cls u, Γ'.rset.get? s = some (cls, u) →
      ∃ sv, slots.get? s = some sv ∧
        ((sv = .erased ∧ u = false) ∨
         (∃ l b, sv = .loc l ∧ H'.cell? l = some (.live 1 .dyn b) ∧
           Ctx.validReuseCtor b.ctor = some cls ∧ b.fields = List.replicate b.ctor.arity .erased ∧
           external l = 0 ∧ edgeCount H' l = 0 ∧ refsIn l (owned' ++ slotVals) = 1)))
    (hpBound : ∀ l, priv l → l < H'.size)
    (hpEdge : ∀ l, priv l → edgeCount H' l = 0)
    (hpVar : ∀ l, priv l → ∀ y, y ≠ x → Γ'.avail y = true → ρo.get? y ≠ some (.loc l))
    (hpVarx : ∀ l, priv l → v ≠ .loc l)
    (hpSlot : ∀ l, priv l → ∀ s, Γ'.rset.contains s = true → slots.get? s ≠ some (.loc l)) :
    OwnedState functions H' external (live ++ [x]) Γ' (ρf.insert x w) (ρo.insert x v) owned'
      lex Δ Jf Jo borrows uniqs retUniq ctors K priv slots slotVals := by
  obtain ⟨_, _, _, _, _, _, hctNone, hprNone⟩ := pre.fresh_facts hx
  refine ⟨fun y hy => ?_, hroots, hsroots, hcounts, fun y hy => ?_,
    fresh_nodup_append pre.distinct (by simp [fresh, hx]), fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_, hepochs,
    fun y key hc => List.mem_append_left _ (pre.ctorOfKnown y key (hctorK ▸ hc)),
    fun y z key idx hp =>
      let p := pre.projOfKnown y z key idx (hprojK ▸ hp)
      ⟨List.mem_append_left _ p.1, List.mem_append_left _ p.2⟩,
    fun y key hy hc => ?_, fun y z key idx hz hy hp => ?_,
    fun y hy => ?_, hrset, hpBound, hpEdge, fun l hl y hy => ?_, hpSlot,
    (pre.stack.mono_pbrw hpbrwSub).bind x v w hx, pre.scope.bind x⟩
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
  · by_cases he : y = x
    · subst he; rw [hctorK, hctNone] at hc; cases hc
    · obtain ⟨v', fs, h1, h2⟩ := hctor y key he hy hc
      exact ⟨v', fs, by rw [Src.NatMap.get?_insert_ne _ _ he]; exact h1, h2⟩
  · by_cases hey : y = x
    · subst hey; rw [hprojK, hprNone] at hp; cases hp
    · by_cases hez : z = x
      · subst hez; exact absurd (pre.projOfKnown y z key idx (hprojK ▸ hp)).2 hx
      · obtain ⟨vz, fs, uv, h1, h2, h3, h4⟩ := hproj y z key idx hey hez hz hy hp
        exact ⟨vz, fs, uv, by rw [Src.NatMap.get?_insert_ne _ _ hez]; exact h1, h2, h3,
          by rw [Src.NatMap.get?_insert_ne _ _ hey]; exact h4⟩
  · by_cases he : y = x
    · subst he
      obtain ⟨hmeta, hvu⟩ := huniqx hy
      exact ⟨hmeta, v, Src.NatMap.get?_insert_self .., hvu⟩
    · obtain ⟨hmeta, v', h1, h2⟩ := huniq y he hy
      exact ⟨hmeta, v', by rw [Src.NatMap.get?_insert_ne _ _ he]; exact h1, h2⟩
  · by_cases he : y = x
    · subst he
      rw [Src.NatMap.get?_insert_self]
      intro hEq; cases hEq; exact hpVarx l hl rfl
    · rw [Src.NatMap.get?_insert_ne _ _ he]
      exact hpVar l hl y he hy

private theorem uniqVal_cons_ne {v : RVal} {u : RVal}
    (h : UniqVal ctors H external (owned ++ slotVals) u)
    (hne : ∀ l, u = .loc l → v ≠ .loc l) :
    UniqVal ctors H external ((v :: owned) ++ slotVals) u := by
  cases u with
  | lit _ | erased => trivial
  | ctor0 c => exact h
  | loc l =>
    obtain ⟨b, hc, hext, hedge, hrefs⟩ := h
    have hv := hne l rfl
    refine ⟨b, hc, hext, hedge, ?_⟩
    simp only [List.cons_append, refsIn, hv, ↓reduceIte, Nat.zero_add]
    exact hrefs

theorem OwnedPre.bindOwned (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} (hx : x ∉ live) {v : RVal} {w : Fir.Val} (hd : Proof.Den H v w)
    (hb : Balance H external ((v :: owned) ++ slotVals))
    (hpv : ∀ l, pre.localPriv l → v ≠ .loc l) :
    OwnedState functions H external (live ++ [x]) (Γ.addOwn x 1) (ρf.insert x w)
      (ρo.insert x v) (v :: owned) lex Δ Jf Jo borrows uniqs retUniq ctors K priv slots slotVals := by
  obtain ⟨hi, _, hbx, _, hpbx, hunx, _, _⟩ := pre.fresh_facts hx
  obtain ⟨toks, htok, hr⟩ := pre.roots
  obtain ⟨skeys, hsk, hsr⟩ := pre.slotRoots
  have hxt := pre.not_tok hx htok
  have hav' : ∀ y, y ≠ x → (Γ.addOwn x 1).avail y = true → Γ.avail y = true := fun y he hy => by
    simp only [Ctx.avail_eq, Ctx.isImm_addOwn, Ctx.tokens_addOwn, ite_eq_right he, Ctx.borrowed_eq,
      Ctx.brw_addOwn, Ctx.epoch_addOwn, Ctx.isPbrw_addOwn] at hy ⊢
    exact hy
  refine pre.extend hx (fun y he hy => pre.den y (hav' y he hy)) hd
    ⟨x :: toks, htok.addOwn x, EnvRoots.cons (Src.NatMap.get?_insert_self ..)
      (hr.insert_fresh x v hxt)⟩ ⟨skeys, hsk.same rfl, hsr⟩ hb (fun y hy => ?_)
    (fun y _ hy => pre.immOk y (by simpa using hy)) (fun hy => by simp [hi] at hy)
    (fun y _ hy => pre.borrowed y (by simpa [Ctx.borrowed_eq] using hy))
    (fun hy => by simp [Ctx.borrowed_eq, hbx] at hy)
    (fun y _ hy => pre.pbrwOk y (by simpa using hy)) (fun hy => by simp [hpbx] at hy)
    (fun _ h => h) (fun y e hy => pre.epochs y e (by simpa using hy))
    rfl rfl
    (fun y key he hy hc => pre.ctorOfOk y key (hav' y he hy) hc)
    (fun y z key idx hey hez hz hy hp =>
      pre.projOfOk y z key idx (hav' z hez hz) (hav' y hey hy) hp)
    (fun y he hy => ?_) (fun hy => by simp [hunx] at hy)
    (fun s cls u hrs => ?_)
    pre.privBound pre.privNoEdge
    (fun l hl y he hy => pre.privNoVar l hl y (hav' y he hy))
    (fun l hl => hpv l (Or.inl hl)) pre.privNoSlot
  · simp only [Ctx.known_eq, Ctx.isImm_addOwn, Ctx.ownHas_addOwn, Ctx.brw_addOwn, Ctx.isPbrw_addOwn,
      Bool.or_eq_true, decide_eq_true_eq] at hy ⊢
    rcases hy with ((h | h | h) | h) | h
    · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr h)
  · obtain ⟨hmeta, u, hu, hvu⟩ := pre.uniqOk y hy
    refine ⟨fun hiy => by
      obtain ⟨ht1, hpb⟩ := hmeta hiy
      exact ⟨by rw [Ctx.tokens_addOwn, ite_eq_right he]; exact ht1, hpb⟩,
      u, hu, uniqVal_cons_ne hvu (fun l hEq => by
        subst hEq
        cases hiy : Γ.isImm y with
        | true =>
          obtain ⟨u', hu', himm⟩ := pre.immOk y hiy
          have : u' = .loc l := Option.some.inj (hu'.symm.trans hu); subst this
          exact absurd rfl (himm l)
        | false => exact hpv l (Or.inr (Or.inr ⟨y, hy, hiy, hu⟩)))⟩
  · obtain ⟨sv, hsv, hcase⟩ := pre.rsetOk s cls u hrs
    refine ⟨sv, hsv, ?_⟩
    rcases hcase with h0 | ⟨l, b, rfl, hc, hvc, hbf, hext, hedge, hrefs⟩
    · exact Or.inl h0
    · have hne : v ≠ .loc l := hpv l (Or.inr (Or.inl ⟨s, cls, u, hrs, hsv⟩))
      exact Or.inr ⟨l, b, rfl, hc, hvc, hbf, hext, hedge, by
        simp only [List.cons_append, refsIn, hne, ↓reduceIte, Nat.zero_add]; exact hrefs⟩

theorem OwnedPre.bindUniqOwned (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} (hx : x ∉ live) {v : RVal} {w : Fir.Val} (hd : Proof.Den H v w)
    (hb : Balance H external ((v :: owned) ++ slotVals))
    (hvU : UniqVal ctors H external ((v :: owned) ++ slotVals) v)
    (hpv : ∀ l, pre.localPriv l → v ≠ .loc l) :
    OwnedState functions H external (live ++ [x]) (Γ.addUniqOwn x) (ρf.insert x w)
      (ρo.insert x v) (v :: owned) lex Δ Jf Jo borrows uniqs retUniq ctors K priv slots slotVals := by
  have st := pre.bindOwned hx hd hb hpv
  obtain ⟨hi, _, _, ht0, hpbx, _, _, _⟩ := pre.fresh_facts hx
  obtain ⟨toks, htok, hr⟩ := st.roots
  obtain ⟨skeys, hsk, hsr⟩ := st.slotRoots
  refine { st with
    roots := ⟨toks, htok.same rfl rfl, hr⟩
    slotRoots := ⟨skeys, hsk.same rfl, hsr⟩
    uniqOk := fun y hy => ?_ }
  rw [Ctx.isUniq_addUniqOwn, Bool.or_eq_true, decide_eq_true_eq] at hy
  rcases hy with rfl | hy
  · refine ⟨fun _ => ⟨by simp [Ctx.tokens_addUniqOwn, ht0], hpbx⟩, v,
      Src.NatMap.get?_insert_self .., hvU⟩
  · by_cases he : y = x
    · subst he
      refine ⟨fun _ => ⟨by simp [Ctx.tokens_addUniqOwn, ht0], hpbx⟩, v,
        Src.NatMap.get?_insert_self .., hvU⟩
    · exact st.uniqOk y hy

theorem OwnedPre.bindImm (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} (hx : x ∉ live) {v : RVal} {w : Fir.Val} (hd : Proof.Den H v w) (himm : ImmVal v)
    (hb : Balance H external (owned ++ slotVals)) :
    OwnedState functions H external (live ++ [x]) (Γ.setImm x) (ρf.insert x w)
      (ρo.insert x v) owned lex Δ Jf Jo borrows uniqs retUniq ctors K priv slots slotVals := by
  obtain ⟨_, _, hbx, _, hpbx, _, _, _⟩ := pre.fresh_facts hx
  obtain ⟨toks, htok, hr⟩ := pre.roots
  obtain ⟨skeys, hsk, hsr⟩ := pre.slotRoots
  have hxt := pre.not_tok hx htok
  have hf : toks.filter (fun y => y != x) = toks :=
    List.filter_eq_self.mpr (fun a ha => by
      have : a ≠ x := fun he => hxt (he ▸ ha)
      simpa using this)
  have htok' := htok.setImm x
  rw [hf] at htok'
  have hav' : ∀ y, y ≠ x → (Γ.setImm x).avail y = true → Γ.avail y = true := fun y he hy => by
    simp only [Ctx.avail_eq, Ctx.isImm_setImm, Ctx.tokens_setImm, Ctx.borrowed_eq,
      Ctx.brw_setImm, Ctx.epoch_setImm, Ctx.isPbrw_setImm, he, decide_false, Bool.false_or,
      ↓reduceIte] at hy ⊢
    exact hy
  refine pre.extend hx (fun y he hy => pre.den y (hav' y he hy)) hd
    ⟨toks, htok', hr.insert_fresh x v hxt⟩ ⟨skeys, hsk.same rfl, hsr⟩ hb (fun y hy => ?_)
    (fun y he hy => pre.immOk y (by simpa [Ctx.isImm_setImm, he] using hy)) (fun _ => himm)
    (fun y he hy => pre.borrowed y (by simpa [Ctx.borrowed_eq, Ctx.brw_setImm, he] using hy))
    (fun hy => by simp [Ctx.borrowed_eq, Ctx.brw_setImm] at hy)
    (fun y _ hy => pre.pbrwOk y (by simpa using hy)) (fun hy => by simp [hpbx] at hy)
    (fun _ h => h) (fun y e hy => ?_)
    rfl rfl
    (fun y key he hy hc => pre.ctorOfOk y key (hav' y he hy) hc)
    (fun y z key idx hey hez hz hy hp =>
      pre.projOfOk y z key idx (hav' z hez hz) (hav' y hey hy) hp)
    (fun y he hy => ?_) (fun hy => by simp [Ctx.isUniq_setImm] at hy)
    pre.rsetOk pre.privBound pre.privNoEdge
    (fun l hl y he hy => pre.privNoVar l hl y (hav' y he hy))
    (fun l _ hEq => himm l hEq) pre.privNoSlot
  · simp only [Ctx.known_eq, Ctx.isImm_setImm, Ctx.ownHas_setImm, Ctx.brw_setImm, Ctx.isPbrw_setImm,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hy ⊢
    by_cases he : y = x
    · exact Or.inl he
    · right
      simp only [he, decide_false, Bool.not_false, true_and, false_or, ↓reduceIte] at hy
      exact hy
  · simp only [Ctx.brw_setImm] at hy
    split at hy
    · cases hy
    · exact pre.epochs y e hy
  · rw [Ctx.isUniq_setImm, Bool.and_eq_true] at hy
    obtain ⟨hmeta, u, hu, hvu⟩ := pre.uniqOk y hy.2
    refine ⟨fun hiy => ?_, u, hu, hvu⟩
    have hiy0 : Γ.isImm y = false := by simpa [Ctx.isImm_setImm, he] using hiy
    obtain ⟨ht1, hpb⟩ := hmeta hiy0
    exact ⟨by simp [Ctx.tokens_setImm, he, ht1], hpb⟩

theorem OwnedPre.bindImmUniq (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} (hx : x ∉ live) {v : RVal} {w : Fir.Val} (hd : Proof.Den H v w)
    (himm : ImmUniq ctors v) (hb : Balance H external (owned ++ slotVals)) :
    OwnedState functions H external (live ++ [x]) (Γ.setImmUniq x) (ρf.insert x w)
      (ρo.insert x v) owned lex Δ Jf Jo borrows uniqs retUniq ctors K priv slots slotVals := by
  have st := pre.bindImm hx hd himm.1 hb
  obtain ⟨toks, htok, hr⟩ := st.roots
  obtain ⟨skeys, hsk, hsr⟩ := st.slotRoots
  refine { st with
    roots := ⟨toks, htok.same rfl rfl, hr⟩
    slotRoots := ⟨skeys, hsk.same rfl, hsr⟩
    uniqOk := fun y hy => ?_ }
  rw [Ctx.isUniq_setImmUniq, Bool.or_eq_true, decide_eq_true_eq] at hy
  rcases hy with rfl | hy
  · refine ⟨fun hc => by simp [Ctx.isImm_setImmUniq] at hc, v,
      Src.NatMap.get?_insert_self .., himm.toUniqVal⟩
  · by_cases he : y = x
    · subst he
      refine ⟨fun hc => by simp [Ctx.isImm_setImmUniq] at hc, v,
        Src.NatMap.get?_insert_self .., himm.toUniqVal⟩
    · exact st.uniqOk y (by simp [Ctx.isUniq_setImm, he, hy])

theorem OwnedPre.bindBorrow (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} (hx : x ∉ live) {v : RVal} {w : Fir.Val} (hd : Proof.Den H v w)
    (hbrw : BorrowVal H v) (hb : Balance H external (owned ++ slotVals)) :
    OwnedState functions H external (live ++ [x]) (Γ.setBorrow x) (ρf.insert x w)
      (ρo.insert x v) owned lex Δ Jf Jo borrows uniqs retUniq ctors K priv slots slotVals := by
  obtain ⟨hi, _, _, _, hpbx, hunx, _, _⟩ := pre.fresh_facts hx
  obtain ⟨toks, htok, hr⟩ := pre.roots
  obtain ⟨skeys, hsk, hsr⟩ := pre.slotRoots
  have hxt := pre.not_tok hx htok
  have hav' : ∀ y, y ≠ x → (Γ.setBorrow x).avail y = true → Γ.avail y = true := fun y he hy => by
    simp only [Ctx.avail_eq, Ctx.isImm_setBorrow, Ctx.tokens_setBorrow, Ctx.borrowed_eq,
      Ctx.brw_setBorrow, Ctx.epoch_setBorrow, Ctx.isPbrw_setBorrow, he, ↓reduceIte] at hy ⊢
    exact hy
  refine pre.extend hx (fun y he hy => pre.den y (hav' y he hy)) hd
    ⟨toks, htok.same rfl rfl, hr.insert_fresh x v hxt⟩ ⟨skeys, hsk.same rfl, hsr⟩ hb (fun y hy => ?_)
    (fun y _ hy => pre.immOk y (by simpa using hy)) (fun hy => by simp [hi] at hy)
    (fun y he hy => pre.borrowed y (by simpa [Ctx.borrowed_eq, Ctx.brw_setBorrow, he] using hy))
    (fun _ => hbrw)
    (fun y _ hy => pre.pbrwOk y (by simpa using hy)) (fun hy => by simp [hpbx] at hy)
    (fun _ h => h) (fun y e hy => ?_)
    rfl rfl
    (fun y key he hy hc => pre.ctorOfOk y key (hav' y he hy) hc)
    (fun y z key idx hey hez hz hy hp =>
      pre.projOfOk y z key idx (hav' z hez hz) (hav' y hey hy) hp)
    (fun y _ hy => pre.uniqOk y hy) (fun hy => by simp [hunx] at hy)
    pre.rsetOk pre.privBound pre.privNoEdge
    (fun l hl y he hy => pre.privNoVar l hl y (hav' y he hy))
    (fun l hl hEq => by
      subst hEq; change 0 < edgeCount H l at hbrw; have := pre.privNoEdge l hl; omega)
    pre.privNoSlot
  · simp only [Ctx.known_eq, Ctx.isImm_setBorrow, Ctx.own_setBorrow, Ctx.brw_setBorrow,
      Ctx.isPbrw_setBorrow, Bool.or_eq_true] at hy ⊢
    by_cases he : y = x
    · exact Or.inl he
    · right; simp only [he, ↓reduceIte] at hy; exact hy
  · simp only [Ctx.brw_setBorrow] at hy
    split at hy
    · cases hy; exact Nat.le_refl _
    · exact pre.epochs y e hy

theorem OwnedPre.bindPbrw (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} (hx : x ∉ live) {v : RVal} {w : Fir.Val} (hd : Proof.Den H v w)
    (hreach : ReachableFrom H external v) (hb : Balance H external (owned ++ slotVals))
    (hpv : ∀ l, priv l → v ≠ .loc l) :
    OwnedState functions H external (live ++ [x]) (Γ.setPbrw x) (ρf.insert x w)
      (ρo.insert x v) owned lex Δ Jf Jo borrows uniqs retUniq ctors K priv slots slotVals := by
  obtain ⟨hi, _, hbx, _, _, hunx, _, _⟩ := pre.fresh_facts hx
  obtain ⟨toks, htok, hr⟩ := pre.roots
  obtain ⟨skeys, hsk, hsr⟩ := pre.slotRoots
  have hxt := pre.not_tok hx htok
  have hav' : ∀ y, y ≠ x → (Γ.setPbrw x).avail y = true → Γ.avail y = true := fun y he hy => by
    simp only [Ctx.avail_eq, Ctx.isImm_setPbrw, Ctx.tokens_setPbrw, Ctx.borrowed_eq,
      Ctx.brw_setPbrw, Ctx.epoch_setPbrw, Ctx.isPbrw_setPbrw, he, decide_false, Bool.false_or] at hy ⊢
    exact hy
  refine pre.extend hx (fun y he hy => pre.den y (hav' y he hy)) hd
    ⟨toks, htok.same rfl rfl, hr.insert_fresh x v hxt⟩ ⟨skeys, hsk.same rfl, hsr⟩ hb (fun y hy => ?_)
    (fun y _ hy => pre.immOk y (by simpa using hy)) (fun hy => by simp [hi] at hy)
    (fun y _ hy => pre.borrowed y (by simpa [Ctx.borrowed_eq] using hy))
    (fun hy => by simp [Ctx.borrowed_eq, hbx] at hy)
    (fun y he hy => pre.pbrwOk y (by simpa [Ctx.isPbrw_setPbrw, he] using hy))
    (fun _ => hreach)
    (fun y hy => by
      change (Γ.setPbrw x).isPbrw y = true
      rw [Ctx.isPbrw_setPbrw]; exact Bool.or_eq_true_iff.mpr (Or.inr hy))
    (fun y e hy => pre.epochs y e hy)
    rfl rfl
    (fun y key he hy hc => pre.ctorOfOk y key (hav' y he hy) hc)
    (fun y z key idx hey hez hz hy hp =>
      pre.projOfOk y z key idx (hav' z hez hz) (hav' y hey hy) hp)
    (fun y he hy => by
      obtain ⟨hmeta, u, hu, hvu⟩ := pre.uniqOk y hy
      exact ⟨fun hiy => ⟨(hmeta hiy).1, by simp [Ctx.isPbrw_setPbrw, he, (hmeta hiy).2]⟩,
        u, hu, hvu⟩)
    (fun hy => by simp [hunx] at hy)
    pre.rsetOk pre.privBound pre.privNoEdge
    (fun l hl y he hy => pre.privNoVar l hl y (hav' y he hy))
    hpv pre.privNoSlot
  · simp only [Ctx.known_eq, Ctx.isImm_setPbrw, Ctx.own_setPbrw, Ctx.brw_setPbrw, Ctx.isPbrw_setPbrw,
      Bool.or_eq_true, decide_eq_true_eq] at hy ⊢
    by_cases he : y = x
    · exact Or.inl he
    · right; simp only [he, false_or] at hy; exact hy

/-- Record a constructor key witnessed by `case` on `x`. -/
theorem OwnedState.setCtor (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x : Var} {key : Key.CtorKey} {vx : RVal} {fs : List RVal}
    (hx : x ∈ live) (hvx : ρo.get? x = some vx) (hac : vx.asCtor K H = some (key, fs)) :
    OwnedState functions H external live (Γ.setCtor x key) ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq ctors K priv slots slotVals := by
  obtain ⟨toks, htok, hr⟩ := st.roots
  obtain ⟨skeys, hsk, hsr⟩ := st.slotRoots
  refine { st with
    roots := ⟨toks, htok.same rfl rfl, hr⟩
    slotRoots := ⟨skeys, hsk.same rfl, hsr⟩
    ctorOfKnown := fun y key' hc => by
      rw [Ctx.ctorOf_setCtor] at hc
      split at hc
      · next he => subst he; exact hx
      · exact st.ctorOfKnown y key' hc
    ctorOfOk := fun y key' hy hc => by
      rw [Ctx.ctorOf_setCtor] at hc
      split at hc
      · next he => subst he; cases hc; exact ⟨vx, fs, hvx, hac⟩
      · exact st.ctorOfOk y key' hy hc }

/-- Record a projection `(y, key, idx)` on `x`. -/
theorem OwnedState.setProj (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {x y : Var} {key : Key.CtorKey} {idx : Nat} {vy uv : RVal} {fs : List RVal}
    (hx : x ∈ live) (hy : y ∈ live)
    (hvy : ρo.get? y = some vy) (hac : vy.asCtor K H = some (key, fs))
    (hget : fs[idx]? = some uv) (huv : ρo.get? x = some uv) :
    OwnedState functions H external live (Γ.setProj x y key idx) ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq ctors K priv slots slotVals := by
  obtain ⟨toks, htok, hr⟩ := st.roots
  obtain ⟨skeys, hsk, hsr⟩ := st.slotRoots
  refine { st with
    roots := ⟨toks, htok.same rfl rfl, hr⟩
    slotRoots := ⟨skeys, hsk.same rfl, hsr⟩
    projOfKnown := fun v z key' idx' hp => by
      rw [Ctx.projOf_setProj] at hp
      split at hp
      · next he => subst he; cases hp; exact ⟨hx, hy⟩
      · exact st.projOfKnown v z key' idx' hp
    projOfOk := fun v z key' idx' hz hv hp => by
      rw [Ctx.projOf_setProj] at hp
      split at hp
      · next he => subst he; cases hp; exact ⟨vy, fs, uv, hvy, hac, hget, huv⟩
      · exact st.projOfOk v z key' idx' hz hv hp }

/-- A variable whose value is a valid immediate becomes one (`setImmUniq`); its tokens were vacuous. -/
theorem OwnedPre.setImmUniqVar (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {y : Var} (hy : Γ.avail y = true) {u : RVal} (hu : ρo.get? y = some u) (himm : ImmUniq ctors u) :
    ∃ owned', OwnedPre functions H external live (Γ.setImmUniq y) ρf ρo owned' lex Δ Jf Jo
      borrows uniqs retUniq ctors K priv slots slotVals ∧ SameRefs owned owned' := by
  obtain ⟨toks, htok, hr⟩ := pre.roots
  obtain ⟨skeys, hsk, hsr⟩ := pre.slotRoots
  obtain ⟨owned', hr', hs⟩ := EnvRoots.filter_imm hu himm.1 hr
  have hav' : ∀ z, (Γ.setImmUniq y).avail z = true → Γ.avail z = true := fun z hz => by
    by_cases he : z = y
    · subst he; exact hy
    · simp only [Ctx.avail_eq, Ctx.isImm_setImmUniq, Ctx.tokens_setImmUniq, Ctx.borrowed_eq,
        Ctx.brw_setImmUniq, Ctx.epoch_setImmUniq, Ctx.isPbrw_setImmUniq, he, decide_false,
        Bool.false_or, ↓reduceIte] at hz ⊢
      exact hz
  refine ⟨owned', ⟨fun z hz => pre.den z (hav' z hz), ⟨_, htok.setImmUniq y, hr'⟩,
    ⟨skeys, hsk.same rfl, hsr⟩,
    fun z hz => pre.known z ?_, pre.distinct, fun z hz => ?_, fun z hz => pre.borrowed z ?_,
    fun z hz => pre.pbrwOk z (by simpa using hz), fun z e hz => ?_,
    pre.ctorOfKnown, pre.projOfKnown,
    fun z key hz hc => pre.ctorOfOk z key (hav' z hz) hc,
    fun v z key idx hz hv hp => pre.projOfOk v z key idx (hav' z hz) (hav' v hv) hp,
    fun z hz => ?_, fun s cls u' hrs => ?_,
    pre.privBound, pre.privNoEdge,
    fun l hl z hz => pre.privNoVar l hl z (hav' z hz), pre.privNoSlot,
    pre.stack, pre.scope⟩, hs⟩
  · by_cases he : z = y
    · subst he; exact Ctx.avail_known hy
    · simp only [Ctx.known_eq, Ctx.isImm_setImmUniq, Ctx.ownHas_setImmUniq, Ctx.brw_setImmUniq,
        Ctx.isPbrw_setImmUniq, he, decide_false, Bool.false_or, Bool.not_false, Bool.true_and,
        ↓reduceIte] at hz ⊢
      exact hz
  · by_cases he : z = y
    · subst he; exact ⟨u, hu, himm.1⟩
    · exact pre.immOk z (by simpa [Ctx.isImm_setImmUniq, he] using hz)
  · by_cases he : z = y
    · subst he; simp [Ctx.borrowed_eq, Ctx.brw_setImmUniq] at hz
    · simpa [Ctx.borrowed_eq, Ctx.brw_setImmUniq, he] using hz
  · simp only [Ctx.brw_setImmUniq] at hz
    split at hz
    · cases hz
    · exact pre.epochs z e hz
  · rw [Ctx.isUniq_setImmUniq, Bool.or_eq_true, decide_eq_true_eq] at hz
    rcases hz with rfl | hz
    · exact ⟨fun hc => by simp [Ctx.isImm_setImmUniq] at hc, u, hu, himm.toUniqVal⟩
    · by_cases he : z = y
      · subst he
        exact ⟨fun hc => by simp [Ctx.isImm_setImmUniq] at hc, u, hu, himm.toUniqVal⟩
      · obtain ⟨hmeta, v', hv', hvu⟩ := pre.uniqOk z hz
        refine ⟨fun hiz => ?_, v', hv', hvu.sameRefs (fun k => by simp [refsIn_append, hs k])⟩
        have hiz0 : Γ.isImm z = false := by simpa [Ctx.isImm_setImmUniq, he] using hiz
        obtain ⟨ht1, hpb⟩ := hmeta hiz0
        exact ⟨by simp [Ctx.tokens_setImmUniq, he, ht1], hpb⟩
  · obtain ⟨sv, hsv, hcase⟩ := pre.rsetOk s cls u' hrs
    refine ⟨sv, hsv, ?_⟩
    rcases hcase with h0 | ⟨l, b, rfl, hc, hvc, hbf, hext, hedge, hrefs⟩
    · exact Or.inl h0
    · exact Or.inr ⟨l, b, rfl, hc, hvc, hbf, hext, hedge, by
        simp only [refsIn_append, ← hs l] at hrefs ⊢; exact hrefs⟩

theorem Ctx.avail_setImmUniq {Γ : Ctx} {y z : Var} (h : Γ.avail y = true) :
    (Γ.setImmUniq z).avail y = true := by
  by_cases he : y = z
  · subst he; simp [Ctx.avail_eq, Ctx.isImm_setImmUniq]
  · simp only [Ctx.avail_eq, Ctx.isImm_setImmUniq, Ctx.tokens_setImmUniq, Ctx.borrowed_eq,
      Ctx.brw_setImmUniq, Ctx.epoch_setImmUniq, Ctx.isPbrw_setImmUniq, he, decide_false,
      Bool.false_or, ↓reduceIte] at h ⊢
    exact h

/-- A primitive's marked arguments become valid immediates (their values are `.lit (.nat _)`). -/
theorem OwnedPre.immArgs :
    ∀ (ms : List Bool) (args : List Arg) {Γ : Ctx} {owned : List RVal},
      OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
        borrows uniqs retUniq ctors K priv slots slotVals →
      (∀ y, Arg.var y ∈ args → Γ.avail y = true ∧ ∃ u, ρo.get? y = some u ∧ ImmUniq ctors u) →
      ∃ owned', OwnedPre functions H external live (Γ.immArgs ms args) ρf ρo owned' lex Δ Jf Jo
        borrows uniqs retUniq ctors K priv slots slotVals ∧ SameRefs owned owned'
  | true :: ms, .var y :: as, Γ, owned, pre, hargs => by
    obtain ⟨hy, u, hu, himm⟩ := hargs y List.mem_cons_self
    obtain ⟨owned₁, pre₁, hs₁⟩ := pre.setImmUniqVar hy hu himm
    obtain ⟨owned', pre', hs'⟩ := OwnedPre.immArgs ms as pre₁ (fun z hz => by
      obtain ⟨hz', rest⟩ := hargs z (List.mem_cons_of_mem _ hz)
      exact ⟨Ctx.avail_setImmUniq hz', rest⟩)
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

/-- **The arguments a signature marks `imm` become valid immediates**, given that the value of
each is one: position by position, so an argument the signature only reads, or consumes, is
asked nothing. (`OwnedPre.immArgs` above is the same for a mask and asks it of every argument;
it remains for the `Cfg.Rc` bridge.) -/
theorem OwnedPre.markImm :
    ∀ (us : List ArgUse) (args : List Arg) {Γ : Ctx} {owned : List RVal},
      OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
        borrows uniqs retUniq ctors K priv slots slotVals →
      (∀ (i : Nat) (y : Var), us[i]? = some ArgUse.imm → args[i]? = some (Arg.var y) →
        Γ.avail y = true ∧ ∃ u, ρo.get? y = some u ∧ ImmUniq ctors u) →
      ∃ owned', OwnedPre functions H external live (Plain.markImm Γ us args) ρf ρo owned' lex Δ
        Jf Jo borrows uniqs retUniq ctors K priv slots slotVals ∧ SameRefs owned owned'
  | [], args, Γ, owned, pre, _ => by
    have hΓ : Plain.markImm Γ [] args = Γ := by cases args <;> rfl
    refine ⟨owned, ?_, SameRefs.refl _⟩
    rw [hΓ]; exact pre
  | u :: us, [], Γ, owned, pre, _ => by
    have hΓ : Plain.markImm Γ (u :: us) [] = Γ := by cases u <;> rfl
    refine ⟨owned, ?_, SameRefs.refl _⟩
    rw [hΓ]; exact pre
  | u :: us, a :: as, Γ, owned, pre, hargs => by
    by_cases hm : u = .imm ∧ ∃ y, a = .var y
    · obtain ⟨rfl, y, rfl⟩ := hm
      obtain ⟨hy, v, hv, himm⟩ := hargs 0 y rfl rfl
      obtain ⟨owned₁, pre₁, hs₁⟩ := pre.setImmUniqVar hy hv himm
      obtain ⟨owned', pre', hs'⟩ := OwnedPre.markImm us as pre₁ (fun i z hi hz => by
        obtain ⟨hz', rest⟩ := hargs (i + 1) z (by simpa using hi) (by simpa using hz)
        exact ⟨Ctx.avail_setImmUniq hz', rest⟩)
      exact ⟨owned', pre', hs₁.trans hs'⟩
    · have hstep : Plain.markImm Γ (u :: us) (a :: as) = Plain.markImm Γ us as := by
        cases u <;> cases a <;> first | rfl | exact absurd ⟨rfl, _, rfl⟩ hm
      obtain ⟨owned', pre', hs'⟩ := OwnedPre.markImm us as pre (fun i z hi hz =>
        hargs (i + 1) z (by simpa using hi) (by simpa using hz))
      refine ⟨owned', ?_, hs'⟩
      rw [hstep]; exact pre'

/-- A release where the signature has one: nothing stays epoch-borrowed. -/
theorem OwnedPre.releaseIf (pre : OwnedPre functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals) (release : Bool) :
    OwnedPre functions H external live (if release then Γ.release else Γ) ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq ctors K priv slots slotVals := by
  cases release <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact pre
  · exact pre.release

end

end IxCC.Own.Plain
