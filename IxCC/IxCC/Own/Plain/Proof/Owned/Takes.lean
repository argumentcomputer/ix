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
    {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry} {borrows : BorrowSigs}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows) :
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

/-- Owned argument values selected by borrow mask `bs`. -/
def selectOwnedVals (bs : List Bool) (vs : List RVal) : List RVal :=
  match vs with
  | [] => []
  | v :: vs =>
    match bs with
    | [] => v :: vs
    | true :: bs => selectOwnedVals bs vs
    | false :: bs => v :: selectOwnedVals bs vs
termination_by structural vs

/-- Borrowed argument values selected by borrow mask `bs`. -/
def selectBorrowedVals (bs : List Bool) (vs : List RVal) : List RVal :=
  match vs with
  | [] => []
  | v :: vs =>
    match bs with
    | [] => []
    | true :: bs => v :: selectBorrowedVals bs vs
    | false :: bs => selectBorrowedVals bs vs
termination_by structural vs

@[simp] theorem selectOwnedVals_nil_right (bs : List Bool) : selectOwnedVals bs [] = [] := rfl
@[simp] theorem selectOwnedVals_nil_left (vs : List RVal) : selectOwnedVals [] vs = vs := by
  cases vs <;> rfl
@[simp] theorem selectBorrowedVals_nil_right (bs : List Bool) : selectBorrowedVals bs [] = [] := rfl
@[simp] theorem selectBorrowedVals_nil_left (vs : List RVal) : selectBorrowedVals [] vs = [] := by
  cases vs <;> rfl

theorem selectOwnedVals_all_false : ∀ (bs : List Bool) (vs : List RVal),
    bs.all (!·) = true → selectOwnedVals bs vs = vs
  | _, [], _ => rfl
  | [], _ :: _, _ => rfl
  | b :: bs, v :: vs, h => by
    cases b
    · simp only [selectOwnedVals]; congr 1; exact selectOwnedVals_all_false bs vs (by simpa using h)
    · simp at h

theorem selectBorrowedVals_all_false : ∀ (bs : List Bool) (vs : List RVal),
    bs.all (!·) = true → selectBorrowedVals bs vs = []
  | _, [], _ => rfl
  | [], _ :: _, _ => rfl
  | b :: bs, _ :: vs, h => by
    cases b
    · simp only [selectBorrowedVals]; exact selectBorrowedVals_all_false bs vs (by simpa using h)
    · simp at h

/-- Every variable passed in a borrowed position satisfies `P`. -/
def BorrowedSatisfies (P : Var → Prop) (bs : List Bool) (args : List Arg) : Prop :=
  match args with
  | [] => True
  | a :: as =>
    match bs with
    | [] => True
    | false :: bs => BorrowedSatisfies P bs as
    | true :: bs =>
      match a with
      | .var x => P x ∧ BorrowedSatisfies P bs as
      | _ => BorrowedSatisfies P bs as
termination_by structural args

theorem checkCallBorrowed_ok {Γ : Ctx} {bs : List Bool} {args : List Arg}
    (h : Γ.checkCallBorrowed bs args = .ok ()) :
    BorrowedSatisfies (fun x => Γ.borrowable x = true) bs args := by
  induction args generalizing bs with
  | nil => trivial
  | cons a as ih =>
    cases bs with
    | nil => trivial
    | cons b bs =>
      cases b with
      | false =>
        simp only [Ctx.checkCallBorrowed] at h
        exact ih h
      | true =>
        cases a with
        | lit _ => exact ih h
        | erased => exact ih h
        | var x =>
          simp only [Ctx.checkCallBorrowed] at h
          cases hb : Γ.borrowable x with
          | false =>
            simp [hb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
          | true =>
            simp only [hb, ↓reduceIte] at h
            exact ⟨hb, ih h⟩

theorem checkTailBorrowed_ok {Γ : Ctx} {bs : List Bool} {args : List Arg}
    (h : Γ.checkTailBorrowed bs args = .ok ()) :
    BorrowedSatisfies (fun x => Γ.isImm x = true ∨ Γ.isPbrw x = true) bs args := by
  induction args generalizing bs with
  | nil => trivial
  | cons a as ih =>
    cases bs with
    | nil => trivial
    | cons b bs =>
      cases b with
      | false =>
        simp only [Ctx.checkTailBorrowed] at h
        exact ih h
      | true =>
        cases a with
        | lit _ => exact ih h
        | erased => exact ih h
        | var x =>
          simp only [Ctx.checkTailBorrowed] at h
          cases hb : (Γ.isImm x || Γ.isPbrw x) with
          | false =>
            simp [hb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
          | true =>
            simp only [hb, ↓reduceIte] at h
            exact ⟨Bool.or_eq_true_iff.mp hb, ih h⟩

theorem takeOwnedArgs_sem_gen {H : Heap} {ρf : Fir.Env} {ρo : Own.Env}
    {P : Var → Prop} {Q : RVal → Prop}
    (hQimm : ∀ v, ImmVal v → Q v) {Γ Γ' : Ctx} {owned : List RVal} {bs : List Bool}
    {args : List Arg} (h : TakeInv H Γ ρf ρo owned) (ht : Γ.takeOwnedArgs bs args = .ok Γ')
    (hbs : BorrowedSatisfies P bs args)
    (hP : ∀ x, P x → Γ'.avail x = true ∧ ∀ v, ρo.get? x = some v → Q v) :
    ∃ vs ws owned', Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
      Sem.Forall2 (Proof.Den H) vs ws ∧ TakeInv H Γ' ρf ρo owned' ∧
      SameRefs owned (selectOwnedVals bs vs ++ owned') ∧ Ctx.Weaker Γ' Γ ∧
      ∀ v, v ∈ selectBorrowedVals bs vs → Q v := by
  induction args generalizing Γ owned bs with
  | nil =>
    cases ht
    exact ⟨[], [], owned, rfl, rfl, .nil, h, SameRefs.refl _, Ctx.Weaker.refl _,
      fun _ hm => by cases hm⟩
  | cons a as ih =>
    cases bs with
    | nil =>
      rw [Ctx.takeOwnedArgs_nil] at ht
      obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw'⟩ := takeArgs_sem h ht
      refine ⟨vs, ws, owned', hvs, hws, hds, h', by simpa using hs', hw', fun _ hm => ?_⟩
      simp at hm
    | cons b bs =>
      cases b with
      | false =>
        simp only [Ctx.takeOwnedArgs] at ht
        cases ha : Γ.takeArg a with
        | error e => rw [ha] at ht; cases ht
        | ok Γ₁ =>
          rw [ha] at ht
          obtain ⟨v, w, owned₁, hv, hw, hd, h₁, hs₁, hw₁⟩ := takeArg_sem h ha
          have hbs' : BorrowedSatisfies P bs as := by simpa [BorrowedSatisfies] using hbs
          obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ'⟩ := ih h₁ ht hbs'
          refine ⟨v :: vs, w :: ws, owned', ?_, ?_, .cons hd hds, h', ?_, hw'.trans hw₁, hQ'⟩
          · simp [Own.evalArgs, hv, hvs]
          · simp [Fir.evalArgs, hw, hws]
          · exact hs₁.trans (SameRefs.cons v hs')
      | true =>
        simp only [Ctx.takeOwnedArgs] at ht
        have hweak := Ctx.takeOwnedArgs_weaker ht
        cases a with
        | var x =>
          obtain ⟨hPx, hbs'⟩ := hbs
          obtain ⟨hav', hQx⟩ := hP x hPx
          obtain ⟨v, w, hv, hw, hd⟩ := h.den x (hweak.avail hav')
          obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ'⟩ := ih h ht hbs'
          refine ⟨v :: vs, w :: ws, owned', ?_, ?_, .cons hd hds, h', hs', hw', ?_⟩
          · simp [Own.evalArgs, Own.evalArg, hv, hvs]
          · simp [Fir.evalArgs, Fir.Arg.eval, hw, hws]
          · intro u hu
            simp only [selectBorrowedVals, List.mem_cons] at hu
            rcases hu with hEq | hu
            · rw [hEq]; exact hQx v hv
            · exact hQ' u hu
        | lit l =>
          obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ'⟩ := ih h ht hbs
          refine ⟨.lit l :: vs, .lit l :: ws, owned', ?_, ?_, .cons (Proof.den_lit H l) hds,
            h', hs', hw', ?_⟩
          · simp [Own.evalArgs, Own.evalArg, hvs]
          · simp [Fir.evalArgs, Fir.Arg.eval, hws]
          · intro u hu
            simp only [selectBorrowedVals, List.mem_cons] at hu
            rcases hu with rfl | hu
            · exact hQimm _ (fun _ h => by cases h)
            · exact hQ' u hu
        | erased =>
          obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ'⟩ := ih h ht hbs
          refine ⟨.erased :: vs, .erased :: ws, owned', ?_, ?_, .cons (Proof.den_erased H) hds,
            h', hs', hw', ?_⟩
          · simp [Own.evalArgs, Own.evalArg, hvs]
          · simp [Fir.evalArgs, Fir.Arg.eval, hws]
          · intro u hu
            simp only [selectBorrowedVals, List.mem_cons] at hu
            rcases hu with rfl | hu
            · exact hQimm _ (fun _ h => by cases h)
            · exact hQ' u hu

theorem takeOwnedArgs_call_sem {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ Γ' : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal}
    {lex : Joins} {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry} {borrows : BorrowSigs}
    {bs : List Bool} {args : List Arg}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    (ht : Γ.takeOwnedArgs bs args = .ok Γ') (hchk : Γ'.checkCallBorrowed bs args = .ok ()) :
    ∃ vs ws owned', Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
      Sem.Forall2 (Proof.Den H) vs ws ∧ TakeInv H Γ' ρf ρo owned' ∧
      SameRefs owned (selectOwnedVals bs vs ++ owned') ∧ Ctx.Weaker Γ' Γ ∧
      ∀ v, v ∈ selectBorrowedVals bs vs → ReachableFrom H (holdRoots external owned') v := by
  have hbs := checkCallBorrowed_ok hchk
  have hweak := Ctx.takeOwnedArgs_weaker ht
  have hP1 : ∀ x, Γ'.borrowable x = true → Γ'.avail x = true ∧ ∀ v, ρo.get? x = some v → True := by
    intro x hx
    refine ⟨?_, fun _ _ => trivial⟩
    simp only [Ctx.borrowable_eq, Ctx.avail_eq, Bool.or_eq_true, decide_eq_true_eq] at hx ⊢
    rcases hx with (h1 | h2) | h3
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inr h2
    · exact Or.inl (Or.inl (Or.inr h3))
  obtain ⟨vs, ws, owned', hvs, hws, hds, inv', hs', hw', _⟩ :=
    takeOwnedArgs_sem_gen (P := fun x => Γ'.borrowable x = true) (Q := fun _ => True)
      (fun _ _ => trivial) st.takeInv ht hbs hP1
  refine ⟨vs, ws, owned', hvs, hws, hds, inv', hs', hw', ?_⟩
  have hQ : ∀ x, Γ'.borrowable x = true → ∀ v, ρo.get? x = some v →
      ReachableFrom H (holdRoots external owned') v := by
    intro x hx v hv
    simp only [Ctx.borrowable_eq, Bool.or_eq_true, decide_eq_true_eq] at hx
    rcases hx with (hi | hp) | hpos
    · obtain ⟨u, hu, himm⟩ := inv'.immOk x hi
      have : u = v := Option.some.inj (hu.symm.trans hv); subst this
      exact .imm himm
    · have hp0 : Γ.isPbrw x = true := by rw [← hw'.isPbrw x]; exact hp
      obtain ⟨u, hu, hreach⟩ := st.pbrwOk x hp0
      have : u = v := Option.some.inj (hu.symm.trans hv); subst this
      exact hreach.mono_ext (fun l => by simp [holdRoots])
    · obtain ⟨toks', htok', hroots'⟩ := inv'.roots
      have hmem := hroots'.member (htok'.mem hpos) hv
      cases v with
      | loc l =>
        have hp' := refsIn_pos hmem
        exact .root (by simp only [holdRoots]; omega)
      | lit _ => exact .imm (fun _ h => by cases h)
      | ctor0 _ => exact .imm (fun _ h => by cases h)
      | erased => exact .imm (fun _ h => by cases h)
  -- Transfer hQ across the evaluated args using hbs
  have hmem : ∀ (bs : List Bool) (args : List Arg) (vs : List RVal),
      Own.evalArgs ρo args = some vs → BorrowedSatisfies (fun x => Γ'.borrowable x = true) bs args →
      ∀ v, v ∈ selectBorrowedVals bs vs → ReachableFrom H (holdRoots external owned') v := by
    intro bs
    induction bs with
    | nil => intro args vs _ _ v hv; simp at hv
    | cons b bs ih =>
      intro args vs hev hbs' v hv
      cases args with
      | nil => simp [Own.evalArgs] at hev; subst hev; simp at hv
      | cons a as =>
        cases ha : Own.evalArg ρo a with
        | none => simp [Own.evalArgs, ha] at hev
        | some u =>
          cases has : Own.evalArgs ρo as with
          | none => simp [Own.evalArgs, ha, has] at hev
          | some us =>
            have hvu : u :: us = vs := by simpa [Own.evalArgs, ha, has] using hev
            subst hvu
            cases b with
            | false =>
              have hbs'' : BorrowedSatisfies (fun x => Γ'.borrowable x = true) bs as := by
                simpa [BorrowedSatisfies] using hbs'
              exact ih as us has hbs'' v hv
            | true =>
              simp only [selectBorrowedVals, List.mem_cons] at hv
              rcases hv with hEq | hv
              · rw [hEq]
                cases a with
                | var x => exact hQ x hbs'.1 u ha
                | lit _ => simp [Own.evalArg] at ha; rw [← ha]; exact .imm (fun _ h => by cases h)
                | erased => simp [Own.evalArg] at ha; rw [← ha]; exact .imm (fun _ h => by cases h)
              · cases a with
                | var _ => exact ih as us has hbs'.2 v hv
                | lit _ | erased => exact ih as us has hbs' v hv
  exact hmem bs args vs hvs hbs

theorem takeOwnedArgs_tail_sem {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ Γ' : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal}
    {lex : Joins} {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry} {borrows : BorrowSigs}
    {bs : List Bool} {args : List Arg}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
    (ht : Γ.takeOwnedArgs bs args = .ok Γ') (hchk : Γ'.checkTailBorrowed bs args = .ok ()) :
    ∃ vs ws owned', Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
      Sem.Forall2 (Proof.Den H) vs ws ∧ TakeInv H Γ' ρf ρo owned' ∧
      SameRefs owned (selectOwnedVals bs vs ++ owned') ∧ Ctx.Weaker Γ' Γ ∧
      ∀ v, v ∈ selectBorrowedVals bs vs → ReachableFrom H external v := by
  have hbs := checkTailBorrowed_ok hchk
  have hweak := Ctx.takeOwnedArgs_weaker ht
  apply takeOwnedArgs_sem_gen (P := fun x => Γ'.isImm x = true ∨ Γ'.isPbrw x = true)
    (Q := ReachableFrom H external) (fun _ h => .imm h) st.takeInv ht hbs
  intro x hx
  rcases hx with hi | hp
  · refine ⟨by simp [Ctx.avail_eq, hi], fun v hv => ?_⟩
    have hi0 : Γ.isImm x = true := by rw [← hweak.isImm x]; exact hi
    obtain ⟨u, hu, himm⟩ := st.immOk x hi0
    have : u = v := Option.some.inj (hu.symm.trans hv); subst this
    exact .imm himm
  · refine ⟨by simp [Ctx.avail_eq, hp], fun v hv => ?_⟩
    have hp0 : Γ.isPbrw x = true := by rw [← hweak.isPbrw x]; exact hp
    obtain ⟨u, hu, hreach⟩ := st.pbrwOk x hp0
    have : u = v := Option.some.inj (hu.symm.trans hv); subst this
    exact hreach

/-- **The state after a fresh binding**, from what the step establishes for each variable. -/
theorem OwnedState.extend {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins}
    {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry} {borrows : BorrowSigs}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows)
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
    fresh_nodup_append st.distinct (by simp [fresh, hx]), fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_, hepochs, (st.stack.mono_pbrw hpbrwSub).bind x v w hx, st.scope.bind x⟩
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
  · by_cases he : y = x
    · subst he
      exact ⟨v, Src.NatMap.get?_insert_self .., hpbrwx hy⟩
    · obtain ⟨v', h1, h2⟩ := hpbrw y he hy
      exact ⟨v', by rw [Src.NatMap.get?_insert_ne _ _ he]; exact h1, h2⟩

/-- A variable not in scope is not known. -/
theorem OwnedState.unknown {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins}
    {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry} {borrows : BorrowSigs}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows) {x : Var}
    (hx : x ∉ live) : Γ.known x = false := by
  cases hk : Γ.known x with
  | false => rfl
  | true => exact absurd (st.known x hk) hx

end IxCC.Own.Plain
