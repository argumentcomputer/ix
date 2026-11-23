import IxCC.Own.Plain.Proof.Owned.State

/-! # Consuming tokens, and call/tail-call argument checking

`TakeInv` is the part of `OwnedState` a consuming use needs: what takes a token of each argument
(`takeArgs`) or of each captured variable (`takeVars`) yields the arguments' values, their
denotations, and the remaining tokens, with the consumed values' references split off
(`SameRefs owned (vs ++ owned')`, an immediate counting for nothing). `takeOwnedUniqueArgs_call_sem`
and `takeOwnedUniqueArgs_tail_sem` additionally verify `@borrowed` and `@unique` call arguments. -/

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
    {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry} {borrows : BorrowSigs} {uniqs : UniqSigs}
    {retUniq : Bool} {ctors : List Lam.CtorInfo} {K : Lam.Known} {priv : Nat → Prop}
    {slots : Src.NatMap RVal} {slotVals : List RVal}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows uniqs retUniq
      ctors K priv slots slotVals) :
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
    have h0 : Γ.total = 0 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    rw [ht.total] at h0
    exact List.eq_nil_of_length_eq_zero h0
  · split at hc <;> cases hc

/-- A closed context holds no live reset slot. -/
theorem closed_rset {Γ : Ctx} {what : String} (hc : Γ.closed what = .ok ()) :
    mapIsEmpty Γ.rset = true := by
  unfold Ctx.closed at hc
  split at hc
  · next h =>
    simp only [Bool.and_eq_true] at h
    exact h.2
  · split at hc <;> cases hc

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

/-- Unique argument values selected by `(bs, us)` (owned and marked `@unique`). -/
def selectUniqueVals (bs us : List Bool) (vs : List RVal) : List RVal :=
  match vs with
  | [] => []
  | v :: vs =>
    match bs, us with
    | true :: bs, _ :: us => selectUniqueVals bs us vs
    | true :: bs, [] => selectUniqueVals bs [] vs
    | false :: bs, true :: us => v :: selectUniqueVals bs us vs
    | false :: bs, false :: us => selectUniqueVals bs us vs
    | false :: bs, [] => selectUniqueVals bs [] vs
    | [], true :: us => v :: selectUniqueVals [] us vs
    | [], false :: us => selectUniqueVals [] us vs
    | [], [] => []
termination_by structural vs

@[simp] theorem selectOwnedVals_nil_right (bs : List Bool) : selectOwnedVals bs [] = [] := rfl
@[simp] theorem selectOwnedVals_nil_left (vs : List RVal) : selectOwnedVals [] vs = vs := by
  cases vs <;> rfl
@[simp] theorem selectBorrowedVals_nil_right (bs : List Bool) : selectBorrowedVals bs [] = [] := rfl
@[simp] theorem selectBorrowedVals_nil_left (vs : List RVal) : selectBorrowedVals [] vs = [] := by
  cases vs <;> rfl
@[simp] theorem selectUniqueVals_nil_right (bs us : List Bool) : selectUniqueVals bs us [] = [] := rfl

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

theorem selectUniqueVals_all_false : ∀ (bs us : List Bool) (vs : List RVal),
    us.all (!·) = true → selectUniqueVals bs us vs = []
  | _, _, [], _ => rfl
  | [], [], _ :: _, _ => rfl
  | true :: bs, [], _ :: vs, _ => selectUniqueVals_all_false bs [] vs rfl
  | false :: bs, [], _ :: vs, _ => selectUniqueVals_all_false bs [] vs rfl
  | true :: bs, _ :: us, _ :: vs, h =>
    selectUniqueVals_all_false bs us vs (by simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2)
  | false :: bs, u :: us, _ :: vs, h => by
    cases u
    · exact selectUniqueVals_all_false bs us vs (by simpa using h)
    · simp at h
  | [], u :: us, _ :: vs, h => by
    cases u
    · exact selectUniqueVals_all_false [] us vs (by simpa using h)
    · simp at h

theorem selectUniqueVals_sub_owned : ∀ (bs us : List Bool) (vs : List RVal) {v : RVal},
    v ∈ selectUniqueVals bs us vs → v ∈ selectOwnedVals bs vs
  | _, _, [], _, h => by cases h
  | [], [], _ :: _, _, h => by cases h
  | true :: bs, [], _ :: vs, _, h => selectUniqueVals_sub_owned bs [] vs h
  | false :: bs, [], _ :: vs, _, h =>
    List.mem_cons_of_mem _ (selectUniqueVals_sub_owned bs [] vs h)
  | true :: bs, _ :: us, _ :: vs, _, h => selectUniqueVals_sub_owned bs us vs h
  | false :: bs, false :: us, _ :: vs, _, h =>
    List.mem_cons_of_mem _ (selectUniqueVals_sub_owned bs us vs h)
  | false :: bs, true :: us, _ :: vs, _, h => by
    simp only [selectUniqueVals, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (selectUniqueVals_sub_owned bs us vs h)
  | [], false :: us, _ :: vs, _, h => by
    have := selectUniqueVals_sub_owned [] us vs h
    rw [selectOwnedVals_nil_left] at this ⊢
    exact List.mem_cons_of_mem _ this
  | [], true :: us, _ :: vs, _, h => by
    simp only [selectUniqueVals, List.mem_cons] at h
    rw [selectOwnedVals_nil_left]
    rcases h with rfl | h
    · exact List.mem_cons_self
    · have := selectUniqueVals_sub_owned [] us vs h
      rw [selectOwnedVals_nil_left] at this
      exact List.mem_cons_of_mem _ this

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

theorem takeOwnedUniqueArgs_sem_gen {H : Heap} {ρf : Fir.Env} {ρo : Own.Env}
    {P : Var → Prop} {Q U : RVal → Prop}
    (hQimm : ∀ v, ImmVal v → Q v) (hUlit : ∀ l, U (.lit l)) (hUer : U .erased)
    {Γ Γ' : Ctx} {owned : List RVal} {bs us : List Bool} {args : List Arg}
    (h : TakeInv H Γ ρf ρo owned)
    (hU : ∀ x, Γ.isUniq x = true → ∀ v, ρo.get? x = some v → U v)
    (ht : Γ.takeOwnedUniqueArgs bs us args = .ok Γ')
    (hbs : BorrowedSatisfies P bs args)
    (hP : ∀ x, P x → Γ'.avail x = true ∧ ∀ v, ρo.get? x = some v → Q v) :
    ∃ vs ws owned', Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
      Sem.Forall2 (Proof.Den H) vs ws ∧ TakeInv H Γ' ρf ρo owned' ∧
      SameRefs owned (selectOwnedVals bs vs ++ owned') ∧ Ctx.Weaker Γ' Γ ∧
      (∀ v, v ∈ selectBorrowedVals bs vs → Q v) ∧
      (∀ v, v ∈ selectUniqueVals bs us vs → U v) ∧
      (∀ x, Arg.var x ∈ args → Γ.avail x = true) := by
  induction args generalizing Γ owned bs us with
  | nil =>
    cases ht
    exact ⟨[], [], owned, rfl, rfl, .nil, h, SameRefs.refl _, Ctx.Weaker.refl _,
      (fun _ hm => by cases hm), (fun _ hm => by cases hm), (fun _ hm => by cases hm)⟩
  | cons a as ih =>
    have htriv : BorrowedSatisfies P [] as := by cases as <;> trivial
    have hstepOwned : ∀ (Γ₁ : Ctx) (bs' us' : List Bool) (ha : Γ.takeArg a = .ok Γ₁)
        (ht' : Γ₁.takeOwnedUniqueArgs bs' us' as = .ok Γ')
        (hbs' : BorrowedSatisfies P bs' as),
        ∃ v w owned₁ vs ws owned',
          Own.evalArg ρo a = some v ∧ a.eval ρf = some w ∧ Proof.Den H v w ∧
          SameRefs owned (v :: owned₁) ∧ Ctx.Weaker Γ₁ Γ ∧
          Own.evalArgs ρo as = some vs ∧ Fir.evalArgs ρf as = some ws ∧
          Sem.Forall2 (Proof.Den H) vs ws ∧ TakeInv H Γ' ρf ρo owned' ∧
          SameRefs owned₁ (selectOwnedVals bs' vs ++ owned') ∧ Ctx.Weaker Γ' Γ₁ ∧
          (∀ u, u ∈ selectBorrowedVals bs' vs → Q u) ∧
          (∀ u, u ∈ selectUniqueVals bs' us' vs → U u) ∧
          (∀ x, Arg.var x ∈ a :: as → Γ.avail x = true) := by
      intro Γ₁ bs' us' ha ht' hbs'
      obtain ⟨v, w, owned₁, hv, hw, hd, h₁, hs₁, hw₁⟩ := takeArg_sem h ha
      obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ', hU', hav'⟩ :=
        ih h₁ (fun x hx => hU x (hw₁.isUniq x hx)) ht' hbs'
      refine ⟨v, w, owned₁, vs, ws, owned', hv, hw, hd, hs₁, hw₁, hvs, hws, hds, h', hs', hw',
        hQ', hU', fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases Ctx.take_ok ha with ⟨hi, _⟩ | ⟨_, n, hn, _⟩
        · simp [Ctx.avail_eq, hi]
        · simp [Ctx.avail_eq, Ctx.tokens_eq, hn]
      · exact hw₁.avail (hav' x hx)
    cases bs with
    | nil =>
      cases us with
      | nil =>
        simp only [Ctx.takeOwnedUniqueArgs] at ht
        cases ha : Γ.takeArg a with
        | error e => rw [ha] at ht; cases ht
        | ok Γ₁ =>
          rw [ha] at ht
          obtain ⟨v, w, owned₁, vs, ws, owned', hv, hw, hd, hs₁, hw₁, hvs, hws, hds, h', hs',
            hw', _, _, hav'⟩ := hstepOwned Γ₁ [] [] ha ht htriv
          refine ⟨v :: vs, w :: ws, owned', by simp [Own.evalArgs, hv, hvs],
            by simp [Fir.evalArgs, hw, hws], .cons hd hds, h',
            hs₁.trans (SameRefs.cons v (by simpa using hs')), hw'.trans hw₁,
            (fun _ hm => by simp at hm), (fun _ hm => by cases hm), hav'⟩
      | cons u us =>
        cases u with
        | false =>
          simp only [Ctx.takeOwnedUniqueArgs] at ht
          cases ha : Γ.takeArg a with
          | error e => rw [ha] at ht; cases ht
          | ok Γ₁ =>
            rw [ha] at ht
            obtain ⟨v, w, owned₁, vs, ws, owned', hv, hw, hd, hs₁, hw₁, hvs, hws, hds, h', hs',
              hw', _, hU', hav'⟩ := hstepOwned Γ₁ [] us ha ht htriv
            refine ⟨v :: vs, w :: ws, owned', by simp [Own.evalArgs, hv, hvs],
              by simp [Fir.evalArgs, hw, hws], .cons hd hds, h',
              hs₁.trans (SameRefs.cons v (by simpa using hs')), hw'.trans hw₁,
              (fun _ hm => by simp at hm), hU', hav'⟩
        | true =>
          cases a with
          | lit l =>
            simp only [Ctx.takeOwnedUniqueArgs] at ht
            obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', _, hU', hav'⟩ :=
              ih h hU ht htriv
            refine ⟨.lit l :: vs, .lit l :: ws, owned', by simp [Own.evalArgs, Own.evalArg, hvs],
              by simp [Fir.evalArgs, Fir.Arg.eval, hws], .cons (Proof.den_lit H l) hds, h',
              hs'.trans (by simpa using (SameRefs.imm_cons (fun _ hc => by cases hc) _).symm), hw',
              (fun _ hm => by simp at hm), fun u hu => ?_, fun x hx => ?_⟩
            · simp only [selectUniqueVals, List.mem_cons] at hu
              rcases hu with rfl | hu
              · exact hUlit l
              · exact hU' u hu
            · rcases List.mem_cons.mp hx with hc | hx
              · cases hc
              · exact hav' x hx
          | erased =>
            simp only [Ctx.takeOwnedUniqueArgs] at ht
            obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', _, hU', hav'⟩ :=
              ih h hU ht htriv
            refine ⟨.erased :: vs, .erased :: ws, owned', by simp [Own.evalArgs, Own.evalArg, hvs],
              by simp [Fir.evalArgs, Fir.Arg.eval, hws], .cons (Proof.den_erased H) hds, h',
              hs'.trans (by simpa using (SameRefs.imm_cons (fun _ hc => by cases hc) _).symm), hw',
              (fun _ hm => by simp at hm), fun u hu => ?_, fun x hx => ?_⟩
            · simp only [selectUniqueVals, List.mem_cons] at hu
              rcases hu with rfl | hu
              · exact hUer
              · exact hU' u hu
            · rcases List.mem_cons.mp hx with hc | hx
              · cases hc
              · exact hav' x hx
          | var x =>
            simp only [Ctx.takeOwnedUniqueArgs] at ht
            cases hu : Γ.isUniq x with
            | false => simp [hu, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ht
            | true =>
              simp only [hu, ↓reduceIte] at ht
              cases ha : Γ.take x with
              | error e => rw [ha] at ht; cases ht
              | ok Γ₁ =>
                rw [ha] at ht
                obtain ⟨v, w, owned₁, vs, ws, owned', hv, hw, hd, hs₁, hw₁, hvs, hws, hds, h', hs',
                  hw', _, hU', hav'⟩ := hstepOwned Γ₁ [] us ha ht htriv
                refine ⟨v :: vs, w :: ws, owned', by simp [Own.evalArgs, hv, hvs],
                  by simp [Fir.evalArgs, hw, hws], .cons hd hds, h',
                  hs₁.trans (SameRefs.cons v (by simpa using hs')), hw'.trans hw₁,
                  (fun _ hm => by simp at hm), fun u' hu' => ?_, hav'⟩
                simp only [selectUniqueVals, List.mem_cons] at hu'
                rcases hu' with rfl | hu'
                · exact hU x hu u' hv
                · exact hU' u' hu'
    | cons b bs =>
      cases b with
      | false =>
        cases us with
        | nil =>
          simp only [Ctx.takeOwnedUniqueArgs] at ht
          cases ha : Γ.takeArg a with
          | error e => rw [ha] at ht; cases ht
          | ok Γ₁ =>
            rw [ha] at ht
            have hbs' : BorrowedSatisfies P bs as := by simpa [BorrowedSatisfies] using hbs
            obtain ⟨v, w, owned₁, vs, ws, owned', hv, hw, hd, hs₁, hw₁, hvs, hws, hds, h', hs',
              hw', hQ', hU', hav'⟩ := hstepOwned Γ₁ bs [] ha ht hbs'
            refine ⟨v :: vs, w :: ws, owned', by simp [Own.evalArgs, hv, hvs],
              by simp [Fir.evalArgs, hw, hws], .cons hd hds, h',
              hs₁.trans (SameRefs.cons v hs'), hw'.trans hw₁, hQ', hU', hav'⟩
        | cons u us =>
          cases u with
          | false =>
            simp only [Ctx.takeOwnedUniqueArgs] at ht
            cases ha : Γ.takeArg a with
            | error e => rw [ha] at ht; cases ht
            | ok Γ₁ =>
              rw [ha] at ht
              have hbs' : BorrowedSatisfies P bs as := by simpa [BorrowedSatisfies] using hbs
              obtain ⟨v, w, owned₁, vs, ws, owned', hv, hw, hd, hs₁, hw₁, hvs, hws, hds, h', hs',
                hw', hQ', hU', hav'⟩ := hstepOwned Γ₁ bs us ha ht hbs'
              refine ⟨v :: vs, w :: ws, owned', by simp [Own.evalArgs, hv, hvs],
                by simp [Fir.evalArgs, hw, hws], .cons hd hds, h',
                hs₁.trans (SameRefs.cons v hs'), hw'.trans hw₁, hQ', hU', hav'⟩
          | true =>
            cases a with
            | lit l =>
              simp only [Ctx.takeOwnedUniqueArgs] at ht
              have hbs' : BorrowedSatisfies P bs as := by simpa [BorrowedSatisfies] using hbs
              obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ', hU', hav'⟩ :=
                ih h hU ht hbs'
              refine ⟨.lit l :: vs, .lit l :: ws, owned', by simp [Own.evalArgs, Own.evalArg, hvs],
                by simp [Fir.evalArgs, Fir.Arg.eval, hws], .cons (Proof.den_lit H l) hds, h',
                hs'.trans (SameRefs.imm_cons (fun _ hc => by cases hc) _).symm, hw', hQ',
                fun u' hu' => ?_, fun x hx => ?_⟩
              · simp only [selectUniqueVals, List.mem_cons] at hu'
                rcases hu' with rfl | hu'
                · exact hUlit l
                · exact hU' u' hu'
              · rcases List.mem_cons.mp hx with hc | hx
                · cases hc
                · exact hav' x hx
            | erased =>
              simp only [Ctx.takeOwnedUniqueArgs] at ht
              have hbs' : BorrowedSatisfies P bs as := by simpa [BorrowedSatisfies] using hbs
              obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ', hU', hav'⟩ :=
                ih h hU ht hbs'
              refine ⟨.erased :: vs, .erased :: ws, owned', by simp [Own.evalArgs, Own.evalArg, hvs],
                by simp [Fir.evalArgs, Fir.Arg.eval, hws], .cons (Proof.den_erased H) hds, h',
                hs'.trans (SameRefs.imm_cons (fun _ hc => by cases hc) _).symm, hw', hQ',
                fun u' hu' => ?_, fun x hx => ?_⟩
              · simp only [selectUniqueVals, List.mem_cons] at hu'
                rcases hu' with rfl | hu'
                · exact hUer
                · exact hU' u' hu'
              · rcases List.mem_cons.mp hx with hc | hx
                · cases hc
                · exact hav' x hx
            | var x =>
              simp only [Ctx.takeOwnedUniqueArgs] at ht
              cases hu : Γ.isUniq x with
              | false => simp [hu, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ht
              | true =>
                simp only [hu, ↓reduceIte] at ht
                cases ha : Γ.take x with
                | error e => rw [ha] at ht; cases ht
                | ok Γ₁ =>
                  rw [ha] at ht
                  have hbs' : BorrowedSatisfies P bs as := by simpa [BorrowedSatisfies] using hbs
                  obtain ⟨v, w, owned₁, vs, ws, owned', hv, hw, hd, hs₁, hw₁, hvs, hws, hds, h', hs',
                    hw', hQ', hU', hav'⟩ := hstepOwned Γ₁ bs us ha ht hbs'
                  refine ⟨v :: vs, w :: ws, owned', by simp [Own.evalArgs, hv, hvs],
                    by simp [Fir.evalArgs, hw, hws], .cons hd hds, h',
                    hs₁.trans (SameRefs.cons v hs'), hw'.trans hw₁, hQ', fun u' hu' => ?_, hav'⟩
                  simp only [selectUniqueVals, List.mem_cons] at hu'
                  rcases hu' with rfl | hu'
                  · exact hU x hu u' hv
                  · exact hU' u' hu'
      | true =>
        have hstepBrw : ∀ (us' : List Bool) (ht' : Γ.takeOwnedUniqueArgs bs us' as = .ok Γ'),
            ∃ vs ws owned', Own.evalArgs ρo (a :: as) = some vs ∧
              Fir.evalArgs ρf (a :: as) = some ws ∧ Sem.Forall2 (Proof.Den H) vs ws ∧
              TakeInv H Γ' ρf ρo owned' ∧
              SameRefs owned (selectOwnedVals (true :: bs) vs ++ owned') ∧ Ctx.Weaker Γ' Γ ∧
              (∀ v, v ∈ selectBorrowedVals (true :: bs) vs → Q v) ∧
              (∀ v, v ∈ selectUniqueVals bs us' vs.tail → U v) ∧
              (∀ x, Arg.var x ∈ a :: as → Γ.avail x = true) := by
          intro us' ht'
          have hweak := Ctx.takeOwnedUniqueArgs_weaker ht'
          cases a with
          | var x =>
            obtain ⟨hPx, hbs'⟩ := hbs
            obtain ⟨hav', hQx⟩ := hP x hPx
            have hav0 := hweak.avail hav'
            obtain ⟨v, w, hv, hw, hd⟩ := h.den x hav0
            obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ', hU', hav'⟩ :=
              ih h hU ht' hbs'
            refine ⟨v :: vs, w :: ws, owned', by simp [Own.evalArgs, Own.evalArg, hv, hvs],
              by simp [Fir.evalArgs, Fir.Arg.eval, hw, hws], .cons hd hds, h', hs', hw',
              fun u hu => ?_, hU', fun z hz => ?_⟩
            · simp only [selectBorrowedVals, List.mem_cons] at hu
              rcases hu with rfl | hu
              · exact hQx u hv
              · exact hQ' u hu
            · rcases List.mem_cons.mp hz with hEq | hz
              · cases hEq; exact hav0
              · exact hav' z hz
          | lit l =>
            obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ', hU', hav'⟩ :=
              ih h hU ht' hbs
            refine ⟨.lit l :: vs, .lit l :: ws, owned', by simp [Own.evalArgs, Own.evalArg, hvs],
              by simp [Fir.evalArgs, Fir.Arg.eval, hws], .cons (Proof.den_lit H l) hds, h', hs',
              hw', fun u hu => ?_, hU', fun z hz => ?_⟩
            · simp only [selectBorrowedVals, List.mem_cons] at hu
              rcases hu with rfl | hu
              · exact hQimm _ (fun _ hc => by cases hc)
              · exact hQ' u hu
            · rcases List.mem_cons.mp hz with hc | hz
              · cases hc
              · exact hav' z hz
          | erased =>
            obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ', hU', hav'⟩ :=
              ih h hU ht' hbs
            refine ⟨.erased :: vs, .erased :: ws, owned', by simp [Own.evalArgs, Own.evalArg, hvs],
              by simp [Fir.evalArgs, Fir.Arg.eval, hws], .cons (Proof.den_erased H) hds, h', hs',
              hw', fun u hu => ?_, hU', fun z hz => ?_⟩
            · simp only [selectBorrowedVals, List.mem_cons] at hu
              rcases hu with rfl | hu
              · exact hQimm _ (fun _ hc => by cases hc)
              · exact hQ' u hu
            · rcases List.mem_cons.mp hz with hc | hz
              · cases hc
              · exact hav' z hz
        cases us with
        | nil =>
          simp only [Ctx.takeOwnedUniqueArgs] at ht
          obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ', hU', hav'⟩ := hstepBrw [] ht
          refine ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ', fun u hu => ?_, hav'⟩
          cases vs with
          | nil => cases hu
          | cons _ _ => exact hU' u hu
        | cons _ us =>
          simp only [Ctx.takeOwnedUniqueArgs] at ht
          obtain ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ', hU', hav'⟩ := hstepBrw us ht
          refine ⟨vs, ws, owned', hvs, hws, hds, h', hs', hw', hQ', fun u hu => ?_, hav'⟩
          cases vs with
          | nil => cases hu
          | cons _ _ => exact hU' u hu

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

/-- Full non-tail call argument checking with `@borrowed` and `@unique` annotations, slot roots,
and private-frame preservation. -/
theorem takeOwnedUniqueArgs_call_sem {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ Γ' : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal}
    {lex : Joins} {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {K : Lam.Known} {priv : Nat → Prop}
    {slots : Src.NatMap RVal} {slotVals : List RVal}
    {bs us : List Bool} {args : List Arg}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows uniqs retUniq
      ctors K priv slots slotVals)
    (ht : Γ.takeOwnedUniqueArgs bs us args = .ok Γ') (hchk : Γ'.checkCallBorrowed bs args = .ok ()) :
    ∃ vs ws owned', Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
      Sem.Forall2 (Proof.Den H) vs ws ∧ TakeInv H Γ' ρf ρo owned' ∧
      SameRefs owned (selectOwnedVals bs vs ++ owned') ∧ Ctx.Weaker Γ' Γ ∧
      (∀ v, v ∈ selectBorrowedVals bs vs → ReachableFrom H (holdRoots external (owned' ++ slotVals)) v) ∧
      (∀ v, v ∈ selectUniqueVals bs us vs →
        UniqVal ctors H (holdRoots external (owned' ++ slotVals)) (selectOwnedVals bs vs) v) ∧
      (∀ x, Arg.var x ∈ args → Γ.avail x = true) := by
  have hbs := checkCallBorrowed_ok hchk
  have hP1 : ∀ x, Γ'.borrowable x = true → Γ'.avail x = true ∧ ∀ v, ρo.get? x = some v → True := by
    intro x hx
    refine ⟨?_, fun _ _ => trivial⟩
    simp only [Ctx.borrowable_eq, Ctx.avail_eq, Bool.or_eq_true, decide_eq_true_eq] at hx ⊢
    rcases hx with (h1 | h2) | h3
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inr h2
    · exact Or.inl (Or.inl (Or.inr h3))
  have hU : ∀ x, Γ.isUniq x = true → ∀ v, ρo.get? x = some v →
      UniqVal ctors H external (owned ++ slotVals) v := by
    intro x hx v hv
    obtain ⟨_, u, hu, hvu⟩ := st.uniqOk x hx
    have : u = v := Option.some.inj (hu.symm.trans hv); subst this
    exact hvu
  obtain ⟨vs, ws, owned', hvs, hws, hds, inv', hs', hw', _, hUv, hav⟩ :=
    takeOwnedUniqueArgs_sem_gen (P := fun x => Γ'.borrowable x = true) (Q := fun _ => True)
      (U := UniqVal ctors H external (owned ++ slotVals))
      (fun _ _ => trivial) (fun _ => trivial) trivial st.takeInv hU ht hbs hP1
  refine ⟨vs, ws, owned', hvs, hws, hds, inv', hs', hw', ?_, ?_, hav⟩
  · have hQ : ∀ x, Γ'.borrowable x = true → ∀ v, ρo.get? x = some v →
        ReachableFrom H (holdRoots external (owned' ++ slotVals)) v := by
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
          exact .root (by simp only [holdRoots, refsIn_append]; omega)
        | lit _ => exact .imm (fun _ h => by cases h)
        | ctor0 _ => exact .imm (fun _ h => by cases h)
        | erased => exact .imm (fun _ h => by cases h)
    have hmem : ∀ (bs : List Bool) (args : List Arg) (vs : List RVal),
        Own.evalArgs ρo args = some vs → BorrowedSatisfies (fun x => Γ'.borrowable x = true) bs args →
        ∀ v, v ∈ selectBorrowedVals bs vs →
          ReachableFrom H (holdRoots external (owned' ++ slotVals)) v := by
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
  · intro v hv
    have hu := hUv v hv
    have hm := selectUniqueVals_sub_owned bs us vs hv
    cases v with
    | lit _ | erased => trivial
    | ctor0 c => exact hu
    | loc l =>
      obtain ⟨b, hc, hext, hedge, hrefs⟩ := hu
      have hpos := refsIn_pos hm
      have hsplit : refsIn l (owned ++ slotVals) =
          refsIn l (selectOwnedVals bs vs) + refsIn l (owned' ++ slotVals) := by
        simp only [refsIn_append, hs' l]; omega
      exact ⟨b, hc, by simp only [holdRoots]; omega, hedge, by omega⟩

/-- Full tail-call argument checking with `@borrowed` and `@unique` annotations. -/
theorem takeOwnedUniqueArgs_tail_sem {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ Γ' : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal}
    {lex : Joins} {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {K : Lam.Known} {priv : Nat → Prop}
    {slots : Src.NatMap RVal} {slotVals : List RVal}
    {bs us : List Bool} {args : List Arg} {what : String}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows uniqs retUniq
      ctors K priv slots slotVals)
    (ht : Γ.takeOwnedUniqueArgs bs us args = .ok Γ')
    (hchk : Γ'.checkTailBorrowed bs args = .ok ())
    (hcl : Γ'.closed what = .ok ()) :
    ∃ vs ws owned', Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
      Sem.Forall2 (Proof.Den H) vs ws ∧ TakeInv H Γ' ρf ρo owned' ∧
      SameRefs owned (selectOwnedVals bs vs ++ owned') ∧ Ctx.Weaker Γ' Γ ∧
      (∀ v, v ∈ selectBorrowedVals bs vs → ReachableFrom H external v) ∧
      (∀ v, v ∈ selectUniqueVals bs us vs →
        UniqVal ctors H external (selectOwnedVals bs vs) v) ∧
      (∀ x, Arg.var x ∈ args → Γ.avail x = true) := by
  have hbs := checkTailBorrowed_ok hchk
  have hweak := Ctx.takeOwnedUniqueArgs_weaker ht
  have hU : ∀ x, Γ.isUniq x = true → ∀ v, ρo.get? x = some v →
      UniqVal ctors H external (owned ++ slotVals) v := by
    intro x hx v hv
    obtain ⟨_, u, hu, hvu⟩ := st.uniqOk x hx
    have : u = v := Option.some.inj (hu.symm.trans hv); subst this
    exact hvu
  obtain ⟨vs, ws, owned', hvs, hws, hds, inv', hs', hw', hbrw, hUv, hav⟩ :=
    takeOwnedUniqueArgs_sem_gen (P := fun x => Γ'.isImm x = true ∨ Γ'.isPbrw x = true)
      (Q := ReachableFrom H external) (U := UniqVal ctors H external (owned ++ slotVals))
      (fun _ h => .imm h) (fun _ => trivial) trivial st.takeInv hU ht hbs (fun x hx => by
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
          exact hreach)
  obtain ⟨toks', htok', hroots'⟩ := inv'.roots
  have hnil := closed_nil htok' hcl
  subst hnil
  have ho' := EnvRoots.nil_inv hroots'
  subst ho'
  obtain ⟨skeys, hsk, hsroots⟩ := st.slotRoots
  have hsnil := (hsk.same hw'.rset).closed_nil (closed_rset hcl)
  subst hsnil
  have hsv := EnvRoots.nil_inv hsroots
  subst hsv
  refine ⟨vs, ws, [], hvs, hws, hds, inv', hs', hw', hbrw, fun v hv => ?_, hav⟩
  exact (hUv v hv).sameRefs (fun k => by simpa using hs' k)

/-- A variable not in scope is not known. -/
theorem OwnedState.unknown {functions : Signatures} {H : Heap} {external : Nat → Nat}
    {live : List Var} {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins}
    {Δ : JCtx} {Jf : List Fir.JEntry} {Jo : List JEntry}
    {borrows : BorrowSigs} {uniqs : UniqSigs} {retUniq : Bool}
    {ctors : List Lam.CtorInfo} {K : Lam.Known} {priv : Nat → Prop}
    {slots : Src.NatMap RVal} {slotVals : List RVal}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo borrows uniqs retUniq
      ctors K priv slots slotVals) {x : Var} (hx : x ∉ live) : Γ.known x = false := by
  cases hk : Γ.known x with
  | false => rfl
  | true => exact absurd (st.known x hk) hx

end IxCC.Own.Plain
