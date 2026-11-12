import IxCC.Own.Plain.Proof.Owned.Binds
import IxCC.Fir.Proof.Unfold

/-! # One binding that calls nothing, against the source's step

From the checker's verdict on `x := r` and the source's successful step, the Own step and the
state after it: a moved token (`x := y`), an immediate (literals, field-less constructors,
projections of immediates, primitives), an allocation (one token per field occurrence), or a
borrowed projection. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var Arg)

theorem except_bind_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem except_pure_ok {ε α : Type} {a b : α} (h : (pure a : Except ε α) = .ok b) : a = b :=
  Except.ok.inj h

theorem Result.ofOption_ok {α : Type} {o : Option α} {a : α} (h : Result.ofOption o = .ok a) :
    o = some a := by
  cases o with
  | none => cases h
  | some b => cases h; rfl

theorem firEvalArgs_length {ρ : Fir.Env} :
    ∀ {args : List Arg} {ws : List Fir.Val}, Fir.evalArgs ρ args = some ws → ws.length = args.length
  | [], ws, h => by simp [Fir.evalArgs] at h; subst h; rfl
  | a :: as, ws, h => by
    cases ha : a.eval ρ with
    | none => simp [Fir.evalArgs, ha] at h
    | some w =>
      cases hs : Fir.evalArgs ρ as with
      | none => simp [Fir.evalArgs, ha, hs] at h
      | some ws' =>
        have : w :: ws' = ws := by simpa [Fir.evalArgs, ha, hs] using h
        subst this
        simp [firEvalArgs_length hs]

theorem evalArgs_mem {ρ : Own.Env} :
    ∀ {args : List Arg} {vs : List RVal} {y : Var} {u : RVal}, Own.evalArgs ρ args = some vs →
      Arg.var y ∈ args → ρ.get? y = some u → u ∈ vs
  | [], _, _, _, _, hy, _ => by simp at hy
  | a :: as, vs, y, u, h, hy, hu => by
    cases ha : Own.evalArg ρ a with
    | none => simp [Own.evalArgs, ha] at h
    | some v =>
      cases hs : Own.evalArgs ρ as with
      | none => simp [Own.evalArgs, ha, hs] at h
      | some vs' =>
        have : v :: vs' = vs := by simpa [Own.evalArgs, ha, hs] using h
        subst this
        rcases List.mem_cons.mp hy with he | hy
        · subst he
          have : v = u := Option.some.inj (ha.symm.trans hu)
          subst this; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (evalArgs_mem hs hy hu)

/-- Variables a primitive reads are available, so they denote. -/
theorem needArgs_sem {H : Heap} {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env}
    (hden : ∀ x, Γ.avail x = true →
      ∃ v w, ρo.get? x = some v ∧ ρf.get? x = some w ∧ Proof.Den H v w) :
    ∀ {args : List Arg}, (∀ x, Arg.var x ∈ args → Γ.avail x = true) →
      ∃ vs ws, Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
        Sem.Forall2 (Proof.Den H) vs ws
  | [], _ => ⟨[], [], rfl, rfl, .nil⟩
  | a :: as, h => by
    obtain ⟨vs, ws, h1, h2, h3⟩ := needArgs_sem hden (args := as)
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha : ∃ v w, Own.evalArg ρo a = some v ∧ a.eval ρf = some w ∧ Proof.Den H v w := by
      cases a with
      | var x => exact hden x (h x List.mem_cons_self)
      | lit l => exact ⟨.lit l, .lit l, rfl, rfl, Proof.den_lit H l⟩
      | erased => exact ⟨.erased, .erased, rfl, rfl, Proof.den_erased H⟩
    obtain ⟨v, w, h4, h5, h6⟩ := ha
    exact ⟨v :: vs, w :: ws, by simp [Own.evalArgs, h4, h1], by simp [Fir.evalArgs, h5, h2],
      .cons h6 h3⟩

section
variable {functions : Signatures} {H : Heap} {external : Nat → Nat} {live : List Var}
  {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins} {Δ : JCtx}
  {Jf : List Fir.JEntry} {Jo : List JEntry}

theorem rhs_step {F : Fir.Program} (pins : BoolPinsOk F)
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo)
    {x : Var} {r : Fir.Rhs} (hx : x ∉ live) (hn : ∀ f args, r ≠ .call f args)
    {Γ' : Ctx} (hc : bindCtx Γ x r = .ok Γ') {w : Fir.Val} (hw : Fir.evalRhs F ρf r = .ok w) :
    ∃ v H' owned', evalRhs { ctors := F.ctors, known := F.known } ρo H r = .ok (v, H') ∧
      OwnedState functions H' external (live ++ [x]) Γ' (ρf.insert x w) (ρo.insert x v) owned'
        lex Δ Jf Jo ∧ ExternalPreserved H H' external := by
  have same : ExternalPreserved H H external := fun _ _ _ h => h
  cases r with
  | call f args => exact absurd rfl (hn f args)
  | arg a =>
    cases a with
    | var y =>
      obtain ⟨Γ₁, ht, hΓ⟩ := except_bind_ok hc
      have hΓ := except_pure_ok hΓ
      have hwy : ρf.get? y = some w := Result.ofOption_ok hw
      obtain ⟨v, w', owned₁, hv, hw', hd, inv₁, hs, hwk⟩ := take_sem st.takeInv ht
      have : w' = w := Option.some.inj (hw'.symm.trans hwy)
      subst this
      have hev : evalRhs { ctors := F.ctors, known := F.known } ρo H (.arg (.var y)) = .ok (v, H) := by
        simp [evalRhs, Own.evalRhs, Own.evalArg, hv]
      cases hi : Γ.isImm y with
      | true =>
        refine ⟨v, H, owned, hev, ?_, same⟩
        rw [hi] at hΓ
        simp only [↓reduceIte] at hΓ
        subst hΓ
        have hΓ₁ : Γ₁ = Γ := by
          rcases Ctx.take_ok ht with ⟨_, h⟩ | ⟨hi', _⟩
          · exact h
          · rw [hi] at hi'; cases hi'
        subst hΓ₁
        obtain ⟨u, hu, himm⟩ := st.immOk y hi
        have : u = v := Option.some.inj (hu.symm.trans hv)
        subst this
        exact st.pre.bindImm hx hd himm st.counts
      | false =>
        refine ⟨v, H, v :: owned₁, hev, ?_, same⟩
        rw [hi] at hΓ
        simp only [Bool.false_eq_true, ↓reduceIte] at hΓ
        subst hΓ
        exact (st.pre.weaker hwk inv₁.roots).bindOwned hx hd (hs.balance st.counts)
    | lit l =>
      cases hc
      have : w = .lit l := (Option.some.inj (Result.ofOption_ok hw)).symm
      subst this
      refine ⟨.lit l, H, owned, by simp [evalRhs, Own.evalRhs, Own.evalArg], ?_, same⟩
      exact st.pre.bindImm hx (Proof.den_lit H l) (by intro l h; cases h) st.counts
    | erased =>
      cases hc
      have : w = .erased := (Option.some.inj (Result.ofOption_ok hw)).symm
      subst this
      refine ⟨.erased, H, owned, by simp [evalRhs, Own.evalRhs, Own.evalArg], ?_, same⟩
      exact st.pre.bindImm hx (Proof.den_erased H) (by intro l h; cases h) st.counts
  | ctor c args =>
    cases hws : Fir.evalArgs ρf args with
    | none => simp [Fir.evalRhs, hws] at hw
    | some ws =>
      by_cases harity : ws.length = c.arity
      · have hw' : w = .ctor c ws := by
          simp [Fir.evalRhs, hws, harity] at hw; exact hw.symm
        subst hw'
        by_cases hz : c.arity = 0
        · have hc' : bindCtx Γ x (.ctor c args) = .ok (Γ.setImm x) := by
            simp [bindCtx, hz]
          rw [hc'] at hc
          cases hc
          have hws0 : ws = [] := List.eq_nil_of_length_eq_zero (harity.trans hz)
          subst hws0
          have hargs : args = [] := by
            have := firEvalArgs_length hws
            exact List.eq_nil_of_length_eq_zero this.symm
          subst hargs
          refine ⟨.ctor0 c, H, owned, ?_, ?_, same⟩
          · simp [evalRhs, Own.evalRhs, Own.evalArgs, hz, Fir.CtorInfo.fieldless]
          · exact st.pre.bindImm hx (Proof.den_ctor0 H c) (by intro l h; cases h) st.counts
        · have hz' : (c.arity == 0) = false := by simpa using hz
          simp only [bindCtx, hz', Bool.false_eq_true, ↓reduceIte] at hc
          obtain ⟨Γ₁, ht, hΓ⟩ := except_bind_ok hc
          have hΓ := except_pure_ok hΓ
          subst hΓ
          obtain ⟨vs, ws', owned₁, hvs, hws', hds, inv₁, hs, hwk⟩ := takeArgs_sem st.takeInv ht
          have : ws' = ws := Option.some.inj (hws'.symm.trans hws)
          subst this
          have hvlen : vs.length = c.arity := hds.length.trans harity
          have hpos : 0 < c.arity := by omega
          have held : Balance H (holdRoots external owned₁) vs :=
            balance_hold.mp (hs.balance st.counts)
          obtain ⟨hr, hb, hresult, hpreserve⟩ :=
            evalRhs_alloc_owned (T := { ctors := F.ctors, known := F.known }) hvs hvlen hpos held hds
          refine ⟨(H.alloc .rc { ctor := c, fields := vs }).1, (H.alloc .rc { ctor := c, fields := vs }).2,
            (H.alloc .rc { ctor := c, fields := vs }).1 :: owned₁, hr, ?_,
            fun root w' _ hd' => hpreserve root w' hd'⟩
          have pre₁ := ((st.pre.weaker hwk inv₁.roots).transport hpreserve
            (fun v hv => canDup_alloc hv _))
          exact pre₁.bindOwned hx hresult
            ((SameRefs.comm _ _).balance (balance_resume hb))
      · simp [Fir.evalRhs, hws, harity] at hw
  | proj y key i =>
    obtain ⟨u, hneed, hΓ⟩ := except_bind_ok hc
    have hΓ := except_pure_ok hΓ
    have hy : Γ.avail y = true := Ctx.need_avail hneed
    obtain ⟨vy, wy, hvy, hwy, hdy⟩ := st.den y hy
    simp only [Fir.evalRhs, hwy] at hw
    cases hcw : wy.asCtor F.known with
    | none => rw [hcw] at hw; cases hw
    | some p =>
      obtain ⟨key', fields⟩ := p
      rw [hcw] at hw
      by_cases hk : key' = key
      · subst hk
        simp only [↓reduceIte] at hw
        have hi : fields[i]? = some w := Result.ofOption_ok hw
        obtain ⟨vs, hview, hfields⟩ := (Values.asCtor_den F.known hdy).1 key' fields hcw
        obtain ⟨v, hget, hv⟩ := hfields.get' hi
        have hm : v ∈ vs := List.mem_of_getElem? hget
        have hev : evalRhs { ctors := F.ctors, known := F.known } ρo H (.proj y key' i) =
            .ok (v, H) := by
          simp [evalRhs, Own.evalRhs, hvy, hview, hget, Result.ofOption, Result.map]
        refine ⟨v, H, owned, hev, ?_, same⟩
        subst hΓ
        cases hi' : Γ.isImm y with
        | true =>
          simp only [↓reduceIte]
          obtain ⟨u', hu', himm⟩ := st.immOk y hi'
          have : u' = vy := Option.some.inj (hu'.symm.trans hvy)
          subst this
          exact st.pre.bindImm hx hv (asCtor_field_imm himm hview hm) st.counts
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact st.pre.bindBorrow hx hv (asCtor_field_canDup st.counts hview hm) st.counts
      · simp only [hk, ↓reduceIte] at hw; cases hw
  | prim op args =>
    obtain ⟨u, hneed, hΓ⟩ := except_bind_ok hc
    have hΓ := except_pure_ok hΓ
    subst hΓ
    have havail := Ctx.needArgs_avail hneed
    obtain ⟨vs, ws, hvs, hws, hds⟩ := needArgs_sem st.den havail
    simp only [Fir.evalRhs, hws] at hw
    obtain ⟨v, hres, hden, himm⟩ := primResult_immediate pins hds hw
    have hargs := primResult_args_immediate hds hw
    have hev : evalRhs { ctors := F.ctors, known := F.known } ρo H (.prim op args) = .ok (v, H) := by
      simp [evalRhs, Own.evalRhs, hvs, hres, Result.map]
    obtain ⟨owned', pre', hs'⟩ := st.pre.immArgs (primImmArgs op args.length) args (fun y hy => by
      refine ⟨havail y hy, ?_⟩
      obtain ⟨u, _, hu, _, _⟩ := st.den y (havail y hy)
      refine ⟨u, hu, ?_⟩
      exact hargs u (evalArgs_mem hvs hy hu))
    exact ⟨v, H, owned', hev, pre'.bindImm hx hden himm (hs'.balance st.counts), same⟩

end

end IxCC.Own.Plain
