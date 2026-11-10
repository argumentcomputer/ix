import IxCC.Lam.Erase.Proof.SimTerm

/-! # Application in the erasure simulation

Applying related values to related slots (`ApplySim`) at clock bound `m`,
given every lower bound: β enters a closure one clock down; a partial
application of a special head accumulates value slots, against its wrapper
global's closure that takes one more λ; the slot that saturates it fires
the head, against the wrapper's body over its binders. That body is the
head's saturated form over variables (`WrapR`): its `let`s rebind the
binders' values without a charge, so the firing meets the forms of the
saturated heads over the same slots, one clock after Lam's entry into the
closure. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)
open IxCC.Sem (Result ClockMono SimUpTo later later_succ)

/-- The wrapper's arguments: its binders' variables, in order. -/
abbrev wrapArgs (I : Input) (h : Head) (c : CId) (a : Nat) : List Src.Term.Arg :=
  (List.range a).map fun i => (Src.Term.var (a - 1 - i), Src.Mode.strict, wrapClass I h c i)

theorem wrapArgs_getElem? {I : Input} {h : Head} {c : CId} {a i : Nat} (hi : i < a) :
    (wrapArgs I h c a)[i]? = some (.var (a - 1 - i), .strict, wrapClass I h c i) := by
  simp [wrapArgs, hi]

theorem wrapClass_read {I : Input} {h : Head} {c : CId} {i : Nat} (hr : headReads I h i = true) :
    wrapClass I h c i = .rel := by
  simp [wrapClass, hr]

theorem rel_irrP (q : Profile) : Src.Rel.rel.irrP q = false := rfl

theorem mkApps_const_ne_var {c : CId} {us : List Ixon.Univ} {j : Nat} :
    ∀ args : List Src.Term.Arg, Src.Term.mkApps (.const c us) args ≠ .var j
  | [] => by simp [Src.Term.mkApps]
  | x :: xs => by
    obtain ⟨f, a, m, r, e⟩ := mkApps_app_or (h := .const c us) (x :: xs) (by simp)
    rw [e]; simp

section Vars

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

/-- An erasure of a variable. -/
theorem TR.var_inv {cx : Cx} {j : Nat} {v : Term} (h : TR I G cx (.var j) v) :
    (∃ l, cx.ctx[j]? = some (some l) ∧ v = cx.lvl l) ∨ (cx.ctx[j]? = some none ∧ v = .box) := by
  generalize e : Src.Term.var j = t at h
  cases h with
  | varSome hl => cases e; exact .inl ⟨_, hl, rfl⟩
  | varNone hl => cases e; exact .inr ⟨hl, rfl⟩
  | app _ hne _ _ =>
    obtain ⟨f, a, m, r, e'⟩ := mkApps_app_or _ hne
    rw [e'] at e; cases e
  | plain => exact absurd e.symm (mkApps_const_ne_var _)
  | variant => exact absurd e.symm (mkApps_const_ne_var _)
  | wrap => exact absurd e.symm (mkApps_const_ne_var _)
  | sat => exact absurd e.symm (mkApps_const_ne_var _)
  | _ => cases e

/-- Only values in a Lam environment. -/
def AllVals (ρ' : Env) : Prop := ∀ s' ∈ ρ', ∃ w, s' = .val w

/-- A variable bound to a value on both sides evaluates freely. -/
theorem var_value {P : Program} {cx : Cx} {j : Nat} {v : Term} (ht : TR I G cx (.var j) v)
    {ρ : Src.Env} {ρ' : Env} (he : EnvR I G cx ρ ρ') (hvals : AllVals ρ') :
    ∃ x x', ρ[j]? = some (.val x) ∧ (∀ k, Lam.eval P k ρ' v = .ok x') ∧ VR I G x x' := by
  rcases ht.var_inv with ⟨l, hl, rfl⟩ | ⟨hl, rfl⟩
  · obtain ⟨s, s', hs, hs', hss⟩ := he.er.get hl
    obtain ⟨w, rfl⟩ := hvals s' (List.mem_of_getElem? hs')
    cases hss with
    | val hv =>
      exact ⟨_, _, hs, fun k => by
        rw [Cx.lvl_eq, he.depth, Lam.eval_var_of P k ρ' hs', Lam.force_val], hv⟩
  · obtain ⟨s, hs, t, ρ₀, ls₀, rfl⟩ := he.er.getNone hl
    exact ⟨_, _, hs, fun k => Lam.eval_box' P k ρ', VR.irr⟩

/-- A by-name reference is a by-name argument. -/
theorem BindR.name_mode : ∀ {cx : Cx} {xs : List (Src.Term.Arg × Bool)} {lets : List Term}
    {refs : List Ref} {cx' : Cx}, BindR I G cx xs lets refs cx' →
      ∀ {j : Nat} {a : Src.Term}, refs[j]? = some (.name a) →
        ∃ r, xs[j]? = some ((a, .byName, r), true)
  | _, _, _, _, _, .nil, _, _, h => by simp at h
  | _, _, _, _, _, .irr _ _, 0, _, h => by simp at h
  | _, _, _, _, _, .irr _ hr, j + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact hr.name_mode h
  | _, _, _, _, _, .name _ _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Ref.name.injEq] at h
    subst h
    exact ⟨_, rfl⟩
  | _, _, _, _, _, .name _ hr, j + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact hr.name_mode h
  | _, _, _, _, _, .strict _ _ _, 0, _, h => by simp at h
  | _, _, _, _, _, .strict _ _ hr, j + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact hr.name_mode h

/-- Binding variables that hold values: the lets are free, and each
relevant argument's reference holds its variable's value. -/
theorem bind_vars {P : Program} {ls : Levels} (X : Term) :
    ∀ {cx : Cx} {xs : List (Src.Term.Arg × Bool)} {lets : List Term} {refs : List Ref}
      {cx' : Cx}, BindR I G cx xs lets refs cx' →
      (∀ x ∈ xs, ∃ jv r fl, x = ((.var jv, .strict, r), fl)) →
      ∀ {ρ : Src.Env} {ρ' : Env}, EnvR I G cx ρ ρ' → AllVals ρ' →
        ∃ ys : List Slot, AllVals ys ∧
          (∀ k, Lam.eval P k ρ' (wrapLets lets X) = Lam.eval P k (ys ++ ρ') X) ∧
          EnvR I G cx' ρ (ys ++ ρ') ∧
          ∀ (i jv : Nat) (r : Src.Rel) (fl : Bool) (ref : Ref),
            xs[i]? = some ((Src.Term.var jv, Src.Mode.strict, r), fl) → refs[i]? = some ref →
            r.irrP cx.prof = false →
            ∃ x, ρ[jv]? = some (Src.Slot.val x) ∧ RefSlot I G ls ρ (ys ++ ρ') ref (.val x)
  | _, _, _, _, _, .nil, _, ρ, ρ', he, _ =>
    ⟨[], fun _ h => by simp at h, fun _ => rfl, he, fun i _ _ _ _ h => by simp at h⟩
  | _, _, _, _, _, .irr hr hrest, hvars, ρ, ρ', he, hvals => by
    obtain ⟨ys, hy, hev, he', hrefs⟩ :=
      bind_vars X hrest (fun x hx => hvars x (List.mem_cons_of_mem _ hx)) he hvals
    refine ⟨ys, hy, hev, he', fun i jv r fl ref hx href hirr => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨⟨_, _, rfl⟩, _⟩ := hx
      rw [hr] at hirr
      cases hirr
    | succ i =>
      simp only [List.getElem?_cons_succ] at hx href
      exact hrefs i jv r fl ref hx href hirr
  | _, _, _, _, _, .name _ _, hvars, _, _, _, _ => by
    obtain ⟨jv, r, fl, e⟩ := hvars _ List.mem_cons_self
    simp only [Prod.mk.injEq] at e
    obtain ⟨⟨_, e, _⟩, _⟩ := e
    cases e
  | cx, _, _, _, _, .strict (a := a) (r := r₀) (v := v) hr ha hrest, hvars, ρ, ρ', he,
      hvals => by
    obtain ⟨jv₀, r', fl', e⟩ := hvars _ List.mem_cons_self
    simp only [Prod.mk.injEq] at e
    obtain ⟨⟨rfl, _, rfl⟩, _⟩ := e
    obtain ⟨x, x', hx, hev₀, hxv⟩ := var_value (P := P) ha he hvals
    have hvals' : AllVals (.val x' :: ρ') := by
      intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact ⟨_, rfl⟩
      · exact hvals s hs
    obtain ⟨ys, hy, hev, he', hrefs⟩ :=
      bind_vars X hrest (fun x hx => hvars x (List.mem_cons_of_mem _ hx)) (he.extra1 (.val x'))
        hvals'
    have e : (ys ++ [Slot.val x']) ++ ρ' = ys ++ (Slot.val x' :: ρ') := by simp
    refine ⟨ys ++ [.val x'], ?_, fun k => ?_, by rw [e]; exact he', ?_⟩
    · intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · exact hy s hs
      · simp at hs; exact ⟨_, hs⟩
    · rw [eval_wrapLets_cons, hev₀, Sem.Result.bind_ok, hev k, e]
    · intro i jv r fl ref hxi href hirr
      rw [e]
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hxi href
        obtain ⟨⟨hj, _, _⟩, _⟩ := hxi
        cases hj
        subst href
        refine ⟨x, hx, (RefSlot.lvl (by simp [he.depth]) (by simp [he.depth]) hxv).extend ys⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hxi href
        exact hrefs i jv r fl ref hxi href hirr

/-- A variable argument holding a value, relevant at `q`. -/
def VarVal (ρ : Src.Env) (q : Profile) (a : Src.Term.Arg) (x : Src.Value) : Prop :=
  ∃ jv r, a = (.var jv, .strict, r) ∧ r.irrP q = false ∧ ρ[jv]? = some (.val x)

/-- A primitive's variable arguments. -/
theorem args_vars {P : Program} :
    ∀ {cx : Cx} {args : List Src.Term.Arg} {args' : List (Term × Mode)}, ArgsR I G cx args args' →
      ∀ {ρ : Src.Env} {ρ' : Env}, EnvR I G cx ρ ρ' → AllVals ρ' →
        ∀ {xs : List Src.Value}, Forall2 (VarVal ρ cx.prof) args xs →
          ∃ vs, (∀ k, Lam.evalList P k ρ' (args'.map (·.1)) = .ok vs) ∧ Forall2 (VR I G) xs vs
  | _, _, _, .nil, _, _, _, _, _, .nil => ⟨[], fun k => Lam.evalList_nil P k _, .nil⟩
  | _, _, _, .irr hr _, _, _, _, _, _, .cons ⟨_, _, e, hirr, _⟩ _ => by
    simp only [Prod.mk.injEq] at e
    obtain ⟨_, _, rfl⟩ := e
    rw [hr] at hirr; cases hirr
  | _, _, _, .strict _ ha hrest, ρ, ρ', he, hvals, _, .cons ⟨jv, r, e, _, hj⟩ hxs => by
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, _, rfl⟩ := e
    obtain ⟨x, x', hx, hev, hxv⟩ := var_value (P := P) ha he hvals
    rw [hx] at hj
    cases hj
    obtain ⟨vs, hevs, hvs⟩ := args_vars hrest he hvals hxs
    exact ⟨x' :: vs, fun k => by
      rw [List.map_cons, Lam.evalList_cons, hev, Sem.Result.bind_ok, hevs, Sem.Result.bind_ok],
      .cons hxv hvs⟩

/-- A constructor's variable fields. -/
theorem fields_vars {P : Program} :
    ∀ {cx cx' : Cx} {c : CId} {q : Profile} {j : Nat} {args : List Src.Term.Arg}
      {fs : List Term}, FieldsR I G cx cx' c q j args fs →
      ∀ {ρ : Src.Env} {ρ'' : Env}, EnvR I G cx' ρ ρ'' → AllVals ρ'' → cx'.prof = cx.prof →
        ∀ {xs : List Src.Value}, Forall2 (VarVal ρ cx.prof) args xs →
          ∃ vs, (∀ k, Lam.evalList P k ρ'' fs = .ok vs) ∧ KeptR I G c j xs vs ∧
            vs.length = fs.length
  | _, _, _, _, _, _, _, .nil, _, _, _, _, _, _, .nil =>
    ⟨[], fun k => Lam.evalList_nil P k _, .nil, rfl⟩
  | _, _, _, _, _, _, _, .keptIrr _ hr _, _, _, _, _, hp, _, .cons ⟨_, _, e, hirr, _⟩ _ => by
    simp only [Prod.mk.injEq] at e
    obtain ⟨_, _, rfl⟩ := e
    rw [hp, hirr] at hr; cases hr
  | _, _, c, q, j, _, _, .keptRel hk _ ha hrest, ρ, ρ'', he, hvals, hp, _,
      .cons ⟨jv, r, e, _, hj⟩ hxs => by
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, _, rfl⟩ := e
    obtain ⟨x, x', hx, hev, hxv⟩ := var_value (P := P) ha he hvals
    rw [hx] at hj
    cases hj
    obtain ⟨vs, hevs, hvs, hl⟩ := fields_vars hrest he hvals hp hxs
    have hk' : I.kept c [] j = true := by rw [← Input.kept_prof I c q j]; exact hk
    exact ⟨x' :: vs, fun k => by
      rw [Lam.evalList_cons, hev, Sem.Result.bind_ok, hevs, Sem.Result.bind_ok],
      .kept hk' hxv hvs, by simp [hl]⟩
  | _, _, _, _, _, _, _, .drop _ hr _, _, _, _, _, _, _, .cons ⟨_, _, e, hirr, _⟩ _ => by
    simp only [Prod.mk.injEq] at e
    obtain ⟨_, _, rfl⟩ := e
    rw [hirr] at hr; cases hr

/-- The wrapper's context: its binders hold the argument values. -/
theorem wrapEnv (q : Profile) {xs : List Src.Value} {vs : List Val}
    (h : Forall2 (VR I G) xs vs) :
    EnvR I G (wrapCx q xs.length) (xs.map .val).reverse (vs.reverse.map .val) where
  er := by
    have hl := h.length
    have hf : Forall2 (SlotAt I G (vs.reverse.map .val)) ((List.range xs.length).map some)
        (xs.map .val) := by
      refine Forall2.of_getElem (by simp) fun i o s ho hs => ?_
      simp only [List.getElem?_map, Option.map_eq_some_iff] at ho hs
      obtain ⟨i', hi', rfl⟩ := ho
      obtain ⟨rfl, hi⟩ := range_getElem?_eq_some hi'
      obtain ⟨x, hx, rfl⟩ := hs
      obtain ⟨v, hv, hxv⟩ := h.get hx
      refine .lvl (by simp; omega) ?_ (.val hxv)
      rw [List.getElem?_map, List.getElem?_reverse (by simp; omega)]
      simp only [List.length_reverse, List.length_map]
      rw [show vs.length - 1 - (vs.length - 1 - i) = i by omega, hv]
      rfl
    have := ER.prependAt hf.reverse (ER.nil (I := I) (G := G) (ρ' := vs.reverse.map .val))
    simpa [wrapCx, List.map_reverse] using this
  depth := by simp [wrapCx, h.length]
  minors := fun _ _ _ _ hl _ => by simp [wrapCx] at hl
  minorsLt := fun _ he => by simp [wrapCx] at he

theorem allVals_rev (vs : List Val) : AllVals (vs.reverse.map .val) := by
  intro s hs
  simp only [List.mem_map] at hs
  obtain ⟨w, _, rfl⟩ := hs
  exact ⟨w, rfl⟩

/-- The wrapper's variable for binder `i` holds argument `i`. -/
theorem wrap_var {xs : List Src.Value} {i : Nat} (hi : i < xs.length) :
    (xs.map Src.Slot.val).reverse[xs.length - 1 - i]? = some (.val xs[i]) := by
  rw [List.getElem?_reverse (by simp; omega)]
  simp only [List.length_map]
  rw [show xs.length - 1 - (xs.length - 1 - i) = i by omega]
  simp [hi]

theorem allVals_append {ys zs : Env} (hy : AllVals ys) (hz : AllVals zs) : AllVals (ys ++ zs) :=
  fun s hs => (List.mem_append.1 hs).elim (hy s) (hz s)

theorem wrapArgs_mem {h : Head} {c : CId} {a : Nat} {x : Src.Term.Arg}
    (hx : x ∈ wrapArgs I h c a) : ∃ jv r, x = (Src.Term.var jv, Src.Mode.strict, r) := by
  simp only [wrapArgs, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact ⟨_, _, rfl⟩

theorem forceAll_vals (p : Src.Program) (k : Nat) :
    ∀ xs : List Src.Value, Src.forceAll p k (xs.map .val) = .ok xs
  | [] => Src.forceAll_nil p k
  | x :: xs => by
    rw [List.map_cons, Src.forceAll_cons, Src.force_val, Sem.Result.bind_ok, forceAll_vals p k xs,
      Sem.Result.bind_ok]

/-- The wrapper's arguments from `n` on, where the head reads them, hold
the argument values. -/
theorem wrap_varVals {h : Head} {c : CId} {q : Profile} {xs : List Src.Value} {n : Nat}
    (hread : ∀ i, n ≤ i → i < xs.length → headReads I h i = true) :
    Forall2 (VarVal (xs.map .val).reverse q) ((wrapArgs I h c xs.length).drop n) (xs.drop n) := by
  refine Forall2.of_getElem (by simp) fun i y x hy hx => ?_
  simp only [List.getElem?_drop] at hy hx
  have hi : n + i < xs.length := lt_of_getElem?_eq_some hx
  rw [wrapArgs_getElem? hi] at hy
  cases hy
  refine ⟨_, _, rfl, by rw [wrapClass_read (hread _ (by omega) hi)]; rfl, ?_⟩
  rw [wrap_var hi]
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hx
  rw [hx]

theorem ValsR.to_forall2 : ∀ {args : List Src.Slot} {vs : List Val}, ValsR I G args vs →
    ∃ xs, args = xs.map .val ∧ Forall2 (VR I G) xs vs
  | _, _, .nil => ⟨[], rfl, .nil⟩
  | _, _, .cons hv hr => by
    obtain ⟨xs, rfl, h⟩ := ValsR.to_forall2 hr
    exact ⟨_ :: xs, rfl, .cons hv h⟩

theorem ValsR.of_forall2 : ∀ {xs : List Src.Value} {vs : List Val}, Forall2 (VR I G) xs vs →
    ValsR I G (xs.map .val) vs
  | _, _, .nil => .nil
  | _, _, .cons hv hr => .cons hv (ValsR.of_forall2 hr)

/-- Binding the wrapper's variables (the first `n` of them): the lets are
free, and the references hold the argument values where the head reads. -/
theorem wrap_bind {P : Program} {h : Head} {c : CId} {q : Profile} {n : Nat}
    {xs' : List (Src.Term.Arg × Bool)} {lets : List Term} {refs : List Ref} {cx' : Cx}
    {xs : List Src.Value} {vs : List Val} (hxv : Forall2 (VR I G) xs vs)
    (hb : BindR I G (wrapCx q xs.length) xs' lets refs cx')
    (hfst : xs'.map (·.1) = (wrapArgs I h c xs.length).take n) (ls : Levels) (X : Term) :
    ∃ ys, (∀ k, Lam.eval P k (vs.reverse.map .val) (wrapLets lets X) =
        Lam.eval P k (ys ++ vs.reverse.map .val) X) ∧
      EnvR I G cx' (xs.map .val).reverse (ys ++ vs.reverse.map .val) ∧
      AllVals (ys ++ vs.reverse.map .val) ∧
      FormArgs I G h ls (xs.map .val).reverse (ys ++ vs.reverse.map .val) refs
        ((xs.map .val).take n) ∧
      (∀ i a, refs.getD i .box ≠ .name a) ∧ cx'.prof = q ∧ cx'.minors = [] := by
  have hvars : ∀ x ∈ xs', ∃ jv r fl, x = ((Src.Term.var jv, Src.Mode.strict, r), fl) := by
    intro x hx
    have hm : x.1 ∈ xs'.map (·.1) := List.mem_map_of_mem hx
    rw [hfst] at hm
    obtain ⟨jv, r, e⟩ := wrapArgs_mem (List.mem_of_mem_take hm)
    exact ⟨jv, r, x.2, by rw [← e]⟩
  obtain ⟨ys, hy, hev, he', hrefs⟩ :=
    bind_vars (P := P) (ls := ls) X hb hvars (wrapEnv q hxv) (allVals_rev vs)
  have hcx := hb.cx_eq
  have hlx : xs'.length = min n xs.length := by
    have := congrArg List.length hfst
    simpa using this
  refine ⟨ys, hev, he', allVals_append hy (allVals_rev vs), ⟨?_, ?_⟩, ?_, by rw [hcx]; rfl,
    by rw [hcx]; rfl⟩
  · simp only [List.length_take, List.length_map, hb.refs_length, hlx]
  · intro i ref s hr hs hread
    have hi : i < n ∧ i < xs.length := by
      have := lt_of_getElem?_eq_some hs
      simp only [List.length_take, List.length_map] at this
      omega
    obtain ⟨⟨y, fl⟩, hyi⟩ : ∃ p, xs'[i]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hy' : y = (Src.Term.var (xs.length - 1 - i), Src.Mode.strict, Src.Rel.rel) := by
      have := congrArg (·[i]?) hfst
      simp only [List.getElem?_map, hyi, Option.map_some, List.getElem?_take, hi.1,
        ↓reduceIte, wrapArgs_getElem? hi.2, Option.some.injEq] at this
      rw [this, wrapClass_read hread]
    subst hy'
    obtain ⟨x, hjx, hrs⟩ := hrefs i _ _ fl ref hyi hr (rel_irrP _)
    rw [wrap_var hi.2, Option.some.injEq, Src.Slot.val.injEq] at hjx
    subst hjx
    have hs' : s = .val xs[i] := by
      simp only [List.getElem?_take, hi.1, ↓reduceIte, List.getElem?_map,
        List.getElem?_eq_getElem hi.2, Option.map_some, Option.some.injEq] at hs
      exact hs.symm
    rw [hs']
    exact hrs
  · intro i a e
    have hi : i < refs.length := by
      refine Nat.lt_of_not_le fun hge => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at e
      cases e
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at e
    obtain ⟨r, hx⟩ := hb.name_mode (by rw [List.getElem?_eq_getElem hi]; simpa using e)
    obtain ⟨jv, r', fl, e'⟩ := hvars _ (List.mem_of_getElem? hx)
    simp only [Prod.mk.injEq] at e'
    obtain ⟨⟨_, e', _⟩, _⟩ := e'
    cases e'

/-- The evaluated binders of a wrapper, in order. -/
theorem evalList_lvls (P : Program) (k : Nat) (q : Profile) (vs : List Val) :
    Lam.evalList P k (vs.reverse.map .val)
      ((List.range vs.length).map fun i => (wrapCx q vs.length).lvl i) = .ok vs := by
  suffices h : ∀ (n : Nat), n ≤ vs.length →
      Lam.evalList P k (vs.reverse.map .val)
        ((List.range' (vs.length - n) n).map fun i => (wrapCx q vs.length).lvl i) =
        .ok (vs.drop (vs.length - n)) by
    have := h vs.length (Nat.le_refl _)
    simpa [List.range_eq_range'] using this
  intro n
  induction n with
  | zero => intro _; simp [Lam.evalList_nil]
  | succ n ih =>
    intro hn
    have e : vs.length - (n + 1) + 1 = vs.length - n := by omega
    rw [List.range'_succ, List.map_cons, Lam.evalList_cons, e, ih (by omega)]
    have hlt : vs.length - (n + 1) < vs.length := by omega
    have hv : (vs.reverse.map Slot.val)[vs.length - 1 - (vs.length - (n + 1))]? =
        some (.val vs[vs.length - (n + 1)]) := by
      rw [List.getElem?_map, List.getElem?_reverse (by omega)]
      simp only [show vs.length - 1 - (vs.length - 1 - (vs.length - (n + 1))) =
        vs.length - (n + 1) by omega, List.getElem?_eq_getElem hlt, Option.map_some]
    rw [Cx.lvl_eq, show (wrapCx q vs.length).depth = vs.length from rfl,
      Lam.eval_var_of P k _ hv, Lam.force_val, Sem.Result.bind_ok, Sem.Result.bind_ok]
    congr 1
    rw [← List.getElem_cons_drop hlt, e]

theorem lams_inj : ∀ (ms : List Mode) {a b : Term}, Term.lams ms a = Term.lams ms b → a = b
  | [], _, _, h => h
  | m :: ms, _, _, h => by
    simp only [Term.lams, List.foldr_cons, Term.lam.injEq, true_and] at h
    exact lams_inj ms h

end Vars

namespace Setting

section

variable {S : Setting} (wf : ProgWF S.I) {m : Nat} (hlt : ∀ m' < m, S.Level m')
include wf hlt

/-- A wrapper's body on its binders' values against the head fired on the
same values. -/
theorem wrap_sat {h : Head} {c : CId} {q : Profile} {body : Term} (hh : S.I.headOf c = some h)
    (hnp : ∀ op, h ≠ .prim op) {xs : List Src.Value} {vs : List Val}
    (hxv : Forall2 (VR S.I S.G) xs vs)
    (hsat : SatR S.I S.G (wrapCx q xs.length) h q (wrapArgs S.I h c xs.length) body)
    (hlen : xs.length = headArity S.I h) {ls : Levels} (hag : Agree ls q) :
    SimUpTo (VR S.I S.G) m (fun k => Src.fire S.p k h ls (xs.map .val))
      (fun k => Lam.eval S.L k (vs.reverse.map .val) body) := by
  generalize hargs : wrapArgs S.I h c xs.length = args at hsat
  generalize hcx : wrapCx q xs.length = cx at hsat
  cases hsat with
  | prim _ => exact absurd rfl (hnp _)
  | @natZero _ c' _ _ _ _ _ _ _ _ _ hd hz =>
    obtain ⟨_, _, _, _, _, hdz⟩ := wf.zeroPin hz
    rw [hd] at hdz
    cases hdz
    simp only [headArity, hd, Nat.add_zero, List.length_eq_zero_iff] at hlen
    subst hlen
    refine (SimUpTo.ok VR.lit).congr (fun k => ?_) (fun k => Lam.eval_lit S.L k _ _)
    have e : Src.fire S.p k (.ctor c') ls (([] : List Src.Value).map Src.Slot.val) =
        Src.fire S.p k (.ctor c') ls ([] ++ []) := rfl
    rw [e, S.fire_ctor_split hd k ls rfl [], Src.forceAll_nil, Sem.Result.bind_ok,
      S.ctorResult_zero hz]
  | @natSucc _ _ c' _ _ _ _ _ _ np nf _ _ _ fs hd hz hs hbind hargsR =>
    subst hargs hcx
    have hlen' : xs.length = np + nf := by simpa [headArity, hd] using hlen
    obtain ⟨ys, hev, he', hav, _, _, hprof, _⟩ := wrap_bind (P := S.L) (n := np) hxv hbind
      (by rw [map_fst_pair]) ls (.prim .natAdd (fs.map (·.1) ++ [.lit (.nat 1)]))
    obtain ⟨vsF, hevF, hF⟩ := args_vars (P := S.L) hargsR he' hav (xs := xs.drop np)
      (by rw [hprof]; exact wrap_varVals fun i hi _ => by simp [headReads, hd, hi])
    have hsrc : ∀ k, Src.fire S.p k (.ctor c') ls (xs.map .val) =
        Src.ctorResult S.p c' ls ((xs.map .val).take np) (xs.drop np) := fun k => by
      conv => lhs; rw [← List.take_append_drop np (xs.map Src.Slot.val)]
      rw [S.fire_ctor_split hd k ls (by simp; omega), ← List.map_drop, forceAll_vals,
        Sem.Result.bind_ok]
    have hlam : ∀ k, Lam.eval S.L k (vs.reverse.map .val)
        (wrapLets _ (.prim .natAdd (fs.map (·.1) ++ [.lit (.nat 1)]))) =
        Lam.primResult S.L.known .natAdd (vsF ++ [.lit (.nat 1)]) := fun k => by
      rw [hev k, Lam.eval_prim, evalList_append_single, hevF k, Sem.Result.bind_ok,
        Lam.eval_lit, Sem.Result.bind_ok, Sem.Result.bind_ok]
    by_cases hx : ∃ n, xs.drop np = [.lit n]
    · obtain ⟨n, hn⟩ := hx
      rw [hn] at hF
      cases hF with
      | cons hv hr =>
        cases hr
        cases hv
        exact (SimUpTo.ok VR.lit).congr (fun k => by rw [hsrc, hn, S.ctorResult_succ hz hs])
          (fun k => by rw [hlam]; exact primResult_succ _ n)
    · exact (SimUpTo.stuck _).congr
        (fun k => by rw [hsrc, S.ctorResult_succ_stuck hz hs ls _ fun n e => hx ⟨n, e⟩])
        (fun k => rfl)
  | @ctorUnbox _ _ c' _ _ _ _ ind _ np nf _ _ _ f _ hd hz hs hbind hfields hu =>
    subst hargs hcx
    have hlen' : xs.length = np + nf := by simpa [headArity, hd] using hlen
    obtain ⟨ys, hev, he', hav, _, _, hprof, _⟩ := wrap_bind (P := S.L) (n := np) hxv hbind
      (by rw [map_fst_pair]) ls f
    obtain ⟨vsF, hevF, hkr, hlF⟩ := fields_vars (P := S.L) hfields he' hav (by rw [hprof]; rfl)
      (xs := xs.drop np) (wrap_varVals fun i hi _ => by simp [headReads, hd, hi])
    match vsF, hlF, hevF, hkr with
    | [v'], _, hevF, hkr =>
      refine (SimUpTo.ok (vr_unboxed wf hd (by rw [← Input.unbox?_prof S.I ind _]; exact hu)
        (ls := ls) (ps := (xs.map .val).take np) (by simp; omega) hkr)).congr (fun k => ?_)
        (fun k => ?_)
      · conv => lhs; rw [← List.take_append_drop np (xs.map Src.Slot.val)]
        rw [S.fire_ctor_split hd k ls (by simp; omega), ← List.map_drop, forceAll_vals,
          Sem.Result.bind_ok, S.ctorResult_con hz hs]
      · rw [hev k, eval_evalList_single, hevF k, Sem.Result.bind_ok]
        rfl
  | @ctorBox _ _ c' _ _ _ _ ind _ np nf _ _ _ fields hd hz hs hbind
      hfields hu =>
    subst hargs hcx
    have hlen' : xs.length = np + nf := by simpa [headArity, hd] using hlen
    obtain ⟨ys, hev, he', hav, _, _, hprof, _⟩ := wrap_bind (P := S.L) (n := np) hxv hbind
      (by rw [map_fst_pair]) ls (.con (S.I.ctorKey c') fields)
    obtain ⟨vsF, hevF, hkr, _⟩ := fields_vars (P := S.L) hfields he' hav (by rw [hprof]; rfl)
      (xs := xs.drop np) (wrap_varVals fun i hi _ => by simp [headReads, hd, hi])
    refine (SimUpTo.ok (VR.con (ls := ls) (ps := (xs.map .val).take np) hd (by simp; omega)
      (by rw [← Input.unbox?_prof S.I ind _]; exact hu) hkr)).congr (fun k => ?_) (fun k => ?_)
    · conv => lhs; rw [← List.take_append_drop np (xs.map Src.Slot.val)]
      rw [S.fire_ctor_split hd k ls (by simp; omega), ← List.map_drop, forceAll_vals,
        Sem.Result.bind_ok, S.ctorResult_con hz hs]
    · rw [hev k, Lam.eval_con, hevF k, Sem.Result.bind_ok]
  | @quotMk _ _ c' _ _ _ _ e hbind hre =>
    subst hargs hcx
    obtain ⟨lv, ty, hq⟩ := S.headOf_quotMk hh
    have hl3 : xs.length = 3 := by simpa [headArity] using hlen
    obtain ⟨ys, hev, he', _, hfa, hnn, hprof, _⟩ := wrap_bind (P := S.L) (n := xs.length) hxv
      hbind (by rw [map_fst_pair, List.take_of_length_le (by simp)]) ls e
    rw [List.take_of_length_le (by simp)] at hfa
    obtain ⟨x₀, x₁, x₂, rfl⟩ : ∃ a b d, xs = [a, b, d] := by
      match xs, hl3 with
      | [a, b, d], _ => exact ⟨a, b, d, rfl⟩
    exact (S.quotMk_form hq he'.depth (S.formArgs_getD hfa (i := 2) (by simp)
      (by simp [headReads])) hre (hnn 2)).congr (fun k => rfl) (fun k => hev k)
  | @quotLift _ _ c' _ _ _ _ f x hbind hrf hrq =>
    subst hargs hcx
    have hl6 : xs.length = 6 := by simpa [headArity] using hlen
    obtain ⟨ys, hev, he', _, hfa, hnn, hprof, _⟩ := wrap_bind (P := S.L) (n := xs.length) hxv
      hbind (by rw [map_fst_pair, List.take_of_length_le (by simp)]) ls
      (.tick (.app f x .strict))
    rw [List.take_of_length_le (by simp)] at hfa
    obtain ⟨x₀, x₁, x₂, x₃, x₄, x₅, rfl⟩ : ∃ a b d e g i, xs = [a, b, d, e, g, i] := by
      match xs, hl6 with
      | [a, b, d, e, g, i], _ => exact ⟨a, b, d, e, g, i, rfl⟩
    exact (quotLift_form hlt he'.depth (S.formArgs_getD hfa (i := 3) (by simp)
      (by simp [headReads])) hrf (hnn 3) (S.formArgs_getD hfa (i := 5) (by simp)
      (by simp [headReads])) hrq (hnn 5)).congr (fun k => rfl) (fun k => hev k)
  | @casesEmpty _ _ c' r _ _ _ _ _ _ _ _ _ _ _ _ _ _ hres hd hbind hk =>
    subst hargs hcx
    obtain ⟨ys, hev, _, _, _, _, _, _⟩ := wrap_bind (P := S.L) (n := xs.length) hxv hbind
      (by rw [map_fst_zipIdx _ (fun ⟨_, _⟩ => rfl), List.take_of_length_le (by simp)]) ls
      (.tick .trap)
    exact (cases_empty_form (S := S) (m := m) (ρ'' := ys ++ vs.reverse.map .val) hres hd hk hag
      (xs.map .val)).congr (fun k => rfl) (fun k => hev k)
  | @casesSub _ _ c' r _ _ _ _ _ np _ nmin ni _ _ _ _ _ _ _ body' hres hd
      hbind hk hbody =>
    subst hargs hcx
    have hl : xs.length = np + 1 + ni + 1 + nmin := by simpa [headArity, hres, hd] using hlen
    obtain ⟨ys, hev, he', _, hfa, hnn, hprof, hmin⟩ := wrap_bind (P := S.L) (n := xs.length) hxv
      hbind (by rw [map_fst_zipIdx _ (fun ⟨_, _⟩ => rfl), List.take_of_length_le (by simp)]) ls
      (.tick body')
    rw [List.take_of_length_le (by simp)] at hfa
    exact (cases_sub_form wf hlt hres hd hk he' (by rw [hprof]; exact hag) hag hfa
      (by simpa using hl) (fun i _ a => hnn i a) (fun i l _ sig => by rw [hmin]; simp)
      (wf.subMinor hd (S.kindAt_sub hk)) hbody).congr (fun k => rfl) (fun k => hev k)
  | @casesUnbox _ _ c' r _ _ _ _ _ np _ nmin ni _ _ _ _ _ l _ body' hres
      hd hbind hk hl hu hbody =>
    subst hargs hcx
    have hlc : xs.length = np + 1 + ni + 1 + nmin := by simpa [headArity, hres, hd] using hlen
    obtain ⟨ys, hev, he', _, hfa, _, hprof, hmin⟩ := wrap_bind (P := S.L) (n := xs.length) hxv
      hbind (by rw [map_fst_zipIdx _ (fun ⟨_, _⟩ => rfl), List.take_of_length_le (by simp)]) ls
      (.tick body')
    rw [List.take_of_length_le (by simp)] at hfa
    exact (cases_unbox_form wf hlt hres hd hk hu he' (by rw [hprof]; exact hag) hag hfa
      (by simpa using hlc) hl (fun sig => by rw [hmin]; simp)
      hbody).congr (fun k => rfl) (fun k => hev k)
  | @casesOrd _ cx' c' r _ _ _ _ _ np _ nmin ni _ _ _ _ _ l alts hres
      hd hbind hk hl hu halts =>
    subst hargs hcx
    have hlc : xs.length = np + 1 + ni + 1 + nmin := by simpa [headArity, hres, hd] using hlen
    obtain ⟨ys, hev, he', _, hfa, _, hprof, _⟩ := wrap_bind (P := S.L) (n := xs.length) hxv
      hbind (by rw [map_fst_zipIdx _ (fun ⟨_, _⟩ => rfl), List.take_of_length_le (by simp)]) ls
      (.tick (.case (cx'.lvl l) alts none))
    rw [List.take_of_length_le (by simp)] at hfa
    exact (cases_ord_form wf hlt hres hd hk hu he' (by rw [hprof]; exact hag) hag hfa
      (by simpa using hlc) hl halts).congr (fun k => rfl) (fun k => hev k)
  | @recr _ _ r _ _ _ _ _ np nmot nmin ni _ _ _ _ _ g argTerms
      hd hbind _ hargsR hg =>
    subst hargs hcx
    have hlr : xs.length = np + nmot + nmin + ni + 1 := by simpa [headArity, hd] using hlen
    obtain ⟨ys, hev, he', _, hfa, hnn, hprof, _⟩ := wrap_bind (P := S.L) (n := xs.length) hxv
      hbind (by rw [map_fst_zipIdx _ (fun ⟨_, _⟩ => rfl), List.take_of_length_le (by simp)]) ls
      (Term.apps (.glob g) argTerms)
    rw [List.take_of_length_le (by simp)] at hfa
    refine (recr_form wf hlt hd he' (by rw [hprof]; exact hag) hag hfa (by simpa using hlr)
      (fun j a _ e => ?_) hargsR hg).congr (fun k => rfl) (fun k => hev k)
    have hj : j < _ := lt_of_getElem?_eq_some e
    exact hnn j a (by rw [List.getD_eq_getElem?_getD, e]; rfl)

/-- The head fired on the values of a saturating application, against its
wrapper's body. -/
theorem wrap_fire {h : Head} {q : Profile} {inner : Term}
    (hw : WrapR S.I S.G h q (Term.lams (List.replicate (headArity S.I h) .strict) inner))
    {ls : Levels} (hag : Agree ls q) {xs : List Src.Value} {vs : List Val}
    (hxv : Forall2 (VR S.I S.G) xs vs) (hlen : xs.length = headArity S.I h) :
    SimUpTo (VR S.I S.G) m (fun k => Src.fire S.p k h ls (xs.map .val))
      (fun k => Lam.eval S.L k (vs.reverse.map .val) inner) := by
  generalize e : Term.lams (List.replicate (headArity S.I h) .strict) inner = B at hw
  cases hw with
  | @prim op hop =>
    subst hop
    have hi := lams_inj _ e
    subst hi
    have hvl : vs.length = headArity S.I (.prim op) := by rw [← hxv.length, hlen]
    refine (prim_value_sim wf op hxv).congr (fun k => ?_) (fun k => ?_)
    · rw [Src.fire_prim, forceAll_vals, Sem.Result.bind_ok]
    · rw [Lam.eval_prim, ← hvl, evalList_lvls, Sem.Result.bind_ok]
  | @other c body hcls hhead hsat =>
    have hi : inner = body := lams_inj _ e
    subst hi
    have hnp : ∀ op, h ≠ .prim op := by
      intro op hop
      subst hop
      rcases hcls with h' | h' | h' | h' | h' <;> cases h'
    have hsat' : SatR S.I S.G (wrapCx q xs.length) h q (wrapArgs S.I h c xs.length) inner := by
      rw [hlen]; exact hsat
    exact wrap_sat wf hlt hhead hnp hxv hsat' hlen hag

/-- Applying related values to related slots, at clock bound `m`. -/
theorem apply_sim : S.ApplySim m := by
  intro f f' s s' hf hs happ
  have hstuck : ∀ (hc : ∀ b d body ρ' ls', f ≠ .clo b d body ρ' ls')
      (hp : ∀ h ls' args, f ≠ .pap h ls' args),
      SimUpTo (VR S.I S.G) m (fun k => Src.apply S.p k f s) (fun k => Lam.apply S.L k f' s') :=
    fun hc hp => (SimUpTo.stuck _).congr (fun k => Src.apply_other S.p k f s hc hp) (fun _ => rfl)
  cases hf with
  | lit => exact hstuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  | str => exact hstuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  | irr => exact hstuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  | quot => exact hstuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  | unboxed => exact hstuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  | con => exact hstuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  | clo her hd hmo hml hag ht =>
    exact S.apply_clo_sim (fun m' h => (hlt m' h).tr) (VR.clo her hd hmo hml hag ht) hs
  | @pap h ls _ q inner vs hw hag hlt' hvals =>
    obtain ⟨v, v', rfl, rfl⟩ : ∃ v v', s = .val v ∧ s' = .val v' := by
      rcases happ with ⟨_, _, _, _, _, e⟩ | ⟨v, v', e₁, e₂⟩
      · cases e
      · exact ⟨v, v', e₁, e₂⟩
    have hvv : VR S.I S.G v v' := by cases hs with | val h => exact h
    obtain ⟨xs, rfl, hxv⟩ := ValsR.to_forall2 hvals
    have hn : xs.length < headArity S.I h := by simpa using hlt'
    have hxv' : Forall2 (VR S.I S.G) (xs ++ [v]) (vs ++ [v']) := hxv.append (.cons hvv .nil)
    have hvl : vs.length = xs.length := hxv.length.symm
    have happ' : ∀ k, Src.apply S.p k (.pap h ls (xs.map .val)) (.val v) =
        if (xs.length + 1 == headArity S.I h) = true then
          Src.fire S.p k h ls ((xs ++ [v]).map .val)
        else if xs.length + 1 < headArity S.I h then .ok (.pap h ls ((xs ++ [v]).map .val))
        else .stuck := fun k => by
      rw [Src.apply_pap, ← headArity_eq S.p S.ch]
      simp
    have hrev : (vs ++ [v']).reverse.map Slot.val = .val v' :: vs.reverse.map .val := by simp
    by_cases hsat : xs.length + 1 = headArity S.I h
    · have hz : headArity S.I h - 1 - xs.length = 0 := by omega
      refine (SimUpTo.laterR (Lam.eval_mono S.L _ _)
        (wrap_fire wf hlt hw hag hxv' (by simp; omega))).congr (fun k => ?_)
        (fun k => ?_)
      · rw [happ' k]
        simp [hsat]
      · rw [Lam.apply_clos, List.length_map, hz, List.replicate_zero, hrev]
        cases k <;> rfl
    · have hlt2 : xs.length + 1 < headArity S.I h := by omega
      have hpap : VR S.I S.G (.pap h ls ((xs ++ [v]).map .val))
          (.clos ((vs ++ [v']).reverse.map .val)
            (Term.lams (List.replicate (headArity S.I h - 1 - ((xs ++ [v]).map Src.Slot.val).length)
              .strict) inner)) :=
        VR.pap hw hag (by simp; omega) (ValsR.of_forall2 hxv')
      refine (SimUpTo.laterR (ClockMono.const _) (SimUpTo.ok hpap)).congr (fun k => ?_)
        (fun k => ?_)
      · rw [happ' k]
        have hne : (xs.length + 1 == headArity S.I h) = false := by simp; omega
        simp [hne, hlt2]
      · rw [Lam.apply_clos, List.length_map, hrev]
        have e : headArity S.I h - 1 - xs.length =
            (headArity S.I h - 1 - ((xs ++ [v]).map Src.Slot.val).length) + 1 := by simp; omega
        rw [e, List.replicate_succ]
        cases k with
        | zero => rfl
        | succ k => exact Lam.eval_lams_cons S.L k _ _ _ _

end

end Setting

end IxCC.Lam.Erase.Proof
