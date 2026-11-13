import IxCC.Src.Relevance.Proof.P1.CaseKey
import IxCC.Src.Relevance.Proof.P1.Plumbing
import IxCC.Src.Relevance.Proof.P1.Recr

/-! # P1, relevance preservation: an application (E7)

The case of the core at an application `app f a m r` (`CaseApp`,
`IxCC.Src.Relevance.Proof.P1.Cases`). E7 evaluates `f`, builds the argument's slot (the marker
where the argument is irrelevant at the levels, the argument's value where it is strict, a
suspension where it is by name) and applies `f`'s value to it.

* `eval f`: the inner-prefix disjunct of `Frame`, with the application's argument prepended to the
  rest of the spine (`frame_fun`); a variable shielded in the application is shielded in `f`, or
  is the argument and unmentioned in `f` (`shieldedIn_app`).
* `eval a` (strict, relevant): `TermC` of the argument and the environment, but at a shielded
  variable, which is exactly `pre_step`'s exception (`frame_arg`).
* `apply fv s` (`pre_apply`): `Live fv` from `f`'s `Post`. A marker meets a value that ignores it:
  `eval_erased_prefix` at a position written erased, `SortCoherent` (a) otherwise. A shielded
  argument meets a closure chain that ignores it and is no partial application
  (`eval_shielded_prefix`). Any other slot is `LiveSlot`. At a partial application the per-minor
  fact grows by one position (`minorsIgnore_snoc`): vacuous at a `Whole` one; at one that is not
  `Whole`, the spine's head is the eliminator's constant and the value holds one slot per argument
  of `f` (`unroll`, by induction on `f` through the induction hypothesis: a constant is δ's partial
  application; one more argument below the arity accumulates, at the arity `fire`'s `Post` is
  `Whole`; any other head has `WholeTerm`), so the new position is the argument's, which C3's
  `MinorC` at the saturated spine covers (`ignoresSlot_of_headC`, a field written erased being
  dropped at every instance, `field_erased_dropped`).
* `Post`: `apply`'s. `Whole` where `WholeTerm` holds: from `apply`'s `Post` at a `Whole` function
  value; otherwise `unroll` makes the application saturate the eliminator, and `fire`'s `Post` is
  `Whole`. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src
open Check Check.Canonical
open IxCC.Lam.Erase.Proof (Agree)

variable {p : Program} {ann : Ann} {ch : Checked}

/-! ## Spines, references, shielding -/

/-- The spine of `mkApps t more`: `t`'s, with `more` appended. -/
theorem spineL_mkApps' : ∀ (t : Term) (more : List Term.Arg),
    (Term.mkApps t more).spineL = (t.spineL.1, t.spineL.2 ++ more)
  | t, [] => by simp [Term.mkApps]
  | t, (a, m, r) :: more => by
    have e : Term.mkApps t ((a, m, r) :: more) = Term.mkApps (.app t a m r) more := rfl
    rw [e, spineL_mkApps' _ more, spineL_app]
    simp

/-- A term whose spine head is no constant has `WholeTerm`. -/
theorem wholeTerm_of_head {t : Term} (h : ∀ c us, t.spineL.1 ≠ .const c us) : WholeTerm p t :=
  fun c us _ hh _ _ => (h c us hh).elim

/-- A variable shielded in an application is shielded in its function, which the argument does
not mention; or it is the argument itself, which the function does not mention, the function's
spine being headed by a variable whose slot ignores the argument's position. -/
theorem shieldedIn_app {x : Nat} {ρ : Env} {f a : Term} {m : Mode} {r : Rel}
    (h : ShieldedIn x ρ (.app f a m r)) :
    (ShieldedIn x ρ f ∧ mentionsVar x a = false) ∨
    (a = .var x ∧ mentionsVar x f = false ∧
      ∃ hv s, f.spineL.1 = .var hv ∧ ρ[hv]? = some s ∧ IgnoresSlot s f.spineL.2.length) := by
  obtain ⟨hv, n, s, hh, hne, hs, hig, ⟨a0, ha0, ha0x⟩, hoth⟩ := h
  simp only [spineL_app] at hh ha0 hoth
  by_cases hn : n < f.spineL.2.length
  · left
    refine ⟨⟨hv, n, s, hh, hne, hs, hig, ⟨a0, ?_, ha0x⟩, fun m' a' hm' hmn => hoth m' a' ?_ hmn⟩, ?_⟩
    · rwa [List.getElem?_append_left hn] at ha0
    · have hl := (List.getElem?_eq_some_iff.1 hm').1
      rw [List.getElem?_append_left hl]
      exact hm'
    · exact hoth f.spineL.2.length (a, m, r) (by simp) (by omega)
  · right
    have hlt := (List.getElem?_eq_some_iff.1 ha0).1
    simp only [List.length_append, List.length_singleton] at hlt
    have hn' : n = f.spineL.2.length := by omega
    subst hn'
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
      Option.some.injEq] at ha0
    subst ha0
    refine ⟨ha0x, ?_, hv, s, hh, hs, hig⟩
    cases hmf : mentionsVar x f
    · rfl
    · exfalso
      have hhd : mentionsVar x f.spineL.1 = false := by
        rw [hh]
        simp [mentionsVar, hne]
      obtain ⟨m', a', hm', hx'⟩ := mentionsVar_arg hmf hhd
      have hlt' := (List.getElem?_eq_some_iff.1 hm').1
      have := hoth m' a' (by rw [List.getElem?_append_left hlt']; exact hm') (by omega)
      rw [this] at hx'
      cases hx'

/-- The environment invariant passes to the function of an application. -/
theorem envOk_fun {ls : Levels} {bs : List Rel} {ρ : Env} {f a : Term} {m : Mode} {r : Rel}
    (h : EnvOk p ann ch ls bs ρ (.app f a m r)) : EnvOk p ann ch ls bs ρ f := by
  obtain ⟨hlen, henv⟩ := h
  refine ⟨hlen, fun x s r' hx hr hirr hm hns => henv x s r' hx hr hirr (by simp [mentionsVar, hm]) ?_⟩
  intro hsi
  rcases shieldedIn_app hsi with ⟨hsf, -⟩ | ⟨-, hmf, -⟩
  · exact hns hsf
  · rw [hm] at hmf
    cases hmf

/-- The environment invariant passes to the argument, unless the argument is a variable the
application shields. -/
theorem envOk_arg {ls : Levels} {bs : List Rel} {ρ : Env} {f a : Term} {m : Mode} {r : Rel}
    (h : EnvOk p ann ch ls bs ρ (.app f a m r))
    (hns : ¬ ∃ x, a = .var x ∧ ShieldedIn x ρ (.app f a m r)) : EnvOk p ann ch ls bs ρ a := by
  obtain ⟨hlen, henv⟩ := h
  refine ⟨hlen, fun x s r' hx hr hirr hm _ => henv x s r' hx hr hirr (by simp [mentionsVar, hm]) ?_⟩
  intro hsi
  rcases shieldedIn_app hsi with ⟨-, hma⟩ | ⟨ha, -, -⟩
  · rw [hm] at hma
    cases hma
  · exact hns ⟨x, ha, hsi⟩

/-! ## The frame of an application, and of its parts -/

/-- An application's frame: the function's spine facts, the argument's facts where it is
relevant, and C3/C4 at the full spine, which continues past the argument with `more`. -/
theorem frame_app_parts {ls : Levels} {ρ : Env} {f a : Term} {m : Mode} {r : Rel}
    (h : Frame p ann ch ls ρ (.app f a m r)) :
    ∃ q bs, Agree ls q ∧ EnvOk p ann ch ls bs ρ (.app f a m r) ∧ RefsHandled p ch q (.app f a m r) ∧
      univsOk p (.app f a m r) = true ∧ SpineC p ann q bs f ∧ (r.irrP q = false → TermC p ann q bs a) ∧
      ∃ more : List Term.Arg, HeadC p ann q f.spineL.1 (f.spineL.2 ++ (a, m, r) :: more) := by
  obtain ⟨q, bs, hag, henv, hrefs, hu, ht | ⟨more, -, hsp, hhc⟩ | ⟨c, us, he, -⟩⟩ := h
  · cases ht with
    | app hhc hsf ha =>
      refine ⟨q, bs, hag, henv, hrefs, hu, hsf, ha, [], ?_⟩
      simp only [spineL_app] at hhc
      exact hhc
  · cases hsp with
    | app hsf ha =>
      refine ⟨q, bs, hag, henv, hrefs, hu, hsf, ha, more, ?_⟩
      simp only [spineL_mkApps', spineL_app] at hhc
      rw [List.append_assoc, List.singleton_append] at hhc
      exact hhc
    | head hne _ _ => exact absurd rfl (hne f a m r)
  · cases he

/-- `eval f`'s frame: the inner-prefix disjunct, the argument prepended to the rest. -/
theorem frame_fun {ls : Levels} {ρ : Env} {f a : Term} {m : Mode} {r : Rel}
    (h : Frame p ann ch ls ρ (.app f a m r)) : Frame p ann ch ls ρ f := by
  obtain ⟨q, bs, hag, henv, hrefs, hu, hsf, -, more, hhc⟩ := frame_app_parts h
  refine ⟨q, bs, hag, envOk_fun henv, ?_, ?_, Or.inr (Or.inl ⟨(a, m, r) :: more, List.cons_ne_nil _ _, hsf, ?_⟩)⟩
  · intro x hx
    apply hrefs x
    simp only [Term.relevantRefs]
    split
    · exact hx
    · exact relevantRefs_mono q a _ hx
  · simp only [univsOk, Bool.and_eq_true] at hu
    exact hu.1
  · simp only [spineL_mkApps']
    exact hhc

/-- `eval a`'s facts where the argument is relevant and no variable the application shields. -/
theorem frame_arg {ls : Levels} {ρ : Env} {f a : Term} {m : Mode} {r : Rel}
    (h : Frame p ann ch ls ρ (.app f a m r)) (hrel : r.irrAt ls = false)
    (hns : ¬ ∃ x, a = .var x ∧ ShieldedIn x ρ (.app f a m r)) :
    ∃ q bs, Agree ls q ∧ EnvOk p ann ch ls bs ρ a ∧ TermOk p ann ch q bs a := by
  obtain ⟨q, bs, hag, henv, hrefs, hu, -, ha, -⟩ := frame_app_parts h
  have hrq : r.irrP q = false := by rw [hag.irr]; exact hrel
  refine ⟨q, bs, hag, envOk_arg henv hns, ⟨ha hrq, ?_, ?_⟩⟩
  · intro x hx
    apply hrefs x
    simp only [Term.relevantRefs, hrq, Bool.false_eq_true, ↓reduceIte]
    rw [relevantRefs_append q a]
    exact List.mem_append_left _ hx
  · simp only [univsOk, Bool.and_eq_true, Bool.or_eq_true] at hu
    rcases hu.2 with h' | h'
    · rw [alwaysIrr_irrAt h' ls] at hrel
      cases hrel
    · exact h'

/-! ## Steps -/

/-- No step to a call other than a variable's evaluation is the shielded step. -/
theorem not_shielded_of_ne {c c' : Call} (h : ∀ k ls ρ x, c' ≠ .eval k ls ρ (.var x)) :
    ¬ ShieldedStep c c' := by
  rintro ⟨k, ls, ρ, f, m, r, x, -, h2, -⟩
  exact h k ls ρ x h2

/-- The function's evaluation is not the shielded step (a variable is not shielded in a spine it
heads). -/
theorem not_shielded_fun {k : Nat} {ls : Levels} {ρ : Env} {f a : Term} {m : Mode} {r : Rel} :
    ¬ ShieldedStep (.eval k ls ρ (.app f a m r)) (.eval k ls ρ f) := by
  rintro ⟨k', ls', ρ', f', m', r', x, h1, h2, hsh⟩
  simp only [Call.eval.injEq, Term.app.injEq] at h1 h2
  obtain ⟨-, -, -, rfl, -, -, -⟩ := h1
  obtain ⟨-, -, -, rfl⟩ := h2
  obtain ⟨hv, n, s, hh, hne, -⟩ := hsh
  simp [Term.spineL, Term.spine, Term.spine.go] at hh
  exact hne hh.symm

/-- E7's step to `apply`, from the function's value and the argument's slot. -/
theorem slotOf_step {k : Nat} {ls : Levels} {ρ : Env} {f a : Term} {m : Mode} {r : Rel} {fv : Value}
    {s : Slot} (hfv : eval p k ls ρ f = .ok fv) (hs : slotOf p k ls ρ (a, m, r) = .ok s) :
    Step p (.eval k ls ρ (.app f a m r)) (.apply k fv s) := by
  simp only [slotOf] at hs
  split at hs
  · rename_i hr
    cases hs
    exact Step.appIrr hfv hr
  · rename_i hr
    have hr' : r.irrAt ls = false := by simpa using hr
    cases m with
    | strict =>
      obtain ⟨x, hx, hs⟩ := bind_ok_inv hs
      cases hs
      exact Step.appStrict hfv hr' hx
    | byName =>
      cases hs
      exact Step.appName hfv hr'

/-! ## The value of a spine prefix that is no `Whole` value -/

/-- Not `Whole`: a partial application of an eliminator over a field written erased. -/
theorem exists_of_not_whole {h : Head} {ls : Levels} {args : List Slot}
    (hw : ¬ Whole p (.pap h ls args)) :
    ∃ c shape, headConst? h = some c ∧ elimShape? p c = some shape ∧ erasedMinors p shape = true := by
  apply Classical.byContradiction
  intro hno
  apply hw
  intro h' ls' args' he c shape hc hsh
  cases he
  cases hem : erasedMinors p shape
  · rfl
  · exact (hno ⟨c, shape, hc, hsh, hem⟩).elim

/-- A value that is not `Whole` is a partial application. -/
theorem pap_of_not_whole {v : Value} (hw : ¬ Whole p v) : ∃ h ls args, v = .pap h ls args := by
  cases v with
  | pap h ls args => exact ⟨h, ls, args, rfl⟩
  | _ => exact (hw (fun _ _ _ he => nomatch he)).elim

/-- An eliminator's special head fires at the eliminator's arity. -/
theorem headArity_of_shape {c : CId} {h : Head} {shape : ElimShape} (hsp : specialHead? p c = some h)
    (hsh : elimShape? p c = some shape) : p.headArity h = shape.arity := by
  cases hres : p.table.resolveOf c with
  | none =>
    cases hd : p.decl? c with
    | none => simp [elimShape?, hres, hd] at hsh
    | some d =>
      cases d with
      | recr sf kk lv np nmot nmin ni ind rules ty =>
        simp [specialHead?, hres, hd] at hsp
        subst hsp
        simp [elimShape?, hres, hd] at hsh
        subst hsh
        rw [headArity_recr hd]
      | _ => simp [elimShape?, hres, hd] at hsh
  | some e =>
    cases e with
    | case r =>
      simp [specialHead?, hres] at hsp
      subst hsp
      cases hd : p.decl? r with
      | none => simp [elimShape?, hres, hd] at hsh
      | some d =>
        cases d with
        | recr sf kk lv np nmot nmin ni ind rules ty =>
          rw [elimShape_cases hres hd] at hsh
          cases hsh
          rw [headArity_cases hres hd]
        | _ => simp [elimShape?, hres, hd] at hsh
    | _ => simp [elimShape?, hres] at hsh

/-- δ at an eliminator: its special head's partial application with no argument. -/
theorem evalConst_elim {k : Nat} {ls : Levels} {c : CId} {shape : ElimShape} {v : Value}
    (hsh : elimShape? p c = some shape) (he : evalConst p k ls c = .ok v) :
    ∃ h, v = .pap h ls [] ∧ headConst? h = some c := by
  rw [evalConst_eq] at he
  cases hres : p.table.resolveOf c with
  | none =>
    cases hd : p.decl? c with
    | none => simp [elimShape?, hres, hd] at hsh
    | some d =>
      cases d with
      | recr sf kk lv np nmot nmin ni ind rules ty =>
        simp only [hres, hd] at he
        have hne : (p.headArity (.recr c) == 0) = false := by rw [headArity_recr hd]; simp
        rw [headValue_eq, hne] at he
        simp only [Bool.false_eq_true, ite_false, Sem.Result.ok.injEq] at he
        exact ⟨.recr c, he.symm, rfl⟩
      | _ => simp [elimShape?, hres, hd] at hsh
  | some e =>
    cases e with
    | case r =>
      simp only [hres] at he
      cases hd : p.decl? r with
      | none => simp [elimShape?, hres, hd] at hsh
      | some d =>
        cases d with
        | recr sf kk lv np nmot nmin ni ind rules ty =>
          have hne : (p.headArity (.cases c) == 0) = false := by rw [headArity_cases hres hd]; simp
          rw [headValue_eq, hne] at he
          simp only [Bool.false_eq_true, ite_false, Sem.Result.ok.injEq] at he
          exact ⟨.cases c, he.symm, rfl⟩
        | _ => simp [elimShape?, hres, hd] at hsh
    | _ => simp [elimShape?, hres] at hsh

/-- **Unrolling.** A spine prefix's value that is not `Whole` is a partial application of the
spine's head constant holding one slot per argument: δ at a constant gives the eliminator's
partial application with none; one more argument below the arity accumulates (at the arity `fire`'s
`Post` is `Whole`); at any other head the term has `WholeTerm`, so its `Post` gives `Whole`. -/
theorem unroll {k : Nat} {ls : Levels} {ρ : Env} :
    ∀ (f : Term) {fv : Value}, Inv p ann ch (.eval k ls ρ f) → Below p ann ch (.eval k ls ρ f) →
      Pre p ann ch (.eval k ls ρ f) → eval p k ls ρ f = .ok fv → ¬ Whole p fv →
      ∃ c us h ls' args, f.spineL.1 = .const c us ∧ fv = .pap h ls' args ∧ headConst? h = some c ∧
        args.length = f.spineL.2.length
  | .app f a m r, fv, hi, hb, hpre, he, hnw => by
    obtain ⟨-, hsteps⟩ := hi hpre
    rw [eval_app_slot] at he
    obtain ⟨fv', hfv', he⟩ := bind_ok_inv he
    obtain ⟨s, hs, he⟩ := bind_ok_inv he
    have hst := slotOf_step hfv' hs
    have hpa := hsteps _ hst (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
    obtain ⟨hpost_a, hsteps_a⟩ := hb _ (.single hst) hpa
    have hnw' : ¬ Whole p fv' := fun hw => hnw ((hpost_a fv he).2 hw)
    have hpf := hsteps _ Step.appFun not_shielded_fun
    obtain ⟨c, us, h, ls', args, hhd, rfl, hc, hlen⟩ :=
      unroll f (hb _ (.single Step.appFun)) (fun c' hc' => hb c' (tg_head Step.appFun hc')) hpf hfv'
        hnw'
    rw [apply_pap] at he
    split at he
    · rename_i heq
      have harity : (args ++ [s]).length = p.headArity h := beq_iff_eq.mp heq
      have hpfire := hsteps_a _ (Step.papFire harity) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
      exact (hnw ((hb _ (.tail (.single hst) (Step.papFire harity)) hpfire).1 fv he).2).elim
    · split at he
      · simp only [Sem.Result.ok.injEq] at he
        subst he
        refine ⟨c, us, h, ls', args ++ [s], ?_, rfl, hc, ?_⟩
        · simp only [spineL_app]
          exact hhd
        · simp [spineL_app, hlen]
      · cases he
  | .const c us, fv, hi, hb, hpre, he, hnw => by
    obtain ⟨-, hsteps⟩ := hi hpre
    rw [eval_const] at he
    have hpc := hsteps _ Step.const (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
    have hpost := (hb _ (.single Step.const) hpc).1 fv he
    obtain ⟨shape, hsh⟩ : ∃ shape, elimShape? p c = some shape := by
      cases hes : elimShape? p c with
      | none => exact (hnw (hpost.2 (fun shape hsh => by rw [hes] at hsh; cases hsh))).elim
      | some shape => exact ⟨shape, rfl⟩
    obtain ⟨h, rfl, hc⟩ := evalConst_elim hsh he
    exact ⟨c, us, h, _, [], rfl, rfl, hc, rfl⟩
  | .var _, fv, hi, _, hpre, he, hnw | .sort _, fv, hi, _, hpre, he, hnw
  | .lam .., fv, hi, _, hpre, he, hnw | .pi .., fv, hi, _, hpre, he, hnw
  | .letE .., fv, hi, _, hpre, he, hnw | .proj .., fv, hi, _, hpre, he, hnw
  | .natLit _, fv, hi, _, hpre, he, hnw | .strLit _, fv, hi, _, hpre, he, hnw => by
    exact (hnw (((hi hpre).1 fv he).2
      (wholeTerm_of_head (by simp [Term.spineL, Term.spine, Term.spine.go])))).elim

/-! ## The per-minor fact at one more position -/

/-- The per-minor fact of a partial application with one more slot: the old positions', and the
new position's. -/
theorem minorsIgnore_snoc {h : Head} {args : List Slot} {s : Slot} (hm : MinorsIgnore p ann h args)
    (hnew : ∀ c shape, headConst? h = some c → elimShape? p c = some shape → ∀ j kidx,
      (args.length, j, kidx) ∈ shape.minors → ∀ k fields,
        ruleCtorFields p ann shape.recr kidx = some (k, fields) →
        ∀ i, i < fields.length → fieldWrittenErased p k i = true → IgnoresSlot s i) :
    MinorsIgnore p ann h (args ++ [s]) := by
  intro c shape hc hsh pos j kidx hmem s' hs' k fields hrcf i hi hwe
  by_cases hp : pos < args.length
  · rw [List.getElem?_append_left hp] at hs'
    exact hm c shape hc hsh pos j kidx hmem s' hs' k fields hrcf i hi hwe
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hp)] at hs'
    have hlt := (List.getElem?_eq_some_iff.1 hs').1
    simp only [List.length_singleton] at hlt
    have hpe : pos = args.length := by omega
    subst hpe
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hs'
    subst hs'
    exact hnew c shape hc hsh j kidx hmem k fields hrcf i hi hwe

/-- A rule's constructor fields are its constructor record's. -/
theorem ruleCtorFields_rel {r : CId} {kidx : Nat} {k : CId} {fields : List FieldClass}
    (h : ruleCtorFields p ann r kidx = some (k, fields)) :
    ∃ kr, ann.ctorRel? k = some kr ∧ fields = kr.fields := by
  cases hd : p.decl? r with
  | none => simp [ruleCtorFields, hd] at h
  | some d =>
    cases d with
    | recr sf kk lv np nmot nmin ni ind rules ty =>
      cases hr : rules[kidx]? with
      | none => simp [ruleCtorFields, hd, hr] at h
      | some rule =>
        cases hkr : ann.ctorRel? rule.ctor with
        | none => simp [ruleCtorFields, hd, hr, hkr] at h
        | some kr =>
          simp [ruleCtorFields, hd, hr, hkr] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨kr, hkr, rfl⟩
    | _ => simp [ruleCtorFields, hd] at h

private theorem propWhen_lawfulBEq_app : LawfulBEq PropWhen where
  rfl := by
    intro a
    cases a with
    | never => rfl
    | allZero ps => show (ps == ps) = true; exact beq_self_eq_true ps
  eq_of_beq := by
    intro a b h
    cases a with
    | never => cases b with
      | never => rfl
      | allZero _ => cases h
    | allZero ps => cases b with
      | never => cases h
      | allZero qs => exact congrArg _ (beq_iff_eq.1 (show (ps == qs) = true from h))

/-- A field class dropped at every instance is dropped at any profile. -/
theorem dropP_of_alwaysDropped {cls : FieldClass} (h : cls.alwaysDropped = true) (q : Profile) :
    cls.dropP q = true := by
  have hl := propWhen_lawfulBEq_app
  unfold FieldClass.alwaysDropped at h
  unfold FieldClass.dropP
  rw [beq_iff_eq.1 h]
  rfl

/-- C3 at a saturated eliminator spine (`ElimC`'s `MinorC`), at the position of an argument
relevant at the levels: the argument's slot ignores each field written erased of the constructor
the minor there meets, given that the slot ignores what the argument's leading λs bind
irrelevantly. -/
theorem ignoresSlot_of_headC (hf : Facts p ann ch) {q : Profile} {ls : Levels} (hag : Agree ls q)
    {c : CId} {us : List Ixon.Univ} {pre more : List Term.Arg} {a : Term} {m : Mode} {r : Rel}
    {s : Slot} (hhc : HeadC p ann q (.const c us) (pre ++ (a, m, r) :: more))
    {shape : ElimShape} (hsh : elimShape? p c = some shape) (hem : erasedMinors p shape = true)
    (hrel : r.irrAt ls = false)
    (hslot : ∀ i b, (lamRels a)[i]? = some b → b.irrAt ls = true → IgnoresSlot s i)
    {j kidx : Nat} (hmem : (pre.length, j, kidx) ∈ shape.minors) {k : CId}
    {fields : List FieldClass} (hrcf : ruleCtorFields p ann shape.recr kidx = some (k, fields))
    {i : Nat} (hi : i < fields.length) (hwe : fieldWrittenErased p k i = true) : IgnoresSlot s i := by
  have hel : ElimC p ann q c us (pre ++ (a, m, r) :: more) := hhc.2
  obtain ⟨h1, h2⟩ := hel shape hsh
  have har : shape.arity ≤ (pre ++ (a, m, r) :: more).length := by
    apply Classical.byContradiction
    intro hlt
    have := h1 (by omega)
    rw [hem] at this
    cases this
  obtain ⟨-, hmin⟩ := h2 har
  have hrq : r.irrP q = false := by rw [hag.irr]; exact hrel
  obtain ⟨hA, hB⟩ := hmin pre.length j kidx hmem a m r k fields (by simp) hrcf hrq
  have hlt : i < (lamRels a).length := by
    apply Classical.byContradiction
    intro hge
    have := hB i hi (by omega)
    rw [hwe] at this
    cases this
  obtain ⟨kr, hkr, hfe⟩ := ruleCtorFields_rel hrcf
  subst hfe
  obtain ⟨cls, hcls, hdrop⟩ := field_erased_dropped (hf.canon.ctors k kr hkr) hwe
  have hb := List.getElem?_eq_getElem hlt
  have hirrq := hA i _ cls hb hcls (dropP_of_alwaysDropped hdrop _)
  refine hslot i _ hb ?_
  rw [← hag.irr]
  exact hirrq

/-- A relevant argument's slot ignores what the argument's leading λs bind irrelevantly at the
levels: a suspension of the argument, or (strict) the closure of the λ it is. -/
theorem ignoresSlot_of_slotOf {k : Nat} {ls : Levels} {ρ : Env} {a : Term} {m : Mode} {r : Rel}
    {s : Slot} (hs : slotOf p k ls ρ (a, m, r) = .ok s) (hr : r.irrAt ls = false) :
    ∀ i b, (lamRels a)[i]? = some b → b.irrAt ls = true → IgnoresSlot s i := by
  intro i b hb hirr
  cases m with
  | strict =>
    simp only [slotOf, hr, Bool.false_eq_true, ↓reduceIte] at hs
    obtain ⟨x, hx, hs⟩ := bind_ok_inv hs
    cases hs
    cases a with
    | lam b0 d0 body0 =>
      rw [eval_lam] at hx
      cases hx
      exact ⟨b, hb, hirr⟩
    | _ => simp [lamRels] at hb
  | byName =>
    simp only [slotOf, hr, Bool.false_eq_true, ↓reduceIte] at hs
    cases hs
    exact ⟨b, hb, hirr⟩

/-! ## `apply`'s precondition -/

/-- E7's `apply` has its precondition: `Live` from the function's `Post`, `SlotFits` by the slot. -/
theorem pre_apply (hf : Facts p ann ch) {k : Nat} {ls : Levels} {ρ : Env} {f a : Term} {m : Mode}
    {r : Rel} (hpre : Frame p ann ch ls ρ (.app f a m r))
    (hcoh : SortCoherent p ann (.eval k ls ρ (.app f a m r)))
    (ih : Below p ann ch (.eval k ls ρ (.app f a m r))) {fv : Value} {s : Slot}
    (hfv : eval p k ls ρ f = .ok fv) (hs : slotOf p k ls ρ (a, m, r) = .ok s) :
    Pre p ann ch (.apply k fv s) := by
  have hfr := frame_fun hpre
  have hif : Inv p ann ch (.eval k ls ρ f) := ih _ (.single Step.appFun)
  have hbf : Below p ann ch (.eval k ls ρ f) := fun c' hc' => ih c' (tg_head Step.appFun hc')
  have hlive : Live p ann ch fv := ((hif hfr).1 fv hfv).1
  refine ⟨hlive, ?_⟩
  cases hr : r.irrAt ls with
  | true =>
    -- a marker: the function value ignores it
    have hsm : s = .val (.irr (some a) ρ ls) := by
      simp only [slotOf, hr, ↓reduceIte, Sem.Result.ok.injEq] at hs
      exact hs.symm
    have hsc : r.irrAt ls = true → ¬ WrittenErasedArg p (.app f a m r) →
        ∀ fv, eval p k ls ρ f = .ok fv → IgnoresNext ann fv := hcoh
    have hig : IgnoresNext ann fv := by
      by_cases hwe : WrittenErasedArg p (.app f a m r)
      · exact eval_erased_prefix hf hpre hwe hfv
      · exact hsc hr hwe fv hfv
    subst hsm
    cases fv with
    | clo b d body ρ' ls' =>
      intro hrel
      simp only [IgnoresNext] at hig
      rw [hig] at hrel
      cases hrel
    | pap h ls' args =>
      cases hlive with
      | pap _ _ hmin _ =>
        exact ⟨fun hn => (hn ⟨hig, _, _, _, rfl⟩).elim, minorsIgnore_snoc hmin (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)⟩
    | lit _ => trivial
    | str _ => trivial
    | con _ _ _ _ => trivial
    | irr _ _ _ => trivial
  | false =>
    by_cases hsh : ∃ x, a = .var x ∧ ShieldedIn x ρ (.app f a m r)
    · -- a shielded argument: the prefix ignores it and is no partial application
      obtain ⟨x, hax, hsi⟩ := hsh
      rcases shieldedIn_app hsi with ⟨-, hma⟩ | ⟨-, -, hv, s0, hhd, hs0, hig0⟩
      · subst hax
        simp [mentionsVar] at hma
      · obtain ⟨hig, hnp⟩ := eval_shielded_prefix (ann := ann) hhd rfl hs0 hig0 hfv
        cases fv with
        | clo b d body ρ' ls' =>
          intro hrel
          simp only [IgnoresNext] at hig
          rw [hig] at hrel
          cases hrel
        | pap h ls' args => exact (hnp h ls' args rfl).elim
        | lit _ => trivial
        | str _ => trivial
        | con _ _ _ _ => trivial
        | irr _ _ _ => trivial
    · obtain ⟨q, bs, hag, henva, htoka⟩ := frame_arg hpre hr hsh
      have hls : LiveSlot p ann ch s := by
        cases m with
        | strict =>
          simp only [slotOf, hr, Bool.false_eq_true, ↓reduceIte] at hs
          obtain ⟨x, hx, hs⟩ := bind_ok_inv hs
          cases hs
          have hpx := (ih _ (.single (Step.appArg hfv hr)) (frame_of_termOk hag henva htoka)).1 x hx
          exact .val hpx.1 (hpx.2 (wholeTerm_of_termC htoka.c))
        | byName =>
          simp only [slotOf, hr, Bool.false_eq_true, ↓reduceIte] at hs
          cases hs
          exact .name q bs hag htoka henva
      cases fv with
      | clo b d body ρ' ls' => exact fun _ => hls
      | pap h ls' args =>
        refine ⟨fun _ => hls, ?_⟩
        by_cases hw : Whole p (.pap h ls' args)
        · exact minorsIgnore_of_whole hf hw
        · cases hlive with
          | pap _ _ hmin _ =>
            refine minorsIgnore_snoc hmin ?_
            obtain ⟨c, us, h', ls'', args', hhd, he', hc, hlen⟩ := unroll f hif hbf hfr hfv hw
            cases he'
            intro c' shape hc' hsh' j kidx hmem k' fields hrcf i hi hwe
            rw [hc] at hc'
            cases hc'
            obtain ⟨c2, shape2, hc2, hsh2, hem⟩ := exists_of_not_whole hw
            rw [hc] at hc2
            cases hc2
            rw [hsh'] at hsh2
            cases hsh2
            obtain ⟨q', bs', hag', -, -, -, -, -, more, hhc⟩ := frame_app_parts hpre
            rw [hhd] at hhc
            rw [hlen] at hmem
            exact ignoresSlot_of_headC hf hag' hhc hsh' hem hr (ignoresSlot_of_slotOf hs hr) hmem hrcf hi hwe
      | lit _ => trivial
      | str _ => trivial
      | con _ _ _ _ => trivial
      | irr _ _ _ => trivial

/-! ## E7 -/

/-- **E7.** An application's result is `apply`'s; its steps have their preconditions but the
shielded variable's evaluation. -/
theorem case_app : CaseApp p ann ch := by
  intro k ls ρ f a m r hf _ hpre hcoh ih
  have hfr := frame_fun hpre
  have hif : Inv p ann ch (.eval k ls ρ f) := ih _ (.single Step.appFun)
  have hbf : Below p ann ch (.eval k ls ρ f) := fun c' hc' => ih c' (tg_head Step.appFun hc')
  refine ⟨fun v hv => ?_, fun c' hst hsh => ?_⟩
  · rw [eval_app_slot] at hv
    obtain ⟨fv, hfv, hv⟩ := bind_ok_inv hv
    obtain ⟨s, hs, hv⟩ := bind_ok_inv hv
    have hst := slotOf_step hfv hs
    have hpa := pre_apply hf hpre hcoh ih hfv hs
    obtain ⟨hpost, hsteps⟩ := ih _ (.single hst) hpa
    refine ⟨(hpost v hv).1, fun hwt => ?_⟩
    by_cases hw : Whole p fv
    · exact (hpost v hv).2 hw
    · obtain ⟨c, us, h, ls', args, hhd, rfl, hc, hlen⟩ := unroll f hif hbf hfr hfv hw
      obtain ⟨c', shape, hc', hsh, hem⟩ := exists_of_not_whole hw
      rw [hc] at hc'
      cases hc'
      have harle := hwt c us shape (by simp only [spineL_app]; exact hhd) hsh hem
      simp only [spineL_app, List.length_append, List.length_singleton] at harle
      cases hpa.1 with
      | pap hseen _ _ hlt =>
        have har := headArity_of_shape (hseen.1 c hc).1 hsh
        have harity : (args ++ [s]).length = p.headArity h := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hv' : fire p k h ls' (args ++ [s]) = .ok v := by
          rw [apply_pap] at hv
          simp only [harity, beq_self_eq_true, ↓reduceIte] at hv
          exact hv
        have hpfire := hsteps _ (Step.papFire harity) (not_shielded_of_ne (fun _ _ _ _ h => by cases h))
        exact ((ih _ (.tail (.single hst) (Step.papFire harity)) hpfire).1 v hv').2
  · cases hst with
    | appFun => exact hfr
    | appIrr hfv hr => exact pre_apply hf hpre hcoh ih hfv (by simp [slotOf, hr])
    | appArg hfv hr =>
      have hns : ¬ ∃ x, a = .var x ∧ ShieldedIn x ρ (.app f a .strict r) := by
        rintro ⟨x, hax, hsi⟩
        subst hax
        exact hsh ⟨k, ls, ρ, f, .strict, r, x, rfl, rfl, hsi⟩
      obtain ⟨q, bs, hag, henv, htok⟩ := frame_arg hpre hr hns
      exact frame_of_termOk hag henv htok
    | appStrict hfv hr hx => exact pre_apply hf hpre hcoh ih hfv (by simp [slotOf, hr, hx, Sem.Result.bind])
    | appName hfv hr => exact pre_apply hf hpre hcoh ih hfv (by simp [slotOf, hr])

end IxCC.Src.Relevance.Proof.P1
