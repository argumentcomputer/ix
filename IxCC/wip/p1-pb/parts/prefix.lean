/-! ### Spine and prefix lemmas (PB) -/

/-- `Result.bind` returning `.ok`. -/
theorem bind_ok_inv {α β : Type} {r : Sem.Result α} {g : α → Sem.Result β} {v : β}
    (h : r.bind g = .ok v) : ∃ x, r = .ok x ∧ g x = .ok v := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | _ => cases h

/-- `Term.spine.go` with an accumulator appends it. -/
theorem spine_go_acc : ∀ (t : Term) (acc : List Term.Arg),
    Term.spine.go t acc = ((Term.spine.go t []).1, (Term.spine.go t []).2 ++ acc)
  | .app f a m r, acc => by
    simp only [Term.spine.go]
    rw [spine_go_acc f ((a, m, r) :: acc), spine_go_acc f [(a, m, r)]]
    simp
  | .var _, _ | .sort _, _ | .const .., _ | .lam .., _ | .pi .., _ | .letE .., _ | .proj .., _
  | .natLit _, _ | .strLit _, _ => by simp [Term.spine.go]

/-- The spine of an application: its function's, with the argument appended. -/
theorem spineL_app (f a : Term) (m : Mode) (r : Rel) :
    (Term.app f a m r).spineL = (f.spineL.1, f.spineL.2 ++ [(a, m, r)]) := by
  show Term.spine.go (.app f a m r) [] = _
  simp only [Term.spine.go]
  exact spine_go_acc f [(a, m, r)]

/-- A term is the application of its spine's head to its spine's arguments. -/
theorem mkApps_spineL (t : Term) : Term.mkApps t.spineL.1 t.spineL.2 = t := Term.spine_mkApps t

/-- `lamRels` is the classes of `lamBinders`. -/
theorem lamRels_eq : ∀ t : Term, lamRels t = (lamBinders t).map (·.rel)
  | .lam b _ t => by simp only [lamRels, lamBinders, List.map_cons, lamRels_eq t]
  | .var _ | .sort _ | .const .. | .app .. | .pi .. | .letE .. | .proj .. | .natLit _
  | .strLit _ => rfl

private theorem propWhen_lawfulBEq' : LawfulBEq PropWhen where
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

/-- A class irrelevant at every instance is irrelevant at any levels. -/
theorem alwaysIrr_irrAt {r : Rel} (h : r.alwaysIrr = true) (ls : Levels) : r.irrAt ls = true := by
  have hl := propWhen_lawfulBEq'
  unfold Rel.alwaysIrr at h
  unfold Rel.irrAt
  rw [beq_iff_eq.1 h]
  rfl

/-- Applying the closure of a λ-telescope along arguments as many as a binder index of the
telescope whose class is irrelevant at the closure's levels gives a closure whose next binder is
that one. -/
theorem applySpine_lamChain {k : Nat} {ls : Levels} {ρ : Env} :
    ∀ (args : List Term.Arg) (b : Binder) (d body : Term) (ρ' : Env) (ls' : Levels) (r : Rel)
      (fv : Value),
      (lamRels (.lam b d body))[args.length]? = some r → r.irrAt ls' = true →
      applySpine p k ls ρ (.clo b d body ρ' ls') args = .ok fv →
      IgnoresNext ann fv ∧ ∀ h' ls'' as, fv ≠ .pap h' ls'' as
  | [], b, d, body, ρ', ls', r, fv, hr, hirr, he => by
    simp only [applySpine, Sem.Result.ok.injEq] at he
    subst he
    simp only [lamRels, List.length_nil, List.getElem?_cons_zero, Option.some.injEq] at hr
    subst hr
    exact ⟨hirr, fun _ _ _ h => by cases h⟩
  | a :: as, b, d, body, ρ', ls', r, fv, hr, hirr, he => by
    simp only [applySpine] at he
    obtain ⟨s, -, he⟩ := bind_ok_inv he
    obtain ⟨v, hv, he⟩ := bind_ok_inv he
    simp only [lamRels, List.length_cons, List.getElem?_cons_succ] at hr
    cases body with
    | lam b2 d2 body2 =>
      rw [apply_clo] at hv
      split at hv
      · cases k with
        | zero => cases hv
        | succ k' =>
          simp only [Sem.later_succ, eval_lam, Sem.Result.ok.injEq] at hv
          subst hv
          exact applySpine_lamChain as b2 d2 body2 _ ls' r fv hr hirr he
      · cases hv
    | _ => simp [lamRels] at hr

/-- Applying a value that is neither a closure nor a partial application is stuck. -/
theorem applySpine_stuck {k : Nat} {ls : Levels} {ρ : Env} {v : Value}
    (h1 : ∀ b d body ρ' ls', v ≠ .clo b d body ρ' ls') (h2 : ∀ h ls' args, v ≠ .pap h ls' args)
    {a : Term.Arg} {as : List Term.Arg} {fv : Value}
    (he : applySpine p k ls ρ v (a :: as) = .ok fv) : False := by
  simp only [applySpine] at he
  obtain ⟨s, -, he⟩ := bind_ok_inv he
  obtain ⟨w, hw, -⟩ := bind_ok_inv he
  rw [apply_other p k v s h1 h2] at hw
  cases hw

/-- A value of a λ-telescope's chain (`IgnoresSlot` at the length of the spine): what a spine
headed by a slot that ignores argument `n` evaluates to after `n` arguments. -/
theorem applySpine_ignoresSlot {k : Nat} {ls : Levels} {ρ : Env} {s : Slot} {v0 fv : Value}
    {args : List Term.Arg} (hig : IgnoresSlot s args.length) (hv0 : force p k s = .ok v0)
    (he : applySpine p k ls ρ v0 args = .ok fv) :
    IgnoresNext ann fv ∧ ∀ h' ls' as, fv ≠ .pap h' ls' as := by
  cases s with
  | val v =>
    rw [force_val] at hv0
    injection hv0 with e
    subst e
    cases v with
    | clo b d body ρ' ls' =>
      obtain ⟨r, hr, hirr⟩ := hig
      exact applySpine_lamChain args b d body ρ' ls' r fv hr hirr he
    | pap _ _ _ => exact hig.elim
    | lit n =>
      cases args with
      | nil => simp only [applySpine, Sem.Result.ok.injEq] at he; subst he; exact ⟨trivial, fun _ _ _ h => by cases h⟩
      | cons a as => exact (applySpine_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) he).elim
    | str s =>
      cases args with
      | nil => simp only [applySpine, Sem.Result.ok.injEq] at he; subst he; exact ⟨trivial, fun _ _ _ h => by cases h⟩
      | cons a as => exact (applySpine_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) he).elim
    | con c ls' ps fs =>
      cases args with
      | nil => simp only [applySpine, Sem.Result.ok.injEq] at he; subst he; exact ⟨trivial, fun _ _ _ h => by cases h⟩
      | cons a as => exact (applySpine_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) he).elim
    | irr t ρ' ls' =>
      cases args with
      | nil => simp only [applySpine, Sem.Result.ok.injEq] at he; subst he; exact ⟨trivial, fun _ _ _ h => by cases h⟩
      | cons a as => exact (applySpine_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) he).elim
  | name t ρ' ls' =>
    rw [force_name] at hv0
    cases k with
    | zero => cases hv0
    | succ k' =>
      simp only [Sem.later_succ] at hv0
      obtain ⟨r, hr, hirr⟩ := hig
      cases t with
      | lam b d body =>
        rw [eval_lam] at hv0
        cases hv0
        exact applySpine_lamChain args b d body ρ' ls' r fv hr hirr he
      | _ => simp [lamRels] at hr

/-- A constant reference keeps the references already collected. -/
theorem relevantRefs_mono (q : Profile) {x : Inst} :
    ∀ (t : Term) (acc : List Inst), x ∈ acc → x ∈ t.relevantRefs q acc
  | .const _ _, _, h => List.mem_cons_of_mem _ h
  | .app f a _ r, acc, h => by
    simp only [Term.relevantRefs]
    have h1 := relevantRefs_mono q f acc h
    split
    · exact h1
    · exact relevantRefs_mono q a _ h1
  | .lam _ _ t, acc, h => by
    simp only [Term.relevantRefs]
    split
    · exact h
    · exact relevantRefs_mono q t acc h
  | .letE _ r _ v b, acc, h => by
    simp only [Term.relevantRefs]
    apply relevantRefs_mono q b
    split
    · exact h
    · exact relevantRefs_mono q v acc h
  | .proj _ _ e, acc, h => by simp only [Term.relevantRefs]; exact relevantRefs_mono q e acc h
  | .var _, _, h | .sort _, _, h | .pi .., _, h | .natLit _, _, h | .strLit _, _, h => by
    simp only [Term.relevantRefs]; exact h

/-- A spine's head constant is among its relevant references. -/
theorem head_mem_relevantRefs (q : Profile) {c : CId} {us : List Ixon.Univ} :
    ∀ (t : Term) (acc : List Inst), t.spineL.1 = .const c us → (c, q.inst us) ∈ t.relevantRefs q acc
  | .const c' us', acc, h => by
    simp only [Term.spineL, Term.spine, Term.spine.go, Term.const.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Term.relevantRefs]
  | .app f a m r, acc, h => by
    rw [spineL_app] at h
    simp only [Term.relevantRefs]
    have h1 := head_mem_relevantRefs q f acc h
    split
    · exact h1
    · exact relevantRefs_mono q a _ h1
  | .var _, _, h | .sort _, _, h | .lam .., _, h | .pi .., _, h | .letE .., _, h | .proj .., _, h
  | .natLit _, _, h | .strLit _, _, h => by simp [Term.spineL, Term.spine, Term.spine.go] at h

/-- The head λ of a spine with tier C's facts has them. -/
theorem spineC_head_lam {q : Profile} {b : Binder} {d body : Term} :
    ∀ {bs : List Rel} {f : Term}, SpineC p ann q bs f → f.spineL.1 = .lam b d body →
      TermC p ann q bs (.lam b d body)
  | _, .app f a m r, h, hh => by
    rw [spineL_app] at hh
    cases h with
    | app hsf _ => exact spineC_head_lam hsf hh
    | head hne _ _ => exact absurd rfl (hne f a m r)
  | _, .lam b' d' body', h, hh => by
    simp only [Term.spineL, Term.spine, Term.spine.go, Term.lam.injEq] at hh
    obtain ⟨rfl, rfl, rfl⟩ := hh
    cases h with
    | head _ _ ht => exact ht
  | _, .var _, _, hh | _, .sort _, _, hh | _, .const .., _, hh | _, .pi .., _, hh
  | _, .letE .., _, hh | _, .proj .., _, hh | _, .natLit _, _, hh | _, .strLit _, _, hh => by
    simp [Term.spineL, Term.spine, Term.spine.go] at hh

/-- C0 along a λ-telescope: a binder written erased is irrelevant at the profile. -/
theorem termC_lamBinder_erased {q : Profile} :
    ∀ {bs : List Rel} {t : Term} {i : Nat} {bd : Binder}, TermC p ann q bs t →
      (lamBinders t)[i]? = some bd → writtenErased bd = true → bd.rel.irrP q = true
  | _, .lam b d t, 0, bd, h, hi, hw => by
    simp only [lamBinders, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    cases h with
    | lam h0 _ => exact h0 hw
  | _, .lam b d t, i + 1, bd, h, hi, hw => by
    simp only [lamBinders, List.getElem?_cons_succ] at hi
    cases h with
    | lam _ ht => exact termC_lamBinder_erased ht hi hw
  | _, .var _, _, _, _, hi, _ | _, .sort _, _, _, _, hi, _ | _, .const .., _, _, _, hi, _
  | _, .app .., _, _, _, hi, _ | _, .pi .., _, _, _, hi, _ | _, .letE .., _, _, _, hi, _
  | _, .proj .., _, _, _, hi, _ | _, .natLit _, _, _, _, hi, _ | _, .strLit _, _, _, _, hi, _ => by
    simp [lamBinders] at hi

/-- A run body agreeing with its constant's header, evaluated and applied to as many arguments as
the index of a parameter written erased, gives a closure that ignores the next one. -/
theorem body_prefix {k k' : Nat} {ls ls' : Levels} {ρ : Env} {ty body : Term} {params : List Rel}
    {n : Nat} {rr : Rel} {v0 fv : Value} {args : List Term.Arg}
    (hb : HeaderOk ty body params) (hn : n ∈ erasedParams ty) (hrr : params[n]? = some rr)
    (hirr : rr.alwaysIrr = true) (hlen : args.length = n) (hv0 : eval p k' ls' [] body = .ok v0)
    (he : applySpine p k ls ρ v0 args = .ok fv) : IgnoresNext ann fv := by
  have hlt := hb.1 n hn
  obtain ⟨b0, hb0⟩ : ∃ b0, (lamRels body)[n]? = some b0 :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have heq := hb.2 n b0 rr hb0 hrr
  subst heq
  cases body with
  | lam b d t =>
    rw [eval_lam] at hv0
    cases hv0
    subst hlen
    exact (applySpine_lamChain args b d t [] ls' b0 fv hb0 (alwaysIrr_irrAt hirr ls') he).1
  | _ => simp [lamRels] at hlt

