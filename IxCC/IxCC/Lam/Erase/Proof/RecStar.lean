import IxCC.Lam.Erase.Proof.Elim

/-! # Recursors after their arguments: `r⋆`

A saturated recursor spine erases to its `r⋆` global applied to every
argument (minors by name). SrcEval fires the recursor: ι, the rule chosen
by the major's constructor (or the only rule, or `trap`), then the rule's
right-hand side over the parameters, motives, minors and fields. Lam enters
`r⋆`'s λ-telescope (charge-free up to the last binder, whose closure entry is
the ι), then `case`s on the major and runs the erased rule body, whose
minor application passes the IHs by name to a λ-telescope. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)
open IxCC.Sem (Result ClockMono SimUpTo later later_succ)

section Slots

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

/-- A Src slot against the Lam slot at a level, or `irr` for □. -/
inductive SlotAt (I : Input) (G : Key.GKey → GlobalId → Prop) (ρ₀ : Env) :
    Option Nat → Src.Slot → Prop
  | lvl {l : Nat} {s : Src.Slot} {s' : Slot} :
      l < ρ₀.length → ρ₀[ρ₀.length - 1 - l]? = some s' → SR I G s s' → SlotAt I G ρ₀ (some l) s
  | box {s : Src.Slot} : IrrSlot s → SlotAt I G ρ₀ none s

theorem FieldSlot.slotAt {ρ₀ : Env} {o : Option Nat} {s : Src.Slot}
    (h : FieldSlot I G ρ₀ o s) : SlotAt I G ρ₀ o s := by
  cases h with
  | lvl hl hg hv => exact .lvl hl hg (.val hv)
  | box hs => exact .box hs

theorem ER.prependAt {ρ₀ : Env} :
    ∀ {xs : List (Option Nat)} {ys : List Src.Slot}, Forall2 (SlotAt I G ρ₀) xs ys →
      ∀ {ctx : List (Option Nat)} {ρ : Src.Env}, ER I G ctx ρ ρ₀ → ER I G (xs ++ ctx) (ys ++ ρ) ρ₀
  | _, _, .nil, _, _, h => h
  | _, _, .cons (.lvl hl hg hs) hr, _, _, h => .lvl hl hg hs (ER.prependAt hr h)
  | _, _, .cons (.box hs) hr, _, _, h => .box hs (ER.prependAt hr h)

theorem Forall2.map_left {α β γ : Type} {R : α → β → Prop} {S : γ → β → Prop} (f : α → γ)
    (h : ∀ a b, R a b → S (f a) b) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 S (xs.map f) ys
  | _, _, .nil => .nil
  | _, _, .cons hr hs => .cons (h _ _ hr) (Forall2.map_left f h hs)

theorem Forall2.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 S xs ys
  | _, _, .nil => .nil
  | _, _, .cons hr hs => .cons (h _ _ hr) (Forall2.imp h hs)

/-- A slot of a λ-telescope thunk forces to a closure whose telescope is
still long enough. -/
theorem TeleSlot.force {p : Src.Program} :
    ∀ {n : Nat} {s : Src.Slot}, TeleSlot n s → ∀ {k : Nat} {f : Src.Value},
      Src.force p k s = .ok f → n = 0 ∨ ∃ b d body ρ ls, f = .clo b d body ρ ls ∧ n ≤ body.lamCount + 1
  | n, _, .lams (m := m) hm, k, f, h => by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact .inl h0
    · refine .inr ?_
      rw [Src.force_name] at h
      cases k with
      | zero => cases h
      | succ k =>
        cases m with
        | lam b d body =>
          rw [later_succ, Src.eval_lam] at h
          cases h
          exact ⟨_, _, _, _, _, rfl, by simp [Src.Term.lamCount] at hm; omega⟩
        | _ => simp [Src.Term.lamCount] at hm; omega
  | n, _, .fwd hv ht, k, f, h => by
    rw [Src.force_name] at h
    cases k with
    | zero => cases h
    | succ k =>
      rw [later_succ, Src.eval_var_of p k _ _ hv] at h
      exact ht.force h

end Slots

/-! ## Entering `r⋆` -/

/-- Every argument's slot is free: the same at every clock. -/
def FreeSlots (P : Program) (ρ : Env) : List (Term × Mode) → List Slot → Prop :=
  Forall2 fun a s => ∀ k, argSlot P k ρ a = .ok s

/-- Applying a λ-telescope closure to exactly its binders, when every
argument's slot is free, enters the body one clock down. -/
theorem applyArgs_lams (P : Program) (ρ : Env) (inner : Term) :
    ∀ (ms : List Mode) (env : Env) (args : List (Term × Mode)) (slots : List Slot) (k : Nat),
      args.length = ms.length + 1 → FreeSlots P ρ args slots →
      Lam.applyArgs P (k + 1) ρ (.clos env (Term.lams ms inner)) args =
        Lam.eval P k (slots.reverse ++ env) inner
  | [], env, [a], [s], k, _, .cons ha .nil => by
    simp only [Lam.applyArgs, ha, Sem.Result.bind_ok, Term.lams, List.foldr_nil,
      Lam.apply_clos, List.reverse_singleton, List.singleton_append]
    cases Lam.eval P k (s :: env) inner <;> rfl
  | m :: ms, env, a :: b :: rest, s :: ss, k, hl, .cons ha hr => by
    rw [Lam.applyArgs_cons, ha, Sem.Result.bind_ok]
    have e : Term.lams (m :: ms) inner = .lam m {} (Term.lams ms inner) := rfl
    rw [e, Lam.apply_clos]
    show (Lam.eval P k (s :: env) (.lam m {} (Term.lams ms inner))).bind _ = _
    rw [Lam.eval_lam, Sem.Result.bind_ok]
    have ih := applyArgs_lams P ρ inner ms (s :: env) (b :: rest) ss k
      (by simp at hl ⊢; omega) hr
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]
  | [], _, [], _, _, hl, _ => by simp at hl
  | [], _, _ :: _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, _, [], _, _, hl, _ => by simp at hl
  | _ :: _, _, [_], _, _, hl, _ => by simp at hl
  | _, _, _ :: _, [], _, _, h => nomatch h

/-! ## A rule's body -/

theorem spine_go_mkApps : ∀ (t : Src.Term) (acc : List Src.Term.Arg) {h : Src.Term}
    {args : List Src.Term.Arg}, Src.Term.spine.go t acc = (h, args) →
      Src.Term.mkApps h args = Src.Term.mkApps t acc
  | .app f a m r, acc, h, args, e => by
    simp only [Src.Term.spine.go] at e
    rw [spine_go_mkApps f _ e]
    rfl
  | .var _, _, _, _, e | .sort _, _, _, _, e | .const .., _, _, _, e | .lam .., _, _, _, e
  | .pi .., _, _, _, e | .letE .., _, _, _, e | .proj .., _, _, _, e | .natLit _, _, _, _, e
  | .strLit _, _, _, _, e => by
    simp only [Src.Term.spine.go, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rfl

theorem spineL_mkApps {t h : Src.Term} {args : List Src.Term.Arg} (e : t.spineL = (h, args)) :
    t = Src.Term.mkApps h args := by
  rw [spine_go_mkApps t [] e]; rfl

theorem peelLams_of_peelUpTo :
    ∀ (n : Nat) (t : Src.Term) {body : Src.Term}, peelUpTo n t = (n, body) → Src.peelLams n t = some body
  | 0, t, body, e => by simp [peelUpTo] at e; subst e; rfl
  | n + 1, .lam _ _ b, body, e => by
    simp only [peelUpTo, Prod.mk.injEq] at e
    obtain ⟨e₁, e₂⟩ := e
    have : peelUpTo n b = (n, body) := by
      rw [← e₂]
      have hk : (peelUpTo n b).1 = n := by omega
      exact Prod.ext hk rfl
    exact peelLams_of_peelUpTo n b this
  | n + 1, .var _, _, e | n + 1, .sort _, _, e | n + 1, .const .., _, e | n + 1, .app .., _, e
  | n + 1, .pi .., _, e | n + 1, .letE .., _, e | n + 1, .proj .., _, e | n + 1, .natLit _, _, e
  | n + 1, .strLit _, _, e => by simp [peelUpTo] at e

theorem RuleArgsR.length {I : Input} {G : Key.GKey → GlobalId → Prop} :
    ∀ {cx : Cx} {args : List Src.Term.Arg} {args' : List (Term × Mode)},
      RuleArgsR I G cx args args' → args.length = args'.length
  | _, _, _, .nil => rfl
  | _, _, _, .irr _ h => by simp [h.length]
  | _, _, _, .name _ _ h => by simp [h.length]
  | _, _, _, .strict _ _ h => by simp [h.length]

/-- A closure whose body has at least `n - 1` further λs. -/
def CloTele (f : Src.Value) (n : Nat) : Prop :=
  n = 0 ∨ ∃ b d body ρ ls, f = .clo b d body ρ ls ∧ n ≤ body.lamCount + 1

/-- A β whose body is a λ gives a closure (or is stuck at the guard). -/
theorem apply_clo_lam {p : Src.Program} {k : Nat} {b : Src.Binder} {d : Src.Term}
    {b₂ : Src.Binder} {d₂ body₂ : Src.Term} {ρ : Src.Env} {ls : Levels} {s : Src.Slot}
    {v : Src.Value} (h : Src.apply p k (.clo b d (.lam b₂ d₂ body₂) ρ ls) s = .ok v) :
    v = .clo b₂ d₂ body₂ (s :: ρ) ls := by
  rw [Src.apply_clo] at h
  split at h
  · cases k with
    | zero => cases h
    | succ k => rw [later_succ, Src.eval_lam] at h; cases h; rfl
  · cases h

/-- After one application inside a telescope, the rest is still one. -/
theorem CloTele.step {p : Src.Program} {f : Src.Value} {n : Nat} (h : CloTele f (n + 1))
    {k : Nat} {s : Src.Slot} {v : Src.Value} (hv : Src.apply p k f s = .ok v) : CloTele v n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact .inl h0
  · rcases h with h | ⟨b, d, body, ρ, ls, rfl, hn⟩
    · cases h
    · cases body with
      | lam b₂ d₂ body₂ =>
        rw [apply_clo_lam hv]
        exact .inr ⟨_, _, _, _, _, rfl, by simp [Src.Term.lamCount] at hn; omega⟩
      | _ => simp [Src.Term.lamCount] at hn; omega

/-! ## Erasures of λ-telescopes -/

theorem mkApps_app_or {h : Src.Term} :
    ∀ (args : List Src.Term.Arg), args ≠ [] → ∃ f a m r, Src.Term.mkApps h args = .app f a m r
  | [], hne => absurd rfl hne
  | [(a, m, r)], _ => ⟨_, _, _, _, rfl⟩
  | (a, m, r) :: b :: rest, _ => by
    obtain ⟨f', a', m', r', e⟩ := mkApps_app_or (h := .app h a m r) (b :: rest) (by simp)
    exact ⟨f', a', m', r', e⟩

theorem mkApps_const_ne_lam {c : CId} {us : List Ixon.Univ} :
    ∀ (args : List Src.Term.Arg) (b : Src.Binder) (d body : Src.Term),
      Src.Term.mkApps (.const c us) args ≠ .lam b d body
  | [], _, _, _ => by simp [Src.Term.mkApps]
  | x :: xs, b, d, body => by
    obtain ⟨f, a, m, r, e⟩ := mkApps_app_or (h := .const c us) (x :: xs) (by simp)
    rw [e]; simp

section

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

/-- An erasure of a Src λ is a Lam λ over an erasure of its body. -/
theorem TR.lam_inv {cx : Cx} {b : Src.Binder} {d body : Src.Term} {t' : Term}
    (h : TR I G cx (.lam b d body) t') :
    ∃ m body', t' = .lam m b.contract body' ∧ TR I G cx.bind body body' := by
  generalize e : Src.Term.lam b d body = t at h
  cases h with
  | lam m hb => cases e; exact ⟨m, _, rfl, hb⟩
  | app _ hne _ _ =>
    obtain ⟨f, a, m, r, e'⟩ := mkApps_app_or _ hne
    rw [e'] at e; cases e
  | plain => exact absurd e.symm (mkApps_const_ne_lam _ _ _ _)
  | variant => exact absurd e.symm (mkApps_const_ne_lam _ _ _ _)
  | wrap => exact absurd e.symm (mkApps_const_ne_lam _ _ _ _)
  | sat => exact absurd e.symm (mkApps_const_ne_lam _ _ _ _)
  | _ => cases e

/-- Setting the modes of an erased λ-telescope keeps it an erasure. -/
theorem TR.setModes :
    ∀ {ms : List Mode} {cx : Cx} {t : Src.Term} {t' t'' : Term}, TR I G cx t t' →
      ms.length ≤ t.lamCount → Term.setModes ms t' = some t'' → TR I G cx t t''
  | [], _, _, _, _, h, _, e => by simp [Term.setModes] at e; subst e; exact h
  | m :: ms, cx, t, t', t'', h, hl, e => by
    cases t with
    | lam b d body =>
      obtain ⟨m₀, body', rfl, hb⟩ := h.lam_inv
      simp only [Term.setModes, Option.map_eq_some_iff] at e
      obtain ⟨body'', e', rfl⟩ := e
      exact .lam m (TR.setModes hb (by simp [Src.Term.lamCount] at hl; omega) e')
    | _ => simp [Src.Term.lamCount] at hl

/-! ## `r⋆`'s argument slots -/

/-- Argument `i` of a recursor spine: related slots, a value on both sides
outside the minors, and a λ-telescope thunk for a minor dispatched by name. -/
def RecSlot (I : Input) (G : Key.GKey → GlobalId → Prop) (r : CId) (q : Profile)
    (np nmot nmin i : Nat) (s : Src.Slot) (s' : Slot) : Prop :=
  SR I G s s' ∧
    (¬ IsMinor np nmot nmin i → ∃ v v', s = .val v ∧ s' = .val v' ∧ VR I G v v') ∧
    (IsMinor np nmot nmin i → I.paramIrr r q i = false →
      hasName (minorSig I r q (i - (np + nmot))) = true →
      TeleSlot (minorSig I r q (i - (np + nmot))).length s)

/-- The argument slots of a recursor spine from position `base`. -/
structure RecSlots (I : Input) (G : Key.GKey → GlobalId → Prop) (r : CId) (q : Profile)
    (np nmot nmin base : Nat) (ss : List Src.Slot) (slots : List Slot) : Prop where
  length : ss.length = slots.length
  at_ : ∀ j s s', ss[j]? = some s → slots[j]? = some s' → RecSlot I G r q np nmot nmin (base + j) s s'

theorem RecSlots.nil {r : CId} {q : Profile} {np nmot nmin base : Nat} :
    RecSlots I G r q np nmot nmin base [] [] :=
  ⟨rfl, fun _ _ _ h => by simp at h⟩

theorem RecSlots.cons {r : CId} {q : Profile} {np nmot nmin i : Nat} {s : Src.Slot} {s' : Slot}
    {ss : List Src.Slot} {slots : List Slot} (h : RecSlot I G r q np nmot nmin i s s')
    (t : RecSlots I G r q np nmot nmin (i + 1) ss slots) :
    RecSlots I G r q np nmot nmin i (s :: ss) (s' :: slots) where
  length := by simp [t.length]
  at_ j a b ha hb := by
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
      subst ha; subst hb
      simpa using h
    | succ j =>
      simp only [List.getElem?_cons_succ] at ha hb
      have := t.at_ j a b ha hb
      rwa [show i + 1 + j = i + (j + 1) by omega] at this

/-- The slots `r⋆` receives: free, and argument by argument related. -/
theorem recArgs_slots {cx : Cx} {ρ : Src.Env} {ρ'' : Env} {ls : Levels}
    (he : EnvR I G cx ρ ρ'') (hag : Agree ls cx.prof) (P : Program) :
    ∀ {r : CId} {q : Profile} {np nmot nmin i : Nat} {refs : List Ref}
      {argTerms : List (Term × Mode)}, RecArgsR I G cx r q np nmot nmin i refs argTerms →
      ∀ {ss : List Src.Slot}, Forall2 (RefSlot I G ls ρ ρ'') refs ss →
        (∀ j a, ¬ IsMinor np nmot nmin (i + j) → refs[j]? ≠ some (.name a)) →
        ∃ slots, FreeSlots P ρ'' argTerms slots ∧ RecSlots I G r q np nmot nmin i ss slots
  | _, _, _, _, _, _, _, _, .nil, _, hrs, _ => by
    cases hrs
    exact ⟨[], .nil, RecSlots.nil⟩
  | _, _, _, _, _, i, _, _, .other hnm hr hrest, _, .cons hs hrs, hnn => by
    obtain ⟨slots, hf, hrs'⟩ := recArgs_slots he hag P hrest hrs fun j a hm => by
      have := hnn (j + 1) a (by rwa [show i + (j + 1) = i + 1 + j by omega])
      simpa using this
    cases hr with
    | box =>
      cases hs with
      | box hirr =>
        obtain ⟨t, ρ₀, ls₀, rfl⟩ := hirr
        exact ⟨.val .box :: slots,
          .cons (fun k => by simp only [argSlot, Lam.eval_box', Sem.Result.bind_ok]) hf,
          .cons ⟨.val .irr, fun _ => ⟨_, _, rfl, rfl, .irr⟩, fun hm => absurd hm hnm⟩ hrs'⟩
    | lvl =>
      cases hs with
      | lvl _ hg hv =>
        refine ⟨.val _ :: slots, .cons (fun k => ?_) hf,
          .cons ⟨.val hv, fun _ => ⟨_, _, rfl, rfl, hv⟩, fun hm => absurd hm hnm⟩ hrs'⟩
        simp only [argSlot]
        rw [Cx.lvl_eq, he.depth, Lam.eval_var_of P k ρ'' hg, Lam.force_val, Sem.Result.bind_ok]
    | name _ => exact absurd rfl (hnn 0 _ (by simpa using hnm))
  | _, _, _, _, _, i, _, _, .minorBox hm hirr hrest, _, .cons hs hrs, hnn => by
    obtain ⟨slots, hf, hrs'⟩ := recArgs_slots he hag P hrest hrs fun j a hm' => by
      have := hnn (j + 1) a (by rwa [show i + (j + 1) = i + 1 + j by omega])
      simpa using this
    cases hs with
    | box hs =>
      obtain ⟨t, ρ₀, ls₀, rfl⟩ := hs
      exact ⟨.val .box :: slots,
        .cons (fun k => by simp only [argSlot, Lam.eval_box', Sem.Result.bind_ok]) hf,
        .cons ⟨.val .irr, fun h => absurd hm h, fun _ h => by rw [hirr] at h; cases h⟩ hrs'⟩
  | _, _, _, _, _, i, _, _, .minorLvl hm hirr hn hrest, _, .cons hs hrs, hnn => by
    obtain ⟨slots, hf, hrs'⟩ := recArgs_slots he hag P hrest hrs fun j a hm' => by
      have := hnn (j + 1) a (by rwa [show i + (j + 1) = i + 1 + j by omega])
      simpa using this
    cases hs with
    | lvl _ hg hv =>
      refine ⟨_ :: slots, .cons (fun k => rfl) hf,
        .cons ⟨?_, fun h => absurd hm h, fun _ _ h => by rw [hn] at h; cases h⟩ hrs'⟩
      rw [Cx.lvl_eq]
      exact SR.delayed (by rw [he.depth]; exact hg) hv
  | _, _, _, _, _, i, _, _, .minorName hm hirr hn ht hrest, _, .cons hs hrs, hnn => by
    obtain ⟨slots, hf, hrs'⟩ := recArgs_slots he hag P hrest hrs fun j a hm' => by
      have := hnn (j + 1) a (by rwa [show i + (j + 1) = i + 1 + j by omega])
      simpa using this
    cases hs with
    | name =>
      exact ⟨_ :: slots, .cons (fun k => rfl) hf,
        .cons ⟨SR.name ht he.er he.depth he.minors he.minorsLt hag, fun h => absurd hm h,
          fun _ _ h => by rw [hn] at h; cases h⟩ hrs'⟩
  | _, _, _, _, _, i, _, _, .minorFwd hm hirr hn hv hlk hrest, _, .cons hs hrs, hnn => by
    obtain ⟨slots, hf, hrs'⟩ := recArgs_slots he hag P hrest hrs fun j a hm' => by
      have := hnn (j + 1) a (by rwa [show i + (j + 1) = i + 1 + j by omega])
      simpa using this
    cases hs with
    | name =>
      obtain ⟨s₀, hs₀, ht₀⟩ := he.minors _ _ _ hv hlk hn
      exact ⟨_ :: slots, .cons (fun k => rfl) hf,
        .cons ⟨SR.name (.varSome hv) he.er he.depth he.minors he.minorsLt hag,
          fun h => absurd hm h, fun _ _ _ => .fwd hs₀ ht₀⟩ hrs'⟩
  | _, _, _, _, _, i, _, _, .minorTele hm hirr hn _ hlen ht hset hrest, _, .cons hs hrs, hnn => by
    obtain ⟨slots, hf, hrs'⟩ := recArgs_slots he hag P hrest hrs fun j a hm' => by
      have := hnn (j + 1) a (by rwa [show i + (j + 1) = i + 1 + j by omega])
      simpa using this
    cases hs with
    | name =>
      exact ⟨_ :: slots, .cons (fun k => rfl) hf,
        .cons ⟨SR.name (ht.setModes hlen hset) he.er he.depth he.minors he.minorsLt hag,
          fun h => absurd hm h, fun _ _ _ => .lams hlen⟩ hrs'⟩

/-- A slot at level `i` of `r⋆`'s telescope, under further binders `X`. -/
theorem RecSlots.slotAt {r : CId} {q : Profile} {np nmot nmin : Nat} {ss : List Src.Slot}
    {slots : List Slot} (h : RecSlots I G r q np nmot nmin 0 ss slots) {i : Nat} {s : Src.Slot}
    (hs : ss[i]? = some s) (X : List Slot) : SlotAt I G (X ++ slots.reverse) (some i) s := by
  have hi : i < slots.length := h.length ▸ lt_of_getElem?_eq_some hs
  obtain ⟨s', hs'⟩ : ∃ s', slots[i]? = some s' := ⟨_, List.getElem?_eq_getElem hi⟩
  refine .lvl (by simp; omega) ?_ (by simpa using (h.at_ i s s' hs hs').1)
  have e : (X ++ slots.reverse).length - 1 - i = X.length + (slots.length - 1 - i) := by
    simp; omega
  rw [e, List.getElem?_append_right (by omega), List.getElem?_reverse (by omega)]
  simpa [show slots.length - 1 - (slots.length - 1 - i) = i by omega] using hs'

theorem RuleBodyR.fields_length {r : CId} {q : Profile} {pre depth : Nat}
    {minors : List (Nat × List Mode)} {rule : Src.Rule} {fields : List (Option Nat)} {t : Term}
    (h : RuleBodyR I G r q pre depth minors rule fields t) : fields.length = rule.fields := by
  cases h with
  | var _ hf _ _ _ _ => exact hf
  | other _ hf _ _ => exact hf

theorem mem_recMinors {r : CId} {q : Profile} {np nmot nmin ni : Nat} {e : Nat × List Mode}
    (h : e ∈ recMinors I r q np nmot nmin ni) :
    ∃ j, j < nmin ∧ e = (np + nmot + j, minorSig I r q j) ∧
      I.paramIrr r q (np + nmot + j) = false := by
  simp only [recMinors, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨j, ⟨hj, hmode⟩, rfl⟩ := h
  refine ⟨j, hj, rfl, ?_⟩
  simp only [recModes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show np + nmot + j < np + nmot + nmin + ni + 1 by omega),
    Option.map_some, Option.getD_some] at hmode
  split at hmode
  · next hc => exact (by simpa using hc : _ ∧ _).2
  · cases hmode

/-- The context of a rule's body inside `r⋆`: its first `pre` binders
at their levels, then its fields; its minors dispatched by name hold
λ-telescopes. -/
theorem ruleEnv {q : Profile} {pre depth : Nat} {minors : List (Nat × List Mode)}
    {fields : List (Option Nat)} {pres fslots : List Src.Slot} {ρ' : Env}
    (hpre : Forall2 (SlotAt I G ρ') ((List.range pre).map some) pres)
    (hflds : Forall2 (SlotAt I G ρ') fields fslots)
    (hfge : ∀ l, some l ∈ fields → pre ≤ l)
    (hmin : ∀ e ∈ minors, e.1 < pre)
    (htele : ∀ l sig, minors.lookup l = some sig → hasName sig = true →
      ∃ s, pres[l]? = some s ∧ TeleSlot sig.length s)
    (hdepth : depth = ρ'.length) (hle : pre ≤ depth) :
    EnvR I G (ruleCx q pre depth minors fields) (pres ++ fslots).reverse ρ' where
  er := by
    simp only [ruleCx, Cx.under, List.reverse_append, List.append_nil]
    exact ER.prependAt hflds.reverse (by simpa using ER.prependAt hpre.reverse (ER.nil (ρ' := ρ')))
  depth := hdepth
  minors := by
    intro v l sig hv hl hn
    simp only [ruleCx, Cx.under, List.append_nil] at hv hl
    have hlenX : ((List.range pre).map some ++ fields).length = (pres ++ fslots).length := by
      simp [← hpre.length, hflds.length]
    have hvlt : v < ((List.range pre).map some ++ fields).length := by
      rw [← List.length_reverse]; exact lt_of_getElem?_eq_some hv
    rw [List.getElem?_reverse hvlt] at hv
    rw [List.getElem?_reverse (hlenX ▸ hvlt), ← hlenX]
    generalize ((List.range pre).map some ++ fields).length - 1 - v = idx at hv ⊢
    by_cases hidx : idx < pre
    · rw [List.getElem?_append_left (by simp; omega)] at hv
      rw [List.getElem?_append_left (by rw [← hpre.length]; simp; omega)]
      simp only [List.getElem?_map, List.getElem?_range hidx, Option.map_some,
        Option.some.injEq] at hv
      subst hv
      exact htele _ _ hl hn
    · rw [List.getElem?_append_right (by simp; omega)] at hv
      have hmem : some l ∈ fields := List.mem_of_getElem? hv
      have h₁ := hfge l hmem
      have h₂ := hmin _ (lookup_mem hl)
      simp at h₂
      omega
  minorsLt := fun e he' => by
    have := hmin e he'
    simp only [ruleCx, Cx.under]
    omega

end

namespace Setting

variable (S : Setting)

/-- SrcEval's recursor step after the ι tick: the rule chosen, its
right-hand side under the parameters, motives, minors and fields. -/
def recStep (p : Src.Program) (k : Nat) (ls : Levels) (kind : Src.RecKind)
    (np nmot nmin ni : Nat) (ind : CId) (rules : List Src.Rule) (args : List Src.Slot) :
    Result Src.Value :=
  (Src.recChosen p k ls kind ind np (np + nmot + nmin + ni)
      ((args.drop (np + nmot + nmin)).take ni) args).bind fun (j, fields) =>
    match rules[j]? with
    | some rule =>
      match Src.peelLams (args.take (np + nmot + nmin) ++ fields).length rule.rhs with
      | some body => Src.eval p k ls (args.take (np + nmot + nmin) ++ fields).reverse body
      | none => .stuck
    | none => .stuck

/-- SrcEval's recursor firing, once its entry and kind are known. -/
theorem fire_recr_of {r : CId} {sf kb : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Src.Rule} {ty : Src.Term} {q : Profile} {ls' : Levels} {kind : Src.RecKind}
    (hd : S.I.decl? r = some (.recr sf kb lv np nmot nmin ni ind rules ty))
    (hk : S.I.kindAt r q = some kind) (hag : Agree ls' q) (args : List Src.Slot) (j : Nat) :
    Src.fire S.p j (.recr r) ls' args =
      later j fun j => recStep S.p j ls' kind np nmot nmin ni ind rules args := by
  rw [Src.fire_recr]
  simp only [Input.kindAt, input_recKind, Option.map_eq_some_iff] at hk
  obtain ⟨k₀, hk₀, rfl⟩ := hk
  have hd' : S.p.decl? r = some (.recr sf kb lv np nmot nmin ni ind rules ty) := hd
  have hk₀' : S.p.table.recKindOf r = some k₀ := hk₀
  simp only [hd', hk₀', Option.map_some, hag.recKind]
  rfl

section

variable {S} {m : Nat} (htr : S.TRSim m) (hap : S.ApplySim m)
include htr hap

/-- A rule's minor applied to its fields and IHs (`ruleBody`): by-name IHs
only when the minor holds a λ-telescope covering them. -/
theorem ruleArgs_sim : ∀ {cx : Cx} {args : List Src.Term.Arg} {args' : List (Term × Mode)},
    RuleArgsR S.I S.G cx args args' →
    ∀ {ρ : Src.Env} {ρ' : Env} {ls : Levels}, EnvR S.I S.G cx ρ ρ' → Agree ls cx.prof →
      ∀ {f : Src.Value} {f' : Val}, VR S.I S.G f f' →
        (CloTele f args.length ∨ hasName (args'.map (·.2)) = false) →
        SimUpTo (VR S.I S.G) m (fun k => Src.applySpine S.p k ls ρ f args)
          (fun k => Lam.applyArgs S.L k ρ' f' args')
  | _, _, _, .nil, ρ, ρ', ls, _, _, f, f', hf, _ =>
    (SimUpTo.ok hf).congr (fun _ => rfl) (fun _ => rfl)
  | _, _, _, .irr (a := a) (r := r) (rest := rest) hr hrest, ρ, ρ', ls, he, hag, f, f', hf,
      hdisj => by
    have hr' : _ = true := (hag.irr _).symm.trans hr
    refine (SimUpTo.bind' (Lam.apply_mono S.L _ _) (fun v => Lam.applyArgs_mono S.L _ v _)
      (hap hf (SR.val (VR.irr (t := some a) (ρ := ρ) (ls := ls))) (.inr ⟨_, _, rfl, rfl⟩))
      fun v v' hv hsrc => ruleArgs_sim hrest he hag hv ?_).congr (fun k => ?_) (fun k => ?_)
    · rcases hdisj with ht | hn
      · obtain ⟨k, _, hk⟩ := hsrc
        exact .inl (CloTele.step (by simpa using ht) hk)
      · exact .inr (by simpa [hasName] using hn)
    · simp only [Src.applySpine, Src.slotOf, hr', ↓reduceIte, Sem.Result.bind_ok]
    · simp only [Lam.applyArgs, Lam.argSlot, Lam.eval_box', Sem.Result.bind_ok]
  | _, _, _, .name (a := a) (r := r) (rest := rest) hr hta hrest, ρ, ρ', ls, he, hag, f, f', hf,
      hdisj => by
    have hr' : _ = false := (hag.irr _).symm.trans hr
    have ht : CloTele f (rest.length + 1) := by
      rcases hdisj with ht | hn
      · simpa using ht
      · simp [hasName] at hn
    obtain ⟨b, d, body, ρ₀, ls₀, rfl, _⟩ : ∃ b d body ρ₀ ls₀, f = .clo b d body ρ₀ ls₀ ∧
        rest.length + 1 ≤ body.lamCount + 1 := by
      rcases ht with h | h
      · simp at h
      · exact h
    refine (SimUpTo.bind' (Lam.apply_mono S.L _ _) (fun v => Lam.applyArgs_mono S.L _ v _)
      (hap hf (SR.name hta he.er he.depth he.minors he.minorsLt hag) (.inl ⟨_, _, _, _, _, rfl⟩))
      fun v v' hv hsrc => ruleArgs_sim hrest he hag hv ?_).congr (fun k => ?_) (fun k => ?_)
    · obtain ⟨k, _, hk⟩ := hsrc
      exact .inl (CloTele.step ht hk)
    · simp only [Src.applySpine, Src.slotOf, hr', Bool.false_eq_true, ↓reduceIte,
        Sem.Result.bind_ok]
    · simp only [Lam.applyArgs, Lam.argSlot, Sem.Result.bind_ok]
  | _, _, _, .strict (a := a) (r := r) (rest := rest) hr hta hrest, ρ, ρ', ls, he, hag, f, f', hf,
      hdisj => by
    have hr' : _ = false := (hag.irr _).symm.trans hr
    refine (SimUpTo.bind (Lam.eval_mono S.L _ _)
      (fun x => (Lam.apply_mono S.L _ _).bind fun v => Lam.applyArgs_mono S.L _ v _)
      (htr hta he hag) fun x x' hx =>
        SimUpTo.bind' (Lam.apply_mono S.L _ _) (fun v => Lam.applyArgs_mono S.L _ v _)
          (hap hf (SR.val hx) (.inr ⟨_, _, rfl, rfl⟩))
          fun v v' hv hsrc => ruleArgs_sim hrest he hag hv ?_).congr (fun k => ?_) (fun k => ?_)
    · rcases hdisj with ht | hn
      · obtain ⟨k, _, hk⟩ := hsrc
        exact .inl (CloTele.step (by simpa using ht) hk)
      · exact .inr (by simpa [hasName] using hn)
    · simp only [Src.applySpine, Src.slotOf, hr', Bool.false_eq_true, ↓reduceIte,
        Sem.Result.bind_assoc, Sem.Result.bind_ok]
    · simp only [Lam.applyArgs, Lam.argSlot, Sem.Result.bind_assoc, Sem.Result.bind_ok]

/-- A recursor rule's body inside `r⋆` against the rule's right-hand side
under its binders. -/
theorem ruleBody_sim {r : CId} {q : Profile} {pre depth : Nat}
    {minors : List (Nat × List Mode)} {rule : Src.Rule} {fields : List (Option Nat)} {t : Term}
    (hb : RuleBodyR S.I S.G r q pre depth minors rule fields t) {ρ : Src.Env} {ρ' : Env}
    {ls : Levels} (he : EnvR S.I S.G (ruleCx q pre depth minors fields) ρ ρ') (hag : Agree ls q) :
    ∃ body, Src.peelLams (pre + rule.fields) rule.rhs = some body ∧
      SimUpTo (VR S.I S.G) m (fun k => Src.eval S.p k ls ρ body) (fun k => Lam.eval S.L k ρ' t) := by
  cases hb with
  | @var body v args h args' hp _ hsp hv hargs hmin =>
    refine ⟨body, peelLams_of_peelUpTo _ _ hp, ?_⟩
    rw [spineL_mkApps hsp]
    refine (SimUpTo.bind' (Lam.eval_mono S.L _ _) (fun w => Lam.applyArgs_mono S.L _ w _)
      (htr hv he hag) fun f f' hf hsrc => ruleArgs_sim htr hap hargs he hag hf ?_).congr
      (fun k => Src.eval_mkApps S.p k ls ρ _ _) (fun k => Lam.eval_apps S.L k ρ' _ _)
    cases hn : hasName (args'.map (·.2)) with
    | false => exact .inr rfl
    | true =>
      obtain ⟨l, hl, hlk⟩ := hmin hn
      obtain ⟨s, hs, hts⟩ := he.minors v l _ hl hlk hn
      obtain ⟨k, _, hk⟩ := hsrc
      rw [Src.eval_var_of S.p k ls ρ hs] at hk
      have hlen : (args'.map (·.2)).length = args.length := by
        simp [(RuleArgsR.length hargs).symm]
      rw [← hlen]
      exact .inl (hts.force hk)
  | other hp _ _ ht =>
    exact ⟨_, peelLams_of_peelUpTo _ _ hp, htr ht he hag⟩

end

section

variable {S} (wf : ProgWF S.I) {m : Nat} (hlt : ∀ m' < m, S.Level m')
include wf hlt

/-- A saturated recursor: the ι on both sides (SrcEval's firing, Lam's
global), then the chosen rule's body over the same slots. -/
theorem recr_form {r : CId} {sf kb : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Src.Rule} {ty : Src.Term} {q : Profile}
    (hd : S.I.decl? r = some (.recr sf kb lv np nmot nmin ni ind rules ty))
    {cx : Cx} {ρ : Src.Env} {ρ'' : Env} {ls ls' : Levels} (he : EnvR S.I S.G cx ρ ρ'')
    (hag : Agree ls cx.prof) (hag' : Agree ls' q) {refs : List Ref} {ss : List Src.Slot}
    (hfa : FormArgs S.I S.G (.recr r) ls ρ ρ'' refs ss)
    (hlen : ss.length = np + nmot + nmin + ni + 1)
    (hnn : ∀ j a, ¬ IsMinor np nmot nmin j → refs[j]? ≠ some (.name a))
    {argTerms : List (Term × Mode)}
    (hargs : RecArgsR S.I S.G cx r q np nmot nmin 0 refs argTerms)
    {g : GlobalId} (hg : S.G (.recStar r q) g) :
    SimUpTo (VR S.I S.G) m (fun j => Src.fire S.p j (.recr r) ls' ss)
      (fun j => Lam.eval S.L j ρ'' (Term.apps (.glob g) argTerms)) := by
  have hrefs : Forall2 (RefSlot S.I S.G ls ρ ρ'') refs ss :=
    Forall2.of_getElem hfa.length.symm fun i ref s hr hs =>
      hfa.at_ i ref s hr hs (by simp [headReads])
  obtain ⟨slots, hfree, hrs⟩ := recArgs_slots he hag S.L hargs hrefs (by simpa using hnn)
  have hsl : slots.length = np + nmot + nmin + ni + 1 := by rw [← hrs.length, hlen]
  obtain ⟨gl, hgl, _, hbody⟩ := S.prog _ _ hg
  have hstar : RecStarR S.I S.G r q gl.body := by cases hbody; assumption
  -- Lam: the global's tick, then its telescope entered.
  have hlam : ∀ inner, gl.body = Term.lams (recModes S.I r q np nmot nmin ni) inner →
      ∀ j, Lam.eval S.L j ρ'' (Term.apps (.glob g) argTerms) =
        later j fun j => Lam.eval S.L j slots.reverse inner := by
    intro inner hb j
    obtain ⟨m₀, ms, hms, hmsl⟩ : ∃ m₀ ms, recModes S.I r q np nmot nmin ni = m₀ :: ms ∧
        ms.length + 1 = np + nmot + nmin + ni + 1 := by
      cases h : recModes S.I r q np nmot nmin ni with
      | nil => simp [recModes] at h
      | cons m₀ ms =>
        have := congrArg List.length h
        simp only [recModes, List.length_map, List.length_range, List.length_cons] at this
        exact ⟨m₀, ms, rfl, this.symm⟩
    rw [Lam.eval_apps, Lam.eval_glob, hgl]
    cases j with
    | zero => rfl
    | succ j =>
      dsimp only
      rw [hb, hms, Lam.eval_lams_cons, Sem.Result.bind_ok,
        applyArgs_lams S.L ρ'' inner ms [] argTerms slots j
          (by rw [hfree.length, hsl]; omega) hfree, List.append_nil, later_succ]
  -- The rule's context: parameters, motives and minors at their levels.
  have hpre : ∀ X : List Slot, Forall2 (SlotAt S.I S.G (X ++ slots.reverse))
      ((List.range (np + nmot + nmin)).map some) (ss.take (np + nmot + nmin)) := fun X =>
    Forall2.of_getElem (by simp; omega) fun i x y hx hy => by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
      obtain ⟨i', hi', rfl⟩ := hx
      obtain ⟨rfl, hi⟩ := range_getElem?_eq_some hi'
      simp only [List.getElem?_take, hi, ↓reduceIte] at hy
      exact hrs.slotAt hy X
  have htele : ∀ l sig, (recMinors S.I r q np nmot nmin ni).lookup l = some sig →
      hasName sig = true →
      ∃ s, (ss.take (np + nmot + nmin))[l]? = some s ∧ TeleSlot sig.length s := by
    intro l sig hl hn
    obtain ⟨j, hj, he', hpi⟩ := mem_recMinors (lookup_mem hl)
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    have h₁ : np + nmot + j < ss.length := by omega
    have h₂ : np + nmot + j < slots.length := by omega
    obtain ⟨_, _, hmin⟩ := hrs.at_ (np + nmot + j) _ _ (List.getElem?_eq_getElem h₁)
      (List.getElem?_eq_getElem h₂)
    simp only [Nat.zero_add, Nat.add_sub_cancel_left] at hmin
    have hj' : np + nmot + j < np + nmot + nmin := by omega
    refine ⟨_, by simp only [List.getElem?_take, hj', ↓reduceIte]
                  exact List.getElem?_eq_getElem h₁,
      hmin ⟨by omega, by omega⟩ hpi hn⟩
  have hmin : ∀ e ∈ recMinors S.I r q np nmot nmin ni, e.1 < np + nmot + nmin := fun e he' => by
    obtain ⟨j, hj, rfl, _⟩ := mem_recMinors he'
    simp only
    omega
  generalize hB : gl.body = B at hstar
  cases hstar with
  | empty hd' hk =>
    rw [hd] at hd'
    cases hd'
    refine (SimUpTo.later (n := m) (c₁ := fun _ => (.trap : Result Src.Value))
      (c₂ := fun _ => (.trap : Result Val)) fun _ _ => SimUpTo.trap).congr (fun j => ?_)
      (fun j => ?_)
    · rw [S.fire_recr_of hd hk hag' ss j]
      cases j <;> rfl
    · rw [hlam _ hB j]
      cases j with
      | zero => rfl
      | succ j => simp only [later_succ]; exact Lam.eval_trap' S.L j _
  | sub hd' hk hhead hrb =>
    rename_i w srcs rule body
    rw [hd] at hd'
    cases hd'
    obtain ⟨k₀, hk₀, hkk⟩ : ∃ k₀, S.I.recKind.get? r = some k₀ ∧ k₀.atProfile q =
        .subsingleton w srcs := by
      simpa [Input.kindAt] using hk
    have hk₀' : S.I.recKind.get? r = some (.subsingleton w srcs) := by
      cases k₀ with
      | subsingleton w' srcs' =>
        simp only [Src.RecKind.atProfile] at hkk
        split at hkk
        · cases hkk; exact hk₀
        · cases hkk
      | _ => simp [Src.RecKind.atProfile] at hkk
    have hidx := wf.recKindIdx hd hk₀'
    have hflen := RuleBodyR.fields_length hrb
    simp only [List.length_map] at hflen
    have hF : Forall2 (SlotAt S.I S.G slots.reverse)
        (srcs.map fun
          | .index i => some (np + nmot + nmin + i)
          | .proof => none)
        (srcs.map fun
          | .index i => ((ss.drop (np + nmot + nmin)).take ni).getD i (Src.Slot.irrNone ls')
          | .proof => Src.Slot.irrNone ls') := by
      refine Forall2.of_getElem (by simp) fun i x y hx hy => ?_
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hx hy
      obtain ⟨s₁, hs₁, rfl⟩ := hx
      obtain ⟨s₂, hs₂, rfl⟩ := hy
      rw [hs₁] at hs₂
      cases hs₂
      cases s₁ with
      | proof => exact .box ⟨_, _, _, rfl⟩
      | index i' =>
        have hi' : i' < ni := hidx i' (List.mem_of_getElem? hs₁)
        have hget : ((ss.drop (np + nmot + nmin)).take ni).getD i' (Src.Slot.irrNone ls') =
            ss[np + nmot + nmin + i']'(by omega) := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi', ↓reduceIte,
            List.getElem?_drop]
          rw [List.getElem?_eq_getElem (by omega)]
          rfl
        dsimp only
        rw [hget]
        simpa using hrs.slotAt (List.getElem?_eq_getElem (by omega)) []
    have hfge : ∀ l, some l ∈ (srcs.map fun
        | Src.FieldSrc.index i => some (np + nmot + nmin + i)
        | Src.FieldSrc.proof => none) → np + nmot + nmin ≤ l := by
      intro l hl
      simp only [List.mem_map] at hl
      obtain ⟨s, _, hs⟩ := hl
      cases s with
      | index i => simp only [Option.some.injEq] at hs; omega
      | proof => cases hs
    have henv := ruleEnv (depth := np + nmot + nmin + ni + 1) (by simpa using hpre []) hF hfge
      hmin htele (q := q) (by simp [hsl]) (by omega)
    refine (SimUpTo.later (n := m) fun m' hm' => ?_).congr
      (fun j => S.fire_recr_of hd hk hag' ss j) (fun j => hlam _ hB j)
    have hlv := hlt m' (by omega)
    obtain ⟨body', hpeel, hsim⟩ := ruleBody_sim hlv.tr hlv.apply hrb henv hag'
    refine hsim.congr (fun j => ?_) (fun j => rfl)
    have h0 : rules[0]? = some rule := by rw [← List.head?_eq_getElem?]; exact hhead
    simp only [recStep, Src.recChosen, Sem.Result.bind_ok, h0, List.length_append,
      List.length_take, List.length_map]
    rw [show min (np + nmot + nmin) ss.length + srcs.length = np + nmot + nmin + rule.fields by
      omega, hpeel]
    rfl
  | ord hd' hk hu halts =>
    rename_i alts
    rw [hd] at hd'
    cases hd'
    obtain ⟨hcount, _⟩ := wf.recRules hd
    refine (SimUpTo.later (n := m) fun m' hm' => ?_).congr
      (fun j => S.fire_recr_of hd hk hag' ss j) (fun j => hlam _ hB j)
    have hlv := hlt m' (by omega)
    have h₁ : np + nmot + nmin + ni < ss.length := by omega
    have h₂ : np + nmot + nmin + ni < slots.length := by omega
    obtain ⟨_, hnon, _⟩ := hrs.at_ (np + nmot + nmin + ni) _ _ (List.getElem?_eq_getElem h₁)
      (List.getElem?_eq_getElem h₂)
    obtain ⟨v, v', hsv, hsv', hvv⟩ := hnon (by unfold IsMinor; omega)
    have hgetD : ss.getD (np + nmot + nmin + ni) default = .val v := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some, hsv]
    have hvar : ∀ j, Lam.eval S.L j slots.reverse (.var 0) = .ok v' := by
      intro j
      have hg0 : slots.reverse[0]? = some (.val v') := by
        rw [List.getElem?_reverse (by omega),
          show slots.length - 1 - 0 = np + nmot + nmin + ni by omega,
          List.getElem?_eq_getElem h₂, hsv']
      rw [Lam.eval_var_of S.L j _ hg0, Lam.force_val]
    cases hsel : S.p.selectRule ind np v with
    | none =>
      refine (SimUpTo.stuck _).congr (fun j => ?_) (fun j => rfl)
      simp only [recStep, Src.recChosen, hgetD, Src.force_val, Sem.Result.bind_ok, hsel,
        Result.ofOption]
      rfl
    | some jf =>
      obtain ⟨jr, flds⟩ := jf
      obtain ⟨rule, key, n, fields, body, vals, hrule, hbody, hasc, hn, hev, hfs, hge⟩ :=
        select_alt wf (RecAltsR.altsFor halts) hcount
          (by rw [← Input.unbox?_prof S.I ind q]; exact hu) hvv hsel slots.reverse
          (by simp [hsl])
      have henv := ruleEnv (depth := np + nmot + nmin + ni + 1 + n) (hpre (vals.reverse.map .val))
        (Forall2.imp (fun _ _ h => FieldSlot.slotAt h) hfs)
        (fun l hl => Nat.le_trans (by omega) (hge l hl)) hmin htele (q := q)
        (by simp [hsl, hn]; omega) (by omega)
      obtain ⟨body', hpeel, hsim⟩ := ruleBody_sim hlv.tr hlv.apply hbody henv hag'
      refine hsim.congr (fun j => ?_) (fun j => ?_)
      · have hflen := RuleBodyR.fields_length hbody
        have hl : (ss.take (np + nmot + nmin) ++ flds).length =
            np + nmot + nmin + rule.fields := by
          simp only [List.length_append, List.length_take, ← hfs.length]
          omega
        simp only [recStep, Src.recChosen, hgetD, Src.force_val, Sem.Result.bind_ok, hsel,
          Result.ofOption, hrule]
        rw [hl, hpeel]
      · rw [Lam.eval_case, hvar, Sem.Result.bind_ok]
        simp only [hasc]
        exact hev j none

end

end Setting

end IxCC.Lam.Erase.Proof
