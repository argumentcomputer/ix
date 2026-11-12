import IxCC.Lam.Erase.Proof.BuildArgs
import IxCC.Lam.Erase.Proof.Bind

/-! # Erasure's saturated forms meet their specification

`saturated` (primitives, constructors, quotients, `casesOn`, recursors)
produces a `SatR` derivation, given a sound recursive call. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)

/-! ## Lists built element by element -/

section Lists

variable {I : Input}

theorem FieldsR.of_step {G : Key.GKey → GlobalId → Prop} {cx cx' : Cx} {c : CId} {q : Profile}
    {j : Nat} {x : Src.Term.Arg} {xs : List Src.Term.Arg} {o : Option Term} {fs : List Term}
    (hx : (I.kept c q j = true ∧ ∃ y, o = some y.1 ∧ ArgOne I G cx' x y) ∨
      (I.kept c q j = false ∧ x.2.2.irrP cx.prof = true ∧ o = none))
    (hrest : FieldsR I G cx cx' c q (j + 1) xs fs) :
    FieldsR I G cx cx' c q j (x :: xs) (match o with | some f => f :: fs | none => fs) := by
  obtain ⟨a, m, r⟩ := x
  rcases hx with ⟨hk, y, rfl, (⟨hr, rfl⟩ | ⟨hr, hm, ht, _⟩)⟩ | ⟨hk, hr, rfl⟩
  · exact .keptIrr hk hr hrest
  · dsimp only at hm ht
    subst hm
    exact .keptRel hk hr ht hrest
  · exact .drop hk hr hrest

theorem sound_fields {cx cx' : Cx} {c : CId} {q : Profile}
    {F : Src.Term.Arg × Nat → M (Option Term)}
    (hF : ∀ x j, Sound (F (x, j)) fun o G =>
      (I.kept c q j = true ∧ ∃ y, o = some y.1 ∧ ArgOne I G cx' x y) ∨
      (I.kept c q j = false ∧ x.2.2.irrP cx.prof = true ∧ o = none)) :
    ∀ (xs : List Src.Term.Arg) (j : Nat),
      Sound ((xs.zipIdx j).filterMapM F) fun fs G => FieldsR I G cx cx' c q j xs fs
  | [], _ => Sound.pure fun _ => .nil
  | x :: xs, j => by
    rw [List.zipIdx_cons, List.filterMapM_cons]
    refine Sound.bind (hF x j) fun o => ?_
    cases o with
    | none =>
      exact (sound_fields hF xs (j + 1)).imp fun fs G h hx =>
        FieldsR.of_step (o := none) hx h
    | some f =>
      exact Sound.bind (sound_fields hF xs (j + 1)) fun fs =>
        Sound.pure fun G h hx => FieldsR.of_step (o := some f) hx h

/-- One alternative of a `casesOn`. -/
def AltOne (I : Input) (G : Key.GKey → GlobalId → Prop) (cx : Cx) (r : CId) (q : Profile)
    (ind : CId) (refs : List Ref) (mbase j : Nat) (rule : Src.Rule) (alt : Alt) : Prop :=
  ∃ key arity fields body, alt = .mk key arity body ∧
    RuleAltR I r q cx.depth ind j rule key arity fields ∧
    MinorR I G (cx.extra arity) (refs.getD (mbase + j) .box) fields body

theorem sound_alts {cx : Cx} {r : CId} {q : Profile} {ind : CId} {refs : List Ref} {mbase : Nat}
    {F : Src.Rule × Nat → M Alt}
    (hF : ∀ rule j, Sound (F (rule, j)) fun alt G => AltOne I G cx r q ind refs mbase j rule alt) :
    ∀ (rules : List Src.Rule) (j : Nat),
      Sound ((rules.zipIdx j).mapM F) fun alts G => AltsR I G cx r q ind refs mbase j rules alts
  | [], _ => Sound.pure fun _ => .nil
  | rule :: rules, j => by
    rw [List.zipIdx_cons, List.mapM_cons]
    refine Sound.bind (hF rule j) fun alt =>
      Sound.bind (sound_alts hF rules (j + 1)) fun alts => Sound.pure fun G h ha => ?_
    obtain ⟨key, arity, fields, body, rfl, h₁, h₂⟩ := ha
    exact .cons h₁ h₂ h

end Lists

/-! ## `ruleAlt` -/

theorem sound_ruleAlt (I : Input) (r : CId) (q : Profile) (base : Nat) (ind : CId) (j : Nat)
    (rule : Src.Rule) :
    Sound (ruleAlt I r q base ind j rule) fun x _ =>
      RuleAltR I r q base ind j rule x.1 x.2.1 x.2.2 := by
  unfold ruleAlt
  split
  · next s lv ind' cidx np nf ty hd =>
    dsimp only
    split
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
      exact Sound.bind (sound_registerCtor _ _ _) fun _ =>
        Sound.pure fun _ _ => ⟨_, _, _, _, _, _, hd, rfl, rfl, rfl, rfl, rfl⟩
    · exact Sound.decline_bind
  · exact Sound.decline

/-! ## A recursor spine's arguments to `r⋆` -/

section RecArgs

variable {I : Input}

/-- One argument of `recForm`. -/
def RecArgOne (I : Input) (G : Key.GKey → GlobalId → Prop) (cx : Cx) (r : CId) (q : Profile)
    (np nmot nmin i : Nat) (ref : Ref) (y : Term × Mode) : Prop :=
  (¬ IsMinor np nmot nmin i ∧ y.2 = .strict ∧ RefR I G cx ref y.1) ∨
  (IsMinor np nmot nmin i ∧ I.paramIrr r q i = true ∧ ref = .box ∧ y = (.box, .strict)) ∨
  (IsMinor np nmot nmin i ∧ I.paramIrr r q i = false ∧
    hasName (minorSig I r q (i - (np + nmot))) = false ∧ ∃ l, ref = .lvl l ∧ y = (cx.lvl l, .name)) ∨
  (IsMinor np nmot nmin i ∧ I.paramIrr r q i = false ∧
    hasName (minorSig I r q (i - (np + nmot))) = false ∧ ∃ m, ref = .name m ∧ y.2 = .name ∧
      TR I G cx m y.1) ∨
  (IsMinor np nmot nmin i ∧ I.paramIrr r q i = false ∧
    hasName (minorSig I r q (i - (np + nmot))) = true ∧ ∃ v l, ref = .name (.var v) ∧
      cx.ctx[v]? = some (some l) ∧ cx.minors.lookup l = some (minorSig I r q (i - (np + nmot))) ∧
      y = (cx.lvl l, .name)) ∨
  (IsMinor np nmot nmin i ∧ I.paramIrr r q i = false ∧
    hasName (minorSig I r q (i - (np + nmot))) = true ∧ ∃ m t, ref = .name m ∧
      (∀ v, m ≠ .var v) ∧ (minorSig I r q (i - (np + nmot))).length ≤ m.lamCount ∧ TR I G cx m t ∧
      Term.setModes (minorSig I r q (i - (np + nmot))) t = some y.1 ∧ y.2 = .name)

theorem RecArgsR.of_one {G : Key.GKey → GlobalId → Prop} {cx : Cx} {r : CId} {q : Profile}
    {np nmot nmin i : Nat} {ref : Ref} {refs : List Ref} {y : Term × Mode}
    {ys : List (Term × Mode)} (h : RecArgOne I G cx r q np nmot nmin i ref y)
    (hr : RecArgsR I G cx r q np nmot nmin (i + 1) refs ys) :
    RecArgsR I G cx r q np nmot nmin i (ref :: refs) (y :: ys) := by
  obtain ⟨t, md⟩ := y
  rcases h with ⟨hm, h2, h3⟩ | ⟨hm, hp, rfl, e⟩ | ⟨hm, hp, hn, l, rfl, e⟩ | ⟨hm, hp, hn, m, rfl, h2, h3⟩ |
    ⟨hm, hp, hn, v, l, rfl, hv, hl, e⟩ | ⟨hm, hp, hn, m, t₀, rfl, hnv, hlen, ht, hs, h2⟩
  · dsimp only at h2 h3; subst h2; exact .other hm h3 hr
  · cases e; exact .minorBox hm hp hr
  · cases e; exact .minorLvl hm hp hn hr
  · dsimp only at h2 h3; subst h2; exact .minorName hm hp hn h3 hr
  · cases e; exact .minorFwd hm hp hn hv hl hr
  · dsimp only at h2 hs; subst h2; exact .minorTele hm hp hn hnv hlen ht hs hr

theorem sound_recArgs {cx : Cx} {r : CId} {q : Profile} {np nmot nmin : Nat}
    {F : Ref × Nat → M (Term × Mode)}
    (hF : ∀ ref i, Sound (F (ref, i)) fun y G => RecArgOne I G cx r q np nmot nmin i ref y) :
    ∀ (refs : List Ref) (i : Nat),
      Sound ((refs.zipIdx i).mapM F) fun ys G => RecArgsR I G cx r q np nmot nmin i refs ys
  | [], _ => Sound.pure fun _ => .nil
  | ref :: refs, i => by
    rw [List.zipIdx_cons, List.mapM_cons]
    exact Sound.bind (hF ref i) fun y =>
      Sound.bind (sound_recArgs hF refs (i + 1)) fun ys => Sound.pure fun _ h hy =>
        RecArgsR.of_one hy h

end RecArgs

/-! ## The forms -/

section Forms

variable {I : Input} {rec : Rec} (hrec : RecSound I rec)
include hrec

theorem sound_primForm (cx : Cx) (op : Src.PrimOp) (q : Profile) (args : List Src.Term.Arg) :
    Sound (primForm I rec cx op args) fun t G => SatR I G cx (.prim op) q args t := by
  unfold primForm
  dsimp only
  have hk : Sound (strictArgs rec cx args >>= fun args' =>
      (Pure.pure (Term.prim (Prim.ofSrc op) (args'.map (·.1))) : M Term))
      fun t G => SatR I G cx (.prim op) q args t :=
    Sound.bind (sound_strictArgs hrec cx args) fun args' => Sound.pure fun _ h => .prim h
  split
  · exact Sound.bind (sound_registerBool I) fun _ => hk.imp fun _ _ h _ => h
  · exact hk

theorem sound_quotMkForm (cx : Cx) (c : CId) (q : Profile) (args : List Src.Term.Arg) :
    Sound (quotMkForm rec cx args) fun t G => SatR I G cx (.quotMk c) q args t := by
  unfold quotMkForm
  exact Sound.bind (sound_bindArgs hrec cx _) fun ⟨lets, refs, cx'⟩ =>
    Sound.bind (sound_refTerm hrec cx' _) fun e => Sound.pure fun _ he hb => .quotMk hb he

theorem sound_quotLiftForm (cx : Cx) (c : CId) (q : Profile) (args : List Src.Term.Arg) :
    Sound (quotLiftForm rec cx args) fun t G => SatR I G cx (.quotLift c) q args t := by
  unfold quotLiftForm
  exact Sound.bind (sound_bindArgs hrec cx _) fun ⟨lets, refs, cx'⟩ =>
    Sound.bind (sound_refTerm hrec cx' _) fun f =>
      Sound.bind (sound_refTerm hrec cx' _) fun x =>
        Sound.pure fun _ hx hf hb => .quotLift hb hf hx

theorem sound_ctorForm (cx : Cx) (c : CId) (q : Profile) (args : List Src.Term.Arg) :
    Sound (ctorForm I rec cx c q args) fun t G => SatR I G cx (.ctor c) q args t := by
  unfold ctorForm
  split
  · next sf lv ind cidx np nf ty hd =>
    split
    · next hz =>
      have hz' : I.known.natZero = some c := (beq_iff_eq.1 hz).symm
      exact Sound.pure fun _ => .natZero hd hz'
    · next hz =>
      have hz' : I.known.natZero ≠ some c := fun e => hz (by rw [e]; exact beq_self_eq_true _)
      refine Sound.bind (sound_bindArgs hrec cx _) fun ⟨lets, refs, cx'⟩ => ?_
      dsimp only
      split
      · next hs =>
        have hs' : I.known.natSucc = some c := (beq_iff_eq.1 hs).symm
        exact Sound.bind (sound_strictArgs hrec cx' _) fun fs =>
          Sound.pure fun _ hf hb => .natSucc hd hz' hs' hb hf
      · next hs =>
        have hs' : I.known.natSucc ≠ some c := fun e => hs (by rw [e]; exact beq_self_eq_true _)
        refine Sound.bind (sound_fields (I := I) (c := c) (q := q) (cx := cx) (cx' := cx')
          (fun x j => ?_) (args.drop np) 0)
          fun fields => ?_
        · obtain ⟨a, m, r⟩ := x
          dsimp only
          split
          · next hk =>
            exact Sound.bind (sound_strictArg hrec cx' (a, m, r)) fun y =>
              Sound.pure fun _ hy => .inl ⟨hk, y, rfl, hy⟩
          · next hk =>
            have hk' : I.kept c q j = false := by simpa using hk
            split
            · exact Sound.decline_bind
            · next hr =>
              exact Sound.pure fun _ => .inr ⟨hk', by simpa using hr, rfl⟩
        · split
          · next j hu =>
            split
            · next f =>
              exact Sound.pure fun _ hF hb => .ctorUnbox hd hz' hs' hb hF hu
            · exact Sound.decline
          · next hu =>
            exact Sound.bind (sound_registerCtor _ _ _) fun _ =>
              Sound.pure fun _ _ hF hb => .ctorBox hd hz' hs' hb hF hu
  · exact Sound.decline

theorem sound_casesForm (cx : Cx) (c r : CId) (q : Profile) (args : List Src.Term.Arg)
    (hres : I.resolve.get? c = some (.case r)) :
    Sound (casesForm I rec cx c r q args) fun t G => SatR I G cx (.cases c) q args t := by
  unfold casesForm
  split
  · next sf k lv np nmot nmin ni ind rules ty hd =>
    dsimp only
    refine Sound.bind (sound_bindArgs hrec cx _) fun ⟨lets, refs, cx'⟩ => ?_
    dsimp only
    split
    · next hk =>
      exact Sound.bind (Sound.pure (Q := fun b _ => b = Term.trap.tick) fun _ => rfl) fun body =>
        Sound.pure fun _ hbody hb => by subst hbody; exact .casesEmpty hres hd hb hk
    · next w srcs hk =>
      exact Sound.bind (sound_minorApp hrec cx' _ _) fun body =>
        Sound.pure fun _ hm hb => .casesSub hres hd hb hk hm
    · next hk =>
      split
      · exact Sound.decline_bind
      · next hmaj =>
        split
        · next j hu =>
          refine Sound.bind (sound_minorApp hrec cx' _ _) fun body =>
            Sound.pure fun _ hm hb => ?_
          generalize hmj : refs.getD (np + 1 + ni) Ref.box = major at hm hmaj
          cases major with
          | box => exact absurd rfl hmaj
          | lvl l => exact .casesUnbox hres hd hb hk hmj hu hm
          | name _ =>
            obtain ⟨x, hx⟩ := hb.getD_name_zipIdx hmj
            simp only [decide_eq_true_eq] at hx
            omega
        · next hu =>
          have hu' : I.unbox? ind q = none := by
            cases h : I.unbox? ind q with
            | none => rfl
            | some j => exact (hu j h).elim
          refine Sound.bind (sound_refTerm hrec cx' _) fun scrut =>
            Sound.bind (sound_alts (I := I) (cx := cx') (r := r) (q := q) (ind := ind) (refs := refs)
              (mbase := np + 1 + ni + 1) (fun rule j => ?_) rules 0) fun alts =>
                Sound.bind (Sound.pure (Q := fun b _ => b = (scrut.case alts none).tick)
                  fun _ => rfl) fun body => Sound.pure fun G hbody halts hsc hb => ?_
          · dsimp only
            exact Sound.bind (sound_ruleAlt I r q cx'.depth ind j rule) fun ⟨key, arity, fields⟩ =>
              Sound.bind (sound_minorApp hrec _ _ _) fun body =>
                Sound.pure fun _ hm ha => ⟨key, arity, fields, body, rfl, ha, hm⟩
          · subst hbody
            generalize hmj : refs.getD (np + 1 + ni) Ref.box = major at hsc hmaj
            cases hsc with
            | box => exact absurd rfl hmaj
            | lvl => exact .casesOrd hres hd hb hk hmj hu' halts
            | name _ =>
              obtain ⟨x, hx⟩ := hb.getD_name_zipIdx hmj
              simp only [decide_eq_true_eq] at hx
              omega
    · exact Sound.decline_bind
  · exact Sound.decline

theorem sound_recForm (cx : Cx) (r : CId) (q : Profile) (args : List Src.Term.Arg) :
    Sound (recForm I rec cx r q args) fun t G => SatR I G cx (.recr r) q args t := by
  unfold recForm
  split
  · next sf k lv np nmot nmin ni ind rules ty hd =>
    dsimp only
    refine Sound.bind (sound_bindArgs hrec cx _) fun ⟨lets, refs, cx'⟩ => ?_
    dsimp only
    refine Sound.ite (fun _ => Sound.decline_bind) fun hc4 => ?_
    refine Sound.bind (sound_recArgs (cx := cx') (r := r) (q := q) (np := np) (nmot := nmot)
      (nmin := nmin) (fun ref i => ?_) refs 0) fun argTerms =>
        Sound.bind (sound_globalId _) fun g => Sound.pure fun _ hg ha hb => .recr hd hb ?_ ha hg
    · dsimp only
      refine Sound.ite (fun hnm => ?_) fun hm => ?_
      · have hm' : ¬ IsMinor np nmot nmin i := fun h => by simp [IsMinor] at h; simp_all
        exact Sound.bind (sound_refTerm hrec cx' ref) fun t =>
          Sound.pure fun _ h => .inl ⟨hm', rfl, h⟩
      · have hm' : IsMinor np nmot nmin i := by
          have h := hm
          simp only [Bool.not_eq_true', Bool.not_eq_false, decide_eq_true_eq] at h
          exact h
        cases ref with
        | box =>
          dsimp only
          refine Sound.ite (fun _ => Sound.decline_bind) fun hp => ?_
          have hp' : I.paramIrr r q i = true := by simpa using hp
          exact Sound.pure fun _ => .inr (.inl ⟨hm', hp', rfl, rfl⟩)
        | lvl l =>
          dsimp only
          refine Sound.ite (fun _ => Sound.decline_bind) fun hp => ?_
          have hp' : I.paramIrr r q i = false := by simpa using hp
          refine Sound.ite (fun _ => Sound.decline_bind) fun hn => ?_
          have hn' : hasName (minorSig I r q (i - (np + nmot))) = false := by simpa using hn
          exact Sound.pure fun _ => .inr (.inr (.inl ⟨hm', hp', hn', l, rfl, rfl⟩))
        | name m =>
          dsimp only
          refine Sound.ite (fun _ => Sound.decline_bind) fun hp => ?_
          have hp' : I.paramIrr r q i = false := by simpa using hp
          refine Sound.ite (fun hn => ?_) fun hn => ?_
          · have hn' : hasName (minorSig I r q (i - (np + nmot))) = false := by simpa using hn
            exact Sound.bind (hrec cx' m) fun t => Sound.pure fun _ ht =>
              .inr (.inr (.inr (.inl ⟨hm', hp', hn', m, rfl, rfl, ht⟩)))
          · have hn' : hasName (minorSig I r q (i - (np + nmot))) = true := by simpa using hn
            split
            · next v =>
              split
              · next l hl =>
                refine Sound.ite (fun hlk => ?_) fun _ => Sound.decline
                have hlk' : cx'.minors.lookup l = some (minorSig I r q (i - (np + nmot))) := by
                  simpa using hlk
                exact Sound.pure fun _ =>
                  .inr (.inr (.inr (.inr (.inl ⟨hm', hp', hn', v, l, rfl, hl, hlk', rfl⟩))))
              · exact Sound.decline
            · next hnv =>
              refine Sound.ite (fun _ => Sound.decline_bind) fun hlen => ?_
              have hlen' : (minorSig I r q (i - (np + nmot))).length ≤ m.lamCount := by
                simpa using hlen
              refine Sound.bind (hrec cx' m) fun t => ?_
              split
              · next t' hs =>
                exact Sound.pure fun _ ht =>
                  .inr (.inr (.inr (.inr (.inr ⟨hm', hp', hn', m, t, rfl,
                    fun v e => hnv v e, hlen', ht, hs, rfl⟩))))
              · exact Sound.decline
    · intro hko e
      apply hc4
      rw [hko, e]
      rfl
  · exact Sound.decline

theorem sound_saturated (cx : Cx) (h : Head) (q : Profile) (args : List Src.Term.Arg) :
    Sound (saturated I rec cx h q args) fun t G => SatR I G cx h q args t := by
  unfold saturated
  cases h with
  | prim op => exact sound_primForm hrec cx op q args
  | word w op => exact Sound.decline
  | ctor c => exact sound_ctorForm hrec cx c q args
  | quotMk c => exact sound_quotMkForm hrec cx c q args
  | quotLift c => exact sound_quotLiftForm hrec cx c q args
  | cases c =>
    dsimp only
    split
    · next r hres => exact sound_casesForm hrec cx c r q args hres
    · exact Sound.decline
  | recr r => exact sound_recForm hrec cx r q args

end Forms

end IxCC.Lam.Erase.Proof
