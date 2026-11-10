import IxCC.Lam.Erase.Proof.BuildTerm

/-! # Erasure of globals meets its specification

The body erasure gives each key (`keyBody`) is a `BodyR` body: a δ body
(`constBody`), its by-name variant, `r⋆` (`recStarBody`, with `ruleBody`
for each rule) or a wrapper (`wrapperBody`), against every key relation
containing the final key table. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)

theorem recSound_rec_ (I : Input) : RecSound I (rec_ I) := sound_term I termFuel

section

variable (I : Input)

theorem sound_constBody (c : CId) (q : Profile) :
    Sound (constBody I c q) fun t G => ∃ b, I.deltaBody c = some b ∧ TR I G (bodyCx q) b t := by
  unfold constBody
  dsimp only
  split
  · next g vs thm hr =>
    exact (recSound_rec_ I _ _).imp fun t G h => ⟨_, by simp [Input.deltaBody, hr], h⟩
  · next thm body hr =>
    exact (recSound_rec_ I _ _).imp fun t G h => ⟨_, by simp [Input.deltaBody, hr], h⟩
  · exact Sound.decline
  · next hr =>
    split
    · next lv ty v hd =>
      exact (recSound_rec_ I _ _).imp fun t G h => ⟨_, by simp [Input.deltaBody, hr, hd], h⟩
    · next lv ty v hd =>
      refine Sound.ite (fun hop => ?_) fun _ => Sound.decline
      exact (recSound_rec_ I _ _).imp fun t G h => ⟨_, by simp [Input.deltaBody, hr, hd, hop], h⟩
    · exact Sound.decline
    · exact Sound.decline

/-- One argument of a rule's minor application. -/
def RuleArgOne (I : Input) (G : Key.GKey → GlobalId → Prop) (cx : Cx) (x : Src.Term.Arg)
    (y : Term × Mode) : Prop :=
  (x.2.2.irrP cx.prof = true ∧ y = (.box, .strict)) ∨
    (x.2.2.irrP cx.prof = false ∧ x.2.1 = .byName ∧ TR I G cx x.1 y.1 ∧ y.2 = .name) ∨
    (x.2.2.irrP cx.prof = false ∧ x.2.1 = .strict ∧ TR I G cx x.1 y.1 ∧ y.2 = .strict)

theorem RuleArgsR.of_forall2 {G : Key.GKey → GlobalId → Prop} {cx : Cx} :
    ∀ {args : List Src.Term.Arg} {args' : List (Term × Mode)},
      Forall2 (RuleArgOne I G cx) args args' → RuleArgsR I G cx args args'
  | _, _, .nil => .nil
  | (a, m, r) :: _, _ :: _, .cons (.inl ⟨hr, rfl⟩) h => .irr hr (RuleArgsR.of_forall2 h)
  | (a, m, r) :: _, (a', m') :: _, .cons (.inr (.inl ⟨hr, hm, ht, hm'⟩)) h => by
    dsimp only at hm hm' ht
    subst hm hm'
    exact .name hr ht (RuleArgsR.of_forall2 h)
  | (a, m, r) :: _, (a', m') :: _, .cons (.inr (.inr ⟨hr, hm, ht, hm'⟩)) h => by
    dsimp only at hm hm' ht
    subst hm hm'
    exact .strict hr ht (RuleArgsR.of_forall2 h)

theorem sound_ruleBody (r : CId) (q : Profile) (pre depth : Nat)
    (minors : List (Nat × List Mode)) (rule : Src.Rule) (fields : List (Option Nat)) :
    Sound (ruleBody I r q pre depth minors rule fields) fun t G =>
      RuleBodyR I G r q pre depth minors rule fields t := by
  unfold ruleBody
  dsimp only
  refine Sound.ite (fun hc => ?_) fun _ => Sound.decline_bind
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hn, hlen⟩ := hc
  have hp : peelUpTo (pre + rule.fields) rule.rhs =
      (pre + rule.fields, (peelUpTo (pre + rule.fields) rule.rhs).2) := Prod.ext hn rfl
  generalize (peelUpTo (pre + rule.fields) rule.rhs).2 = body at hp ⊢
  have hcx : ({ prof := q, ctx := [], depth := depth, minors := minors } : Cx).under
      ((List.range pre).map some ++ fields) = ruleCx q pre depth minors fields := rfl
  rw [hcx]
  have hsp : body.spineL = (body.spine.1, body.spine.2) := rfl
  generalize body.spine.1 = hd at hsp ⊢
  generalize body.spine.2 = args at hsp ⊢
  split
  · next v =>
    refine Sound.bind (recSound_rec_ I _ _) fun h => ?_
    refine Sound.bind (Sound.mapM (P := fun x y G => RuleArgOne I G (ruleCx q pre depth minors fields) x y)
      fun x _ => ?_) fun args' => ?_
    · obtain ⟨a, m, rl⟩ := x
      dsimp only
      refine Sound.ite (fun hr => Sound.pure fun _ => .inl ⟨hr, rfl⟩) fun hr => ?_
      have hr' : rl.irrP q = false := by simpa using hr
      refine Sound.ite (fun hm => ?_) fun hm => ?_
      · have hm' : m = .byName := by
          cases m with
          | strict => exact absurd hm (by decide)
          | byName => rfl
        exact Sound.bind (recSound_rec_ I _ _) fun t => Sound.pure fun _ ht =>
          .inr (.inl ⟨hr', hm', ht, rfl⟩)
      · have hm' : m = .strict := by
          cases m with
          | strict => rfl
          | byName => exact absurd (by decide) hm
        exact Sound.bind (recSound_rec_ I _ _) fun t => Sound.pure fun _ ht =>
          .inr (.inr ⟨hr', hm', ht, rfl⟩)
    · have hargs : ∀ G, Forall2 (RuleArgOne I G (ruleCx q pre depth minors fields)) args args' →
          RuleArgsR I G (ruleCx q pre depth minors fields) args args' :=
        fun G h => RuleArgsR.of_forall2 I h
      refine Sound.ite (fun hn => ?_) fun hn => ?_
      · split
        · next l hl =>
          refine Sound.ite (fun hlk => ?_) fun _ => Sound.decline_bind
          have hlk' : (ruleCx q pre depth minors fields).minors.lookup l =
              some (args'.map (·.2)) := by simpa using hlk
          exact Sound.pure fun G ha hh => .var hp hlen hsp hh (hargs G ha)
            fun _ => ⟨l, hl, hlk'⟩
        · exact Sound.decline_bind
      · have hn' : hasName (args'.map (·.2)) = false := by simpa using hn
        exact Sound.pure fun G ha hh => .var hp hlen hsp hh (hargs G ha)
          fun e => by rw [hn'] at e; cases e
  · next hnv =>
    exact (recSound_rec_ I _ _).imp fun t G h =>
      .other hp hlen (fun v e => hnv v (by rw [hsp] at e; exact e)) h

/-- One alternative of `r⋆`. -/
def RecAltOne (I : Input) (G : Key.GKey → GlobalId → Prop) (r : CId) (q : Profile)
    (pre arity : Nat) (minors : List (Nat × List Mode)) (ind : CId) (j : Nat) (rule : Src.Rule)
    (alt : Alt) : Prop :=
  ∃ key n fields body, alt = .mk key n body ∧ RuleAltR I r q arity ind j rule key n fields ∧
    RuleBodyR I G r q pre (arity + n) minors rule fields body

theorem sound_recAlts {r : CId} {q : Profile} {pre arity : Nat} {minors : List (Nat × List Mode)}
    {ind : CId} {F : Src.Rule × Nat → M Alt}
    (hF : ∀ rule j, Sound (F (rule, j)) fun alt G =>
      RecAltOne I G r q pre arity minors ind j rule alt) :
    ∀ (rules : List Src.Rule) (j : Nat),
      Sound ((rules.zipIdx j).mapM F) fun alts G =>
        RecAltsR I G r q pre arity minors ind j rules alts
  | [], _ => Sound.pure fun _ => .nil
  | rule :: rules, j => by
    rw [List.zipIdx_cons, List.mapM_cons]
    refine Sound.bind (hF rule j) fun alt =>
      Sound.bind (sound_recAlts hF rules (j + 1)) fun alts => Sound.pure fun G h ha => ?_
    obtain ⟨key, n, fields, body, rfl, h₁, h₂⟩ := ha
    exact .cons h₁ h₂ h

theorem sound_recStarBody (r : CId) (q : Profile) :
    Sound (recStarBody I r q) fun t G => RecStarR I G r q t := by
  unfold recStarBody
  dsimp only
  split
  · next sf k lv np nmot nmin ni ind rules ty hd =>
    have hrules : I.rulesOf r = rules := by simp [Input.rulesOf, hd]
    split
    · next hk =>
      exact Sound.bind (Sound.pure (Q := fun b _ => b = Term.trap) fun _ => rfl) fun body =>
        Sound.pure fun _ hb => by subst hb; exact .empty hd hk
    · next w srcs hk =>
      rw [hrules]
      split
      · next rule hr =>
        exact Sound.bind (sound_ruleBody I r q _ _ _ rule _) fun body =>
          Sound.pure fun _ hb => .sub hd hk hr hb
      · exact Sound.decline_bind
    · next hk =>
      refine Sound.ite (fun _ => Sound.decline_bind) fun hu => ?_
      have hu' : I.unbox? ind q = none := by simpa using hu
      refine Sound.bind (sound_recAlts I (r := r) (q := q) (pre := np + nmot + nmin)
        (arity := np + nmot + nmin + ni + 1) (ind := ind) (fun rule j => ?_) rules 0) fun alts =>
          Sound.bind (Sound.pure (Q := fun b _ => b = (Term.var 0).case alts none) fun _ => rfl)
            fun body => Sound.pure fun _ hb ha => by subst hb; exact .ord hd hk hu' ha
      dsimp only
      exact Sound.bind (sound_ruleAlt I r q _ ind j rule) fun ⟨key, n, fields⟩ =>
        Sound.bind (sound_ruleBody I r q _ _ _ rule fields) fun body =>
          Sound.pure fun _ hb ha => ⟨key, n, fields, body, rfl, ha, hb⟩
    · exact Sound.decline_bind
  · exact Sound.decline

omit I in
theorem PrimOp.eq_of_beq {a b : Src.PrimOp} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | (cases h)

omit I in
theorem Head.eq_of_beq {a b : Head} (h : (a == b) = true) : a = b := by
  cases a with
  | ctor c =>
    cases b with
    | ctor d => exact congrArg _ (beq_iff_eq.1 (show (c == d) = true from h))
    | _ => cases h
  | quotMk c =>
    cases b with
    | quotMk d => exact congrArg _ (beq_iff_eq.1 (show (c == d) = true from h))
    | _ => cases h
  | quotLift c =>
    cases b with
    | quotLift d => exact congrArg _ (beq_iff_eq.1 (show (c == d) = true from h))
    | _ => cases h
  | recr c =>
    cases b with
    | recr d => exact congrArg _ (beq_iff_eq.1 (show (c == d) = true from h))
    | _ => cases h
  | cases c =>
    cases b with
    | cases d => exact congrArg _ (beq_iff_eq.1 (show (c == d) = true from h))
    | _ => cases h
  | prim c =>
    cases b with
    | prim d => exact congrArg _ (PrimOp.eq_of_beq (show (c == d) = true from h))
    | _ => cases h

omit I in
theorem Head.opt_eq_of_beq {a b : Option Head} (h : (a == b) = true) : a = b := by
  cases a <;> cases b
  · rfl
  · cases h
  · cases h
  · exact congrArg some (Head.eq_of_beq h)

theorem sound_wrapperBody (h : Head) (q : Profile) :
    Sound (wrapperBody I h q) fun t G => WrapR I G h q t := by
  unfold wrapperBody
  cases h with
  | prim op => exact Sound.pure fun _ => .prim rfl
  | ctor c =>
    dsimp only
    refine Sound.ite (fun hh => ?_) fun _ => Sound.decline_bind
    exact Sound.bind (sound_saturated (recSound_rec_ I) _ _ q _) fun t =>
      Sound.pure fun _ hs => .other (.inl rfl) (Head.opt_eq_of_beq hh) hs
  | quotMk c =>
    dsimp only
    refine Sound.ite (fun hh => ?_) fun _ => Sound.decline_bind
    exact Sound.bind (sound_saturated (recSound_rec_ I) _ _ q _) fun t =>
      Sound.pure fun _ hs => .other (.inr (.inl rfl)) (Head.opt_eq_of_beq hh) hs
  | quotLift c =>
    dsimp only
    refine Sound.ite (fun hh => ?_) fun _ => Sound.decline_bind
    exact Sound.bind (sound_saturated (recSound_rec_ I) _ _ q _) fun t =>
      Sound.pure fun _ hs => .other (.inr (.inr (.inl rfl))) (Head.opt_eq_of_beq hh) hs
  | recr c =>
    dsimp only
    refine Sound.ite (fun hh => ?_) fun _ => Sound.decline_bind
    exact Sound.bind (sound_saturated (recSound_rec_ I) _ _ q _) fun t =>
      Sound.pure fun _ hs => .other (.inr (.inr (.inr (.inl rfl)))) (Head.opt_eq_of_beq hh) hs
  | cases c =>
    dsimp only
    refine Sound.ite (fun hh => ?_) fun _ => Sound.decline_bind
    exact Sound.bind (sound_saturated (recSound_rec_ I) _ _ q _) fun t =>
      Sound.pure fun _ hs => .other (.inr (.inr (.inr (.inr rfl)))) (Head.opt_eq_of_beq hh) hs

theorem sound_keyBody (key : Key.GKey) :
    Sound (keyBody I key) fun t G => BodyR I G key t.1 := by
  unfold keyBody
  dsimp only
  split
  · next c q =>
    exact Sound.bind (sound_constBody I c q) fun body => Sound.pure fun _ ⟨b, hb, ht⟩ => .const hb ht
  · next c q =>
    split
    · next a hlz =>
      refine Sound.ite (fun hc => ?_) fun _ => Sound.decline_bind
      obtain ⟨b, hb, hab⟩ : ∃ b, I.deltaBody c = some b ∧ a ≤ b.lamCount := by
        revert hc
        cases hb : I.deltaBody c with
        | none => intro h; simp at h
        | some b => intro h; exact ⟨b, rfl, by simpa using h⟩
      refine Sound.bind (sound_constBody I c q) fun b₀ => ?_
      split
      · next t hs =>
        exact Sound.pure fun _ ⟨b', hb', ht⟩ => by
          rw [hb] at hb'
          cases hb'
          exact .byName hlz hb hab ht hs
      · exact Sound.decline
    · exact Sound.decline
  · next r q =>
    exact Sound.bind (sound_recStarBody I r q) fun body => Sound.pure fun _ h => .recStar h
  · next h q =>
    exact Sound.bind (sound_wrapperBody I h q) fun body => Sound.pure fun _ hw => .wrapper hw
  · exact Sound.decline

end

end IxCC.Lam.Erase.Proof
