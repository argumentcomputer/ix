import IxCC.Lam.Erase.Proof.Sound
import IxCC.Lam.Erase.Proof.Spec

/-! # Erasure's argument helpers meet their specification

Given a sound recursive call (`RecSound`), `strictArgs`, `bindArgs`,
`refTerm` and `minorApp` produce `ArgsR`, `BindR`, `RefR` and `MinorR`
derivations against every key relation containing the final table
(M2.2). -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)

theorem Sound.decline_bind {α β : Type} {code message : String} {c : Option CId}
    {f : α → M β} {Q : β → (Key.GKey → GlobalId → Prop) → Prop} :
    Sound (Erase.decline code message c >>= f) Q :=
  fun s b s'' e => by
    obtain ⟨a, s', hx, _⟩ := Sound.bind_run e
    exact ((Sound.decline (Q := fun _ _ => False) s a s' hx).2 (fun _ _ => True)
      fun _ _ _ => trivial).elim

/-- The recursive call erasure's helpers receive is sound. -/
def RecSound (I : Input) (rec : Rec) : Prop :=
  ∀ cx t, Sound (rec cx t) fun t' G => TR I G cx t t'

/-- One argument of `strictArgs`. -/
def ArgOne (I : Input) (G : Key.GKey → GlobalId → Prop) (cx : Cx) (x : Src.Term.Arg)
    (y : Term × Mode) : Prop :=
  (x.2.2.irrP cx.prof = true ∧ y = (.box, .strict)) ∨
    (x.2.2.irrP cx.prof = false ∧ x.2.1 = .strict ∧ TR I G cx x.1 y.1 ∧ y.2 = .strict)

theorem ArgsR.of_forall2 {I : Input} {G : Key.GKey → GlobalId → Prop} {cx : Cx} :
    ∀ {args : List Src.Term.Arg} {args' : List (Term × Mode)},
      Forall2 (ArgOne I G cx) args args' → ArgsR I G cx args args'
  | _, _, .nil => .nil
  | (a, m, r) :: _, _ :: _, .cons (.inl ⟨hr, rfl⟩) h => .irr hr (ArgsR.of_forall2 h)
  | (a, m, r) :: _, (a', m') :: _, .cons (.inr ⟨hr, hm, ht, hm'⟩) h => by
    dsimp only at hm hm' ht
    subst hm hm'
    exact .strict hr ht (ArgsR.of_forall2 h)

section

variable {I : Input} {rec : Rec} (hrec : RecSound I rec)
include hrec

theorem sound_strictArg (cx : Cx) (x : Src.Term.Arg) :
    Sound (strictArg rec cx x) fun y G => ArgOne I G cx x y := by
  obtain ⟨a, m, r⟩ := x
  unfold strictArg
  by_cases hr : r.irrP cx.prof = true
  · simp only [hr, ↓reduceIte]
    exact Sound.pure fun _ => .inl ⟨hr, rfl⟩
  · have hr' : r.irrP cx.prof = false := by simpa using hr
    simp only [hr', Bool.false_eq_true, ↓reduceIte]
    cases m with
    | strict => exact Sound.bind (hrec cx a) fun t => Sound.pure fun _ ht => .inr ⟨hr', rfl, ht, rfl⟩
    | byName => exact Sound.decline

theorem sound_strictArgs (cx : Cx) (args : List Src.Term.Arg) :
    Sound (strictArgs rec cx args) fun args' G => ArgsR I G cx args args' :=
  (Sound.mapM fun x _ => sound_strictArg hrec cx x).imp fun _ _ h => ArgsR.of_forall2 h

theorem sound_bindArgs : ∀ (cx : Cx) (xs : List (Src.Term.Arg × Bool)),
    Sound (bindArgs rec cx xs) fun r G => BindR I G cx xs r.1 r.2.1 r.2.2
  | cx, [] => by
    unfold bindArgs
    exact Sound.pure fun _ => .nil
  | cx, ((a, m, r), ok) :: rest => by
    unfold bindArgs
    by_cases hr : r.irrP cx.prof = true
    · simp only [hr, ↓reduceIte]
      exact Sound.bind (sound_bindArgs cx rest) fun ⟨ls, rs, cx'⟩ =>
        Sound.pure fun _ h => .irr hr h
    · have hr' : r.irrP cx.prof = false := by simpa using hr
      simp only [hr', Bool.false_eq_true, ↓reduceIte]
      cases m with
      | byName =>
        dsimp only
        cases ok with
        | true =>
          simp only [↓reduceIte]
          exact Sound.bind (sound_bindArgs cx rest) fun ⟨ls, rs, cx'⟩ =>
            Sound.pure fun _ h => .name hr' h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact Sound.decline_bind
      | strict =>
        exact Sound.bind (hrec cx a) fun v =>
          Sound.bind (sound_bindArgs (cx.extra 1) rest) fun ⟨ls, rs, cx'⟩ =>
            Sound.pure fun _ h hv => .strict hr' hv h

theorem sound_refTerm (cx : Cx) (ref : Ref) :
    Sound (refTerm rec cx ref) fun t G => RefR I G cx ref t := by
  cases ref with
  | box => exact Sound.pure fun _ => .box
  | lvl l => exact Sound.pure fun _ => .lvl
  | name a => exact (hrec cx a).imp fun _ _ h => .name h

theorem sound_minorApp (cx : Cx) (minor : Ref) (fields : List (Option Nat)) :
    Sound (minorApp rec cx minor fields) fun t G => MinorR I G cx minor fields t := by
  unfold minorApp
  cases minor with
  | box => exact Sound.pure fun _ => .box
  | lvl l => exact Sound.pure fun _ => .lvl
  | name m =>
    dsimp only
    exact Sound.bind (hrec _ _) fun body' =>
      Sound.pure fun _ h => .name rfl h

end

end IxCC.Lam.Erase.Proof
